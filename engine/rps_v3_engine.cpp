#include <stdint.h>

extern "C" __attribute__((import_module("env"), import_name("now_ms"))) double now_ms();

static const int SIZE = 9;
static const int N = 81;
static const int BLUE = 1;
static const int RED = -1;
static const int ROCK = 1;
static const int PAPER = 2;
static const int SCISSORS = 3;
static const int MATE = 10000000;
static const int INF = 1000000000;
static const int MAX_MOVES = 272;
static const int MAX_PLY = 128;
static const int TT_BITS = 17;
static const int TT_SIZE = 1 << TT_BITS;
static const uint64_t MASK64 = ~uint64_t(0);

enum TTFlag : uint8_t { TT_EXACT = 0, TT_LOWER = 1, TT_UPPER = 2 };

struct Position {
  int8_t pieces[N];
  int8_t territory[N];
  int8_t side;
  int8_t bluePieces;
  int8_t redPieces;
  int8_t blueTerritory;
  int8_t redTerritory;
  int8_t neutral;
  uint16_t ply;
  uint8_t consecutivePasses;
  uint64_t hash;
};

struct Undo {
  int move;
  int8_t captured;
  int8_t claimed;
  int8_t side;
  int8_t bluePieces;
  int8_t redPieces;
  int8_t blueTerritory;
  int8_t redTerritory;
  int8_t neutral;
  uint16_t ply;
  uint8_t consecutivePasses;
  uint64_t hash;
};

struct TTEntry {
  uint64_t key;
  int32_t score;
  int16_t move;
  int8_t depth;
  uint8_t flag;
  uint8_t generation;
  uint8_t pad[3];
};

struct Stats {
  uint32_t nodes;
  uint32_t qnodes;
  uint32_t ttHits;
  uint32_t cutoffs;
  int32_t score;
  int32_t bestMove;
  int32_t completedDepth;
  double elapsedMs;
};

struct TacticalStats {
  int threatened;
  int preyEdges;
  int uniquePrey;
  int safeNeutralMoves;
  int neutralMoves;
  int mobility;
  int safeMobility;
  int escapeMoves;
  int huntPressure;
  int diversity;
};

static Position pos;
static Stats stats;
static TTEntry tt[TT_SIZE];
static int32_t historyTable[2][N * N];
static int16_t killers[MAX_PLY][2];
static uint64_t zPiece[N][6];
static uint64_t zTerr[N][2];
static uint64_t zSide;
static uint64_t zPass[3];
static int8_t neighbors[N][8];
static int8_t neighborCount[N];
static uint64_t rngState = 0x9e3779b97f4a7c15ULL;
static uint8_t generation = 0;
static int stopSearch = 0;
static double deadlineMs = 0.0;
static uint32_t nodeLimit = 0xffffffffu;
static int qDepthLimit = 4;
static int useLMR = 1;
static int initialized = 0;

static inline int iabs(int x) { return x < 0 ? -x : x; }
static inline int imax(int a, int b) { return a > b ? a : b; }
static inline int imin(int a, int b) { return a < b ? a : b; }
static inline int ownerOf(int piece) { return piece > 0 ? BLUE : piece < 0 ? RED : 0; }
static inline int typeOf(int piece) { return piece < 0 ? -piece : piece; }
static inline int rowOf(int sq) { return sq / SIZE; }
static inline int colOf(int sq) { return sq % SIZE; }
static inline int encodeMove(int from, int to) { return from * N + to; }
static inline int moveFrom(int move) { return move / N; }
static inline int moveTo(int move) { return move % N; }
static inline int colorIndex(int side) { return side == BLUE ? 0 : 1; }

static inline int beats(int attackerType, int victimType) {
  return (attackerType == ROCK && victimType == SCISSORS) ||
         (attackerType == SCISSORS && victimType == PAPER) ||
         (attackerType == PAPER && victimType == ROCK);
}

static uint64_t rand64() {
  uint64_t x = rngState;
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  rngState = x;
  return x;
}

static inline int pieceZIndex(int piece) {
  return piece > 0 ? piece - 1 : 3 + (-piece - 1);
}

static void initZobrist() {
  for (int sq = 0; sq < N; ++sq) {
    for (int i = 0; i < 6; ++i) zPiece[sq][i] = rand64();
    zTerr[sq][0] = rand64();
    zTerr[sq][1] = rand64();
  }
  zSide = rand64();
  for (int i = 0; i < 3; ++i) zPass[i] = rand64();
}

static void initNeighbors() {
  for (int sq = 0; sq < N; ++sq) {
    int r = rowOf(sq), c = colOf(sq), count = 0;
    for (int dr = -1; dr <= 1; ++dr) {
      for (int dc = -1; dc <= 1; ++dc) {
        if (dr == 0 && dc == 0) continue;
        int nr = r + dr, nc = c + dc;
        if (nr >= 0 && nr < SIZE && nc >= 0 && nc < SIZE) {
          neighbors[sq][count++] = (int8_t)(nr * SIZE + nc);
        }
      }
    }
    neighborCount[sq] = (int8_t)count;
  }
}

static uint64_t computeHash(const Position& p) {
  uint64_t hash = 0;
  for (int sq = 0; sq < N; ++sq) {
    int piece = p.pieces[sq];
    if (piece) hash ^= zPiece[sq][pieceZIndex(piece)];
    int territory = p.territory[sq];
    if (territory == BLUE) hash ^= zTerr[sq][0];
    else if (territory == RED) hash ^= zTerr[sq][1];
  }
  if (p.side == RED) hash ^= zSide;
  hash ^= zPass[p.consecutivePasses >= 2 ? 2 : p.consecutivePasses];
  return hash;
}

static void clearStats() {
  stats.nodes = 0;
  stats.qnodes = 0;
  stats.ttHits = 0;
  stats.cutoffs = 0;
  stats.score = 0;
  stats.bestMove = -1;
  stats.completedDepth = 0;
  stats.elapsedMs = 0.0;
}

static inline int terminalWinner(const Position& p) {
  if (p.bluePieces == 0) return RED;
  if (p.redPieces == 0) return BLUE;
  if (p.neutral == 0) return p.blueTerritory > p.redTerritory ? BLUE : RED;
  if (p.consecutivePasses >= 2) {
    if (p.blueTerritory != p.redTerritory) return p.blueTerritory > p.redTerritory ? BLUE : RED;
    if (p.bluePieces != p.redPieces) return p.bluePieces > p.redPieces ? BLUE : RED;
    return 0;
  }
  return 2;
}

static int generateMoves(const Position& p, int side, int capturesOnly, int* out) {
  int count = 0;
  for (int from = 0; from < N; ++from) {
    int piece = p.pieces[from];
    if (!piece || ownerOf(piece) != side) continue;
    for (int i = 0; i < neighborCount[from]; ++i) {
      int to = neighbors[from][i];
      int target = p.pieces[to];
      if (!target) {
        if (!capturesOnly) out[count++] = encodeMove(from, to);
      } else if (ownerOf(target) != side && beats(typeOf(piece), typeOf(target))) {
        out[count++] = encodeMove(from, to);
      }
    }
  }
  return count;
}

static inline int hasAnyLegalMove(const Position& p, int side) {
  for (int from = 0; from < N; ++from) {
    int piece = p.pieces[from];
    if (!piece || ownerOf(piece) != side) continue;
    for (int i = 0; i < neighborCount[from]; ++i) {
      int target = p.pieces[neighbors[from][i]];
      if (!target || (ownerOf(target) != side && beats(typeOf(piece), typeOf(target)))) return 1;
    }
  }
  return 0;
}

static inline Undo makeMove(Position& p, int move) {
  Undo u;
  u.move = move;
  u.captured = 0;
  u.claimed = 0;
  u.side = p.side;
  u.bluePieces = p.bluePieces;
  u.redPieces = p.redPieces;
  u.blueTerritory = p.blueTerritory;
  u.redTerritory = p.redTerritory;
  u.neutral = p.neutral;
  u.ply = p.ply;
  u.consecutivePasses = p.consecutivePasses;
  u.hash = p.hash;

  if (move < 0) {
    p.hash ^= zPass[p.consecutivePasses >= 2 ? 2 : p.consecutivePasses];
    p.side = -p.side;
    p.hash ^= zSide;
    ++p.ply;
    ++p.consecutivePasses;
    p.hash ^= zPass[p.consecutivePasses >= 2 ? 2 : p.consecutivePasses];
    return u;
  }

  int from = moveFrom(move), to = moveTo(move);
  int moving = p.pieces[from];
  int captured = p.pieces[to];
  u.captured = captured;

  p.hash ^= zPiece[from][pieceZIndex(moving)];
  if (captured) p.hash ^= zPiece[to][pieceZIndex(captured)];
  p.hash ^= zPiece[to][pieceZIndex(moving)];

  p.pieces[from] = 0;
  p.pieces[to] = moving;

  if (captured > 0) --p.bluePieces;
  else if (captured < 0) --p.redPieces;

  if (p.territory[to] == 0) {
    p.territory[to] = p.side;
    u.claimed = p.side;
    --p.neutral;
    if (p.side == BLUE) ++p.blueTerritory;
    else ++p.redTerritory;
    p.hash ^= zTerr[to][p.side == BLUE ? 0 : 1];
  }

  p.hash ^= zPass[p.consecutivePasses >= 2 ? 2 : p.consecutivePasses];
  p.side = -p.side;
  p.hash ^= zSide;
  ++p.ply;
  p.consecutivePasses = 0;
  p.hash ^= zPass[0];
  return u;
}

static inline void undoMove(Position& p, const Undo& u) {
  if (u.move >= 0) {
    int from = moveFrom(u.move), to = moveTo(u.move);
    p.pieces[from] = p.pieces[to];
    p.pieces[to] = u.captured;
    if (u.claimed) p.territory[to] = 0;
  }
  p.side = u.side;
  p.bluePieces = u.bluePieces;
  p.redPieces = u.redPieces;
  p.blueTerritory = u.blueTerritory;
  p.redTerritory = u.redTerritory;
  p.neutral = u.neutral;
  p.ply = u.ply;
  p.consecutivePasses = u.consecutivePasses;
  p.hash = u.hash;
}

static int squareThreatened(const Position& p, int square, int side, int type, int removedSquare) {
  for (int i = 0; i < neighborCount[square]; ++i) {
    int sq = neighbors[square][i];
    if (sq == removedSquare) continue;
    int enemy = p.pieces[sq];
    if (enemy && ownerOf(enemy) == -side && beats(typeOf(enemy), type)) return 1;
  }
  return 0;
}

static int nearestPreyDistance(const Position& p, int square, int side, int type) {
  int best = 99;
  for (int target = 0; target < N; ++target) {
    int enemy = p.pieces[target];
    if (!enemy || ownerOf(enemy) != -side || !beats(type, typeOf(enemy))) continue;
    int distance = imax(iabs(rowOf(square) - rowOf(target)), iabs(colOf(square) - colOf(target)));
    if (distance < best) best = distance;
  }
  return best;
}

static TacticalStats tacticalStats(const Position& p, int side) {
  TacticalStats s = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  int types[4] = {0, 0, 0, 0};
  uint8_t preySeen[N];
  for (int i = 0; i < N; ++i) preySeen[i] = 0;

  for (int from = 0; from < N; ++from) {
    int piece = p.pieces[from];
    if (!piece || ownerOf(piece) != side) continue;
    int type = typeOf(piece);
    ++types[type];
    int pieceThreatened = squareThreatened(p, from, side, type, -1);
    if (pieceThreatened) ++s.threatened;

    int preyDistance = nearestPreyDistance(p, from, side, type);
    if (preyDistance < 99) s.huntPressure += 9 - preyDistance;

    for (int i = 0; i < neighborCount[from]; ++i) {
      int to = neighbors[from][i];
      int target = p.pieces[to];
      int legal = !target || (ownerOf(target) != side && beats(type, typeOf(target)));
      if (!legal) continue;

      ++s.mobility;
      int safe = !squareThreatened(p, to, side, type, target ? to : -1);
      if (safe) {
        ++s.safeMobility;
        if (pieceThreatened) ++s.escapeMoves;
      }

      if (!target) {
        if (p.territory[to] == 0) {
          ++s.neutralMoves;
          if (safe) ++s.safeNeutralMoves;
        }
      } else {
        ++s.preyEdges;
        if (!preySeen[to]) {
          preySeen[to] = 1;
          ++s.uniquePrey;
        }
      }
    }
  }

  s.diversity = (types[ROCK] > 0) + (types[PAPER] > 0) + (types[SCISSORS] > 0);
  return s;
}

static int nearestNeutralDistance(const Position& p, int side) {
  if (p.neutral == 0) return 0;
  int total = 0, count = 0;
  for (int sq = 0; sq < N; ++sq) {
    int piece = p.pieces[sq];
    if (!piece || ownerOf(piece) != side) continue;
    int r = rowOf(sq), c = colOf(sq), best = 99;
    for (int target = 0; target < N; ++target) {
      if (p.territory[target] != 0 || p.pieces[target] != 0) continue;
      int d = imax(iabs(r - rowOf(target)), iabs(c - colOf(target)));
      if (d < best) best = d;
      if (best <= 1) break;
    }
    total += best;
    ++count;
  }
  return count ? (total * 100) / count : 2000;
}

static int evaluateBlue(const Position& p) {
  int winner = terminalWinner(p);
  if (winner == BLUE) return MATE - p.ply;
  if (winner == RED) return -MATE + p.ply;
  if (winner == 0) return 0;

  TacticalStats blue = tacticalStats(p, BLUE);
  TacticalStats red = tacticalStats(p, RED);
  int territoryDiff = p.blueTerritory - p.redTerritory;
  int pieceDiff = p.bluePieces - p.redPieces;
  int score = territoryDiff * 100 + pieceDiff * 1100;
  score += (red.threatened - blue.threatened) * 220;
  score += (blue.preyEdges - red.preyEdges) * 110;
  score += (blue.uniquePrey - red.uniquePrey) * 80;
  score += (blue.safeNeutralMoves - red.safeNeutralMoves) * 24;
  score += (blue.neutralMoves - red.neutralMoves) * 7;
  score += (blue.safeMobility - red.safeMobility) * 5;
  score += (blue.escapeMoves - red.escapeMoves) * 16;
  score += (blue.mobility - red.mobility) * 2;
  score += (blue.huntPressure - red.huntPressure) * 30;
  score += (blue.diversity - red.diversity) * 48;

  if (p.neutral <= 36) {
    int blueDistance = nearestNeutralDistance(p, BLUE);
    int redDistance = nearestNeutralDistance(p, RED);
    score += ((redDistance - blueDistance) * (p.neutral <= 16 ? 30 : 15)) / 100;
  }
  if (p.neutral <= 20) score += territoryDiff * (20 - p.neutral) * 3;
  return score;
}

static inline int evaluateForSide(const Position& p) {
  int blue = evaluateBlue(p);
  return p.side == BLUE ? blue : -blue;
}

static inline int shouldStop() {
  uint32_t total = stats.nodes + stats.qnodes;
  if (stopSearch) return 1;
  if (total >= nodeLimit) {
    stopSearch = 1;
    return 1;
  }
  if ((total & 511u) == 0u && now_ms() >= deadlineMs) {
    stopSearch = 1;
    return 1;
  }
  return 0;
}

static inline TTEntry* probeTT(uint64_t key) {
  return &tt[(uint32_t)(key ^ (key >> 32)) & (TT_SIZE - 1)];
}

static inline int scoreToTT(int score, int ply) {
  if (score > MATE - MAX_PLY) return score + ply;
  if (score < -MATE + MAX_PLY) return score - ply;
  return score;
}

static inline int scoreFromTT(int score, int ply) {
  if (score > MATE - MAX_PLY) return score - ply;
  if (score < -MATE + MAX_PLY) return score + ply;
  return score;
}

static inline int isKiller(int move, int ply) {
  if (ply >= MAX_PLY) return 0;
  return killers[ply][0] == move || killers[ply][1] == move;
}

static inline void recordKiller(int move, int ply) {
  if (ply >= MAX_PLY) return;
  if (killers[ply][0] != move) {
    killers[ply][1] = killers[ply][0];
    killers[ply][0] = move;
  }
}

static int moveOrderScore(const Position& p, int move, int tableMove, int ply) {
  if (move == tableMove) return 2000000000;
  int from = moveFrom(move), to = moveTo(move);
  int moving = p.pieces[from], target = p.pieces[to];
  int side = ownerOf(moving), type = typeOf(moving);
  int score = 0;
  if (target) score += 1010000;
  if (p.territory[to] == 0) score += 90000;
  if (isKiller(move, ply)) score += 45000;
  score += historyTable[colorIndex(side)][move];

  int threats = 0, prey = 0, neutralAdjacent = 0;
  for (int i = 0; i < neighborCount[to]; ++i) {
    int sq = neighbors[to][i];
    int adjacent = p.pieces[sq];
    if (!adjacent) {
      if (p.territory[sq] == 0) ++neutralAdjacent;
    } else if (ownerOf(adjacent) == -side) {
      if (beats(typeOf(adjacent), type)) ++threats;
      if (beats(type, typeOf(adjacent))) ++prey;
    }
  }
  score += prey * 7000 + neutralAdjacent * 250 - threats * 12000;
  return score;
}

static inline int moveIsTactical(const Position& p, int move) {
  int from = moveFrom(move), to = moveTo(move);
  int moving = p.pieces[from], side = ownerOf(moving), type = typeOf(moving);
  if (p.pieces[to]) return 1;
  if (squareThreatened(p, from, side, type, -1)) return 1;
  for (int i = 0; i < neighborCount[to]; ++i) {
    int enemy = p.pieces[neighbors[to][i]];
    if (enemy && ownerOf(enemy) == -side && beats(type, typeOf(enemy))) return 1;
  }
  return 0;
}

static void orderMoves(const Position& p, int* moves, int count, int tableMove, int ply) {
  int scores[MAX_MOVES];
  for (int i = 0; i < count; ++i) scores[i] = moveOrderScore(p, moves[i], tableMove, ply);
  for (int i = 1; i < count; ++i) {
    int move = moves[i], score = scores[i], j = i - 1;
    while (j >= 0 && scores[j] < score) {
      moves[j + 1] = moves[j];
      scores[j + 1] = scores[j];
      --j;
    }
    moves[j + 1] = move;
    scores[j + 1] = score;
  }
}

static int quiescence(Position& p, int alpha, int beta, int ply, int depthLeft);
static int search(Position& p, int depth, int alpha, int beta, int ply, int pvNode);

static int generateQuiescenceMoves(const Position& p, int* out) {
  int count = generateMoves(p, p.side, 1, out);
  for (int from = 0; from < N; ++from) {
    int piece = p.pieces[from];
    if (!piece || ownerOf(piece) != p.side) continue;
    int type = typeOf(piece);
    if (!squareThreatened(p, from, p.side, type, -1)) continue;
    for (int i = 0; i < neighborCount[from]; ++i) {
      int to = neighbors[from][i];
      if (p.pieces[to]) continue;
      if (!squareThreatened(p, to, p.side, type, -1)) out[count++] = encodeMove(from, to);
    }
  }
  return count;
}

static int quiescence(Position& p, int alpha, int beta, int ply, int depthLeft) {
  ++stats.qnodes;
  if (shouldStop()) return 0;
  int winner = terminalWinner(p);
  if (winner != 2) {
    if (winner == 0) return 0;
    return winner == p.side ? MATE - ply : -MATE + ply;
  }

  int standPat = evaluateForSide(p);
  if (standPat >= beta) return standPat;
  if (standPat > alpha) alpha = standPat;

  int moves[MAX_MOVES];
  int count = generateQuiescenceMoves(p, moves);
  if (!count && !hasAnyLegalMove(p, p.side)) {
    Undo u = makeMove(p, -1);
    int score = -quiescence(p, -beta, -alpha, ply + 1, depthLeft - 1);
    undoMove(p, u);
    return score;
  }
  if (depthLeft <= 0 || !count) return standPat;
  orderMoves(p, moves, count, -1, ply);

  for (int i = 0; i < count; ++i) {
    Undo u = makeMove(p, moves[i]);
    int score = -quiescence(p, -beta, -alpha, ply + 1, depthLeft - 1);
    undoMove(p, u);
    if (stopSearch) return 0;
    if (score >= beta) return score;
    if (score > alpha) alpha = score;
  }
  return alpha;
}

static int search(Position& p, int depth, int alpha, int beta, int ply, int pvNode) {
  ++stats.nodes;
  if (shouldStop()) return 0;

  int winner = terminalWinner(p);
  if (winner != 2) {
    if (winner == 0) return 0;
    return winner == p.side ? MATE - ply : -MATE + ply;
  }
  if (depth <= 0) return quiescence(p, alpha, beta, ply, qDepthLimit);

  int originalAlpha = alpha;
  TTEntry* entry = probeTT(p.hash);
  int tableMove = -1;
  if (entry->key == p.hash) {
    ++stats.ttHits;
    tableMove = entry->move;
    if (entry->depth >= depth && !pvNode) {
      int ttScore = scoreFromTT(entry->score, ply);
      if (entry->flag == TT_EXACT) return ttScore;
      if (entry->flag == TT_LOWER && ttScore >= beta) return ttScore;
      if (entry->flag == TT_UPPER && ttScore <= alpha) return ttScore;
    }
  }

  int moves[MAX_MOVES];
  int count = generateMoves(p, p.side, 0, moves);
  if (!count) {
    Undo u = makeMove(p, -1);
    int score = -search(p, depth - 1, -beta, -alpha, ply + 1, pvNode);
    undoMove(p, u);
    return score;
  }
  orderMoves(p, moves, count, tableMove, ply);

  int bestMove = moves[0], bestScore = -INF, first = 1;
  for (int i = 0; i < count; ++i) {
    int move = moves[i], to = moveTo(move);
    int isCapture = p.pieces[to] != 0;
    int isClaim = p.territory[to] == 0;
    int quiet = !isCapture && !isClaim;
    int tactical = moveIsTactical(p, move);
    Undo u = makeMove(p, move);
    int reduction = 0;
    if (useLMR && !pvNode && depth >= 3 && i >= 4 && quiet && !tactical && !isKiller(move, ply)) {
      reduction = (depth >= 6 && i >= 10) ? 2 : 1;
    }

    int score;
    if (first) {
      score = -search(p, depth - 1, -beta, -alpha, ply + 1, pvNode);
      first = 0;
    } else {
      score = -search(p, depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, 0);
      if (!stopSearch && reduction && score > alpha) {
        score = -search(p, depth - 1, -alpha - 1, -alpha, ply + 1, 0);
      }
      if (!stopSearch && score > alpha && score < beta) {
        score = -search(p, depth - 1, -beta, -alpha, ply + 1, pvNode);
      }
    }
    undoMove(p, u);
    if (stopSearch) return 0;

    if (score > bestScore) { bestScore = score; bestMove = move; }
    if (score > alpha) {
      alpha = score;
    }
    if (alpha >= beta) {
      ++stats.cutoffs;
      if (quiet) {
        recordKiller(move, ply);
        int* h = &historyTable[colorIndex(p.side)][move];
        int bonus = depth * depth * 16;
        *h += bonus - (*h * bonus) / 1000000;
      }
      break;
    }
  }

  uint8_t flag = TT_EXACT;
  if (bestScore <= originalAlpha) flag = TT_UPPER;
  else if (bestScore >= beta) flag = TT_LOWER;
  if (entry->key != p.hash || entry->generation != generation || entry->depth <= depth) {
    entry->key = p.hash;
    entry->score = scoreToTT(bestScore, ply);
    entry->move = (int16_t)bestMove;
    entry->depth = (int8_t)depth;
    entry->flag = flag;
    entry->generation = generation;
  }
  return bestScore;
}

static int searchRoot(Position& p, int depth, int alpha, int beta, int* outScore) {
  int originalAlpha = alpha;
  TTEntry* entry = probeTT(p.hash);
  int tableMove = entry->key == p.hash ? entry->move : -1;
  int moves[MAX_MOVES];
  int count = generateMoves(p, p.side, 0, moves);
  if (!count) { *outScore = 0; return -1; }
  orderMoves(p, moves, count, tableMove, 0);

  int bestMove = moves[0], bestScore = -INF, first = 1;
  for (int i = 0; i < count; ++i) {
    if (shouldStop()) break;
    int move = moves[i];
    Undo u = makeMove(p, move);
    int score;
    if (first) {
      score = -search(p, depth - 1, -beta, -alpha, 1, 1);
      first = 0;
    } else {
      score = -search(p, depth - 1, -alpha - 1, -alpha, 1, 0);
      if (!stopSearch && score > alpha && score < beta) {
        score = -search(p, depth - 1, -beta, -alpha, 1, 1);
      }
    }
    undoMove(p, u);
    if (stopSearch) break;
    if (score > bestScore) { bestScore = score; bestMove = move; }
    if (score > alpha) alpha = score;
    if (alpha >= beta) break;
  }

  if (!stopSearch) {
    uint8_t flag = TT_EXACT;
    if (bestScore <= originalAlpha) flag = TT_UPPER;
    else if (bestScore >= beta) flag = TT_LOWER;
    entry->key = p.hash;
    entry->score = bestScore;
    entry->move = (int16_t)bestMove;
    entry->depth = (int8_t)depth;
    entry->flag = flag;
    entry->generation = generation;
  }
  *outScore = bestScore;
  return bestMove;
}

extern "C" __attribute__((export_name("init_engine"))) void init_engine() {
  if (initialized) return;
  initZobrist();
  initNeighbors();
  for (int i = 0; i < TT_SIZE; ++i) {
    tt[i].key = 0;
    tt[i].move = -1;
    tt[i].depth = -1;
    tt[i].generation = 0;
  }
  for (int side = 0; side < 2; ++side) for (int move = 0; move < N * N; ++move) historyTable[side][move] = 0;
  for (int p = 0; p < MAX_PLY; ++p) killers[p][0] = killers[p][1] = -1;
  initialized = 1;
}

extern "C" __attribute__((export_name("clear_position"))) void clear_position() {
  init_engine();
  for (int i = 0; i < N; ++i) { pos.pieces[i] = 0; pos.territory[i] = 0; }
  pos.side = BLUE;
  pos.bluePieces = pos.redPieces = 0;
  pos.blueTerritory = pos.redTerritory = 0;
  pos.neutral = N;
  pos.ply = 0;
  pos.consecutivePasses = 0;
  pos.hash = 0;
}

extern "C" __attribute__((export_name("set_piece"))) void set_piece(int square, int piece) {
  if (square >= 0 && square < N && piece >= -3 && piece <= 3) pos.pieces[square] = (int8_t)piece;
}

extern "C" __attribute__((export_name("set_territory"))) void set_territory(int square, int owner) {
  if (square >= 0 && square < N && owner >= -1 && owner <= 1) pos.territory[square] = (int8_t)owner;
}

extern "C" __attribute__((export_name("set_side"))) void set_side(int side) {
  pos.side = side == RED ? RED : BLUE;
}

extern "C" __attribute__((export_name("finalize_position"))) void finalize_position() {
  pos.bluePieces = pos.redPieces = 0;
  pos.blueTerritory = pos.redTerritory = 0;
  pos.neutral = N;
  for (int i = 0; i < N; ++i) {
    if (pos.pieces[i] > 0) ++pos.bluePieces;
    else if (pos.pieces[i] < 0) ++pos.redPieces;
    if (pos.territory[i] == BLUE) { ++pos.blueTerritory; --pos.neutral; }
    else if (pos.territory[i] == RED) { ++pos.redTerritory; --pos.neutral; }
  }
  pos.hash = computeHash(pos);
}

extern "C" __attribute__((export_name("search_best_move"))) int search_best_move(int maxDepth, double timeMs, uint32_t maxNodes) {
  init_engine();
  ++generation;
  clearStats();
  stopSearch = 0;
  deadlineMs = now_ms() + (timeMs <= 0 ? 1.0e12 : timeMs);
  nodeLimit = maxNodes == 0 ? 0xffffffffu : maxNodes;
  maxDepth = maxDepth < 1 ? 1 : maxDepth > 64 ? 64 : maxDepth;
  for (int side = 0; side < 2; ++side) {
    for (int move = 0; move < N * N; ++move) historyTable[side][move] /= 2;
  }
  double started = now_ms();

  int rootMoves[MAX_MOVES];
  int rootCount = generateMoves(pos, pos.side, 0, rootMoves);
  if (!rootCount) {
    Undo u = makeMove(pos, -1);
    stats.score = -search(pos, maxDepth - 1, -INF, INF, 1, 1);
    undoMove(pos, u);
    stats.bestMove = -1;
    stats.completedDepth = maxDepth;
    stats.elapsedMs = now_ms() - started;
    return -1;
  }
  stats.bestMove = rootMoves[0];
  int previousScore = 0;

  for (int depth = 1; depth <= maxDepth; ++depth) {
    if (shouldStop()) break;
    int alpha = -INF, beta = INF;
    if (depth >= 4) {
      int window = 90 + depth * 20;
      alpha = previousScore - window;
      beta = previousScore + window;
    }
    int score = 0;
    int move = searchRoot(pos, depth, alpha, beta, &score);
    if (stopSearch) break;
    if (score <= alpha || score >= beta) {
      move = searchRoot(pos, depth, -INF, INF, &score);
      if (stopSearch) break;
    }
    stats.bestMove = move;
    stats.score = score;
    stats.completedDepth = depth;
    previousScore = score;
  }
  stats.elapsedMs = now_ms() - started;
  return stats.bestMove;
}

extern "C" __attribute__((export_name("set_qdepth"))) void set_qdepth(int value) { qDepthLimit = value < 0 ? 0 : value > 8 ? 8 : value; }
extern "C" __attribute__((export_name("set_lmr"))) void set_lmr(int enabled) { useLMR = enabled ? 1 : 0; }
extern "C" __attribute__((export_name("clear_tt"))) void clear_tt() {
  for (int i = 0; i < TT_SIZE; ++i) { tt[i].key = 0; tt[i].move = -1; tt[i].depth = -1; tt[i].generation = 0; }
  for (int side = 0; side < 2; ++side) for (int move = 0; move < N * N; ++move) historyTable[side][move] = 0;
  for (int ply = 0; ply < MAX_PLY; ++ply) killers[ply][0] = killers[ply][1] = -1;
}
extern "C" __attribute__((export_name("get_nodes"))) uint32_t get_nodes() { return stats.nodes; }
extern "C" __attribute__((export_name("get_qnodes"))) uint32_t get_qnodes() { return stats.qnodes; }
extern "C" __attribute__((export_name("get_tt_hits"))) uint32_t get_tt_hits() { return stats.ttHits; }
extern "C" __attribute__((export_name("get_cutoffs"))) uint32_t get_cutoffs() { return stats.cutoffs; }
extern "C" __attribute__((export_name("get_score"))) int get_score() { return stats.score; }
extern "C" __attribute__((export_name("get_depth"))) int get_depth() { return stats.completedDepth; }
extern "C" __attribute__((export_name("get_elapsed_ms"))) double get_elapsed_ms() { return stats.elapsedMs; }
extern "C" __attribute__((export_name("get_blue_territory"))) int get_blue_territory() { return pos.blueTerritory; }
extern "C" __attribute__((export_name("get_red_territory"))) int get_red_territory() { return pos.redTerritory; }
