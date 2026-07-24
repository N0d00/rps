#include <stdint.h>

extern "C" __attribute__((import_module("env"), import_name("now_ms"))) double now_ms();

struct Bitboard {
  uint64_t lo;
  uint64_t hi;

  inline bool operator!() const { return !lo && !hi; }
  inline operator bool() const { return lo || hi; }
};

inline Bitboard operator|(Bitboard a, Bitboard b) { return {a.lo | b.lo, a.hi | b.hi}; }
inline Bitboard operator&(Bitboard a, Bitboard b) { return {a.lo & b.lo, a.hi & b.hi}; }
inline Bitboard operator~(Bitboard a) { return {~a.lo, ~a.hi}; }
inline Bitboard& operator|=(Bitboard& a, Bitboard b) { a.lo |= b.lo; a.hi |= b.hi; return a; }
inline Bitboard& operator&=(Bitboard& a, Bitboard b) { a.lo &= b.lo; a.hi &= b.hi; return a; }

static inline void bb_clear_bit(Bitboard& bb, int square) {
  if (square < 64) bb.lo &= ~(1ULL << square);
  else bb.hi &= ~(1ULL << (square - 64));
}

static inline void bb_set_bit(Bitboard& bb, int square) {
  if (square < 64) bb.lo |= (1ULL << square);
  else bb.hi |= (1ULL << (square - 64));
}

static const int SIZE = 9;
static const int N = 81;
static const int BLUE = 1;
static const int RED = -1;
static const int ROCK = 1;
static const int PAPER = 2;
static const int SCISSORS = 3;
static const int MATE = 10000000;
static const int INF = 1000000000;
static const int MAX_MOVES = 64;
static const int MAX_PLY = 128;
static const int TT_BITS = 17;
static const int TT_SIZE = 1 << TT_BITS;
static const uint64_t MASK64 = ~uint64_t(0);

static const Bitboard BOARD_MASK = {0xFFFFFFFFFFFFFFFFULL, 0x1FFFFULL};

// Tunable Evaluation Weights (from V2.1 baseline)
static const int TERRITORY_W = 80;
static const int PIECE_W = 1800;
static const int THREATENED_W = 320;
static const int PREY_W = 180;
static const int SAFE_NEUTRAL_W = 24;
static const int NEUTRAL_W = 9;
static const int MOBILITY_W = 3;
static const int DIVERSITY_W = 42;
static const int PROX_FAR_W = 10;
static const int PROX_NEAR_W = 20;
static const int LATE_TERR_W = 2;

enum TTFlag : uint8_t { TT_EXACT = 0, TT_LOWER = 1, TT_UPPER = 2 };

struct Position {
  int8_t pieces[N];
  int8_t territory[N];
  Bitboard blue_rock;
  Bitboard blue_paper;
  Bitboard blue_scissors;
  Bitboard red_rock;
  Bitboard red_paper;
  Bitboard red_scissors;
  Bitboard territory_blue;
  Bitboard territory_red;
  int8_t side;
  int8_t bluePieces;
  int8_t redPieces;
  int8_t blueTerritory;
  int8_t redTerritory;
  int8_t neutral;
  uint16_t ply;
  uint8_t consecutivePasses;
  int lastMove;
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
  int lastMove;
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
  int safeNeutralMoves;
  int neutralMoves;
  int mobility;
  int diversity;
};

static Position pos;
static Stats stats;
static TTEntry tt[TT_SIZE];
static int32_t historyTable[2][N * N];
static int16_t killers[MAX_PLY][2];
static int countermoves[N * N];
static uint64_t zPiece[N][6];
static uint64_t zTerr[N][2];
static uint64_t zSide;
static uint64_t rngState = 0x9e3779b97f4a7c15ULL;
static uint8_t generation = 0;
static int stopSearch = 0;
static double deadlineMs = 0.0;
static uint32_t nodeLimit = 0xffffffffu;
static int qDepthLimit = 4;
static int useLMR = 1;
static int initialized = 0;
static Bitboard neighbors[N];

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
}

static void initNeighbors() {
  for (int sq = 0; sq < N; ++sq) {
    neighbors[sq] = {0, 0};
    int r = rowOf(sq), c = colOf(sq);
    for (int dr = -1; dr <= 1; ++dr) {
      for (int dc = -1; dc <= 1; ++dc) {
        if (dr == 0 && dc == 0) continue;
        int nr = r + dr, nc = c + dc;
        if (nr >= 0 && nr < SIZE && nc >= 0 && nc < SIZE) {
          bb_set_bit(neighbors[sq], nr * SIZE + nc);
        }
      }
    }
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

static inline int pop_lsb(Bitboard& bb) {
  if (bb.lo) {
    int idx = __builtin_ctzll(bb.lo);
    bb.lo &= ~(1ULL << idx);
    return idx;
  }
  if (bb.hi) {
    int idx = __builtin_ctzll(bb.hi);
    bb.hi &= ~(1ULL << idx);
    return idx + 64;
  }
  return -1;
}

static inline int popcount128(Bitboard bb) {
  return __builtin_popcountll(bb.lo) + __builtin_popcountll(bb.hi);
}

static int generateMoves(const Position& p, int side, int capturesOnly, int* out) {
  int count = 0;
  Bitboard occupied_blue = p.blue_rock | p.blue_paper | p.blue_scissors;
  Bitboard occupied_red = p.red_rock | p.red_paper | p.red_scissors;
  Bitboard occupied = occupied_blue | occupied_red;
  Bitboard my_pieces = (side == BLUE) ? occupied_blue : occupied_red;

  Bitboard temp_pieces = my_pieces;
  while (temp_pieces) {
    int from = pop_lsb(temp_pieces);
    int moving = p.pieces[from];
    int type = typeOf(moving);
    Bitboard nb = neighbors[from];

    // Quiet moves
    if (!capturesOnly) {
      Bitboard quiet = nb & ~occupied;
      while (quiet) {
        int to = pop_lsb(quiet);
        if (count < MAX_MOVES) out[count++] = encodeMove(from, to);
      }
    }

    // Captures
    Bitboard enemy = (side == BLUE) ? occupied_red : occupied_blue;
    Bitboard prey = {0, 0};
    if (type == ROCK) prey = (side == BLUE) ? p.red_scissors : p.blue_scissors;
    else if (type == PAPER) prey = (side == BLUE) ? p.red_rock : p.blue_rock;
    else if (type == SCISSORS) prey = (side == BLUE) ? p.red_paper : p.blue_paper;

    Bitboard captures = nb & enemy & prey;
    while (captures) {
      int to = pop_lsb(captures);
      if (count < MAX_MOVES) out[count++] = encodeMove(from, to);
    }
  }
  return count;
}

static inline void set_bitboard_piece(Position& p, int square, int piece) {
  bb_clear_bit(p.blue_rock, square);
  bb_clear_bit(p.blue_paper, square);
  bb_clear_bit(p.blue_scissors, square);
  bb_clear_bit(p.red_rock, square);
  bb_clear_bit(p.red_paper, square);
  bb_clear_bit(p.red_scissors, square);

  if (piece == BLUE * ROCK) bb_set_bit(p.blue_rock, square);
  else if (piece == BLUE * PAPER) bb_set_bit(p.blue_paper, square);
  else if (piece == BLUE * SCISSORS) bb_set_bit(p.blue_scissors, square);
  else if (piece == RED * ROCK) bb_set_bit(p.red_rock, square);
  else if (piece == RED * PAPER) bb_set_bit(p.red_paper, square);
  else if (piece == RED * SCISSORS) bb_set_bit(p.red_scissors, square);
}

static inline void set_bitboard_territory(Position& p, int square, int owner) {
  bb_clear_bit(p.territory_blue, square);
  bb_clear_bit(p.territory_red, square);
  if (owner == BLUE) bb_set_bit(p.territory_blue, square);
  else if (owner == RED) bb_set_bit(p.territory_red, square);
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
  u.lastMove = p.lastMove;
  u.hash = p.hash;

  if (move < 0) {
    p.side = -p.side;
    p.hash ^= zSide;
    ++p.ply;
    ++p.consecutivePasses;
    p.lastMove = -1;
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
  set_bitboard_piece(p, from, 0);
  set_bitboard_piece(p, to, moving);

  if (captured > 0) --p.bluePieces;
  else if (captured < 0) --p.redPieces;

  if (p.territory[to] == 0) {
    p.territory[to] = p.side;
    u.claimed = p.side;
    --p.neutral;
    if (p.side == BLUE) {
      ++p.blueTerritory;
      bb_set_bit(p.territory_blue, to);
    } else {
      ++p.redTerritory;
      bb_set_bit(p.territory_red, to);
    }
    p.hash ^= zTerr[to][p.side == BLUE ? 0 : 1];
  }

  p.side = -p.side;
  p.hash ^= zSide;
  ++p.ply;
  p.consecutivePasses = 0;
  p.lastMove = move;
  return u;
}

static inline void undoMove(Position& p, const Undo& u) {
  if (u.move >= 0) {
    int from = moveFrom(u.move), to = moveTo(u.move);
    int moving = p.pieces[to];
    p.pieces[from] = moving;
    p.pieces[to] = u.captured;
    set_bitboard_piece(p, from, moving);
    set_bitboard_piece(p, to, u.captured);
    if (u.claimed) {
      p.territory[to] = 0;
      if (u.claimed == BLUE) bb_clear_bit(p.territory_blue, to);
      else bb_clear_bit(p.territory_red, to);
    }
  }
  p.side = u.side;
  p.bluePieces = u.bluePieces;
  p.redPieces = u.redPieces;
  p.blueTerritory = u.blueTerritory;
  p.redTerritory = u.redTerritory;
  p.neutral = u.neutral;
  p.ply = u.ply;
  p.consecutivePasses = u.consecutivePasses;
  p.lastMove = u.lastMove;
  p.hash = u.hash;
}

static TacticalStats tacticalStats(const Position& p, int side) {
  TacticalStats s = {0, 0, 0, 0, 0, 0};
  int types[4] = {0, 0, 0, 0};

  Bitboard occupied_blue = p.blue_rock | p.blue_paper | p.blue_scissors;
  Bitboard occupied_red = p.red_rock | p.red_paper | p.red_scissors;
  Bitboard occupied = occupied_blue | occupied_red;
  Bitboard my_pieces = (side == BLUE) ? occupied_blue : occupied_red;

  Bitboard temp_pieces = my_pieces;
  while (temp_pieces) {
    int from = pop_lsb(temp_pieces);
    int moving = p.pieces[from];
    int type = typeOf(moving);
    ++types[type];

    Bitboard nb = neighbors[from];
    Bitboard enemy_predators = {0, 0};
    Bitboard enemy_prey = {0, 0};
    if (type == ROCK) {
      enemy_predators = (side == BLUE) ? p.red_paper : p.blue_paper;
      enemy_prey = (side == BLUE) ? p.red_scissors : p.blue_scissors;
    } else if (type == PAPER) {
      enemy_predators = (side == BLUE) ? p.red_scissors : p.blue_scissors;
      enemy_prey = (side == BLUE) ? p.red_rock : p.blue_rock;
    } else if (type == SCISSORS) {
      enemy_predators = (side == BLUE) ? p.red_rock : p.blue_rock;
      enemy_prey = (side == BLUE) ? p.red_paper : p.blue_paper;
    }

    if (nb & enemy_predators) ++s.threatened;

    int prey_count = popcount128(nb & enemy_prey);
    s.preyEdges += prey_count;

    Bitboard quiet = nb & ~occupied;
    s.mobility += popcount128(quiet) + prey_count;

    Bitboard neutral_adjacent = nb & ~(p.territory_blue | p.territory_red) & ~occupied;
    s.neutralMoves += popcount128(neutral_adjacent);

    Bitboard temp_neutral = neutral_adjacent;
    while (temp_neutral) {
      int to = pop_lsb(temp_neutral);
      if (!(neighbors[to] & enemy_predators)) {
        ++s.safeNeutralMoves;
      }
    }
  }

  s.diversity = (types[ROCK] > 0) + (types[PAPER] > 0) + (types[SCISSORS] > 0);
  return s;
}

static int nearestNeutralDistance(const Position& p, int side) {
  if (p.neutral == 0) return 0;
  int total = 0, count = 0;

  Bitboard occupied_blue = p.blue_rock | p.blue_paper | p.blue_scissors;
  Bitboard occupied_red = p.red_rock | p.red_paper | p.red_scissors;
  Bitboard occupied = occupied_blue | occupied_red;
  Bitboard my_pieces = (side == BLUE) ? occupied_blue : occupied_red;
  Bitboard neutral_board = ~(p.territory_blue | p.territory_red) & ~occupied & BOARD_MASK;

  Bitboard temp_pieces = my_pieces;
  while (temp_pieces) {
    int sq = pop_lsb(temp_pieces);
    int r = rowOf(sq), c = colOf(sq), best = 99;

    Bitboard temp_neutral = neutral_board;
    while (temp_neutral) {
      int target = pop_lsb(temp_neutral);
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
  int score = territoryDiff * TERRITORY_W + pieceDiff * PIECE_W;
  score += (red.threatened - blue.threatened) * THREATENED_W;
  score += (blue.preyEdges - red.preyEdges) * PREY_W;
  score += (blue.safeNeutralMoves - red.safeNeutralMoves) * SAFE_NEUTRAL_W;
  score += (blue.neutralMoves - red.neutralMoves) * NEUTRAL_W;
  score += (blue.mobility - red.mobility) * MOBILITY_W;
  score += (blue.diversity - red.diversity) * DIVERSITY_W;

  if (p.neutral <= 36) {
    int blueDistance = nearestNeutralDistance(p, BLUE);
    int redDistance = nearestNeutralDistance(p, RED);
    score += ((redDistance - blueDistance) * (p.neutral <= 16 ? PROX_NEAR_W : PROX_FAR_W)) / 100;
  }
  if (p.neutral <= 20) score += territoryDiff * (20 - p.neutral) * LATE_TERR_W;
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
  if ((total & 2047u) == 0u && now_ms() >= deadlineMs) {
    stopSearch = 1;
    return 1;
  }
  return 0;
}

static inline TTEntry* probeTT(uint64_t key) {
  return &tt[(uint32_t)(key ^ (key >> 32)) & (TT_SIZE - 1)];
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

  if (target) {
    // MVV-LVA Capture Ordering
    int victimVal = typeOf(target) * 100;
    int attackerVal = type;
    score += 1010000 + victimVal - attackerVal;
  }
  if (p.territory[to] == 0) score += 90000;
  if (isKiller(move, ply)) score += 45000;
  
  // Countermove Heuristic
  int lastMove = (ply > 0) ? p.lastMove : -1;
  if (lastMove >= 0 && move == countermoves[lastMove]) score += 40000;

  score += historyTable[colorIndex(side)][move];

  int r = rowOf(to), c = colOf(to), threats = 0, prey = 0, neutralAdjacent = 0;
  Bitboard nb = neighbors[to];
  
  Bitboard enemy_predators = {0, 0};
  Bitboard enemy_prey = {0, 0};
  if (type == ROCK) {
    enemy_predators = (side == BLUE) ? p.red_paper : p.blue_paper;
    enemy_prey = (side == BLUE) ? p.red_scissors : p.blue_scissors;
  } else if (type == PAPER) {
    enemy_predators = (side == BLUE) ? p.red_scissors : p.blue_scissors;
    enemy_prey = (side == BLUE) ? p.red_rock : p.blue_rock;
  } else if (type == SCISSORS) {
    enemy_predators = (side == BLUE) ? p.red_rock : p.blue_rock;
    enemy_prey = (side == BLUE) ? p.red_paper : p.blue_paper;
  }

  threats = popcount128(nb & enemy_predators);
  prey = popcount128(nb & enemy_prey);
  
  Bitboard neutral_mask = ~(p.territory_blue | p.territory_red) & ~(p.blue_rock | p.blue_paper | p.blue_scissors | p.red_rock | p.red_paper | p.red_scissors);
  neutralAdjacent = popcount128(nb & neutral_mask);

  score += prey * 3000 + neutralAdjacent * 500 - threats * 8000;
  return score;
}

static inline int see(const Position& p, int move) {
  int from = moveFrom(move), to = moveTo(move);
  int moving = p.pieces[from], captured = p.pieces[to];
  if (!captured) return 0;

  int side = ownerOf(moving);
  int type = typeOf(moving);
  Bitboard nb = neighbors[to];

  Bitboard enemy_predators = {0, 0};
  if (type == ROCK) enemy_predators = (side == BLUE) ? p.red_paper : p.blue_paper;
  else if (type == PAPER) enemy_predators = (side == BLUE) ? p.red_scissors : p.blue_scissors;
  else if (type == SCISSORS) enemy_predators = (side == BLUE) ? p.red_rock : p.blue_rock;

  // Exclude 'from' square since it becomes empty
  bb_clear_bit(enemy_predators, from);

  if (nb & enemy_predators) {
    return 0; // Exchange is equal or negative
  }
  return PIECE_W; // Profitable capture
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
  if (depthLeft <= 0) return standPat;

  int moves[MAX_MOVES];
  int count = generateMoves(p, p.side, 1, moves);
  if (!count) return standPat;
  orderMoves(p, moves, count, -1, ply);

  for (int i = 0; i < count; ++i) {
    // 1-ply SEE pruning in Quiescence Search
    if (see(p, moves[i]) <= 0) continue;

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
      if (entry->flag == TT_EXACT) return entry->score;
      if (entry->flag == TT_LOWER && entry->score >= beta) return entry->score;
      if (entry->flag == TT_UPPER && entry->score <= alpha) return entry->score;
    }
  }

  // Dynamic Null Move Pruning (Dynamic NMP)
  if (useLMR && !pvNode && depth >= 3) {
    int sidePieces = (p.side == BLUE) ? p.bluePieces : p.redPieces;
    if (sidePieces >= 3 && evaluateForSide(p) >= beta) {
      Undo u = makeMove(p, -1);
      int reduction = 2 + (depth / 6);
      int score = -search(p, depth - 1 - reduction, -beta, -beta + 1, ply + 1, 0);
      undoMove(p, u);
      if (score >= beta) return score;
    }
  }

  // Futility Pruning flag
  int capturesOnly = 0;
  if (depth == 1 && !pvNode && !isKiller(tableMove, ply)) {
    int staticEval = evaluateForSide(p);
    int margin = 150;
    if (staticEval + margin < alpha) {
      capturesOnly = 1;
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

    if (quiet && capturesOnly) continue; // Skip quiet moves due to futility pruning

    Undo u = makeMove(p, move);
    int reduction = 0;
    if (useLMR && !pvNode && depth >= 3 && i >= 4 && quiet && !isKiller(move, ply)) {
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
      if (quiet) {
        int* h = &historyTable[colorIndex(p.side)][move];
        int value = *h + depth * depth;
        *h = value > 1000000 ? 1000000 : value;
      }
    }
    if (alpha >= beta) {
      ++stats.cutoffs;
      if (quiet) recordKiller(move, ply);
      if (ply > 0 && u.move >= 0) {
        countermoves[u.move] = move; // Record countermove
      }
      break;
    }
  }

  uint8_t flag = TT_EXACT;
  if (bestScore <= originalAlpha) flag = TT_UPPER;
  else if (bestScore >= beta) flag = TT_LOWER;
  if (entry->key != p.hash || entry->generation != generation || entry->depth <= depth) {
    entry->key = p.hash;
    entry->score = bestScore;
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
  for (int p = 0; p < MAX_PLY; ++p) killers[p][0] = killers[p][1] = -1;
  for (int i = 0; i < N * N; ++i) countermoves[i] = -1;
  initialized = 1;
}

extern "C" __attribute__((export_name("clear_position"))) void clear_position() {
  init_engine();
  for (int i = 0; i < N; ++i) { pos.pieces[i] = 0; pos.territory[i] = 0; }
  pos.blue_rock = pos.blue_paper = pos.blue_scissors = {0, 0};
  pos.red_rock = pos.red_paper = pos.red_scissors = {0, 0};
  pos.territory_blue = pos.territory_red = {0, 0};
  pos.side = BLUE;
  pos.bluePieces = pos.redPieces = 0;
  pos.blueTerritory = pos.redTerritory = 0;
  pos.neutral = N;
  pos.ply = 0;
  pos.consecutivePasses = 0;
  pos.lastMove = -1;
  pos.hash = 0;
}

extern "C" __attribute__((export_name("set_piece"))) void set_piece(int square, int piece) {
  if (square >= 0 && square < N && piece >= -3 && piece <= 3) {
    pos.pieces[square] = (int8_t)piece;
    set_bitboard_piece(pos, square, piece);
  }
}

extern "C" __attribute__((export_name("set_territory"))) void set_territory(int square, int owner) {
  if (square >= 0 && square < N && owner >= -1 && owner <= 1) {
    pos.territory[square] = (int8_t)owner;
    set_bitboard_territory(pos, square, owner);
  }
}

extern "C" __attribute__((export_name("set_side"))) void set_side(int side) {
  pos.side = side == RED ? RED : BLUE;
}

extern "C" __attribute__((export_name("finalize_position"))) void finalize_position() {
  pos.bluePieces = pos.redPieces = 0;
  pos.blueTerritory = pos.redTerritory = 0;
  pos.neutral = N;
  pos.blue_rock = pos.blue_paper = pos.blue_scissors = {0, 0};
  pos.red_rock = pos.red_paper = pos.red_scissors = {0, 0};
  pos.territory_blue = pos.territory_red = {0, 0};

  for (int i = 0; i < N; ++i) {
    int piece = pos.pieces[i];
    if (piece) {
      set_bitboard_piece(pos, i, piece);
      if (piece > 0) ++pos.bluePieces;
      else ++pos.redPieces;
    }
    int owner = pos.territory[i];
    if (owner == BLUE) {
      bb_set_bit(pos.territory_blue, i);
      ++pos.blueTerritory;
      --pos.neutral;
    } else if (owner == RED) {
      bb_set_bit(pos.territory_red, i);
      ++pos.redTerritory;
      --pos.neutral;
    }
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
  double started = now_ms();

  int rootMoves[MAX_MOVES];
  int rootCount = generateMoves(pos, pos.side, 0, rootMoves);
  if (!rootCount) { stats.bestMove = -1; return -1; }
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
