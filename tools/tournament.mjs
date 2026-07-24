#!/usr/bin/env node

import { availableParallelism } from 'node:os';
import { readFile, writeFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { isMainThread, parentPort, workerData, Worker } from 'node:worker_threads';

const SIZE = 9;
const TYPES = ['rock', 'paper', 'scissors'];
const BEATS = { rock: 'scissors', scissors: 'paper', paper: 'rock' };
const COLORS = ['blue', 'red'];
const ALL_BOTS = [
  { id: 'javascript-minimax', label: 'JavaScript minimax' },
  { id: 'rps-v2-engine', label: 'rps_v2_engine.wasm' },
  { id: 'rps-v2-1-engine', label: 'rps_v2_1_engine.wasm' },
  { id: 'rps-v3-engine', label: 'rps_v3_engine.wasm' },
  { id: 'rps-v4-engine', label: 'rps_v4_engine.wasm' },
  { id: 'rps-v5-engine', label: 'rps_v5_engine.wasm' },
  { id: 'rps-v6-engine', label: 'rps_v6_engine.wasm' },
];
const ROOT = fileURLToPath(new URL('..', import.meta.url));

function emptyCell() {
  return { territory: null, piece: null };
}

function newBoard(layout) {
  const board = Array.from({ length: SIZE }, () => Array.from({ length: SIZE }, emptyCell));
  const blueSetup = layout === 9 ? [
    [3, 0, 'rock'], [3, 1, 'paper'], [3, 2, 'scissors'],
    [4, 0, 'rock'], [4, 1, 'paper'], [4, 2, 'scissors'],
    [5, 0, 'rock'], [5, 1, 'paper'], [5, 2, 'scissors'],
  ] : [
    [3, 1, 'rock'], [3, 2, 'rock'],
    [4, 1, 'paper'], [4, 2, 'paper'],
    [5, 1, 'scissors'], [5, 2, 'scissors'],
  ];
  const redSetup = layout === 9 ? [
    [3, 6, 'scissors'], [3, 7, 'paper'], [3, 8, 'rock'],
    [4, 6, 'scissors'], [4, 7, 'paper'], [4, 8, 'rock'],
    [5, 6, 'scissors'], [5, 7, 'paper'], [5, 8, 'rock'],
  ] : [
    [3, 6, 'scissors'], [3, 7, 'scissors'],
    [4, 6, 'paper'], [4, 7, 'paper'],
    [5, 6, 'rock'], [5, 7, 'rock'],
  ];
  for (const [r, c, type] of blueSetup) board[r][c] = { territory: 'blue', piece: { owner: 'blue', type } };
  for (const [r, c, type] of redSetup) board[r][c] = { territory: 'red', piece: { owner: 'red', type } };
  return board;
}

function inBounds(r, c) {
  return r >= 0 && r < SIZE && c >= 0 && c < SIZE;
}

function isLegalMove(board, from, to, player) {
  if (!from || !to || !inBounds(from.r, from.c) || !inBounds(to.r, to.c)) return false;
  if (Math.max(Math.abs(from.r - to.r), Math.abs(from.c - to.c)) !== 1) return false;
  const source = board[from.r][from.c];
  const target = board[to.r][to.c];
  if (!source.piece || (player && source.piece.owner !== player)) return false;
  if (!target.piece) return true;
  if (target.piece.owner === source.piece.owner) return false;
  return BEATS[source.piece.type] === target.piece.type;
}

function allLegalMoves(player, board) {
  const moves = [];
  for (let r = 0; r < SIZE; r++) for (let c = 0; c < SIZE; c++) {
    if (board[r][c].piece?.owner !== player) continue;
    for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) {
      if (dr === 0 && dc === 0) continue;
      const move = { from: { r, c }, to: { r: r + dr, c: c + dc } };
      if (isLegalMove(board, move.from, move.to, player)) moves.push(move);
    }
  }
  return moves;
}

function cloneBoard(board) {
  return board.map(row => row.map(cell => ({
    territory: cell.territory,
    piece: cell.piece ? { ...cell.piece } : null,
  })));
}

function applyMove(board, move) {
  const source = board[move.from.r][move.from.c];
  const target = board[move.to.r][move.to.c];
  const captured = target.piece?.type ?? null;
  target.piece = source.piece;
  source.piece = null;
  if (target.territory === null) target.territory = target.piece.owner;
  return captured;
}

function simulateMove(board, move) {
  const copy = cloneBoard(board);
  applyMove(copy, move);
  return copy;
}

function scores(board) {
  const result = { blue: 0, red: 0 };
  for (const row of board) for (const cell of row) if (cell.territory) result[cell.territory]++;
  return result;
}

function pieceCounts(board) {
  const result = { blue: 0, red: 0 };
  for (const row of board) for (const cell of row) if (cell.piece) result[cell.piece.owner]++;
  return result;
}

function determineWinner(board) {
  const territory = scores(board);
  const pieces = pieceCounts(board);
  if (pieces.blue === 0) return { winner: 'red', reason: 'elimination' };
  if (pieces.red === 0) return { winner: 'blue', reason: 'elimination' };
  if (territory.blue + territory.red === SIZE * SIZE) {
    return { winner: territory.blue > territory.red ? 'blue' : 'red', reason: 'full-board territory' };
  }
  return null;
}

// This section is a direct port of index.html's move ordering, evaluation, and
// depth-3 root search. Blue minimizes the same red-positive evaluation.
function adjacentThreats(board, r, c, owner, type) {
  let threats = 0;
  let prey = 0;
  for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) {
    if (dr === 0 && dc === 0) continue;
    const nr = r + dr;
    const nc = c + dc;
    if (!inBounds(nr, nc)) continue;
    const piece = board[nr][nc].piece;
    if (!piece || piece.owner === owner) continue;
    if (BEATS[piece.type] === type) threats++;
    if (BEATS[type] === piece.type) prey++;
  }
  return { threats, prey };
}

function threatenedPieceCount(board, player) {
  let threatened = 0;
  for (let r = 0; r < SIZE; r++) for (let c = 0; c < SIZE; c++) {
    const piece = board[r][c].piece;
    if (piece?.owner === player && adjacentThreats(board, r, c, player, piece.type).threats > 0) threatened++;
  }
  return threatened;
}

function immediateCaptureCount(board, player) {
  return allLegalMoves(player, board).reduce((count, move) => count + (board[move.to.r][move.to.c].piece ? 1 : 0), 0);
}

function terminalValue(board) {
  const result = determineWinner(board);
  if (result?.winner === 'red') return 1_000_000;
  if (result?.winner === 'blue') return -1_000_000;
  return null;
}

function evaluateBoard(board) {
  const terminal = terminalValue(board);
  if (terminal !== null) return terminal;
  const score = scores(board);
  const pieces = pieceCounts(board);
  const redThreatened = threatenedPieceCount(board, 'red');
  const blueThreatened = threatenedPieceCount(board, 'blue');
  const redCaptures = immediateCaptureCount(board, 'red');
  const blueCaptures = immediateCaptureCount(board, 'blue');
  let value = (score.red - score.blue) * 34 + (pieces.red - pieces.blue) * 520;
  value += (blueThreatened - redThreatened) * 150 + (redCaptures - blueCaptures) * 72;
  value += (allLegalMoves('red', board).length - allLegalMoves('blue', board).length) * 2;
  for (let r = 0; r < SIZE; r++) for (let c = 0; c < SIZE; c++) {
    const piece = board[r][c].piece;
    if (!piece) continue;
    const positional = Math.max(0, 7 - (Math.abs(r - 4) + Math.abs(c - 4)));
    value += piece.owner === 'red' ? positional : -positional;
  }
  return value;
}

function moveOrderingScore(board, move, player) {
  const target = board[move.to.r][move.to.c];
  const after = simulateMove(board, move);
  const moved = after[move.to.r][move.to.c].piece;
  const danger = adjacentThreats(after, move.to.r, move.to.c, player, moved.type);
  let value = target.piece ? 900 : 0;
  if (target.territory === null) value += 90;
  value -= danger.threats * 420;
  value += danger.prey * 70;
  const enemy = player === 'red' ? 'blue' : 'red';
  value += threatenedPieceCount(after, enemy) * 55 - threatenedPieceCount(after, player) * 95;
  return value;
}

function orderedMoves(board, player, limit = 15) {
  return allLegalMoves(player, board)
    .map(move => ({ move, order: moveOrderingScore(board, move, player) }))
    .sort((a, b) => b.order - a.order)
    .slice(0, limit)
    .map(entry => entry.move);
}

function minimax(board, player, depth, alpha, beta) {
  const terminal = terminalValue(board);
  if (terminal !== null) return terminal;
  if (depth <= 0) return evaluateBoard(board);
  const moves = orderedMoves(board, player, depth >= 4 ? 14 : 17);
  if (!moves.length) return minimax(board, player === 'red' ? 'blue' : 'red', depth - 1, alpha, beta);
  const maximizing = player === 'red';
  let best = maximizing ? -Infinity : Infinity;
  for (const move of moves) {
    const value = minimax(simulateMove(board, move), player === 'red' ? 'blue' : 'red', depth - 1, alpha, beta);
    if (maximizing) {
      best = Math.max(best, value);
      alpha = Math.max(alpha, best);
    } else {
      best = Math.min(best, value);
      beta = Math.min(beta, best);
    }
    if (beta <= alpha) break;
  }
  return best;
}

function chooseJavaScriptMove(board, player) {
  const moves = orderedMoves(board, player, 18);
  if (!moves.length) return null;
  const maximizing = player === 'red';
  let bestMove = moves[0];
  let bestValue = maximizing ? -Infinity : Infinity;
  for (const move of moves) {
    const value = minimax(simulateMove(board, move), player === 'red' ? 'blue' : 'red', 3, -Infinity, Infinity);
    if ((maximizing && value > bestValue) || (!maximizing && value < bestValue)) {
      bestValue = value;
      bestMove = move;
    }
  }
  return { ...bestMove, stats: { depth: 4, score: bestValue } };
}

function hashSeed(text) {
  let hash = 2166136261;
  for (let i = 0; i < text.length; i++) {
    hash ^= text.charCodeAt(i);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function seededRandom(seed) {
  let state = hashSeed(seed);
  return () => {
    state += 0x6d2b79f5;
    let value = state;
    value = Math.imul(value ^ (value >>> 15), value | 1);
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61);
    return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
  };
}

function makeOpening(layout, seed, openingPlies) {
  const board = newBoard(layout);
  const random = seededRandom(seed);
  const moves = [];
  let current = 'blue';
  for (let ply = 0; ply < openingPlies && !determineWinner(board); ply++) {
    const legal = allLegalMoves(current, board);
    if (legal.length) {
      const move = legal[Math.floor(random() * legal.length)];
      const captured = applyMove(board, move);
      moves.push({ ply: ply + 1, player: current, ...move, captured });
    }
    current = current === 'blue' ? 'red' : 'blue';
  }
  return { board, current, moves };
}

const wasmRuntimes = new Map();

async function loadWasm(botId) {
  if (wasmRuntimes.has(botId)) return wasmRuntimes.get(botId);
  const filenames = {
    'rps-v2-engine': 'rps_v2_engine.wasm',
    'rps-v2-1-engine': 'rps_v2_1_engine.wasm',
    'rps-v3-engine': 'rps_v3_engine.wasm',
    'rps-v4-engine': 'rps_v4_engine.wasm',
    'rps-v5-engine': 'rps_v5_engine.wasm',
    'rps-v6-engine': 'rps_v6_engine.wasm',
  };
  const filename = filenames[botId];
  if (!filename) throw new Error(`Unknown WASM bot: ${botId}`);
  const bytes = await readFile(`${ROOT}/${filename}`);
  const { instance } = await WebAssembly.instantiate(bytes, { env: { now_ms: () => performance.now() } });
  instance.exports.init_engine();
  wasmRuntimes.set(botId, instance.exports);
  return instance.exports;
}

async function chooseWasmMove(botId, board, color, config) {
  const engine = await loadWasm(botId);
  const typeCode = { rock: 1, paper: 2, scissors: 3 };
  const colorCode = { blue: 1, red: -1 };
  engine.clear_position();
  for (let r = 0; r < SIZE; r++) for (let c = 0; c < SIZE; c++) {
    const square = r * SIZE + c;
    const cell = board[r][c];
    if (cell.piece) engine.set_piece(square, typeCode[cell.piece.type] * colorCode[cell.piece.owner]);
    if (cell.territory) engine.set_territory(square, colorCode[cell.territory]);
  }
  engine.set_side(colorCode[color]);
  engine.set_qdepth(config.qDepth);
  engine.finalize_position();
  const packed = engine.search_best_move(config.maxDepth, config.timeMs, config.maxNodes);
  if (packed < 0) return null;
  const fromSquare = Math.floor(packed / 81);
  const toSquare = packed % 81;
  return {
    from: { r: Math.floor(fromSquare / SIZE), c: fromSquare % SIZE },
    to: { r: Math.floor(toSquare / SIZE), c: toSquare % SIZE },
    stats: {
      depth: engine.get_depth(), score: engine.get_score(), nodes: engine.get_nodes(),
      qNodes: engine.get_qnodes(), ttHits: engine.get_tt_hits(), cutoffs: engine.get_cutoffs(),
      elapsedMs: engine.get_elapsed_ms(),
    },
  };
}

async function playGame(task, config) {
  const opening = makeOpening(config.layout, task.seed, config.openingPlies);
  const board = opening.board;
  let current = opening.current;
  let consecutivePasses = 0;
  const moves = [];
  let result = determineWinner(board);
  for (const botId of new Set(Object.values(task.colors))) {
    if (botId !== 'javascript-minimax') (await loadWasm(botId)).clear_tt();
  }
  for (let ply = opening.moves.length + 1; !result && ply <= config.maxPlies; ply++) {
    const botId = task.colors[current];
    const legal = allLegalMoves(current, board);
    if (!legal.length) {
      moves.push({ ply, player: current, bot: botId, passed: true });
      consecutivePasses++;
      if (consecutivePasses >= 2) {
        const territory = scores(board);
        const pieces = pieceCounts(board);
        const winner = territory.blue !== territory.red
          ? (territory.blue > territory.red ? 'blue' : 'red')
          : pieces.blue !== pieces.red
            ? (pieces.blue > pieces.red ? 'blue' : 'red')
            : null;
        result = winner ? { winner, reason: 'two-pass adjudication' } : { winner: null, reason: 'two-pass draw' };
        break;
      }
      current = current === 'blue' ? 'red' : 'blue';
      continue;
    }
    consecutivePasses = 0;
    const choice = botId === 'javascript-minimax'
      ? chooseJavaScriptMove(board, current)
      : await chooseWasmMove(botId, board, current, config);
    if (!choice || !isLegalMove(board, choice.from, choice.to, current)) {
      throw new Error(`${botId} returned an illegal move for ${current}: ${JSON.stringify(choice)}`);
    }
    const captured = applyMove(board, choice);
    moves.push({ ply, player: current, bot: botId, from: choice.from, to: choice.to, captured, stats: choice.stats });
    result = determineWinner(board);
    current = current === 'blue' ? 'red' : 'blue';
  }
  const finalScores = scores(board);
  const finalPieces = pieceCounts(board);
  return {
    id: task.id,
    pairing: task.pairing,
    matchedSeed: task.seed,
    colors: task.colors,
    winnerColor: result?.winner ?? null,
    winnerBot: result?.winner ? task.colors[result.winner] : null,
    outcome: result?.reason ?? 'max plies draw',
    plies: opening.moves.length + moves.length,
    openingMoves: opening.moves,
    moves,
    finalScores,
    finalPieces,
    finalBoard: board,
  };
}

function usage() {
  return `Usage: node tools/tournament.mjs [options]\n\n` +
    `  --games-per-pairing N  Even number of games (default: 10)\n` +
    `  --time-ms N            WASM time per move (default: 250)\n` +
    `  --max-plies N          Draw limit including opening (default: 200)\n` +
    `  --layout 6|9           Initial pieces per side (default: 9)\n` +
    `  --concurrency N        Worker count (default: available CPUs)\n` +
    `  --opening-plies N      Seeded random opening length (default: 4)\n` +
    `  --seed TEXT            Tournament seed (default: rps-v2-tournament)\n` +
    `  --max-depth N          WASM maximum depth (default: 10)\n` +
    `  --q-depth N            WASM quiescence depth (default: 4)\n` +
    `  --max-nodes N          Node limit per move; 0 disables (default: 0)\n` +
    `  --bots IDS             Comma-separated bot IDs (default: all)\n` +
    `  --output PATH          Result file relative to the repo (default: tournament-results.json)\n` +
    `  --help                 Show this help`;
}

function parseArgs(argv) {
  const config = {
    gamesPerPairing: 10,
    timeMs: 250,
    maxPlies: 200,
    layout: 9,
    concurrency: availableParallelism(),
    openingPlies: 4,
    seed: 'rps-v2-tournament',
    maxDepth: 10,
    qDepth: 4,
    maxNodes: 0,
    bots: ALL_BOTS.map(bot => bot.id).join(','),
    output: 'tournament-results.json',
  };
  const options = {
    '--games-per-pairing': 'gamesPerPairing', '--time-ms': 'timeMs', '--max-plies': 'maxPlies',
    '--layout': 'layout', '--concurrency': 'concurrency', '--opening-plies': 'openingPlies',
    '--seed': 'seed', '--max-depth': 'maxDepth', '--q-depth': 'qDepth', '--max-nodes': 'maxNodes',
    '--bots': 'bots', '--output': 'output',
  };
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === '--help') return { help: true };
    const key = options[argv[i]];
    if (!key) throw new Error(`Unknown option: ${argv[i]}`);
    if (argv[i + 1] === undefined) throw new Error(`Missing value for ${argv[i]}`);
    config[key] = ['seed', 'bots', 'output'].includes(key) ? argv[++i] : Number(argv[++i]);
  }
  for (const key of ['gamesPerPairing', 'timeMs', 'maxPlies', 'layout', 'concurrency', 'openingPlies', 'maxDepth', 'qDepth', 'maxNodes']) {
    if (!Number.isInteger(config[key]) || config[key] < (['openingPlies', 'qDepth', 'maxNodes'].includes(key) ? 0 : 1)) {
      throw new Error(`Invalid value for ${key}`);
    }
  }
  if (config.gamesPerPairing % 2 !== 0) throw new Error('--games-per-pairing must be even for matched color assignments');
  if (![6, 9].includes(config.layout)) throw new Error('--layout must be 6 or 9');
  if (config.openingPlies > config.maxPlies) throw new Error('--opening-plies cannot exceed --max-plies');
  const requested = config.bots.split(',').filter(Boolean);
  config.botList = ALL_BOTS.filter(bot => requested.includes(bot.id));
  if (config.botList.length !== requested.length || config.botList.length < 2) {
    throw new Error('--bots must contain at least two distinct known bot IDs');
  }
  return config;
}

function makeTasks(config) {
  const tasks = [];
  for (let a = 0; a < config.botList.length; a++) for (let b = a + 1; b < config.botList.length; b++) {
    const pairing = [config.botList[a].id, config.botList[b].id];
    for (let match = 0; match < config.gamesPerPairing / 2; match++) {
      const seed = `${config.seed}:opening-${match}`;
      tasks.push({ id: `${a}-${b}-${match}-a`, pairing, seed, colors: { blue: pairing[0], red: pairing[1] } });
      tasks.push({ id: `${a}-${b}-${match}-b`, pairing, seed, colors: { blue: pairing[1], red: pairing[0] } });
    }
  }
  return tasks;
}

async function runWorkers(tasks, config) {
  const results = [];
  let next = 0;
  const count = Math.min(config.concurrency, tasks.length);
  await Promise.all(Array.from({ length: count }, () => new Promise((resolve, reject) => {
    const worker = new Worker(new URL(import.meta.url), { workerData: config });
    worker.on('message', message => {
      if (message.error) {
        worker.terminate();
        reject(new Error(message.error));
        return;
      }
      if (message.result) results.push(message.result);
      if (next < tasks.length) worker.postMessage(tasks[next++]);
      else worker.postMessage(null);
    });
    worker.on('error', reject);
    worker.on('exit', code => code === 0 ? resolve() : reject(new Error(`Worker exited with code ${code}`)));
  })));
  return results.sort((a, b) => a.id.localeCompare(b.id));
}

function summarize(games, bots) {
  const standings = bots.map(bot => ({ bot: bot.id, label: bot.label, wins: 0, draws: 0, losses: 0, points: 0 }));
  const byBot = new Map(standings.map(row => [row.bot, row]));
  for (const game of games) {
    const [a, b] = game.pairing;
    if (!game.winnerBot) {
      for (const bot of [a, b]) {
        byBot.get(bot).draws++;
        byBot.get(bot).points += 0.5;
      }
    } else {
      const loser = game.winnerBot === a ? b : a;
      byBot.get(game.winnerBot).wins++;
      byBot.get(game.winnerBot).points++;
      byBot.get(loser).losses++;
    }
  }
  standings.sort((a, b) => b.points - a.points || b.wins - a.wins || a.bot.localeCompare(b.bot));
  const pairings = [];
  for (let a = 0; a < bots.length; a++) for (let b = a + 1; b < bots.length; b++) {
    const left = bots[a].id;
    const right = bots[b].id;
    const relevant = games.filter(game => game.pairing[0] === left && game.pairing[1] === right);
    pairings.push({
      bots: [left, right],
      wins: [relevant.filter(game => game.winnerBot === left).length, relevant.filter(game => game.winnerBot === right).length],
      draws: relevant.filter(game => !game.winnerBot).length,
    });
  }
  return { standings, pairings };
}

async function main() {
  let config;
  try {
    config = parseArgs(process.argv.slice(2));
  } catch (error) {
    console.error(error.message);
    console.error(usage());
    process.exitCode = 1;
    return;
  }
  if (config.help) {
    console.log(usage());
    return;
  }
  const tasks = makeTasks(config);
  console.log(`Running ${tasks.length} games with ${Math.min(config.concurrency, tasks.length)} workers...`);
  const games = await runWorkers(tasks, config);
  const summary = summarize(games, config.botList);
  console.log('\nStandings');
  console.log('Bot                         W  D  L  Pts');
  for (const row of summary.standings) {
    console.log(`${row.bot.padEnd(27)} ${String(row.wins).padStart(2)} ${String(row.draws).padStart(2)} ${String(row.losses).padStart(2)} ${row.points.toFixed(1).padStart(4)}`);
  }
  console.log('\nPairings');
  for (const pairing of summary.pairings) {
    console.log(`${pairing.bots[0]} ${pairing.wins[0]}-${pairing.draws}-${pairing.wins[1]} ${pairing.bots[1]}`);
  }
  const report = {
    formatVersion: 1,
    generatedAt: new Date().toISOString(),
    config,
    bots: config.botList,
    standings: summary.standings,
    pairings: summary.pairings,
    games,
  };
  const resultPath = resolve(ROOT, config.output);
  await writeFile(resultPath, `${JSON.stringify(report, null, 2)}\n`);
  console.log(`\nDetailed results: ${resultPath}`);
}

if (isMainThread) {
  await main();
} else {
  parentPort.on('message', async task => {
    if (task === null) {
      parentPort.close();
      return;
    }
    try {
      parentPort.postMessage({ result: await playGame(task, workerData) });
    } catch (error) {
      parentPort.postMessage({ error: error.stack || error.message });
    }
  });
  parentPort.postMessage({ ready: true });
}
