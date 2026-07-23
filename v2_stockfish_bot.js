(function (global) {
  'use strict';

  async function instantiate(url) {
    const imports = { env: { now_ms: () => performance.now() } };

    if (WebAssembly.instantiateStreaming) {
      try {
        const response = await fetch(url);
        if (!response.ok) throw new Error(`Unable to load engine (${response.status})`);
        return (await WebAssembly.instantiateStreaming(response, imports)).instance;
      } catch (error) {
        console.warn('Streaming WASM load failed; retrying with ArrayBuffer.', error);
      }
    }

    const response = await fetch(url);
    if (!response.ok) throw new Error(`Unable to load engine (${response.status})`);
    return (await WebAssembly.instantiate(await response.arrayBuffer(), imports)).instance;
  }

  async function loadEngine(url) {
    const instance = await instantiate(url);
    const engine = instance.exports;
    engine.init_engine();

    return {
      engine,
      chooseMove(position, options) {
        const { board, color } = position;
        const { maxDepth = 10, timeMs = 250, qDepth = 4 } = options;
        const typeCode = { rock: 1, paper: 2, scissors: 3 };
        const colorCode = { blue: 1, red: -1 };

        engine.clear_position();
        for (let r = 0; r < board.length; r++) {
          for (let c = 0; c < board[r].length; c++) {
            const square = r * 9 + c;
            const cell = board[r][c];
            if (cell.piece) {
              engine.set_piece(square, typeCode[cell.piece.type] * colorCode[cell.piece.owner]);
            }
            if (cell.territory) engine.set_territory(square, colorCode[cell.territory]);
          }
        }

        engine.set_side(colorCode[color]);
        engine.set_qdepth(qDepth);
        engine.finalize_position();

        // The third search argument is an optional node limit; zero disables it.
        const packedMove = engine.search_best_move(maxDepth, timeMs, 0);
        if (packedMove < 0) return null;

        const fromSquare = Math.floor(packedMove / 81);
        const toSquare = packedMove % 81;
        return {
          from: { r: Math.floor(fromSquare / 9), c: fromSquare % 9 },
          to: { r: Math.floor(toSquare / 9), c: toSquare % 9 },
          stats: {
            depth: engine.get_depth(),
            score: engine.get_score(),
            nodes: engine.get_nodes(),
            qNodes: engine.get_qnodes(),
            ttHits: engine.get_tt_hits(),
            cutoffs: engine.get_cutoffs(),
            elapsedMs: engine.get_elapsed_ms(),
          },
        };
      },
    };
  }

  global.RPSV2StockfishBot = { loadEngine };
})(globalThis);
