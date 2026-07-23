(function (global) {
  'use strict';

  async function loadEngine(url) {
    if (!global.RPSV2StockfishBot) throw new Error('v2_stockfish_bot.js must be loaded first.');
    return global.RPSV2StockfishBot.loadEngine(url);
  }

  async function chooseWebsiteMove(board, options = {}) {
    const { runtime, color = 'red', maxDepth = 10, timeMs = 250, qDepth = 4 } = options;
    if (!runtime) throw new Error('The V2 WASM engine has not been initialized.');

    const result = runtime.chooseMove({ board, color }, { maxDepth, timeMs, qDepth });
    if (!result) return null;
    return result;
  }

  global.RPSV2Wasm = { loadEngine, chooseWebsiteMove };
})(globalThis);
