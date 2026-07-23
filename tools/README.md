# V2 tournament harness

Run the default tournament from the repository root:

```sh
node tools/tournament.mjs
```

This runs 10 games per pairing with the current six-piece website layout, WASM settings `maxDepth=10`, `timeMs=250`, and `qDepth=4`, and a 200-ply draw limit. Use `node tools/tournament.mjs --help` for options, including `--layout 9`.

For fairness, every pairing uses the same five deterministic seeded random opening positions. Every position is played twice with the bots swapping blue and red, and an even `--games-per-pairing` is required. Games run in worker threads so each synchronous WASM search gets its own worker; `--concurrency` controls the worker count. WASM transposition tables are cleared between games so worker scheduling cannot leak search state across matches. The harness prints standings and pairing records and writes every opening, move, search statistic, and final result to `tournament-results.json`.
