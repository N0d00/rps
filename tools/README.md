# V2 tournament harness

Run the default tournament from the repository root:

```sh
node tools/tournament.mjs
```

This runs 10 games per pairing with the current nine-piece V2 layout, WASM settings `maxDepth=10`, `timeMs=250`, and `qDepth=4`, and a 200-ply draw limit. Use `node tools/tournament.mjs --help` for options.

For fairness, every pairing uses the same five deterministic seeded random opening positions. Every position is played twice with the bots swapping blue and red, and an even `--games-per-pairing` is required. Games run in worker threads so each synchronous WASM search gets its own worker; `--concurrency` controls the worker count. WASM transposition tables are cleared between games so worker scheduling cannot leak search state across matches. The harness prints standings and pairing records and writes every opening, move, search statistic, and final result to `tournament-results.json`.

Use `--output tournament-results-v3.json` to preserve an existing report.

For reproducible comparisons, use a fixed node budget and only the desired bots, for example `--max-nodes 100000 --bots rps-v2-1-engine,rps-v3-engine`.
