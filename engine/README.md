# V2.1 engine

`rps_v2_1_engine.cpp` is the original V2 engine source with only evaluation
constants changed. Search behavior, move generation, terminal rules,
transposition tables, LMR, and quiescence are unchanged.

V2.1 changes:

- territory: 118 -> 80
- material: 760 -> 1800
- threatened enemy pieces: 165 -> 320
- immediate capture opportunities: 82 -> 180
- neutral-square proximity: 42/22 -> 20/10
- late territory ramp: 80 - 4n -> 40 - 2n

Build with Clang from the WASI SDK:

```sh
clang++ --target=wasm32-unknown-unknown -O3 -fno-builtin -nostdlib \
  -Wl,--no-entry -Wl,--export-memory -Wl,--allow-undefined \
  -Wl,--initial-memory=16777216 -Wl,--max-memory=134217728 \
  engine/rps_v2_1_engine.cpp -o rps_v2_1_engine.wasm
```
