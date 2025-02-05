# toyprover
(WIP)  
This repo build a (toy-level) first order logic prover in Lean 4.

## usage

```bash
lake build toyprover
.lake/build/bin/toyprover <tptp file path>
```

## test

Currently, use Pelletier's `Seventy-five problems for testing automatic theorem provers` as test cases.

Run `make test` to run the test in Window.
