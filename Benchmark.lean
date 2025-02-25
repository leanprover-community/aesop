/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Cascade
import Benchmark.Cluster
import Benchmark.Command
import Benchmark.Depth
import Benchmark.Indep
import Benchmark.Trans

/-!
# Benchmarks for Incremental Forward Reasoning for White-Box Proof Search

To run the benchmarks, simply load this file normally or build it with
`lake build +Benchmark`.

## The `bchmk` command.

This is a custom command with syntax
```
#bchmk (nIter : Nat) with (l : List Nat) using (b : Benchmark)
```

`nIter` determines the number of times the benchmark is be run.

Then, given `l : List Nat`, we execute a benchmark `b` for each element of `l`.
We output the average over `nIter` runs for each element of `l`.
See below for a description of the different benchmarks studied. (Uncomment the
`#check benchX` lines.)

See `Benchmark/Basic.lean` for the definition of the `Benchmark` type.

## Lists with relevant values

We run the benchmarks on the following lists:

- `pows (n : Nat)` :
The list of the first `n` powers of two : `(List.range n).map (2 ^ ·)`

- `steps (n : Nat)` :
The range between `1` and `n - 1`: `(List.range' 1 (n - 1))`
This contains the relevant values for the depth test.

## Benchmark Configuration

The benchmarks are set up with the same configuration as in the paper, only with
`nIter = 1` instead of `nIter = 20`.
This take about 8 minutes on our machine (a MacBook Pro with an Apple M2 Pro
processor and 32GB of RAM).
-/

/- We effectively disable Lean's deterministic timeout mechanism
(`maxHeartbeats`) and its global limit on recursion depth (`maxRecDepth`). -/
set_option maxHeartbeats 100000000
set_option maxRecDepth   100000000

/- Uncomment to reveal benchmark parameters. -/
-- #check benchTrans
-- #check benchIndep
-- #check benchDepth

/- Transitivity benchmark -/
bchmk 1 with pows 6  using benchTrans 0
bchmk 1 with pows 6  using benchTrans 100

/- Independence benchmark -/
bchmk 1 with pows 6  using benchIndep 6 0
bchmk 1 with pows 6  using benchIndep 6 100

/- Depth benchmark -/
bchmk 1 with steps 6 using benchDepth 6 0 100 0
bchmk 1 with steps 6 using benchDepth 6 0 100 100
