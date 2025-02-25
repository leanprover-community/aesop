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
bchmk 20 with pows 6  using benchTrans 0
bchmk 20 with pows 6  using benchTrans 100

/- Independence benchmark -/
bchmk 20 with pows 6  using benchIndep 6 0
bchmk 20 with pows 6  using benchIndep 6 100

/- Depth benchmark -/
bchmk 20 with steps 6 using benchDepth 6 0 100 0
bchmk 20 with steps 6 using benchDepth 6 0 100 100
