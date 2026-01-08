/-
Copyright (c) 2026 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/

import Benchmark.Command
import Benchmark.Depth

/- Uncomment to reveal benchmark parameters. -/
-- #check benchDepth

/- Depth benchmark -/
bchmk 10 with steps 6 using depth 6 0 100 0
bchmk 10 with steps 6 using depth 6 0 100 100
