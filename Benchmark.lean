/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Xavier Généreux
-/
import AesopTest.Forward.Benchmark

/-
# Benchmark for Incremental Forward Reasoning for White-Box Proof Search

To run the following test, simply load this file normaly or build it
using the `lake` command given in the README.

There are three main tests :

## Transitivity
The benchmark `runTestTrans` corresponds to the **Transitivity Benchmark**
presented in the paper.

The data in the paper for the benchmark is run with these specific parameters :
`bchmk 20 with steps k using fun n ↦ runTestDepth k 0 100 n (0 | 100)`

## Independence
The benchmark `runTestIndep`

The data in the paper for the benchmark is run with these specific parameters :
`bchmk 50 with (pows 6) using fun n ↦ runTestIndep 6 n (0 | 100)`

## Depth
The benchmark `runTestDepth`

The data in the paper for the benchmark is run with these specific parameters :
`bchmk 20 with (pows 6) using fun n ↦ runTestTrans n (0 | 100)`

This specific test is also presented with the precompilation turned on.
Precompilation can be switched on in `lakefile.toml`, see the README for
detailed instructions.

-/

/-
**Uncomment to reveal parameters**
#check runTestTrans
#check runTestIndep
#check runTestErase
-/

local notation "k" => 2

set_option maxHeartbeats 100000000
set_option maxRecDepth 10000000
bchmk 1 with (pows 6) using fun n ↦ runTestTrans n 0
bchmk 1 with (pows 6) using fun n ↦ runTestTrans n 100
bchmk 1 with (pows 6) using fun n ↦ runTestIndep 6 n 0
bchmk 1 with (pows 6) using fun n ↦ runTestIndep 6 n 100
bchmk 1 with steps k using fun n ↦ runTestDepth k 0 100 n 0
bchmk 1 with steps k using fun n ↦ runTestDepth k 0 100 n 100
