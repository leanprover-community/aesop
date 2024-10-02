/-
Copyright (c) 2024 Son Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Son Ho, Jannis Limperg
-/

import Aesop

@[aesop safe forward (pattern := l)] theorem th1  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th2  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th3  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th4  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th5  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th6  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th7  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th8  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th9  (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th10 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th11 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th12 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th13 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th14 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th15 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th16 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th17 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th18 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th19 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th20 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th21 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th22 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th23 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th24 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th25 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th26 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th27 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th28 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th29 (l : List α) : l.length ≥ 0 := by simp
@[aesop safe forward (pattern := l)] theorem th30 (l : List α) : l.length ≥ 0 := by simp

/--
error: unsolved goals
α : Type u_1
l0 l1 l2 : List α
fwd : (l0 ++ l1 ++ l2).length ≥ 0
fwd_1 : l0.length ≥ 0
fwd_2 : l2.length ≥ 0
fwd_3 : l1.length ≥ 0
fwd_4 : (l0 ++ l1).length ≥ 0
⊢ (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length
-/
#guard_msgs in
theorem test (l0 l1 l2 : List α) : (l0 ++ l1 ++ l2).length = l0.length + l1.length + l2.length := by
  saturate
