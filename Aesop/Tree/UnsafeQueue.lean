/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule

namespace Aesop

def UnsafeQueue := Subarray (IndexMatchResult UnsafeRule)

namespace UnsafeQueue

instance : Inhabited UnsafeQueue :=
  inferInstanceAs $ Inhabited (Subarray (IndexMatchResult UnsafeRule))

@[inline]
def initial (rs : Array (IndexMatchResult UnsafeRule)) : UnsafeQueue :=
  rs.toSubarray

protected def empty : UnsafeQueue :=
  #[].toSubarray

instance : EmptyCollection UnsafeQueue :=
  ⟨UnsafeQueue.empty⟩

@[inline]
def pop? (queue : UnsafeQueue) :
    Option (IndexMatchResult UnsafeRule × UnsafeQueue) :=
  if h : queue.start < queue.stop
    then
      let head := queue.as.get ⟨queue.start, Nat.lt_of_lt_of_le h queue.h₂⟩
      let tail :=
        { queue with
          start := queue.start + 1
          h₁ := Nat.le_of_lt_succ $ Nat.succ_lt_succ h  }
      some (head, tail)
    else
      none

@[inline]
def size (queue : UnsafeQueue) : Nat :=
  queue.stop - queue.start

@[inline]
def isEmpty (queue : UnsafeQueue) : Bool :=
  queue.size == 0

end UnsafeQueue

end Aesop
