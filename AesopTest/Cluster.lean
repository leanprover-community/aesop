import Aesop.Util.UnionFind

open Aesop

def features : Nat → Array Nat
  | 0 => #[10]
  | 1 => #[10, 20]
  | 2 => #[20]
  | _ => #[]

-- Connectivity is transitive even when the endpoint images are disjoint.
#guard (cluster features #[0, 1, 2, 3]).size == 2
#guard (cluster features #[0, 1, 2, 3]).any fun xs =>
  xs.size == 3 && xs.contains 0 && xs.contains 1 && xs.contains 2
#guard (cluster features #[0, 1, 2, 3]).any (· == #[3])
#guard (cluster (fun _ : Nat => #[0, 0]) #[1, 2, 1, 3]).size == 1
#guard (cluster (fun _ : Nat => #[] : Nat → Array Nat) #[]).isEmpty
-- A common feature requires only one merge per occurrence.
#guard (cluster (fun _ : Nat => #[0]) (Array.range 1000)).size == 1
