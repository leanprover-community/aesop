module

public import Std.Data.HashSet.Lemmas

public section

open Std (HashSet)

namespace Aesop

/-- A hash set that preserves the order of insertions. -/
structure OrderedHashSet (α) [BEq α] [Hashable α] where
  toArray : Array α
  toHashSet : HashSet α
  deriving Inhabited

namespace OrderedHashSet

variable [BEq α] [Hashable α]

instance : EmptyCollection (OrderedHashSet α) :=
  ⟨⟨#[], ∅⟩⟩

def emptyWithCapacity (n : Nat) : OrderedHashSet α where
  toArray := Array.emptyWithCapacity n
  toHashSet := HashSet.emptyWithCapacity n

def insert (x : α) (s : OrderedHashSet α) : OrderedHashSet α :=
  if x ∈ s.toHashSet then
    s
  else {
    toArray := s.toArray.push x
    toHashSet := s.toHashSet.insert x
  }

def insertMany [ForIn Id ρ α] (xs : ρ) (s : OrderedHashSet α) :
    OrderedHashSet α := Id.run do
  let mut result := s
  for x in xs do
    result := result.insert x
  return result

def ofArray (xs : Array α) : OrderedHashSet α :=
  (∅ : OrderedHashSet α).insertMany xs

def contains (x : α) (s : OrderedHashSet α) : Bool :=
  s.toHashSet.contains x

instance : Membership α (OrderedHashSet α) where
  mem s x := x ∈ s.toHashSet

instance {s : OrderedHashSet α} : Decidable (x ∈ s) :=
  inferInstanceAs (Decidable (x ∈ s.toHashSet))

@[specialize]
def foldlM [Monad m] (f : β → α → m β) (init : β)
    (s : OrderedHashSet α) : m β :=
  s.toArray.foldlM f init

def foldl (f : β → α → β) (init : β) (s : OrderedHashSet α) : β :=
  s.toArray.foldl f init

@[specialize]
def foldrM [Monad m] (f : α → β → m β) (init : β)
    (s : OrderedHashSet α) : m β :=
  s.toArray.foldrM f init

def foldr (f : α → β → β) (init : β) (s : OrderedHashSet α) : β :=
  s.toArray.foldr f init

instance [Monad m] : ForIn m (OrderedHashSet α) α where
  forIn s b f := ForIn.forIn s.toArray b f

end Aesop.OrderedHashSet
