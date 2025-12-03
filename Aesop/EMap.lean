import Aesop.Tracing
import Aesop.Util.Basic

open Lean Lean.Meta

namespace Aesop

-- FIXME docs

/-- A map whose keys are expressions. Keys are identified up to defeq. We use
`reducible` transparency and treat metavariables as rigid (i.e.,
unassignable). -/
structure EMap (α) where
  /-- The mappings stored in the map. Defeq expressions are identified, so
  for each equivalence class of defeq expressions we only store one
  representative. Missing values indicate expressions that were removed from the
  map. -/
  rep : PArray (Option (Expr × α))
  /-- An index for `rep`. For each expression `e` at index `i` in `rep`,
  `idx.getMatch` returns a list of indexes containing `i`. This is used as a
  pre-filter during lookups/insertions/modifications to reduce the number of
  defeq comparisons. -/
  idx : DiscrTree Nat
  deriving Inhabited

namespace EMap

protected def empty : EMap α where
  rep := .empty
  idx := .empty

instance : EmptyCollection (EMap α) :=
  ⟨.empty⟩

variable [Monad m] [MonadLiftT MetaM m]

instance : ForM m (EMap α) (Expr × α) where
  forM map f := map.rep.forM fun
    | none => return
    | some x => f x

instance : ForIn m (EMap α) (Expr × α) where
  forIn map init f := map.rep.forIn init fun
    | none, s => return .yield s
    | some x, s => f x s

def foldlM (init : σ) (f : σ → Expr → α → m σ) (map : EMap α) : m σ :=
  map.rep.foldlM (init := init) fun
    | s, none => return s
    | s, some (e, a) => f s e a

def foldl (init : σ) (f : σ → Expr → α → σ) (map : EMap α) : σ :=
  inline <| map.foldlM (m := Id) init f

private def getCandidates (e : Expr) (map : EMap α) : m (Array Nat) :=
  map.idx.getMatch e

@[specialize]
def alterM (e : Expr) (f : α → m (Option α × β)) (map : EMap α) :
    m (EMap α × Option β) := do
  let lctx ← show MetaM _ from getLCtx
  let mut rep := map.rep
  for i in ← map.getCandidates e do
    let some (e', old) := map.rep[i]!
      | continue
    if e'.hasAnyFVar (! lctx.contains ·) then
      rep := rep.set i none
      continue
    if ← isDefEqReducibleRigid e' e then
      let (new?, b) ← f old
      let entry := new?.map (e', ·)
      return ({ map with rep := rep.set i entry }, b)
  return ({ map with rep }, none)

def alter (e : Expr) (f : α → Option α × β) (map : EMap α) :
    MetaM (EMap α × Option β) := do
  inline <| map.alterM e fun a => return f a

@[specialize]
def insertNew (e : Expr) (a : α) (map : EMap α) : m (EMap α) := do
  let i := map.rep.size
  let rep := map.rep.push (e, a)
  let idx ← map.idx.insert e i
  return { idx, rep }

@[specialize]
def insertWithM (e : Expr) (f : Option α → m α) (map : EMap α) :
    m (EMap α × Option α × α) := do
  let (map, vals?) ← map.alterM e fun old => do
    let new ← f (some old)
    return (new, (old, new))
  match vals? with
  | none =>
    let new ← f none
    return (← map.insertNew e new, none, new)
  | some (old, new) =>
    return (map, old, new)

def insertWith (e : Expr) (f : Option α → α) (map : EMap α) :
    MetaM (EMap α × Option α × α) :=
  inline <| map.insertWithM e fun a? => return f a?

def insert (e : Expr) (a : α) (map : EMap α) : MetaM (EMap α) :=
  (·.fst) <$> inline (map.insertWithM e (fun _ => return a))

def singleton (e : Expr) (a : α) : m (EMap α) :=
  EMap.empty.insertNew e a

def findWithKey? (e : Expr) (map : EMap α) : MetaM (Option (Expr × α)) := do
  let lctx ← getLCtx
  for i in ← map.getCandidates e do
    let some (e', a) := map.rep[i]!
      | continue
    if e'.hasAnyFVar (! lctx.contains ·) then
      continue
    if ← isDefEqReducibleRigid e e' then
      return some (e', a)
  return none

def find? (e : Expr) (map : EMap α) : MetaM (Option α) := do
  return (← inline <| map.findWithKey? e).map (·.2)

@[specialize]
def mapM (f : Expr → α → m β) (map : EMap α) : m (EMap β) := do
  let rep ← map.rep.mapM fun x? => x?.mapM fun (e, a) => return (e, ← f e a)
  return { map with rep }

def map (f : Expr → α → β) (map : EMap α) : EMap β :=
  map.mapM (m := Id) f

end EMap
end Aesop
