import Aesop

open Aesop
open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser
open Lean.Parser.Tactic (tacticSeq)

initialize registerTraceClass `bench

inductive SNat where
  | zero
  | succ (n : SNat)

abbrev Nat.toSNat : Nat → SNat
  | zero => .zero
  | succ n => .succ n.toSNat

elab "snat% " n:num : term => do
  let n ← elabTerm n (some $ .const ``Nat [])
  reduceAll (.app (.const ``Nat.toSNat []) n)

instance : MonadBacktrack Core.SavedState CoreM where
  saveState := Core.saveState
  restoreState := Core.SavedState.restore

instance : MonadBacktrack Elab.Command.State CommandElabM where
  saveState := get
  restoreState s := modify fun s' => {
    s with
    traceState := s'.traceState
    ngen := s'.ngen
  }

initialize timeRef : IO.Ref Nanos ← IO.mkRef 0

elab "time " t:tactic : tactic => do
  let nanos ← Aesop.time' do Lean.Elab.Tactic.evalTactic t
  timeRef.set nanos

def withStatefulForward [MonadWithOptions m] (opt : Bool) (k : m α) : m α :=
  withOptions (fun opts ↦ aesop.dev.statefulForward.set opts opt) k

/-- A benchmark that can be run by the `bchmk` command. -/
structure Benchmark where
  /-- A title for the benchmark's output. -/
  title : String
  /-- A function that executes the benchmark once. -/
  fn : Nat → Option (TSyntax ``tacticSeq) → CommandElabM Nanos

namespace Benchmark

def run (n : Nat) (ts? : Option (TSyntax ``tacticSeq)) (bm : Benchmark)
  (statefulForward : Bool) (maxHeartbeats := 100000000000) (maxRecDepth := 100000000000) : CommandElabM Nanos := do
    withScope (fun s => {
      s with
      opts :=
        Lean.maxHeartbeats.set (val := maxHeartbeats) <|
        Lean.maxRecDepth.set (val := maxRecDepth) <|
        Elab.async.set (val := false) <|
        aesop.dev.statefulForward.set s.opts statefulForward
    }) do
      withTraceNode `bench (fun r => return m!"{exceptEmoji r} run benchmark {bm.title} for input {n}") do
      let result ← withoutModifyingState do
        let result ← bm.fn n ts?
        if (← get).messages.hasErrors then
          let errs := m!"\n".joinSep <| ← (← get).messages.toList.filter (·.severity == .error) |>.mapM (·.toString)
          throwError m!"errors while executing benchmark {bm.title}:{indentD errs}"
        return result
      addTraceAsMessages
      return result

end Benchmark
