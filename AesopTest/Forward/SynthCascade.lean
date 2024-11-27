import Aesop
import AesopTest.Forward.Definitions

open Aesop
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

elab "testCascade " nRules:num " by " ts:tacticSeq : command => do
  let some nRules := nRules.raw.isNatLit?
    | throwUnsupportedSyntax
  let mut pNames := Array.mkEmpty nRules
  for i in [:nRules] do
      pNames := pNames.push (Name.mkSimple $ "P" ++ toString i)
  for pName in pNames do
    elabCommand $ ← `(command| axiom $(mkIdent pName) : SNat → Prop)
  let mut binders : TSyntaxArray ``Term.bracketedBinder := #[]
  for i in [1:nRules] do
    binders : TSyntaxArray ``Term.bracketedBinder ←
    /- The following option feels like it should slow down the old forward significantly :-/
      --(((pNames.take i).push pNames[0]!).eraseIdx 0).mapIdxM fun j pName ↦ do
      (pNames.take i).mapIdxM fun j pName ↦ do
        `(bracketedBinder| ($(mkIdent $ .mkSimple $
          "p" ++ toString i ++ toString j) : $(mkIdent pName):ident $(mkIdent `n)))
    let sig : Term ← `(∀ $(mkIdent `n) $binders:bracketedBinder*, $(mkIdent pNames[i]!):ident $(mkIdent `n))
    elabCommand $ ← `(command|
      @[aesop safe forward]
      axiom $(mkIdent $ .mkSimple $ "l" ++ toString i):ident : $sig:term
    )
  elabCommand $ ← `(command|
    theorem $(mkIdent $ .mkSimple $ "t")
        ($(mkIdent `h0) : $(mkIdent pNames[0]!):ident (snat% 300)) : True := by $ts
  )
/-
/-
 **Uncomment for single test** :-/
testCascade 35 by
  set_option trace.profiler true in
  set_option aesop.dev.statefulForward false in
  saturate [*]
  trivial

#check l3
-/

def runTestCascade (nRs : Nat) : CommandElabM Nanos := do
  let mut nRs := Syntax.mkNatLit nRs
  let cmd := elabCommand <| ← `(testCascade $nRs by
    set_option maxHeartbeats 5000000 in
    set_option aesop.dev.statefulForward false in
    saturate
    trivial)
  Aesop.time' <| liftCoreM <| withoutModifyingState $ liftCommandElabM cmd

/-
X : This is probably safe to delete. (Old benchmark)
open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser in
elab "bmCascade " nRules:num : command => do
  let some nRules:= nRules.raw.isNatLit?
    | throwUnsupportedSyntax
  for i in [:(nRules + 1)] do
    let mut inum := (Lean.Syntax.mkNatLit (2 ^ i))
    elabCommand $ ← `(testCascade $inum by
      set_option maxHeartbeats 5000000 in
      set_option aesop.dev.statefulForward false in
      set_option trace.profiler true in
      --set_option trace.aesop.forward true in
      --set_option trace.saturate true in
      --set_option profiler true in
      saturate $inum [*]
      trivial)

bmCascade 6

/-X : I need we need this test somewhere -/
example (P : Nat → Prop) (hP : ∀ n, P n → P (n + 1)) (h0 : P 0)
   : P 50 := by
  set_option trace.profiler true in
  set_option aesop.dev.statefulForward false in
  saturate 50 [*]
  assumption

-/
