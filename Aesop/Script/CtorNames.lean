import Aesop.Util.Basic

open Lean Lean.Meta

namespace Aesop

structure CtorNames where
  ctor : Name
  args : Array Name
  /-- Whether the constructor has at least one implicit argument. -/
  hasImplicitArg : Bool

namespace CtorNames

def toRCasesPat (cn : CtorNames) : TSyntax `rcasesPat := Unhygienic.run do
  let ns ← cn.args.mapM λ n =>
    `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent n):ident)
  if cn.hasImplicitArg then
    `(rcasesPat| @⟨ $ns,* ⟩)
  else
    `(rcasesPat| ⟨ $ns,* ⟩)

private def nameBase : Name → Name
  | .anonymous => .anonymous
  | .str _ s => .str .anonymous s
  | .num _ n => .num .anonymous n

open Lean.Parser.Tactic in
def toInductionAltLHS (cn : CtorNames) :
    TSyntax ``inductionAltLHS := Unhygienic.run do
  let ns := cn.args.map mkIdent
  let ctor := mkIdent $ nameBase cn.ctor
  if cn.hasImplicitArg then
    `(inductionAltLHS| | @$ctor $ns:ident*)
  else
    `(inductionAltLHS| | $ctor $ns:ident*)

open Lean.Parser.Tactic in
def toInductionAlt (cn : CtorNames) (tacticSeq : Array Syntax.Tactic) :
    TSyntax ``inductionAlt := Unhygienic.run do
  `(inductionAlt| $(cn.toInductionAltLHS):inductionAltLHS => $tacticSeq:tactic*)

def toAltVarNames (cn : CtorNames) : AltVarNames where
  explicit := true
  varNames := cn.args.toList

def mkFreshArgNames (lctx : LocalContext) (cn : CtorNames) :
    CtorNames × LocalContext :=
  let (args, lctx) := getUnusedNames lctx cn.args
  ({ cn with args }, lctx)

end CtorNames

open Lean.Parser.Tactic in
def ctorNamesToRCasesPats (cns : Array CtorNames) : TSyntax ``rcasesPatMed :=
  Unhygienic.run do `(rcasesPatMed| $(cns.map (·.toRCasesPat)):rcasesPat|*)

open Lean.Parser.Tactic in
def ctorNamesToInductionAlts (cns : Array (CtorNames × Array Syntax.Tactic)) :
    TSyntax ``inductionAlts := Unhygienic.run do
  let alts := cns.map λ (cn, tacticSeq) => cn.toInductionAlt tacticSeq
  `(inductionAlts| with $alts:inductionAlt*)

def mkCtorNames (iv : InductiveVal) : CoreM (Array CtorNames) := MetaM.run' do
  iv.ctors.toArray.mapM λ ctor => do
    let cv ← getConstInfoCtor ctor
    let arity := cv.numParams + cv.numFields
    forallBoundedTelescope cv.type arity λ args _ => do
      let mut result := Array.mkEmpty cv.numFields
      let mut hasImplicitArg := false
      for arg in args[cv.numParams:] do
        let ldecl ← arg.fvarId!.getDecl
        result := result.push ldecl.userName
        hasImplicitArg := hasImplicitArg || ! ldecl.binderInfo.isExplicit
      return { args := result, ctor, hasImplicitArg }

end Aesop
