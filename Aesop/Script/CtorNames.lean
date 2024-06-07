import Aesop.Util.Basic

open Lean Lean.Meta

namespace Aesop

def namesToRCasesPat (ns : Array Name) (implicit : Bool) :
    TSyntax `rcasesPat := Unhygienic.run do
  let ns ← ns.mapM λ n =>
    `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent n):ident)
  if implicit then
    `(rcasesPat| @⟨ $ns,* ⟩)
  else
    `(rcasesPat| ⟨ $ns,* ⟩)

structure CtorNames where
  ctor : Name
  args : Array Name
  /-- Whether the constructor has at least one implicit argument. -/
  hasImplicitArg : Bool

namespace CtorNames

def toRCasesPat (cn : CtorNames) : TSyntax `rcasesPat :=
  namesToRCasesPat cn.args cn.hasImplicitArg

def toAltVarNames (cn : CtorNames) : AltVarNames where
  explicit := true
  varNames := cn.args.toList

def mkFreshArgNames (lctx : LocalContext) (cn : CtorNames) :
    CtorNames × LocalContext :=
  let (args, lctx) := getUnusedNames lctx cn.args
  ({ cn with args }, lctx)

end CtorNames

open Lean.Parser.Tactic in
def ctorNamesToRCasesPats (cns : Array CtorNames) : (TSyntax ``rcasesPatMed) :=
  Unhygienic.run do `(rcasesPatMed| $(cns.map (·.toRCasesPat)):rcasesPat|*)

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
