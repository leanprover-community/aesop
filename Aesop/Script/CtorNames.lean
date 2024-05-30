import Aesop.Util.Basic

open Lean Lean.Meta

namespace Aesop

structure CtorNames where
  ctor : Name
  args : Array Name
  /-- Whether the constructor has at least one implicit argument. -/
  hasImplicitArg : Bool

namespace CtorNames

def toRCasesPat [Monad m] [MonadQuotation m] (cn : CtorNames) :
    m (TSyntax `rcasesPat) := do
  let ns ← cn.args.mapM λ n =>
    `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent n):ident)
  if cn.hasImplicitArg then
    `(rcasesPat| @⟨ $ns,* ⟩)
  else
    `(rcasesPat| ⟨ $ns,* ⟩)

def toAltVarNames (cn : CtorNames) : AltVarNames where
  explicit := true
  varNames := cn.args.toList

def mkFreshArgNames (lctx : LocalContext) (cn : CtorNames) :
    CtorNames × LocalContext :=
  let (args, lctx) := getUnusedNames lctx cn.args
  ({ cn with args }, lctx)

end CtorNames

open Lean.Parser.Tactic Syntax in
def ctorNamesToRCasesPats [Monad m] [MonadQuotation m] (cns : Array CtorNames) :
    m (TSyntax ``rcasesPatLo) := do
  -- I can't figure out the quotation magic to generate the stuff below.
  let pat : TSyntax ``rcasesPatMed :=
    ⟨mkNode ``rcasesPatMed #[mkSep (← cns.mapM (·.toRCasesPat)) (mkAtom "|")]⟩
  `(rcasesPatLo| $pat)

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
