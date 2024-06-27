/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Batteries.Lean.Meta.Basic
import Aesop.Util.Basic

namespace Aesop

open Lean Lean.Meta

/-
Forward rules must only succeed once for each combination of immediate
hypotheses; otherwise any forward rule could be applied infinitely often (if
it can be applied at all). We use the following scheme to ensure this:

- Whenever we add a hypothesis `h : T` as an instance of a forward rule, we also
  add an `implDetail` hypothesis `h' : T`.
- Before we add a hypothesis `h : T`, we check whether there is already an
  `implDetail` `h' : T`. If so, `h` is not added.

This scheme ensures that forward rules never add more than one hypothesis of
any given type. `h'` is added as an `implDetail`, rather than as a regular
hypothesis, to ensure that future rule applications do not change its type.

We also encode two pieces of data in the name of `h`: the name `h` and the
*forward depth* of `h`. The forward depth of a hypothesis not generated by
forward reasoning is 0. The forward depth of a hypothesis `h` generated by
forward reasoning is one plus the maximal forward depth of any hypothesis used
in the proof of `h`. The `saturate` tactic uses this information to limit its
reasoning depth.
-/

/-- Prefix of the regular hyps added by `forward`. -/
def forwardHypPrefix := `fwd

/-- Prefix of the `implDetail` hyps added by `forward`. -/
def forwardImplDetailHypPrefix := `__aesop.fwd

/-- Name of the `implDetail` hyp corresponding to the forward `hyp` with name
`fwdHypName` and depth `depth`. -/
def forwardImplDetailHypName (fwdHypName : Name) (depth : Nat) : Name :=
  .num forwardImplDetailHypPrefix depth ++ fwdHypName

/--
Parse a name generated by `forwardImplDetailHypName`, obtaining the
`fwdHypName` and `depth`.
-/
def matchForwardImplDetailHypName (n : Name) : Option (Nat × Name) :=
  match n.components with
  | `__aesop :: `fwd :: .num .anonymous depth :: components =>
    let name := Name.ofComponents components
    some (depth, name)
  | _ => none

/--
Check whether the given name was generated by `forwardImplDetailHypName`.
We assume that nobody else adds hyps with the `forwardImplHypDetailPrefix`
prefix.
-/
def isForwardImplDetailHypName (n : Name) : Bool :=
  (`__aesop.fwd).isPrefixOf n

end Aesop
