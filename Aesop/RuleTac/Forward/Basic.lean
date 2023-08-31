/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Batteries.Lean.Meta.Basic

namespace Aesop

open Lean Lean.Meta

/-
Forward rules must only succeed once for each combination of immediate
hypotheses; otherwise any forward rule could be applied infinitely often (if
it can be applied at all). We use the following scheme to ensure this:

- Whenever we add a hypothesis `h : T` as an instance of a forward rule, we also
  add an `implDetail` decl `h' : T`.
- Before we add a hypothesis `h : T`, we check whether there is already an
  `implDetail` `h' : T`. If so, `h` is not added.

This scheme ensures that forward rules never add more than one hypothesis of
any given type. `h'` is added as an `implDetail`, rather than as a regular
hypothesis, to ensure that future rule applications do not change its type.
-/

-- Prefix of the regular hyps added by `forward`.
def forwardHypPrefix := `fwd

-- Prefix of the `implDetail` hyps added by `forward`.
def forwardImplDetailHypPrefix := `_fwd

-- Names for the `implDetail` hyps added by `forward`.
def mkFreshForwardImplDetailHypName : MetaM Name :=
  mkFreshIdWithPrefix forwardImplDetailHypPrefix

def isForwardImplDetailHypName (n : Name) : Bool :=
  forwardImplDetailHypPrefix.isPrefixOf n

end Aesop
