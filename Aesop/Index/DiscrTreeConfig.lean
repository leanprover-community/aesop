/-
Copyright (c) 2021-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Lean

namespace Aesop

open Lean Lean.Meta

/-- The configuration used by all Aesop indices. -/
-- I don't really know what I'm doing here. I'm just copying the config used
-- by `simp`; see `Meta/Simp/Types.lean:mkIndexConfig`.
def indexConfig : ConfigWithKey :=
  ({ proj := .no, transparency := .reducible : Config }).toConfigWithKey

def mkDiscrTreePath (e : Expr) : MetaM (Array DiscrTree.Key) :=
  withConfigWithKey indexConfig $ DiscrTree.mkPath e

def getUnify (t : DiscrTree α) (e : Expr) : MetaM (Array α) :=
  withConfigWithKey indexConfig $ t.getUnify e

def getMatch (t : DiscrTree α) (e : Expr) : MetaM (Array α) :=
  withConfigWithKey indexConfig $ t.getMatch e

end Aesop
