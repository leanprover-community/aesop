/-
Copyright (c) 2021-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Rule

namespace Aesop

inductive BaseRuleSetMember
  | normRule (r : NormRule)
  | unsafeRule (r : UnsafeRule)
  | safeRule (r : SafeRule)
  | unfoldRule (r : UnfoldRule)
  deriving Inhabited

def BaseRuleSetMember.name : BaseRuleSetMember → RuleName
  | normRule r => r.name
  | unsafeRule r => r.name
  | safeRule r => r.name
  | unfoldRule r => r.name

inductive GlobalRuleSetMember
  | base (m : BaseRuleSetMember)
  | normSimpRule (e : NormSimpRule)
  deriving Inhabited

def GlobalRuleSetMember.name : GlobalRuleSetMember → RuleName
  | base m => m.name
  | normSimpRule r => r.name

inductive LocalRuleSetMember
  | global (m : GlobalRuleSetMember)
  | localNormSimpRule (r : LocalNormSimpRule)
  deriving Inhabited

def LocalRuleSetMember.name : LocalRuleSetMember → RuleName
  | global m => m.name
  | localNormSimpRule r => r.name

def LocalRuleSetMember.toGlobalRuleSetMember? :
    LocalRuleSetMember → Option GlobalRuleSetMember
  | global m => some m
  | _ => none

end Aesop
