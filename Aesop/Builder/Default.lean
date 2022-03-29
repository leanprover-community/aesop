/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Builder.Constructors
import Aesop.Builder.NormSimp
import Aesop.Builder.Tactic

open Lean
open Lean.Meta

namespace Aesop

private def throwDefaultBuilderFailure (ruleType : String) (id : Name) : MetaM α :=
  throwError "aesop: Unable to interpret {id} as {ruleType} rule. Try specifying a builder."

namespace GlobalRuleBuilder

-- TODO In the default builders below, we should distinguish between fatal and
-- nonfatal errors. E.g. if the `tactic` builder finds a declaration that is not
-- of tactic type, this is a nonfatal error and we should continue with the next
-- builder. But if the simp builder finds an equation that cannot be interpreted
-- as a simp lemma for some reason, this is a fatal error. Continuing with the
-- next builder is more confusing than anything because the user probably
-- intended to add a simp lemma.

def unsafeRuleDefault : GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  constructors decl <|>
  tactic TacticBuilderOptions.default decl <|>
  apply decl <|>
  throwDefaultBuilderFailure "an unsafe" decl

def safeRuleDefault : GlobalRuleBuilder RegularRuleBuilderResult := λ decl =>
  constructors decl <|>
  tactic TacticBuilderOptions.default decl <|>
  apply decl <|>
  throwDefaultBuilderFailure "a safe" decl

def normRuleDefault : GlobalRuleBuilder NormRuleBuilderResult := λ decl =>
  NormRuleBuilderResult.regular <$> tactic TacticBuilderOptions.default decl <|>
  normSimpLemmas decl <|>
  NormRuleBuilderResult.regular <$> apply decl <|>
  throwDefaultBuilderFailure "a norm" decl

end GlobalRuleBuilder


namespace LocalRuleBuilder

def unsafeRuleDefault : LocalRuleBuilder RegularRuleBuilderResult :=
  λ hypUserName goal =>
    apply hypUserName goal <|>
    throwDefaultBuilderFailure "an unsafe" hypUserName

def safeRuleDefault : LocalRuleBuilder RegularRuleBuilderResult :=
  λ hypUserName goal =>
    apply hypUserName goal <|>
    throwDefaultBuilderFailure "a safe" hypUserName

def normRuleDefault : LocalRuleBuilder NormRuleBuilderResult :=
  λ hypUserName goal =>
    throwError "aesop: Please specify a builder for norm rule {hypUserName}."

end LocalRuleBuilder


namespace RuleBuilder

def unsafeDefault : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.unsafeRuleDefault
    LocalRuleBuilder.unsafeRuleDefault

def safeDefault : RuleBuilder RegularRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.safeRuleDefault
    LocalRuleBuilder.safeRuleDefault

def normDefault : RuleBuilder NormRuleBuilderResult :=
  ofGlobalAndLocalRuleBuilder GlobalRuleBuilder.normRuleDefault
    LocalRuleBuilder.normRuleDefault

end RuleBuilder

end Aesop
