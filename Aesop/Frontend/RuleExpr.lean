/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Aesop.Builder.Cases
public import Aesop.Builder.Default
public import Aesop.Builder.Forward
public import Aesop.Builder.Unfold
public import Aesop.RuleSet.Filter

public section

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term


variable [Monad m] [MonadError m]


namespace Aesop.Frontend

namespace Parser

declare_syntax_cat Aesop.priority

syntax num "%" : Aesop.priority
syntax "-"? num : Aesop.priority

end Parser

inductive Priority
  | int (i : Int)
  | percent (p : Percent)
  deriving Inhabited

namespace Priority

def «elab» (stx : Syntax) : ElabM Priority :=
  withRef stx do
    unless ← shouldParsePriorities do throwError
      "unexpected priority."
    match stx with
    | `(priority| $p:num %) =>
      let p := p.raw.toNat
      match Percent.ofNat p with
      | some p => return percent p
      | none => throwError "percentage '{p}%' is not between 0 and 100."
    | `(priority| - $i:num) =>
      return int $ - i.raw.toNat
    | `(priority| $i:num) =>
      return int i.raw.toNat
    | _ => throwUnsupportedSyntax

instance : ToString Priority where
  toString
    | int i => toString i
    | percent p => p.toHumanString

def toInt? : Priority → Option Int
  | int i => some i
  | _ => none

def toPercent? : Priority → Option Percent
  | percent p => some p
  | _ => none

end Priority



namespace Parser

declare_syntax_cat Aesop.phase (behavior := symbol)

syntax "safe" : Aesop.phase
syntax "norm" : Aesop.phase
syntax "unsafe" : Aesop.phase

end Parser

def PhaseName.«elab» (stx : Syntax) : ElabM PhaseName :=
  withRef stx do
    match stx with
    | `(phase| safe) => return .safe
    | `(phase| norm) => return .norm
    | `(phase| unsafe) => return .«unsafe»
    | _ => throwUnsupportedSyntax


namespace Parser

declare_syntax_cat Aesop.builder_name (behavior := symbol)

syntax "apply" : Aesop.builder_name
syntax "simp" : Aesop.builder_name
syntax "unfold" : Aesop.builder_name
syntax "tactic" : Aesop.builder_name
syntax "constructors" : Aesop.builder_name
syntax "forward" : Aesop.builder_name
syntax "destruct" : Aesop.builder_name
syntax "cases" : Aesop.builder_name
syntax "default" : Aesop.builder_name

end Parser

inductive DBuilderName
  | regular (b : BuilderName)
  | «default»
  deriving Inhabited

namespace DBuilderName

def «elab» (stx : Syntax) : ElabM DBuilderName :=
  withRef stx do
    match stx with
    | `(builder_name| apply)        => return regular .apply
    | `(builder_name| simp)         => return regular .simp
    | `(builder_name| unfold)       => return regular .unfold
    | `(builder_name| tactic)       => return regular .tactic
    | `(builder_name| constructors) => return regular .constructors
    | `(builder_name| forward)      => return regular .forward
    | `(builder_name| destruct)     => return regular .destruct
    | `(builder_name| cases)        => return regular .cases
    | `(builder_name| default)      => return «default»
    | _ => throwUnsupportedSyntax

end DBuilderName

inductive IndexingMode : Type
  | unindexed
  | target (matchingConclusion : TransparencyMode)
  | hyps (matchingHypType : TransparencyMode)
  deriving Inhabited, BEq

namespace IndexingMode

partial def complete (matchable : Expr → MetaM α) :
    IndexingMode → MetaM (Option α × IndexingMode)
  | target matchingConclusion => do
    let some conclusion ← matchingConclusion |>
        run { mayPostpone := false, errIfMVarUnassigned := false }
      | throwError "aesop: index target did not match conclusion"
    let some result ← matchable conclusion
      | throwError "aesop: index target did not match"
    return (some result, target conclusion)
  | hyps matchingHypType => do
    let some hypType ← matchingHypType |>
        run { mayPostpone := false, errIfMVarUnassigned := false }
      | throwError "aesop: index target did not match hypothesis"
    let some result ← matchable hypType
      | throwError "aesop: index target did not match"
    return (some result, hyps hypType)
  | unindexed =>
    return (none, unindexed)

end IndexingMode

namespace Parser

syntax "target " term : Aesop.indexing_mode
syntax "hyp " term : Aesop.indexing_mode
syntax "unindexed " : Aesop.indexing_mode

end Parser

def IndexingMode.elab (stx : Syntax) : ElabM IndexingMode :=
  withRef stx do
    match stx with
    | `(indexing_mode| target $t:term) => return target t
    | `(indexing_mode| hyp $t:term) => return hyps t
    | `(indexing_mode| unindexed) => return unindexed
    | _ => throwUnsupportedSyntax

inductive TransparencySpec
  | transparency (t : TransparencyMode)
  | transparency! (t : TransparencyMode)
  deriving Inhabited

inductive BuilderOption
  | immediate (immediates : Array Name)
  | index (imodes : Array IndexingMode)
  | pattern (p : Term)
  | casesPatterns (ps : Array Term)
  | transparency (t : TransparencySpec)
  deriving Inhabited

namespace Parser

syntax transparency := &"default" <|> &"reducible" <|> &"instances" <|> &"all"

def elabTransparency (stx : TSyntax `Aesop.transparency) : TransparencyMode :=
  match stx.raw with
  | `(transparency| default) => .default
  | `(transparency| reducible) => .reducible
  | `(transparency| instances) => .instances
  | `(transparency| all) => .all
  | _ => unreachable!

end Parser

open Parser in
syntax " (" &"immediate" " := " "[" ident,+,? "]" ")" : Aesop.builder_option
syntax " (" &"index" " := " "[" Aesop.indexing_mode,+,? "]" ")" : Aesop.builder_option
syntax " (" &"pattern" " := " term ")" : Aesop.builder_option
syntax " (" &"cases_patterns" " := " "[" term,+,? "]" ")" : Aesop.builder_option
syntax " (" &"transparency" " := " transparency ")" : Aesop.builder_option
syntax " (" &"transparency!" " := " transparency ")" : Aesop.builder_option

namespace BuilderOption

def «elab» (stx : Syntax) : ElabM BuilderOption :=
  withRef stx do
    match stx with
    | `(builder_option| (immediate := $[$immediates],*)) =>
      return immediate $ immediates.map (·.getId)
    | `(builder_option| (index := $[$imodes],*)) =>
      return index $ ← imodes.mapM IndexingMode.elab
    | `(builder_option| (pattern := $p:term)) =>
      return pattern p
    | `(builder_option| (cases_patterns := $[$ps:term],*)) =>
      return casesPatterns ps
    | `(builder_option| (transparency := $t)) =>
      return transparency $ .transparency $ elabTransparency t
    | `(builder_option| (transparency! := $t)) =>
      return transparency $ .transparency! $ elabTransparency t
    | _ => throwUnsupportedSyntax

end BuilderOption

inductive RuleSets
  | all
  | ruleSets (ruleSets : Array Name)
  deriving Inhabited

namespace RuleSets

def toOption : RuleSets → Option (Array Name)
  | all => none
  | ruleSets ruleSets => some ruleSets

def toNames (default : Name) : RuleSets → Array Name
  | all => #[default]
  | ruleSets ruleSets => ruleSets

end RuleSets

namespace Parser

syntax ruleSetsFeature := "(" &"rule_sets" " := " "[" ident,+,? "]" ")"

end Parser

namespace RuleSets

def «elab» (stx : Syntax) : ElabM RuleSets :=
  withRef stx do
    match stx with
    | `(ruleSetsFeature| (rule_sets := [ $nss,* ])) =>
      return ruleSets $ nss.map (·.getId)
    | _ => throwUnsupportedSyntax

end RuleSets

namespace Parser

declare_syntax_cat Aesop.feature (behavior := symbol)

-- NOTE: This grammar has overlapping rules `ident`, `Aesop.phase` and
-- `Aesop.builder_name`, which can all consist of a single ident. For ambiguous
-- parses, a `choice` node with two children is created; one being an
-- `Aesop.phase` or `Aesop.builder_name` node and the other being a `featIdent`
-- node. When we process these `choice` nodes, we select the non-`ident` one.

syntax Aesop.phase : Aesop.feature
syntax Aesop.priority : Aesop.feature
syntax Aesop.builder_name : Aesop.feature
syntax Aesop.builder_option : Aesop.feature
syntax ruleSetsFeature : Aesop.feature
syntax (name := featIdent) ident : Aesop.feature
/--
A term in parentheses, optionally followed by projections. The projections are
attached to the term before it is elaborated, so `(Nat.add_comm n a).symm` can
be written without an extra pair of parentheses around the whole expression.
-/
syntax "(" term ")" ("." rawIdent)* : Aesop.feature

end Parser

inductive Feature
  | phase (p : PhaseName)
  | priority (p : Priority)
  | builder (b : DBuilderName)
  | builderOption (o : BuilderOption)
  | term (i : Term)
  | ruleSets (rs : RuleSets)
  deriving Inhabited

namespace Feature

-- Workaround for codegen bug, see #182
set_option compiler.extract_closed false in
partial def «elab» (stx : Syntax) : ElabM Feature :=
  withRef stx do
    match stx with
    | `(feature| $p:Aesop.priority) => priority <$> Priority.elab p
    | `(feature| $p:Aesop.phase) => phase <$> PhaseName.elab p
    | `(feature| $b:Aesop.builder_name) => builder <$> DBuilderName.elab b
    | `(feature| $o:Aesop.builder_option) => builderOption <$> BuilderOption.elab o
    | `(feature| $rs:ruleSetsFeature) => ruleSets <$> RuleSets.elab rs
    | `(feature| $i:ident) => return term i
    | `(feature| ($t:term)$[.$projs]*) =>
      return term ⟨projs.foldl (init := t) fun t proj =>
        mkNode ``Parser.Term.proj #[t, mkAtomFrom t ".", proj]⟩
    | stx => do
      if stx.isOfKind choiceKind then
        let nonIdentAlts :=
          stx.getArgs.filter λ stx => ! stx.isOfKind ``Parser.featIdent
        if h : nonIdentAlts.size = 1 then
          return ← «elab» $ nonIdentAlts[0]
      throwUnsupportedSyntax

end Feature


namespace Parser

declare_syntax_cat Aesop.rule_expr (behavior := symbol)

syntax Aesop.feature : Aesop.rule_expr
syntax Aesop.feature ppSpace Aesop.rule_expr : Aesop.rule_expr
syntax Aesop.feature " [" Aesop.rule_expr,+,? "]" : Aesop.rule_expr

end Parser

inductive RuleExpr
  | node (f : Feature) (args : Array RuleExpr)
  deriving Inhabited

namespace RuleExpr

open Parser in
partial def «elab» (stx : Syntax) : ElabM RuleExpr :=
  withRef stx do
    match stx with
    | `(rule_expr| $f:Aesop.feature $e:Aesop.rule_expr) => do
      let f ← Feature.elab f
      let e ← «elab» e
      return node f #[e]
    | `(rule_expr| $f:Aesop.feature [ $es:Aesop.rule_expr,* ]) => do
      let f ← Feature.elab f
      let es ← es.getElems.mapM «elab»
      return node f es
    | `(rule_expr| $f:Aesop.feature) => do
      let f ← Feature.elab f
      return node f #[]
    | _ => throwUnsupportedSyntax

partial def toArray : RuleExpr → Array (Array Feature)
  | node f args => do
    if args.isEmpty then
      return #[#[f]]
    else
      let mut result := #[]
      for arg in args do
        for features in toArray arg do
          result := result.push (#[f] ++ features)
      return result

end RuleExpr

end Aesop.Frontend
