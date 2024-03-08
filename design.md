# New Forward Reasoning Design

## Preliminaries

### Forward Rules

A *forward rule* is a tactic that, in a local context containing *input hypotheses* `h₁ : H₁, ..., hₙ : Hₙ`, produces *output hypotheses* `o₁ : O₁, ..., oₘ : Oₘ` and adds them to the context.
Both input hypotheses and output hypotheses are *telescopes*, so the types of later hypotheses may depend on earlier hypotheses.
We can also view the input hypotheses as a subcontext, since contexts are exactly telescopes.

Example: the lemma

```lean
theorem eq_of_le_ge : ∀ {n : Nat}, n ≤ 0 → n ≥ 0 → n = 0
```

induces a forward rule with input hypotheses `n : Nat, p : n ≤ 0, q : n ≥ 0` and output hypothesis `n = 0`.

We write `r : Φ → Ψ` for a rule with input hypotheses `Φ` and output hypotheses `Ψ`.
Note that `Ψ` generally depends on `Φ`.

To apply a rule `r : Φ → Ψ` to a goal `Γ ⊢ T` naively, we find all subcontexts `Δ ⊆ Γ` such that `Δ` matches `Φ`.
We then extend `Γ` with the output hypotheses `Ψ[Φ := Δ]`.

Note that we use matching rather than unification.
This means that metavariables in the context `Γ` are treated as opaque terms and are never assigned.
Rationale: if we have a hypothesis `h : T[?x]` in the context, where `T` is a type containing a metavariable `?x`, then there may be different forward rules which require different instantiations of `?x`.
We should not arbitrarily privilege any of these rules by assigning `?x` according to the instantiation determined by this rule.

An output hypothesis `h : T` is *redundant* if `T : Prop` and there is already a hypothesis `h' : T` in the context.
A goal `Γ ⊢ T` is *saturated* for a set of forward rules if all output hypotheses of the rules, when applied to `Γ`, are redundant.

Note that this notion of redundancy/saturation does not work for rules with non-`Prop` output hypotheses.
For example, a rule application which splits the hypothesis `p : ℕ × ℕ` into `m : ℕ` and `n : ℕ` is not redundant just because we already have a natural number `k : ℕ` in the context, since `m`, `n` and `k` are all different.
We therefore focus on `Prop`-valued forward rules.
The saturation criterion as stated also does not take into account computation.

### Destruct Rules

A *destruct rule* is a forward rule that, if it succeeds, clears the input hypotheses.
This is intended for rules which preserve all (relevant) information from the input hypotheses in the output hypotheses.
The lemma `eq_of_le_ge` above would be suitable as a destruct rule.

The advantage of destruct rules is that we don't have to worry about a rule applying multiple times to subgoals: the input hypotheses are gone after the rule has been applied.

A complication: when other hypotheses in the context depend on the input hypotheses, the input hypotheses cannot be cleared.
So then the destruct rule becomes a regular forward rule.
Perhaps it would be sensible to clear only the `Prop`-valued input hypotheses, on which nothing will reasonably depend (because of proof irrelevance).
This is probably the more useful behaviour anyway: if we apply `eq_of_le_ge`, we want to clear `n ≤ 0` and `n ≥ 0`, but not `n`.

## Faster Forward Reasoning

Currently, forward/destruct rules (henceforth just forward rules) can be registered in any Aesop phase (i.e., as norm, safe or unsafe rules) and can be given a priority.
We propose to keep these semantics exactly the same, but to speed up the selection and application of forward rules with a *forward rule index* and a *forward state*.
This forward state is a data structure associated to each goal in the search tree.
It caches information about the local context of the goal and uses this cached information to quickly find forward rules that can be applied to the goal.

### Preliminaries

For a rule `r : Φ → Ψ` with input hypotheses `Φ = (x₁ : T₁) ... (xₙ : Tₙ)`, we call `xᵢ` a *maximal input hypothesis* if there is no `j > i` such that `Tⱼ` depends on `xᵢ`, and a *non-maximal input hypothesis* otherwise.
If we find matching hypotheses for all maximal input hypotheses in the local context, we can apply `r`, since each non-maximal input hypothesis is uniquely determined by at least one maximal input hypothesis.

Each maximal input hypothesis has a unique index between `1` and `n`.
We call theses indices *slots* of `r` and define `slots(r)` as the set of slots of `r`.

Given a slot `i` and hypothesis `h : T` with `T ≡[σ] Tᵢ` (i.e. `σ` is the substitution that results from unifying `T` and `Tᵢ`), we say that `h` is *suitable for slot `i`* and define `sub(h) ≔ σ`.

A *shared variable* of `r` is an input hypothesis `xᵢ` such that there are at least two input hypothesis types `Tⱼ`, `Tₖ` in which `xᵢ` occurs.
A shared variable is necessarily a non-maximal input hypothesis.
We also write `?xᵢ` to emphasise that we interpret `xᵢ` as a variable (and, in the code, as a metavariable).
The *shared variables of a slot* `i` of `r` are those shared variables `?x` that occur in `Tᵢ` and in at least one slot `j < i`.

A *match* `M` for `r` is a partial map from slots of `r` to hypotheses in the context.
It must satisfy the following conditions:

- For each slot `i` of `r`, if `M(i)` is defined, then `M(i) ≡ Tᵢ` with a substitution `σᵢ`.
  The domain of this substitution is a subset of the non-maximal input hypotheses.
- For all slots `i` and `j` of `r` such that `M(i)` and `M(j)` are defined, `σᵢ` and `σⱼ` are compatible.
- `M` is downward-closed: if `M(i)` is defined, then for any slot `j < i` of `r`, `M(j)` is also defined.

A match of `r` is *complete* if `M(i)` is defined for every slot `i` of `r`, and *incomplete* otherwise.
The *level of a match* `M`, `lvl(M)`, is the maximal `i` such that `M(i)` is defined.
The *substitution of a match* `M`, `sub(M)`, is the union of the substitutions `σᵢ` for each `i` such that `Mᵢ` is defined.
This union is defined since the `σᵢ` are pairwise compatible.
The *shared variables of a match* `M` are the shared variables of `lvl(M)`.

Hypotheses in a local context are identified by a *unique name*.
If a tactic changes the type (and possibly value) of a hypothesis but the new type/value is defeq to the old one, the hypothesis's unique name does not need to change.
Otherwise, the tactic adds a new hypothesis and deletes the old one.
However, there are also tactics which change the unique names of hypotheses even though the types/values of these hypotheses remain unchanged.

### Forward State Interface

A *forward state* `s` contains metadata about a local context and supports the following operations:

- `AddHyps(s, Γ)` adds the hypotheses `Γ` to `s`.
- `RemoveHyps(s, Γ)` removes the hypotheses `Γ` from `s`.
- `ApplyFVarSubst(s, σ)` applies the unique name substitution `σ` to `s`.
  A unique name substitution is a mapping from unique names to unique names.
  The mapping `σ(h) = h'` indicates that hypothesis `h'` in the current local context corresponds to `h` in `s` and has merely been renamed.
  The types and values (if any) of `h` and `h'` must be defeq.
- `GetSafeRules(s)` returns all tuples `(r, M)` such that
  - `r : Φ → Ψ` is a safe forward rule;
  - `M` is a complete match for `r`;
  - this tuple has not been previously been discarded by `PopNorm(s)`, `PopSafe(s)` or `PopUnsafe(s)`.
  The tuples are ordered by the rule's priority (with ties broken arbitrarily).
- `GetUnsafeRules(s)` works like `GetSafeRules(s)` but for unsafe rules.
- `GetFirstNormRule(s)` returns a tuple `(r, Γ)` as in `GetSafeRules(s)`, but `r` is the highest-priority norm forward rule that satisfies all other conditions.
- `PopNormRule(s)`, `PopSafeRule(s)` and `PopUnsafeRule(s)` discard the first tuple `(r, M)` that would otherwise be returned by `GetSafeRules(s)`.

### Forward State Usage

#### Overview

We use the forward state in two ways:

1. When selecting rules for a goal `G`, we use the forward state to efficiently determine forward rules that may be applicable to `G`.
2. When a rule is executed on a goal `G` and yields subgoals `G₁, ..., Gₙ`, we must construct forward states for the subgoals `Gᵢ`.
   To facilitate this, the rule produces a *context diff* that indicates what changed in the context.
   For forward rules, this diff is almost trivial since we just add hypotheses.
   (Destruct rules may additionally delete some hypotheses.)

#### Selecting Forward Rules

Given a goal `G` with forward state `s`, to select safe and unsafe rules we simply use `GetSafeRules(s)` and `GetUnsafeRules(s)`.

To select norm rules, we use `GetFirstNormRule(s)`.
We must update `s` after every application of a norm rule, so there is no need to select multiple norm rules at once.

After a forward rule has been successfully applied, we use `PopNormRule(s)`/`PopSafeRule(s)`/`PopUnsafeRule(s)` to remove it from the forward state.

#### Constructing Forward States

The forward state for a goal `G` caches information about the local context of `G`.
As such, we can always construct a forward state from `G`.
However, the whole idea behind forward states is that it is much cheaper to take the forward state of the parent goal of `G` and make some (usually small) adjustments.

Hence, when a rule `r` is run in context `Γ`, the rule reports a *context diff* for each subgoal `G` with context `Δ`.
This is a tuple `(A, R, σ)` where

- `A` is the set of hypotheses that were added to `G`;
- `R` is a set of hypotheses that were removed from `G`;
- `σ` is a unique name substitution from `Γ` to `Δ`.

The context diff must accurately reflect the changes made by `r`, i.e.

```
Δ = σ(Γ \ R), A
```

up to reordering of hypotheses.

The forward state for the child goal `G` is then

```
AddHyps(ApplyFVarSubst(RemoveHyps(s, R), σ), A)
```

If a rule does not generate a context diff, we compute it.
However, we can't reasonably construct `σ` for a tactic which renamed some hypotheses, so we must treat the renamed hypotheses as added/removed.
It remains to be seen whether this is a problem in practice.

### Forward State Implementation

#### Indexing

We use a discrimination tree `I` to index forward rules.
`I` maps types `T` to sets of pairs `(r, i)` where `r : (x₁ : T₁) ... (xₙ : Tₙ) → Ψ` is a rule, `i` is a slot of `r` and `T` is likely defeq to `Tᵢ`.
We use this index to quickly determine the rules for which a new hypothesis is likely relevant.
The index `I` is not goal-specific, so it can be built once and for all before the search starts.

#### Complete Match Queues

The forward state contains three *complete match queues* `πₙ`, `πₛ` and `πᵤ` for norm, safe and unsafe rules.
These store tuples `(r, M)` where `r` is a rule and `M` is a complete match for `r`.
Collectively, `πₙ`, `πₛ` and `πᵤ` contain all such tuples except those which have previously been popped.
The queues are ordered by rule priority, with ties broken arbitrarily.
`GetFirstNormRule`, `GetSafeRules`, `GetUnsafeRules`, `PopNormRule`, `PopSafeRule` and `PopUnsafeRule` operate on the complete match queues in the expected manner.

#### Rule States

##### Overview

A forward state `s` for goal `G` maps each rule `r` to a *rule state*.
This is a data structure containing all incomplete matches for `r` that can be constructed in the local context of `G`.

When a hypothesis `h : T` is added to `s`, we use the index to determine those rules `r` with an input hypothesis likely matching `T`.
We then unify `T` and the type of the input hypothesis and if this unification is successful, we update the rule state for `r`.
Any complete matches discovered during this update are added to the complete match queues.

##### Data Structure

For each shared variable `?x`, the rule state for a rule `r : (x₁ : T₁) ... (xₙ : Tₙ) → Ψ` contains a *variable map* `μₓ`.
This map associates pairs `(t, i)`, where `t` is an expression and `i` is a slot of `r`, to pairs `(𝕄, ℍ)`, where

- `𝕄` is the set of all incomplete matches `M` for `r` in the local context with `lvl(M) = i` and `sub(M)(?x) = t`.
  In other words, `𝕄` contains exactly those partial matches which already contain assignments for all slots up to `i` and which instantiate `?x` with `t`.
- `ℍ` is the set of all hypotheses `h` suitable for `i` with `sub(h)(?x) = t`, i.e. the set of hypotheses which match `Tᵢ` while instantiating `?x` with `t`.

##### Basic Operations

`AddHypothesis(h, i)` adds a hypothesis `h` suitable for slot `i` to the variable maps of the shared variables of `i`.

```
AddHypothesis(h, i):
  For each shared variable ?x of i:
    Let (𝕄, ℍ) := μₓ(t, i)
    Update μₓ(t, i) := (𝕄, ℍ ∪ {h})
```

`AddMatch(M)` adds a partial match `M` to the variable maps of the shared variables of `M`.

```
AddMatch(M):
  If M is complete:
    Push (r, M) onto πₙ, πₛ or πᵤ according to the type of the rule r
  Else:
    For each shared variable ?x of M:
      Let t := μₓ(sub(M)(?x))
      Let (𝕄, ℍ) := μₓ(t, lvl(M))
      Update μₓ(t, lvl(M)) := (𝕄 ∪ {M}, ℍ)
```

`LookupMatches(h, i)`, where `h` is a hypothesis suitable for slot `i`, looks up those partial matches `M` with `lvl(M) = i - 1` for which `sub(M)` and `sub(h)` are compatible.

```
LookupMatches(h, i):
  If i = 1:
    Return ∅
  For each shared variable ?xⱼ of i:
    Let (𝕄ⱼ, _) ≔ μₓⱼ(σ(xₖ), i - 1)
  Return ⋂ⱼ 𝕄ⱼ
```

`LookupHypotheses(M)`, where `M` is a match, looks up hypotheses `h` suitable for `lvl(M) + 1` such that `sub(h)` and `sub(M)` are compatible.

```
LookupHypotheses(M):
  For each shared variable ?xⱼ of lvl(M) + 1:
    Let (_, ℍⱼ) ≔ μₓⱼ(sub(M)(xⱼ), lvl(M) + 1)
  Return ⋂ⱼ ℍⱼ
```

Note: both `LookupMatches(h, i)` and `LookupHypotheses(M)` wrongly return the empty set if the set of shared variables of `i` or `lvl(M)` is empty.
However, we can make sure that this doesn't happen by partitioning the input hypotheses into mvar clusters and using a separate rule state for each mvar cluster.

##### Insertion

When the index indicates that a hypothesis `h : T` may match the input hypothesis `xᵢ : Tᵢ`, we first determine whether `h` is indeed suitable for `i`.
If so, we run the following function.

```
Insert(h, i):
  AddHypothesis(h, i)
  If i = 1:
    AddMatch({i ↦ H})
  Else:
    For each match M in LookupMatches(h, i):
      AddMatch(M ∪ {i ↦ H}).
```

##### Comparison with Substitution Trees

We could also implement the rule state with a standard substitution tree.
A substitution tree stores substitutions and supports queries for compatible substitutions.
However, it likely performs badly since insertion into a substitution tree is expensive, and we do a lot of insertions.

##### Optimisations

1. When we create new matches, we always do so by adding data to existing matches.
   As a result, much data is shared between matches.
   We should choose a data representation (e.g. linked lists) that allows us to exploit this sharing.
2. A match at level 1 is just a hypothesis.
   Storing these matches is therefore redundant when we're already storing the hypotheses.
   Similarly, we don't need to store matches at the maximal level `n` since they are already complete.
3. The intersection of sets of hypotheses/matches can be computed efficiently if we give each hypothesis and each match a unique identifier.
   In this case, the intersection comes down to an intersection of sets of natural numbers, which is very efficient.
4. Similarly, we can give a unique identifier to each instantiation of a variable.
   This should speed up lookups and insertions into the variable maps `μₓ`, which are quite frequent.

#### Deletion

To implement `RemoveHyps`, we add a set `ρ` of removed hypotheses to the forward state.
Then, whenever we construct a new partial match or return a complete partial match, we check whether any of its hypotheses are contained in `ρ`.
If so, we remove it from the forward state.

Alternatively, we could do a linear scan through all the rule states every time `RemoveHyps` is called, but this would likely be less efficient.

Yet another alternative would be to check `ρ` only when we get a complete match.
This implies that we may do unnecessary work on partial matches that will never become viable because one of their components has vanished.
Whether this tradeoff is worth it needs to be investigated empirically.

#### FVar Substitution

To implement `ApplyFVarSubst`, we add an fvar substitution `τ` to the forward state.
Then, whenever we refer to a hypothesis `h` and `τ(h)` is defined, we replace `h` with `τ(h)`.

Can we avoid these many lookups into `τ`?
We could version `τ` with a natural number `v` which is incremented each time `ApplyFVarSubst` is called.
We then annotate each hypothesis name `h` with a version number `w` which indicates that `τ(h) = h` for version `w` of `τ`.
If we then look up a hypothesis name with `w = v`, we can skip the lookup into `τ`.
This means that there is only one such lookup for each application of `ApplyFVarSubst` and each hypothesis name, so we are asymptotically no worse than a linear scan through the data structure.
A similar optimisation also applies to `RemoveHyps`.

## Pattern-Based Forward Rules

TODO sync this with the implementation

For the applications below, our notion of forward rules is too restrictive.
Forward rules in the sense discussed so far are triggered by the presence of certain hypotheses.
But we also want forward rules that are triggered by the presence of terms of a certain shape in a hypothesis (or in the target).
For example, a rule may establish `0 ≤ ↑n`, where `↑n` is the coercion to `Int` of a natural number `n` and `↑n` appears somewhere in the goal.
Similarly, it may be useful to establish `min x y ≤ x` and `min x y ≤ y` for any occurrence of the pattern `min ?x ?y` in the goal.

### Definition

A *pattern-based forward rule* consists of

- A *pattern* `p`.
  This is an expression with free variables (metavariables) `x₁ : T₁, ..., xₙ : Tₙ`.
  For now, we only consider forward rules with a single pattern.
- A forward rule `r : ∀ xᵢ : Tᵢ, Φ → Ψ`, where both the input and output hypotheses may depend on the variables `xᵢ`.
  (This notation is a bit fishy — the rule is really a tactic which receives a substitution for the `xᵢ` and can do whatever it wants with this.)

When applying a forward rule to a goal `Γ ⊢ T`, we first check whether any subterm `t` of `Γ` or `T` unifies with `p` (structurally or with reducible transparency?).
If so, we obtain instantiations `u₁ : T₁, ..., uₙ : Tₙ` for the pattern variables.
We then apply the forward rule `r u₁ ... uₙ` as usual.

### Integration Into Accumulating Partial Matches Algorithm

We extend the *match* structure with a substitution `σ` resulting from a pattern.

We add a discrimination tree `M₃` to the rule index.
This tree maps patterns to rules for which the pattern is relevant.

When a new hypothesis `h : T` arrives, we look up every subterm of `T` in `M₃`.
Each match yields a rule `r` and a substitution `σ`.
We then add `σ` to the match map of `r`.

When checking whether a match is valid, we now use `σ` as the initial substitution (rather than `∅`).

## Falsifying the Goal

In a typical saturation-based prover, we negate the target at the start and try to derive a contradiction.
This is also how `linarith` currently works.
We can integrate this idea as follows:

- Negate the target at the start and introduce it.
- Keep track of which rule applications used the negated target (transitively).
- At the end of the forward phase, when we haven't found a contradiction, throw away the output hypotheses resulting from rule applications that used the negated target (and throw away the negated target).

Completeness issue: during the search, we might throw away rule applications that are redundant.
E.g. when a prior rule application `R₁` produced an output hypothesis `o₁ : O` and a later rule application `R₂` produces `o₂ : O`, we throw away `o₂`.
However, if `o₁` doesn't depend on the negated target while `o₂` does, then we should throw away `o₁` instead, since `o₁` holds only conditionally.

## Application: Positivity

Mathlib's `positivity` tactic [1] establishes facts of the form `0 < t` (positivity), `0 ≤ t` (nonnegativity) and `0 ≠ t` (nonzeroness).
It does this by going through the term `t`, which must be composed of function symbols and variables such that each function symbol has a registered *positivity extension*.
Such an extension tells `positivity` how to combine positivity/nonnegativity/nonzeroness information about the function arguments into a positivity/nonnegativity/nonzeroness result about the function application.

[1] https://github.com/leanprover-community/mathlib4/blob/26eb2b0ade1d7e252d07b13ea9253f9c8652facd/Mathlib/Tactic/Positivity/Core.lean

For example, the positivity extension for `min` matches a term `min a b`, analyses `a` and `b` and combines the results:

- If `a < 0` and `b < 0`, then `min a b < 0`.
- If `a > 0` and `b > 0`, then `min a b > 0`.
- If `a ≤ 0` and `b < 0`, then `min a b ≤ 0`.
- Etc.

See [2] for more extensions.

[2] https://github.com/leanprover-community/mathlib4/blob/26eb2b0ade1d7e252d07b13ea9253f9c8652facd/Mathlib/Tactic/Positivity/Basic.lean

This is essentially just forward reasoning with pattern-based rules, where the rules are applied 'inside-out'.
So I believe once we have efficient support for such forward rules, we could emulate `positivity` in Aesop without much efficiency loss.
Advantages:

- With incremental forward rules, we get incremental positivity checking, which should be much more efficient than running `positivity` over and over again.
- The results of `positivity` are available to other forward rules, and the results of other forward rules to `positivity`.
  - The first part is nice because with the current Aesop architecture, rules have to ask for a positivity result if they need it, which may happen repeatedly.
    Adding these results to the context can be seen as perfect caching.
  - The second part is nice because `positivity` extensions cannot currently make use of any information that is not of the form `0 < t`, `0 ≤ t` or `0 ≠ t`.
    But surely there are modules which could be interested in other facts (TODO find examples).
    
### TODO: Why Not Backwards Rules?

## Application: Arithmetic Forward Reasoning

The Polya paper [1] describes a heuristic solver for problems involving real inequalities.
Rob Lewis's MSc thesis [2] has more details.

[1] https://arxiv.org/pdf/1404.4410.pdf
[2] https://robertylewis.com/files/ms_thesis.pdf

The basic idea is to perform heuristic forward reasoning with a 'blackboard' architecture.
The blackboard is a central data structure that contains arithmetic information, specifically comparisons between subterms of the original goal.
This information is in some canonical form.
The solver then runs 'modules', which are functions that derive additional comparisons from the comparisons currently found on the blackboard.
For example, a module about the `min` function could identify all terms of the form `min(x₁, ..., xₙ)` that appear in any comparisons on the blackboard and assert `min(x₁, ..., xₙ) ≤ xᵢ` for `i = x, ..., n`.

Particularly interesting are the Fourier-Motzkin modules, which use Fourier-Motzkin elimination to derive facts about sums and products.
Essentially, given a system of linear inequalities, we can derive comparisons between any two variables `xᵢ` and `xⱼ` by eliminating all other variables from the system.

I believe that forward rules could be used to implement something akin to Polya as an Aesop rule set.
The local context would play the part of Polya's blackboard, and forward rules would play the part of Polya's modules.

However, there are various challenges:

- Polya's blackboard is not just a list of hypotheses; it's a data structure that performs, for example, consistency checks between the current hypotheses.
  The blackboard API would have to be emulated by additional rules, which would probably be expensive.
- Polya only deals with real inequalities, but we also need integer and natural inequalities.
  So we're looking to copy Polya's architecture, but not necessarily the specific modules.
- Polya includes a normalisation pass that canonises terms.
  We could implement this as a normalisation rule.

## Meeting with Son 2024-01-16

- feature request for conditional rewrite rules: either leave as Aesop subgoals or to prove manually
  - example: in ℤ/qℤ, `x invertible → xx⁻¹ = 1`.
    But in Son's use case, `x` is always invertible, so Aesop should either prove this goal or leave it to the user.
  - solution: add a `simp` discharger that 'solves' preconditions with mvars and either adds these as subgoals or leaves them to the user
  - needs new annotation for "leave this goal to the user"
- feature request: forward rules with multiple subgoals
  - possible solution: generate `P ∨ Q` and split later
  - use case: `linarith` wants `x ≠ y` to be split into `x < y ∨ x > y`
