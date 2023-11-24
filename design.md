# New Forward Reasoning Design

## Forward Rules

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

To apply a rule `r : Φ → Ψ` to a goal `Γ ⊢ T`, we find all subcontexts `Δ ⊆ Γ` such that `Δ` unifies with `Φ`.
We then extend `Γ` with the output hypotheses `Ψ[Φ := Δ]`.

An output hypothesis `h : T` is *redundant* if `T` is a `Prop` and there is already a hypothesis `h' : T` in the context.
A goal `Γ ⊢ T` is *saturated* for a set of forward rules if all output hypotheses of the rules, when applied to `Γ`, are redundant.

Note that this notion of redundancy/saturation does not work for rules with non-`Prop` output hypotheses.
For example, a rule application which splits the hypothesis `p : ℕ × ℕ` into `m : ℕ` and `n : ℕ` is not redundant just because we already have a natural number `k : ℕ` in the context, since `m`, `n` and `k` are all different.
I suggest we ignore this complication and focus on `Prop`-valued forward rules.

TODO NOTE: we don't do unification but just matching, meaning we don't instantiate mvars in the context when we match input hypotheses against them.

## Proposed Integration into Aesop Search

Currently, Aesop proceeds in three phases when faced with a goal:

1. Normalise the goal. This means in particular that we run `simp_all`.
2. Apply safe rules as much as possible.
   (The new goals created during this are also normalised.)
3. Apply unsafe rules.

We propose that we split each phase into two subphases: a *forward subphase* in which we apply only forward rules, and a *regular subphase* in which we apply all other rules.

Note: if we falsify the goal (as discussed below), we have to preserve the saturated context with falsified goal between the norm forward phase and the safe forward phase.
But maybe we don't need forward norm rules at all.

Alternatives:

1. Introduce a separate *forward phase* between the normalisation phase (1) and the safe phase (2).
2. Don't have separate phases at all.

## Falsifying the Goal

In a typical saturation-based prover, we negate the target at the start and try to derive a contradiction.
This is also how `linarith` currently works.
We can integrate this idea as follows:

- Negate the target at the start and introduce it.
- Keep track of which rule applications used the negated target (transitively).
- At the end of the forward phase, when we haven't found a contradiction, throw away the output hypotheses resulting from rule applications that used the negated target (and throw away the negated target).

Completeness issue: during the search, we might throw away rule applications that are redundant.
E.g. when a prior rule application `R₁` produced an output hypothesis `o₁ : O` and a later rule application `R₂` produces `o₂ : O`, we throw away `o₂`.
However, we should not do this if `o₂` doesn't use the negated target but `o₁` does.

## Destruct Rules

A *destruct rule* is a forward rule that, if it succeeds, clears the input hypotheses.
This is intended for rules which preserve all (relevant) information from the input hypotheses in the output hypotheses.
The lemma `eq_of_le_ge` above would be suitable as a destruct rule.

The advantage of destruct rules is that we don't have to worry about a rule applying multiple times to subgoals: the input hypotheses are gone after the rule has been applied.

A complication: when other hypotheses in the context depend on the input hypotheses, the input hypotheses cannot be cleared.
So then the destruct rule becomes a regular forward rule.
Perhaps it would be sensible to clear only the `Prop`-valued input hypotheses, on which nothing will reasonably depend (because of proof irrelevance).
This is probably the more useful behaviour anyway: if we apply `eq_of_le_ge`, we want to clear `n ≤ 0` and `n ≥ 0`, but not `n`.

## Indexing Problem

The indexing problem is about efficiently finding all forward rules that may apply to a goal.
We need to do this at least for the root goal.

### Problem

To apply forward rules to a goal `Γ ⊢ T`, we must efficiently find all rules `r : Φ → Ψ` such that `Φ` is a subcontext of `Γ`.
After the found rules have been applied, the context is extended with output hypotheses `Γ₁`, so we must now find all rules `r : Φ₁ → Ψ₁` such that `Φ₁` is a subcontext of `Γ, Γ₁`, and so on until all rules fail.

### Solution: Iterated Discrimination Trees

We use a discrimination tree which maps input hypothesis types to

- an array of rules (these are rules which require only one hypothesis of the given type); and
- another discrimination tree (for rules which require multiple hypotheses).
  
For a rule `r : ∀ (h₁ : T₁) ... (hₙ : Tₙ), Ψ`, the *indexed hypotheses* are those input hypotheses `hᵢ₁, ..., hᵢₘ` that don't have forward dependencies, i.e. where there is no `hⱼ : Tⱼ` such that `hᵢₖ` appears in `Tⱼ`.
We restrict indexing to these hypotheses.
This makes sense because the values of non-indexed hypotheses (i.e. those with forward dependencies) are determined by unification as soon as we know the values of the indexed hypotheses.
In effect, we treat non-indexed hypotheses as implicit arguments.
  
#### Naive Scheme
  
To index a rule `r` with indexed hypotheses `h₁ : T₁, ..., hₙ : Tₙ`, we map each `Tᵢ` to a discrimination tree which indexes the `hⱼ` for `j ≠ i`, recursively.
Once `n = 1`, the recursion terminates and we map `T₁` to `r`.
Thus, any ordering of the input hypotheses corresponds to a series of discrimination trees in the iterated discrimination tree, the last of which contains the rule.
  
To retrieve rules applicable in the context `h₁ : T₁, ..., hₘ : Tₘ`, we iterate through the `Tᵢ`.
For each `Tᵢ`, we perform a lookup in the current collection of iterated discrimination trees (initially, the root discrimination tree).
This lookup yields (a) an array of rules which are already applicable; (b) additional discrimination trees, containing rules that may become applicable if more hypotheses match.
The latter are added to the collection of discrimination trees.

This scheme scales very poorly with long chains of hypotheses: for `n` hypotheses, we get `n!` leaves in the discrimination trees.
We may pragmatically limit the number of indexed hypotheses to, say, 3, preferring to index later hypotheses since they tend to be more specific.

#### Ordered Scheme

The core issue with the naive scheme is that we have to index every permutation of the indexed hypotheses.
We can avoid this by fixing a term order.
We then index only one permutation of the indexed hypotheses, determined by the order, and when we look up matching hypotheses for a context, we go through the context in the same order.
We call this indexing data structure an *ordered iterated discrimination tree*.

However, suppose that the input hypotheses `h₁ : T₁, ..., hₙ : Tₙ` match the context hypotheses `k₁ : U₁, ..., kₙ : Uₙ`.
This doesn't mean that `Tᵢ = Uᵢ` but merely that `Uᵢ` is an *instance* of `Tᵢ`, i.e. `Uᵢ = Tᵢ[σ]` for some substitution `σ`.
(I'm not sure whether `σ` is a substitution of `fvar`s, `mvar`s or both.)
Thus, we need an order that is *stable under substitution*, in the sense that `Tᵢ < Tⱼ` implies `Tᵢ[σ] < Tⱼ[σ]` (i.e., `Uᵢ < Uⱼ`) for any substitution `σ`.
For instance, we must ensure
```
(?n = ?m) < (?n + ?m = ?k)    ⇒    (0 = ?m) < (?n + ?m = 4)
```

The previous condition means that the order can't be a strict total order.
Proof: assume that the order is total.
This means the terms `T₁ := P ?x` and `T₂ := ?y` have to be ordered somehow; wlog assume `T₁ < T₂`.
Take `σ := {?x ↦ a, ?y ↦ a}`.
Then `T₁[σ] = T₂[σ]`, but by assumption we should have `T₁[σ] < T₂[σ]`.

When looking up hypotheses, we can deal with this non-totality by considering
permutations of equivalent hyps.
E.g. suppose we have
```
T₁ < T₂ ≈ T₃ ≈ T₄ < T₅
```
Then we need to query for
```
T₁, T₂, T₃, T₄, T₅
T₁, T₃, T₂, T₄, T₅
...
```

This is hopefully fine since the typical context won't contain many equivalent hyps.

## Incrementality Problem

### Problem

When we apply forward rules in a loop, we work in successively expanding contexts `Γ₁, Γ₂, Γ₃, ...` where `Γ₂ = Γ₁, Φ₁`, `Γ₃ = Γ₂, Φ₂`, etc.
The new hypotheses `Φᵢ` are the output hypotheses generated by the applied forward rules.
To determine which rules are applicable in `Γᵢ`, we could just use the indexing procedure.
However, there are two problems with this:

1. It's inefficient — we'd rather not do a full lookup every time.
2. We're only interested in rules that actually use the new hypotheses `Φᵢ`, since rules which apply to `Γᵢ` have already been run.
   
We also have a similar problem with goal modifications between forward phases.
Often, a backward rule applied between two forward phases will perform only small modifications of the context, in particular adding a few hypotheses.
Incrementality would also help here.
   
### Solution 1: Partially Ordered Iterated Discrimination Trees

We first observe that we can simplify the problem by considering the new hypotheses one by one.
Thus, we work in contexts `Γ₁`, `Γ₂ := Γ₁, h₁ : T₁`, `Γ₃ := Γ₂, h₂ : T₂`, etc., where `Φ₁ = h₁ : T₁, h₂ : T₂, ...`.
Each time we generate new output hypotheses, we add them to a queue.

Now, suppose we operate in context `Γ, h : T` where `h` is the new hypothesis.
We want to find rules `r : Φ → Ψ` such that `Φ ⊆ Γ, h : T` but `Φ ⊈ Γ`.

To query such rules efficiently, we modify the ordered iterated discrimination tree index defined above as follows: for a rule `r : Φ → Ψ` with `Φ = h₁ : T₁, ..., hₙ : Tₙ`, we create an iterated discrimination tree which, at the root, maps each `hᵢ` to an ordered (!) iterated discrimination tree for `h₁, ..., hᵢ₋₁, hᵢ₊₁, ..., hₙ`.
Thus, the new index acts like the naive scheme at the root, and like the ordered scheme everywhere else.

When querying the index, we can now look up `h` at the root.
If it matches, we match the returned ordered iterated discrimination tree against `Γ` as usual.

### Solution 2: Accumulating Partial Matches

We again consider the new hypotheses one by one, but for this solution we use completely different data structures.
The guiding principle is that we want to reuse work that's already been done, so we want to look at each new hypothesis exactly once.

#### Data Structures

In the following, we identify the input hypotheses of a rule `r : (h₁ : T₁) ... (hₙ : Tₙ) → Ψ` with their indices `1, ..., n`.

A *match* `m` for the rule `r` is a partial map from input hypothesis indices `1, ..., n` into hypotheses in the current context `Γ`.
It indicates that hypotheses `m(k₁), ..., m(kₗ)` in `Γ` can possibly be used to discharge the input hypotheses `k₁, ..., kₗ` of `r`.

A match `m` for `r` is *consistent* if the substitutions which arise from unifying each input hypothesis `hᵢ : Tᵢ ∈ dom(m)` with `m(i)` are consistent (i.e. they agree on variables shared between them).
For example, for the rule `r : n ≥ 0 → n ≤ 0 → n = 0`, the match `1 ↦ (h₁ : x ≥ 0), 2 ↦ (h₂ : y ≤ 0)` (with `x ≠ y`) is not consistent since unifying `?n ≥ 0` with `x ≥ 0` yields the substitution `?n ↦ x` while `?n ≤ 0` and `y ≤ 0` yield the substitution `?n ↦ y`.

A match `m` for `r : Φ → Ψ` is *complete* if it covers all of `r`'s input hypotheses, i.e. `dom(m) = Φ`.

We maintain two maps:

- `M₁` maps input hypothesis types `T` to pairs `(r, i)`, where `r : Φ → Ψ` is a rule and the `i`-th input hypothesis in `Φ` has type `T`.
  This is a discrimination tree, so the mapping is approximate: if `M₁(T) = (r, i)`, then the `i`-th input hypothesis of `r` *may* unify with `T`.
  The discrimination tree is pre-computed and forms the rule index.
- `M₂` maps rules `r` to matches `m` of `r`.
  This map is maintained throughout the forward phase (and hopefully between forward phases as well).
  We maintain the invariant that `M₂` contains a superset of the valid, incomplete matches for all rules and the current context `Γ`.

#### Algorithm

Let `Γ` be the current context and let `h : T` be the new hypothesis.
We proceed as follows:

```text
For each rule r and input hypothesis index i in M₁(T):
  For each match m in M₂(r):
    If m(i) is not defined:
      Add to M₂(r) the match m ∪ { i ↦ h }.
  Add to M₂(r) the match { i ↦ h }.

For all added matches m that are complete:
  Remove m from M₂(r).
  If m is valid:
    Let Ψ be the result of applying r to the hypotheses in m.
    Add the non-redundant hypotheses in Ψ to the context queue.
```

#### Better Representation of Sets of Matches

The above representation of sets of matches (as, well, sets of matches) is quite inefficient.
We want a data structure that represents a set of matches for a specific rule `r` with input hypotheses `Ψ = h₁ : T₁, ..., hₙ : Tₙ`.
When a new context hypothesis `h : T` with `T =[σ] Tᵢ` for some `i` and `σ` arrives, the data structure should allow us to quickly determine all complete and consistent matches for `r` in the current context that involve `h`.
(I write `x =[σ] y` if `x` unifies with `y` with most general unifier `σ`.)

##### Attempt 1: Candidate Map

TODO cache substitutions

We use a finite map `F` from hypothesis indices `1, ..., n` to lists of candidate hypotheses `C₁ = c₁₁ : U₁₁, ..., c₁ₘ₁ : U₁ₘ₁` etc.
When a new hypothesis `h : T` arrives, we proceed as follows:

```
For each i such that, according to the index, T may unify with Tᵢ:
  Add h to the candidate list Cᵢ.
  If F(j) is nonempty for all j:
    Let σ ≔ ∅ be the empty substitution.
    For all k ∈ 1, ..., n:
      For all c : U ∈ Cₖ:
        If Tₖ[σ] =[σ'] U[σ]:
          σ ≔ σ'
        Else:
          Continue.
      If the previous loop was unsuccessful for all c:
        Continue.
      Else if k = n:
        Return the selected candidates as a complete and consistent match.
```

This algorithm has the major disadvantage that it unifies the same hypotheses over and over again.

##### Attempt 2: Candidate Graph

We first pre-compute an undirected, simple *variable graph* `P` for the rule `r`:

- Nodes are input hypothesis indices `i ∈ {1, ..., n}`.
- Edges are labelled with nonempty sets of variables.
  An edge `i --{x₁, ..., xₘ}-- j` indicates that `Tᵢ` and `Tⱼ` share exactly the variables `x₁, ..., xₘ`.

During the forward reasoning phase, we maintain an undirected, simple *candidate graph* `G` for `r`:

- Nodes are tuples `(i, h : T, σ)` where `i` is an input hypothesis index and `h : T` is a hypothesis in the context such that `T =[σ] Tᵢ`.
- Edges are unlabelled.
  An edge between `(i, h : T, σ)` and `(i', h' : T', σ')` indicates that there is an edge `i --V-- i'` in the variable graph and `σ` and `σ'` are *consistent* on the variables in `V`.
  This means that for each variable `?x ∈ V`, `σ(?x) = σ'(?x)`.
  Note that in our setup, the variable assignments `σ(?x)` and `σ'(?x)` don't contain metavariables (or rather, we don't want to assign any metavariables in there).
  So unification of `σ(?x)` and `σ'(?x)` reduces to equality (possibly up to computation).

A *complete and consistent match* in `G` is a subset `(1, h₁ : T₁, σ₁), ..., (n, hₙ : Tₙ, σₙ)` such that for each edge `i --V-- i'` in the variable graph, `G` contains an edge between the nodes with indices `i` and `i'`.

Now, when a new hypothesis `h : T` arrives, we proceed as follows:

```
For each i such that, according to the index, T may unify with Tᵢ:
  If T =[σ] Tᵢ:
    Add a new node (i, h : T, σ).
    For each i' such that there is an edge with label V between `i` and `i'`:
      For each node (i', h' : T', σ'):
        If σ and σ' are consistent on V:
          Add an edge between the two nodes in the candidate graph.

    For each complete and consistent match in G that contains the new node (i', h' : T', σ'):
      Extract the corresponding match, which is also complete and consistent.
```

We still need a way to efficiently find the complete and consistent matches in `G` that involve a particular node.
To that end, we add to each node in the candidate graph a set of hypothesis indices `W`.
This set indicates which edges the node is still waiting for.
When we add an edge between `(i, h : T, σ, W)` and `(i', h' : T', σ', W')`, we then remove `i'` from `W` and `i` from `W'`.
To extract a complete and consistent match involving `(i, h : T, σ, W)`, we now just have to follow edges from `i` in the variable graph, and this traversal fails as soon as we encounter a node whose waiting set `W'` is nonempty.

It's still a bit unclear to me, though, how to efficiently do this traversal.
For example, take a lemma with hypotheses
```
1 : P ?x   2 : Q ?x ?y   3 : R ?x ?y   4 : S ?y
```
The pattern graph is
```
 ?x ----2---- ?y
   /    |?x  \
  1     |?y   4
   \    |    /
 ?x ----3---- ?y
```
So we must reach the same node for `4` from `1` via `2` and `3`.
In general, finding a subgraph of the candidate graph `G` isomorphic to the variable graph `P` is an instance of the subgraph isomorphism problem, which is NP-complete.
We have the additional constraint that we know one node that must be included in the subgraph, but this doesn't change the complexity.

Proof: by reduction.
To transform a regular subgraph iso problem into a constrained subgraph iso problem, add a node and connect it to all other nodes in the graph.
Finding a subgraph iso involving the new node in the new graph is then equivalent to finding a subgraph iso in the old graph.

## Pattern-Based Forward Rules

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

TODO integration into candidate graph algorithm.

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
