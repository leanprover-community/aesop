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

##### Attempt 3: Candidate Tree

As usual, let `r : h₁ : T₁ → ... → hₙ : Tₙ → Ψ` be a forward rule.
We want to represent a set of partial matches for `r`.

###### Precomputation: Hypothesis Tree

When we index `r`, we arrange the `Tᵢ` into a *hypothesis tree* with two alternating types of nodes:

- *Index nodes* store
  - the index of an input hypothesis;
  - a hash map of the node's children, which are variable nodes.
- *Variable nodes* store
  - a list of variables;
  - an ordered list of the node's children, which are index nodes.

For an input hypothesis `hᵢ : Tᵢ`, the corresponding index node in the tree has index `i`.
The children of an index node are variable nodes containing subsets of the variables which occur in the input hypothesis referenced by the index node.
The children of a variable node are index nodes whose input hypotheses share exactly the variables of the variable node with the variable node's parent.

Example: the tree

```
         1
        / \
 [?x, ?y] [?x, ?z]
   |        /  \
   2       3    4
   |
  [ ]
   |
   5
```

indicates that `T₁` and `T₂` have exactly the variables `?x` and `?y` in common; `T₁` and `T₃` as well as `T₁` and `T₄` have exactly `?x` and `?z` in common; and `T₂` and `T₅` have no variables in common.

A hypothesis tree `t` is *valid for `r`* if it has the following properties:

- For each input hypothesis `hᵢ : Tᵢ`, `t` contains exactly one index node with index `i`.
- The childrens' children of an index node for `Tᵢ` are exactly those `j ≠ i` such that `Tᵢ` and `Tⱼ` share at least one variable.
  (TODO this condition is hot garbage. But what's the right one?)

This means that the hypothesis tree is a sort of covering for the hypotheses' dependency graph.
We assume henceforth that each rule `r` is associated with a valid hypothesis tree.

To limit the tree's size, it is probably preferable to put input hypotheses with many variables close to the root.

###### Running Example

Let `r : Φ → Ψ` have input hypotheses

```
Φ = h₁ : T₁[?x], h₂ : T₂[?x], h₃ : T₃[?x,?y], h₄ : T₄[?y,?z], h₅ : T₅[?y], h₆ : T₆[?w]
```

We select `h₃ : T₃[?x, ?y]` as the root since it has the most variable connections to other hypotheses.
This forces us to add children for `h₁ : T₁[?x]`, `h₂ : T₂[?x]`, `h₄ : T₄[?y, ?z]`, `h₅ : T₅[?y]` with corresponding variable nodes.
The leftover hypothesis `h₆ : T₆[?w]` can be added anywhere; we choose the root.
This results in the following hypothesis tree:

```
           --- 3 ---
          /     |   \
        [?x]   [?y] [ ]
        / \    / \   |
       1   2  4   5  6
```

###### Runtime: Candidate Tree

At runtime, we store the partial matches in a *candidate tree* with three alternating types of nodes:

- *Index nodes* store
  - the index of an input hypothesis;
  - a hash map of the node's children, which are variable nodes.
- *Variable nodes* store
  - an `n`-tuple of variables (for some `m`);
  - an iterated discrimination tree mapping `m`-tuples of terms to the node's children, which are instantiation nodes.
- *Instantiation nodes* store
  - a nonempty list of hypotheses
  - an ordered list of the node's children, which are index nodes.

The index nodes and variable nodes mirror the precomputed hypothesis tree.
An instantiation node for terms `(a₁, ..., aₘ)` with hypotheses `hᵢ₁, hᵢ₂, ...`, parent variables `(?x₁, ..., ?xₘ)` and parent's parent index `k` indicates that the types of the hypotheses `hᵢⱼ` unify with `Tₖ` with a substitution that maps `?x₁` to `a₁`, `?x₂` to `?a₂`, etc.

Example: the tree

```
                 1
                / \
        [?x, ?y]   [?x, ?z]
        /     \
(a, b) /       \ (a, c)
      /         \
    [h₁, h₂]   [h₃]
       |
       2
       |
      [ ]
       |
      [h₄]
```

indicates that

- `h₁ : T₁[?x := a, ?y := b]`
- `h₂ : T₁[?x := a, ?y := b]`
- `h₃ : T₁[?x := a, ?y := c]`
- `h₄ : T₂`

Note that `T₁` and `T₂` may contain additional metavariables.
E.g. `T₁` may contain a metavariable `?z` which doesn't occur in `T₂` (otherwise it would show up in the left variable node of `1`.)
So when we write `h₁ : T₁[?x := a, ?y := b]`, we mean that `T₁[?x := a, ?y := b]` unifies with the type of `h₁`.

A candidate tree `t` *matches* a hypothesis tree `u` if `t` becomes a subtree of `u` when we remove instantiation nodes.
More precisely, if we replace each subtree of the form
```
  [?x₁, ...]
    /      \
   /   ...  \
  /          \
[h₁₁, ...]    [hₖ₁, ...]
  |     |       |     |
  | ... |       | ... |
  |     |       |     |
  i₁₁  ...      iₖ₁  ...
```
with one of the trees
```
[?x₁, ...]  ...   [hₖ₁, ...]
  |     |           |     |
  | ... |           | ... |
  |     |           |     |
  i₁₁  ...          iₖ₁  ...
```
then the resulting overall tree must be a subtree of `u`, regardless of which replacement trees we chose.

We maintain the invariant that our candidate trees always match the hypothesis tree of `r`.

###### Insertion

Let `h : T` be a new hypothesis such that `T =[σ] Tᵢ` for some `i`.
To insert `h` into the candidate tree, we proceed as follows.

Let `(I₁, V₁, ..., Iₘ)` with `Iₘ = i` be the path to `i` in the hypothesis tree.
The `Iⱼ` are indices (or index nodes); the `Vⱼ` are sets of variables (or variable nodes).
This path can be precomputed for each `i`.

We follow the same path in the candidate tree.
When we encounter a variable node for `?x₁, ..., ?xₖ`, we look up `(σ(?x₁), ..., σ(?xₖ))` in the variable node's discrimination tree.
We then recurse into the instantiation node returned by this lookup and continue to follow `p`.
If the lookup is unsuccessful, we create a new instantiation node, insert it into the discrimination tree and continue to follow `p`.

Once we've reached the end of `p`, let `V₁, ..., Vₗ` be the sets of hypotheses that are children of `i` in the hypothesis tree.
For each such set `Vⱼ = {?x₁, ..., ?xₒ}`, add the corresponding variable node to `i`.
In the variable node's discrimination tree, add the mapping `(σ(?x₁), ..., σ(?xₒ)) ↦ [h]` (or add `h` to this instantiation node if it already exists).

We have so far ignored the complication that some of the intermediate index nodes on the path `p` may not exist because we haven't found suitable hypotheses yet.
In this case, we put `h` into a waiting list.
When we later add one of the intermediate index nodes, we try to insert `h` again.
This can be made more efficient, for example by having waiting lists at each node in the graph.
Then we don't have to walk parts of the path over and over again.

###### Running Example

Suppose the following hypotheses arrive one by one:

- `h₁ : T₁[?x ↦ a]`
  Path: `(3, [?x], 1)`
  The intermediate node `3` is not present, so `h₁` goes on the waiting list.
- `h₂ : T₃[?x ↦ a, ?y ↦ b]`
  Path: `(3)`
  ```
          3
        /   \
      [?x]  [?y]
    a /      | b
    [h₂]    [h₂]
    /
   1
   |
  [ ]
   |
  [h₁]
  ```
  It's now possible to insert `h₁`, so we remove it from the waiting list.
- `h₃ : T₃[?x ↦ a, ?y ↦ c]`
  Path: `(3)`
  ```
          3
        /   \
      [?x]  [?y]--
    a /      | b  \ c
    [h₂,h₃] [h₂]  [h₃]
    /
   1
   |
  [ ]
   |
  [h₁]
  ```
- `h₄ : T₂[?x ↦ a]`
  Path: `(3, [?x], 2)`
  ```
          3
        /   \
      [?x]  [?y]--
    a /      | b  \ c
    [h₂,h₃] [h₂]  [h₃]
    /  \
   1    2
   |    |
  [ ]  [ ]
   |    |
  [h₁] [h₄]
  ```
- `h₅ : T₄[?y ↦ b, ?z ↦ c]`
  Path: `(3, [?y], 4)`
  ```
          3
        /   \
      [?x]  [?y]--
    a /      | b  \ c
    [h₂,h₃] [h₂]  [h₃]
    /  \     |
   1    2    4
   |    |    |
  [ ]  [ ]  [ ]
   |    |    |
  [h₁] [h₄] [h₅]
  ```
- `h₆ : T₅[?y ↦ b]`
  Path: `(3, [?y], 5)`
  ```
          3
        /   \
      [?x]  [?y]--
    a /      | b  \ c
    [h₂,h₃] [h₂]  [h₃]
    /  \     |  \
   1    2    4   5
   |    |    |   |
  [ ]  [ ]  [ ] [ ]
   |    |    |   |
  [h₁] [h₄] [h₅] [h₆]
  ```
- `h₇ : T₆[?w ↦ d]`
  Path: `(3, [], 6)`
  ```
          3 ----------------
        /   \              |
      [?x]  [?y]--        [ ]
    a /      | b  \ c      |
    [h₂,h₃] [h₂]  [h₃]     6
    /  \     |  \          |
   1    2    4   5        [ ]
   |    |    |   |         |
  [ ]  [ ]  [ ] [ ]       [h₇]
   |    |    |   |
  [h₁] [h₄] [h₅] [h₆]
  ```

###### Extraction

A complete match is a subtree of the candidate tree which covers all input hypotheses `Tᵢ`, subject to the following coherence condition:
If an index node for `Tᵢ` has children `V₁, ..., Vₘ`, then there must be a hypothesis `h` such that for each instantiation node that is a child of `Vⱼ` and is present in the complete match subtree, `h` is contained in the instantiation node.
In other words: For each index node, we must choose *one* hypothesis to include in the match.

We can speed up the search for a complete match by tracking which subtrees are already complete.
When we insert a hypothesis, we can then determine, bottom-up, which subtrees have become complete.
As soon as the root becomes complete, we have a complete match.
However, we need to take care to report each complete match only once.

##### Attempt 4: Hypothesis Maps

(Chronologically, this is attempt 3.)

###### Precomputation

Let `r : Φ → Ψ` with `Φ = h₁ : T₁, ..., hₙ : Tₙ` be the rule for which we collect partial matches.

For each subset `V` of the variables in `Φ`, we define the *hypothesis set*
```
π_V = { Tᵢ | vars(Tᵢ) ⊆ V }
```
where `vars(Tᵢ)` is the set of variables in `Tᵢ`.

Note that for `|V| = n + 1`, we have
```
π_V = (⋃_{|V'| = n} π_V') ∪ { Tᵢ | vars(Tᵢ) = V }
```
This gives us an inductive characterisation of the sets `π_V`.

###### Running Example

Let `r : Φ → Ψ` have input hypotheses

```
Φ = h₁ : T₁[?x], h₂ : T₂[?x], h₃ : T₃[?x,?y], h₄ : T₄[?y,?z], h₅ : T₅[?y], h₆ : T₆[?w]
```

We precompute the hypothesis sets
```
π_{?x} = { T₁[?x], T₂[?x] }
π_{?y} = { T₅[?y] }
π_{?z} = ∅
π_{?w} = { T₆[?w] }

π_{?x,?y} = π_{?x} ∪ π_{?y} ∪ { T₃[?x,?y] }
π_{?x,?z} = π_{?x} ∪ π_{?z} ∪ ∅
π_{?x,?w} = π_{?x} ∪ π_{?w} ∪ ∅
π_{?y,?z} = π_{?y} ∪ π_{?z} ∪ { T₄[?y,?z] }
π_{?y,?w} = π_{?y} ∪ π_{?w} ∪ ∅
π_{?z,?w} = π_{?z} ∪ π_{?w} ∪ ∅

π_{?x,?y,?z} = π_{?x,?y} ∪ π_{?y,?z} ∪ π_{?x,?z} ∪ ∅
π_{?x,?y,?w} = π_{?x,?y} ∪ π_{?y,?w} ∪ π_{?x,?w} ∪ ∅
π_{?x,?z,?w} = π_{?x,?z} ∪ π_{?z,?w} ∪ π_{?x,?w} ∪ ∅
π_{?y,?z,?w} = π_{?y,?z} ∪ π_{?z,?w} ∪ π_{?y,?w} ∪ ∅

π_{?x,?y,?z,?w} = π_{?x,?y,?z} ∪ {?x,?y,?w} ∪ π_{?x,?z,?w} ∪ π_{?y,?z,?w}
```

In this example, many combinations of variables don't occur, so as an optimisation, we restrict ourselves to the *relevant hypothesis sets* (TODO what are these in general?):
```
π_{?x} = { T₁[?x], T₂[?x] }
π_{?y} = { T₅[?y] }
π_{?z} = ∅
π_{?w} = { T₆[?w] }

π_{?x,?y} = π_{?x} ∪ π_{?y} ∪ { T₃[?x,?y] }
π_{?y,?z} = π_{?y} ∪ π_{?z} ∪ { T₄[?y,?z] }

π_{?x,?y,?z,?w} = π_{?x,?y} ∪ π_{?y,?z} ∪ π_{?w}
```
Note that we've also changed the definition of the last hypothesis set.
It now refers to 2- and 1-variable sets instead of 3-variable sets.

We say that `T₃` is *fresh* in `π_{?x,?y}` since it doesn't appear in `π_{?x}` or `π_{?y}`.

###### Runtime

For each relevant hypothesis set `π_V`, we maintain a *hypothesis map* `μ_V` from `|V|`-tuples of terms to `|μ_V|`-tuples of hypotheses.
Each hypothesis in a tuple can also be undefined.
Let `V = {?x₁, ..., ?xₘ}`, `μ_V = {T₁, ..., Tₖ}` and `σ = {?x₁ ↦ a₁, ..., ?xₘ ↦ aₘ}`.
If `μ_V(a₁, ..., aₘ) = (h₁, ..., hₖ)`, this means that `h₁ : T₁[σ]`, ..., `hₖ : Tₖ[σ]`.
Thus, `(h₁, ..., hₖ)` is a match for the input hypotheses which depend only on `V`.
If some of the `hᵢ` are missing from the tuple (we write `(..., ?, ...)`), the match is partial.

To implement `μ_V`, we take advantage of the fact that the hypothesis map `π_V` can be partly expressed in terms of hypothesis sets `π_V'` with `|V'| < |V|`.
Let `π_V = π_V₁ ∪ ... ∪ π_Vₘ ∪ { T₁, ..., Tₒ }`.
We implement `μ_V` as a discrimination tree `t` which maps `|V|`-tuples of terms to tuples of hypotheses `(h₁ : T₁, ..., hₒ : Tₒ)`.
We then define `μ_V(A) = μ_V₁(A) ⊕ ... ⊕ μ_Vₘ(A) ⊕ t(A)` where `⊕` is concatenation of tuples (possibly with some reordering) and `A` is a tuple of terms.

###### Insertion

Let `h : T` be a new hypothesis such that `T =[σ] Tᵢ` for some `i`.

To insert `h` into the hypothesis maps, consider the relevant hypothesis sets `π_V`.
For each such `π_V = ⋃_j π_Vⱼ ∪ V`:

- If `Tᵢ ∉ V`, leave `μ_V` unchanged.
- Otherwise, let `A = (σ(?x₁), ..., σ(?xₘ))`.
  The `?xⱼ` are the variables in `V`.
  (We assume here that `σ(?xⱼ)` is defined for all `?xⱼ`, but I think this is guaranteed by the construction of the hypothesis sets.)
  Now update the mapping `A ↦ (h₁, ..., hᵢ₋₁, ?, hᵢ₊₁, ..., hₖ)` in `μ_V` by replacing the `?` with `h`.
  If the mapping does not exist yet, create it, setting `hⱼ ≔ ?` for all `j ≠ i`.

###### Running Example

TODO

###### Extraction

When we insert `h : T` into `μ_V` with instantiating terms `A`, we must check whether this leads to a complete match.
To that end, we check:

- Is the tuple into which `h` was inserted now fully defined (i.e., doesn't contain any `?`s)?
  This can be optimised by keeping track of the number of `?`s in each tuple.
- For all `π_V'` on which `π_V` depends, is `μ_V'(A)` fully defined?
  The answers can be partially cached.
- For all `π_V''` which depend on `π_V`, is `μ_V''(A')` fully defined for any
  tuple `A'` of which `A` is a subsequence/subset?
  TODO this I don't know how to do efficiently.

###### Running Example

TODO

##### Attempt 5: Variable Maps

Let `r : Φ → Ψ` with `Φ = h₁ : T₁, ..., hₙ : Tₙ` be the rule for which we collect partial matches.
We go back to a representation of partial matches as simply pairs `(σ, M = {1 ↦ H₁, ..., n ↦ Hₙ})`, where `σ` is a substitution and `H₁ : U₁, ..., Hₙ : Uₙ` are hypotheses such that `Uᵢ[σ] = Tᵢ`.
If a match is incomplete, it lacks mappings for some of the indices `1, ..., n`.
We require that the substitution `σ` covers exactly the variables occurring in the `Tᵢ` for which `M` contains a mapping, so `dom(σ) = { vars(Tᵢ) | M(i) is defined }`.
In other words, `σ` does not unnecessarily constrain variables other than those 'forced' by the `Hᵢ`.
This means that `σ` is uniquely determined by the `Hᵢ`.

It suffices to store one hypothesis per input hypothesis index, rather than a set of hypotheses.
To see why, suppose we have `H : U` with `U ≡[τ] Tᵢ` and a partial match `(σ, M)` with `M(i) = V`.
Since `σ` covers all variables in `Tᵢ`, we must have `τ = σ|vars(Tᵢ)` (the restriction of `σ` to `vars(Tᵢ)`).
Thus, `U = Tᵢ[τ] = Tᵢ[σ]`, so `M(i)` and `H` have the same type, making them duplicates.
We can therefore ignore `H`.

###### Data Structure

We now construct an efficient data structure representing a set of partial matches.

The data structure consists of the following:

- A bijective map `N` from natural numbers to partial matches.
  The natural numbers are arbitrary and are used as identifiers for the partial matches.
- For each variable `?x` in `Φ`, a map `μₓ` which maps terms to sets of natural numbers.
  Invariant: the set `μₓ(t)` contains exactly the identifiers of the partial matches `(σ, _)` in `N` with `σ(?x) = t`.
- For each variable `?x` in `Φ`, a set `πₓ` of natural numbers.
  Invariant: `πₓ` contains exactly the identifiers of the partial matches `(σ, _)` in `N` with `?x ∉ dom(σ)`.
  
###### Insertion

The data structure supports a single operation, `insert(H : U, i, τ)`, which extends the current partial matches with `H : U`, where `U ≡[τ] Tᵢ`, and returns a set of complete matches.
The returned complete matches are those previously incomplete matches that are completed by adding `H`.
(This set is often empty.)

The `insert(H : U, i, τ)` operation works as follows:

1. Retrieve the set `Σ` of (indices of) partial matches compatible with `τ`.
   For each variable `?xᵢ` in `vars(Φ)`:
   - If `?xᵢ ∈ dom(τ)`, let `Σₓᵢ = μₓᵢ(τ(xᵢ)) ∪ πₓᵢ`.
   - Otherwise, TODO
   This makes `Σₓᵢ` the set of partial matches whose substitutions are compatible with `τ` along `?xᵢ`.
   We then have `Σ = ⋂ᵢ Σₓᵢ`.
2. For each partial match `(σ, M)` in `Σ`:
   - If `M(i)` is already defined: skip the following steps.
   - If `M[i ↦ H]` is complete: add `M[i ↦ H]` to the output and skip the following steps.
   - If `dom(τ) ⊆ dom(σ)`: replace `(σ, M)` with `(σ, M[i ↦ H])`, keeping the same identifier.
   - If `dom(τ) ⊈ dom(σ)`:
     - Let `ν = σ ∪ τ`. This is well-defined since `σ` and `τ` agree on all shared variables.
     - Insert the partial match `(ν, M[i ↦ H])` into `N` with fresh identifier `k`.
     - For each `?x` in `dom(ν)`, insert the mapping `ν(?x) ↦ k` into `μₓ`.
     - For each `?x` in `vars(Φ) ∖ dom(ν)`, insert `k` into `πₓ`.

##### Attempt 6: Variable Map Tree

Same setup as in the previous attempt.

###### Data Structure

For each variable `?x ∈ vars(Φ)`, let `h₁ : T₁, ..., hₖ : Tₖ` be those input hypotheses with `?x ∈ vars(Tᵢ)`.
If `k > 1`, we maintain a map (discrimination tree or hash map) `μₓ` from terms `t` to tuples `(H₁, ..., Hₖ)` (called *connections*).
Each component `Hᵢ` of such a connection is a list of hypotheses `h : T` such that `T ≡ Tᵢ[?x ↦ t]`.
A connection is *full* if every component `Hᵢ` is nonempty.

Additionally, we superimpose a tree onto this data structure.
Let `<` be an arbitrary total order on the variables `vars(Φ)`.
We maintain the invariant that whenever a hypothesis `h` appears in `μᵤ` and `μᵥ` with `?u < ?v`, there is an edge from the occurrence of `h` in `μᵤ` to the connection in which `h` occurs in `μᵥ`.

###### Insertion

As above, we define an operation `insert(H : U, i, τ)` where `U ≡[τ] Tᵢ`.

Let `dom(τ) = ?x₁, ..., ?xₖ` with `?x₁ < ... < ?xₖ`.
For each `?xᵢ` such that `μ_xᵢ` exists, let `μ_xᵢ(τ(xᵢ)) = C` be the connection associated to the value of `xᵢ` in `τ` (or an empty connection if `τ(xᵢ) ∉ dom(μ_xᵢ)`).
Now:

- Update `C` by adding `H` to the tuple component corresponding to `i`.
- Add an edge from the previously added entry in `μ_xᵢ₋₁` to `C`.

###### Complete Match Detection

Let `C` be a connection in one of the `μₓ`.
`C` is *complete* if

- `C` is full and
- for every hypothesis list `Hᵢ` in `C`, there is a hypothesis `h ∈ Hᵢ` such that all edges from `h` point to complete connections.

If `?x` is minimal in `vars(Φ)` and a connection in `μₓ` is complete, then we have a complete match.

To incrementalise this notion of completeness, we add the following components to the data structure:

- One backward edge for each existing forward edge.
- A boolean for each connection, indicating whether the connection is complete.
- A boolean for each hypothesis list of each connection, indicating whether there is a hypothesis `h` in the list such that all outgoing edges from `h` point to complete connections.
  If so, we say that the hypothesis list is *complete*.
- A natural number `ic(h)` for each occurrence of a hypothesis `h`, indicating the number of outgoing edges from `h` that point to incomplete connections.

Now, when inserting a hypothesis `h` into hypothesis list `H` of connection `C`, we proceed as follows:

```
Update ic(h).
If H is not already complete:
  If ic(h) = 0:
    Mark H as complete.
    If all other hypothesis lists of C are complete:
      Mark C as complete.
      If C belongs to μ_x₁ (with x₁ minimal):
        Extract the complete match from C.
      For each hypothesis h' reachable via a backward edge from C:
        Decrement ic(h').
        If ic(h') = 0:
          recurse.
```

###### Problem

The above notion of completeness is unsound because it can pick connections `C`, `D` such that `C` selects hypothesis `h₁` and `D` selects hypothesis `h₂` (with `h₁ ≠ h₂`) for a given input hypothesis index.
We then can't extract a complete match.
To fix this, we can adjust the complete match detection algorithm to remember which hypothesis was previously selected for any given index.
But this defeats much of the caching we do during complete match detection; in fact, it requires backtracking.

##### Attempt 7: Travelling Partial Matches

Let `h₁ : T₁, ..., hₙ : Tₙ` be the input hypotheses.
The central idea of this technique is to tightly restrict the 'progression' of a partial match towards completeness:
we first add a hypothesis matching `T₁`, then add a compatible hypothesis for `T₂`, etc.
If this process reaches `Tₙ`, the match is complete.

Let partial matches be defined as tuples `(σ, M)` where `σ` is a substitution and `M` is a partial map from input hypothesis indices to hypotheses.
As above, we require that the hypotheses in `cod(M)` have compatible substitutions and that `σ` is exactly the union of these substitutions (so this representation is redundant).
Our algorithm ensures that `M` is downward closed, so if `M(i)` is defined, then `M(j)` is also defined for every `j` with `1 ≤ j ≤ i`.
This means the partial matches progress through `T₁`, `T₂`, etc. in order.
The *level* `lvl(σ, M)` of a partial match `(σ, M)` is the maximal `i` such that `M(i)` is defined.
It indicates how far along a partial match is on its way to `Tₙ`.

###### Data Structure Interface

We maintain *index maps* `μₘ` and `μₕ`.
The map `μₘ` maps tuples `(τ, i)`, where `τ` is a substitution and `i` is a natural number, to partial matches which are compatible with `τ` and have level `i`.
The map `μₕ` maps tuples `(τ, i)` as above to tuples `(H : T, ρ)`, where `H` is a hypothesis with `T ≡[ρ] Tᵢ` and `ρ` is compatible with `τ`.

###### Insertion

```
Insert(H : U, i, τ):
  Insert into μₕ: μₕ(τ, i) ≔ H.
  If i = 1:
    AddPartialMatch(τ, {i ↦ H}).
  Else:
    For each partial match (ρ, M) in μₘ(τ, i - 1):
      AddPartialMatch(τ ∪ ρ, M ∪ {i ↦ H}).

AddPartialMatch(τ, M):
  Let i ≔ lvl(M).
  Insert into μₘ: μₘ(τ, i) ≔ (τ, M).
  If i = n:
    Return (τ, M) as a complete match.
  Else:
    For each (H, ρ) in μₕ(τ, i + 1):
      AddPartialMatch(τ ∪ ρ, M ∪ {i + 1 ↦ H}).
```

###### Data Structure Implementation

For this algorithm to be efficient, we must efficiently implement the maps `μₘ` and `μₕ`.
Note that `μₘ` and `μₕ` have the same domain, so we actually implement one map, `μ`, which maps tuples `(τ, i)` to lists of partial matches and lists of hypotheses.
Thus, the codomain of `μ` is the type of tuples `(Ms, Hs)` where `Ms` is a list of partial matches and `Hs` is a list of hypotheses.
We call such tuples *μ-values*.
Further, we can curry and implement a map `μ` which maps substitutions `τ` to maps from `i` to μ-values.

To implement this map, we use the following data structure.
For each variable `?x`, we create a discrimination tree `μₓ` which maps terms `t` to maps from indices `i` to μ-values.
We write `μₓ(t, i)ₕ` for the hypotheses at `μₓ(t)(i)`, and `μₓ(t, i)ₘ` for the partial matches.
We then maintain the invariant that `μₓ(t, i)ₕ` is the set of all hypotheses `H : Tᵢ[ρ]` with `ρ(x) = t`.
Similarly, `μₓ(t, i)ₘ` is the set of partial matches `(ρ, M)` with `lvl(M) = i` and `ρ(x) = t`.

We now define lookup functions for matches and hypotheses:

```
Lookup(τ, i, j):
  Let cv ≔ vars{T₁, ..., Tᵢ} ∩ vars(Tᵢ₊₁).
  For each variable xₖ in cv:
    Let vₖ ≔ μₓₖ(τ(xₖ), j)
  Return ⋂ₖ vₖ
  
LookupMatches(τ, i):
  Lookup(τ, i, i).1.

LookupHypotheses(τ, i):
  Lookup(τ, i, i + 1).2.
```

The intersection of μ-values is defined componentwise, so `(Ms, Hs) ∩ (Ms', Hs') = (Ms ∩ Ms', Hs ∩ Hs')`.

In the above insertion algorithm, we use these lookup functions in two ways:

1. Look up `μ(τ, i - 1)ₘ`, where `τ` is the substitution of a hypothesis matching type `Tᵢ`.
   This lookup should return all partial matches `(ρ, M)` with `lvl(M) = i - 1` and `ρ` compatible with `τ`.
   `LookupMatches(τ, i - 1)` implements this specification.
2. Look up `μ(τ, i + 1)ₕ`, where `τ` is the substitution of a partial match at level `i`.
   This lookup should return all hypotheses at level `i + 1` with a substitution `ρ` compatible with `τ`.
   `LookupHypotheses(τ, i)` implements this specification.

The function `Lookup(τ, i, j)` has two preconditions:

1. `τ(x)` is defined for every `x ∈ vars{T₁, ..., Tᵢ} ∩ vars(Tᵢ₊₁)`.
   This is the case in both of our use cases.
   When looking up matches for a hypothesis for `Tᵢ₊₁` with substitution `τ`, `τ` covers `Tᵢ₊₁`.
   When looking up hypotheses for a match at level `i` with substitution `τ`, `τ` covers `{T₁, ..., Tᵢ}`.
2. `vars{T₁, ..., Tᵢ} ∩ vars(Tᵢ₊₁)` is not empty.
   If this precondition is violated, the lookup function will always return the empty set, even though any partial match for `T₁, ..., Tᵢ` is compatible with any hypothesis for `Tᵢ₊₁` (as they don't share any variables).
   However, we can ensure that the set of common variables is never empty.
   If the input hypothesis types `T₁, ..., Tₙ` are all part of the same metavariable cluster, then they can be ordered in such a way that `Tᵢ₁` shares a variable with `Tᵢ₂`, `Tᵢ₁` or `Tᵢ₂` share a variable with `Tᵢ₃`, etc.
   If the input hypotheses form multiple metavariable clusters, we can use separate data structures for these (which should also be good for performance).

As an alternative to this whole data structure, we could use a standard substitution tree.
A substitution tree stores substitutions and supports queries for compatible substitutions.
However, it likely performs badly since insertion into a substitution tree is expensive, and we do a lot of insertions.

###### Optimisations

1. When we create new partial matches, we always do so by adding data to existing partial matches.
   As a result, much data is shared between partial matches.
   We should choose a data representation (e.g. linked lists) that allows us to exploit this sharing.
2. A partial match at level 1 is just a hypothesis.
   Storing these partial matches is therefore redundant when we're already storing the hypotheses.
   Similarly, we don't need to store partial matches at the maximal level `n`.
3. The intersection of sets of hypotheses/matches can be computed efficiently if we give each hypothesis and each partial match a unique identifier.
   In this case, the intersection comes down to an intersection of sets of natural numbers, which is very efficient.
4. Similarly, we can give a unique identifier to each instantiation of a variable.
   This should speed up lookups and insertions into the variable maps `μₓ`, which are quite frequent.
5. If a variable `x` occurs in only one hypothesis, we don't need to maintain a map `μₓ`.

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

(TODO integration into more advanced algorithms.)

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
