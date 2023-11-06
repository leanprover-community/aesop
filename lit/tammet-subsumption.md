# Tanel Tammet: Towards Efficient Subsumption

https://link.springer.com/chapter/10.1007/BFb0054276

## Overview

This paper discusses efficient techniques for checking whether clauses subsume each other.
The techniques were implemented in a resolution prover called Gandalf.

## Preliminaries

The paper uses the language of first-order logic, even though the Gandalf prover also supports type theory.

A *term* is either a variables or a function symbol applied to other terms.

An *atom* is `P(t₁, ..., tₙ)`, where `P` is a predicate symbol of arity `n` and the `tᵢ` are terms.

A *literal* is either `a` or `¬ a`, where `a` is an atom.

A *clause* is a set of literals.
We read the set as a disjunction: `{A₁, ..., Aₙ}` corresponds to the formula `A₁ ∨ ... ∨ Aₙ`.

A *unit clause* is a clause containing a single literal.

A term/literal/clause is *ground* if it doesn't contain variables.

A literal `A` *subsumes* a literal `B` if there is a substitution `σ` such that `A[σ] = B` (i.e., `A` is a generalisation of `B`).

A clause `C` *subsumes* a clause `D` if there is a substitution `σ` such that `C[σ] ⊆ D`.
This means that `C[σ]` implies `D`.
(If `C` and `D` are ground, then `C ⊆ D` iff `C` implies `D`.
If `C` and `D` are non-ground, then `C ⊆ D` still implies that `C` implies `D`.)

Gandalf checks for clause subsumption in two different contexts:

- *Forward subsumption*: is a newly derived clause already subsumed (implied) by existing clauses?
  If so, the newly derived clause is redundant and can be removed.
- *Backward subsumption*: which existing clauses are subsumed by a newly derived clause?
  These clauses can be removed.
  
## Relation to Aesop Forward Reasoning
  
Our problem in Aesop is not clause subsumption, but it's substantially similar.
We can view our input hypotheses as a set of (generally non-ground) formulas (not literals) `C`.
We can view our context as a set of 'ground' formulas `D`.
(The formulas in `D` are 'ground' because while they may contain variables, we don't want to instantiate these.)
We then ask whether there is a substitution `σ` such that `C[σ] ⊆ D` -- this is precisely the subsumption problem.

## Unit Forward Subsumption

To check whether a newly derived clause `D = {A₁, ..., Aₙ}` is subsumed by an existing unit clause `C = {B}`, Tammet puts all existing unit clauses into a discrimination tree.
We then look up all the `Aᵢ` in the discrimination tree.
If a unit clause `C = {Aᵢ}` is found, `D` is subsumed by `C`.
If a unit clause `C = {¬ Aᵢ}` is found, we can remove `Aᵢ` from `D`.

I'm not sure whether this helps us.

## Literal Ordering

Tammet defines an ordering `>` on literals with the property that bigger literals are (heuristically) less likely to subsume a random clause.
We may view bigger literals as 'more complex'.
This ordering is used in the following sections.
(I deviate from the paper's structure here.)

The ordering `>` is defined as the lexicographic ordering of the following features:

- `ground(A)`: 1 if `A` is ground; `0` otherwise.
- `size(A)`: the number of subterms in `A`.
- `depth(A)`: the depth of the deepest term in `A`.
- `cnum(A)`: the number of occurrences of constants in `A`.

This ordering additionally (and importantly) has the property that if
`A > B`, then `A` cannot subsume `B`.

I think we could adapt this approach, with some modifications:

- Tammet pre-computes the features.
  We can't do that, but we can do the next-best thing and cache them.
- We have to reducibly normalise our terms first.
  Otherwise the lemma does not hold.
- I'm not sure what our equivalent for the `cnum` function would be.
- There might be other nice features.

## Nonunit Forward Subsumption Indexing 

The core idea here seems to be that instead of indexing *one* input hypothesis per forward rule, we could index *two*.
The scheme is very similar to our iterated discrimination tree, but instead of indexing all permutations of `n` input hypotheses, we only index 2 permutations of 2 input hypotheses.
This keeps the index reasonably small.

Tammet indexes on the biggest two literals in a clause according to the `>` ordering.
We could easily adopt this.
In fact, we already use a much cruder version of this heuristic which simply assumes that later hypotheses are more complex.

## Clause-to-Clause Subsumption

This is the algorithm for actually checking whether a clause `C = {A₁, ..., Aₙ}` subsumes a clause `D = {B₁, ..., Bₘ}`.
The core algorithm is based on a backtracking search:

- Check whether `A₁` subsumes any of the `Bᵢ`.
  - If not: fail.
  - If so: let `σ` be the resulting substitution.
    - Check whether `A₂[σ]` subsumes any of the `Bⱼ`.
      - If not, backtrack and check subsumption of `A₁` for other `Bⱼ`.
      - Etc.

Aesop currently implements precisely this approach.

Tammet describes a number of optimisations (following a paper by Gottlob and Leitsch) to avoid backtracking.
E.g. if a literal `Aᵢ` is ground, it never needs to be backtracked because we wouldn't get a different substitution anyway.
We could implement these optimisations as well.

Additionally, Tammet uses a number of tests that can quickly determine non-subsumption, based on the same features used for the literal ordering.
For example:

- If `A > B`, then `A` does not subsume `B`.
- If the set of predicate names (for us: constant names) in `A` is not a subset of those in `B`, then `A` does not subsume `B`.

This looks like a very good idea to me.

## Back Subsumption

Here the main idea is, again, that `A > B` implies that `A` does not subsume `B`.
Thus, it suffices to check a small number of clauses.
As a result, linear search is sufficiently efficient.
