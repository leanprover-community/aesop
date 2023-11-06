# Stephan Schulz: Simple and Efficient Clause Subsumption with Feature Vector Indexing

https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=2d90ca4194160d90593bd89661649aa08ca78adb

## Overview

This paper discusses feature vector indexing for clause subsumption.

## Preliminaries

See <tammet-subsumption.md>.

## Subsumption-Compatible Clause Features

A *subsumption-compatible clause feature* is a function `F` from clauses to ℕ such that whenever `C` subsumes `D`, `F(C) ≤ F(D)`.

I think this is exactly the same idea as the literal ordering in <tammet-subsumption.md>.

For a clause `C`, let `C⁺` be the set of positive literals in `C` and let `C⁻` be the set of negative literals in `C`.
Let `|C|` be the number of literals in `C`.
Let `|C|f` be the number of occurrences of the function symbol `f` in `C`.
Let `df(C)` be the deepest occurrence of the function symbol `f` in `C`.

The following features are subsumption-compatible:

- `|C⁺|` and `|C⁻|`
- `|C⁺|f` and `|C⁻|f` for arbitrary `f`
- `df(C⁺)` and `df(C⁻)` for arbitrary `f`
- Any linear combination of subsumption-compatible features with non-negative coefficients.

## Clause Feature Vectors

A *clause feature vector function* is a function from clauses to `ℕⁿ` which maps any clause `C` to the *feature vector* `(F₁(C), ..., Fₙ(C))`, where `Fᵢ(C)` is a clause feature.

A feature vector function is *subsumption-compatible* if all its component features are.
For such feature vector functions, it follows that if `C` subsumes `D`, then `(F₁(C), ..., Fₙ(C)) ≤ (F₁(D), ..., Fₙ(D))` (where `≤` is defined componentwise).
We can thus quickly determine whether `C` might subsume `D`, based on their feature vectors.

## Feature Vector Index

We can index clauses by their feature vectors by arranging the features in a trie.
This allows us to efficiently query clauses that may subsume a given clause, and also clauses that may be subsumed by a given clause.

The order in which we arrange features can drastically change the branching behaviour, and thus the size, of the trie.
The paper thus performs some statistical analysis to predict the optimal order of the features.

## Relevance for Aesop Forward Reasoning

I believe we could use this indexing scheme in place of discrimination trees.
But since we already have discrimination trees, I'm not sure that we gain much.
