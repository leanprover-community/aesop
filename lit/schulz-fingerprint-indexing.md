# Stephan Schulz: Fingerprint Indexing for Paramodulation and Rewriting

https://link.springer.com/chapter/10.1007/978-3-642-31365-3_37

## Overview

The paper introduces fingerprint indexing, a term indexing technique that serves as an alternative to discrimination tree indexing.

## Preliminaries

We work in first-order logic.

A *position* in a term is a sequence of natural numbers.
Let `ε` be the empty sequence.
Let `i.p` be the sequence `p` with `i` prepended.
The term `t|p` at position `p` of term `t` is (partially) defined as follows:

- `t|ε = t`
- `f(x₁, ..., xₙ)|i.p = xᵢ|p`

## Fingerprints

Let `p` be a position and `t` a term.
The *general fingerprint feature function* `gfpf(t, p)` is defined by

- `gfpf(t, p) = A` if `t|p` is a variable
- `gfpf(t, p) = f` if `t|p` is the function symbol `f`
- `gfpf(t, p) = B` if `t|p` is undefined but `t|q` is a variable for some prefix `q` of `p`
- `gfpf(t, p) = N` otherwise

A *fingerprint feature function* is `gfpf(·, p)` for some fixed position `p`.

By evaluating a fingerprint feature function for terms `t` and `u`, we can determine whether `t` and `q` may match/unify.
Essentially, we look at the position in both terms and check whether they have either the same function symbol there or a variable.
If not, we can be sure that the two terms won't unify.

We can evaluate multiple fingerprint feature functions to get a vector of fingerprint features for each term.
We call this a *fingerprint*.

## Fingerprint Index

By arranging the fingerprint features in a trie, we can get an efficient index for fingerprints, just like in <schulz-feature-vector.md>.

## Use for Aesop Forward Reasoning

Same use cases as a discrimination tree afaict.
May provide better performance, but probably not drastically better.
