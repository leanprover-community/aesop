# Tanel Tammet, GKC: A Reasoning System for Large Knowledge Bases

<https://link.springer.com/chapter/10.1007/978-3-030-29436-6_32>

## Overview

Describes GKC, a first-order theorem prover designed to handle large databases of shallow facts.
Largely irrelevant for us, except possibly for one cute trick.

For subsumption checking, GKC uses feature vectors as in <tamet-subsumption.md> and <schulz-feature.vector.md>.
Among others, it uses one novel feature: a hash of a small *ground prefix* of each literal.
This is a prefix of the sequential rendering of a literal (say, the first 3 constants), excluding variables.
Like other features, this can be used for a quick, approximate check for non-subsumption.

I don't expect that this level of optimisation will help us much, but I thought it was cool.
