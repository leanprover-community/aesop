# Aesop

This is a work-in-progress proof search tactic for Lean 4.

## Building

With [elan](https://github.com/leanprover/elan) installed, `lake build`
should suffice.

## Adding Aesop to Your Project

To use Aesop in a Lean 4 project, first add this package as a dependency. In
your `lakefile.lean`, add

```lean
dependencies := #[
  { name := `aesop
    src := Source.git "https://github.com/JLimperg/aesop" "<current HEAD commit of this repo>" }
]
```

Now run `lake configure`. Unless you use the exact same Lean 4 nightly as
this project (see our `lean-toolchain`), you'll get a warning. If you use a later
nightly, you'll probably be fine and Aesop will compile anyway. If not, please
open an issue and we'll update the tactic.

You should now be able to use the `aesop` tactic:

```lean
import Aesop

def id' : α → α :=
  by aesop
```

TODO Document (and, indeed, find out) how to use Aesop as a plugin.

## Usage

This section gives an overview of what Aesop does and how to use it. I first
explain how the tactic works (as far as users need to know), then explain how to
configure and use it. Aesop is very work in progress and this text may be out of
date, so if you have questions, please ping me (Jannis Limperg) on the Lean
Zulip or via email.

### Overview

Aesop does best-first search over a collection of rules. A rule is an arbitrary
tactic plus some metadata, particularly an estimate of how likely the rule is to
lead to a successful proof. This estimate is used to prioritise goals and rules.
Rules are registered with an attribute or with arguments to the tactic.

### Rules

A rule is a metaprogram of type
``` lean
RuleTacInput → MetaM RuleTacOutput
```
This is essentially `MVarId → MetaM (List MVarId)` plus some additional
metadata, so rules are at their core just `MetaM` tactics.

Rules come in three flavours: normalisation rules, safe rules and unsafe rules.
Normalisation rules are applied to bring a goal into normal form. They cannot
fail and must produce at most one goal. Safe rules are rules that are never
backtracked: if a safe rule succeeds on a goal, it is applied and no other rule
is considered. Unsafe rules (which comprise most rules), in contrast, are
backtrackable.

Rules may not modify the environment. I do not think this will be a problem, but
it means no `evalExpr`. (More precisely, environment modifications are reverted
when the tactic finishes, which will likely cause the rule to fail. In
principle, we could support environment modifications, but it would require some
engineering and perhaps cooperation from the rule tactics.)

### Simplification

During goal normalisation, we invoke the simplifier once with the default simp
lemmas as a builtin rule. I expect this rule will do most of the normalisation
work. Users can also register additional simp lemmas which are only used by
Aesop.

(Ideally, users should be able to easily define and enable/disable sets of Aesop
simp lemmas, as well as sets of Aesop rules.)

### Search Tree

As we apply rules to goals, we build a (mutable) search tree. This is an and-or
tree containing goal nodes and rule application nodes. The root node is the
initial goal. A rule application (rapp for short) produces a rule application
node, which has zero or more subgoals. The rapps of a goal form a disjunction
(we must prove any of them to prove the goal) while the subgoals of a rapp form
a conjunction (we must prove all of them).

At any point during the search, a goal or rapp can be in one of three states:

- proven: A goal is proven if it has a proven rapp. A rapp is proven if all its
  subgoals are proven.
- unprovable: A goal is unprovable if all of its rapps are unprovable *and* we
  have attempted to apply all possible rules to the goal. A rapp is unprovable
  if any of its subgoals is unprovable.
- irrelevant: A goal is irrelevant if one of its siblings is unprovable. (Then
  the parent rapp is already unprovable.) Similarly, a rapp is irrelevant if
  one of its siblings is already proven.

As soon as a goal or rapp is marked as irrelevant, it is not considered in the
search.

### Prioritisation

We prioritise goals based on an estimate of how likely they are to be part of a
successful proof. To form this estimate, we associate each unsafe rule with a
success probability, which gives a rough estimate of how likely the rule is to
solve the goal. E.g. both or-introduction rules might be assigned a 50% success
probability. Safe rules are treated as having 100% success probability.

The success probability of a goal is then the product of the success
probabilities of all rapps in its branch. Thus, if we search for a proof of `P ∨
Q ∨ R`, we may end up with goals `P (50%)`, `Q (25%)` and `R (25%)` (which, I
suppose, illustrates that this is hardly an exact method).

When we have picked the highest-priority goal, we must also prioritise the rules
to be applied. The three rule flavours have different prioritisation mechanisms:

- Norm and safe rules have an integer penalty. They are applied in order of
  penalty, lowest first. The builtin `simp` normalisation rule has penalty 0.
- Unsafe rules are applied in order of success probability, highest first.

### Search

The search state contains a priority queue of active goals and a search tree.
Initially, they both contain only the goal on which the tactic was called. Then
the tactic executes the following loop until the root goal is either proven or
unprovable:

1. From the active goal queue, pick the goal with the highest success
   probability. If it is already proven/unprovable/irrelevant, skip it.
2. Run all applicable normalisation rules on the goal (in penalty order). Record
   the new goal in the search tree. If any of the normalisation rules produces
   no subgoals, the goal is proven. If any of the normalisation rules produces
   more than one goal, the tactic fails.
3. Try to apply the applicable safe rules to the goal, in penalty order. If any
   applies, record a new rapp and its subgoals. Since we do not want to apply
   any other rules to the goal, it is not reinserted into the active goal queue.
4. If no safe rule succeeded, try to apply the applicable unsafe rules to the
   goal, in order of success probability. If any applies, record the rapp and
   its subgoals, then reinsert the goal into the active goal queue (unless there
   are no more unsafe rules to apply).
   
### Indexing

Rules can be indexed with an expression (or, more accurately, a discrimination
tree key). Such rules are stored in a discrimination tree and are only used if a
goal's target matches the key. (This is why I wrote 'applicable rules' above.)

Other indexing methods, particularly by hypothesis, are WIP.

### Default Rules

Aesop includes a collection of rules that are always part of the rule set.
Currently, this collection is rather small and haphazard. See
`Aesop/DefaultRules.lean`.

### Attribute

With these preliminaries out of the way, we can get to the practical part. Rules
are added to the global Aesop rule set by annotating definitions with the
`@[aesop]` attribute. The syntax of this attribute is

``` lean
@[aesop <flavour>? <priority>? <clause>*]
```

where

- `flavour` is `norm` for a normalisation rule, `safe` for a safe rule,
  `unsafe` for an unsafe rule. If it is omitted, the default is `unsafe`.
- `priority` is an integer for `norm` and `safe` rules or a success probability
  for unsafe rule. The success probability is written `n%` with `0 <= n <= 100`.
  (The percent sign is mandatory.) The priority may be omitted for `norm` and
  `safe` rules (the default is 1), but not for `unsafe` rules.
- `clause` is one of the following configuration clauses (which must be enclosed
  in parentheses unless they consist of only one word):
  - `(builder <builder>)`: determines how the definition is interpreted as a
    rule. See below.
  - Other clauses WIP.

The semantics of this attribute are the same (slightly unfortunate) ones as for
all Lean attributes: as soon as a file is transitively imported, all its
`aesop`-annotated definitions are added to the rule set. The attribute can be
scoped to tame this proliferation a little.

#### Rule Builders

Rule builders (or just builders) interpret a definition as a rule (i.e., a
tactic). The following builders are currently implemented:

- `apply`: Turns any definition `f : ∀ xᵢ, T xᵢ` into the tactic `apply f`.
- `tactic`: Turns a tactic definition into a tactic. A tactic definition must
  have one of the following types:
  ```lean
  RuleTac = RuleTacInput → MetaM RuleTacOutput
    -- Is directly used as a rule tactic.
  UserRuleTac = RuleTacInput → MetaM UserRuleTacOutput
    -- Can omit some of the information from `RuleTacOutput`. Somewhat less
    -- performant since Aesop then has to calculate this information itself.
  TacticM Unit
    -- Is converted into a UserRuleTac.
  ```
- `simp`: Turns a definition `e : ∀ xᵢ, y = z` into a simp lemma used by the
  builtin normalisation `simp` rule. This is like tagging `e` with `@[simp]`.
  Applies only to normalisation rules.
- `unfold`: Makes the builtin normalisation `simp` rule unfold the tagged
  definition. Applies only to normalisation rules.

If no builder is given, a default builder is chosen based on the type of the
tagged definition. For safe and unsafe rules, the `tactic` and `apply` builders
are tried. For normalisation rules, the `tactic`, `simp` and `apply` builders
are tried.

More builders, particularly for forward rules (i.e. rules applied to a
hypothesis), are WIP.

#### Examples

Some possibly useful rules:

``` lean
-- This is a default rule.
@[aesop safe 1 (builder tactic)] -- penalty and builder could be omitted
def aesopAssumption : TacticM Unit := do
  evalTactic (← `(tactic|assumption))

-- This should be a default rule.
@[aesop unsafe 50% (builder apply)] -- 'unsafe' and builder could be omitted
def aesopOrIntroLeft : α → α ∨ β :=
  Or.inl
```

### Tactic Invocation

The tactic has this syntax:

``` lean
aesop <clause>*
```

Clauses may be added to configure the tactic. Currently implemented are:

- `(norm [<ident> <penalty>? <clause>*, ...])`: adds one or more normalisation
  rules. For each rule, give the name of the definition that should be added,
  the penalty (default 1) and configuration clauses. This is equivalent to
  tagging `<ident>` with `@[aesop norm <penalty> <clause>*]` (but only for this
  invocation). `<ident>` may also be a hypothesis, but not all builders support
  this (yet).
- `(safe [<ident> <penalty>? <clause>*, ...])`: same for safe rules.
- `(unsafe [<ident> <percent>% <clause>*, ...])`: same for unsafe rules (but
  with a success probability instead of a penalty).

### Debugging

To see step-by-step what Aesop is doing, use

``` lean
set_option trace.aesop.steps true
```

There are also various `trace.aesop.steps.*` options which you can
set to `false` to disable certain parts of the output. See `Aesop/Tracing.lean`.

To see the rule set used by a particular tactic invocation, use

``` lean
set_option trace.aesop.ruleSet true
```

## Implementation

Some notes on major implementation choices (very incomplete).

### Search Tree

The search tree is a mutable, non-persistent tree, so nodes contain pointers
(`IO.Ref`s) to their children and parents and when we update a node, we do so
destructively. This is a bit of work because we must deal with unsafe data
types, but it should be very fast. See `MutAltTree.lean` and `Tree.lean`.

### Propagating 'proven'/'unprovable'/'irrelevant'

When we determine that a goal is proven or unprovable, we must propagate this
information to its ancestors and siblings, like this:

- When a goal is proven, we iterate through its ancestors. Then, for each
  ancestor:
  - If the ancestor is a goal, we mark it as proven.
  - If the ancestor is a rapp and all its subgoals are proven, we mark it
    as proven. We also mark the siblings of this rapp and their descendants as
    irrelevant.
  - If the ancestor is a rapp and not all its subgoals are proven, we stop the
    iteration.
- When a goal is unprovable, we also iterate through its ancestors:
  - If the ancestor is a rapp, we mark it as unprovable.
  - If the ancestor is a goal and all its rapps are unprovable and the goal
    does not have any applicable rules, we mark it as unprovable. We also
    mark the siblings of this goal and their descendands as irrelevant.
  - If the ancestor is a goal which has rules that may succeed, we stop the
    iteration.

See `setProven` and friends in `Tree.lean`.

### Metavariables

This is not fully implemented yet. But basically, the problem is that when a
rule generates metavariables, its subgoals are not independent any more.
Example:

``` text
                   ⊢ x ~ z
                      |
                    ~-trans
                    /      \
              ⊢ x ~ ?y    ⊢ ?y ~ z
```

When we apply a rule to the goal `x ~ ?y`, it may instantiate the meta `?y`,
thus irreversibly changing the goal `?y ~ z`. This is bad if the applied rule
is unsafe and should thus be backtrackable.

There are several possible solutions to this problem. The one I'm currently
implementing is essentially this: when a rule instantiates a meta, we duplicate
the entire branch of the tree that depends on the meta. In the example:

``` text
                   ⊢ x ~ z
                      |-------------------------------|
                    ~-trans [?y := x]              ~-trans
                    /      \                       /      \
              ⊢ x ~ x    ⊢ x ~ z             ⊢ x ~ ?y    ⊢ ?y ~ z
                 |
               ~-refl [?y := x]
```

Then we perhaps prioritise the branch with the instantiated meta.

### Metavariable Contexts

To implement the above solution (and also for general hygiene), it is useful
to give every rapp its own metavariable context. A rapp thus stores a
`Meta.SavedState` reflecting the `MetaM` state after the rule was applied to
its parent goal. In this state, the parent goal meta is assigned to the proof
term produced by the rule tactic and the produced subgoal metas are in scope.

With this setup, we can easily duplicate a branch by just copying all the nodes
and their meta states. If we operated on the global `MetaM` state instead, we
would have to be very careful to duplicate all relevant metavariables. The
tradeoff is that we now have to be careful to always operate in the metavariable
context of the correct rapp. See `runMetaM` and friends in
`BestFirstSearch.lean`. I've tried a few approaches to make this less of a
footgun, but none of them pulled its weight.

When we switch between different rapps' `MetaM` states, we use `saveState` and
`restoreState`. These only affect the backtrackable parts of the state, notably
excluding trace messages and caches. The non-backtrackable parts are merged into
the global `MetaM` state, which serves us well since it lets us collect the
trace messages from all rules we run.

The environment, on the other hand, is backtrackable, so changes to it are not
merged into the global state. This is a good thing since we probably do not want
rules which end up not contributing to the proof to change the environment.
However, it also means that, at least without special support from the proof
reconstruction procedure below, even the rules that do contribute to the proof
cannot change the environment (and will probably fail in mysterious ways if they
try).

### Proof Reconstruction

When Aesop has proven a goal, we must still extract the proof term. This is
not entirely trivial since the proof is stored as a sequence of metavariable
assignments in the `MetaM` states of the relevant rapps. These assignments are
as follows:

- When we normalise a goal `G`, we run the normalisation tactics on `G`'s goal
  meta in the context of `G`'s parent rapp. The new goal meta resulting from
  this process then becomes `G`'s goal meta.
- When we run a regular (safe or unsafe) rule on a goal `G`, we run the rule
  tactic on `G`'s goal meta in the context of `G`'s parent rapp. The resulting
  `MetaM` state then becomes the state of the new rapp. In this state, `G`'s
  goal meta is assigned and the subgoals produced by the rule tactic are in
  scope. Note that the `MetaM` state of `G`'s parent rapp is not modified at
  all.

This means that to reconstruct the proof term, we must iterate through the
successful branch of the search tree, starting at the leaf nodes (which are
rapps without subgoals). From there, we proceed up the tree as follows:

- For each goal `G`, we find the rapp that proves `G`. Then we assign `G`'s goal
  meta (in the `MetaM` context of `G`'s parent rapp) to the proof term extracted
  from the proven rapp.
- To get the proof term of a rapp `R`, we instantiate the goal meta of `R`'s
  parent goal in the `MetaM` context of `R`. This should give us a meta-free
  proof term since all metas that previously occurred in the assignment of this
  meta -- particularly the subgoals of `R` -- have been assigned in previous
  steps of the iteration.
