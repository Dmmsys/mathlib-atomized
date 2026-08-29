/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter

/-!
# Sequences in topological spaces

In this file we define sequential closure, continuity, compactness etc.

## Main definitions

### Set operation
* `seqClosure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `IsSeqClosed s`: predicate saying that a set is sequentially closed, i.e., `seqClosure s ⊆ s`;
* `SeqContinuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `IsSeqCompact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `FrechetUrysohnSpace X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `SequentialSpace X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `SeqCompactSpace X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Tags

sequentially closed, sequentially compact, sequential space
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
Definition of `seqClosure` / `seqClosure` 的定义

English:
definition seqClosure
  signature: (s : Set X)
  body: { a | exists x : Nat -> X, (forall n : Nat, x n in s) ∧ Tendsto x atTop (𝓝 a) }

中文:
定义 seqClosure
  签名: (s : Set X)
  定义体: { a | exists x : Nat -> X, (forall n : Nat, x n in s) ∧ Tendsto x atTop (𝓝 a) }

Depends on / 依赖: Tendsto
-/
def seqClosure (s : Set X) : Set X :=
  { a | exists x : Nat -> X, (forall n : Nat, x n in s) ∧ Tendsto x atTop (𝓝 a) }

/--
Definition of `IsSeqClosed` / `IsSeqClosed` 的定义

English:
definition IsSeqClosed
  signature: (s : Set X)
  body: forall ⦃x : Nat -> X⦄ ⦃p : X⦄, (forall n, x n in s) -> Tendsto x atTop (𝓝 p) -> p in s

中文:
定义 IsSeqClosed
  签名: (s : Set X)
  定义体: forall ⦃x : Nat -> X⦄ ⦃p : X⦄, (forall n, x n in s) -> Tendsto x atTop (𝓝 p) -> p in s

Depends on / 依赖: Tendsto
-/
def IsSeqClosed (s : Set X) : Prop :=
  forall ⦃x : Nat -> X⦄ ⦃p : X⦄, (forall n, x n in s) -> Tendsto x atTop (𝓝 p) -> p in s

/--
Definition of `SeqContinuous` / `SeqContinuous` 的定义

English:
definition SeqContinuous
  signature: (f : X -> Y)
  body: forall ⦃x : Nat -> X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) -> Tendsto (f ∘ x) atTop (𝓝 (f p))

中文:
定义 SeqContinuous
  签名: (f : X -> Y)
  定义体: forall ⦃x : Nat -> X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) -> Tendsto (f ∘ x) atTop (𝓝 (f p))

Depends on / 依赖: Tendsto
-/
def SeqContinuous (f : X -> Y) : Prop :=
  forall ⦃x : Nat -> X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) -> Tendsto (f ∘ x) atTop (𝓝 (f p))

/--
Definition of `IsSeqCompact` / `IsSeqCompact` 的定义

English:
definition IsSeqCompact
  signature: (s : Set X)
  body: forall ⦃x : Nat -> X⦄, (forall n, x n in s) -> exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)

中文:
定义 IsSeqCompact
  签名: (s : Set X)
  定义体: forall ⦃x : Nat -> X⦄, (forall n, x n in s) -> exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)

Depends on / 依赖: StrictMono, Tendsto
-/
def IsSeqCompact (s : Set X) :=
  forall ⦃x : Nat -> X⦄, (forall n, x n in s) -> exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)

variable (X)

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
@[mk_iff]
/--
Definition of `SeqCompactSpace` / `SeqCompactSpace` 的定义

English:
class SeqCompactSpace
  parameters: : Prop where
  axioms and operations (1):
    - isSeqCompact_univ : IsSeqCompact (univ : Set X)

中文:
类 SeqCompactSpace
  参数: : 命题 where
  公理与运算 (1 个):
    - isSeqCompact_univ : IsSeqCompact (univ : Set X)
-/
class SeqCompactSpace : Prop where
  isSeqCompact_univ : IsSeqCompact (univ : Set X)

export SeqCompactSpace (isSeqCompact_univ)

/--
Definition of `FrechetUrysohnSpace` / `FrechetUrysohnSpace` 的定义

English:
class FrechetUrysohnSpace
  parameters: : Prop where
  axioms and operations (1):
    - closure_subset_seqClosure : forall s : Set X, closure s subseteq seqClosure s

中文:
类 FrechetUrysohnSpace
  参数: : 命题 where
  公理与运算 (1 个):
    - closure_subset_seqClosure : 对任意 s : Set X, closure s subseteq seqClosure s
-/
class FrechetUrysohnSpace : Prop where
  closure_subset_seqClosure : forall s : Set X, closure s subseteq seqClosure s

/--
Definition of `SequentialSpace` / `SequentialSpace` 的定义

English:
class SequentialSpace
  parameters: : Prop where
  axioms and operations (1):
    - isClosed_of_seq : forall s : Set X, IsSeqClosed s -> IsClosed s

中文:
类 SequentialSpace
  参数: : 命题 where
  公理与运算 (1 个):
    - isClosed_of_seq : 对任意 s : Set X, IsSeqClosed s -> IsClosed s

Depends on / 依赖: SequentialSpace, SequentialSpace.isClosed_of_seq, isClosed_of_seq
-/
class SequentialSpace : Prop where
  isClosed_of_seq : forall s : Set X, IsSeqClosed s -> IsClosed s

variable {X}

/--
theorem `IsSeqClosed.isClosed` / 定理 `IsSeqClosed.isClosed`

English:
theorem IsSeqClosed.isClosed
  given: [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s)
  proof: SequentialSpace.isClosed_of_seq s hs

中文:
定理 IsSeqClosed.isClosed
  条件: [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s)
  证明: SequentialSpace.isClosed_of_seq s hs
-/
protected theorem IsSeqClosed.isClosed [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s) :
    IsClosed s :=
  SequentialSpace.isClosed_of_seq s hs
