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

/-- The sequential closure of a set `s : Set X` in a topological space `X` is the set of all `a : X`
which arise as limit of sequences in `s`. Note that the sequential closure of a set is not
guaranteed to be sequentially closed. -/
/-
**seqClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：seqClosure (s : Set X) : Set X
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequential closure of a set `s : Set X` in a topological space `X` is the se
t of all `a : X`
which arise as limit of sequences in `s`. Note that the sequential closure of a 
set is not
guaranteed to be sequentially closed.
-/
def seqClosure (s : Set X) : Set X :=
  { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) }

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`, the
limit belongs to `s` as well. Note that the sequential closure of a set is not guaranteed to be
sequentially closed. -/
/-
**IsSeqClosed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSeqClosed (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is sequentially closed if for any converging sequence `x n` of element
s of `s`, the
limit belongs to `s` as well. Note that the sequential closure of a set is not g
uaranteed to be
sequentially closed.
-/
def IsSeqClosed (s : Set X) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → Tendsto x atTop (𝓝 p) → p ∈ s

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
convergent sequences. -/
/-
**SeqContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SeqContinuous (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between topological spaces is sequentially continuous if it commutes 
with limit of
convergent sequences.
-/
def SeqContinuous (f : X → Y) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) → Tendsto (f ∘ x) atTop (𝓝 (f p))

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
/-
**IsSeqCompact** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSeqCompact (s : Set X)
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence.
-/
def IsSeqCompact (s : Set X) :=
  ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)

variable (X)

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
@[mk_iff]
/-
**SeqCompactSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence.
-/
class SeqCompactSpace : Prop where
  isSeqCompact_univ : IsSeqCompact (univ : Set X)

export SeqCompactSpace (isSeqCompact_univ)

/-- A topological space is called a *Fréchet-Urysohn space*, if the sequential closure of any set
is equal to its closure. Since one of the inclusions is trivial, we require only the non-trivial one
in the definition. -/
/-
**FrechetUrysohnSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is called a *Fréchet-Urysohn space*, if the sequential closu
re of any set
is equal to its closure. Since one of the inclusions is trivial, we require only
 the non-trivial one
in the definition.
-/
class FrechetUrysohnSpace : Prop where
  closure_subset_seqClosure : ∀ s : Set X, closure s ⊆ seqClosure s

/-- A topological space is said to be a *sequential space* if any sequentially closed set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space. -/
/-
**SequentialSpace** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：SequentialSpace : Prop where isClosed_of_seq : forall s : Set X, IsSeqClos
ed s -> IsClosed s  variable {X}  /-- In a sequential space, a sequentially clos
ed set is closed. -/ protected theorem IsSeqClosed.isClosed [SequentialSpace X] 
{s : Set X} (hs : IsSeqClosed s) : IsClosed s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is said to be a *sequential space* if any sequentially close
d set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space.
-/
class SequentialSpace : Prop where
  isClosed_of_seq : ∀ s : Set X, IsSeqClosed s → IsClosed s

variable {X}

/-- In a sequential space, a sequentially closed set is closed. -/
/-
**IsSeqClosed.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `IsSeqClosed`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [SequentialSpace X] {s : Set 
X}, IsSeqClosed s → IsClosed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SequentialSpace.isClosed_of_seq`：∀ {X : Type u_1} {inst : TopologicalSpa
ce X} [self : SequentialSpace X] (s : Set X), IsSeqClosed s → IsClosed s

--- 原说明 ---
In a sequential space, a sequentially closed set is closed.
-/
protected theorem IsSeqClosed.isClosed [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s) :
    IsClosed s :=
  SequentialSpace.isClosed_of_seq s hs
