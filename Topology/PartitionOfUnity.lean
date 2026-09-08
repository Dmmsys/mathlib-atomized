/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Continuous partition of unity

In this file we define `PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)`
to be a continuous partition of unity on `s` indexed by `ι`. More precisely,
`f : PartitionOfUnity ι X s` is a collection of continuous functions `f i : C(X, ℝ)`, `i : ι`,
such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* `∑ᶠ i, f i x = 1` for all `x ∈ s`;
* `∑ᶠ i, f i x ≤ 1` for all `x : X`.

In the case `s = univ` the last assumption follows from the previous one but it is convenient to
have this assumption in the case `s ≠ univ`.

We also define a bump function covering,
`BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)`, to be a collection of
functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* for each `x ∈ s` there exists `i : ι` such that `f i y = 1` in a neighborhood of `x`.

The term is motivated by the smooth case.

If `f` is a bump function covering indexed by a linearly ordered type, then
`g i x = f i x * ∏ᶠ j < i, (1 - f j x)` is a partition of unity, see
`BumpCovering.toPartitionOfUnity`. Note that only finitely many terms `1 - f j x` are not equal
to one, so this product is well-defined.

Note that `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so most terms in the sum
`∑ᶠ i, g i x` cancel, and we get `∑ᶠ i, g i x = 1 - ∏ᶠ i, (1 - f i x)`, and the latter product
equals zero because one of `f i x` is equal to one.

We say that a partition of unity or a bump function covering `f` is *subordinate* to a family of
sets `U i`, `i : ι`, if the closure of the support of each `f i` is included in `U i`. We use
Urysohn's Lemma to prove that a locally finite open covering of a normal topological space admits a
subordinate bump function covering (hence, a subordinate partition of unity), see
`BumpCovering.exists_isSubordinate_of_locallyFinite`. If `X` is a paracompact space, then any
open covering admits a locally finite refinement, hence it admits a subordinate bump function
covering and a subordinate partition of unity, see `BumpCovering.exists_isSubordinate`.

We also provide two slightly more general versions of these lemmas,
`BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop` and
`BumpCovering.exists_isSubordinate_of_prop`, to be used later in the construction of a smooth
partition of unity.

## Implementation notes

Most (if not all) books only define a partition of unity of the whole space. However, quite a few
proofs only deal with `f i` such that `tsupport (f i)` meets a specific closed subset, and
it is easier to formalize these proofs if we don't have other functions right away.

We use `WellOrderingRel j i` instead of `j < i` in the definition of
`BumpCovering.toPartitionOfUnity` to avoid a `[LinearOrder ι]` assumption. While
`WellOrderingRel j i` is a well order, not only a strict linear order, we never use this property.

## Tags

partition of unity, bump function, Urysohn's lemma, normal space, paracompact space
-/

@[expose] public section

universe u v

open Function Set Filter Topology

noncomputable section

/-- A continuous partition of unity on a set `s : Set X` is a collection of continuous functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* the sum `∑ᶠ i, f i x` is equal to one for every `x ∈ s` and is less than or equal to one
  otherwise.

If `X` is a normal paracompact space, then `PartitionOfUnity.exists_isSubordinate` guarantees
that for every open covering `U : Set (Set X)` of `s` there exists a partition of unity that is
subordinate to `U`.
-/
/-
**PartitionOfUnity** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X
参数：ι X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous partition of unity on a set `s : Set X` is a collection of continuo
us functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every po
int `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` 
are zero on `U`;
* the functions `f i` are nonnegative;
* the sum `∑ᶠ i, f i x` is equal to one for every `x ∈ s` and is less than or eq
ual to one
  otherwise.

If `X` is a normal paracompact space, then `PartitionOfUnity.exists_isSubordinat
e` guarantees
that for every open covering `U : Set (Set X)` of `s` there exists a partition o
f unity that is
subordinate to `U`.
-/
structure PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collection of continuous functions underlying this partition of unity -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- the functions sum up to one on `s` -/
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  /-- the functions sum up to at most one, globally -/
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1

/-- A `BumpCovering ι X s` is an indexed family of functions `f i`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* for all `i`, `x` we have `0 ≤ f i x ≤ 1`;
* each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`.

One of the main use cases for a `BumpCovering` is to define a `PartitionOfUnity`, see
`BumpCovering.toPartitionOfUnity`, but some proofs can directly use a `BumpCovering` instead of
a `PartitionOfUnity`.

If `X` is a normal paracompact space, then `BumpCovering.exists_isSubordinate` guarantees that for
every open covering `U : Set (Set X)` of `s` there exists a `BumpCovering` of `s` that is
subordinate to `U`.
-/
/-
**BumpCovering** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X
参数：ι X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `BumpCovering ι X s` is an indexed family of functions `f i`, `i : ι`, such th
at

* the supports of `f i` form a locally finite family of sets, i.e., for every po
int `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` 
are zero on `U`;
* for all `i`, `x` we have `0 ≤ f i x ≤ 1`;
* each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`.

One of the main use cases for a `BumpCovering` is to define a `PartitionOfUnity`
, see
`BumpCovering.toPartitionOfUnity`, but some proofs can directly use a `BumpCover
ing` instead of
a `PartitionOfUnity`.

If `X` is a normal paracompact space, then `BumpCovering.exists_isSubordinate` g
uarantees that for
every open covering `U : Set (Set X)` of `s` there exists a `BumpCovering` of `s
` that is
subordinate to `U`.
-/
structure BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collections of continuous functions underlying this bump covering -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- the functions are each at most one -/
  le_one' : toFun ≤ 1
  /-- Each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`. -/
  eventuallyEq_one' : ∀ x ∈ s, ∃ i, toFun i =ᶠ[𝓝 x] 1

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

namespace PartitionOfUnity

variable {E : Type*} [AddCommMonoid E] [SMulWithZero ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {s : Set X} (f : PartitionOfUnity ι X s)

/-
**PartitionOfUnity.** 是 Mathlib 中的一个实例，位于命名空间 `PartitionOfUnity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (PartitionOfUnity ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**PartitionOfUnity.locallyFinite** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {s : Set X} (f : P
artitionOfUnity ι X s),   LocallyFinite fun i => Function.support ⇑(f i)
参数：f : PartitionOfUnity ι X s；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.locallyFinite'`：∀ {ι : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity 
ι X s), LocallyFinite…
-/
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'
/-
**PartitionOfUnity.locallyFinite_tsupport** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOf
Unity`。
形式化陈述：locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.closure`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologic
alSpace X] {f : ι → Set X},   LocallyFinite f → LocallyFinite fun i => closure (
f i)
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
-/
theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure
/-
**PartitionOfUnity.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：nonneg (i : ι) (x : X) : 0 <= f i x
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.nonneg'`：∀ {ι : Type u_1} {X : Type u_2} [inst : Topolo
gicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X s),
 0 ≤ self.toFu…
-/
theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x
/-
**PartitionOfUnity.sum_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：sum_eq_one {x : X} (hx : x in s) : ∑ᶠ i, f i x = 1
参数：hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_eq_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : To
pologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X
 s), ∀ x ∈ s, ∑ᶠ (…
-/
theorem sum_eq_one {x : X} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx

/-- If `f` is a partition of unity on `s`, then for every `x ∈ s` there exists an index `i` such
that `0 < f i x`. -/
/-
**PartitionOfUnity.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：exists_pos {x : X} (hx : x in s) : exists i, 0 < f i x
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_eq_one`：sum_eq_one {x : X} (hx : x in s) : ∑ᶠ i, f 
i x = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `PartitionOfUnity.nonneg`：nonneg (i : ι) (x : X) : 0 <= f i x
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `f` is a partition of unity on `s`, then for every `x ∈ s` there exists an in
dex `i` such
that `0 < f i x`.
-/
theorem exists_pos {x : X} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  have H := f.sum_eq_one hx
  contrapose! H
  simpa only [fun i => (H i).antisymm (f.nonneg i x), finsum_zero] using zero_ne_one
/-
**PartitionOfUnity.sum_le_one** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：sum_le_one (x : X) : ∑ᶠ i, f i x <= 1
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.sum_le_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : To
pologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X
 s) (x : X), ∑ᶠ (i…
-/
theorem sum_le_one (x : X) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x
/-
**PartitionOfUnity.sum_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：sum_nonneg (x : X) : 0 <= ∑ᶠ i, f i x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finsum_nonneg`：∀ {α : Sort u_4} {M : Type u_7} [inst : AddCommMonoid M] 
[inst_1 : Preorder M] [IsOrderedAddMonoid M] {f : α → M},   (∀ (i : α), 0 ≤ f i)
 → …
· 使用定理 `PartitionOfUnity.nonneg`：nonneg (i : ι) (x : X) : 0 <= f i x
-/
theorem sum_nonneg (x : X) : 0 ≤ ∑ᶠ i, f i x :=
  finsum_nonneg fun i => f.nonneg i x
/-
**PartitionOfUnity.le_one** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：le_one (i : ι) (x : X) : f i x <= 1
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `single_le_finsum`：∀ {α : Type u_1} {M : Type u_7} [inst : AddCommMonoid 
M] [inst_1 : Preorder M] [IsOrderedAddMonoid M] (i : α)   {f : α → M}, Function.
HasFin…
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
· 使用定理 `PartitionOfUnity.nonneg`：nonneg (i : ι) (x : X) : 0 <= f i x
· 使用定理 `PartitionOfUnity.sum_le_one`：sum_le_one (x : X) : ∑ᶠ i, f i x <= 1
-/
theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  (single_le_finsum i (f.locallyFinite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

section finsupport

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

/-- The support of a partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ support f i`, i.e. `f i x₀ ≠ 0`. -/
/-
**PartitionOfUnity.finsupport** 是 Mathlib 中的一个定义，位于命名空间 `PartitionOfUnity`。
形式化陈述：finsupport : Finset ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ support f i`, i.e. `f i x₀ ≠ 0`.
-/
def finsupport : Finset ι := (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]
/-
**PartitionOfUnity.mem_finsupport** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：mem_finsupport (x₀ : X) {i} : i in ρ.finsupport x₀ ↔ i in support fun i =>
 ρ i x₀
参数：x₀ : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_finsupport (x₀ : X) {i} :
    i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i ↦ ρ i x₀ := by
  simp only [finsupport, mem_support, Finite.mem_toFinset, mem_ofPred_eq]

@[simp]
/-
**PartitionOfUnity.coe_finsupport** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：coe_finsupport (x₀ : X) : (ρ.finsupport x₀ : Set ι) = support fun i => ρ i
 x₀
参数：x₀ : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `PartitionOfUnity.mem_finsupport`：mem_finsupport (x₀ : X) {i} : i in ρ.fi
nsupport x₀ ↔ i in support fun i => ρ i x₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_finsupport (x₀ : X) :
    (ρ.finsupport x₀ : Set ι) = support fun i ↦ ρ i x₀ := by
  ext
  rw [Finset.mem_coe, mem_finsupport]

variable {x₀ : X}
/-
**PartitionOfUnity.sum_finsupport** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：sum_finsupport (hx₀ : x₀ in s) : ∑ i in ρ.finsupport x₀, ρ i x₀ = 1
参数：hx₀ : x₀ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartitionOfUnity.sum_eq_one`：sum_eq_one {x : X} (hx : x in s) : ∑ᶠ i, f 
i x = 1
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `PartitionOfUnity.coe_finsupport`：coe_finsupport (x₀ : X) : (ρ.finsupport
 x₀ : Set ι) = support fun i => ρ i x₀
-/
theorem sum_finsupport (hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1 := by
  rw [← ρ.sum_eq_one hx₀, finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x₀).superset]
/-
**PartitionOfUnity.sum_finsupport'** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：sum_finsupport' (hx₀ : x₀ in s) {I : Finset ι} (hI : ρ.finsupport x₀ subse
teq I) : ∑ i in I, ρ i x₀ = 1
参数：hx₀ : x₀ in s；hI : ρ.finsupport x₀ subseteq I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `PartitionOfUnity.sum_finsupport`：sum_finsupport (hx₀ : x₀ in s) : ∑ i in
 ρ.finsupport x₀, ρ i x₀ = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartitionOfUnity.mem_finsupport`：mem_finsupport (x₀ : X) {i} : i in ρ.fi
nsupport x₀ ↔ i in support fun i => ρ i x₀
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem sum_finsupport' (hx₀ : x₀ ∈ s) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i ∈ I, ρ i x₀ = 1 := by
  classical
  rw [← Finset.sum_sdiff hI, ρ.sum_finsupport hx₀]
  suffices ∑ i ∈ I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i ∈ I \ ρ.finsupport x₀, 0 by
    rw [this, add_eq_right, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsupport, mem_support, Classical.not_not] at hx
  exact hx.2
/-
**PartitionOfUnity.sum_finsupport_smul_eq_finsum** 是 Mathlib 中的一个定理，位于命名空间 `Part
itionOfUnity`。
形式化陈述：sum_finsupport_smul_eq_finsum {M : Type*} [AddCommMonoid M] [Module Real M
] (φ : ι -> X -> M) : ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ
 i x₀
参数：φ : ι -> X -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartitionOfUnity.coe_finsupport`：coe_finsupport (x₀ : X) : (ρ.finsupport
 x₀ : Set ι) = support fun i => ρ i x₀
· 使用引理 `Function.support_smul`：support_smul [Semiring R] [IsDomain R] [AddCommMo
noid M] [Module R M] [Module.IsTorsionFree R M] (f : α -> R) (g : α -> M) : supp
ort (f • g)…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem sum_finsupport_smul_eq_finsum {M : Type*} [AddCommMonoid M] [Module ℝ M] (φ : ι → X → M) :
    ∑ i ∈ ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ := by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  have : (fun i ↦ (ρ i) x₀ • φ i x₀) = (fun i ↦ (ρ i) x₀) • (fun i ↦ φ i x₀) :=
    funext fun _ => (Pi.smul_apply' _ _ _).symm
  rw [ρ.coe_finsupport x₀, this, support_smul]
  exact inter_subset_left

end finsupport

section fintsupport -- partitions of unity have locally finite `tsupport`

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

/-- The `tsupport`s of a partition of unity are locally finite. -/
/-
**PartitionOfUnity.finite_tsupport** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：finite_tsupport : {i | x₀ in tsupport (ρ i)}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty

--- 原说明 ---
The `tsupport`s of a partition of unity are locally finite.
-/
theorem finite_tsupport : {i | x₀ ∈ tsupport (ρ i)}.Finite := by
  rcases ρ.locallyFinite x₀ with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

/-- The tsupport of a partition of unity at a point `x₀` as a `Finset`.
  This is the set of `i : ι` such that `x₀ ∈ tsupport f i`. -/
/-
**PartitionOfUnity.fintsupport** 是 Mathlib 中的一个定义，位于命名空间 `PartitionOfUnity`。
形式化陈述：fintsupport (x₀ : X) : Finset ι
参数：x₀ : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.finite_tsupport`：finite_tsupport : {i | x₀ in tsupport 
(ρ i)}.Finite

--- 原说明 ---
The tsupport of a partition of unity at a point `x₀` as a `Finset`.
  This is the set of `i : ι` such that `x₀ ∈ tsupport f i`.
-/
def fintsupport (x₀ : X) : Finset ι :=
  (ρ.finite_tsupport x₀).toFinset
/-
**PartitionOfUnity.mem_fintsupport_iff** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUni
ty`。
形式化陈述：mem_fintsupport_iff (i : ι) : i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `PartitionOfUnity.finite_tsupport`：finite_tsupport : {i | x₀ in tsupport 
(ρ i)}.Finite
-/
theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x₀ ↔ x₀ ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _
/-
**PartitionOfUnity.eventually_fintsupport_subset** 是 Mathlib 中的一个定理，位于命名空间 `Part
itionOfUnity`。
形式化陈述：eventually_fintsupport_subset : forallᶠ y in 𝓝 x₀, ρ.fintsupport y subsete
q ρ.fintsupport x₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LocallyFinite.eventually_subset`：LocallyFinite.eventually_subset {s : ι 
-> Set X} (hs : LocallyFinite s) (hs' : forall i, IsClosed (s i)) (x : X) : fora
llᶠ y in 𝓝 x, {i | y …
· 使用定理 `LocallyFinite.closure`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologic
alSpace X] {f : ι → Set X},   LocallyFinite f → LocallyFinite fun i => closure (
f i)
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartitionOfUnity.mem_fintsupport_iff`：mem_fintsupport_iff (i : ι) : i in
 ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
-/
theorem eventually_fintsupport_subset :
    ∀ᶠ y in 𝓝 x₀, ρ.fintsupport y ⊆ ρ.fintsupport x₀ := by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ ↦ isClosed_closure) x₀).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz
/-
**PartitionOfUnity.finsupport_subset_fintsupport** 是 Mathlib 中的一个定理，位于命名空间 `Part
itionOfUnity`。
形式化陈述：finsupport_subset_fintsupport : ρ.finsupport x₀ subseteq ρ.fintsupport x₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartitionOfUnity.mem_fintsupport_iff`：mem_fintsupport_iff (i : ι) : i in
 ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PartitionOfUnity.mem_finsupport`：mem_finsupport (x₀ : X) {i} : i in ρ.fi
nsupport x₀ ↔ i in support fun i => ρ i x₀
-/
theorem finsupport_subset_fintsupport : ρ.finsupport x₀ ⊆ ρ.fintsupport x₀ := fun i hi ↦ by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.mem_finsupport x₀).mp hi
/-
**PartitionOfUnity.eventually_finsupport_subset** 是 Mathlib 中的一个定理，位于命名空间 `Parti
tionOfUnity`。
形式化陈述：eventually_finsupport_subset : forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq 
ρ.fintsupport x₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `PartitionOfUnity.eventually_fintsupport_subset`：eventually_fintsupport_s
ubset : forallᶠ y in 𝓝 x₀, ρ.fintsupport y subseteq ρ.fintsupport x₀
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `PartitionOfUnity.finsupport_subset_fintsupport`：finsupport_subset_fintsu
pport : ρ.finsupport x₀ subseteq ρ.fintsupport x₀
-/
theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.finsupport y ⊆ ρ.fintsupport x₀ :=
  (ρ.eventually_fintsupport_subset x₀).mono
    fun y hy ↦ (ρ.finsupport_subset_fintsupport y).trans hy

end fintsupport

/-- If `f` is a partition of unity on `s : Set X` and `g : X → E` is continuous at every point of
the topological support of some `f i`, then `fun x ↦ f i x • g x` is continuous on the whole space.
-/
/-
**PartitionOfUnity.continuous_smul** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：continuous_smul {g : X -> E} {i : ι} (hg : forall x in tsupport (f i), Con
tinuousAt g x) : Continuous fun x => f i x • g x
参数：hg : forall x in tsupport (f i), ContinuousAt g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_tsupport`：∀ {α : Type u_2} {β : Type u_4} [inst : Topologi
calSpace α] [inst_1 : Zero β] [inst_2 : TopologicalSpace β] {f : α → β},   (∀ x 
∈ tsupport f…
· 使用定理 `ContinuousAt.smul`：ContinuousAt.smul (hf : ContinuousAt f b) (hg : Conti
nuousAt g b) : ContinuousAt (f • g) b
· 使用定理 `ContinuousMap.continuousAt`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] (f : C(α, β)) (x : α),   Continuou
sAt (⇑f) x
· 使用定理 `tsupport_smul_subset_left`：tsupport_smul_subset_left {M α} [Zero M] [Zer
o α] [SMulWithZero M α] (f : X -> M) (g : X -> α) : (tsupport fun x => f x • g x
) subseteq tsup…

--- 原说明 ---
If `f` is a partition of unity on `s : Set X` and `g : X → E` is continuous at e
very point of
the topological support of some `f i`, then `fun x ↦ f i x • g x` is continuous 
on the whole space.
-/
theorem continuous_smul {g : X → E} {i : ι} (hg : ∀ x ∈ tsupport (f i), ContinuousAt g x) :
    Continuous fun x => f i x • g x :=
  continuous_of_tsupport fun x hx =>
    ((f i).continuousAt x).smul <| hg x <| tsupport_smul_subset_left _ _ hx

/-- If `f` is a partition of unity on a set `s : Set X` and `g : ι → X → E` is a family of functions
such that each `g i` is continuous at every point of the topological support of `f i`, then the sum
`fun x ↦ ∑ᶠ i, f i x • g i x` is continuous on the whole space. -/
/-
**PartitionOfUnity.continuous_finsum_smul** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOf
Unity`。
形式化陈述：continuous_finsum_smul [ContinuousAdd E] {g : ι -> X -> E} (hg : forall (i
), forall x in tsupport (f i), ContinuousAt (g i) x) : Continuous fun x => ∑ᶠ i,
 f i x • g i x
参数：hg : forall (i), forall x in tsupport (f i), ContinuousAt (g i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_finsum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid M]
 [Conti…
· 使用定理 `PartitionOfUnity.continuous_smul`：continuous_smul {g : X -> E} {i : ι} (
hg : forall x in tsupport (f i), ContinuousAt g x) : Continuous fun x => f i x •
 g x
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f

--- 原说明 ---
If `f` is a partition of unity on a set `s : Set X` and `g : ι → X → E` is a fam
ily of functions
such that each `g i` is continuous at every point of the topological support of 
`f i`, then the sum
`fun x ↦ ∑ᶠ i, f i x • g i x` is continuous on the whole space.
-/
theorem continuous_finsum_smul [ContinuousAdd E] {g : ι → X → E}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), ContinuousAt (g i) x) :
    Continuous fun x => ∑ᶠ i, f i x • g i x :=
  (continuous_finsum fun i => f.continuous_smul (hg i)) <|
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

/-- A partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same type if
for each `i` the closure of the support of `f i` is a subset of `U i`. -/
/-
**PartitionOfUnity.IsSubordinate** 是 Mathlib 中的一个定义，位于命名空间 `PartitionOfUnity`。
形式化陈述：IsSubordinate (U : ι -> Set X) : Prop
参数：U : ι -> Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partition of unity `f i` is subordinate to a family of sets `U i` indexed by t
he same type if
for each `i` the closure of the support of `f i` is a subset of `U i`.
-/
def IsSubordinate (U : ι → Set X) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i

variable {f}
/-
**PartitionOfUnity.exists_finset_nhds'** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUni
ty`。
形式化陈述：exists_finset_nhds' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) : ex
ists I : Finset ι, (forallᶠ x in 𝓝[s] x₀, ∑ i in I, ρ i x = 1) ∧ forallᶠ x in 𝓝 
x₀, support (ρ · x) subseteq I
参数：ρ : PartitionOfUnity ι X s；x₀ : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.exists_finset_support`：∀ {ι : Type u_1} {X : Type u_5} [in
st : TopologicalSpace X] {M : Type u_6} [inst_1 : Zero M] {f : ι → X → M},   (Lo
callyFinite fun i => Func…
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartitionOfUnity.sum_eq_one`：sum_eq_one {x : X} (hx : x in s) : ∑ᶠ i, f 
i x = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem exists_finset_nhds' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    ∃ I : Finset ι, (∀ᶠ x in 𝓝[s] x₀, ∑ i ∈ I, ρ i x = 1) ∧
      ∀ᶠ x in 𝓝 x₀, support (ρ · x) ⊆ I := by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine ⟨I, eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in ↦ ?_), hI⟩
  have : ∑ᶠ i : ι, ρ i x = ∑ i ∈ I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this
/-
**PartitionOfUnity.exists_finset_nhds** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUnit
y`。
形式化陈述：exists_finset_nhds (ρ : PartitionOfUnity ι X univ) (x₀ : X) : exists I : F
inset ι, forallᶠ x in 𝓝 x₀, ∑ i in I, ρ i x = 1 ∧ support (ρ · x) subseteq I
参数：ρ : PartitionOfUnity ι X univ；x₀ : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.exists_finset_nhds'`：exists_finset_nhds' {s : Set X} (ρ
 : PartitionOfUnity ι X s) (x₀ : X) : exists I : Finset ι, (forallᶠ x in 𝓝[s] x₀
, ∑ i in I, ρ i x = 1) ∧ f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_and`：eventually_and {p q : α -> Prop} {f : Filter α} :
 (forallᶠ x in f, p x ∧ q x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in f, q x
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem exists_finset_nhds (ρ : PartitionOfUnity ι X univ) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i ∈ I, ρ i x = 1 ∧ support (ρ · x) ⊆ I := by
  rcases ρ.exists_finset_nhds' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H
/-
**PartitionOfUnity.exists_finset_nhds_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `
PartitionOfUnity`。
形式化陈述：exists_finset_nhds_support_subset {U : ι -> Set X} (hso : f.IsSubordinate 
U) (ho : forall i, IsOpen (U i)) (x : X) : exists is : Finset ι, exists n in 𝓝 x
, n subseteq ⋂ i in is, U i ∧ forall z in n, (support (f · z)) subseteq is
参数：hso : f.IsSubordinate U；ho : forall i, IsOpen (U i)；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.exists_finset_nhds_support_subset`：∀ {X : Type u_1} {R : T
ype u_8} {ι : Type u_9} [inst : TopologicalSpace X] {U : ι → Set X} [inst_1 : Ze
ro R]   {f : ι → X → R},   (LocallyFi…
· 使用定理 `PartitionOfUnity.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topo
logicalSpace X] {s : Set X} (f : PartitionOfUnity ι X s),   LocallyFinite fun i 
=> Function.support …
-/
theorem exists_finset_nhds_support_subset {U : ι → Set X} (hso : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ is : Finset ι, ∃ n ∈ 𝓝 x, n ⊆ ⋂ i ∈ is, U i ∧ ∀ z ∈ n, (support (f · z)) ⊆ is :=
  f.locallyFinite.exists_finset_nhds_support_subset hso ho x

/-- If `f` is a partition of unity that is subordinate to a family of open sets `U i` and
`g : ι → X → E` is a family of functions such that each `g i` is continuous on `U i`, then the sum
`fun x ↦ ∑ᶠ i, f i x • g i x` is a continuous function. -/
/-
**PartitionOfUnity.IsSubordinate.continuous_finsum_smul** 是 Mathlib 中的一个定理，位于命名空
间 `PartitionOfUnity.IsSubordinate`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {E : Type u_1} [in
st_1 : AddCommMonoid E]   [inst_2 : SMulWithZero ℝ E] [inst_3 : TopologicalSpace
 E] [ContinuousSMul ℝ E] {s : Set X}   {f : PartitionOfUnity ι X s} [ContinuousA
dd E] {U : ι → Set X},   (∀ (i : ι), IsOpen (U i)) →     f.IsSubordinate U →    
   ∀ {g : ι → X → E}, (∀ (i : ι), ContinuousOn (g i) (U i)) → Continuous fun x =
> ∑ᶠ (i : ι), (f i) x • g i x
参数：∀ (i : ι), IsOpen (U i)；∀ (i : ι), ContinuousOn (g i) (U i)；i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.continuous_finsum_smul`：continuous_finsum_smul [Continu
ousAdd E] {g : ι -> X -> E} (hg : forall (i), forall x in tsupport (f i), Contin
uousAt (g i) x) : Continuous …
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If `f` is a partition of unity that is subordinate to a family of open sets `U i
` and
`g : ι → X → E` is a family of functions such that each `g i` is continuous on `
U i`, then the sum
`fun x ↦ ∑ᶠ i, f i x • g i x` is a continuous function.
-/
theorem IsSubordinate.continuous_finsum_smul [ContinuousAdd E] {U : ι → Set X}
    (ho : ∀ i, IsOpen (U i)) (hf : f.IsSubordinate U) {g : ι → X → E}
    (hg : ∀ i, ContinuousOn (g i) (U i)) : Continuous fun x => ∑ᶠ i, f i x • g i x :=
  f.continuous_finsum_smul fun i _ hx => (hg i).continuousAt <| (ho i).mem_nhds <| hf i hx

end PartitionOfUnity

namespace BumpCovering

variable {s : Set X} (f : BumpCovering ι X s)

/-
**BumpCovering.** 是 Mathlib 中的一个实例，位于命名空间 `BumpCovering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (BumpCovering ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**BumpCovering.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {s : Set X} (f : B
umpCovering ι X s), f.toFun = ⇑f
参数：f : BumpCovering ι X s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFun_eq_coe : f.toFun = f := rfl
/-
**BumpCovering.locallyFinite** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {s : Set X} (f : B
umpCovering ι X s),   LocallyFinite fun i => Function.support ⇑(f i)
参数：f : BumpCovering ι X s；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.locallyFinite'`：∀ {ι : Type u_1} {X : Type u_2} [inst : Top
ologicalSpace X] {s : optParam (Set X) Set.univ} (self : BumpCovering ι X s),   
LocallyFinite fun…
-/
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'
/-
**BumpCovering.locallyFinite_tsupport** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.closure`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologic
alSpace X] {f : ι → Set X},   LocallyFinite f → LocallyFinite fun i => closure (
f i)
· 使用定理 `BumpCovering.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topologi
calSpace X] {s : Set X} (f : BumpCovering ι X s),   LocallyFinite fun i => Funct
ion.support ⇑(f …
-/
theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure
/-
**BumpCovering.point_finite** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {s : Set X} (f : B
umpCovering ι X s) (x : X),   {i | (f i) x ≠ 0}.Finite
参数：f : BumpCovering ι X s；x : X；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite
· 使用定理 `BumpCovering.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topologi
calSpace X] {s : Set X} (f : BumpCovering ι X s),   LocallyFinite fun i => Funct
ion.support ⇑(f …
-/
protected theorem point_finite (x : X) : { i | f i x ≠ 0 }.Finite :=
  f.locallyFinite.point_finite x
/-
**BumpCovering.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：nonneg (i : ι) (x : X) : 0 <= f i x
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.nonneg'`：∀ {ι : Type u_1} {X : Type u_2} [inst : Topologica
lSpace X] {s : optParam (Set X) Set.univ} (self : BumpCovering ι X s),   0 ≤ sel
f.toFun
-/
theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x
/-
**BumpCovering.le_one** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：le_one (i : ι) (x : X) : f i x <= 1
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.le_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : Topologica
lSpace X] {s : optParam (Set X) Set.univ} (self : BumpCovering ι X s),   self.to
Fun ≤ 1
-/
theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  f.le_one' i x

open scoped Classical in
/-- A `BumpCovering` that consists of a single function, uniformly equal to one, defined as an
/-
**BumpCovering.for** 是 Mathlib 中的一个示例，位于命名空间 `BumpCovering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example for `Inhabited` instance. -/
/-
**BumpCovering.single** 是 Mathlib 中的一个定义，位于命名空间 `BumpCovering`。
形式化陈述：{ι : Type u} → {X : Type v} → [inst : TopologicalSpace X] → ι → (s : Set X
) → BumpCovering ι X s
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `BumpCovering` that consists of a single function, uniformly equal to one, def
ined as an
example for `Inhabited` instance.
-/
protected def single (i : ι) (s : Set X) : BumpCovering ι X s where
  toFun := Pi.single i 1
  locallyFinite' x := by
    refine ⟨univ, univ_mem, (finite_singleton i).subset ?_⟩
    rintro j ⟨x, hx, -⟩
    contrapose! hx
    rw [mem_singleton_iff] at hx
    simp [hx]
  nonneg' := le_update_iff.2 ⟨fun _ => zero_le_one, fun _ _ => le_rfl⟩
  le_one' := update_le_iff.2 ⟨le_rfl, fun _ _ _ => zero_le_one⟩
  eventuallyEq_one' x _ := ⟨i, by rw [Pi.single_eq_same, ContinuousMap.coe_one]⟩

open scoped Classical in
@[simp]
/-
**BumpCovering.coe_single** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：coe_single (i : ι) (s : Set X) : ⇑(BumpCovering.single i s) = Pi.single i 
1
参数：i : ι；s : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_single (i : ι) (s : Set X) : ⇑(BumpCovering.single i s) = Pi.single i 1 := by
  rfl
/-
**BumpCovering.** 是 Mathlib 中的一个实例，位于命名空间 `BumpCovering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited ι] : Inhabited (BumpCovering ι X s) :=
  ⟨BumpCovering.single default s⟩

/-- A collection of bump functions `f i` is subordinate to a family of sets `U i` indexed by the
same type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
/-
**BumpCovering.IsSubordinate** 是 Mathlib 中的一个定义，位于命名空间 `BumpCovering`。
形式化陈述：IsSubordinate (f : BumpCovering ι X s) (U : ι -> Set X) : Prop
参数：f : BumpCovering ι X s；U : ι -> Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A collection of bump functions `f i` is subordinate to a family of sets `U i` in
dexed by the
same type if for each `i` the closure of the support of `f i` is a subset of `U 
i`.
-/
def IsSubordinate (f : BumpCovering ι X s) (U : ι → Set X) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i
/-
**BumpCovering.IsSubordinate.mono** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering.IsSubo
rdinate`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {s : Set X} {f : B
umpCovering ι X s} {U V : ι → Set X},   f.IsSubordinate U → (∀ (i : ι), U i ⊆ V 
i) → f.IsSubordinate V
参数：∀ (i : ι), U i ⊆ V i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem IsSubordinate.mono {f : BumpCovering ι X s} {U V : ι → Set X} (hU : f.IsSubordinate U)
    (hV : ∀ i, U i ⊆ V i) : f.IsSubordinate V :=
  fun i => Subset.trans (hU i) (hV i)

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. This version assumes that `p : (X → ℝ) → Prop` is a predicate
that satisfies Urysohn's lemma, and provides a `BumpCovering` such that each function of the
covering satisfies `p`. -/
/-
**BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop** 是 Mathlib 中的一个定理，
位于命名空间 `BumpCovering`。
形式化陈述：exists_isSubordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X -> R
eal) -> Prop) (h01 : forall s t, IsClosed s -> IsClosed t -> Disjoint s t -> exi
sts f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Re
al) 1) (hs : IsClosed s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : Lo
callyFinite U) (hU : s subseteq ⋃ i, U i) : exists f : BumpCovering ι X s, (fora
ll i, p (f i)) ∧ f.IsSubordinate U
参数：p : (X -> Real) -> Prop；h01 : forall s t, IsClosed s -> IsClosed t -> Disjoin
t s t -> exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in
 Icc (0 : Real) 1；hs : IsClosed s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hf 
: LocallyFinite U；hU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closure_subset`：exists_subset_iUnion_closure_subset
 (hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in
 u i }.Finite) (us : s su…
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite ope
n covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to 
`U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, se
e
`BumpCovering.exists_isSubordinate`. This version assumes that `p : (X → ℝ) → Pr
op` is a predicate
that satisfies Urysohn's lemma, and provides a `BumpCovering` such that each fun
ction of the
covering satisfies `p`.
-/
theorem exists_isSubordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X → ℝ) → Prop)
    (h01 : ∀ s t, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases exists_subset_iUnion_closure_subset hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU⟩
  have hVU' : ∀ i, V i ⊆ U i := fun i => Subset.trans subset_closure (hVU i)
  rcases exists_subset_iUnion_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x)
      hsV with
    ⟨W, hsW, hWo, hWV⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) isClosed_closure
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp : ∀ i, support (f i) ⊆ V i := fun i => support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. -/
/-
**BumpCovering.exists_isSubordinate_of_locallyFinite** 是 Mathlib 中的一个定理，位于命名空间 `
BumpCovering`。
形式化陈述：exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U
 : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s subs
eteq ⋃ i, U i) : exists f : BumpCovering ι X s, f.IsSubordinate U
参数：hs : IsClosed s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hf : LocallyFinite
 U；hU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop`：exists_isSub
ordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X -> Real) -> Prop) (h01
 : forall s t, IsClosed s -> IsClosed t -> Disjo…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `trivial`：True
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…

--- 原说明 ---
If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite ope
n covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to 
`U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, se
e
`BumpCovering.exists_isSubordinate`.
-/
theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, f.IsSubordinate U :=
  let ⟨f, _, hfU⟩ :=
    exists_isSubordinate_of_locallyFinite_of_prop (fun _ => True)
      (fun _ _ hs ht hd =>
        (exists_continuous_zero_one_of_isClosed hs ht hd).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU
  ⟨f, hfU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. This version assumes that
`p : (X → ℝ) → Prop` is a predicate that satisfies Urysohn's lemma, and provides a
`BumpCovering` such that each function of the covering satisfies `p`. -/
/-
**BumpCovering.exists_isSubordinate_of_prop** 是 Mathlib 中的一个定理，位于命名空间 `BumpCover
ing`。
形式化陈述：exists_isSubordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X 
-> Real) -> Prop) (h01 : forall s t, IsClosed s -> IsClosed t -> Disjoint s t ->
 exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 
: Real) 1) (hs : IsClosed s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hU 
: s subseteq ⋃ i, U i) : exists f : BumpCovering ι X s, (forall i, p (f i)) ∧ f.
IsSubordinate U
参数：p : (X -> Real) -> Prop；h01 : forall s t, IsClosed s -> IsClosed t -> Disjoin
t s t -> exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in
 Icc (0 : Real) 1；hs : IsClosed s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hU 
: s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `precise_refinement_set`：precise_refinement_set [ParacompactSpace X] {s :
 Set X} (hs : IsClosed s) (u : ι -> Set X) (uo : forall i, IsOpen (u i)) (us : s
 subseteq ⋃ …
· 使用定理 `BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop`：exists_isSub
ordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X -> Real) -> Prop) (h01
 : forall s t, IsClosed s -> IsClosed t -> Disjo…
· 使用定理 `BumpCovering.IsSubordinate.mono`：∀ {ι : Type u} {X : Type v} [inst : Top
ologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U V : ι → Set X},   f.IsS
ubordinate U → (∀ (i …

--- 原说明 ---
If `X` is a paracompact normal topological space and `U` is an open covering of 
a closed set
`s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. This v
ersion assumes that
`p : (X → ℝ) → Prop` is a predicate that satisfies Urysohn's lemma, and provides
 a
`BumpCovering` such that each function of the covering satisfies `p`.
-/
theorem exists_isSubordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X → ℝ) → Prop)
    (h01 : ∀ s t, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. -/
/-
**BumpCovering.exists_isSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s
) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hU : s subseteq ⋃ i, U i) : ex
ists f : BumpCovering ι X s, f.IsSubordinate U
参数：hs : IsClosed s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hU : s subseteq ⋃ 
i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `precise_refinement_set`：precise_refinement_set [ParacompactSpace X] {s :
 Set X} (hs : IsClosed s) (u : ι -> Set X) (uo : forall i, IsOpen (u i)) (us : s
 subseteq ⋃ …
· 使用定理 `BumpCovering.exists_isSubordinate_of_locallyFinite`：exists_isSubordinate
_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι -> Set X) (ho : foral
l i, IsOpen (U i)) (hf : LocallyFinite U…
· 使用定理 `BumpCovering.IsSubordinate.mono`：∀ {ι : Type u} {X : Type v} [inst : Top
ologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U V : ι → Set X},   f.IsS
ubordinate U → (∀ (i …

--- 原说明 ---
If `X` is a paracompact normal topological space and `U` is an open covering of 
a closed set
`s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`.
-/
theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

/-- If `X` is a locally compact T2 topological space and `U i`, `i : ι`, is a locally finite open
covering of a compact set `s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`.
If `X` is a paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. This version assumes that `p : (X → ℝ) → Prop` is a predicate
that satisfies Urysohn's lemma, and provides a `BumpCovering` such that each function of the
covering satisfies `p`. -/
/-
**BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop_t2space** 是 Mathlib
 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：exists_isSubordinate_of_locallyFinite_of_prop_t2space [LocallyCompactSpace
 X] [T2Space X] (p : (X -> Real) -> Prop) (h01 : forall s t, IsClosed s -> IsCom
pact t -> Disjoint s t -> exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧
 forall x, f x in Icc (0 : Real) 1) (hs : IsCompact s) (U : ι -> Set X) (ho : fo
rall i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s subseteq ⋃ i, U i) : exists
 f : BumpCovering ι X s, (forall i, p (f i)) ∧ f.IsSubordinate U ∧ forall i, Has
CompactSupport (f i)
参数：p : (X -> Real) -> Prop；h01 : forall s t, IsClosed s -> IsCompact t -> Disjoi
nt s t -> exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x i
n Icc (0 : Real) 1；hs : IsCompact s；U : ι -> Set X；ho : forall i, IsOpen (U i)；h
f : LocallyFinite U；hU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closure_subset_t2space`：exists_subset_iUnion_closur
e_subset_t2space (hs : IsCompact s) (uo : forall i, IsOpen (u i)) (uf : forall x
 in s, { i | x in u i }.Finite) (…
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `X` is a locally compact T2 topological space and `U i`, `i : ι`, is a locall
y finite open
covering of a compact set `s`, then there exists a `BumpCovering ι X s` that is 
subordinate to `U`.
If `X` is a paracompact space, then the assumption `hf : LocallyFinite U` can be
 omitted, see
`BumpCovering.exists_isSubordinate`. This version assumes that `p : (X → ℝ) → Pr
op` is a predicate
that satisfies Urysohn's lemma, and provides a `BumpCovering` such that each fun
ction of the
covering satisfies `p`.
-/
theorem exists_isSubordinate_of_locallyFinite_of_prop_t2space [LocallyCompactSpace X] [T2Space X]
    (p : (X → ℝ) → Prop) (h01 : ∀ s t, IsClosed s → IsCompact t → Disjoint s t → ∃ f : C(X, ℝ),
    p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsCompact s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U ∧
      ∀ i, HasCompactSupport (f i) := by
  rcases exists_subset_iUnion_closure_subset_t2space hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU, hcp⟩
  have hVU' i : V i ⊆ U i := subset_closure.trans (hVU i)
  rcases exists_subset_iUnion_closure_subset_t2space hs hVo
    (fun x _ => (hf.subset hVU').point_finite x) hsV with ⟨W, hsW, hWo, hWV, hWc⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) (hWc i)
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp i : support (f i) ⊆ V i := support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i),
    fun i => IsCompact.of_isClosed_subset (hcp i) isClosed_closure <| closure_mono (hsupp i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. -/
/-
**BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space**
 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space [LocallyCo
mpactSpace X] [T2Space X] (hs : IsCompact s) (U : ι -> Set X) (ho : forall i, Is
Open (U i)) (hf : LocallyFinite U) (hU : s subseteq ⋃ i, U i) : exists f : BumpC
overing ι X s, f.IsSubordinate U ∧ forall i, HasCompactSupport (f i)
参数：hs : IsCompact s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hf : LocallyFinit
e U；hU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop_t2space`：exis
ts_isSubordinate_of_locallyFinite_of_prop_t2space [LocallyCompactSpace X] [T2Spa
ce X] (p : (X -> Real) -> Prop) (h01 : forall s t, IsClo…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `trivial`：True
· 使用定理 `exists_continuous_zero_one_of_isCompact'`：exists_continuous_zero_one_of_
isCompact' [RegularSpace X] [LocallyCompactSpace X] {s t : Set X} (hs : IsCompac
t s) (ht : IsClosed t) (hd : D…
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x

--- 原说明 ---
If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite ope
n covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to 
`U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, se
e
`BumpCovering.exists_isSubordinate`.
-/
theorem exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space [LocallyCompactSpace X]
    [T2Space X]
    (hs : IsCompact s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, f.IsSubordinate U ∧ ∀ i, HasCompactSupport (f i) := by
  -- need to switch 0 and 1 in `exists_continuous_zero_one_of_isCompact`
  simpa using
    exists_isSubordinate_of_locallyFinite_of_prop_t2space (fun _ => True)
      (fun _ _ ht hs hd =>
        (exists_continuous_zero_one_of_isCompact' hs ht hd.symm).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU

/-- Index of a bump function such that `f i =ᶠ[𝓝 x] 1`. -/
/-
**BumpCovering.ind** 是 Mathlib 中的一个定义，位于命名空间 `BumpCovering`。
形式化陈述：ind (x : X) (hx : x in s) : ι
参数：x : X；hx : x in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.eventuallyEq_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace X] {s : optParam (Set X) Set.univ} (self : BumpCovering ι X s),
   ∀ x ∈ s, ∃ i, ⇑(s…

--- 原说明 ---
Index of a bump function such that `f i =ᶠ[𝓝 x] 1`.
-/
def ind (x : X) (hx : x ∈ s) : ι :=
  (f.eventuallyEq_one' x hx).choose
/-
**BumpCovering.eventuallyEq_one** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：eventuallyEq_one (x : X) (hx : x in s) : f (f.ind x hx) =ᶠ[𝓝 x] 1
参数：x : X；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `BumpCovering.eventuallyEq_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace X] {s : optParam (Set X) Set.univ} (self : BumpCovering ι X s),
   ∀ x ∈ s, ∃ i, ⇑(s…
-/
theorem eventuallyEq_one (x : X) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
  (f.eventuallyEq_one' x hx).choose_spec
/-
**BumpCovering.ind_apply** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：ind_apply (x : X) (hx : x in s) : f (f.ind x hx) x = 1
参数：x : X；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `BumpCovering.eventuallyEq_one`：eventuallyEq_one (x : X) (hx : x in s) : 
f (f.ind x hx) =ᶠ[𝓝 x] 1
-/
theorem ind_apply (x : X) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
  (f.eventuallyEq_one x hx).eq_of_nhds

/-- Partition of unity defined by a `BumpCovering`. We use this auxiliary definition to prove some
properties of the new family of functions before bundling it into a `PartitionOfUnity`. Do not use
this definition, use `BumpCovering.toPartitionOfUnity` instead.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `LinearOrder ι`, we use `WellOrderingRel` instead of `(<)`. -/
/-
**BumpCovering.toPOUFun** 是 Mathlib 中的一个定义，位于命名空间 `BumpCovering`。
形式化陈述：toPOUFun (i : ι) (x : X) : Real
参数：i : ι；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partition of unity defined by a `BumpCovering`. We use this auxiliary definition
 to prove some
properties of the new family of functions before bundling it into a `PartitionOf
Unity`. Do not use
this definition, use `BumpCovering.toPartitionOfUnity` instead.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f
 j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals on
e, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `LinearOrder ι`, we use `WellOrderingRel` instea
d of `(<)`.
-/
def toPOUFun (i : ι) (x : X) : ℝ :=
  f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)
/-
**BumpCovering.toPOUFun_zero_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：toPOUFun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPOUFun i x = 0
参数：h : f i x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BumpCovering.toPOUFun.eq_1`：∀ {ι : Type u} {X : Type v} [inst : Topologi
calSpace X] {s : Set X} (f : BumpCovering ι X s) (i : ι) (x : X),   f.toPOUFun i
 x = (f i) x * ∏…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem toPOUFun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPOUFun i x = 0 := by
  rw [toPOUFun, h, zero_mul]
/-
**BumpCovering.support_toPOUFun_subset** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：support_toPOUFun_subset (i : ι) : support (f.toPOUFun i) subseteq support 
(f i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `BumpCovering.toPOUFun_zero_of_zero`：toPOUFun_zero_of_zero {i : ι} {x : X
} (h : f i x = 0) : f.toPOUFun i x = 0
-/
theorem support_toPOUFun_subset (i : ι) : support (f.toPOUFun i) ⊆ support (f i) :=
  fun _ => mt <| f.toPOUFun_zero_of_zero

open scoped Classical in
/-
**BumpCovering.toPOUFun_eq_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：toPOUFun_eq_mul_prod (i : ι) (x : X) (t : Finset ι) (ht : forall j, WellOr
deringRel j i -> f j x != 0 -> j in t) : f.toPOUFun i x = f i x * ∏ j in t with 
WellOrderingRel j i, (1 - f j x)
参数：i : ι；x : X；t : Finset ι；ht : forall j, WellOrderingRel j i -> f j x != 0 -> 
j in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `finprod_cond_eq_prod_of_cond_iff`：finprod_cond_eq_prod_of_cond_iff (f : 
α -> M) {p : α -> Prop} {t : Finset α} (h : forall {x}, f x != 1 -> (p x ↔ x in 
t)) : (∏ᶠ (i) (_ : p i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
-/
theorem toPOUFun_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPOUFun i x = f i x * ∏ j ∈ t with WellOrderingRel j i, (1 - f j x) := by
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun {j} hj => ?_)
  rw [Ne, sub_eq_self] at hj
  rw [Finset.mem_filter, Iff.comm, and_iff_right_iff_imp]
  exact flip (ht j) hj
/-
**BumpCovering.sum_toPOUFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：sum_toPOUFun_eq (x : X) : ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.point_finite`：∀ {ι : Type u} {X : Type v} [inst : Topologic
alSpace X] {s : Set X} (f : BumpCovering ι X s) (x : X),   {i | (f i) x ≠ 0}.Fin
ite
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BumpCovering.support_toPOUFun_subset`：support_toPOUFun_subset (i : ι) : 
support (f.toPOUFun i) subseteq support (f i)
· 使用引理 `Function.mulSupport_one_sub`：mulSupport_one_sub [AddGroup R] (f : ι -> R
) : mulSupport (fun x => 1 - f x) = support f
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `Finset.prod_one_sub_ordered`：prod_one_sub_ordered [LinearOrder ι] (s : F
inset ι) (f : ι -> R) : ∏ i in s, (1 - f i) = 1 - ∑ i in s, f i * ∏ j in s with 
j < i, (1 - f j)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BumpCovering.toPOUFun_eq_mul_prod`：toPOUFun_eq_mul_prod (i : ι) (x : X) 
(t : Finset ι) (ht : forall j, WellOrderingRel j i -> f j x != 0 -> j in t) : f.
toPOUFun i x = f i x * …
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem sum_toPOUFun_eq (x : X) : ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x) := by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x ≠ 0 } := Finite.coe_toFinset _
  have A : (support fun i => toPOUFun f i x) ⊆ s := by
    rw [hs]
    exact fun i hi => f.support_toPOUFun_subset i hi
  have B : (mulSupport fun i => 1 - f i x) ⊆ s := by
    rw [hs, mulSupport_one_sub]
    exact fun i => id
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mulSupport_subset _ B,
    Finset.prod_one_sub_ordered, sub_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  convert! f.toPOUFun_eq_mul_prod _ _ _ fun j _ hj => _
  rwa [Finite.mem_toFinset]

open scoped Classical in
/-
**BumpCovering.exists_finset_toPOUFun_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Bu
mpCovering`。
形式化陈述：exists_finset_toPOUFun_eventuallyEq (i : ι) (x : X) : exists t : Finset ι,
 f.toPOUFun i =ᶠ[𝓝 x] f i * ∏ j in t with WellOrderingRel j i, (1 - f j)
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `BumpCovering.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topologi
calSpace X] {s : Set X} (f : BumpCovering ι X s),   LocallyFinite fun i => Funct
ion.support ⇑(f …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMap.coe_prod`：coe_prod [CommMonoid β] [ContinuousMul β] {ι : T
ype*} (s : Finset ι) (f : ι -> C(α, β)) : ⇑(∏ i in s, f i) = ∏ i in s, (f i : α 
-> β)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `BumpCovering.toPOUFun_eq_mul_prod`：toPOUFun_eq_mul_prod (i : ι) (x : X) 
(t : Finset ι) (ht : forall j, WellOrderingRel j i -> f j x != 0 -> j in t) : f.
toPOUFun i x = f i x * …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem exists_finset_toPOUFun_eventuallyEq (i : ι) (x : X) : ∃ t : Finset ι,
    f.toPOUFun i =ᶠ[𝓝 x] f i * ∏ j ∈ t with WellOrderingRel j i, (1 - f j) := by
  rcases f.locallyFinite x with ⟨U, hU, hf⟩
  use hf.toFinset
  filter_upwards [hU] with y hyU
  simp only [ContinuousMap.coe_prod, Pi.mul_apply, Finset.prod_apply]
  apply toPOUFun_eq_mul_prod
  intro j _ hj
  exact hf.mem_toFinset.2 ⟨y, ⟨hj, hyU⟩⟩
/-
**BumpCovering.continuous_toPOUFun** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`。
形式化陈述：continuous_toPOUFun (i : ι) : Continuous (f.toPOUFun i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `continuous_finprod_cond`：continuous_finprod_cond {f : ι -> X -> M} {p : 
ι -> Prop} (hc : forall i, p i -> Continuous (f i)) (hf : LocallyFinite fun i =>
 mulSupport (…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.mulSupport_one_sub`：mulSupport_one_sub [AddGroup R] (f : ι -> R
) : mulSupport (fun x => 1 - f x) = support f
· 使用定理 `BumpCovering.locallyFinite`：∀ {ι : Type u} {X : Type v} [inst : Topologi
calSpace X] {s : Set X} (f : BumpCovering ι X s),   LocallyFinite fun i => Funct
ion.support ⇑(f …
-/
theorem continuous_toPOUFun (i : ι) : Continuous (f.toPOUFun i) := by
  refine (map_continuous <| f i).mul <| continuous_finprod_cond (fun j _ => by fun_prop) ?_
  simp only [mulSupport_one_sub]
  exact f.locallyFinite

/-- The partition of unity defined by a `BumpCovering`.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `LinearOrder ι`, we use `WellOrderingRel` instead of `(<)`. -/
/-
**BumpCovering.toPartitionOfUnity** 是 Mathlib 中的一个定义，位于命名空间 `BumpCovering`。
形式化陈述：toPartitionOfUnity : PartitionOfUnity ι X s where toFun i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.continuous_toPOUFun`：continuous_toPOUFun (i : ι) : Continuo
us (f.toPOUFun i)

--- 原说明 ---
The partition of unity defined by a `BumpCovering`.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f
 j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals on
e, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `LinearOrder ι`, we use `WellOrderingRel` instea
d of `(<)`.
-/
def toPartitionOfUnity : PartitionOfUnity ι X s where
  toFun i := ⟨f.toPOUFun i, f.continuous_toPOUFun i⟩
  locallyFinite' := f.locallyFinite.subset f.support_toPOUFun_subset
  nonneg' i x :=
    mul_nonneg (f.nonneg i x) (finprod_cond_nonneg fun j _ => sub_nonneg.2 <| f.le_one j x)
  sum_eq_one' x hx := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub_eq_self]
    apply finprod_eq_zero (fun i => 1 - f i x) (f.ind x hx)
    · simp only [f.ind_apply x hx, sub_self]
    · rw [HasFiniteMulSupport, mulSupport_one_sub]
      exact f.point_finite x
  sum_le_one' x := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub_le_self_iff]
    exact finprod_nonneg fun i => sub_nonneg.2 <| f.le_one i x
/-
**BumpCovering.toPartitionOfUnity_apply** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering`
。
形式化陈述：toPartitionOfUnity_apply (i : ι) (x : X) : f.toPartitionOfUnity i x = f i 
x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartitionOfUnity_apply (i : ι) (x : X) :
    f.toPartitionOfUnity i x = f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x) := rfl

open scoped Classical in
/-
**BumpCovering.toPartitionOfUnity_eq_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `BumpCov
ering`。
形式化陈述：toPartitionOfUnity_eq_mul_prod (i : ι) (x : X) (t : Finset ι) (ht : forall
 j, WellOrderingRel j i -> f j x != 0 -> j in t) : f.toPartitionOfUnity i x = f 
i x * ∏ j in t with WellOrderingRel j i, (1 - f j x)
参数：i : ι；x : X；t : Finset ι；ht : forall j, WellOrderingRel j i -> f j x != 0 -> 
j in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.toPOUFun_eq_mul_prod`：toPOUFun_eq_mul_prod (i : ι) (x : X) 
(t : Finset ι) (ht : forall j, WellOrderingRel j i -> f j x != 0 -> j in t) : f.
toPOUFun i x = f i x * …
-/
theorem toPartitionOfUnity_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPartitionOfUnity i x = f i x * ∏ j ∈ t with WellOrderingRel j i, (1 - f j x) :=
  f.toPOUFun_eq_mul_prod i x t ht

open scoped Classical in
/-
**BumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq** 是 Mathlib 中的一个定理，
位于命名空间 `BumpCovering`。
形式化陈述：exists_finset_toPartitionOfUnity_eventuallyEq (i : ι) (x : X) : exists t :
 Finset ι, f.toPartitionOfUnity i =ᶠ[𝓝 x] f i * ∏ j in t with WellOrderingRel j 
i, (1 - f j)
参数：i : ι；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.exists_finset_toPOUFun_eventuallyEq`：exists_finset_toPOUFun
_eventuallyEq (i : ι) (x : X) : exists t : Finset ι, f.toPOUFun i =ᶠ[𝓝 x] f i * 
∏ j in t with WellOrderingRel j i, (1 …
-/
theorem exists_finset_toPartitionOfUnity_eventuallyEq (i : ι) (x : X) : ∃ t : Finset ι,
    f.toPartitionOfUnity i =ᶠ[𝓝 x] f i * ∏ j ∈ t with WellOrderingRel j i, (1 - f j) :=
  f.exists_finset_toPOUFun_eventuallyEq i x
/-
**BumpCovering.toPartitionOfUnity_zero_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `BumpCo
vering`。
形式化陈述：toPartitionOfUnity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPart
itionOfUnity i x = 0
参数：h : f i x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.toPOUFun_zero_of_zero`：toPOUFun_zero_of_zero {i : ι} {x : X
} (h : f i x = 0) : f.toPOUFun i x = 0
-/
theorem toPartitionOfUnity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) :
    f.toPartitionOfUnity i x = 0 :=
  f.toPOUFun_zero_of_zero h
/-
**BumpCovering.support_toPartitionOfUnity_subset** 是 Mathlib 中的一个定理，位于命名空间 `Bump
Covering`。
形式化陈述：support_toPartitionOfUnity_subset (i : ι) : support (f.toPartitionOfUnity 
i) subseteq support (f i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.support_toPOUFun_subset`：support_toPOUFun_subset (i : ι) : 
support (f.toPOUFun i) subseteq support (f i)
-/
theorem support_toPartitionOfUnity_subset (i : ι) :
    support (f.toPartitionOfUnity i) ⊆ support (f i) :=
  f.support_toPOUFun_subset i
/-
**BumpCovering.sum_toPartitionOfUnity_eq** 是 Mathlib 中的一个定理，位于命名空间 `BumpCovering
`。
形式化陈述：sum_toPartitionOfUnity_eq (x : X) : ∑ᶠ i, f.toPartitionOfUnity i x = 1 - ∏
ᶠ i, (1 - f i x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.sum_toPOUFun_eq`：sum_toPOUFun_eq (x : X) : ∑ᶠ i, f.toPOUFun
 i x = 1 - ∏ᶠ i, (1 - f i x)
-/
theorem sum_toPartitionOfUnity_eq (x : X) :
    ∑ᶠ i, f.toPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - f i x) :=
  f.sum_toPOUFun_eq x
/-
**BumpCovering.IsSubordinate.toPartitionOfUnity** 是 Mathlib 中的一个定理，位于命名空间 `BumpC
overing.IsSubordinate`。
形式化陈述：∀ {ι : Type u} {X : Type v} [inst : TopologicalSpace X] {s : Set X} {f : B
umpCovering ι X s} {U : ι → Set X},   f.IsSubordinate U → f.toPartitionOfUnity.I
sSubordinate U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `BumpCovering.support_toPartitionOfUnity_subset`：support_toPartitionOfUni
ty_subset (i : ι) : support (f.toPartitionOfUnity i) subseteq support (f i)
-/
theorem IsSubordinate.toPartitionOfUnity {f : BumpCovering ι X s} {U : ι → Set X}
    (h : f.IsSubordinate U) : f.toPartitionOfUnity.IsSubordinate U :=
  fun i => Subset.trans (closure_mono <| f.support_toPartitionOfUnity_subset i) (h i)

end BumpCovering

namespace PartitionOfUnity

variable {s : Set X}

/-
**PartitionOfUnity.** 是 Mathlib 中的一个实例，位于命名空间 `PartitionOfUnity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited ι] : Inhabited (PartitionOfUnity ι X s) :=
  ⟨BumpCovering.toPartitionOfUnity default⟩

/-- If `X` is a normal topological space and `U` is a locally finite open covering of a closed set
`s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. -/
/-
**PartitionOfUnity.exists_isSubordinate_of_locallyFinite** 是 Mathlib 中的一个定理，位于命名
空间 `PartitionOfUnity`。
形式化陈述：exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U
 : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s subs
eteq ⋃ i, U i) : exists f : PartitionOfUnity ι X s, f.IsSubordinate U
参数：hs : IsClosed s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hf : LocallyFinite
 U；hU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.exists_isSubordinate_of_locallyFinite`：exists_isSubordinate
_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι -> Set X) (ho : foral
l i, IsOpen (U i)) (hf : LocallyFinite U…
· 使用定理 `BumpCovering.IsSubordinate.toPartitionOfUnity`：∀ {ι : Type u} {X : Type 
v} [inst : TopologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U : ι → Set
 X},   f.IsSubordinate U → f.toPart…

--- 原说明 ---
If `X` is a normal topological space and `U` is a locally finite open covering o
f a closed set
`s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. If
 `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, se
e
`BumpCovering.exists_isSubordinate`.
-/
theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. -/
/-
**PartitionOfUnity.exists_isSubordinate** 是 Mathlib 中的一个定理，位于命名空间 `PartitionOfUn
ity`。
形式化陈述：exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s
) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hU : s subseteq ⋃ i, U i) : ex
ists f : PartitionOfUnity ι X s, f.IsSubordinate U
参数：hs : IsClosed s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hU : s subseteq ⋃ 
i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.exists_isSubordinate`：exists_isSubordinate [NormalSpace X] 
[ParacompactSpace X] (hs : IsClosed s) (U : ι -> Set X) (ho : forall i, IsOpen (
U i)) (hU : s subseteq …
· 使用定理 `BumpCovering.IsSubordinate.toPartitionOfUnity`：∀ {ι : Type u} {X : Type 
v} [inst : TopologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U : ι → Set
 X},   f.IsSubordinate U → f.toPart…

--- 原说明 ---
If `X` is a paracompact normal topological space and `U` is an open covering of 
a closed set
`s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`.
-/
theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

/-- If `X` is a locally compact T2 topological space and `U` is a locally finite open covering of a
compact set `s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. -/
/-
**PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space** 是 Mathlib 中的一
个定理，位于命名空间 `PartitionOfUnity`。
形式化陈述：exists_isSubordinate_of_locallyFinite_t2space [LocallyCompactSpace X] [T2S
pace X] (hs : IsCompact s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : 
LocallyFinite U) (hU : s subseteq ⋃ i, U i) : exists f : PartitionOfUnity ι X s,
 f.IsSubordinate U ∧ forall i, HasCompactSupport (f i)
参数：hs : IsCompact s；U : ι -> Set X；ho : forall i, IsOpen (U i)；hf : LocallyFinit
e U；hU : s subseteq ⋃ i, U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2s
pace`：exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space [LocallyCo
mpactSpace X] [T2Space X] (hs : IsCompact s) (U : ι -> Set X) (ho …
· 使用定理 `BumpCovering.IsSubordinate.toPartitionOfUnity`：∀ {ι : Type u} {X : Type 
v} [inst : TopologicalSpace X] {s : Set X} {f : BumpCovering ι X s} {U : ι → Set
 X},   f.IsSubordinate U → f.toPart…
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `BumpCovering.support_toPartitionOfUnity_subset`：support_toPartitionOfUni
ty_subset (i : ι) : support (f.toPartitionOfUnity i) subseteq support (f i)

--- 原说明 ---
If `X` is a locally compact T2 topological space and `U` is a locally finite ope
n covering of a
compact set `s`, then there exists a `PartitionOfUnity ι X s` that is subordinat
e to `U`.
-/
theorem exists_isSubordinate_of_locallyFinite_t2space [LocallyCompactSpace X] [T2Space X]
    (hs : IsCompact s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U ∧ ∀ i, HasCompactSupport (f i) :=
  let ⟨f, hfsub, hfcp⟩ :=
    BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space hs U ho hf hU
  ⟨f.toPartitionOfUnity, hfsub.toPartitionOfUnity, fun i => IsCompact.of_isClosed_subset (hfcp i)
    isClosed_closure <| closure_mono (f.support_toPartitionOfUnity_subset i)⟩

end PartitionOfUnity

/-- A variation of **Urysohn's lemma**.

In a locally compact T2 space `X`, for a compact set `t` and a finite family of open sets `{s i}_i`
such that `t ⊆ ⋃ i, s i`, there is a family of compactly supported continuous functions `{f i}_i`
supported in `s i`, `∑ i, f i x = 1` on `t` and `0 ≤ f i x ≤ 1`. -/
/-
**exists_continuous_sum_one_of_isOpen_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_continuous_sum_one_of_isOpen_isCompact [T2Space X] [LocallyCompactS
pace X] {n : Nat} {t : Set X} {s : Fin n -> Set X} (hs : forall (i : Fin n), IsO
pen (s i)) (htcp : IsCompact t) (hst : t subseteq ⋃ i, s i) : exists f : Fin n -
> C(X, Real), (forall (i : Fin n), tsupport (f i) subseteq s i) ∧ EqOn (∑ i, f i
) 1 t ∧ (forall (i : Fin n), forall (x : X), f i x in Icc (0 : Real) 1) ∧ (foral
l (i : Fin n), HasCompactSupport (f i))
参数：hs : forall (i : Fin n), IsOpen (s i)；htcp : IsCompact t；hst : t subseteq ⋃ i
, s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space`：exists_i
sSubordinate_of_locallyFinite_t2space [LocallyCompactSpace X] [T2Space X] (hs : 
IsCompact s) (U : ι -> Set X) (ho : forall i, IsOpen…
· 使用定理 `locallyFinite_of_finite`：locallyFinite_of_finite [Finite ι] (f : ι -> Se
t X) : LocallyFinite f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `PartitionOfUnity.sum_eq_one'`：∀ {ι : Type u_1} {X : Type u_2} [inst : To
pologicalSpace X] {s : optParam (Set X) Set.univ}   (self : PartitionOfUnity ι X
 s), ∀ x ∈ s, ∑ᶠ (…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Fintype.sum_subset`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] {s : Finset ι} {f : ι → M},   (∀ (i : ι), f i ≠ 0 → i 
∈ s) → ∑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `PartitionOfUnity.nonneg`：nonneg (i : ι) (x : X) : 0 <= f i x
· 使用定理 `PartitionOfUnity.le_one`：le_one (i : ι) (x : X) : f i x <= 1

--- 原说明 ---
A variation of **Urysohn's lemma**.

In a locally compact T2 space `X`, for a compact set `t` and a finite family of 
open sets `{s i}_i`
such that `t ⊆ ⋃ i, s i`, there is a family of compactly supported continuous fu
nctions `{f i}_i`
supported in `s i`, `∑ i, f i x = 1` on `t` and `0 ≤ f i x ≤ 1`.
-/
theorem exists_continuous_sum_one_of_isOpen_isCompact [T2Space X] [LocallyCompactSpace X]
    {n : ℕ} {t : Set X} {s : Fin n → Set X} (hs : ∀ (i : Fin n), IsOpen (s i)) (htcp : IsCompact t)
    (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧ EqOn (∑ i, f i) 1 t
      ∧ (∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1)
      ∧ (∀ (i : Fin n), HasCompactSupport (f i)) := by
  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space htcp s
    hs (locallyFinite_of_finite _) hst
  use f
  refine ⟨fun i ↦ hfsub i, ?_, ?_, fun i => hfcp i⟩
  · intro x hx
    simp only [Finset.sum_apply, Pi.one_apply]
    have h := f.sum_eq_one' x hx
    rw [finsum_eq_sum (fun i => (f.toFun i) x)
      (Finite.subset finite_univ (subset_univ (support fun i ↦ (f.toFun i) x)))] at h
    rwa [Fintype.sum_subset (by simp)] at h
  intro i x
  exact ⟨f.nonneg i x, PartitionOfUnity.le_one f i x⟩
