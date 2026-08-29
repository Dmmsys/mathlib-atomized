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

/--
Definition of `PartitionOfUnity` / `PartitionOfUnity` 的定义

English:
structure PartitionOfUnity
  parameters: (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)
  axioms and operations (5):
    - toFun : ι -> C(X, Real)
    - locallyFinite' : LocallyFinite fun i => support (toFun i)
    - nonneg' : 0 <= toFun
    - sum_eq_one' : forall x in s, ∑ᶠ i, toFun i x = 1
    - sum_le_one' : forall x, ∑ᶠ i, toFun i x <= 1

中文:
结构 单位分解
  参数: (ι X : 类型) [拓扑空间 X] (s : 集合 X := univ)
  公理与运算 (5 个):
    - toFun : ι -> C(X, 实数)
    - locallyFinite' : 局部有限 fun i => support (toFun i)
    - nonneg' : 0 <= toFun
    - sum_eq_one' : 对任意 x in s, ∑ᶠ i, toFun i x = 1
    - sum_le_one' : 对任意 x, ∑ᶠ i, toFun i x <= 1
-/
structure PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collection of continuous functions underlying this partition of unity -/
  toFun : ι -> C(X, Real)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 <= toFun
  /-- the functions sum up to one on `s` -/
  sum_eq_one' : forall x in s, ∑ᶠ i, toFun i x = 1
  /-- the functions sum up to at most one, globally -/
  sum_le_one' : forall x, ∑ᶠ i, toFun i x <= 1

/--
Definition of `BumpCovering` / `BumpCovering` 的定义

English:
structure BumpCovering
  parameters: (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)
  axioms and operations (5):
    - toFun : ι -> C(X, Real)
    - locallyFinite' : LocallyFinite fun i => support (toFun i)
    - nonneg' : 0 <= toFun
    - le_one' : toFun <= 1
    - eventuallyEq_one' : forall x in s, exists i, toFun i =ᶠ[𝓝 x] 1

中文:
结构 BumpCovering
  参数: (ι X : 类型) [拓扑空间 X] (s : 集合 X := univ)
  公理与运算 (5 个):
    - toFun : ι -> C(X, 实数)
    - locallyFinite' : 局部有限 fun i => support (toFun i)
    - nonneg' : 0 <= toFun
    - le_one' : toFun <= 1
    - eventuallyEq_one' : 对任意 x in s, 存在 i, toFun i =ᶠ[𝓝 x] 1
-/
structure BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collections of continuous functions underlying this bump covering -/
  toFun : ι -> C(X, Real)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 <= toFun
  /-- the functions are each at most one -/
  le_one' : toFun <= 1
  /-- Each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`. -/
  eventuallyEq_one' : forall x in s, exists i, toFun i =ᶠ[𝓝 x] 1

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

namespace PartitionOfUnity

variable {E : Type*} [AddCommMonoid E] [SMulWithZero Real E] [TopologicalSpace E] [ContinuousSMul Real E]
  {s : Set X} (f : PartitionOfUnity ι X s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (PartitionOfUnity ι X s) ι C(X, Real)
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 :
  签名: 函数状 (单位分解 ι X s) ι C(X, 实数)
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr
-/
instance : FunLike (PartitionOfUnity ι X s) ι C(X, Real) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
theorem `locallyFinite` / 定理 `locallyFinite`

English:
theorem locallyFinite
  statement: LocallyFinite fun i => support (f i)
  proof: f.locallyFinite'

中文:
定理 locallyFinite
  结论: 局部有限 fun i => support (f i)
  证明: f.locallyFinite'
-/
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

/--
theorem `locallyFinite_tsupport` / 定理 `locallyFinite_tsupport`

English:
theorem locallyFinite_tsupport
  statement: LocallyFinite fun i => tsupport (f i)
  proof: f.locallyFinite.closure

中文:
定理 locallyFinite_tsupport
  结论: 局部有限 fun i => tsupport (f i)
  证明: f.locallyFinite.closure

Depends on / 依赖: closure, f.locallyFinite.closure, locallyFinite
-/
theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (i : ι) (x : X)
  statement: 0 <= f i x
  proof: f.nonneg' i x

中文:
定理 nonneg
  条件: (i : ι) (x : X)
  结论: 0 <= f i x
  证明: f.nonneg' i x

Depends on / 依赖: f.nonneg, nonneg
-/
theorem nonneg (i : ι) (x : X) : 0 <= f i x :=
  f.nonneg' i x

/--
theorem `sum_eq_one` / 定理 `sum_eq_one`

English:
theorem sum_eq_one
  given: {x : X} (hx : x in s)
  statement: ∑ᶠ i, f i x = 1
  proof: f.sum_eq_one' x hx

中文:
定理 sum_eq_one
  条件: {x : X} (hx : x in s)
  结论: ∑ᶠ i, f i x = 1
  证明: f.sum_eq_one' x hx

Depends on / 依赖: f.sum_eq_one, sum_eq_one
-/
theorem sum_eq_one {x : X} (hx : x in s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx

/--
theorem `exists_pos` / 定理 `exists_pos`

English:
theorem exists_pos
  given: {x : X} (hx : x in s)
  statement: exists i, 0 < f i x
  proof: by
  have H := f.sum_eq_one hx
  contrapose! H
  simpa only [fun i => (H i).antisymm (f.nonneg i x), finsum_zero] using zero_ne_one

中文:
定理 存在_pos
  条件: {x : X} (hx : x in s)
  结论: 存在 i, 0 < f i x
  证明: by
  have H := f.sum_eq_one hx
  contrapose! H
  simpa only [fun i => (H i).antisymm (f.nonneg i x), finsum_zero] using zero_ne_one

Depends on / 依赖: antisymm, contrapose, f.nonneg, f.sum_eq_one, finsum_zero, nonneg, sum_eq_one, zero_ne_one
-/
theorem exists_pos {x : X} (hx : x in s) : exists i, 0 < f i x := by
  have H := f.sum_eq_one hx
  contrapose! H
  simpa only [fun i => (H i).antisymm (f.nonneg i x), finsum_zero] using zero_ne_one

/--
theorem `sum_le_one` / 定理 `sum_le_one`

English:
theorem sum_le_one
  given: (x : X)
  statement: ∑ᶠ i, f i x <= 1
  proof: f.sum_le_one' x

中文:
定理 sum_le_one
  条件: (x : X)
  结论: ∑ᶠ i, f i x <= 1
  证明: f.sum_le_one' x

Depends on / 依赖: f.sum_le_one, sum_le_one
-/
theorem sum_le_one (x : X) : ∑ᶠ i, f i x <= 1 :=
  f.sum_le_one' x

/--
theorem `sum_nonneg` / 定理 `sum_nonneg`

English:
theorem sum_nonneg
  given: (x : X)
  statement: 0 <= ∑ᶠ i, f i x
  proof: finsum_nonneg fun i => f.nonneg i x

中文:
定理 sum_nonneg
  条件: (x : X)
  结论: 0 <= ∑ᶠ i, f i x
  证明: finsum_nonneg fun i => f.nonneg i x

Depends on / 依赖: f.nonneg, finsum_nonneg, nonneg
-/
theorem sum_nonneg (x : X) : 0 <= ∑ᶠ i, f i x :=
  finsum_nonneg fun i => f.nonneg i x

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: (i : ι) (x : X)
  statement: f i x <= 1
  proof: (single_le_finsum i (f.locallyFinite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

中文:
定理 le_one
  条件: (i : ι) (x : X)
  结论: f i x <= 1
  证明: (single_le_finsum i (f.locallyFinite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

Depends on / 依赖: f.locallyFinite.point_finite, f.nonneg, f.sum_le_one, locallyFinite, nonneg, point_finite, single_le_finsum, sum_le_one
-/
theorem le_one (i : ι) (x : X) : f i x <= 1 :=
  (single_le_finsum i (f.locallyFinite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

section finsupport

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

/--
Definition of `finsupport` / `finsupport` 的定义

English:
definition finsupport
  signature: : Finset ι
  body: (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]

中文:
定义 finsupport
  签名: : 有限集 ι
  定义体: (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]

Depends on / 依赖: locallyFinite, locallyFinite.point_finite, point_finite, toFinset
-/
def finsupport : Finset ι := (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]
/--
theorem `mem_finsupport` / 定理 `mem_finsupport`

English:
theorem mem_finsupport
  given: (x₀ : X) {i}
  proof: by
  simp only [finsupport, mem_support, Finite.mem_toFinset, mem_ofPred_eq]

@[simp]

中文:
定理 mem_finsupport
  条件: (x₀ : X) {i}
  证明: by
  simp only [finsupport, mem_support, Finite.mem_toFinset, mem_ofPred_eq]

@[simp]

Depends on / 依赖: Finite, Finite.mem_toFinset, finsupport, mem_ofPred_eq, mem_support, mem_toFinset
-/
theorem mem_finsupport (x₀ : X) {i} :
    i in ρ.finsupport x₀ ↔ i in support fun i => ρ i x₀ := by
  simp only [finsupport, mem_support, Finite.mem_toFinset, mem_ofPred_eq]

@[simp]
/--
theorem `coe_finsupport` / 定理 `coe_finsupport`

English:
theorem coe_finsupport
  given: (x₀ : X)
  proof: by
  ext
  rw [Finset.mem_coe]; rw [mem_finsupport]

中文:
定理 coe_finsupport
  条件: (x₀ : X)
  证明: by
  ext
  rw [Finset.mem_coe]; rw [mem_finsupport]

Depends on / 依赖: Finset, Finset.mem_coe, mem_coe, mem_finsupport
-/
theorem coe_finsupport (x₀ : X) :
    (ρ.finsupport x₀ : Set ι) = support fun i => ρ i x₀ := by
  ext
  rw [Finset.mem_coe]; rw [mem_finsupport]

variable {x₀ : X}

/--
theorem `sum_finsupport` / 定理 `sum_finsupport`

English:
theorem sum_finsupport
  given: (hx₀ : x₀ in s)
  statement: ∑ i in ρ.finsupport x₀, ρ i x₀ = 1
  proof: by
  rw [← ρ.sum_eq_one hx₀]; rw [finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x₀).superset]

中文:
定理 sum_finsupport
  条件: (hx₀ : x₀ in s)
  结论: ∑ i in ρ.finsupport x₀, ρ i x₀ = 1
  证明: by
  rw [← ρ.sum_eq_one hx₀]; rw [finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x₀).superset]

Depends on / 依赖: coe_finsupport, finsum_eq_sum_of_support_subset, sum_eq_one, superset
-/
theorem sum_finsupport (hx₀ : x₀ in s) : ∑ i in ρ.finsupport x₀, ρ i x₀ = 1 := by
  rw [← ρ.sum_eq_one hx₀]; rw [finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x₀).superset]

/--
theorem `sum_finsupport'` / 定理 `sum_finsupport'`

English:
theorem sum_finsupport'
  given: (hx₀ : x₀ in s) {I : Finset ι} (hI : ρ.finsupport x₀ subseteq I)
  proof: by
  classical
  rw [← Finset.sum_sdiff hI]; rw [ρ.sum_finsupport hx₀]
  suffices ∑ i in I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i in I \ ρ.finsupport x₀, 0 by
    rw [this]; rw [add_eq_right]; rw [Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsu

中文:
定理 sum_finsupport'
  条件: (hx₀ : x₀ in s) {I : 有限集 ι} (hI : ρ.finsupport x₀ subseteq I)
  证明: by
  classical
  rw [← Finset.sum_sdiff hI]; rw [ρ.sum_finsupport hx₀]
  suffices ∑ i in I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i in I \ ρ.finsupport x₀, 0 by
    rw [this]; rw [add_eq_right]; rw [Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsu

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.mem_sdiff, Finset.sum_congr, Finset.sum_const_zero, Finset.sum_sdiff, add_eq_right, classical, finsupport, mem_finsupport, mem_sdiff, mem_support, not_not, sum_congr, sum_const_zero, sum_finsupport, sum_sdiff
-/
theorem sum_finsupport' (hx₀ : x₀ in s) {I : Finset ι} (hI : ρ.finsupport x₀ subseteq I) :
    ∑ i in I, ρ i x₀ = 1 := by
  classical
  rw [← Finset.sum_sdiff hI]; rw [ρ.sum_finsupport hx₀]
  suffices ∑ i in I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i in I \ ρ.finsupport x₀, 0 by
    rw [this]; rw [add_eq_right]; rw [Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsupport, mem_support, Classical.not_not] at hx
  exact hx.2

/--
theorem `sum_finsupport_smul_eq_finsum` / 定理 `sum_finsupport_smul_eq_finsum`

English:
theorem sum_finsupport_smul_eq_finsum
  given: {M : Type*} [AddCommMonoid M] [Module Real M] (φ : ι -> X -> M)
  proof: by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  have : (fun i => (ρ i) x₀ • φ i x₀) = (fun i => (ρ i) x₀) • (fun i => φ i x₀) :=
    funext fun _ => (Pi.smul_apply' _ _ _).symm
  rw [ρ.coe_finsupport x₀]; rw [this]; rw [support_smul]
  exact inter_subset_left

中文:
定理 sum_finsupport_smul_eq_finsum
  条件: {M : 类型} [加法交换幺半群 M] [模 实数 M] (φ : ι -> X -> M)
  证明: by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  have : (fun i => (ρ i) x₀ • φ i x₀) = (fun i => (ρ i) x₀) • (fun i => φ i x₀) :=
    funext fun _ => (Pi.smul_apply' _ _ _).symm
  rw [ρ.coe_finsupport x₀]; rw [this]; rw [support_smul]
  exact inter_subset_left

Depends on / 依赖: Pi.smul_apply, coe_finsupport, finsum_eq_sum_of_support_subset, inter_subset_left, smul_apply, support_smul
-/
theorem sum_finsupport_smul_eq_finsum {M : Type*} [AddCommMonoid M] [Module Real M] (φ : ι -> X -> M) :
    ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ := by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  have : (fun i => (ρ i) x₀ • φ i x₀) = (fun i => (ρ i) x₀) • (fun i => φ i x₀) :=
    funext fun _ => (Pi.smul_apply' _ _ _).symm
  rw [ρ.coe_finsupport x₀]; rw [this]; rw [support_smul]
  exact inter_subset_left

end finsupport

section fintsupport -- partitions of unity have locally finite `tsupport`

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

/--
theorem `finite_tsupport` / 定理 `finite_tsupport`

English:
theorem finite_tsupport
  statement: {i | x₀ in tsupport (ρ i)}.Finite
  proof: by
  rcases ρ.locallyFinite x₀ with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

中文:
定理 finite_tsupport
  结论: {i | x₀ in tsupport (ρ i)}.有限
  证明: by
  rcases ρ.locallyFinite x₀ with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

Depends on / 依赖: ht.subset, inter_comm, locallyFinite, mem_closure_iff_nhds, mem_closure_iff_nhds.mp, subset, t_in
-/
theorem finite_tsupport : {i | x₀ in tsupport (ρ i)}.Finite := by
  rcases ρ.locallyFinite x₀ with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

/--
Definition of `fintsupport` / `fintsupport` 的定义

English:
definition fintsupport
  signature: (x₀ : X)
  body: (ρ.finite_tsupport x₀).toFinset

中文:
定义 fintsupport
  签名: (x₀ : X)
  定义体: (ρ.finite_tsupport x₀).toFinset

Depends on / 依赖: finite_tsupport, toFinset
-/
def fintsupport (x₀ : X) : Finset ι :=
  (ρ.finite_tsupport x₀).toFinset

/--
theorem `mem_fintsupport_iff` / 定理 `mem_fintsupport_iff`

English:
theorem mem_fintsupport_iff
  given: (i : ι)
  statement: i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
  proof: Finite.mem_toFinset _

中文:
定理 mem_fintsupport_iff
  条件: (i : ι)
  结论: i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i)
  证明: Finite.mem_toFinset _

Depends on / 依赖: Finite, Finite.mem_toFinset, mem_toFinset
-/
theorem mem_fintsupport_iff (i : ι) : i in ρ.fintsupport x₀ ↔ x₀ in tsupport (ρ i) :=
  Finite.mem_toFinset _

/--
theorem `eventually_fintsupport_subset` / 定理 `eventually_fintsupport_subset`

English:
theorem eventually_fintsupport_subset
  proof: by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ => isClosed_closure) x₀).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

中文:
定理 eventually_fintsupport_subset
  证明: by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ => isClosed_closure) x₀).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

Depends on / 依赖: PartitionOfUnity, PartitionOfUnity.mem_fintsupport_iff, closure, eventually_subset, isClosed_closure, locallyFinite, locallyFinite.closure.eventually_subset, mem_fintsupport_iff
-/
theorem eventually_fintsupport_subset :
    forallᶠ y in 𝓝 x₀, ρ.fintsupport y subseteq ρ.fintsupport x₀ := by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ => isClosed_closure) x₀).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

/--
theorem `finsupport_subset_fintsupport` / 定理 `finsupport_subset_fintsupport`

English:
theorem finsupport_subset_fintsupport
  statement: ρ.finsupport x₀ subseteq ρ.fintsupport x₀
  proof: fun i hi => by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.mem_finsupport x₀).mp hi

中文:
定理 finsupport_subset_fintsupport
  结论: ρ.finsupport x₀ subseteq ρ.fintsupport x₀
  证明: fun i hi => by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.mem_finsupport x₀).mp hi

Depends on / 依赖: mem_finsupport, mem_fintsupport_iff, subset_closure
-/
theorem finsupport_subset_fintsupport : ρ.finsupport x₀ subseteq ρ.fintsupport x₀ := fun i hi => by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.mem_finsupport x₀).mp hi

/--
theorem `eventually_finsupport_subset` / 定理 `eventually_finsupport_subset`

English:
theorem eventually_finsupport_subset
  statement: forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀
  proof: (ρ.eventually_fintsupport_subset x₀).mono
    fun y hy => (ρ.finsupport_subset_fintsupport y).trans hy

中文:
定理 eventually_finsupport_subset
  结论: 对任意ᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀
  证明: (ρ.eventually_fintsupport_subset x₀).mono
    fun y hy => (ρ.finsupport_subset_fintsupport y).trans hy

Depends on / 依赖: eventually_fintsupport_subset, finsupport_subset_fintsupport
-/
theorem eventually_finsupport_subset : forallᶠ y in 𝓝 x₀, ρ.finsupport y subseteq ρ.fintsupport x₀ :=
  (ρ.eventually_fintsupport_subset x₀).mono
    fun y hy => (ρ.finsupport_subset_fintsupport y).trans hy

end fintsupport

/--
theorem `continuous_smul` / 定理 `continuous_smul`

English:
theorem continuous_smul
  given: {g : X -> E} {i : ι} (hg : forall x in tsupport (f i), ContinuousAt g x)
  proof: continuous_of_tsupport fun x hx =>
((f i).continuousAt x).smul hg x tsupport_smul_subset_left _ _ hx

中文:
定理 continuous_smul
  条件: {g : X -> E} {i : ι} (hg : 对任意 x in tsupport (f i), ContinuousAt g x)
  证明: continuous_of_tsupport fun x hx =>
((f i).continuousAt x).smul hg x tsupport_smul_subset_left _ _ hx

Depends on / 依赖: continuousAt, continuous_of_tsupport, tsupport_smul_subset_left
-/
theorem continuous_smul {g : X -> E} {i : ι} (hg : forall x in tsupport (f i), ContinuousAt g x) :
    Continuous fun x => f i x • g x :=
  continuous_of_tsupport fun x hx =>
((f i).continuousAt x).smul hg x tsupport_smul_subset_left _ _ hx

/--
theorem `continuous_finsum_smul` / 定理 `continuous_finsum_smul`

English:
theorem continuous_finsum_smul
  statement: [ContinuousAdd E] {g : ι -> X -> E}
  proof: (continuous_finsum fun i => f.continuous_smul (hg i))
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

中文:
定理 continuous_finsum_smul
  结论: [连续加法 E] {g : ι -> X -> E}
  证明: (continuous_finsum fun i => f.continuous_smul (hg i))
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

Depends on / 依赖: continuous_finsum, continuous_smul, f.continuous_smul, f.locallyFinite.subset, locallyFinite, subset, support_smul_subset_left
-/
theorem continuous_finsum_smul [ContinuousAdd E] {g : ι -> X -> E}
    (hg : forall (i), forall x in tsupport (f i), ContinuousAt (g i) x) :
    Continuous fun x => ∑ᶠ i, f i x • g i x :=
(continuous_finsum fun i => f.continuous_smul (hg i))
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

/--
Definition of `IsSubordinate` / `IsSubordinate` 的定义

English:
definition IsSubordinate
  signature: (U : ι -> Set X)
  body: forall i, tsupport (f i) subseteq U i

中文:
定义 IsSubordinate
  签名: (U : ι -> 集合 X)
  定义体: forall i, tsupport (f i) subseteq U i

Depends on / 依赖: subseteq, tsupport
-/
def IsSubordinate (U : ι -> Set X) : Prop :=
  forall i, tsupport (f i) subseteq U i

variable {f}

/--
theorem `exists_finset_nhds'` / 定理 `exists_finset_nhds'`

English:
theorem exists_finset_nhds'
  given: {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)
  proof: by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine ⟨I, eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in => ?_), hI⟩
  have : ∑ᶠ i : ι, ρ i x = ∑ i in I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this

中文:
定理 存在_finset_nhds'
  条件: {s : 集合 X} (ρ : 单位分解 ι X s) (x₀ : X)
  证明: by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine ⟨I, eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in => ?_), hI⟩
  have : ∑ᶠ i : ι, ρ i x = ∑ i in I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this

Depends on / 依赖: eq_comm, eventually_nhdsWithin_iff, eventually_nhdsWithin_iff.mpr, exists_finset_support, finsum_eq_sum_of_support_subset, hI.mono, locallyFinite, locallyFinite.exists_finset_support, sum_eq_one, x_in
-/
theorem exists_finset_nhds' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    exists I : Finset ι, (forallᶠ x in 𝓝[s] x₀, ∑ i in I, ρ i x = 1) ∧
      forallᶠ x in 𝓝 x₀, support (ρ · x) subseteq I := by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine ⟨I, eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in => ?_), hI⟩
  have : ∑ᶠ i : ι, ρ i x = ∑ i in I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this

/--
theorem `exists_finset_nhds` / 定理 `exists_finset_nhds`

English:
theorem exists_finset_nhds
  given: (ρ : PartitionOfUnity ι X univ) (x₀ : X)
  proof: by
  rcases ρ.exists_finset_nhds' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H

中文:
定理 存在_finset_nhds
  条件: (ρ : 单位分解 ι X univ) (x₀ : X)
  证明: by
  rcases ρ.exists_finset_nhds' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H

Depends on / 依赖: eventually_and, exists_finset_nhds, nhdsWithin_univ
-/
theorem exists_finset_nhds (ρ : PartitionOfUnity ι X univ) (x₀ : X) :
    exists I : Finset ι, forallᶠ x in 𝓝 x₀, ∑ i in I, ρ i x = 1 ∧ support (ρ · x) subseteq I := by
  rcases ρ.exists_finset_nhds' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H

/--
theorem `exists_finset_nhds_support_subset` / 定理 `exists_finset_nhds_support_subset`

English:
theorem exists_finset_nhds_support_subset
  statement: {U : ι -> Set X} (hso : f.IsSubordinate U)
  proof: f.locallyFinite.exists_finset_nhds_support_subset hso ho x

中文:
定理 存在_finset_nhds_support_subset
  结论: {U : ι -> 集合 X} (hso : f.IsSubordinate U)
  证明: f.locallyFinite.exists_finset_nhds_support_subset hso ho x

Depends on / 依赖: exists_finset_nhds_support_subset, f.locallyFinite.exists_finset_nhds_support_subset, locallyFinite
-/
theorem exists_finset_nhds_support_subset {U : ι -> Set X} (hso : f.IsSubordinate U)
    (ho : forall i, IsOpen (U i)) (x : X) :
    exists is : Finset ι, exists n in 𝓝 x, n subseteq ⋂ i in is, U i ∧ forall z in n, (support (f · z)) subseteq is :=
  f.locallyFinite.exists_finset_nhds_support_subset hso ho x

/--
theorem `IsSubordinate.continuous_finsum_smul` / 定理 `IsSubordinate.continuous_finsum_smul`

English:
theorem IsSubordinate.continuous_finsum_smul
  statement: [ContinuousAdd E] {U : ι -> Set X}
  proof: f.continuous_finsum_smul fun i _ hx => (hg i).continuousAt (ho i).mem_nhds hf i hx

中文:
定理 IsSubordinate.continuous_finsum_smul
  结论: [连续加法 E] {U : ι -> 集合 X}
  证明: f.continuous_finsum_smul fun i _ hx => (hg i).continuousAt (ho i).mem_nhds hf i hx

Depends on / 依赖: continuousAt, continuous_finsum_smul, f.continuous_finsum_smul, mem_nhds
-/
theorem IsSubordinate.continuous_finsum_smul [ContinuousAdd E] {U : ι -> Set X}
    (ho : forall i, IsOpen (U i)) (hf : f.IsSubordinate U) {g : ι -> X -> E}
    (hg : forall i, ContinuousOn (g i) (U i)) : Continuous fun x => ∑ᶠ i, f i x • g i x :=
f.continuous_finsum_smul fun i _ hx => (hg i).continuousAt (ho i).mem_nhds hf i hx

end PartitionOfUnity

namespace BumpCovering

variable {s : Set X} (f : BumpCovering ι X s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (BumpCovering ι X s) ι C(X, Real)
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 :
  签名: 函数状 (BumpCovering ι X s) ι C(X, 实数)
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr
-/
instance : FunLike (BumpCovering ι X s) ι C(X, Real) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  statement: f.toFun = f
  proof: rfl

中文:
引理 toFun_eq_coe
  结论: f.toFun = f
  证明: rfl
-/
@[simp] lemma toFun_eq_coe : f.toFun = f := rfl

/--
theorem `locallyFinite` / 定理 `locallyFinite`

English:
theorem locallyFinite
  statement: LocallyFinite fun i => support (f i)
  proof: f.locallyFinite'

中文:
定理 locallyFinite
  结论: 局部有限 fun i => support (f i)
  证明: f.locallyFinite'
-/
protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

/--
theorem `locallyFinite_tsupport` / 定理 `locallyFinite_tsupport`

English:
theorem locallyFinite_tsupport
  statement: LocallyFinite fun i => tsupport (f i)
  proof: f.locallyFinite.closure

中文:
定理 locallyFinite_tsupport
  结论: 局部有限 fun i => tsupport (f i)
  证明: f.locallyFinite.closure

Depends on / 依赖: closure, f.locallyFinite.closure, locallyFinite
-/
theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

/--
theorem `point_finite` / 定理 `point_finite`

English:
theorem point_finite
  given: (x : X)
  statement: { i | f i x != 0 }.Finite
  proof: f.locallyFinite.point_finite x

中文:
定理 point_finite
  条件: (x : X)
  结论: { i | f i x != 0 }.有限
  证明: f.locallyFinite.point_finite x
-/
protected theorem point_finite (x : X) : { i | f i x != 0 }.Finite :=
  f.locallyFinite.point_finite x

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (i : ι) (x : X)
  statement: 0 <= f i x
  proof: f.nonneg' i x

中文:
定理 nonneg
  条件: (i : ι) (x : X)
  结论: 0 <= f i x
  证明: f.nonneg' i x

Depends on / 依赖: f.nonneg, nonneg
-/
theorem nonneg (i : ι) (x : X) : 0 <= f i x :=
  f.nonneg' i x

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: (i : ι) (x : X)
  statement: f i x <= 1
  proof: f.le_one' i x

中文:
定理 le_one
  条件: (i : ι) (x : X)
  结论: f i x <= 1
  证明: f.le_one' i x

Depends on / 依赖: f.le_one, le_one
-/
theorem le_one (i : ι) (x : X) : f i x <= 1 :=
  f.le_one' i x

open scoped Classical in
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (i : ι) (s : Set X)
  body: Pi.single i 1
  locallyFinite' x := by
    refine ⟨univ, univ_mem, (finite_singleton i).subset ?_⟩
    rintro j ⟨x, hx, -⟩
    contrapose! hx
    rw [mem_singleton_iff] at hx
    simp [hx]
  nonneg' := le_update_iff.2 ⟨fun _ => zero_le_one, fun _ _ => le_rfl⟩
  le_one' := update_le_iff.2 ⟨le_rfl, fu

中文:
定义 single
  签名: (i : ι) (s : 集合 X)
  定义体: Pi.single i 1
  locallyFinite' x := by
    refine ⟨univ, univ_mem, (finite_singleton i).subset ?_⟩
    rintro j ⟨x, hx, -⟩
    contrapose! hx
    rw [mem_singleton_iff] at hx
    simp [hx]
  nonneg' := le_update_iff.2 ⟨fun _ => zero_le_one, fun _ _ => le_rfl⟩
  le_one' := update_le_iff.2 ⟨le_rfl, fu
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
/--
theorem `coe_single` / 定理 `coe_single`

English:
theorem coe_single
  given: (i : ι) (s : Set X)
  statement: ⇑(BumpCovering.single i s) = Pi.single i 1
  proof: by
  rfl

中文:
定理 coe_single
  条件: (i : ι) (s : 集合 X)
  结论: ⇑(BumpCovering.single i s) = 依赖函数类型.single i 1
  证明: by
  rfl
-/
theorem coe_single (i : ι) (s : Set X) : ⇑(BumpCovering.single i s) = Pi.single i 1 := by
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: ι] : Inhabited (BumpCovering ι X s)
  body: ⟨BumpCovering.single default s⟩

中文:
实例 [可居
  签名: ι] : 可居 (BumpCovering ι X s)
  定义体: ⟨BumpCovering.single default s⟩

Depends on / 依赖: BumpCovering, BumpCovering.single, single
-/
instance [Inhabited ι] : Inhabited (BumpCovering ι X s) :=
  ⟨BumpCovering.single default s⟩

/--
Definition of `IsSubordinate` / `IsSubordinate` 的定义

English:
definition IsSubordinate
  signature: (f : BumpCovering ι X s) (U : ι -> Set X)
  body: forall i, tsupport (f i) subseteq U i

中文:
定义 IsSubordinate
  签名: (f : BumpCovering ι X s) (U : ι -> 集合 X)
  定义体: forall i, tsupport (f i) subseteq U i

Depends on / 依赖: subseteq, tsupport
-/
def IsSubordinate (f : BumpCovering ι X s) (U : ι -> Set X) : Prop :=
  forall i, tsupport (f i) subseteq U i

/--
theorem `IsSubordinate.mono` / 定理 `IsSubordinate.mono`

English:
theorem IsSubordinate.mono
  statement: {f : BumpCovering ι X s} {U V : ι -> Set X} (hU : f.IsSubordinate U)
  proof: fun i => Subset.trans (hU i) (hV i)

中文:
定理 IsSubordinate.mono
  结论: {f : BumpCovering ι X s} {U V : ι -> 集合 X} (hU : f.IsSubordinate U)
  证明: fun i => Subset.trans (hU i) (hV i)
-/
theorem IsSubordinate.mono {f : BumpCovering ι X s} {U V : ι -> Set X} (hU : f.IsSubordinate U)
    (hV : forall i, U i subseteq V i) : f.IsSubordinate V :=
  fun i => Subset.trans (hU i) (hV i)

/--
theorem `exists_isSubordinate_of_locallyFinite_of_prop` / 定理 `exists_isSubordinate_of_locallyFinite_of_prop`

English:
theorem exists_isSubordinate_of_locallyFinite_of_prop
  statement: [NormalSpace X] (p : (X -> Real) -> Prop)
  proof: by
  rcases exists_subset_iUnion_closure_subset hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU⟩
  have hVU' : forall i, V i subseteq U i := fun i => Subset.trans subset_closure (hVU i)
  rcases exists_subset_iUnion_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x

中文:
定理 存在_isSubordinate_of_locallyFinite_of_prop
  结论: [正规空间 X] (p : (X -> 实数) -> 命题)
  证明: by
  rcases exists_subset_iUnion_closure_subset hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU⟩
  have hVU' : forall i, V i subseteq U i := fun i => Subset.trans subset_closure (hVU i)
  rcases exists_subset_iUnion_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x

Depends on / 依赖: Classical, Classical.not_not, Subset, Subset.trans, disjoint_right, exists_subset_iUnion_closure_subset, hf.point_finite, hf.subset, isClosed_closure, isClosed_compl_iff, not_not, point_finite, subset, subset_closure, subseteq
-/
theorem exists_isSubordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X -> Real) -> Prop)
    (h01 : forall s t, IsClosed s -> IsClosed t -> Disjoint s t ->
      exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1)
    (hs : IsClosed s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s subseteq ⋃ i, U i) : exists f : BumpCovering ι X s, (forall i, p (f i)) ∧ f.IsSubordinate U := by
  rcases exists_subset_iUnion_closure_subset hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU⟩
  have hVU' : forall i, V i subseteq U i := fun i => Subset.trans subset_closure (hVU i)
  rcases exists_subset_iUnion_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x)
      hsV with
    ⟨W, hsW, hWo, hWV⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) isClosed_closure
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp : forall i, support (f i) subseteq V i := fun i => support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

/--
theorem `exists_isSubordinate_of_locallyFinite` / 定理 `exists_isSubordinate_of_locallyFinite`

English:
theorem exists_isSubordinate_of_locallyFinite
  statement: [NormalSpace X] (hs : IsClosed s) (U : ι -> Set X)
  proof: let ⟨f, _, hfU⟩ :=
    exists_isSubordinate_of_locallyFinite_of_prop (fun _ => True)
      (fun _ _ hs ht hd =>
        (exists_continuous_zero_one_of_isClosed hs ht hd).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU
  ⟨f, hfU⟩

中文:
定理 存在_isSubordinate_of_locallyFinite
  结论: [正规空间 X] (hs : 是闭集 s) (U : ι -> 集合 X)
  证明: let ⟨f, _, hfU⟩ :=
    exists_isSubordinate_of_locallyFinite_of_prop (fun _ => True)
      (fun _ _ hs ht hd =>
        (exists_continuous_zero_one_of_isClosed hs ht hd).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU
  ⟨f, hfU⟩

Depends on / 依赖: exists_continuous_zero_one_of_isClosed, exists_isSubordinate_of_locallyFinite_of_prop
-/
theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι -> Set X)
    (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s subseteq ⋃ i, U i) :
    exists f : BumpCovering ι X s, f.IsSubordinate U :=
  let ⟨f, _, hfU⟩ :=
    exists_isSubordinate_of_locallyFinite_of_prop (fun _ => True)
      (fun _ _ hs ht hd =>
        (exists_continuous_zero_one_of_isClosed hs ht hd).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU
  ⟨f, hfU⟩

/--
theorem `exists_isSubordinate_of_prop` / 定理 `exists_isSubordinate_of_prop`

English:
theorem exists_isSubordinate_of_prop
  statement: [NormalSpace X] [ParacompactSpace X] (p : (X -> Real) -> Prop)
  proof: by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

中文:
定理 存在_isSubordinate_of_prop
  结论: [正规空间 X] [仿紧空间 X] (p : (X -> 实数) -> 命题)
  证明: by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

Depends on / 依赖: exists_isSubordinate_of_locallyFinite_of_prop, hf.mono, precise_refinement_set
-/
theorem exists_isSubordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X -> Real) -> Prop)
    (h01 : forall s t, IsClosed s -> IsClosed t -> Disjoint s t ->
      exists f : C(X, Real), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1)
    (hs : IsClosed s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hU : s subseteq ⋃ i, U i) :
    exists f : BumpCovering ι X s, (forall i, p (f i)) ∧ f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

/--
theorem `exists_isSubordinate` / 定理 `exists_isSubordinate`

English:
theorem exists_isSubordinate
  statement: [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι -> Set X)
  proof: by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

中文:
定理 存在_isSubordinate
  结论: [正规空间 X] [仿紧空间 X] (hs : 是闭集 s) (U : ι -> 集合 X)
  证明: by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

Depends on / 依赖: exists_isSubordinate_of_locallyFinite, hf.mono, precise_refinement_set
-/
theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι -> Set X)
    (ho : forall i, IsOpen (U i)) (hU : s subseteq ⋃ i, U i) : exists f : BumpCovering ι X s, f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

/--
theorem `exists_isSubordinate_of_locallyFinite_of_prop_t2space` / 定理 `exists_isSubordinate_of_locallyFinite_of_prop_t2space`

English:
theorem exists_isSubordinate_of_locallyFinite_of_prop_t2space
  statement: [LocallyCompactSpace X] [T2Space X]
  proof: by
  rcases exists_subset_iUnion_closure_subset_t2space hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU, hcp⟩
  have hVU' i : V i subseteq U i := subset_closure.trans (hVU i)
  rcases exists_subset_iUnion_closure_subset_t2space hs hVo
    (fun x _ => (hf.subset hVU').point_finite 

中文:
定理 存在_isSubordinate_of_locallyFinite_of_prop_t2space
  结论: [局部紧空间 X] [T2空间 X]
  证明: by
  rcases exists_subset_iUnion_closure_subset_t2space hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU, hcp⟩
  have hVU' i : V i subseteq U i := subset_closure.trans (hVU i)
  rcases exists_subset_iUnion_closure_subset_t2space hs hVo
    (fun x _ => (hf.subset hVU').point_finite 

Depends on / 依赖: Classical, Classical.not_not, disjoint_right, exists_subset_iUnion_closure_subset_t2space, hf.point_finite, hf.subset, isClosed_compl_iff, not_not, point_finite, subset, subset_closure, subset_closure.trans, subseteq, support
-/
theorem exists_isSubordinate_of_locallyFinite_of_prop_t2space [LocallyCompactSpace X] [T2Space X]
    (p : (X -> Real) -> Prop) (h01 : forall s t, IsClosed s -> IsCompact t -> Disjoint s t -> exists f : C(X, Real),
    p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1)
    (hs : IsCompact s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s subseteq ⋃ i, U i) :
    exists f : BumpCovering ι X s, (forall i, p (f i)) ∧ f.IsSubordinate U ∧
      forall i, HasCompactSupport (f i) := by
  rcases exists_subset_iUnion_closure_subset_t2space hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU, hcp⟩
  have hVU' i : V i subseteq U i := subset_closure.trans (hVU i)
  rcases exists_subset_iUnion_closure_subset_t2space hs hVo
    (fun x _ => (hf.subset hVU').point_finite x) hsV with ⟨W, hsW, hWo, hWV, hWc⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) (hWc i)
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp i : support (f i) subseteq V i := support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i),
fun i => IsCompact.of_isClosed_subset (hcp i) isClosed_closure closure_mono (hsupp i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

/--
theorem `exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space` / 定理 `exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space`

English:
theorem exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space
  statement: [LocallyCompactSpace X]
  proof: by
  -- need to switch 0 and 1 in `exists_continuous_zero_one_of_isCompact`
  simpa using
    exists_isSubordinate_of_locallyFinite_of_prop_t2space (fun _ => True)
      (fun _ _ ht hs hd =>
        (exists_continuous_zero_one_of_isCompact' hs ht hd.symm).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho

中文:
定理 存在_isSubordinate_hasCompactSupport_of_locallyFinite_t2space
  结论: [局部紧空间 X]
  证明: by
  -- need to switch 0 and 1 in `exists_continuous_zero_one_of_isCompact`
  simpa using
    exists_isSubordinate_of_locallyFinite_of_prop_t2space (fun _ => True)
      (fun _ _ ht hs hd =>
        (exists_continuous_zero_one_of_isCompact' hs ht hd.symm).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho
-/
theorem exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space [LocallyCompactSpace X]
    [T2Space X]
    (hs : IsCompact s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s subseteq ⋃ i, U i) :
    exists f : BumpCovering ι X s, f.IsSubordinate U ∧ forall i, HasCompactSupport (f i) := by
  -- need to switch 0 and 1 in `exists_continuous_zero_one_of_isCompact`
  simpa using
    exists_isSubordinate_of_locallyFinite_of_prop_t2space (fun _ => True)
      (fun _ _ ht hs hd =>
        (exists_continuous_zero_one_of_isCompact' hs ht hd.symm).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU

/--
Definition of `ind` / `ind` 的定义

English:
definition ind
  signature: (x : X) (hx : x in s)
  body: (f.eventuallyEq_one' x hx).choose

中文:
定义 ind
  签名: (x : X) (hx : x in s)
  定义体: (f.eventuallyEq_one' x hx).choose

Depends on / 依赖: eventuallyEq_one, f.eventuallyEq_one
-/
def ind (x : X) (hx : x in s) : ι :=
  (f.eventuallyEq_one' x hx).choose

/--
theorem `eventuallyEq_one` / 定理 `eventuallyEq_one`

English:
theorem eventuallyEq_one
  given: (x : X) (hx : x in s)
  statement: f (f.ind x hx) =ᶠ[𝓝 x] 1
  proof: (f.eventuallyEq_one' x hx).choose_spec

中文:
定理 eventuallyEq_one
  条件: (x : X) (hx : x in s)
  结论: f (f.ind x hx) =ᶠ[𝓝 x] 1
  证明: (f.eventuallyEq_one' x hx).choose_spec

Depends on / 依赖: choose_spec, eventuallyEq_one, f.eventuallyEq_one
-/
theorem eventuallyEq_one (x : X) (hx : x in s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
  (f.eventuallyEq_one' x hx).choose_spec

/--
theorem `ind_apply` / 定理 `ind_apply`

English:
theorem ind_apply
  given: (x : X) (hx : x in s)
  statement: f (f.ind x hx) x = 1
  proof: (f.eventuallyEq_one x hx).eq_of_nhds

中文:
定理 ind_apply
  条件: (x : X) (hx : x in s)
  结论: f (f.ind x hx) x = 1
  证明: (f.eventuallyEq_one x hx).eq_of_nhds

Depends on / 依赖: eq_of_nhds, eventuallyEq_one, f.eventuallyEq_one
-/
theorem ind_apply (x : X) (hx : x in s) : f (f.ind x hx) x = 1 :=
  (f.eventuallyEq_one x hx).eq_of_nhds

/--
Definition of `toPOUFun` / `toPOUFun` 的定义

English:
definition toPOUFun
  signature: (i : ι) (x : X)
  body: f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)

中文:
定义 toPOUFun
  签名: (i : ι) (x : X)
  定义体: f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)

Depends on / 依赖: WellOrderingRel
-/
def toPOUFun (i : ι) (x : X) : Real :=
  f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)

/--
theorem `toPOUFun_zero_of_zero` / 定理 `toPOUFun_zero_of_zero`

English:
theorem toPOUFun_zero_of_zero
  given: {i : ι} {x : X} (h : f i x = 0)
  statement: f.toPOUFun i x = 0
  proof: by
  rw [toPOUFun]; rw [h]; rw [zero_mul]

中文:
定理 toPOUFun_zero_of_zero
  条件: {i : ι} {x : X} (h : f i x = 0)
  结论: f.toPOUFun i x = 0
  证明: by
  rw [toPOUFun]; rw [h]; rw [zero_mul]

Depends on / 依赖: toPOUFun, zero_mul
-/
theorem toPOUFun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPOUFun i x = 0 := by
  rw [toPOUFun]; rw [h]; rw [zero_mul]

/--
theorem `support_toPOUFun_subset` / 定理 `support_toPOUFun_subset`

English:
theorem support_toPOUFun_subset
  given: (i : ι)
  statement: support (f.toPOUFun i) subseteq support (f i)
  proof: fun _ => mt f.toPOUFun_zero_of_zero

中文:
定理 support_toPOUFun_subset
  条件: (i : ι)
  结论: support (f.toPOUFun i) subseteq support (f i)
  证明: fun _ => mt f.toPOUFun_zero_of_zero

Depends on / 依赖: f.toPOUFun_zero_of_zero, toPOUFun_zero_of_zero
-/
theorem support_toPOUFun_subset (i : ι) : support (f.toPOUFun i) subseteq support (f i) :=
fun _ => mt f.toPOUFun_zero_of_zero

open scoped Classical in
/--
theorem `toPOUFun_eq_mul_prod` / 定理 `toPOUFun_eq_mul_prod`

English:
theorem toPOUFun_eq_mul_prod
  statement: (i : ι) (x : X) (t : Finset ι)
  proof: by
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun {j} hj => ?_)
  rw [Ne]; rw [sub_eq_self] at hj
  rw [Finset.mem_filter]; rw [Iff.comm]; rw [and_iff_right_iff_imp]
  exact flip (ht j) hj

中文:
定理 toPOUFun_eq_mul_prod
  结论: (i : ι) (x : X) (t : 有限集 ι)
  证明: by
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun {j} hj => ?_)
  rw [Ne]; rw [sub_eq_self] at hj
  rw [Finset.mem_filter]; rw [Iff.comm]; rw [and_iff_right_iff_imp]
  exact flip (ht j) hj

Depends on / 依赖: Finset, Finset.mem_filter, Iff.comm, and_iff_right_iff_imp, congr_arg, finprod_cond_eq_prod_of_cond_iff, mem_filter, sub_eq_self
-/
theorem toPOUFun_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : forall j, WellOrderingRel j i -> f j x != 0 -> j in t) :
    f.toPOUFun i x = f i x * ∏ j in t with WellOrderingRel j i, (1 - f j x) := by
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun {j} hj => ?_)
  rw [Ne]; rw [sub_eq_self] at hj
  rw [Finset.mem_filter]; rw [Iff.comm]; rw [and_iff_right_iff_imp]
  exact flip (ht j) hj

/--
theorem `sum_toPOUFun_eq` / 定理 `sum_toPOUFun_eq`

English:
theorem sum_toPOUFun_eq
  given: (x : X)
  statement: ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x)
  proof: by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x != 0 } := Finite.coe_toFinset _
  have A : (support fun i => toPOUFun f i x) subseteq s := by
    rw [hs]
    exact fun i hi => f.support_toPOUFun_subset i hi
  have B : (mulSupport fun i => 1 - f i x) subseteq s := by
 

中文:
定理 sum_toPOUFun_eq
  条件: (x : X)
  结论: ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x)
  证明: by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x != 0 } := Finite.coe_toFinset _
  have A : (support fun i => toPOUFun f i x) subseteq s := by
    rw [hs]
    exact fun i hi => f.support_toPOUFun_subset i hi
  have B : (mulSupport fun i => 1 - f i x) subseteq s := by
 

Depends on / 依赖: Finite, Finite.coe_toFinset, Finset, LinearOrder, WellOrderingRel, classical, coe_toFinset, f.point_finite, f.support_toPOUFun_subset, finprod_eq_prod_of_mulSupport_subset, finsum_eq_sum_of_support_subset, linearOrderOfSTO, mulSupport, mulSupport_one_sub, point_finite, subseteq, support, support_toPOUFun_subset, toFinset, toPOUFun
-/
theorem sum_toPOUFun_eq (x : X) : ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x) := by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x != 0 } := Finite.coe_toFinset _
  have A : (support fun i => toPOUFun f i x) subseteq s := by
    rw [hs]
    exact fun i hi => f.support_toPOUFun_subset i hi
  have B : (mulSupport fun i => 1 - f i x) subseteq s := by
    rw [hs]; rw [mulSupport_one_sub]
    exact fun i => id
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  rw [finsum_eq_sum_of_support_subset _ A]; rw [finprod_eq_prod_of_mulSupport_subset _ B]; rw [Finset.prod_one_sub_ordered]; rw [sub_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  convert! f.toPOUFun_eq_mul_prod _ _ _ fun j _ hj => _
  rwa [Finite.mem_toFinset]

open scoped Classical in
/--
theorem `exists_finset_toPOUFun_eventuallyEq` / 定理 `exists_finset_toPOUFun_eventuallyEq`

English:
theorem exists_finset_toPOUFun_eventuallyEq
  given: (i : ι) (x : X)
  statement: exists t : Finset ι,
  proof: by
  rcases f.locallyFinite x with ⟨U, hU, hf⟩
  use hf.toFinset
  filter_upwards [hU] with y hyU
  simp only [ContinuousMap.coe_prod, Pi.mul_apply, Finset.prod_apply]
  apply toPOUFun_eq_mul_prod
  intro j _ hj
  exact hf.mem_toFinset.2 ⟨y, ⟨hj, hyU⟩⟩

中文:
定理 存在_finset_toPOUFun_eventuallyEq
  条件: (i : ι) (x : X)
  结论: 存在 t : 有限集 ι,
  证明: by
  rcases f.locallyFinite x with ⟨U, hU, hf⟩
  use hf.toFinset
  filter_upwards [hU] with y hyU
  simp only [ContinuousMap.coe_prod, Pi.mul_apply, Finset.prod_apply]
  apply toPOUFun_eq_mul_prod
  intro j _ hj
  exact hf.mem_toFinset.2 ⟨y, ⟨hj, hyU⟩⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_prod, Finset, Finset.prod_apply, Pi.mul_apply, coe_prod, f.locallyFinite, filter_upwards, hf.mem_toFinset, hf.toFinset, locallyFinite, mem_toFinset, mul_apply, prod_apply, toFinset, toPOUFun_eq_mul_prod
-/
theorem exists_finset_toPOUFun_eventuallyEq (i : ι) (x : X) : exists t : Finset ι,
    f.toPOUFun i =ᶠ[𝓝 x] f i * ∏ j in t with WellOrderingRel j i, (1 - f j) := by
  rcases f.locallyFinite x with ⟨U, hU, hf⟩
  use hf.toFinset
  filter_upwards [hU] with y hyU
  simp only [ContinuousMap.coe_prod, Pi.mul_apply, Finset.prod_apply]
  apply toPOUFun_eq_mul_prod
  intro j _ hj
  exact hf.mem_toFinset.2 ⟨y, ⟨hj, hyU⟩⟩

/--
theorem `continuous_toPOUFun` / 定理 `continuous_toPOUFun`

English:
theorem continuous_toPOUFun
  given: (i : ι)
  statement: Continuous (f.toPOUFun i)
  proof: by
refine (map_continuous <| f i).mul continuous_finprod_cond (fun j _ => by fun_prop) ?_
  simp only [mulSupport_one_sub]
  exact f.locallyFinite

中文:
定理 continuous_toPOUFun
  条件: (i : ι)
  结论: 连续 (f.toPOUFun i)
  证明: by
refine (map_continuous <| f i).mul continuous_finprod_cond (fun j _ => by fun_prop) ?_
  simp only [mulSupport_one_sub]
  exact f.locallyFinite

Depends on / 依赖: continuous_finprod_cond, f.locallyFinite, fun_prop, locallyFinite, map_continuous, mulSupport_one_sub
-/
theorem continuous_toPOUFun (i : ι) : Continuous (f.toPOUFun i) := by
refine (map_continuous <| f i).mul continuous_finprod_cond (fun j _ => by fun_prop) ?_
  simp only [mulSupport_one_sub]
  exact f.locallyFinite

/--
Definition of `toPartitionOfUnity` / `toPartitionOfUnity` 的定义

English:
definition toPartitionOfUnity
  signature: : PartitionOfUnity ι X s where
  body: ⟨f.toPOUFun i, f.continuous_toPOUFun i⟩
  locallyFinite' := f.locallyFinite.subset f.support_toPOUFun_subset
  nonneg' i x :=
    mul_nonneg (f.nonneg i x) (finprod_cond_nonneg fun j _ => sub_nonneg.2 <| f.le_one j x)
  sum_eq_one' x hx := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub

中文:
定义 toPartitionOfUnity
  签名: : 单位分解 ι X s where
  定义体: ⟨f.toPOUFun i, f.continuous_toPOUFun i⟩
  locallyFinite' := f.locallyFinite.subset f.support_toPOUFun_subset
  nonneg' i x :=
    mul_nonneg (f.nonneg i x) (finprod_cond_nonneg fun j _ => sub_nonneg.2 <| f.le_one j x)
  sum_eq_one' x hx := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub

Depends on / 依赖: continuous_toPOUFun, f.continuous_toPOUFun, f.toPOUFun, toPOUFun
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
exact finprod_nonneg fun i => sub_nonneg.2 f.le_one i x

/--
theorem `toPartitionOfUnity_apply` / 定理 `toPartitionOfUnity_apply`

English:
theorem toPartitionOfUnity_apply
  given: (i : ι) (x : X)
  proof: rfl

中文:
定理 toPartitionOfUnity_apply
  条件: (i : ι) (x : X)
  证明: rfl
-/
theorem toPartitionOfUnity_apply (i : ι) (x : X) :
    f.toPartitionOfUnity i x = f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x) := rfl

open scoped Classical in
/--
theorem `toPartitionOfUnity_eq_mul_prod` / 定理 `toPartitionOfUnity_eq_mul_prod`

English:
theorem toPartitionOfUnity_eq_mul_prod
  statement: (i : ι) (x : X) (t : Finset ι)
  proof: f.toPOUFun_eq_mul_prod i x t ht

中文:
定理 toPartitionOfUnity_eq_mul_prod
  结论: (i : ι) (x : X) (t : 有限集 ι)
  证明: f.toPOUFun_eq_mul_prod i x t ht

Depends on / 依赖: f.toPOUFun_eq_mul_prod, toPOUFun_eq_mul_prod
-/
theorem toPartitionOfUnity_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : forall j, WellOrderingRel j i -> f j x != 0 -> j in t) :
    f.toPartitionOfUnity i x = f i x * ∏ j in t with WellOrderingRel j i, (1 - f j x) :=
  f.toPOUFun_eq_mul_prod i x t ht

open scoped Classical in
/--
theorem `exists_finset_toPartitionOfUnity_eventuallyEq` / 定理 `exists_finset_toPartitionOfUnity_eventuallyEq`

English:
theorem exists_finset_toPartitionOfUnity_eventuallyEq
  given: (i : ι) (x : X)
  statement: exists t : Finset ι,
  proof: f.exists_finset_toPOUFun_eventuallyEq i x

中文:
定理 存在_finset_toPartitionOfUnity_eventuallyEq
  条件: (i : ι) (x : X)
  结论: 存在 t : 有限集 ι,
  证明: f.exists_finset_toPOUFun_eventuallyEq i x

Depends on / 依赖: exists_finset_toPOUFun_eventuallyEq, f.exists_finset_toPOUFun_eventuallyEq
-/
theorem exists_finset_toPartitionOfUnity_eventuallyEq (i : ι) (x : X) : exists t : Finset ι,
    f.toPartitionOfUnity i =ᶠ[𝓝 x] f i * ∏ j in t with WellOrderingRel j i, (1 - f j) :=
  f.exists_finset_toPOUFun_eventuallyEq i x

/--
theorem `toPartitionOfUnity_zero_of_zero` / 定理 `toPartitionOfUnity_zero_of_zero`

English:
theorem toPartitionOfUnity_zero_of_zero
  given: {i : ι} {x : X} (h : f i x = 0)
  proof: f.toPOUFun_zero_of_zero h

中文:
定理 toPartitionOfUnity_zero_of_zero
  条件: {i : ι} {x : X} (h : f i x = 0)
  证明: f.toPOUFun_zero_of_zero h

Depends on / 依赖: f.toPOUFun_zero_of_zero, toPOUFun_zero_of_zero
-/
theorem toPartitionOfUnity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) :
    f.toPartitionOfUnity i x = 0 :=
  f.toPOUFun_zero_of_zero h

/--
theorem `support_toPartitionOfUnity_subset` / 定理 `support_toPartitionOfUnity_subset`

English:
theorem support_toPartitionOfUnity_subset
  given: (i : ι)
  proof: f.support_toPOUFun_subset i

中文:
定理 support_toPartitionOfUnity_subset
  条件: (i : ι)
  证明: f.support_toPOUFun_subset i

Depends on / 依赖: f.support_toPOUFun_subset, support_toPOUFun_subset
-/
theorem support_toPartitionOfUnity_subset (i : ι) :
    support (f.toPartitionOfUnity i) subseteq support (f i) :=
  f.support_toPOUFun_subset i

/--
theorem `sum_toPartitionOfUnity_eq` / 定理 `sum_toPartitionOfUnity_eq`

English:
theorem sum_toPartitionOfUnity_eq
  given: (x : X)
  proof: f.sum_toPOUFun_eq x

中文:
定理 sum_toPartitionOfUnity_eq
  条件: (x : X)
  证明: f.sum_toPOUFun_eq x

Depends on / 依赖: f.sum_toPOUFun_eq, sum_toPOUFun_eq
-/
theorem sum_toPartitionOfUnity_eq (x : X) :
    ∑ᶠ i, f.toPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - f i x) :=
  f.sum_toPOUFun_eq x

/--
theorem `IsSubordinate.toPartitionOfUnity` / 定理 `IsSubordinate.toPartitionOfUnity`

English:
theorem IsSubordinate.toPartitionOfUnity
  statement: {f : BumpCovering ι X s} {U : ι -> Set X}
  proof: fun i => Subset.trans (closure_mono <| f.support_toPartitionOfUnity_subset i) (h i)

中文:
定理 IsSubordinate.toPartitionOfUnity
  结论: {f : BumpCovering ι X s} {U : ι -> 集合 X}
  证明: fun i => Subset.trans (closure_mono <| f.support_toPartitionOfUnity_subset i) (h i)

Depends on / 依赖: Subset, Subset.trans, closure_mono, f.support_toPartitionOfUnity_subset, support_toPartitionOfUnity_subset
-/
theorem IsSubordinate.toPartitionOfUnity {f : BumpCovering ι X s} {U : ι -> Set X}
    (h : f.IsSubordinate U) : f.toPartitionOfUnity.IsSubordinate U :=
  fun i => Subset.trans (closure_mono <| f.support_toPartitionOfUnity_subset i) (h i)

end BumpCovering

namespace PartitionOfUnity

variable {s : Set X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: ι] : Inhabited (PartitionOfUnity ι X s)
  body: ⟨BumpCovering.toPartitionOfUnity default⟩

中文:
实例 [可居
  签名: ι] : 可居 (单位分解 ι X s)
  定义体: ⟨BumpCovering.toPartitionOfUnity default⟩

Depends on / 依赖: BumpCovering, BumpCovering.toPartitionOfUnity, toPartitionOfUnity
-/
instance [Inhabited ι] : Inhabited (PartitionOfUnity ι X s) :=
  ⟨BumpCovering.toPartitionOfUnity default⟩

/--
theorem `exists_isSubordinate_of_locallyFinite` / 定理 `exists_isSubordinate_of_locallyFinite`

English:
theorem exists_isSubordinate_of_locallyFinite
  statement: [NormalSpace X] (hs : IsClosed s) (U : ι -> Set X)
  proof: let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

中文:
定理 存在_isSubordinate_of_locallyFinite
  结论: [正规空间 X] (hs : 是闭集 s) (U : ι -> 集合 X)
  证明: let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

Depends on / 依赖: BumpCovering, BumpCovering.exists_isSubordinate_of_locallyFinite, exists_isSubordinate_of_locallyFinite, f.toPartitionOfUnity, hf.toPartitionOfUnity, toPartitionOfUnity
-/
theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι -> Set X)
    (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s subseteq ⋃ i, U i) :
    exists f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

/--
theorem `exists_isSubordinate` / 定理 `exists_isSubordinate`

English:
theorem exists_isSubordinate
  statement: [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι -> Set X)
  proof: let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

中文:
定理 存在_isSubordinate
  结论: [正规空间 X] [仿紧空间 X] (hs : 是闭集 s) (U : ι -> 集合 X)
  证明: let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

Depends on / 依赖: BumpCovering, BumpCovering.exists_isSubordinate, exists_isSubordinate, f.toPartitionOfUnity, hf.toPartitionOfUnity, toPartitionOfUnity
-/
theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι -> Set X)
    (ho : forall i, IsOpen (U i)) (hU : s subseteq ⋃ i, U i) :
    exists f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

/--
theorem `exists_isSubordinate_of_locallyFinite_t2space` / 定理 `exists_isSubordinate_of_locallyFinite_t2space`

English:
theorem exists_isSubordinate_of_locallyFinite_t2space
  statement: [LocallyCompactSpace X] [T2Space X]
  proof: let ⟨f, hfsub, hfcp⟩ :=
    BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space hs U ho hf hU
  ⟨f.toPartitionOfUnity, hfsub.toPartitionOfUnity, fun i => IsCompact.of_isClosed_subset (hfcp i)
isClosed_closure closure_mono (f.support_toPartitionOfUnity_subset i)⟩

中文:
定理 存在_isSubordinate_of_locallyFinite_t2space
  结论: [局部紧空间 X] [T2空间 X]
  证明: let ⟨f, hfsub, hfcp⟩ :=
    BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space hs U ho hf hU
  ⟨f.toPartitionOfUnity, hfsub.toPartitionOfUnity, fun i => IsCompact.of_isClosed_subset (hfcp i)
isClosed_closure closure_mono (f.support_toPartitionOfUnity_subset i)⟩

Depends on / 依赖: BumpCovering, BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space, IsCompact, IsCompact.of_isClosed_subset, closure_mono, exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space, f.support_toPartitionOfUnity_subset, f.toPartitionOfUnity, hfsub.toPartitionOfUnity, isClosed_closure, of_isClosed_subset, support_toPartitionOfUnity_subset, toPartitionOfUnity
-/
theorem exists_isSubordinate_of_locallyFinite_t2space [LocallyCompactSpace X] [T2Space X]
    (hs : IsCompact s) (U : ι -> Set X) (ho : forall i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s subseteq ⋃ i, U i) :
    exists f : PartitionOfUnity ι X s, f.IsSubordinate U ∧ forall i, HasCompactSupport (f i) :=
  let ⟨f, hfsub, hfcp⟩ :=
    BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space hs U ho hf hU
  ⟨f.toPartitionOfUnity, hfsub.toPartitionOfUnity, fun i => IsCompact.of_isClosed_subset (hfcp i)
isClosed_closure closure_mono (f.support_toPartitionOfUnity_subset i)⟩

end PartitionOfUnity

/--
theorem `exists_continuous_sum_one_of_isOpen_isCompact` / 定理 `exists_continuous_sum_one_of_isOpen_isCompact`

English:
theorem exists_continuous_sum_one_of_isOpen_isCompact
  statement: [T2Space X] [LocallyCompactSpace X]
  proof: by
  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space htcp s
    hs (locallyFinite_of_finite _) hst
  use f
  refine ⟨fun i => hfsub i, ?_, ?_, fun i => hfcp i⟩
  · intro x hx
    simp only [Finset.sum_apply, Pi.one_apply]
    have h := f.sum_eq_one' x hx
   

中文:
定理 存在_continuous_sum_one_of_isOpen_isCompact
  结论: [T2空间 X] [局部紧空间 X]
  证明: by
  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space htcp s
    hs (locallyFinite_of_finite _) hst
  use f
  refine ⟨fun i => hfsub i, ?_, ?_, fun i => hfcp i⟩
  · intro x hx
    simp only [Finset.sum_apply, Pi.one_apply]
    have h := f.sum_eq_one' x hx
   

Depends on / 依赖: Finite, Finite.subset, Finset, Finset.sum_apply, Fintype, Fintype.sum_subset, PartitionOfUnity, PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space, PartitionOfUnity.le_one, Pi.one_apply, exists_isSubordinate_of_locallyFinite_t2space, f.nonneg, f.sum_eq_one, f.toFun, finite_univ, finsum_eq_sum, le_one, locallyFinite_of_finite, nonneg, one_apply
-/
theorem exists_continuous_sum_one_of_isOpen_isCompact [T2Space X] [LocallyCompactSpace X]
    {n : Nat} {t : Set X} {s : Fin n -> Set X} (hs : forall (i : Fin n), IsOpen (s i)) (htcp : IsCompact t)
    (hst : t subseteq ⋃ i, s i) :
    exists f : Fin n -> C(X, Real), (forall (i : Fin n), tsupport (f i) subseteq s i) ∧ EqOn (∑ i, f i) 1 t
      ∧ (forall (i : Fin n), forall (x : X), f i x in Icc (0 : Real) 1)
      ∧ (forall (i : Fin n), HasCompactSupport (f i)) := by
  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space htcp s
    hs (locallyFinite_of_finite _) hst
  use f
  refine ⟨fun i => hfsub i, ?_, ?_, fun i => hfcp i⟩
  · intro x hx
    simp only [Finset.sum_apply, Pi.one_apply]
    have h := f.sum_eq_one' x hx
    rw [finsum_eq_sum (fun i => (f.toFun i) x)
      (Finite.subset finite_univ (subset_univ (support fun i => (f.toFun i) x)))] at h
    rwa [Fintype.sum_subset (by simp)] at h
  intro i x
  exact ⟨f.nonneg i x, PartitionOfUnity.le_one f i x⟩
