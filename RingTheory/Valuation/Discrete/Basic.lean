/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.Group.Cyclic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ`, a valuation `v : A → Γ` on a ring `A` is
*discrete*, if there is an element `γ : Γˣ` that is `< 1` and generated the range of `v`,
implemented as `MonoidWithZeroHom.valueGroup v`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `γ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.

Note that this definition of discrete implies that the valuation is nontrivial and of rank one, as
is commonly assumed in number theory. To avoid potential confusion with other definitions of
discrete, we use the name `IsRankOneDiscrete` to refer to discrete valuations in this setting.

## Main Definitions
* `Valuation.IsRankOneDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if there is
  an element `γ : Γˣ` that is `< 1` and generates the range of `v`.
* `Valuation.IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is
  a uniformizer if `v π` is a generator of the value group that is `<1`.
* `Valuation.Uniformizer`: A structure bundling an element of a ring and a proof that it is a
  uniformizer.

## Main Results
* `Valuation.IsUniformizer.of_associated`: An element associated to a uniformizer is itself a
  uniformizer.
* `Valuation.associated_of_isUniformizer`: If two elements are uniformizers, they are associated.
* `Valuation.IsUniformizer.is_generator` A generator of the maximal ideal is a uniformizer when
  the valuation is discrete.
* `Valuation.IsRankOneDiscrete.mk'`: if the `valueGroup` of the valuation `v` is cyclic and
  nontrivial, then `v` is discrete.
* `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`: If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then there exists a uniformizer for `v`.
* `Valuation.isUniformizer_of_maximalIdeal_eq_span`: Given a discrete valuation `v` on a field `K`,
  a generator of the maximal ideal of `v.valuationSubring` is a uniformizer for `v`.
* `Valuation.valuationSubring_isDiscreteValuationRing` : If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then `v.valuationSubring` is a discrete
  valuation ring. This instance is the formalization of Chapter I, Section 1, Proposition 1 in
  [serre1968].


## TODO
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

@[expose] public section

namespace Valuation

open LinearOrderedCommGroup MonoidWithZeroHom Set Subgroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/--
Definition of `IsRankOneDiscrete` / `IsRankOneDiscrete` 的定义

English:
class IsRankOneDiscrete
  parameters: : Prop where
  axioms and operations (1):
    - exists_generator_lt_one' : exists (γ : Γˣ), zpowers γ = (valueGroup (.ofClass v)) ∧ γ < 1

中文:
类 是RankOneDiscrete
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_generator_lt_one' : 存在 (γ : Γˣ), zpowers γ = (valueGroup (.ofClass v)) ∧ γ < 1
-/
class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : exists (γ : Γˣ), zpowers γ = (valueGroup (.ofClass v)) ∧ γ < 1

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

/--
lemma `exists_generator_lt_one` / 引理 `exists_generator_lt_one`

English:
lemma exists_generator_lt_one
  statement: exists (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1
  proof: exists_generator_lt_one'

中文:
引理 存在_generator_lt_one
  结论: 存在 (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1
  证明: exists_generator_lt_one'

Depends on / 依赖: exists_generator_lt_one
-/
lemma exists_generator_lt_one : exists (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1 :=
  exists_generator_lt_one'

/--
Definition of `generator` / `generator` 的定义

English:
definition generator
  signature: : Γˣ
  body: (exists_generator_lt_one v).choose

中文:
定义 generator
  签名: : Γˣ
  定义体: (exists_generator_lt_one v).choose

Depends on / 依赖: exists_generator_lt_one
-/
noncomputable def generator : Γˣ := (exists_generator_lt_one v).choose

/--
lemma `generator_zpowers_eq_valueGroup` / 引理 `generator_zpowers_eq_valueGroup`

English:
lemma generator_zpowers_eq_valueGroup
  proof: (exists_generator_lt_one v).choose_spec.1

中文:
引理 generator_zpowers_eq_valueGroup
  证明: (exists_generator_lt_one v).choose_spec.1

Depends on / 依赖: choose_spec, exists_generator_lt_one
-/
lemma generator_zpowers_eq_valueGroup :
    zpowers (generator v) = valueGroup (.ofClass v) :=
  (exists_generator_lt_one v).choose_spec.1

/--
lemma `generator_mem_valueGroup` / 引理 `generator_mem_valueGroup`

English:
lemma generator_mem_valueGroup
  proof: by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)

中文:
引理 generator_mem_valueGroup
  证明: by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)

Depends on / 依赖: IsRankOneDiscrete, IsRankOneDiscrete.generator, IsRankOneDiscrete.generator_zpowers_eq_valueGroup, generator, generator_zpowers_eq_valueGroup, mem_zpowers
-/
lemma generator_mem_valueGroup :
    (IsRankOneDiscrete.generator v) in valueGroup (.ofClass v) := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)

/--
lemma `generator_lt_one` / 引理 `generator_lt_one`

English:
lemma generator_lt_one
  statement: generator v < 1
  proof: (exists_generator_lt_one v).choose_spec.2

中文:
引理 generator_lt_one
  结论: generator v < 1
  证明: (exists_generator_lt_one v).choose_spec.2

Depends on / 依赖: choose_spec, exists_generator_lt_one
-/
lemma generator_lt_one : generator v < 1 :=
  (exists_generator_lt_one v).choose_spec.2

/--
lemma `generator_ne_one` / 引理 `generator_ne_one`

English:
lemma generator_ne_one
  statement: generator v != 1
  proof: ne_of_lt generator_lt_one v

中文:
引理 generator_ne_one
  结论: generator v != 1
  证明: ne_of_lt generator_lt_one v

Depends on / 依赖: generator_lt_one, ne_of_lt
-/
lemma generator_ne_one : generator v != 1 :=
ne_of_lt generator_lt_one v

/--
lemma `generator_zpowers_eq_range` / 引理 `generator_zpowers_eq_range`

English:
lemma generator_zpowers_eq_range
  given: (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w]
  proof: by
  simp [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

中文:
引理 generator_zpowers_eq_range
  条件: (K : 类型) [域 K] (w : 赋值 K Γ) [是RankOneDiscrete w]
  证明: by
  simp [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

Depends on / 依赖: generator_zpowers_eq_valueGroup, valueGroup_eq_range
-/
lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (zpowers (generator w)) = range w \ {0} := by
  simp [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

/--
lemma `generator_mem_range` / 引理 `generator_mem_range`

English:
lemma generator_mem_range
  given: (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w]
  proof: by
  apply sdiff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

中文:
引理 generator_mem_range
  条件: (K : 类型) [域 K] (w : 赋值 K Γ) [是RankOneDiscrete w]
  证明: by
  apply sdiff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

Depends on / 依赖: generator, generator_zpowers_eq_range, sdiff_subset
-/
lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    ↑(generator w) in range w := by
  apply sdiff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

/--
lemma `generator_ne_zero` / 引理 `generator_ne_zero`

English:
lemma generator_ne_zero
  statement: (generator v : Γ) != 0
  proof: by simp

中文:
引理 generator_ne_zero
  结论: (generator v : Γ) != 0
  证明: by simp
-/
lemma generator_ne_zero : (generator v : Γ) != 0 := by simp

/--
Definition of `generator'` / `generator'` 的定义

English:
definition generator'
  signature: : valueGroup (.ofClass v)
  body: ⟨generator v, generator_mem_valueGroup v⟩

@[simp]

中文:
定义 generator'
  签名: : valueGroup (.ofClass v)
  定义体: ⟨generator v, generator_mem_valueGroup v⟩

@[simp]

Depends on / 依赖: generator, generator_mem_valueGroup
-/
noncomputable def generator' : valueGroup (.ofClass v) := ⟨generator v, generator_mem_valueGroup v⟩

@[simp]
/--
lemma `embedding_generator'` / 引理 `embedding_generator'`

English:
lemma embedding_generator'
  proof: rfl

中文:
引理 embedding_generator'
  证明: rfl

Depends on / 依赖: generator, ofClass
-/
lemma embedding_generator' :
    ValueGroup₀.embedding (f := .ofClass v) (generator' v) = generator v := rfl

/--
lemma `generator'_zpowers_eq_top` / 引理 `generator'_zpowers_eq_top`

English:
lemma generator'_zpowers_eq_top
  statement: (zpowers (generator' v)) = ⊤
  proof: by
  rw [← map_subtype_inj]; rw [MonoidHom.map_zpowers]; rw [subtype_apply]; rw [← MonoidHom.range_eq_map]; rw [Subgroup.subtype_range]
  apply generator_zpowers_eq_valueGroup

中文:
引理 generator'_zpowers_eq_top
  结论: (zpowers (generator' v)) = ⊤
  证明: by
  rw [← map_subtype_inj]; rw [MonoidHom.map_zpowers]; rw [subtype_apply]; rw [← MonoidHom.range_eq_map]; rw [Subgroup.subtype_range]
  apply generator_zpowers_eq_valueGroup
-/
lemma generator'_zpowers_eq_top : (zpowers (generator' v)) = ⊤ := by
  rw [← map_subtype_inj]; rw [MonoidHom.map_zpowers]; rw [subtype_apply]; rw [← MonoidHom.range_eq_map]; rw [Subgroup.subtype_range]
  apply generator_zpowers_eq_valueGroup

/--
lemma `generator'_lt_one` / 引理 `generator'_lt_one`

English:
lemma generator'_lt_one
  statement: generator' v < 1
  proof: (exists_generator_lt_one v).choose_spec.2

中文:
引理 generator'_lt_one
  结论: generator' v < 1
  证明: (exists_generator_lt_one v).choose_spec.2
-/
lemma generator'_lt_one : generator' v < 1 :=
  (exists_generator_lt_one v).choose_spec.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCyclic valueGroup (.ofClass v)
  body: by
  rw [← generator_zpowers_eq_valueGroup]
  exact isCyclic_zpowers (generator v)

中文:
实例 :
  签名: 是循环 valueGroup (.ofClass v)
  定义体: by
  rw [← generator_zpowers_eq_valueGroup]
  exact isCyclic_zpowers (generator v)

Depends on / 依赖: generator, generator_zpowers_eq_valueGroup, isCyclic_zpowers
-/
instance : IsCyclic valueGroup (.ofClass v) := by
  rw [← generator_zpowers_eq_valueGroup]
  exact isCyclic_zpowers (generator v)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: v.IsNontrivial
  body: by
  apply IsNontrivial.mk
  by_contra! h1
  have hvalueGroup : valueGroup (.ofClass v) = ⊥ := by
    simp only [valueGroup, valueMonoid, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      closure_eq_bot_iff, subset_singleton_iff, mem_preimage, mem_range, forall_exists_index,
      Units.ext_iff]
    intro y x
    specialize h1 x
    aesop
  aesop (add safe forward [generator_lt_one, generator_zpowers_eq_valueGroup])

中文:
实例 :
  签名: v.是非平凡
  定义体: by
  apply IsNontrivial.mk
  by_contra! h1
  have hvalueGroup : valueGroup (.ofClass v) = ⊥ := by
    simp only [valueGroup, valueMonoid, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      closure_eq_bot_iff, subset_singleton_iff, mem_preimage, mem_range, forall_exists_index,
      Units.ext_iff]
    intro y x
    specialize h1 x
    aesop
  aesop (add safe forward [generator_lt_one, generator_zpowers_eq_valueGroup])

Depends on / 依赖: IsNontrivial, IsNontrivial.mk, Submonoid, Submonoid.coe_set_mk, Subsemigroup, Subsemigroup.coe_set_mk, Units.ext_iff, closure_eq_bot_iff, coe_set_mk, ext_iff, forall_exists_index, forward, generator_lt_one, generator_zpowers_eq_valueGroup, hvalueGroup, mem_preimage, mem_range, ofClass, specialize, subset_singleton_iff
-/
instance : v.IsNontrivial := by
  apply IsNontrivial.mk
  by_contra! h1
  have hvalueGroup : valueGroup (.ofClass v) = ⊥ := by
    simp only [valueGroup, valueMonoid, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      closure_eq_bot_iff, subset_singleton_iff, mem_preimage, mem_range, forall_exists_index,
      Units.ext_iff]
    intro y x
    specialize h1 x
    aesop
  aesop (add safe forward [generator_lt_one, generator_zpowers_eq_valueGroup])

/--
lemma `valueGroup_genLTOne_eq_generator` / 引理 `valueGroup_genLTOne_eq_generator`

English:
lemma valueGroup_genLTOne_eq_generator
  statement: (valueGroup (.ofClass v)).genLTOne = generator v
  proof: ((valueGroup (.ofClass v)).genLTOne_unique (generator_lt_one v)
      (generator_zpowers_eq_valueGroup v)).symm

中文:
引理 valueGroup_genLTOne_eq_generator
  结论: (valueGroup (.ofClass v)).genLTOne = generator v
  证明: ((valueGroup (.ofClass v)).genLTOne_unique (generator_lt_one v)
      (generator_zpowers_eq_valueGroup v)).symm

Depends on / 依赖: genLTOne_unique, generator_lt_one, generator_zpowers_eq_valueGroup, ofClass, valueGroup
-/
lemma valueGroup_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = generator v :=
  ((valueGroup (.ofClass v)).genLTOne_unique (generator_lt_one v)
      (generator_zpowers_eq_valueGroup v)).symm

section WithZeroMulInt

open WithZero

variable {v : Valuation A Intᵐ⁰} [hv : v.IsRankOneDiscrete]

/--
theorem `generator_eq_exp_neg_one_of_mem_range` / 定理 `generator_eq_exp_neg_one_of_mem_range`

English:
theorem generator_eq_exp_neg_one_of_mem_range
  given: (hπ : exp (-1) in Set.range v)
  proof: by
  rw [← Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator]
  suffices Units.mk0 (exp (-1)) (by simp) = (Subgroup.genLTOne (valueGroup (.ofClass v))) by
    simp [← this]
  apply Subgroup.genLTOne_unique
  · exact compareOfLessAndEq_eq_lt.mp rfl
  · ext n
    simp_all only [Int.reduceNeg, exp_neg, Subgroup.mem_zpowers_iff, mem_valueGroup_iff_of_comm,
      ne_eq]
    refine ⟨fun ⟨k, h⟩ => ?_ , fun _ => ⟨-WithZero.log n, by aesop⟩⟩
    rw [← h]
    have ⟨π, hπ⟩ := hπ
    cases k with
    | ofNat n => refine ⟨1, ?_, π ^ n, ?_⟩ <;> simp [hπ]
    | negSucc n => refine ⟨π ^ (n + 1), ?_, 1, ?_⟩ <;> simp [hπ, Int.negSucc_eq, mul_assoc]

中文:
定理 generator_eq_exp_neg_one_of_mem_range
  条件: (hπ : exp (-1) in 集合.range v)
  证明: by
  rw [← Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator]
  suffices Units.mk0 (exp (-1)) (by simp) = (Subgroup.genLTOne (valueGroup (.ofClass v))) by
    simp [← this]
  apply Subgroup.genLTOne_unique
  · exact compareOfLessAndEq_eq_lt.mp rfl
  · ext n
    simp_all only [Int.reduceNeg, exp_neg, Subgroup.mem_zpowers_iff, mem_valueGroup_iff_of_comm,
      ne_eq]
    refine ⟨fun ⟨k, h⟩ => ?_ , fun _ => ⟨-WithZero.log n, by aesop⟩⟩
    rw [← h]
    have ⟨π, hπ⟩ := hπ
    cases k with
    | ofNat n => refine ⟨1, ?_, π ^ n, ?_⟩ <;> simp [hπ]
    | negSucc n => refine ⟨π ^ (n + 1), ?_, 1, ?_⟩ <;> simp [hπ, Int.negSucc_eq, mul_assoc]

Depends on / 依赖: Int.reduceNeg, IsRankOneDiscrete, Subgroup, Subgroup.genLTOne, Subgroup.genLTOne_unique, Subgroup.mem_zpowers_iff, Units.mk0, Valuation, Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator, WithZero, WithZero.log, compareOfLessAndEq_eq_lt, compareOfLessAndEq_eq_lt.mp, exp_neg, genLTOne, genLTOne_unique, mem_valueGroup_iff_of_comm, mem_zpowers_iff, ne_eq, ofClass
-/
theorem generator_eq_exp_neg_one_of_mem_range (hπ : exp (-1) in Set.range v) :
    hv.generator = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp) := by
  rw [← Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator]
  suffices Units.mk0 (exp (-1)) (by simp) = (Subgroup.genLTOne (valueGroup (.ofClass v))) by
    simp [← this]
  apply Subgroup.genLTOne_unique
  · exact compareOfLessAndEq_eq_lt.mp rfl
  · ext n
    simp_all only [Int.reduceNeg, exp_neg, Subgroup.mem_zpowers_iff, mem_valueGroup_iff_of_comm,
      ne_eq]
    refine ⟨fun ⟨k, h⟩ => ?_ , fun _ => ⟨-WithZero.log n, by aesop⟩⟩
    rw [← h]
    have ⟨π, hπ⟩ := hπ
    cases k with
    | ofNat n => refine ⟨1, ?_, π ^ n, ?_⟩ <;> simp [hπ]
    | negSucc n => refine ⟨π ^ (n + 1), ?_, 1, ?_⟩ <;> simp [hπ, Int.negSucc_eq, mul_assoc]

/--
lemma `generator_eq_exp_neg_one_of_surjective` / 引理 `generator_eq_exp_neg_one_of_surjective`

English:
lemma generator_eq_exp_neg_one_of_surjective
  given: (hsurj : Function.Surjective v)
  proof: generator_eq_exp_neg_one_of_mem_range (by aesop)

@[deprecated generator_eq_exp_neg_one_of_surjective (since := "2026-04-01")]

中文:
引理 generator_eq_exp_neg_one_of_surjective
  条件: (hsurj : 函数.满射 v)
  证明: generator_eq_exp_neg_one_of_mem_range (by aesop)

@[deprecated generator_eq_exp_neg_one_of_surjective (since := "2026-04-01")]

Depends on / 依赖: generator_eq_exp_neg_one_of_mem_range
-/
lemma generator_eq_exp_neg_one_of_surjective (hsurj : Function.Surjective v) :
    hv.generator = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp) :=
  generator_eq_exp_neg_one_of_mem_range (by aesop)

@[deprecated generator_eq_exp_neg_one_of_surjective (since := "2026-04-01")]
/--
lemma `generator_eq_neg_exp_one_of_surjective` / 引理 `generator_eq_neg_exp_one_of_surjective`

English:
lemma generator_eq_neg_exp_one_of_surjective
  given: (hsurj : Function.Surjective v)
  proof: generator_eq_exp_neg_one_of_surjective hsurj

中文:
引理 generator_eq_neg_exp_one_of_surjective
  条件: (hsurj : 函数.满射 v)
  证明: generator_eq_exp_neg_one_of_surjective hsurj

Depends on / 依赖: generator_eq_exp_neg_one_of_surjective
-/
lemma generator_eq_neg_exp_one_of_surjective (hsurj : Function.Surjective v) :
    hv.generator = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp) :=
  generator_eq_exp_neg_one_of_surjective hsurj

end WithZeroMulInt

end IsRankOneDiscrete

section IsRankOneDiscrete

variable [hv : IsRankOneDiscrete v]

/--
Definition of `IsUniformizer` / `IsUniformizer` 的定义

English:
definition IsUniformizer
  signature: (π : A)
  body: v π = hv.generator

中文:
定义 IsUniformizer
  签名: (π : A)
  定义体: v π = hv.generator

Depends on / 依赖: generator, hv.generator
-/
def IsUniformizer (π : A) : Prop := v π = hv.generator

variable {v} {π : A}

namespace IsUniformizer

/--
theorem `iff` / 定理 `iff`

English:
theorem iff
  statement: v.IsUniformizer π ↔ v π = hv.generator
  proof: refl _

中文:
定理 iff
  结论: v.IsUniformizer π ↔ v π = hv.generator
  证明: refl _
-/
theorem iff : v.IsUniformizer π ↔ v π = hv.generator := refl _

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (hπ : IsUniformizer v π)
  statement: π != 0
  proof: by
  intro h0
  rw [h0]; rw [IsUniformizer]; rw [map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

@[simp]

中文:
定理 ne_zero
  条件: (hπ : IsUniformizer v π)
  结论: π != 0
  证明: by
  intro h0
  rw [h0]; rw [IsUniformizer]; rw [map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

@[simp]

Depends on / 依赖: IsUniformizer, Units.ne_zero, map_zero, ne_zero
-/
theorem ne_zero (hπ : IsUniformizer v π) : π != 0 := by
  intro h0
  rw [h0]; rw [IsUniformizer]; rw [map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

@[simp]
/--
lemma `val` / 引理 `val`

English:
lemma val
  given: (hπ : v.IsUniformizer π)
  statement: v π = hv.generator
  proof: hπ

中文:
引理 val
  条件: (hπ : v.IsUniformizer π)
  结论: v π = hv.generator
  证明: hπ
-/
lemma val (hπ : v.IsUniformizer π) : v π = hv.generator := hπ

/--
lemma `val_lt_one` / 引理 `val_lt_one`

English:
lemma val_lt_one
  given: (hπ : v.IsUniformizer π)
  statement: v π < 1
  proof: hπ ▸ hv.generator_lt_one

中文:
引理 val_lt_one
  条件: (hπ : v.IsUniformizer π)
  结论: v π < 1
  证明: hπ ▸ hv.generator_lt_one

Depends on / 依赖: generator_lt_one, hv.generator_lt_one
-/
lemma val_lt_one (hπ : v.IsUniformizer π) : v π < 1 := hπ ▸ hv.generator_lt_one

/--
lemma `val_ne_zero` / 引理 `val_ne_zero`

English:
lemma val_ne_zero
  given: (hπ : v.IsUniformizer π)
  statement: v π != 0
  proof: by
  by_contra h0
  simp only [IsUniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ

中文:
引理 val_ne_zero
  条件: (hπ : v.IsUniformizer π)
  结论: v π != 0
  证明: by
  by_contra h0
  simp only [IsUniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ

Depends on / 依赖: IsUniformizer, Units.ne_zero, ne_zero
-/
lemma val_ne_zero (hπ : v.IsUniformizer π) : v π != 0 := by
  by_contra h0
  simp only [IsUniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ

/--
theorem `val_pos` / 定理 `val_pos`

English:
theorem val_pos
  given: (hπ : IsUniformizer v π)
  statement: 0 < v π
  proof: by
  rw [IsUniformizer.iff] at hπ; simp [zero_lt_iff, ne_eq, hπ]

中文:
定理 val_pos
  条件: (hπ : IsUniformizer v π)
  结论: 0 < v π
  证明: by
  rw [IsUniformizer.iff] at hπ; simp [zero_lt_iff, ne_eq, hπ]

Depends on / 依赖: IsUniformizer, IsUniformizer.iff, ne_eq, zero_lt_iff
-/
theorem val_pos (hπ : IsUniformizer v π) : 0 < v π := by
  rw [IsUniformizer.iff] at hπ; simp [zero_lt_iff, ne_eq, hπ]

/--
lemma `zpowers_eq_valueGroup` / 引理 `zpowers_eq_valueGroup`

English:
lemma zpowers_eq_valueGroup
  given: (hπ : v.IsUniformizer π)
  proof: by
  rw [← (valueGroup (.ofClass v)).genLTOne_zpowers_eq_top]
  congr
  simp only [val, Units.mk0_val, hπ]
  exact IsRankOneDiscrete.valueGroup_genLTOne_eq_generator v

中文:
引理 zpowers_eq_valueGroup
  条件: (hπ : v.IsUniformizer π)
  证明: by
  rw [← (valueGroup (.ofClass v)).genLTOne_zpowers_eq_top]
  congr
  simp only [val, Units.mk0_val, hπ]
  exact IsRankOneDiscrete.valueGroup_genLTOne_eq_generator v

Depends on / 依赖: IsRankOneDiscrete, IsRankOneDiscrete.valueGroup_genLTOne_eq_generator, Units.mk0_val, genLTOne_zpowers_eq_top, mk0_val, ofClass, valueGroup, valueGroup_genLTOne_eq_generator
-/
lemma zpowers_eq_valueGroup (hπ : v.IsUniformizer π) :
    valueGroup (.ofClass v) = zpowers (Units.mk0 (v π) hπ.val_ne_zero) := by
  rw [← (valueGroup (.ofClass v)).genLTOne_zpowers_eq_top]
  congr
  simp only [val, Units.mk0_val, hπ]
  exact IsRankOneDiscrete.valueGroup_genLTOne_eq_generator v

end IsUniformizer

variable (v) in
/-- The structure `Uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer. -/
@[ext]
/--
Definition of `Uniformizer` / `Uniformizer` 的定义

English:
structure Uniformizer
  parameters: where
  axioms and operations (2):
    - val : v.integer
    - valuation_gt_one : v.IsUniformizer val

中文:
结构 一致化子
  参数: where
  公理与运算 (2 个):
    - val : v.integer
    - valuation_gt_one : v.IsUniformizer val
-/
structure Uniformizer where
  /-- The integer underlying a `Uniformizer` -/
  val : v.integer
  valuation_gt_one : v.IsUniformizer val

namespace Uniformizer

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {x : A} (hx : v.IsUniformizer x)
  body: ⟨x, le_of_lt hx.val_lt_one⟩
  valuation_gt_one := hx

@[simp]

中文:
定义 mk'
  签名: {x : A} (hx : v.IsUniformizer x)
  定义体: ⟨x, le_of_lt hx.val_lt_one⟩
  valuation_gt_one := hx

@[simp]

Depends on / 依赖: hx.val_lt_one, le_of_lt, val_lt_one
-/
def mk' {x : A} (hx : v.IsUniformizer x) : v.Uniformizer where
  val := ⟨x, le_of_lt hx.val_lt_one⟩
  valuation_gt_one := hx

@[simp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe v.Uniformizer v.integer
  body: ⟨fun π => π.val⟩

中文:
实例 :
  签名: Coe v.一致化子 v.integer
  定义体: ⟨fun π => π.val⟩
-/
instance : Coe v.Uniformizer v.integer := ⟨fun π => π.val⟩

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (π : Uniformizer v)
  statement: π.1.1 != 0
  proof: π.2.ne_zero

中文:
定理 ne_zero
  条件: (π : 一致化子 v)
  结论: π.1.1 != 0
  证明: π.2.ne_zero

Depends on / 依赖: ne_zero
-/
theorem ne_zero (π : Uniformizer v) : π.1.1 != 0 := π.2.ne_zero

end Uniformizer

end IsRankOneDiscrete

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : Valuation R Γ} [hv : IsRankOneDiscrete v]

/--
theorem `IsUniformizer.not_isUnit` / 定理 `IsUniformizer.not_isUnit`

English:
theorem IsUniformizer.not_isUnit
  given: {π : v.integer} (hπ : IsUniformizer v π)
  statement: ¬ IsUnit π
  proof: fun h => ne_of_gt hπ.val_lt_one (Integers.one_of_isUnit (integer.integers v) h).symm

中文:
定理 IsUniformizer.not_isUnit
  条件: {π : v.integer} (hπ : IsUniformizer v π)
  结论: ¬ 是单位 π
  证明: fun h => ne_of_gt hπ.val_lt_one (Integers.one_of_isUnit (integer.integers v) h).symm

Depends on / 依赖: Integers, Integers.one_of_isUnit, integer, integer.integers, integers, ne_of_gt, one_of_isUnit, val_lt_one
-/
theorem IsUniformizer.not_isUnit {π : v.integer} (hπ : IsUniformizer v π) : ¬ IsUnit π :=
  fun h => ne_of_gt hπ.val_lt_one (Integers.one_of_isUnit (integer.integers v) h).symm

end CommRing

section Ring

variable {R : Type*} [Ring R] (v : Valuation R Γ) [IsCyclic (valueGroup (.ofClass v))]
  [Nontrivial (valueGroup (.ofClass v))]

/--
Instance `IsRankOneDiscrete.mk'` / 实例 `IsRankOneDiscrete.mk'`

English:
instance IsRankOneDiscrete.mk'
  signature: : IsRankOneDiscrete v
  body: ⟨(valueGroup (.ofClass v)).genLTOne, ⟨(valueGroup (.ofClass v)).genLTOne_zpowers_eq_top,
    (valueGroup (.ofClass v)).genLTOne_lt_one⟩⟩

中文:
实例 是RankOneDiscrete.mk'
  签名: : 是RankOneDiscrete v
  定义体: ⟨(valueGroup (.ofClass v)).genLTOne, ⟨(valueGroup (.ofClass v)).genLTOne_zpowers_eq_top,
    (valueGroup (.ofClass v)).genLTOne_lt_one⟩⟩

Depends on / 依赖: genLTOne, genLTOne_lt_one, genLTOne_zpowers_eq_top, ofClass, valueGroup
-/
instance IsRankOneDiscrete.mk' : IsRankOneDiscrete v :=
  ⟨(valueGroup (.ofClass v)).genLTOne, ⟨(valueGroup (.ofClass v)).genLTOne_zpowers_eq_top,
    (valueGroup (.ofClass v)).genLTOne_lt_one⟩⟩

end Ring

section Field

open Ideal IsLocalRing Valuation.IsRankOneDiscrete

variable {K : Type*} [Field K] (v : Valuation K Γ)

/- When the valuation is defined over a field instead that simply on a (commutative) ring, we use
the notion of `valuationSubring` instead of the weaker one of `integer` to access the
corresponding API. -/
local notation "K₀" => v.valuationSubring

section IsNontrivial

variable [IsCyclic (valueGroup (.ofClass v))] [Nontrivial (valueGroup (.ofClass v))]

/--
theorem `exists_isUniformizer_of_isCyclic_of_nontrivial` / 定理 `exists_isUniformizer_of_isCyclic_of_nontrivial`

English:
theorem exists_isUniformizer_of_isCyclic_of_nontrivial
  statement: exists π : K₀, IsUniformizer v (π : K)
  proof: by
  simp only [IsUniformizer.iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  set g := (valueGroup (.ofClass v)).genLTOne with hg
  obtain ⟨⟨π, hπ⟩, hγ0⟩ : g.1 in ((range (MonoidWithZeroHom.ofClass v)) \ {0}) := by
    rw [← valueGroup_eq_range]; rw [hg]
    exact mem_image_of_mem Units.val (valueGroup (.ofClass v)).genLTOne_mem
  use π
  simp only [MonoidWithZeroHom.coe_ofClass] at hπ
  rw [hπ]; rw [hg]
  exact ⟨le_of_lt (valueGroup (.ofClass v)).genLTOne_lt_one,
    by rw [valueGroup_genLTOne_eq_generator]⟩

中文:
定理 存在_isUniformizer_of_isCyclic_of_nontrivial
  结论: 存在 π : K₀, IsUniformizer v (π : K)
  证明: by
  simp only [IsUniformizer.iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  set g := (valueGroup (.ofClass v)).genLTOne with hg
  obtain ⟨⟨π, hπ⟩, hγ0⟩ : g.1 in ((range (MonoidWithZeroHom.ofClass v)) \ {0}) := by
    rw [← valueGroup_eq_range]; rw [hg]
    exact mem_image_of_mem Units.val (valueGroup (.ofClass v)).genLTOne_mem
  use π
  simp only [MonoidWithZeroHom.coe_ofClass] at hπ
  rw [hπ]; rw [hg]
  exact ⟨le_of_lt (valueGroup (.ofClass v)).genLTOne_lt_one,
    by rw [valueGroup_genLTOne_eq_generator]⟩

Depends on / 依赖: IsUniformizer, IsUniformizer.iff, MonoidWithZeroHom, MonoidWithZeroHom.coe_ofClass, MonoidWithZeroHom.ofClass, Subtype, Subtype.exists, Units.val, coe_ofClass, exists_prop, genLTOne, genLTOne_lt_one, genLTOne_mem, le_of_lt, mem_image_of_mem, mem_valuationSubring_iff, ofClass, valueGroup, valueGroup_eq_range, valueGroup_genLTOne_eq_generator
-/
theorem exists_isUniformizer_of_isCyclic_of_nontrivial : exists π : K₀, IsUniformizer v (π : K) := by
  simp only [IsUniformizer.iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  set g := (valueGroup (.ofClass v)).genLTOne with hg
  obtain ⟨⟨π, hπ⟩, hγ0⟩ : g.1 in ((range (MonoidWithZeroHom.ofClass v)) \ {0}) := by
    rw [← valueGroup_eq_range]; rw [hg]
    exact mem_image_of_mem Units.val (valueGroup (.ofClass v)).genLTOne_mem
  use π
  simp only [MonoidWithZeroHom.coe_ofClass] at hπ
  rw [hπ]; rw [hg]
  exact ⟨le_of_lt (valueGroup (.ofClass v)).genLTOne_lt_one,
    by rw [valueGroup_genLTOne_eq_generator]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (Uniformizer v)
  body: ⟨⟨(exists_isUniformizer_of_isCyclic_of_nontrivial v).choose,
    (exists_isUniformizer_of_isCyclic_of_nontrivial v).choose_spec⟩⟩

中文:
实例 :
  签名: 非空 (一致化子 v)
  定义体: ⟨⟨(exists_isUniformizer_of_isCyclic_of_nontrivial v).choose,
    (exists_isUniformizer_of_isCyclic_of_nontrivial v).choose_spec⟩⟩

Depends on / 依赖: choose_spec, exists_isUniformizer_of_isCyclic_of_nontrivial
-/
instance : Nonempty (Uniformizer v) :=
  ⟨⟨(exists_isUniformizer_of_isCyclic_of_nontrivial v).choose,
    (exists_isUniformizer_of_isCyclic_of_nontrivial v).choose_spec⟩⟩

end IsNontrivial

section IsRankOneDiscrete

section Uniformizer

variable {v} [hv : v.IsRankOneDiscrete]

/--
theorem `IsUniformizer.of_associated` / 定理 `IsUniformizer.of_associated`

English:
theorem IsUniformizer.of_associated
  statement: {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
  proof: by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 := (Integers.isUnit_iff_valuation_eq_one <| integer.integers v).mp u.isUnit
  rwa [IsUniformizer.iff, ← hu, Subring.coe_mul, map_mul, this, mul_one, ← IsUniformizer.iff]

中文:
定理 IsUniformizer.of_associated
  结论: {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
  证明: by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 := (Integers.isUnit_iff_valuation_eq_one <| integer.integers v).mp u.isUnit
  rwa [IsUniformizer.iff, ← hu, Subring.coe_mul, map_mul, this, mul_one, ← IsUniformizer.iff]

Depends on / 依赖: Integers, Integers.isUnit_iff_valuation_eq_one, IsUniformizer, IsUniformizer.iff, Subring, Subring.coe_mul, coe_mul, integer, integer.integers, integers, isUnit, isUnit_iff_valuation_eq_one, map_mul, mul_one, u.isUnit
-/
theorem IsUniformizer.of_associated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (H : Associated π₁ π₂) : IsUniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 := (Integers.isUnit_iff_valuation_eq_one <| integer.integers v).mp u.isUnit
  rwa [IsUniformizer.iff, ← hu, Subring.coe_mul, map_mul, this, mul_one, ← IsUniformizer.iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `associated_of_isUniformizer` / 定理 `associated_of_isUniformizer`

English:
theorem associated_of_isUniformizer
  statement: {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
  proof: by
  have hval : v ((π₁ : K)⁻¹ * π₂) = 1 := by
    simp [IsUniformizer.iff.mp h1, IsUniformizer.iff.mp h2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑) : K₀ -> K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ h1.ne_zero]

中文:
定理 associated_of_isUniformizer
  结论: {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
  证明: by
  have hval : v ((π₁ : K)⁻¹ * π₂) = 1 := by
    simp [IsUniformizer.iff.mp h1, IsUniformizer.iff.mp h2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑) : K₀ -> K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ h1.ne_zero]

Depends on / 依赖: Integers, Integers.isUnit_iff_valuation_eq_one, IsUniformizer, IsUniformizer.iff.mp, Subtype, Subtype.val_injective, apply_fun, h1.ne_zero, integer, integer.integers, integers, isUnit_iff_valuation_eq_one, le_of_eq, mem_integer_iff, mul_assoc, ne_zero, v.integer, v.mem_integer_iff, val_injective
-/
theorem associated_of_isUniformizer {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (h2 : IsUniformizer v π₂) : Associated π₁ π₂ := by
  have hval : v ((π₁ : K)⁻¹ * π₂) = 1 := by
    simp [IsUniformizer.iff.mp h1, IsUniformizer.iff.mp h2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑) : K₀ -> K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ h1.ne_zero]

/--
theorem `exists_pow_Uniformizer` / 定理 `exists_pow_Uniformizer`

English:
theorem exists_pow_Uniformizer
  given: {r : K₀} (hr : r != 0) (π : Uniformizer v)
  proof: by
  have hr₀ : v r != 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr : Γˣ := Units.mk0 (v r) hr₀ with hvr_def
  have hvr : vr in (valueGroup (.ofClass v)) := by
    apply mem_valueGroup
    rw [hvr_def]; rw [Units.val_mk0 hr₀]
    exact mem_range_self _
  rw [π.2.zpowers_eq_valueGroup]; rw [mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    rw [← Units.val_mk0 hr₀]; rw [← hm]
    simp [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hm₀ : 0 <= m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ π.2.val_pos π.2.val_lt_one]; rw [hm']
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [map_mul]; rw [map_zpow₀]; rw [← hm']; rw [zpow_neg]; rw [hm']; rw [inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) != 0 := by
    simp only [zpow_neg, ne_eq, mul_eq_zero, inv_eq_zero, ZeroMemClass.coe_eq_zero, not_or, ha]
    refine ⟨?_, hr⟩
    rw [hn]; rw [zpow_natCast]; rw [pow_eq_zero_iff']; rw [not_and_or]
    exact Or.inl π.ne_zero
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec]; rw [Subring.coe_pow]; rw [ha]; rw [← mul_assoc]; rw [zpow_neg]; rw [hn]; rw [zpow_natCast]; rw [mul_inv_cancel₀ (pow_ne_zero _ π.ne_zero)]; rw [one_mul]

中文:
定理 存在_pow_Uniformizer
  条件: {r : K₀} (hr : r != 0) (π : 一致化子 v)
  证明: by
  have hr₀ : v r != 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr : Γˣ := Units.mk0 (v r) hr₀ with hvr_def
  have hvr : vr in (valueGroup (.ofClass v)) := by
    apply mem_valueGroup
    rw [hvr_def]; rw [Units.val_mk0 hr₀]
    exact mem_range_self _
  rw [π.2.zpowers_eq_valueGroup]; rw [mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    rw [← Units.val_mk0 hr₀]; rw [← hm]
    simp [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hm₀ : 0 <= m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ π.2.val_pos π.2.val_lt_one]; rw [hm']
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [map_mul]; rw [map_zpow₀]; rw [← hm']; rw [zpow_neg]; rw [hm']; rw [inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) != 0 := by
    simp only [zpow_neg, ne_eq, mul_eq_zero, inv_eq_zero, ZeroMemClass.coe_eq_zero, not_or, ha]
    refine ⟨?_, hr⟩
    rw [hn]; rw [zpow_natCast]; rw [pow_eq_zero_iff']; rw [not_and_or]
    exact Or.inl π.ne_zero
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec]; rw [Subring.coe_pow]; rw [ha]; rw [← mul_assoc]; rw [zpow_neg]; rw [hn]; rw [zpow_natCast]; rw [mul_inv_cancel₀ (pow_ne_zero _ π.ne_zero)]; rw [one_mul]

Depends on / 依赖: Subring, Subring.coe_eq_zero_iff, Units.mk0, Units.val_mk0, Units.val_zpow_eq_zpow_val, coe_eq_zero_iff, hvr_def, mem_range_self, mem_valueGroup, mem_zpowers_iff, ne_eq, ofClass, val_mk0, val_zpow_eq_zpow_val, valueGroup, zero_iff, zpowers_eq_valueGroup
-/
theorem exists_pow_Uniformizer {r : K₀} (hr : r != 0) (π : Uniformizer v) :
    exists n : Nat, exists u : K₀ˣ, r = (π.1 ^ n).1 * u.1 := by
  have hr₀ : v r != 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr : Γˣ := Units.mk0 (v r) hr₀ with hvr_def
  have hvr : vr in (valueGroup (.ofClass v)) := by
    apply mem_valueGroup
    rw [hvr_def]; rw [Units.val_mk0 hr₀]
    exact mem_range_self _
  rw [π.2.zpowers_eq_valueGroup]; rw [mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    rw [← Units.val_mk0 hr₀]; rw [← hm]
    simp [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hm₀ : 0 <= m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ π.2.val_pos π.2.val_lt_one]; rw [hm']
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [map_mul]; rw [map_zpow₀]; rw [← hm']; rw [zpow_neg]; rw [hm']; rw [inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) != 0 := by
    simp only [zpow_neg, ne_eq, mul_eq_zero, inv_eq_zero, ZeroMemClass.coe_eq_zero, not_or, ha]
    refine ⟨?_, hr⟩
    rw [hn]; rw [zpow_natCast]; rw [pow_eq_zero_iff']; rw [not_and_or]
    exact Or.inl π.ne_zero
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec]; rw [Subring.coe_pow]; rw [ha]; rw [← mul_assoc]; rw [zpow_neg]; rw [hn]; rw [zpow_natCast]; rw [mul_inv_cancel₀ (pow_ne_zero _ π.ne_zero)]; rw [one_mul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Uniformizer.is_generator` / 定理 `Uniformizer.is_generator`

English:
theorem Uniformizer.is_generator
  given: (π : Uniformizer v)
  proof: by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply π.2.not_isUnit h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp [hx₀]
    · obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
      rw [← Subring.coe_mul]; rw [Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h =>
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n != 0 := fun h => by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp [Ideal.mem_span_singleton, hu, dvd_pow_self _ hn]

中文:
定理 一致化子.is_generator
  条件: (π : 一致化子 v)
  证明: by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply π.2.not_isUnit h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp [hx₀]
    · obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
      rw [← Subring.coe_mul]; rw [Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h =>
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n != 0 := fun h => by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp [Ideal.mem_span_singleton, hu, dvd_pow_self _ hn]

Depends on / 依赖: Ideal.mem_span_singleto, Ideal.span_singleton_eq_top, IsUnit, Subring, Subring.coe_mul, Subtype, Subtype.coe_inj, Units.isUnit, coe_inj, coe_mul, eq_of_le, eq_top_of_isUnit_mem, exists_pow_Uniformizer, isMaximal, isUnit, maximalIdeal, maximalIdeal.isMaximal, mem_span_singleto, ne_top, not_isUnit
-/
theorem Uniformizer.is_generator (π : Uniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} := by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply π.2.not_isUnit h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp [hx₀]
    · obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
      rw [← Subring.coe_mul]; rw [Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h =>
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n != 0 := fun h => by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp [Ideal.mem_span_singleton, hu, dvd_pow_self _ hn]

/--
theorem `IsUniformizer.is_generator` / 定理 `IsUniformizer.is_generator`

English:
theorem IsUniformizer.is_generator
  given: {π : v.valuationSubring} (hπ : IsUniformizer v π)
  proof: Uniformizer.is_generator ⟨π, hπ⟩

中文:
定理 IsUniformizer.is_generator
  条件: {π : v.valuationSubring} (hπ : IsUniformizer v π)
  证明: Uniformizer.is_generator ⟨π, hπ⟩

Depends on / 依赖: Uniformizer, Uniformizer.is_generator, is_generator
-/
theorem IsUniformizer.is_generator {π : v.valuationSubring} (hπ : IsUniformizer v π) :
    maximalIdeal v.valuationSubring = Ideal.span {π} :=
  Uniformizer.is_generator ⟨π, hπ⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pow_Uniformizer_is_pow_generator` / 定理 `pow_Uniformizer_is_pow_generator`

English:
theorem pow_Uniformizer_is_pow_generator
  given: (π : Uniformizer v) (n : Nat)
  proof: by
  rw [← Ideal.span_singleton_pow]; rw [Uniformizer.is_generator]

中文:
定理 pow_Uniformizer_is_pow_generator
  条件: (π : 一致化子 v) (n : 自然数)
  证明: by
  rw [← Ideal.span_singleton_pow]; rw [Uniformizer.is_generator]

Depends on / 依赖: Ideal.span_singleton_pow, Uniformizer, Uniformizer.is_generator, is_generator, span_singleton_pow
-/
theorem pow_Uniformizer_is_pow_generator (π : Uniformizer v) (n : Nat) :
    maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow]; rw [Uniformizer.is_generator]

end Uniformizer

end IsRankOneDiscrete

/--
theorem `valuationSubring_not_isField` / 定理 `valuationSubring_not_isField`

English:
theorem valuationSubring_not_isField
  statement: [Nontrivial (valueGroup (.ofClass v))]
  proof: by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

中文:
定理 valuationSubring_not_isField
  结论: [非平凡 (valueGroup (.ofClass v))]
  证明: by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

Depends on / 依赖: Subring, Subring.coe_eq_zero_iff, coe_eq_zero_iff, exists_isUniformizer_of_isCyclic_of_nontrivial, isUnit_iff_exists_inv, ne_eq, ne_zero, not_isUnit, specialize
-/
theorem valuationSubring_not_isField [Nontrivial (valueGroup (.ofClass v))]
    [IsCyclic (valueGroup (.ofClass v))] : ¬ IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUniformizer_of_maximalIdeal_eq_span` / 定理 `isUniformizer_of_maximalIdeal_eq_span`

English:
theorem isUniformizer_of_maximalIdeal_eq_span
  statement: [v.IsRankOneDiscrete] {r : K₀}
  proof: by
  have hr₀ : r != 0 := by
    intro h
    rw [h]; rw [Set.singleton_zero]; rw [span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (valuationSubring_not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := exists_pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π]; rw [hπ⟩]; rw [span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

中文:
定理 isUniformizer_of_maximalIdeal_eq_span
  结论: [v.是RankOneDiscrete] {r : K₀}
  证明: by
  have hr₀ : r != 0 := by
    intro h
    rw [h]; rw [Set.singleton_zero]; rw [span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (valuationSubring_not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := exists_pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π]; rw [hπ⟩]; rw [span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

Depends on / 依赖: Ring.ne_bot_of_isMaximal_of_not_isField, Set.singleton_zero, Uniformizer, Uniformizer.is_generator, exists_isUniformizer_of_isCyclic_of_nontrivial, exists_pow_Uniformizer, isMaximal, is_generator, maximalIdeal, maximalIdeal.isMaximal, ne_bot_of_isMaximal_of_not_isField, of_associated, singleton_zero, span_singleton_eq_span_singleton, span_zero, v.valuationSubring, valuationSubring, valuationSubring_not_isField
-/
theorem isUniformizer_of_maximalIdeal_eq_span [v.IsRankOneDiscrete] {r : K₀}
    (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsUniformizer v r := by
  have hr₀ : r != 0 := by
    intro h
    rw [h]; rw [Set.singleton_zero]; rw [span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (valuationSubring_not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := exists_pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π]; rw [hπ⟩]; rw [span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ideal_isPrincipal` / 定理 `ideal_isPrincipal`

English:
theorem ideal_isPrincipal
  statement: [IsCyclic (valueGroup (.ofClass v))]
  proof: by
  suffices forall P : Ideal K₀, P.IsPrime -> Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu]; rw [Ideal.mul_unit_mem_iff_mem P u.isUnit]; rw [IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn)]; rw [← Ideal.span_singleton_le_iff_mem] at hx_mem
      replace hx_mem := π.is_generator ▸ hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, π.is_generator⟩

中文:
定理 ideal_isPrincipal
  结论: [是循环 (valueGroup (.ofClass v))]
  证明: by
  suffices forall P : Ideal K₀, P.IsPrime -> Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu]; rw [Ideal.mul_unit_mem_iff_mem P u.isUnit]; rw [IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn)]; rw [← Ideal.span_singleton_le_iff_mem] at hx_mem
      replace hx_mem := π.is_generator ▸ hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, π.is_generator⟩

Depends on / 依赖: IsPrime, IsPrincipal, IsPrincipalIdealRing, IsPrincipalIdealRing.of_prime, Nonempty, Nonempty.some, P.IsPrime, SetLike, SetLike.coe_eq_coe, Submodule, Submodule.IsPrincipal, Submodule.exists_mem_ne_zero_of_ne_bot, Subring, Subring.coe_mul, Uniformizer, bot_isPrincipal, coe_eq_coe, coe_mul, exists_mem_ne_zero_of_ne_bot, exists_pow_Uniformizer
-/
theorem ideal_isPrincipal [IsCyclic (valueGroup (.ofClass v))]
    [Nontrivial (valueGroup (.ofClass v))] (I : Ideal K₀) : I.IsPrincipal := by
  suffices forall P : Ideal K₀, P.IsPrime -> Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu]; rw [Ideal.mul_unit_mem_iff_mem P u.isUnit]; rw [IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn)]; rw [← Ideal.span_singleton_le_iff_mem] at hx_mem
      replace hx_mem := π.is_generator ▸ hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, π.is_generator⟩

/--
theorem `valuationSubring_isPrincipalIdealRing` / 定理 `valuationSubring_isPrincipalIdealRing`

English:
theorem valuationSubring_isPrincipalIdealRing
  statement: [IsCyclic (valueGroup (.ofClass v))]
  proof: ⟨(ideal_isPrincipal v ·)⟩

中文:
定理 valuationSubring_isPrincipalIdealRing
  结论: [是循环 (valueGroup (.ofClass v))]
  证明: ⟨(ideal_isPrincipal v ·)⟩

Depends on / 依赖: ideal_isPrincipal
-/
theorem valuationSubring_isPrincipalIdealRing [IsCyclic (valueGroup (.ofClass v))]
    [Nontrivial (valueGroup (.ofClass v))] : IsPrincipalIdealRing K₀ :=
  ⟨(ideal_isPrincipal v ·)⟩

/--
Instance `valuationSubring_isDiscreteValuationRing` / 实例 `valuationSubring_isDiscreteValuationRing`

English:
instance valuationSubring_isDiscreteValuationRing
  signature: [IsCyclic (valueGroup (.ofClass v))]
  body: valuationSubring_isPrincipalIdealRing v
  toIsLocalRing := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact valuationSubring_not_isField v

中文:
实例 valuationSubring_isDiscreteValuationRing
  签名: [是循环 (valueGroup (.ofClass v))]
  定义体: valuationSubring_isPrincipalIdealRing v
  toIsLocalRing := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact valuationSubring_not_isField v

Depends on / 依赖: valuationSubring_isPrincipalIdealRing
-/
instance valuationSubring_isDiscreteValuationRing [IsCyclic (valueGroup (.ofClass v))]
    [Nontrivial (valueGroup (.ofClass v))] : IsDiscreteValuationRing K₀ where
  toIsPrincipalIdealRing := valuationSubring_isPrincipalIdealRing v
  toIsLocalRing := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact valuationSubring_not_isField v

end Field

end Valuation
