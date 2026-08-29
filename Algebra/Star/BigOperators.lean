/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Big-operators lemmas about `star` algebraic operations

These results are kept separate from `Algebra.Star.Basic` to avoid it needing to import `Finset`.
-/

public section


variable {R : Type*}

@[simp]
/--
theorem `star_prod` / 定理 `star_prod`

English:
theorem star_prod
  given: [CommMonoid R] [StarMul R] {α : Type*} (s : Finset α) (f : α -> R)
  proof: map_prod (starMulAut : R ≃* R) _ _

@[simp]

中文:
定理 star_prod
  条件: [CommMonoid R] [StarMul R] {α : 类型} (s : Finset α) (f : α -> R)
  证明: map_prod (starMulAut : R ≃* R) _ _

@[simp]

Depends on / 依赖: map_prod, starMulAut
-/
theorem star_prod [CommMonoid R] [StarMul R] {α : Type*} (s : Finset α) (f : α -> R) :
    star (∏ x in s, f x) = ∏ x in s, star (f x) := map_prod (starMulAut : R ≃* R) _ _

@[simp]
/--
theorem `star_sum` / 定理 `star_sum`

English:
theorem star_sum
  given: [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : Finset α) (f : α -> R)
  proof: map_sum (starAddEquiv : R ≃+ R) _ _

@[aesop safe apply (rule_sets := [CStarAlgebra])]

中文:
定理 star_sum
  条件: [AddCommMonoid R] [StarAddMonoid R] {α : 类型} (s : Finset α) (f : α -> R)
  证明: map_sum (starAddEquiv : R ≃+ R) _ _

@[aesop safe apply (rule_sets := [CStarAlgebra])]

Depends on / 依赖: map_sum, starAddEquiv
-/
theorem star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : Finset α) (f : α -> R) :
    star (∑ x in s, f x) = ∑ x in s, star (f x) := map_sum (starAddEquiv : R ≃+ R) _ _

@[aesop safe apply (rule_sets := [CStarAlgebra])]
/--
theorem `isSelfAdjoint_sum` / 定理 `isSelfAdjoint_sum`

English:
theorem isSelfAdjoint_sum
  statement: {ι : Type*} [AddCommMonoid R] [StarAddMonoid R] (s : Finset ι)
  proof: by
  simpa [IsSelfAdjoint, star_sum] using Finset.sum_congr rfl fun _ hi => h _ hi

@[simp]

中文:
定理 isSelfAdjoint_sum
  结论: {ι : 类型} [AddCommMonoid R] [StarAddMonoid R] (s : Finset ι)
  证明: by
  simpa [IsSelfAdjoint, star_sum] using Finset.sum_congr rfl fun _ hi => h _ hi

@[simp]

Depends on / 依赖: Finset, Finset.sum_congr, IsSelfAdjoint, star_sum, sum_congr
-/
theorem isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [StarAddMonoid R] (s : Finset ι)
    {x : ι -> R} (h : forall i in s, IsSelfAdjoint (x i)) : IsSelfAdjoint (∑ i in s, x i) := by
  simpa [IsSelfAdjoint, star_sum] using Finset.sum_congr rfl fun _ hi => h _ hi

@[simp]
/--
theorem `star_finsuppSum` / 定理 `star_finsuppSum`

English:
theorem star_finsuppSum
  statement: {ι : Type*} {M : Type*} [Zero M] [AddCommMonoid R] [StarAddMonoid R]
  proof: by
  simp [Finsupp.sum]

@[simp]

中文:
定理 star_finsuppSum
  结论: {ι : 类型} {M : 类型} [Zero M] [AddCommMonoid R] [StarAddMonoid R]
  证明: by
  simp [Finsupp.sum]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum
-/
theorem star_finsuppSum {ι : Type*} {M : Type*} [Zero M] [AddCommMonoid R] [StarAddMonoid R]
    (s : ι ->₀ M) (f : ι -> M -> R) : star (s.sum f) = s.sum (fun i m => star f i m) := by
  simp [Finsupp.sum]

@[simp]
/--
theorem `star_finsuppProd` / 定理 `star_finsuppProd`

English:
theorem star_finsuppProd
  statement: {ι : Type*} {M : Type*} [Zero M] [CommMonoid R] [StarMul R]
  proof: by
  simp [Finsupp.prod]

中文:
定理 star_finsuppProd
  结论: {ι : 类型} {M : 类型} [Zero M] [CommMonoid R] [StarMul R]
  证明: by
  simp [Finsupp.prod]

Depends on / 依赖: Finsupp, Finsupp.prod
-/
theorem star_finsuppProd {ι : Type*} {M : Type*} [Zero M] [CommMonoid R] [StarMul R]
    (s : ι ->₀ M) (f : ι -> M -> R) : star (s.prod f) = s.prod (fun i m => star f i m) := by
  simp [Finsupp.prod]
