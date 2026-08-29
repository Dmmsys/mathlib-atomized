/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Intermediate Fields of Rational Function Fields

Results relating `IntermediateField` and `RatFunc`.
-/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial Algebra

@[expose] public section

variable (f : K⟮X⟯)

/--
theorem `adjoin_X` / 定理 `adjoin_X`

English:
theorem adjoin_X
  statement: K⟮(X : K⟮X⟯)⟯ = ⊤
  proof: eq_top_iff.mpr fun g _ => (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

中文:
定理 adjoin_X
  结论: K⟮(X : K⟮X⟯)⟯ = ⊤
  证明: eq_top_iff.mpr fun g _ => (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, g.denom, g.num, mem_adjoin_simple_iff
-/
theorem adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ => (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

/--
theorem `IntermediateField.adjoin_X` / 定理 `IntermediateField.adjoin_X`

English:
theorem IntermediateField.adjoin_X
  given: (E : IntermediateField K K⟮X⟯)
  proof: by
  rw [← restrictScalars_eq_top_iff (K := K)]; rw [IntermediateField.restrictScalars_adjoin]; rw [_root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

中文:
定理 中间域.adjoin_X
  条件: (E : 中间域 K K⟮X⟯)
  证明: by
  rw [← restrictScalars_eq_top_iff (K := K)]; rw [IntermediateField.restrictScalars_adjoin]; rw [_root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

Depends on / 依赖: IntermediateField, IntermediateField.restrictScalars_adjoin, RatFunc, RatFunc.adjoin_X.symm, _root_, _root_.eq_top_iff, adjoin, adjoin.mono, adjoin_X, eq_top_iff, le_of_eq, le_trans, restrictScalars_adjoin, restrictScalars_eq_top_iff
-/
theorem IntermediateField.adjoin_X (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K)]; rw [IntermediateField.restrictScalars_adjoin]; rw [_root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

/--
Definition of `IntermediateField.adjoinXEquiv` / `IntermediateField.adjoinXEquiv` 的定义

English:
definition IntermediateField.adjoinXEquiv
  signature: (E : IntermediateField K K⟮X⟯)
  body: (equivOfEq (adjoin_X E)).trans topEquiv

中文:
定义 中间域.adjoinXEquiv
  签名: (E : 中间域 K K⟮X⟯)
  定义体: (equivOfEq (adjoin_X E)).trans topEquiv

Depends on / 依赖: adjoin_X, equivOfEq, topEquiv
-/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯ :=
  (equivOfEq (adjoin_X E)).trans topEquiv

/--
Definition of `minpolyX` / `minpolyX` 的定义

English:
abbreviation minpolyX
  signature: (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A]
  body: f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

中文:
缩写 minpolyX
  签名: (A : 类型) [交换环 A] [代数 K A] [代数 K[f] A]
  定义体: f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

Depends on / 依赖: Polynomial, Polynomial.C, algebraMap, f.denom.map, f.num.map, self_mem_adjoin_singleton
-/
noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

/--
theorem `minpolyX_map` / 定理 `minpolyX_map`

English:
theorem minpolyX_map
  statement: (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
  proof: by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]

中文:
定理 minpolyX_map
  结论: (A : 类型) [交换环 A] [代数 K A] [代数 (代数.adjoin K {f}) A]
  证明: by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq, Polynomial, Polynomial.map_map, algebraMap_apply, algebraMap_eq, map_map, minpolyX
-/
theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
/--
theorem `C_minpolyX` / 定理 `C_minpolyX`

English:
theorem C_minpolyX
  given: (x : K)
  statement: (C x).minpolyX K⟮C x⟯ = 0
  proof: by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]

中文:
定理 C_minpolyX
  条件: (x : K)
  结论: (C x).minpolyX K⟮C x⟯ = 0
  证明: by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, minpolyX, sub_eq_zero
-/
theorem C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0 := by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]

/--
theorem `minpolyX_aeval_X` / 定理 `minpolyX_aeval_X`

English:
theorem minpolyX_aeval_X
  statement: (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0
  proof: by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

中文:
定理 minpolyX_aeval_X
  结论: (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0
  证明: by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

Depends on / 依赖: IntermediateField, IntermediateField.algebraMap_apply, aeval_C, aeval_X_left_eq_algebraMap, aeval_map_algebraMap, aeval_sub, algebraMap_apply, algebraMap_ne_zero, coe_algebraMap, denom_ne_zero, f.denom_ne_zero, map_mul, nth_rw, num_div_denom, sub_self
-/
theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0 := by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

/--
theorem `eq_C_of_minpolyX_coeff_eq_zero` / 定理 `eq_C_of_minpolyX_coeff_eq_zero`

English:
theorem eq_C_of_minpolyX_coeff_eq_zero
  proof: by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀]; rw [eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero))]; rw [eq_comm]
  simpa [sub_eq_zero] using hf

中文:
定理 eq_C_of_minpolyX_coeff_eq_zero
  证明: by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀]; rw [eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero))]; rw [eq_comm]
  simpa [sub_eq_zero] using hf

Depends on / 依赖: _root_, _root_.map_ne_zero, denom_ne_zero, eq_comm, eq_div_iff, f.denom.leadingCoeff, f.denom.natDegree, f.denom_ne_zero, f.num.coeff, leadingCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, map_ne_zero, natDegree, sub_eq_zero
-/
theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)) : exists c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀]; rw [eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero))]; rw [eq_comm]
  simpa [sub_eq_zero] using hf

/--
theorem `minpolyX_eq_zero_iff` / 定理 `minpolyX_eq_zero_iff`

English:
theorem minpolyX_eq_zero_iff
  statement: (f.minpolyX K⟮f⟯) = 0 ↔ exists c, f = C c
  proof: ⟨fun h => f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

中文:
定理 minpolyX_eq_zero_iff
  结论: (f.minpolyX K⟮f⟯) = 0 ↔ 存在 c, f = C c
  证明: ⟨fun h => f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

Depends on / 依赖: eq_C_of_minpolyX_coeff_eq_zero, f.eq_C_of_minpolyX_coeff_eq_zero
-/
theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ exists c, f = C c :=
  ⟨fun h => f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

/--
theorem `isAlgebraic_adjoin_simple_X` / 定理 `isAlgebraic_adjoin_simple_X`

English:
theorem isAlgebraic_adjoin_simple_X
  given: (hf : ¬exists c, f = C c)
  statement: IsAlgebraic K⟮f⟯ (X : K⟮X⟯)
  proof: ⟨f.minpolyX K⟮f⟯, fun H => hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

中文:
定理 isAlgebraic_adjoin_simple_X
  条件: (hf : ¬存在 c, f = C c)
  结论: 是代数 K⟮f⟯ (X : K⟮X⟯)
  证明: ⟨f.minpolyX K⟮f⟯, fun H => hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

Depends on / 依赖: f.minpolyX, f.minpolyX_aeval_X, f.minpolyX_eq_zero_iff.mp, minpolyX, minpolyX_aeval_X, minpolyX_eq_zero_iff
-/
theorem isAlgebraic_adjoin_simple_X (hf : ¬exists c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯) :=
  ⟨f.minpolyX K⟮f⟯, fun H => hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

/--
theorem `isAlgebraic_adjoin_simple_X'` / 定理 `isAlgebraic_adjoin_simple_X'`

English:
theorem isAlgebraic_adjoin_simple_X'
  given: (hf : ¬exists c, f = C c)
  proof: by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : K⟮X⟯)⟯ :=
isAlgebraic_adjoin_simple isAlgebraic_iff_isIntegral.mp f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

中文:
定理 isAlgebraic_adjoin_simple_X'
  条件: (hf : ¬存在 c, f = C c)
  证明: by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : K⟮X⟯)⟯ :=
isAlgebraic_adjoin_simple isAlgebraic_iff_isIntegral.mp f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, IntermediateField, IntermediateField.adjoinXEquiv, IsAlgebraic, adjoinXEquiv, f.isAlgebraic_adjoin_simple_X, isAlgebraic, isAlgebraic_adjoin_simple, isAlgebraic_adjoin_simple_X, isAlgebraic_iff_isIntegral, isAlgebraic_iff_isIntegral.mp
-/
theorem isAlgebraic_adjoin_simple_X' (hf : ¬exists c, f = C c) :
    Algebra.IsAlgebraic K⟮f⟯ K⟮X⟯ := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : K⟮X⟯)⟯ :=
isAlgebraic_adjoin_simple isAlgebraic_iff_isIntegral.mp f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

/--
theorem `natDegree_denom_le_natDegree_minpolyX` / 定理 `natDegree_denom_le_natDegree_minpolyX`

English:
theorem natDegree_denom_le_natDegree_minpolyX
  given: (hf : ¬exists c, f = C c)
  proof: le_natDegree_of_ne_zero fun H => hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

中文:
定理 natDegree_denom_le_natDegree_minpolyX
  条件: (hf : ¬存在 c, f = C c)
  证明: le_natDegree_of_ne_zero fun H => hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

Depends on / 依赖: eq_C_of_minpolyX_coeff_eq_zero, f.eq_C_of_minpolyX_coeff_eq_zero, le_natDegree_of_ne_zero
-/
theorem natDegree_denom_le_natDegree_minpolyX (hf : ¬exists c, f = C c) :
    f.denom.natDegree <= (f.minpolyX K⟮f⟯).natDegree :=
  le_natDegree_of_ne_zero fun H => hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `natDegree_num_le_natDegree_minpolyX` / 定理 `natDegree_num_le_natDegree_minpolyX`

English:
theorem natDegree_num_le_natDegree_minpolyX
  given: (hf : ¬exists c, f = C c)
  proof: by
  have f_ne_zero : f != 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, AddSubgroupClass.coe_sub,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap,
    ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero]; rw [← mul_right_inj' (inv_ne_zero f_ne_zero)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ f_ne_zero]; rw [one_mul]; rw [← eq_div_iff (_root_.map_ne_zero C).mpr Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero)]; rw [← inv_inj]; rw [inv_inv]; rw [← map_div₀]; rw [← map_inv₀] at H
  exact hf ⟨_, H⟩

中文:
定理 natDegree_num_le_natDegree_minpolyX
  条件: (hf : ¬存在 c, f = C c)
  证明: by
  have f_ne_zero : f != 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, AddSubgroupClass.coe_sub,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap,
    ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero]; rw [← mul_right_inj' (inv_ne_zero f_ne_zero)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ f_ne_zero]; rw [one_mul]; rw [← eq_div_iff (_root_.map_ne_zero C).mpr Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero)]; rw [← inv_inj]; rw [inv_inv]; rw [← map_div₀]; rw [← map_inv₀] at H
  exact hf ⟨_, H⟩

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.coe_sub, MulMemClass, MulMemClass.coe_mul, RingHom, RingHom.map_zero, SubalgebraClass, SubalgebraClass.coe_algebraMap, ZeroMemClass, ZeroMemClass.coe_zero, algebraMap_eq_C, coe_algebraMap, coe_mul, coe_sub, coe_zero, coeff_C_mul, coeff_map, coeff_natDegree, coeff_sub, eq_div_iff
-/
theorem natDegree_num_le_natDegree_minpolyX (hf : ¬exists c, f = C c) :
    f.num.natDegree <= (f.minpolyX K⟮f⟯).natDegree := by
  have f_ne_zero : f != 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, AddSubgroupClass.coe_sub,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap,
    ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero]; rw [← mul_right_inj' (inv_ne_zero f_ne_zero)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ f_ne_zero]; rw [one_mul]; rw [← eq_div_iff (_root_.map_ne_zero C).mpr Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero)]; rw [← inv_inj]; rw [inv_inv]; rw [← map_div₀]; rw [← map_inv₀] at H
  exact hf ⟨_, H⟩

/--
theorem `natDegree_minpolyX` / 定理 `natDegree_minpolyX`

English:
theorem natDegree_minpolyX
  proof: by
  by_cases hf : exists c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree <= _ := natDegree_sub_le _ _
    rw [natDegree_map]; rw [natDegree_C_mul fun H => hf ⟨0]; rw [by simpa [map_zero] using congr($(H).val)⟩,
      natDegree_map] at this
    exact this
· exact max_le (natDegree_num_le_natDegree_minpolyX f hf) le_natDegree_of_ne_zero
      fun H => hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

中文:
定理 natDegree_minpolyX
  证明: by
  by_cases hf : exists c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree <= _ := natDegree_sub_le _ _
    rw [natDegree_map]; rw [natDegree_C_mul fun H => hf ⟨0]; rw [by simpa [map_zero] using congr($(H).val)⟩,
      natDegree_map] at this
    exact this
· exact max_le (natDegree_num_le_natDegree_minpolyX f hf) le_natDegree_of_ne_zero
      fun H => hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

Depends on / 依赖: eq_C_of_minpolyX_coeff_eq_zero, f.eq_C_of_minpolyX_coeff_eq_zero, f.minpolyX, le_antisymm, le_natDegree_of_ne_zero, map_zero, max_le, minpolyX, natDegree, natDegree_C_mul, natDegree_map, natDegree_num_le_natDegree_minpolyX, natDegree_sub_le
-/
theorem natDegree_minpolyX :
    (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : exists c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree <= _ := natDegree_sub_le _ _
    rw [natDegree_map]; rw [natDegree_C_mul fun H => hf ⟨0]; rw [by simpa [map_zero] using congr($(H).val)⟩,
      natDegree_map] at this
    exact this
· exact max_le (natDegree_num_le_natDegree_minpolyX f hf) le_natDegree_of_ne_zero
      fun H => hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

/--
theorem `transcendental_of_ne_C` / 定理 `transcendental_of_ne_C`

English:
theorem transcendental_of_ne_C
  given: (hf : ¬exists c, f = C c)
  statement: Transcendental K f
  proof: by
  intro H
  have := isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K K⟮X⟯ := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
exact tr Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

中文:
定理 transcendental_of_ne_C
  条件: (hf : ¬存在 c, f = C c)
  结论: 超越 K f
  证明: by
  intro H
  have := isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K K⟮X⟯ := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
exact tr Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.trans, Algebra.Transcendental, Algebra.transcendental_iff_not_isAlgebraic, H.isIntegral, IsAlgebraic, Transcendental, f.isAlgebraic_adjoin_simple_X, infer_instance, isAlgebraic_adjoin_simple, isAlgebraic_adjoin_simple_X, isIntegral, transcendental_iff_not_isAlgebraic
-/
theorem transcendental_of_ne_C (hf : ¬exists c, f = C c) : Transcendental K f := by
  intro H
  have := isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K K⟮X⟯ := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
exact tr Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `irreducible_minpolyX'` / 定理 `irreducible_minpolyX'`

English:
theorem irreducible_minpolyX'
  given: (hf : ¬exists c, f = C c)
  statement: Irreducible (f.minpolyX K[f])
  proof: by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [algebraMap_eq, map_sub, mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, algEquivOfTranscendental_coe, Polynomial.map_map, map_mul,
      map_C, RingHom.coe_coe, aeval_X, e, φ]
    congr 2 <;> ext <;> simp
  rw [← φ_map]; rw [MulEquiv.irreducible_iff]
  have : φ = Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [X_mul_C, Bivariate.swap_apply, aevalAeval, aevalAevalEquiv, Equiv.coe_fn_mk,
      AlgHom.coe_comp, AlgHom.coe_restrictScalars', coe_aeval_eq_eval, Function.comp_apply,
      aeval_sub, aeval_C, algebraMap_def, coe_mapRingHom, map_mul, aeval_X, eval_sub,
      eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this]; rw [MulEquiv.irreducible_iff]
  convert!
    irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
      ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm]; rw [X_mul_C]; rw [map_neg]; rw [neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

中文:
定理 irreducible_minpolyX'
  条件: (hf : ¬存在 c, f = C c)
  结论: 不可约 (f.minpolyX K[f])
  证明: by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [algebraMap_eq, map_sub, mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, algEquivOfTranscendental_coe, Polynomial.map_map, map_mul,
      map_C, RingHom.coe_coe, aeval_X, e, φ]
    congr 2 <;> ext <;> simp
  rw [← φ_map]; rw [MulEquiv.irreducible_iff]
  have : φ = Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [X_mul_C, Bivariate.swap_apply, aevalAeval, aevalAevalEquiv, Equiv.coe_fn_mk,
      AlgHom.coe_comp, AlgHom.coe_restrictScalars', coe_aeval_eq_eval, Function.comp_apply,
      aeval_sub, aeval_C, algebraMap_def, coe_mapRingHom, map_mul, aeval_X, eval_sub,
      eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this]; rw [MulEquiv.irreducible_iff]
  convert!
    irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
      ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm]; rw [X_mul_C]; rw [map_neg]; rw [neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

Depends on / 依赖: AlgEquiv, AlgEquiv.toRingEquiv_toRingHom, MulEquiv, MulEquiv.irreducible_iff, Polynomial, Polynomial.C, Polynomial.X, Polynomial.algEquivOfTranscendental, Polynomial.map_map, RingHom, RingHom.coe_coe, aeval_X, algEquivOfTranscendental, algEquivOfTranscendental_coe, algebraMap, algebraMap_eq, coe_coe, e.toRingEquiv, f.denom.map, f.minpolyX
-/
theorem irreducible_minpolyX' (hf : ¬exists c, f = C c) : Irreducible (f.minpolyX K[f]) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [algebraMap_eq, map_sub, mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, algEquivOfTranscendental_coe, Polynomial.map_map, map_mul,
      map_C, RingHom.coe_coe, aeval_X, e, φ]
    congr 2 <;> ext <;> simp
  rw [← φ_map]; rw [MulEquiv.irreducible_iff]
  have : φ = Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [X_mul_C, Bivariate.swap_apply, aevalAeval, aevalAevalEquiv, Equiv.coe_fn_mk,
      AlgHom.coe_comp, AlgHom.coe_restrictScalars', coe_aeval_eq_eval, Function.comp_apply,
      aeval_sub, aeval_C, algebraMap_def, coe_mapRingHom, map_mul, aeval_X, eval_sub,
      eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this]; rw [MulEquiv.irreducible_iff]
  convert!
    irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
      ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm]; rw [X_mul_C]; rw [map_neg]; rw [neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

/--
theorem `irreducible_minpolyX` / 定理 `irreducible_minpolyX`

English:
theorem irreducible_minpolyX
  given: (hf : ¬exists c, f = C c)
  statement: Irreducible (f.minpolyX K⟮f⟯)
  proof: by
  have : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

中文:
定理 irreducible_minpolyX
  条件: (hf : ¬存在 c, f = C c)
  结论: 不可约 (f.minpolyX K⟮f⟯)
  证明: by
  have : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

Depends on / 依赖: IsPrimitive, IsPrimitive.irreducible_iff_irreducible_map_fraction_map, Nat.max_eq_zero_iff, UniqueFactorizationMonoid, algebraMap, eq_C_iff, f.eq_C_iff, f.irreducible_minpolyX, f.minpolyX, f.minpolyX_map, f.natDegree_minpolyX, f.transcendental_of_ne_C, irreducible_iff_irreducible_map_fraction_map, irreducible_minpolyX, isPrimitive, max_eq_zero_iff, minpolyX, minpolyX_map, natDegree_map_le, natDegree_minpolyX
-/
theorem irreducible_minpolyX (hf : ¬exists c, f = C c) : Irreducible (f.minpolyX K⟮f⟯) := by
  have : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

/--
theorem `finrank_eq_max_natDegree` / 定理 `finrank_eq_max_natDegree`

English:
theorem finrank_eq_max_natDegree
  proof: by
  by_cases hf : exists c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c in ⊥ from ⟨c]; rw [rfl⟩)]; rw [finrank_bot']; rw [Module.finrank_of_not_finite fun H => Algebra.transcendental_iff_not_isAlgebraic.mp
transcendental Algebra.IsAlgebraic.of_finite K K⟮X⟯]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq]; rw [adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral]; rw [← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X]; rw [mul_comm]; rw [natDegree_C_mul inv_ne_zero leadingCoeff_ne_zero.mpr fun H =>
    hf ((minpolyX_eq_zero_iff f).mp H)]; rw [natDegree_minpolyX]

中文:
定理 finrank_eq_max_natDegree
  证明: by
  by_cases hf : exists c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c in ⊥ from ⟨c]; rw [rfl⟩)]; rw [finrank_bot']; rw [Module.finrank_of_not_finite fun H => Algebra.transcendental_iff_not_isAlgebraic.mp
transcendental Algebra.IsAlgebraic.of_finite K K⟮X⟯]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq]; rw [adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral]; rw [← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X]; rw [mul_comm]; rw [natDegree_C_mul inv_ne_zero leadingCoeff_ne_zero.mpr fun H =>
    hf ((minpolyX_eq_zero_iff f).mp H)]; rw [natDegree_minpolyX]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.of_finite, Algebra.transcendental_iff_not_isAlgebraic.mp, IntermediateField, IntermediateField.adjoinXEquiv, IsAlgebraic, Module, Module.finrank_of_not_finite, adjoin, adjoin.finrank, adjoinXEquiv, adjoin_simple_eq_bot_iff, adjoin_simple_eq_bot_iff.mpr, eq_of_irreducible, f.irreducible_minpolyX, f.isAlgebraic_adjoin_simple_X, f.minpol, finrank, finrank_bot, finrank_eq
-/
theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : exists c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c in ⊥ from ⟨c]; rw [rfl⟩)]; rw [finrank_bot']; rw [Module.finrank_of_not_finite fun H => Algebra.transcendental_iff_not_isAlgebraic.mp
transcendental Algebra.IsAlgebraic.of_finite K K⟮X⟯]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq]; rw [adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral]; rw [← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X]; rw [mul_comm]; rw [natDegree_C_mul inv_ne_zero leadingCoeff_ne_zero.mpr fun H =>
    hf ((minpolyX_eq_zero_iff f).mp H)]; rw [natDegree_minpolyX]

/--
theorem `IntermediateField.isAlgebraic_X` / 定理 `IntermediateField.isAlgebraic_X`

English:
theorem IntermediateField.isAlgebraic_X
  given: {E : IntermediateField K K⟮X⟯} (hE : E != ⊥)
  proof: by
  rw [ne_eq]; rw [← le_bot_iff]; rw [SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁)
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

中文:
定理 中间域.isAlgebraic_X
  条件: {E : 中间域 K K⟮X⟯} (hE : E != ⊥)
  证明: by
  rw [ne_eq]; rw [← le_bot_iff]; rw [SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁)
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

Depends on / 依赖: IsAlgebraic, IsAlgebraic.tower_top_of_subalgebra_le, SetLike, SetLike.not_le_iff_exists, adjoin_simple_le_iff, adjoin_simple_le_iff.mpr, f.isAlgebraic_adjoin_simple_X, isAlgebraic_adjoin_simple_X, le_bot_iff, ne_eq, not_le_iff_exists, tower_top_of_subalgebra_le
-/
theorem IntermediateField.isAlgebraic_X {E : IntermediateField K K⟮X⟯} (hE : E != ⊥) :
    IsAlgebraic E (X : K⟮X⟯) := by
  rw [ne_eq]; rw [← le_bot_iff]; rw [SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁)
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

end

end RatFunc
