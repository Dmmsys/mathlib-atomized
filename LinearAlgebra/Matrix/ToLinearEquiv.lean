/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Matrices and linear equivalences

This file gives the map `Matrix.toLinearEquiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

* `Matrix.toLinearEquiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

* `Matrix.exists_mulVec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear equivalence, linear isomorphism, determinant, inverse

-/

@[expose] public section

open Module

variable {n : Type*} [Fintype n]

namespace Matrix

section LinearEquiv

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section ToLinearEquiv'

variable [DecidableEq n]

/--
Definition of `toLinearEquiv'` / `toLinearEquiv'` 的定义

English:
definition toLinearEquiv'
  signature: (P : Matrix n n R) (_ : Invertible P)
  body: GeneralLinearGroup.generalLinearEquiv _ _
Matrix.GeneralLinearGroup.toLin unitOfInvertible P

@[simp]

中文:
定义 toLinearEquiv'
  签名: (P : 矩阵 n n R) (_ : 可逆 P)
  定义体: GeneralLinearGroup.generalLinearEquiv _ _
Matrix.GeneralLinearGroup.toLin unitOfInvertible P

@[simp]

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.generalLinearEquiv, Matrix, Matrix.GeneralLinearGroup.toLin, generalLinearEquiv, unitOfInvertible
-/
def toLinearEquiv' (P : Matrix n n R) (_ : Invertible P) : (n -> R) ≃ₗ[R] n -> R :=
GeneralLinearGroup.generalLinearEquiv _ _
Matrix.GeneralLinearGroup.toLin unitOfInvertible P

@[simp]
/--
theorem `toLinearEquiv'_apply` / 定理 `toLinearEquiv'_apply`

English:
theorem toLinearEquiv'_apply
  given: (P : Matrix n n R) (h : Invertible P)
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv'_apply
  条件: (P : 矩阵 n n R) (h : 可逆 P)
  证明: rfl

@[simp]
-/
theorem toLinearEquiv'_apply (P : Matrix n n R) (h : Invertible P) :
    (P.toLinearEquiv' h : Module.End R (n -> R)) = Matrix.toLin' P :=
  rfl

@[simp]
/--
theorem `toLinearEquiv'_symm_apply` / 定理 `toLinearEquiv'_symm_apply`

English:
theorem toLinearEquiv'_symm_apply
  given: (P : Matrix n n R) (h : Invertible P)
  proof: rfl

中文:
定理 toLinearEquiv'_symm_apply
  条件: (P : 矩阵 n n R) (h : 可逆 P)
  证明: rfl
-/
theorem toLinearEquiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n -> R)) = Matrix.toLin' (⅟P) :=
  rfl

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

/-- Given `hA : IsUnit A.det` and `b : Basis R b`, `A.toLinearEquiv b hA` is
the `LinearEquiv` arising from `toLin b b A`.

See `Matrix.toLinearEquiv'` for this result on `n → R`.
-/
@[simps apply]
/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det)
  body: toLin b b A
  toFun := toLin b b A
  invFun := toLin b b A⁻¹
  left_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA,
      toLin_one, LinearMap.id_apply]
  right_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.mul_nonsing_inv _ hA,
      toLin_one, LinearMap.id_apply]

中文:
定义 toLinearEquiv
  签名: [DecidableEq n] (A : 矩阵 n n R) (hA : 是单位 A.det)
  定义体: toLin b b A
  toFun := toLin b b A
  invFun := toLin b b A⁻¹
  left_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA,
      toLin_one, LinearMap.id_apply]
  right_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.mul_nonsing_inv _ hA,
      toLin_one, LinearMap.id_apply]
-/
noncomputable def toLinearEquiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    M ≃ₗ[R] M where
  __ := toLin b b A
  toFun := toLin b b A
  invFun := toLin b b A⁻¹
  left_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.nonsing_inv_mul _ hA,
      toLin_one, LinearMap.id_apply]
  right_inv x := by
    simp_rw [← LinearMap.comp_apply, ← Matrix.toLin_mul b b b, Matrix.mul_nonsing_inv _ hA,
      toLin_one, LinearMap.id_apply]

/--
theorem `ker_toLin_eq_bot` / 定理 `ker_toLin_eq_bot`

English:
theorem ker_toLin_eq_bot
  given: [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det)
  proof: ker_eq_bot.mpr (toLinearEquiv b A hA).injective

中文:
定理 ker_toLin_eq_bot
  条件: [DecidableEq n] (A : 矩阵 n n R) (hA : 是单位 A.det)
  证明: ker_eq_bot.mpr (toLinearEquiv b A hA).injective

Depends on / 依赖: injective, ker_eq_bot, ker_eq_bot.mpr, toLinearEquiv
-/
theorem ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.ker (toLin b b A) = ⊥ :=
  ker_eq_bot.mpr (toLinearEquiv b A hA).injective

/--
theorem `range_toLin_eq_top` / 定理 `range_toLin_eq_top`

English:
theorem range_toLin_eq_top
  given: [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det)
  proof: range_eq_top.mpr (toLinearEquiv b A hA).surjective

中文:
定理 range_toLin_eq_top
  条件: [DecidableEq n] (A : 矩阵 n n R) (hA : 是单位 A.det)
  证明: range_eq_top.mpr (toLinearEquiv b A hA).surjective

Depends on / 依赖: range_eq_top, range_eq_top.mpr, surjective, toLinearEquiv
-/
theorem range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.range (toLin b b A) = ⊤ :=
  range_eq_top.mpr (toLinearEquiv b A hA).surjective

end ToLinearEquiv

section Nondegenerate

open Matrix

/--
theorem `exists_mulVec_eq_zero_iff_aux` / 定理 `exists_mulVec_eq_zero_iff_aux`

English:
theorem exists_mulVec_eq_zero_iff_aux
  statement: {K : Type*} [DecidableEq n] [Field K]
  proof: by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mulVec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective (Matrix.toLin' M) := by
      simpa only [← LinearMap.ker_eq_bot, ker_toLin'_eq_bot_iff, not_imp_not] using h
    have : M * (LinearEquiv.ofInjectiveEndo _ this).symm.toMatrix' = 1 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
      rw [Matrix.toLin'_mul]; rw [Matrix.toLin'_one]; rw [Matrix.toLin'_toMatrix']; rw [LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this

中文:
定理 存在_mulVec_eq_zero_iff_aux
  结论: {K : 类型} [DecidableEq n] [域 K]
  证明: by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mulVec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective (Matrix.toLin' M) := by
      simpa only [← LinearMap.ker_eq_bot, ker_toLin'_eq_bot_iff, not_imp_not] using h
    have : M * (LinearEquiv.ofInjectiveEndo _ this).symm.toMatrix' = 1 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
      rw [Matrix.toLin'_mul]; rw [Matrix.toLin'_one]; rw [Matrix.toLin'_toMatrix']; rw [LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this
-/
private theorem exists_mulVec_eq_zero_iff_aux {K : Type*} [DecidableEq n] [Field K]
    {M : Matrix n n K} : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0 := by
  constructor
  · rintro ⟨v, hv, mul_eq⟩
    contrapose! hv
    exact eq_zero_of_mulVec_eq_zero hv mul_eq
  · contrapose!
    intro h
    have : Function.Injective (Matrix.toLin' M) := by
      simpa only [← LinearMap.ker_eq_bot, ker_toLin'_eq_bot_iff, not_imp_not] using h
    have : M * (LinearEquiv.ofInjectiveEndo _ this).symm.toMatrix' = 1 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
      rw [Matrix.toLin'_mul]; rw [Matrix.toLin'_one]; rw [Matrix.toLin'_toMatrix']; rw [LinearMap.comp_apply]
      exact (LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) this).apply_symm_apply v
    exact Matrix.det_ne_zero_of_right_inverse this

/--
theorem `exists_mulVec_eq_zero_iff'` / 定理 `exists_mulVec_eq_zero_iff'`

English:
theorem exists_mulVec_eq_zero_iff'
  statement: {A : Type*} (K : Type*) [DecidableEq n] [CommRing A]
  proof: by
  have : (exists v != 0, (algebraMap A K).mapMatrix M *ᵥ v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det]; rw [IsFractionRing.to_map_eq_zero_iff] at this
  refine Iff.trans ?_ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => ?_) hv, ?_⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine (RingHom.map_mulVec _ _ _ i).symm.trans ?_
      rw [mul_eq]; rw [Pi.zero_apply]; rw [map_zero]; rw [Pi.zero_apply]
  · let := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => ?_) hv, ?_⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf]; rw [Subtype.coe_mk]; rw [Pi.zero_apply]; rw [map_zero]; rw [Algebra.smul_def]; rw [mul_eq_zero]; rw [IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine IsFractionRing.injective A K ?_
      calc
        algebraMap A K ((M *ᵥ (fun i : n => f (v i) _)) i) =
            ((algebraMap A K).mapMatrix M *ᵥ algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]

中文:
定理 存在_mulVec_eq_zero_iff'
  结论: {A : 类型} (K : 类型) [DecidableEq n] [交换环 A]
  证明: by
  have : (exists v != 0, (algebraMap A K).mapMatrix M *ᵥ v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det]; rw [IsFractionRing.to_map_eq_zero_iff] at this
  refine Iff.trans ?_ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => ?_) hv, ?_⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine (RingHom.map_mulVec _ _ _ i).symm.trans ?_
      rw [mul_eq]; rw [Pi.zero_apply]; rw [map_zero]; rw [Pi.zero_apply]
  · let := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => ?_) hv, ?_⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf]; rw [Subtype.coe_mk]; rw [Pi.zero_apply]; rw [map_zero]; rw [Algebra.smul_def]; rw [mul_eq_zero]; rw [IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine IsFractionRing.injective A K ?_
      calc
        algebraMap A K ((M *ᵥ (fun i : n => f (v i) _)) i) =
            ((algebraMap A K).mapMatrix M *ᵥ algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]
-/
private theorem exists_mulVec_eq_zero_iff' {A : Type*} (K : Type*) [DecidableEq n] [CommRing A]
    [Nontrivial A] [Field K] [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} :
    (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0 := by
  have : (exists v != 0, (algebraMap A K).mapMatrix M *ᵥ v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det]; rw [IsFractionRing.to_map_eq_zero_iff] at this
  refine Iff.trans ?_ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => ?_) hv, ?_⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine (RingHom.map_mulVec _ _ _ i).symm.trans ?_
      rw [mul_eq]; rw [Pi.zero_apply]; rw [map_zero]; rw [Pi.zero_apply]
  · let := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => ?_) hv, ?_⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf]; rw [Subtype.coe_mk]; rw [Pi.zero_apply]; rw [map_zero]; rw [Algebra.smul_def]; rw [mul_eq_zero]; rw [IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine IsFractionRing.injective A K ?_
      calc
        algebraMap A K ((M *ᵥ (fun i : n => f (v i) _)) i) =
            ((algebraMap A K).mapMatrix M *ᵥ algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]

variable {A : Type*} [CommRing A] [IsDomain A] {M N : Matrix n n A}

/--
theorem `exists_mulVec_eq_zero_iff` / 定理 `exists_mulVec_eq_zero_iff`

English:
theorem exists_mulVec_eq_zero_iff
  given: [DecidableEq n]
  statement: (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
  proof: exists_mulVec_eq_zero_iff' (FractionRing A)

中文:
定理 存在_mulVec_eq_zero_iff
  条件: [DecidableEq n]
  结论: (存在 v != 0, M *ᵥ v = 0) ↔ M.det = 0
  证明: exists_mulVec_eq_zero_iff' (FractionRing A)

Depends on / 依赖: FractionRing, exists_mulVec_eq_zero_iff
-/
theorem exists_mulVec_eq_zero_iff [DecidableEq n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0 :=
  exists_mulVec_eq_zero_iff' (FractionRing A)

/--
theorem `exists_vecMul_eq_zero_iff` / 定理 `exists_vecMul_eq_zero_iff`

English:
theorem exists_vecMul_eq_zero_iff
  given: [DecidableEq n]
  statement: (exists v != 0, v ᵥ* M = 0) ↔ M.det = 0
  proof: by
  simpa only [← M.det_transpose, ← mulVec_transpose] using exists_mulVec_eq_zero_iff

中文:
定理 存在_vecMul_eq_zero_iff
  条件: [DecidableEq n]
  结论: (存在 v != 0, v ᵥ* M = 0) ↔ M.det = 0
  证明: by
  simpa only [← M.det_transpose, ← mulVec_transpose] using exists_mulVec_eq_zero_iff

Depends on / 依赖: M.det_transpose, det_transpose, exists_mulVec_eq_zero_iff, mulVec_transpose
-/
theorem exists_vecMul_eq_zero_iff [DecidableEq n] : (exists v != 0, v ᵥ* M = 0) ↔ M.det = 0 := by
  simpa only [← M.det_transpose, ← mulVec_transpose] using exists_mulVec_eq_zero_iff

/--
theorem `nondegenerate_iff_det_ne_zero` / 定理 `nondegenerate_iff_det_ne_zero`

English:
theorem nondegenerate_iff_det_ne_zero
  given: [DecidableEq n]
  statement: Nondegenerate M ↔ M.det != 0
  proof: by
  grind [nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero, exists_mulVec_eq_zero_iff,
    exists_vecMul_eq_zero_iff]

中文:
定理 nondegenerate_iff_det_ne_zero
  条件: [DecidableEq n]
  结论: 非退化 M ↔ M.det != 0
  证明: by
  grind [nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero, exists_mulVec_eq_zero_iff,
    exists_vecMul_eq_zero_iff]

Depends on / 依赖: exists_mulVec_eq_zero_iff, exists_vecMul_eq_zero_iff, nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero
-/
theorem nondegenerate_iff_det_ne_zero [DecidableEq n] : Nondegenerate M ↔ M.det != 0 := by
  grind [nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero, exists_mulVec_eq_zero_iff,
    exists_vecMul_eq_zero_iff]

/--
lemma `separatingLeft_iff_det_ne_zero` / 引理 `separatingLeft_iff_det_ne_zero`

English:
lemma separatingLeft_iff_det_ne_zero
  given: [DecidableEq n]
  statement: SeparatingLeft M ↔ M.det != 0
  proof: by
  grind [separatingLeft_iff_forall_vecMul_eq_zero, exists_vecMul_eq_zero_iff]

中文:
引理 separatingLeft_iff_det_ne_zero
  条件: [DecidableEq n]
  结论: SeparatingLeft M ↔ M.det != 0
  证明: by
  grind [separatingLeft_iff_forall_vecMul_eq_zero, exists_vecMul_eq_zero_iff]

Depends on / 依赖: exists_vecMul_eq_zero_iff, separatingLeft_iff_forall_vecMul_eq_zero
-/
lemma separatingLeft_iff_det_ne_zero [DecidableEq n] : SeparatingLeft M ↔ M.det != 0 := by
  grind [separatingLeft_iff_forall_vecMul_eq_zero, exists_vecMul_eq_zero_iff]

/--
lemma `separatingRight_iff_det_ne_zero` / 引理 `separatingRight_iff_det_ne_zero`

English:
lemma separatingRight_iff_det_ne_zero
  given: [DecidableEq n]
  statement: SeparatingRight M ↔ M.det != 0
  proof: by
  grind [separatingRight_iff_forall_mulVec_eq_zero, exists_mulVec_eq_zero_iff]

omit [Fintype n] in

中文:
引理 separatingRight_iff_det_ne_zero
  条件: [DecidableEq n]
  结论: SeparatingRight M ↔ M.det != 0
  证明: by
  grind [separatingRight_iff_forall_mulVec_eq_zero, exists_mulVec_eq_zero_iff]

omit [Fintype n] in

Depends on / 依赖: exists_mulVec_eq_zero_iff, separatingRight_iff_forall_mulVec_eq_zero
-/
lemma separatingRight_iff_det_ne_zero [DecidableEq n] : SeparatingRight M ↔ M.det != 0 := by
  grind [separatingRight_iff_forall_mulVec_eq_zero, exists_mulVec_eq_zero_iff]

omit [Fintype n] in
/--
theorem `nondegenerate_iff_separatingLeft` / 定理 `nondegenerate_iff_separatingLeft`

English:
theorem nondegenerate_iff_separatingLeft
  given: [Finite n]
  statement: M.Nondegenerate ↔ M.SeparatingLeft
  proof: by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero]; rw [separatingLeft_iff_det_ne_zero]

alias ⟨_, SeparatingLeft.nondegenerate⟩ := nondegenerate_iff_separatingLeft

omit [Fintype n] in

中文:
定理 nondegenerate_iff_separatingLeft
  条件: [有限 n]
  结论: M.非退化 ↔ M.SeparatingLeft
  证明: by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero]; rw [separatingLeft_iff_det_ne_zero]

alias ⟨_, SeparatingLeft.nondegenerate⟩ := nondegenerate_iff_separatingLeft

omit [Fintype n] in

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, nondegenerate_iff_det_ne_zero, ofFinite, separatingLeft_iff_det_ne_zero
-/
theorem nondegenerate_iff_separatingLeft [Finite n] : M.Nondegenerate ↔ M.SeparatingLeft := by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero]; rw [separatingLeft_iff_det_ne_zero]

alias ⟨_, SeparatingLeft.nondegenerate⟩ := nondegenerate_iff_separatingLeft

omit [Fintype n] in
/--
theorem `nondegenerate_iff_separatingRight` / 定理 `nondegenerate_iff_separatingRight`

English:
theorem nondegenerate_iff_separatingRight
  given: [Finite n]
  statement: M.Nondegenerate ↔ M.SeparatingRight
  proof: by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero]; rw [separatingRight_iff_det_ne_zero]

alias ⟨_, SeparatingRight.nondegenerate⟩ := nondegenerate_iff_separatingRight

omit [Fintype n] in

中文:
定理 nondegenerate_iff_separatingRight
  条件: [有限 n]
  结论: M.非退化 ↔ M.SeparatingRight
  证明: by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero]; rw [separatingRight_iff_det_ne_zero]

alias ⟨_, SeparatingRight.nondegenerate⟩ := nondegenerate_iff_separatingRight

omit [Fintype n] in

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, nondegenerate_iff_det_ne_zero, ofFinite, separatingRight_iff_det_ne_zero
-/
theorem nondegenerate_iff_separatingRight [Finite n] : M.Nondegenerate ↔ M.SeparatingRight := by
  classical
  have := Fintype.ofFinite n
  rw [nondegenerate_iff_det_ne_zero]; rw [separatingRight_iff_det_ne_zero]

alias ⟨_, SeparatingRight.nondegenerate⟩ := nondegenerate_iff_separatingRight

omit [Fintype n] in
/--
theorem `separatingLeft_iff_separatingRight` / 定理 `separatingLeft_iff_separatingRight`

English:
theorem separatingLeft_iff_separatingRight
  given: [Finite n]
  statement: M.SeparatingLeft ↔ M.SeparatingRight
  proof: nondegenerate_iff_separatingLeft.symm.trans nondegenerate_iff_separatingRight

alias ⟨SeparatingLeft.separatingRight, SeparatingRight.separatingLeft⟩ :=
  separatingLeft_iff_separatingRight

中文:
定理 separatingLeft_iff_separatingRight
  条件: [有限 n]
  结论: M.SeparatingLeft ↔ M.SeparatingRight
  证明: nondegenerate_iff_separatingLeft.symm.trans nondegenerate_iff_separatingRight

alias ⟨SeparatingLeft.separatingRight, SeparatingRight.separatingLeft⟩ :=
  separatingLeft_iff_separatingRight

Depends on / 依赖: nondegenerate_iff_separatingLeft, nondegenerate_iff_separatingLeft.symm.trans, nondegenerate_iff_separatingRight
-/
theorem separatingLeft_iff_separatingRight [Finite n] : M.SeparatingLeft ↔ M.SeparatingRight :=
  nondegenerate_iff_separatingLeft.symm.trans nondegenerate_iff_separatingRight

alias ⟨SeparatingLeft.separatingRight, SeparatingRight.separatingLeft⟩ :=
  separatingLeft_iff_separatingRight

/--
theorem `Nondegenerate.mul_iff_right` / 定理 `Nondegenerate.mul_iff_right`

English:
theorem Nondegenerate.mul_iff_right
  given: (h : N.Nondegenerate)
  proof: by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_right h

中文:
定理 非退化.mul_iff_right
  条件: (h : N.非退化)
  证明: by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_right h

Depends on / 依赖: classical, det_mul, mul_ne_zero_iff_right, nondegenerate_iff_det_ne_zero
-/
theorem Nondegenerate.mul_iff_right (h : N.Nondegenerate) :
    (M * N).Nondegenerate ↔ M.Nondegenerate := by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_right h

/--
theorem `Nondegenerate.mul_iff_left` / 定理 `Nondegenerate.mul_iff_left`

English:
theorem Nondegenerate.mul_iff_left
  given: (h : M.Nondegenerate)
  proof: by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_left h

omit [Fintype n] in

中文:
定理 非退化.mul_iff_left
  条件: (h : M.非退化)
  证明: by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_left h

omit [Fintype n] in

Depends on / 依赖: classical, det_mul, mul_ne_zero_iff_left, nondegenerate_iff_det_ne_zero
-/
theorem Nondegenerate.mul_iff_left (h : M.Nondegenerate) :
    (M * N).Nondegenerate ↔ N.Nondegenerate := by
  classical
  simp only [nondegenerate_iff_det_ne_zero, det_mul] at h ⊢
  exact mul_ne_zero_iff_left h

omit [Fintype n] in
/--
theorem `Nondegenerate.smul_iff` / 定理 `Nondegenerate.smul_iff`

English:
theorem Nondegenerate.smul_iff
  given: [Finite n] {t : A} (h : t != 0)
  proof: by
  have := Fintype.ofFinite
  rw [nondegenerate_def]; rw [nondegenerate_def]
  simp [smul_mulVec, mul_eq_zero_iff_left h]

alias ⟨Nondegenerate.det_ne_zero, Nondegenerate.of_det_ne_zero⟩ := nondegenerate_iff_det_ne_zero

中文:
定理 非退化.smul_iff
  条件: [有限 n] {t : A} (h : t != 0)
  证明: by
  have := Fintype.ofFinite
  rw [nondegenerate_def]; rw [nondegenerate_def]
  simp [smul_mulVec, mul_eq_zero_iff_left h]

alias ⟨Nondegenerate.det_ne_zero, Nondegenerate.of_det_ne_zero⟩ := nondegenerate_iff_det_ne_zero

Depends on / 依赖: Fintype, Fintype.ofFinite, mul_eq_zero_iff_left, nondegenerate_def, ofFinite, smul_mulVec
-/
theorem Nondegenerate.smul_iff [Finite n] {t : A} (h : t != 0) :
    (t • M).Nondegenerate ↔ M.Nondegenerate := by
  have := Fintype.ofFinite
  rw [nondegenerate_def]; rw [nondegenerate_def]
  simp [smul_mulVec, mul_eq_zero_iff_left h]

alias ⟨Nondegenerate.det_ne_zero, Nondegenerate.of_det_ne_zero⟩ := nondegenerate_iff_det_ne_zero

end Nondegenerate

end LinearEquiv

section Determinant

/--
lemma `det_ne_zero_of_sum_col_pos` / 引理 `det_ne_zero_of_sum_col_pos`

English:
lemma det_ne_zero_of_sum_col_pos
  statement: [DecidableEq n]
  proof: by
  cases isEmpty_or_nonempty n
  · simp
  · contrapose! h2
    obtain ⟨v, ⟨h_vnz, h_vA⟩⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h2
    wlog h_sup : 0 < Finset.sup' Finset.univ Finset.univ_nonempty v
    · refine this h1 inferInstance h2 (-1 • v) (by simp [*]) ?_ ?_
      · rw [Matrix.smul_vecMul, h_vA, smul_zero]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h_vnz
        simp_rw [Finset.lt_sup'_iff, Finset.mem_univ, true_and] at h_sup ⊢
        simp_rw [not_exists, not_lt] at h_sup
        refine ⟨i, ?_⟩
        rw [Pi.smul_apply]; rw [neg_smul]; rw [one_smul]; rw [Left.neg_pos_iff]
        exact Ne.lt_of_le hi (h_sup i)
    · obtain ⟨j₀, -, h_j₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
      refine ⟨j₀, ?_⟩
      rw [← mul_le_mul_iff_right₀ (h_j₀ ▸ h_sup)]; rw [Finset.mul_sum]; rw [mul_zero]
      rw [show 0 = ∑ i]; rw [v i * A i j₀ from (congrFun h_vA j₀).symm]
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h : i = j₀
      · rw [h]
      · exact (mul_le_mul_right_of_neg (h1 h)).mpr (h_j₀ ▸ Finset.le_sup' v hi)

中文:
引理 det_ne_zero_of_sum_col_pos
  结论: [DecidableEq n]
  证明: by
  cases isEmpty_or_nonempty n
  · simp
  · contrapose! h2
    obtain ⟨v, ⟨h_vnz, h_vA⟩⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h2
    wlog h_sup : 0 < Finset.sup' Finset.univ Finset.univ_nonempty v
    · refine this h1 inferInstance h2 (-1 • v) (by simp [*]) ?_ ?_
      · rw [Matrix.smul_vecMul, h_vA, smul_zero]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h_vnz
        simp_rw [Finset.lt_sup'_iff, Finset.mem_univ, true_and] at h_sup ⊢
        simp_rw [not_exists, not_lt] at h_sup
        refine ⟨i, ?_⟩
        rw [Pi.smul_apply]; rw [neg_smul]; rw [one_smul]; rw [Left.neg_pos_iff]
        exact Ne.lt_of_le hi (h_sup i)
    · obtain ⟨j₀, -, h_j₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
      refine ⟨j₀, ?_⟩
      rw [← mul_le_mul_iff_right₀ (h_j₀ ▸ h_sup)]; rw [Finset.mul_sum]; rw [mul_zero]
      rw [show 0 = ∑ i]; rw [v i * A i j₀ from (congrFun h_vA j₀).symm]
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h : i = j₀
      · rw [h]
      · exact (mul_le_mul_right_of_neg (h1 h)).mpr (h_j₀ ▸ Finset.le_sup' v hi)

Depends on / 依赖: Finset, Finset.lt_sup, Finset.mem_univ, Finset.sup, Finset.univ, Finset.univ_nonempty, Function, Function.ne_iff.mp, Matrix, Matrix.exists_vecMul_eq_zero_iff.mpr, Matrix.smul_vecMul, Pi.smul_apply, _iff, contrapose, exists_vecMul_eq_zero_iff, h_sup, h_vA, h_vnz, isEmpty_or_nonempty, lt_sup
-/
lemma det_ne_zero_of_sum_col_pos [DecidableEq n]
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {A : Matrix n n S} (h1 : Pairwise fun i j => A i j < 0) (h2 : forall j, 0 < ∑ i, A i j) :
    A.det != 0 := by
  cases isEmpty_or_nonempty n
  · simp
  · contrapose! h2
    obtain ⟨v, ⟨h_vnz, h_vA⟩⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h2
    wlog h_sup : 0 < Finset.sup' Finset.univ Finset.univ_nonempty v
    · refine this h1 inferInstance h2 (-1 • v) (by simp [*]) ?_ ?_
      · rw [Matrix.smul_vecMul, h_vA, smul_zero]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h_vnz
        simp_rw [Finset.lt_sup'_iff, Finset.mem_univ, true_and] at h_sup ⊢
        simp_rw [not_exists, not_lt] at h_sup
        refine ⟨i, ?_⟩
        rw [Pi.smul_apply]; rw [neg_smul]; rw [one_smul]; rw [Left.neg_pos_iff]
        exact Ne.lt_of_le hi (h_sup i)
    · obtain ⟨j₀, -, h_j₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
      refine ⟨j₀, ?_⟩
      rw [← mul_le_mul_iff_right₀ (h_j₀ ▸ h_sup)]; rw [Finset.mul_sum]; rw [mul_zero]
      rw [show 0 = ∑ i]; rw [v i * A i j₀ from (congrFun h_vA j₀).symm]
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h : i = j₀
      · rw [h]
      · exact (mul_le_mul_right_of_neg (h1 h)).mpr (h_j₀ ▸ Finset.le_sup' v hi)

/--
lemma `det_ne_zero_of_sum_row_pos` / 引理 `det_ne_zero_of_sum_row_pos`

English:
lemma det_ne_zero_of_sum_row_pos
  statement: [DecidableEq n]
  proof: by
  rw [← Matrix.det_transpose]
  refine det_ne_zero_of_sum_col_pos ?_ ?_
  · simp_rw [Matrix.transpose_apply]
    exact fun i j h => h1 h.symm
  · simp_rw [Matrix.transpose_apply]
    exact h2

中文:
引理 det_ne_zero_of_sum_row_pos
  结论: [DecidableEq n]
  证明: by
  rw [← Matrix.det_transpose]
  refine det_ne_zero_of_sum_col_pos ?_ ?_
  · simp_rw [Matrix.transpose_apply]
    exact fun i j h => h1 h.symm
  · simp_rw [Matrix.transpose_apply]
    exact h2

Depends on / 依赖: Matrix, Matrix.det_transpose, Matrix.transpose_apply, det_ne_zero_of_sum_col_pos, det_transpose, h.symm, simp_rw, transpose_apply
-/
lemma det_ne_zero_of_sum_row_pos [DecidableEq n]
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {A : Matrix n n S} (h1 : Pairwise fun i j => A i j < 0) (h2 : forall i, 0 < ∑ j, A i j) :
    A.det != 0 := by
  rw [← Matrix.det_transpose]
  refine det_ne_zero_of_sum_col_pos ?_ ?_
  · simp_rw [Matrix.transpose_apply]
    exact fun i j h => h1 h.symm
  · simp_rw [Matrix.transpose_apply]
    exact h2

end Determinant

end Matrix
