/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Normal field extensions

In this file we define normal field extensions.

## Main Definitions

- `Normal F K` where `K` is a field extension of `F`.
-/

@[expose] public section

noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- Typeclass for normal field extensions: an algebraic extension of fields `K/F` is *normal*
if the minimal polynomial of every element `x` in `K` splits in `K`, i.e. every `F`-conjugate
of `x` is in `K`. -/
@[stacks 09HM]
/--
Definition of `Normal` / `Normal` 的定义

English:
class Normal
  parameters: : Prop extends Algebra.IsAlgebraic F K where
  extends: Algebra.IsAlgebraic F K
  axioms and operations (1):
    - splits'((x : K)) : Splits ((minpoly F x).map (algebraMap F K))

中文:
类 Normal
  参数: : 命题 extends Algebra.IsAlgebraic F K where
  继承: Algebra.IsAlgebraic F K
  公理与运算 (1 个):
    - splits'((x : K)) : Splits ((minpoly F x).map (algebraMap F K))
-/
class Normal : Prop extends Algebra.IsAlgebraic F K where
  splits' (x : K) : Splits ((minpoly F x).map (algebraMap F K))

variable {F K}

/--
theorem `Normal.isIntegral` / 定理 `Normal.isIntegral`

English:
theorem Normal.isIntegral
  given: (_ : Normal F K) (x : K)
  statement: IsIntegral F x
  proof: Algebra.IsIntegral.isIntegral x

中文:
定理 Normal.isIntegral
  条件: (_ : Normal F K) (x : K)
  结论: Is整数egral F x
  证明: Algebra.IsIntegral.isIntegral x

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isIntegral
-/
theorem Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral x

/--
theorem `Normal.splits` / 定理 `Normal.splits`

English:
theorem Normal.splits
  given: (_ : Normal F K) (x : K)
  statement: Splits ((minpoly F x).map (algebraMap F K))
  proof: Normal.splits' x

中文:
定理 Normal.splits
  条件: (_ : Normal F K) (x : K)
  结论: Splits ((minpoly F x).map (algebraMap F K))
  证明: Normal.splits' x

Depends on / 依赖: Normal, Normal.splits, splits
-/
theorem Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly F x).map (algebraMap F K)) :=
  Normal.splits' x

/--
theorem `normal_iff` / 定理 `normal_iff`

English:
theorem normal_iff
  proof: ⟨fun h x => ⟨h.isIntegral x, h.splits x⟩, fun h =>
    { isAlgebraic := fun x => (h x).1.isAlgebraic
      splits' := fun x => (h x).2 }⟩

中文:
定理 normal_iff
  证明: ⟨fun h x => ⟨h.isIntegral x, h.splits x⟩, fun h =>
    { isAlgebraic := fun x => (h x).1.isAlgebraic
      splits' := fun x => (h x).2 }⟩

Depends on / 依赖: h.isIntegral, h.splits, isAlgebraic, isIntegral, splits
-/
theorem normal_iff :
    Normal F K ↔ forall x : K, IsIntegral F x ∧ Splits ((minpoly F x).map (algebraMap F K)) :=
  ⟨fun h x => ⟨h.isIntegral x, h.splits x⟩, fun h =>
    { isAlgebraic := fun x => (h x).1.isAlgebraic
      splits' := fun x => (h x).2 }⟩

/--
theorem `Normal.out` / 定理 `Normal.out`

English:
theorem Normal.out
  proof: normal_iff.1

中文:
定理 Normal.out
  证明: normal_iff.1

Depends on / 依赖: normal_iff
-/
theorem Normal.out :
    Normal F K -> forall x : K, IsIntegral F x ∧ Splits ((minpoly F x).map (algebraMap F K)) :=
  normal_iff.1

variable (F K)

/--
Instance `normal_self` / 实例 `normal_self`

English:
instance normal_self
  signature: : Normal F F where
  body: fun _ => isIntegral_algebraMap.isAlgebraic
  splits' := fun x => (minpoly.eq_X_sub_C' x).symm ▸ by simp

中文:
实例 normal_self
  签名: : Normal F F where
  定义体: fun _ => isIntegral_algebraMap.isAlgebraic
  splits' := fun x => (minpoly.eq_X_sub_C' x).symm ▸ by simp

Depends on / 依赖: isAlgebraic, isIntegral_algebraMap, isIntegral_algebraMap.isAlgebraic
-/
instance normal_self : Normal F F where
  isAlgebraic := fun _ => isIntegral_algebraMap.isAlgebraic
  splits' := fun x => (minpoly.eq_X_sub_C' x).symm ▸ by simp

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

@[stacks 09HN]
/--
theorem `Normal.tower_top_of_normal` / 定理 `Normal.tower_top_of_normal`

English:
theorem Normal.tower_top_of_normal
  given: [h : Normal F E]
  statement: Normal K E
  proof: normal_iff.2 fun x => by
    obtain ⟨hx, hhx⟩ := h.out x
    rw [algebraMap_eq F K E]; rw [← map_map] at hhx
    exact ⟨hx.tower_top, hhx.of_dvd (map_ne_zero (map_ne_zero (minpoly.ne_zero hx)))
      ((map_dvd_map' _).mpr (minpoly.dvd_map_of_isScalarTower F K x))⟩

中文:
定理 Normal.tower_top_of_normal
  条件: [h : Normal F E]
  结论: Normal K E
  证明: normal_iff.2 fun x => by
    obtain ⟨hx, hhx⟩ := h.out x
    rw [algebraMap_eq F K E]; rw [← map_map] at hhx
    exact ⟨hx.tower_top, hhx.of_dvd (map_ne_zero (map_ne_zero (minpoly.ne_zero hx)))
      ((map_dvd_map' _).mpr (minpoly.dvd_map_of_isScalarTower F K x))⟩

Depends on / 依赖: algebraMap_eq, dvd_map_of_isScalarTower, h.out, hhx.of_dvd, hx.tower_top, map_dvd_map, map_map, map_ne_zero, minpoly, minpoly.dvd_map_of_isScalarTower, minpoly.ne_zero, ne_zero, normal_iff, of_dvd, tower_top
-/
theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2 fun x => by
    obtain ⟨hx, hhx⟩ := h.out x
    rw [algebraMap_eq F K E]; rw [← map_map] at hhx
    exact ⟨hx.tower_top, hhx.of_dvd (map_ne_zero (map_ne_zero (minpoly.ne_zero hx)))
      ((map_dvd_map' _).mpr (minpoly.dvd_map_of_isScalarTower F K x))⟩

/--
Instance `IntermediateField.normal` / 实例 `IntermediateField.normal`

English:
instance IntermediateField.normal
  signature: (K : IntermediateField F E) [Normal F E]
  body: Normal.tower_top_of_normal F K E

中文:
实例 IntermediateField.normal
  签名: (K : 整数ermediateField F E) [Normal F E]
  定义体: Normal.tower_top_of_normal F K E

Depends on / 依赖: Normal, Normal.tower_top_of_normal, tower_top_of_normal
-/
instance IntermediateField.normal (K : IntermediateField F E) [Normal F E] : Normal K E :=
  Normal.tower_top_of_normal F K E

/--
theorem `AlgHom.normal_bijective` / 定理 `AlgHom.normal_bijective`

English:
theorem AlgHom.normal_bijective
  given: [h : Normal F E] (ϕ : E ->ₐ[F] K)
  statement: Function.Bijective ϕ
  proof: h.toIsAlgebraic.bijective_of_isScalarTower' ϕ

中文:
定理 AlgHom.normal_bijective
  条件: [h : Normal F E] (ϕ : E ->ₐ[F] K)
  结论: Function.Bijective ϕ
  证明: h.toIsAlgebraic.bijective_of_isScalarTower' ϕ

Depends on / 依赖: bijective_of_isScalarTower, h.toIsAlgebraic.bijective_of_isScalarTower, toIsAlgebraic
-/
theorem AlgHom.normal_bijective [h : Normal F E] (ϕ : E ->ₐ[F] K) : Function.Bijective ϕ :=
  h.toIsAlgebraic.bijective_of_isScalarTower' ϕ

variable {E F}
variable {E' : Type*} [Field E'] [Algebra F E']

/--
theorem `Normal.of_algEquiv` / 定理 `Normal.of_algEquiv`

English:
theorem Normal.of_algEquiv
  given: [h : Normal F E] (f : E ≃ₐ[F] E')
  statement: Normal F E'
  proof: by
  rw [normal_iff] at h ⊢
  intro x; specialize h (f.symm x)
  rw [← f.apply_symm_apply x]; rw [minpoly.algEquiv_eq]; rw [← f.toAlgHom.comp_algebraMap]; rw [← map_map]
  exact ⟨h.1.map f, h.2.map _⟩

中文:
定理 Normal.of_algEquiv
  条件: [h : Normal F E] (f : E ≃ₐ[F] E')
  结论: Normal F E'
  证明: by
  rw [normal_iff] at h ⊢
  intro x; specialize h (f.symm x)
  rw [← f.apply_symm_apply x]; rw [minpoly.algEquiv_eq]; rw [← f.toAlgHom.comp_algebraMap]; rw [← map_map]
  exact ⟨h.1.map f, h.2.map _⟩

Depends on / 依赖: algEquiv_eq, apply_symm_apply, comp_algebraMap, f.apply_symm_apply, f.symm, f.toAlgHom.comp_algebraMap, map_map, minpoly, minpoly.algEquiv_eq, normal_iff, specialize, toAlgHom
-/
theorem Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E' := by
  rw [normal_iff] at h ⊢
  intro x; specialize h (f.symm x)
  rw [← f.apply_symm_apply x]; rw [minpoly.algEquiv_eq]; rw [← f.toAlgHom.comp_algebraMap]; rw [← map_map]
  exact ⟨h.1.map f, h.2.map _⟩

/--
theorem `AlgEquiv.transfer_normal` / 定理 `AlgEquiv.transfer_normal`

English:
theorem AlgEquiv.transfer_normal
  given: (f : E ≃ₐ[F] E')
  statement: Normal F E ↔ Normal F E'
  proof: ⟨fun _ => Normal.of_algEquiv f, fun _ => Normal.of_algEquiv f.symm⟩

中文:
定理 AlgEquiv.transfer_normal
  条件: (f : E ≃ₐ[F] E')
  结论: Normal F E ↔ Normal F E'
  证明: ⟨fun _ => Normal.of_algEquiv f, fun _ => Normal.of_algEquiv f.symm⟩

Depends on / 依赖: Normal, Normal.of_algEquiv, f.symm, of_algEquiv
-/
theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun _ => Normal.of_algEquiv f, fun _ => Normal.of_algEquiv f.symm⟩

/--
theorem `Normal.of_equiv_equiv` / 定理 `Normal.of_equiv_equiv`

English:
theorem Normal.of_equiv_equiv
  statement: {M N : Type*} [Field N] [Field M] [Algebra M N]
  proof: by
  have := h
  rw [normal_iff] at h ⊢
  intro x
  rw [← g.apply_symm_apply x]
  refine ⟨(h (g.symm x)).1.map_of_comp_eq _ _ hcomp, ?_⟩
  rw [← minpoly.map_eq_of_equiv_equiv hcomp]; rw [map_map]; rw [hcomp]; rw [← map_map]
  exact (h (g.symm x)).2.map _

中文:
定理 Normal.of_equiv_equiv
  结论: {M N : 类型} [Field N] [Field M] [Algebra M N]
  证明: by
  have := h
  rw [normal_iff] at h ⊢
  intro x
  rw [← g.apply_symm_apply x]
  refine ⟨(h (g.symm x)).1.map_of_comp_eq _ _ hcomp, ?_⟩
  rw [← minpoly.map_eq_of_equiv_equiv hcomp]; rw [map_map]; rw [hcomp]; rw [← map_map]
  exact (h (g.symm x)).2.map _

Depends on / 依赖: apply_symm_apply, g.apply_symm_apply, g.symm, map_eq_of_equiv_equiv, map_map, map_of_comp_eq, minpoly, minpoly.map_eq_of_equiv_equiv, normal_iff
-/
theorem Normal.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N]
    [h : Normal F E] {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = (g : E ->+* N).comp (algebraMap F E)) :
    Normal M N := by
  have := h
  rw [normal_iff] at h ⊢
  intro x
  rw [← g.apply_symm_apply x]
  refine ⟨(h (g.symm x)).1.map_of_comp_eq _ _ hcomp, ?_⟩
  rw [← minpoly.map_eq_of_equiv_equiv hcomp]; rw [map_map]; rw [hcomp]; rw [← map_map]
  exact (h (g.symm x)).2.map _

end NormalTower

namespace IntermediateField

variable {F K}
variable {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

@[simp]
/--
theorem `restrictScalars_normal` / 定理 `restrictScalars_normal`

English:
theorem restrictScalars_normal
  given: {E : IntermediateField K L}
  proof: Iff.rfl

中文:
定理 restrictScalars_normal
  条件: {E : 整数ermediateField K L}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem restrictScalars_normal {E : IntermediateField K L} :
    Normal F (E.restrictScalars F) ↔ Normal F E :=
  Iff.rfl

end IntermediateField

variable {F} {K}
variable {K₁ K₂ K₃ : Type*} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ ->ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ ->ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/--
Definition of `AlgHom.restrictNormalAux` / `AlgHom.restrictNormalAux` 的定义

English:
definition AlgHom.restrictNormalAux
  signature: [h : Normal F E]
  body: ⟨ϕ x, by
      suffices (toAlgHom F E K₁).range.map ϕ <= _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx]; rw [← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine ((h.splits z).of_dvd (map_ne_zero (minpoly.ne_zero (h.isIntegral z)))
        (min

中文:
定义 AlgHom.restrictNormalAux
  签名: [h : Normal F E]
  定义体: ⟨ϕ x, by
      suffices (toAlgHom F E K₁).range.map ϕ <= _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx]; rw [← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine ((h.splits z).of_dvd (map_ne_zero (minpoly.ne_zero (h.isIntegral z)))
        (min

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, IsIntegral, Subtype, Subtype.mem, aeval_algHom_apply, coe_toRingHom, degree_eq_one_of_irreducible, h.isIntegral, h.splits, irreducible, isIntegral, map_ne_zero, mem_range_of_degree_eq_one, minpoly, minpoly.dvd, minpoly.irreducible, minpoly.mem_range_of_degree_eq_one, minpoly.ne_zero
-/
def AlgHom.restrictNormalAux [h : Normal F E] :
    (toAlgHom F E K₁).range ->ₐ[F] (toAlgHom F E K₂).range where
  toFun x :=
    ⟨ϕ x, by
      suffices (toAlgHom F E K₁).range.map ϕ <= _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx]; rw [← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine ((h.splits z).of_dvd (map_ne_zero (minpoly.ne_zero (h.isIntegral z)))
        (minpoly.dvd E _ (by simp [aeval_algHom_apply]))).degree_eq_one_of_irreducible
        (minpoly.irreducible ?_)
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      suffices IsIntegral F _ by exact this.tower_top
      exact ((h.isIntegral z).map <| toAlgHom F E K₁).map ϕ⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
map_add' x y := Subtype.ext by simp
map_mul' x y := Subtype.ext by simp
  commutes' x := Subtype.ext (ϕ.commutes x)

/-- Restrict algebra homomorphism to normal subfield. -/
@[stacks 0BME "Part 1"]
/--
Definition of `AlgHom.restrictNormal` / `AlgHom.restrictNormal` 的定义

English:
definition AlgHom.restrictNormal
  signature: [Normal F E]
  body: ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂)).symm.toAlgHom.comp
        (ϕ.restrictNormalAux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₁)).toAlgHom

中文:
定义 AlgHom.restrictNormal
  签名: [Normal F E]
  定义体: ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂)).symm.toAlgHom.comp
        (ϕ.restrictNormalAux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₁)).toAlgHom

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, ofInjectiveField, restrictNormalAux, symm.toAlgHom.comp, toAlgHom
-/
def AlgHom.restrictNormal [Normal F E] : E ->ₐ[F] E :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂)).symm.toAlgHom.comp
        (ϕ.restrictNormalAux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₁)).toAlgHom

/--
Definition of `AlgHom.restrictNormal'` / `AlgHom.restrictNormal'` 的定义

English:
definition AlgHom.restrictNormal'
  signature: [Normal F E]
  body: AlgEquiv.ofBijective (AlgHom.restrictNormal ϕ E) (AlgHom.normal_bijective F E E _)

@[simp]

中文:
定义 AlgHom.restrictNormal'
  签名: [Normal F E]
  定义体: AlgEquiv.ofBijective (AlgHom.restrictNormal ϕ E) (AlgHom.normal_bijective F E E _)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgHom, AlgHom.normal_bijective, AlgHom.restrictNormal, normal_bijective, ofBijective, restrictNormal
-/
def AlgHom.restrictNormal' [Normal F E] : Gal(E/F) :=
  AlgEquiv.ofBijective (AlgHom.restrictNormal ϕ E) (AlgHom.normal_bijective F E E _)

@[simp]
/--
theorem `AlgHom.restrictNormal_commutes` / 定理 `AlgHom.restrictNormal_commutes`

English:
theorem AlgHom.restrictNormal_commutes
  given: [Normal F E] (x : E)
  proof: Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂))
      (ϕ.restrictNormalAux E ⟨IsScalarTower.toAlgHom F E K₁ x, x, rfl⟩))

中文:
定理 AlgHom.restrictNormal_commutes
  条件: [Normal F E] (x : E)
  证明: Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂))
      (ϕ.restrictNormalAux E ⟨IsScalarTower.toAlgHom F E K₁ x, x, rfl⟩))

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, Subtype, Subtype.ext_iff.mp, apply_symm_apply, ext_iff, ofInjectiveField, restrictNormalAux, toAlgHom
-/
theorem AlgHom.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x) :=
  Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂))
      (ϕ.restrictNormalAux E ⟨IsScalarTower.toAlgHom F E K₁ x, x, rfl⟩))

/--
theorem `AlgHom.restrictNormal_comp` / 定理 `AlgHom.restrictNormal_comp`

English:
theorem AlgHom.restrictNormal_comp
  given: [Normal F E]
  proof: AlgHom.ext fun _ =>
    (algebraMap E K₃).injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])

中文:
定理 AlgHom.restrictNormal_comp
  条件: [Normal F E]
  证明: AlgHom.ext fun _ =>
    (algebraMap E K₃).injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.ext, AlgHom.restrictNormal_commutes, algebraMap, comp_apply, injective, restrictNormal_commutes
-/
theorem AlgHom.restrictNormal_comp [Normal F E] :
    (ψ.restrictNormal E).comp (ϕ.restrictNormal E) = (ψ.comp ϕ).restrictNormal E :=
  AlgHom.ext fun _ =>
    (algebraMap E K₃).injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])

/--
Definition of `AlgEquiv.restrictNormal` / `AlgEquiv.restrictNormal` 的定义

English:
definition AlgEquiv.restrictNormal
  signature: [Normal F E]
  body: AlgHom.restrictNormal' χ.toAlgHom E

@[simp]

中文:
定义 AlgEquiv.restrictNormal
  签名: [Normal F E]
  定义体: AlgHom.restrictNormal' χ.toAlgHom E

@[simp]

Depends on / 依赖: AlgHom, AlgHom.restrictNormal, restrictNormal, toAlgHom
-/
def AlgEquiv.restrictNormal [Normal F E] : Gal(E/F) :=
  AlgHom.restrictNormal' χ.toAlgHom E

@[simp]
/--
theorem `AlgEquiv.restrictNormal_commutes` / 定理 `AlgEquiv.restrictNormal_commutes`

English:
theorem AlgEquiv.restrictNormal_commutes
  given: [Normal F E] (x : E)
  proof: χ.toAlgHom.restrictNormal_commutes E x

中文:
定理 AlgEquiv.restrictNormal_commutes
  条件: [Normal F E] (x : E)
  证明: χ.toAlgHom.restrictNormal_commutes E x

Depends on / 依赖: restrictNormal_commutes, toAlgHom, toAlgHom.restrictNormal_commutes
-/
theorem AlgEquiv.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x) :=
  χ.toAlgHom.restrictNormal_commutes E x

/--
theorem `AlgEquiv.restrictNormal_apply` / 定理 `AlgEquiv.restrictNormal_apply`

English:
theorem AlgEquiv.restrictNormal_apply
  statement: (L : IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F))
  proof: AlgEquiv.restrictNormal_commutes σ L x

中文:
定理 AlgEquiv.restrictNormal_apply
  结论: (L : 整数ermediateField F K₁) [Normal F L] (σ : Gal(K₁/F))
  证明: AlgEquiv.restrictNormal_commutes σ L x

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal_commutes, restrictNormal_commutes
-/
theorem AlgEquiv.restrictNormal_apply (L : IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F))
    (x : L) : restrictNormal σ L x = σ x :=
  AlgEquiv.restrictNormal_commutes σ L x

/--
theorem `AlgEquiv.restrictNormal_eq_one_iff` / 定理 `AlgEquiv.restrictNormal_eq_one_iff`

English:
theorem AlgEquiv.restrictNormal_eq_one_iff
  statement: (L : IntermediateField F K₁) [Normal F L]
  proof: by
  simp [AlgEquiv.ext_iff, Subtype.ext_iff, AlgEquiv.restrictNormal_apply]

中文:
定理 AlgEquiv.restrictNormal_eq_one_iff
  结论: (L : 整数ermediateField F K₁) [Normal F L]
  证明: by
  simp [AlgEquiv.ext_iff, Subtype.ext_iff, AlgEquiv.restrictNormal_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff, AlgEquiv.restrictNormal_apply, Subtype, Subtype.ext_iff, ext_iff, restrictNormal_apply
-/
theorem AlgEquiv.restrictNormal_eq_one_iff (L : IntermediateField F K₁) [Normal F L]
    (σ : Gal(K₁/F)) : restrictNormal σ L = 1 ↔ forall x in L, σ x = x := by
  simp [AlgEquiv.ext_iff, Subtype.ext_iff, AlgEquiv.restrictNormal_apply]

/--
theorem `AlgEquiv.restrictNormal_trans` / 定理 `AlgEquiv.restrictNormal_trans`

English:
theorem AlgEquiv.restrictNormal_trans
  given: [Normal F E]
  proof: AlgEquiv.ext fun _ =>
    (algebraMap E K₃).injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])

中文:
定理 AlgEquiv.restrictNormal_trans
  条件: [Normal F E]
  证明: AlgEquiv.ext fun _ =>
    (algebraMap E K₃).injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgEquiv.restrictNormal_commutes, AlgEquiv.trans_apply, algebraMap, injective, restrictNormal_commutes, trans_apply
-/
theorem AlgEquiv.restrictNormal_trans [Normal F E] :
    (χ.trans ω).restrictNormal E = (χ.restrictNormal E).trans (ω.restrictNormal E) :=
  AlgEquiv.ext fun _ =>
    (algebraMap E K₃).injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])

/--
Definition of `AlgEquiv.restrictNormalHom` / `AlgEquiv.restrictNormalHom` 的定义

English:
definition AlgEquiv.restrictNormalHom
  signature: [Normal F E]
  body: MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E

中文:
定义 AlgEquiv.restrictNormalHom
  签名: [Normal F E]
  定义体: MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E

Depends on / 依赖: MonoidHom, MonoidHom.mk, restrictNormal, restrictNormal_trans
-/
def AlgEquiv.restrictNormalHom [Normal F E] : Gal(K₁/F) ->* Gal(E/F) :=
  MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E

/--
lemma `AlgEquiv.restrictNormalHom_apply` / 引理 `AlgEquiv.restrictNormalHom_apply`

English:
lemma AlgEquiv.restrictNormalHom_apply
  statement: (L : IntermediateField F K₁) [Normal F L]
  proof: AlgEquiv.restrictNormal_commutes σ L x

中文:
引理 AlgEquiv.restrictNormalHom_apply
  结论: (L : 整数ermediateField F K₁) [Normal F L]
  证明: AlgEquiv.restrictNormal_commutes σ L x

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal_commutes, restrictNormal_commutes
-/
lemma AlgEquiv.restrictNormalHom_apply (L : IntermediateField F K₁) [Normal F L]
    (σ : Gal(K₁/F)) (x : L) : restrictNormalHom L σ x = σ x :=
  AlgEquiv.restrictNormal_commutes σ L x

variable (F K₁)

/-- If `K₁/E/F` is a tower of fields with `E/F` normal then `AlgHom.restrictNormal'` is an
equivalence. -/
@[simps, stacks 0BR4]
/--
Definition of `Normal.algHomEquivAut` / `Normal.algHomEquivAut` 的定义

English:
definition Normal.algHomEquivAut
  signature: [Normal F E]
  body: AlgHom.restrictNormal' σ E
  invFun σ := (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom
  left_inv σ := by
    ext
    simp [AlgHom.restrictNormal']
  right_inv σ := by
    ext
    simp only [AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
    apply FaithfulSMul.algebraMap_injective E K₁
    rw [

中文:
定义 Normal.algHomEquivAut
  签名: [Normal F E]
  定义体: AlgHom.restrictNormal' σ E
  invFun σ := (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom
  left_inv σ := by
    ext
    simp [AlgHom.restrictNormal']
  right_inv σ := by
    ext
    simp only [AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
    apply FaithfulSMul.algebraMap_injective E K₁
    rw [

Depends on / 依赖: AlgHom, AlgHom.restrictNormal, restrictNormal
-/
def Normal.algHomEquivAut [Normal F E] : (E ->ₐ[F] K₁) ≃ Gal(E/F) where
  toFun σ := AlgHom.restrictNormal' σ E
  invFun σ := (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom
  left_inv σ := by
    ext
    simp [AlgHom.restrictNormal']
  right_inv σ := by
    ext
    simp only [AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
    apply FaithfulSMul.algebraMap_injective E K₁
    rw [AlgHom.restrictNormal_commutes]
    simp

end Restrict

section lift

set_option backward.defeqAttrib.useBackward true in
/-- The group homomorphism given by restricting an algebra isomorphism to itself
is the identity map. -/
@[simp]
/--
theorem `AlgEquiv.restrictNormalHom_id` / 定理 `AlgEquiv.restrictNormalHom_id`

English:
theorem AlgEquiv.restrictNormalHom_id
  statement: (F K : Type*)
  proof: by
  ext f x
  dsimp only [restrictNormalHom, MonoidHom.mk'_apply, MonoidHom.id_apply]
  apply (algebraMap K K).injective
  rw [AlgEquiv.restrictNormal_commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

中文:
定理 AlgEquiv.restrictNormalHom_id
  结论: (F K : 类型)
  证明: by
  ext f x
  dsimp only [restrictNormalHom, MonoidHom.mk'_apply, MonoidHom.id_apply]
  apply (algebraMap K K).injective
  rw [AlgEquiv.restrictNormal_commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal_commutes, Algebra, Algebra.algebraMap_self, MonoidHom, MonoidHom.id_apply, MonoidHom.mk, RingHom, RingHom.id_apply, _apply, algebraMap, algebraMap_self, id_apply, injective, restrictNormalHom, restrictNormal_commutes
-/
theorem AlgEquiv.restrictNormalHom_id (F K : Type*)
    [Field F] [Field K] [Algebra F K] [Normal F K] :
    AlgEquiv.restrictNormalHom K = MonoidHom.id Gal(K/F) := by
  ext f x
  dsimp only [restrictNormalHom, MonoidHom.mk'_apply, MonoidHom.id_apply]
  apply (algebraMap K K).injective
  rw [AlgEquiv.restrictNormal_commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

namespace IsScalarTower

/--
theorem `AlgEquiv.restrictNormalHom_comp` / 定理 `AlgEquiv.restrictNormalHom_comp`

English:
theorem AlgEquiv.restrictNormalHom_comp
  statement: (F K₁ K₂ K₃ : Type*)
  proof: by
  ext f x
  apply (algebraMap K₁ K₃).injective
  rw [IsScalarTower.algebraMap_eq K₁ K₂ K₃]
  simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, RingHom.coe_comp, Function.comp_apply,
    ← algebraMap_apply, AlgEquiv.restrictNormal_commutes, MonoidHom.coe_comp]

中文:
定理 AlgEquiv.restrictNormalHom_comp
  结论: (F K₁ K₂ K₃ : 类型)
  证明: by
  ext f x
  apply (algebraMap K₁ K₃).injective
  rw [IsScalarTower.algebraMap_eq K₁ K₂ K₃]
  simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, RingHom.coe_comp, Function.comp_apply,
    ← algebraMap_apply, AlgEquiv.restrictNormal_commutes, MonoidHom.coe_comp]

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom, AlgEquiv.restrictNormal_commutes, Function, Function.comp_apply, IsScalarTower, IsScalarTower.algebraMap_eq, MonoidHom, MonoidHom.coe_comp, MonoidHom.mk, RingHom, RingHom.coe_comp, _apply, algebraMap, algebraMap_apply, algebraMap_eq, coe_comp, comp_apply, injective, restrictNormalHom
-/
theorem AlgEquiv.restrictNormalHom_comp (F K₁ K₂ K₃ : Type*)
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] :
    AlgEquiv.restrictNormalHom K₁ =
    (AlgEquiv.restrictNormalHom K₁).comp
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := K₃) K₂) := by
  ext f x
  apply (algebraMap K₁ K₃).injective
  rw [IsScalarTower.algebraMap_eq K₁ K₂ K₃]
  simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, RingHom.coe_comp, Function.comp_apply,
    ← algebraMap_apply, AlgEquiv.restrictNormal_commutes, MonoidHom.coe_comp]

/--
theorem `AlgEquiv.restrictNormalHom_comp_apply` / 定理 `AlgEquiv.restrictNormalHom_comp_apply`

English:
theorem AlgEquiv.restrictNormalHom_comp_apply
  statement: (K₁ K₂ : Type*) {F K₃ : Type*}
  proof: by
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp F K₁ K₂ K₃]; rw [MonoidHom.comp_apply]

中文:
定理 AlgEquiv.restrictNormalHom_comp_apply
  结论: (K₁ K₂ : 类型) {F K₃ : 类型}
  证明: by
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp F K₁ K₂ K₃]; rw [MonoidHom.comp_apply]

Depends on / 依赖: AlgEquiv, IsScalarTower, IsScalarTower.AlgEquiv.restrictNormalHom_comp, MonoidHom, MonoidHom.comp_apply, comp_apply, restrictNormalHom_comp
-/
theorem AlgEquiv.restrictNormalHom_comp_apply (K₁ K₂ : Type*) {F K₃ : Type*}
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] (f : K₃ ≃ₐ[F] K₃) :
    AlgEquiv.restrictNormalHom K₁ f =
    (AlgEquiv.restrictNormalHom K₁) (AlgEquiv.restrictNormalHom K₂ f) := by
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp F K₁ K₂ K₃]; rw [MonoidHom.comp_apply]

end IsScalarTower

end lift
