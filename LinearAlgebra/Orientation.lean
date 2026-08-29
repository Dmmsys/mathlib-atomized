/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.Ray
public import Mathlib.LinearAlgebra.Determinant

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `Orientation` is a type synonym for `Module.Ray` for the case where the module is that of
  alternating maps from a module to its underlying ring. An orientation may be associated with an
  alternating map or with a basis.

* `Module.Oriented` is a type class for a choice of orientation of a module that is considered
  the positive orientation.

## Implementation notes

`Orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `Fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/

@[expose] public section

noncomputable section

open Module

section OrderedCommSemiring

variable (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (ι ι' : Type*)

/--
Definition of `Orientation` / `Orientation` 的定义

English:
abbreviation Orientation
  body: Module.Ray R (M [⋀^ι]->ₗ[R] R)

中文:
缩写 Orientation
  定义体: Module.Ray R (M [⋀^ι]->ₗ[R] R)

Depends on / 依赖: Module, Module.Ray
-/
abbrev Orientation := Module.Ray R (M [⋀^ι]->ₗ[R] R)

/--
Definition of `Module.Oriented` / `Module.Oriented` 的定义

English:
class Module.Oriented
  parameters: where
  axioms and operations (1):
    - positiveOrientation : Orientation R M ι

中文:
类 Module.Oriented
  参数: where
  公理与运算 (1 个):
    - positiveOrientation : Orientation R M ι
-/
class Module.Oriented where
  /-- Fix a positive orientation. -/
  positiveOrientation : Orientation R M ι

export Module.Oriented (positiveOrientation)

variable {R M}

/--
Definition of `Orientation.map` / `Orientation.map` 的定义

English:
definition Orientation.map
  signature: (e : M ≃ₗ[R] N)
  body: Module.Ray.map AlternatingMap.domLCongr R R ι R e

@[simp]

中文:
定义 Orientation.map
  签名: (e : M ≃ₗ[R] N)
  定义体: Module.Ray.map AlternatingMap.domLCongr R R ι R e

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.domLCongr, Module, Module.Ray.map, domLCongr
-/
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
Module.Ray.map AlternatingMap.domLCongr R R ι R e

@[simp]
/--
theorem `Orientation.map_apply` / 定理 `Orientation.map_apply`

English:
theorem Orientation.map_apply
  given: (e : M ≃ₗ[R] N) (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0)
  proof: rfl

@[simp]

中文:
定理 Orientation.map_apply
  条件: (e : M ≃ₗ[R] N) (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0)
  证明: rfl

@[simp]
-/
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.compLinearEquiv_eq_zero_iff e.symm).mp hv) :=
  rfl

@[simp]
/--
theorem `Orientation.map_refl` / 定理 `Orientation.map_refl`

English:
theorem Orientation.map_refl
  statement: (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _
  proof: by
  rw [Orientation.map]; rw [AlternatingMap.domLCongr_refl]; rw [Module.Ray.map_refl]

@[simp]

中文:
定理 Orientation.map_refl
  结论: (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _
  证明: by
  rw [Orientation.map]; rw [AlternatingMap.domLCongr_refl]; rw [Module.Ray.map_refl]

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.domLCongr_refl, Module, Module.Ray.map_refl, Orientation, Orientation.map, domLCongr_refl, map_refl
-/
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _ := by
  rw [Orientation.map]; rw [AlternatingMap.domLCongr_refl]; rw [Module.Ray.map_refl]

@[simp]
/--
theorem `Orientation.map_symm` / 定理 `Orientation.map_symm`

English:
theorem Orientation.map_symm
  given: (e : M ≃ₗ[R] N)
  proof: rfl

中文:
定理 Orientation.map_symm
  条件: (e : M ≃ₗ[R] N)
  证明: rfl
-/
theorem Orientation.map_symm (e : M ≃ₗ[R] N) :
    (Orientation.map ι e).symm = Orientation.map ι e.symm := rfl

section Reindex

variable (R M) {ι ι'}

/--
Definition of `Orientation.reindex` / `Orientation.reindex` 的定义

English:
definition Orientation.reindex
  signature: (e : ι ≃ ι')
  body: Module.Ray.map AlternatingMap.domDomCongrₗ R e

@[simp]

中文:
定义 Orientation.reindex
  签名: (e : ι ≃ ι')
  定义体: Module.Ray.map AlternatingMap.domDomCongrₗ R e

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.domDomCongr, Module, Module.Ray.map
-/
def Orientation.reindex (e : ι ≃ ι') : Orientation R M ι ≃ Orientation R M ι' :=
Module.Ray.map AlternatingMap.domDomCongrₗ R e

@[simp]
/--
theorem `Orientation.reindex_apply` / 定理 `Orientation.reindex_apply`

English:
theorem Orientation.reindex_apply
  given: (e : ι ≃ ι') (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0)
  proof: rfl

@[simp]

中文:
定理 Orientation.reindex_apply
  条件: (e : ι ≃ ι') (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0)
  证明: rfl

@[simp]
-/
theorem Orientation.reindex_apply (e : ι ≃ ι') (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0) :
    Orientation.reindex R M e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.domDomCongr e) (mt (v.domDomCongr_eq_zero_iff e).mp hv) :=
  rfl

@[simp]
/--
theorem `Orientation.reindex_refl` / 定理 `Orientation.reindex_refl`

English:
theorem Orientation.reindex_refl
  statement: (Orientation.reindex R M <| Equiv.refl ι) = Equiv.refl _
  proof: by
  rw [Orientation.reindex]; rw [AlternatingMap.domDomCongrₗ_refl]; rw [Module.Ray.map_refl]

@[simp]

中文:
定理 Orientation.reindex_refl
  结论: (Orientation.reindex R M <| Equiv.refl ι) = Equiv.refl _
  证明: by
  rw [Orientation.reindex]; rw [AlternatingMap.domDomCongrₗ_refl]; rw [Module.Ray.map_refl]

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.domDomCongr, Module, Module.Ray.map_refl, Orientation, Orientation.reindex, map_refl, reindex
-/
theorem Orientation.reindex_refl : (Orientation.reindex R M <| Equiv.refl ι) = Equiv.refl _ := by
  rw [Orientation.reindex]; rw [AlternatingMap.domDomCongrₗ_refl]; rw [Module.Ray.map_refl]

@[simp]
/--
theorem `Orientation.reindex_symm` / 定理 `Orientation.reindex_symm`

English:
theorem Orientation.reindex_symm
  given: (e : ι ≃ ι')
  proof: rfl

中文:
定理 Orientation.reindex_symm
  条件: (e : ι ≃ ι')
  证明: rfl
-/
theorem Orientation.reindex_symm (e : ι ≃ ι') :
    (Orientation.reindex R M e).symm = Orientation.reindex R M e.symm :=
  rfl

end Reindex

/-- A module is canonically oriented with respect to an empty index type. -/
instance (priority := 100) IsEmpty.oriented [IsEmpty ι] : Module.Oriented R M ι where
  positiveOrientation :=
rayOfNeZero R (AlternatingMap.constLinearEquivOfIsEmpty 1)
      AlternatingMap.constLinearEquivOfIsEmpty.injective.ne (by exact one_ne_zero)

@[simp]
/--
theorem `Orientation.map_positiveOrientation_of_isEmpty` / 定理 `Orientation.map_positiveOrientation_of_isEmpty`

English:
theorem Orientation.map_positiveOrientation_of_isEmpty
  given: [IsEmpty ι] (f : M ≃ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 Orientation.map_positiveOrientation_of_isEmpty
  条件: [IsEmpty ι] (f : M ≃ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem Orientation.map_positiveOrientation_of_isEmpty [IsEmpty ι] (f : M ≃ₗ[R] N) :
    Orientation.map ι f positiveOrientation = positiveOrientation := rfl

@[simp]
/--
theorem `Orientation.map_of_isEmpty` / 定理 `Orientation.map_of_isEmpty`

English:
theorem Orientation.map_of_isEmpty
  given: [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  proof: by
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.compLinearMap_apply]
  congr
  simp only [LinearEquiv.coe_coe, eq_iff_true_of_subsingleton]

中文:
定理 Orientation.map_of_isEmpty
  条件: [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  证明: by
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.compLinearMap_apply]
  congr
  simp only [LinearEquiv.coe_coe, eq_iff_true_of_subsingleton]

Depends on / 依赖: AlternatingMap, AlternatingMap.compLinearMap_apply, LinearEquiv, LinearEquiv.coe_coe, Module, Module.Ray.ind, Orientation, Orientation.map_apply, coe_coe, compLinearMap_apply, eq_iff_true_of_subsingleton, map_apply
-/
theorem Orientation.map_of_isEmpty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = x := by
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.compLinearMap_apply]
  congr
  simp only [LinearEquiv.coe_coe, eq_iff_true_of_subsingleton]

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

@[simp]
/--
theorem `Orientation.map_neg` / 定理 `Orientation.map_neg`

English:
theorem Orientation.map_neg
  given: {ι : Type*} (f : M ≃ₗ[R] N) (x : Orientation R M ι)
  proof: Module.Ray.map_neg _ x

@[simp]

中文:
定理 Orientation.map_neg
  条件: {ι : 类型} (f : M ≃ₗ[R] N) (x : Orientation R M ι)
  证明: Module.Ray.map_neg _ x

@[simp]
-/
protected theorem Orientation.map_neg {ι : Type*} (f : M ≃ₗ[R] N) (x : Orientation R M ι) :
    Orientation.map ι f (-x) = -Orientation.map ι f x :=
  Module.Ray.map_neg _ x

@[simp]
/--
theorem `Orientation.reindex_neg` / 定理 `Orientation.reindex_neg`

English:
theorem Orientation.reindex_neg
  given: {ι ι' : Type*} (e : ι ≃ ι') (x : Orientation R M ι)
  proof: Module.Ray.map_neg _ x

中文:
定理 Orientation.reindex_neg
  条件: {ι ι' : 类型} (e : ι ≃ ι') (x : Orientation R M ι)
  证明: Module.Ray.map_neg _ x
-/
protected theorem Orientation.reindex_neg {ι ι' : Type*} (e : ι ≃ ι') (x : Orientation R M ι) :
    Orientation.reindex R M e (-x) = -Orientation.reindex R M e x :=
  Module.Ray.map_neg _ x

namespace Module.Basis

variable {ι ι' : Type*}

/--
theorem `map_orientation_eq_det_inv_smul` / 定理 `map_orientation_eq_det_inv_smul`

English:
theorem map_orientation_eq_det_inv_smul
  statement: [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
  proof: by
  cases nonempty_fintype ι
  let := Classical.decEq ι
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]; rw [smul_rayOfNeZero]; rw [ray_eq_iff]; rw [Units.smul_def]; rw [(g.compLinearMap f.symm).eq_smul_basis_det e]; rw [g.eq_smul_basis_det e]; rw [AlternatingMap.co

中文:
定理 map_orientation_eq_det_inv_smul
  结论: [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
  证明: by
  cases nonempty_fintype ι
  let := Classical.decEq ι
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]; rw [smul_rayOfNeZero]; rw [ray_eq_iff]; rw [Units.smul_def]; rw [(g.compLinearMap f.symm).eq_smul_basis_det e]; rw [g.eq_smul_basis_det e]; rw [AlternatingMap.co

Depends on / 依赖: AlternatingMap, AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Basis.det_comp, Basis.det_self, Classical, Classical.decEq, LinearEquiv, LinearEquiv.symm, Module, Module.Ray.ind, Orientation, Orientation.map_apply, Units.smul_def, compLinearMap, compLinearMap_apply, det_comp, det_self, eq_smul_basis_det, f.symm
-/
theorem map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x := by
  cases nonempty_fintype ι
  let := Classical.decEq ι
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]; rw [smul_rayOfNeZero]; rw [ray_eq_iff]; rw [Units.smul_def]; rw [(g.compLinearMap f.symm).eq_smul_basis_det e]; rw [g.eq_smul_basis_det e]; rw [AlternatingMap.compLinearMap_apply]; rw [AlternatingMap.smul_apply]; rw [show (fun i => (LinearEquiv.symm f).toLinearMap (e i)) = (LinearEquiv.symm f).toLinearMap ∘ e
    by rfl]; rw [Basis.det_comp]; rw [Basis.det_self]; rw [mul_one]; rw [smul_eq_mul]; rw [mul_comm]; rw [mul_smul]; rw [LinearEquiv.coe_inv_det]

variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/--
Definition of `orientation` / `orientation` 的定义

English:
definition orientation
  signature: (e : Basis ι R M)
  body: rayOfNeZero R _ e.det_ne_zero

中文:
定义 orientation
  签名: (e : Basis ι R M)
  定义体: rayOfNeZero R _ e.det_ne_zero
-/
protected def orientation (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero

/--
theorem `orientation_map` / 定理 `orientation_map`

English:
theorem orientation_map
  given: (e : Basis ι R M) (f : M ≃ₗ[R] N)
  proof: by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']

中文:
定理 orientation_map
  条件: (e : Basis ι R M) (f : M ≃ₗ[R] N)
  证明: by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']

Depends on / 依赖: Basis.det_map, Basis.orientation, Orientation, Orientation.map_apply, det_map, map_apply, orientation, simp_rw
-/
theorem orientation_map (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).orientation = Orientation.map ι f e.orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']

/--
theorem `orientation_reindex` / 定理 `orientation_reindex`

English:
theorem orientation_reindex
  given: (e : Basis ι R M) (eι : ι ≃ ι')
  proof: by
  simp_rw [Basis.orientation, Orientation.reindex_apply, Basis.det_reindex']

中文:
定理 orientation_reindex
  条件: (e : Basis ι R M) (eι : ι ≃ ι')
  证明: by
  simp_rw [Basis.orientation, Orientation.reindex_apply, Basis.det_reindex']

Depends on / 依赖: Basis.det_reindex, Basis.orientation, Orientation, Orientation.reindex_apply, det_reindex, orientation, reindex_apply, simp_rw
-/
theorem orientation_reindex (e : Basis ι R M) (eι : ι ≃ ι') :
    (e.reindex eι).orientation = Orientation.reindex R M eι e.orientation := by
  simp_rw [Basis.orientation, Orientation.reindex_apply, Basis.det_reindex']

/--
theorem `orientation_unitsSMul` / 定理 `orientation_unitsSMul`

English:
theorem orientation_unitsSMul
  given: (e : Basis ι R M) (w : ι -> Units R)
  proof: by
  rw [Basis.orientation]; rw [Basis.orientation]; rw [smul_rayOfNeZero]; rw [ray_eq_iff]; rw [e.det.eq_smul_basis_det (e.unitsSMul w)]; rw [det_unitsSMul_self]; rw [Units.smul_def]; rw [smul_smul]
  norm_cast
  simp only [inv_mul_cancel, Units.val_one, one_smul]
  exact SameRay.rfl

@[simp]

中文:
定理 orientation_unitsSMul
  条件: (e : Basis ι R M) (w : ι -> Units R)
  证明: by
  rw [Basis.orientation]; rw [Basis.orientation]; rw [smul_rayOfNeZero]; rw [ray_eq_iff]; rw [e.det.eq_smul_basis_det (e.unitsSMul w)]; rw [det_unitsSMul_self]; rw [Units.smul_def]; rw [smul_smul]
  norm_cast
  simp only [inv_mul_cancel, Units.val_one, one_smul]
  exact SameRay.rfl

@[simp]

Depends on / 依赖: Basis.orientation, SameRay, SameRay.rfl, Units.smul_def, Units.val_one, det_unitsSMul_self, e.det.eq_smul_basis_det, e.unitsSMul, eq_smul_basis_det, inv_mul_cancel, one_smul, orientation, ray_eq_iff, smul_def, smul_rayOfNeZero, smul_smul, unitsSMul, val_one
-/
theorem orientation_unitsSMul (e : Basis ι R M) (w : ι -> Units R) :
    (e.unitsSMul w).orientation = (∏ i, w i)⁻¹ • e.orientation := by
  rw [Basis.orientation]; rw [Basis.orientation]; rw [smul_rayOfNeZero]; rw [ray_eq_iff]; rw [e.det.eq_smul_basis_det (e.unitsSMul w)]; rw [det_unitsSMul_self]; rw [Units.smul_def]; rw [smul_smul]
  norm_cast
  simp only [inv_mul_cancel, Units.val_one, one_smul]
  exact SameRay.rfl

@[simp]
/--
theorem `orientation_isEmpty` / 定理 `orientation_isEmpty`

English:
theorem orientation_isEmpty
  given: [IsEmpty ι] (b : Basis ι R M)
  proof: by
  rw [Basis.orientation]
  congr
  exact b.det_isEmpty

中文:
定理 orientation_isEmpty
  条件: [IsEmpty ι] (b : Basis ι R M)
  证明: by
  rw [Basis.orientation]
  congr
  exact b.det_isEmpty

Depends on / 依赖: Basis.orientation, b.det_isEmpty, det_isEmpty, orientation
-/
theorem orientation_isEmpty [IsEmpty ι] (b : Basis ι R M) :
    b.orientation = positiveOrientation := by
  rw [Basis.orientation]
  congr
  exact b.det_isEmpty

end Module.Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*}

namespace Orientation

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_or_eq_neg_of_isEmpty` / 定理 `eq_or_eq_neg_of_isEmpty`

English:
theorem eq_or_eq_neg_of_isEmpty
  given: [IsEmpty ι] (o : Orientation R M ι)
  proof: by
  induction o using Module.Ray.ind with | h x hx =>
  dsimp [positiveOrientation]
  simp only [ray_eq_iff]
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  intro h
  set f : (M [⋀^ι]->ₗ[R] R) ≃ₗ[R] R := AlternatingMap.constLinearEquivOfIsEmpty.symm
  have H : LinearIndependent R ![f x, 1

中文:
定理 eq_or_eq_neg_of_isEmpty
  条件: [IsEmpty ι] (o : Orientation R M ι)
  证明: by
  induction o using Module.Ray.ind with | h x hx =>
  dsimp [positiveOrientation]
  simp only [ray_eq_iff]
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  intro h
  set f : (M [⋀^ι]->ₗ[R] R) ≃ₗ[R] R := AlternatingMap.constLinearEquivOfIsEmpty.symm
  have H : LinearIndependent R ![f x, 1

Depends on / 依赖: AlternatingMap, AlternatingMap.constLinearEquivOfIsEmpty.symm, Fin.sum_univ_succ, Finset, Finset.univ, LinearIndependent, Module, Module.Ray.ind, constLinearEquivOfIsEmpty, convert, f.ker, f.toLinearMap, fin_cases, h.map, linearIndependent_iff, positiveOrientation, ray_eq_iff, sameRay_or_sameRay_neg_iff_not_linearIndependent, sum_univ_succ, toLinearMap
-/
theorem eq_or_eq_neg_of_isEmpty [IsEmpty ι] (o : Orientation R M ι) :
    o = positiveOrientation ∨ o = -positiveOrientation := by
  induction o using Module.Ray.ind with | h x hx =>
  dsimp [positiveOrientation]
  simp only [ray_eq_iff]
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  intro h
  set f : (M [⋀^ι]->ₗ[R] R) ≃ₗ[R] R := AlternatingMap.constLinearEquivOfIsEmpty.symm
  have H : LinearIndependent R ![f x, 1] := by
    convert! h.map' f.toLinearMap f.ker
    ext i
    fin_cases i <;> simp [f]
  rw [linearIndependent_iff'] at H
  simpa using H Finset.univ ![1, -f x] (by simp [Fin.sum_univ_succ]) 0 (by simp)

end Orientation

namespace Module.Basis

variable [Fintype ι] [DecidableEq ι]

/--
theorem `orientation_eq_iff_det_pos` / 定理 `orientation_eq_iff_det_pos`

English:
theorem orientation_eq_iff_det_pos
  given: (e₁ e₂ : Basis ι R M)
  proof: calc
    e₁.orientation = e₂.orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).ne_zero

中文:
定理 orientation_eq_iff_det_pos
  条件: (e₁ e₂ : Basis ι R M)
  证明: calc
    e₁.orientation = e₂.orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).ne_zero

Depends on / 依赖: SameRay, det.eq_smul_basis_det, det_ne_zero, eq_smul_basis_det, isUnit_det, ne_zero, orientation, ray_eq_iff, sameRay_smul_left_iff_of_ne
-/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) :
    e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.orientation = e₂.orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).ne_zero

/--
theorem `orientation_eq_or_eq_neg` / 定理 `orientation_eq_or_eq_neg`

English:
theorem orientation_eq_or_eq_neg
  given: (e : Basis ι R M) (x : Orientation R M ι)
  proof: by
  induction x using Module.Ray.ind with | h x hx =>
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_i

中文:
定理 orientation_eq_or_eq_neg
  条件: (e : Basis ι R M) (x : Orientation R M ι)
  证明: by
  induction x using Module.Ray.ind with | h x hx =>
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_i

Depends on / 依赖: Basis.orientation, Module, Module.Ray.ind, det_ne_zero, e.det_ne_zero, eq_smul_basis_det, lt_or_lt_iff_ne, map_basis_ne_zero_iff, ne_comm, neg_rayOfNeZero, orientation, ray_eq_iff, sameRay_neg_smul_left_iff_of_ne, sameRay_smul_left_iff_of_ne, x.eq_smul_basis_det, x.map_basis_ne_zero_iff
-/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x = e.orientation ∨ x = -e.orientation := by
  induction x using Module.Ray.ind with | h x hx =>
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_iff_ne, ne_comm]

/--
theorem `orientation_ne_iff_eq_neg` / 定理 `orientation_ne_iff_eq_neg`

English:
theorem orientation_ne_iff_eq_neg
  given: (e : Basis ι R M) (x : Orientation R M ι)
  proof: ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩

中文:
定理 orientation_ne_iff_eq_neg
  条件: (e : Basis ι R M) (x : Orientation R M ι)
  证明: ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩

Depends on / 依赖: Module, Module.Ray.ne_neg_self, e.orientation, e.orientation_eq_or_eq_neg, h.symm, ne_neg_self, orientation, orientation_eq_or_eq_neg, resolve_left
-/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x != e.orientation ↔ x = -e.orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩

/--
theorem `orientation_comp_linearEquiv_eq_iff_det_pos` / 定理 `orientation_comp_linearEquiv_eq_iff_det_pos`

English:
theorem orientation_comp_linearEquiv_eq_iff_det_pos
  given: (e : Basis ι R M) (f : M ≃ₗ[R] M)
  proof: by
  rw [orientation_map]; rw [e.map_orientation_eq_det_inv_smul]; rw [units_inv_smul]; rw [units_smul_eq_self_iff]; rw [LinearEquiv.coe_det]

中文:
定理 orientation_comp_linearEquiv_eq_iff_det_pos
  条件: (e : Basis ι R M) (f : M ≃ₗ[R] M)
  证明: by
  rw [orientation_map]; rw [e.map_orientation_eq_det_inv_smul]; rw [units_inv_smul]; rw [units_smul_eq_self_iff]; rw [LinearEquiv.coe_det]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_det, coe_det, e.map_orientation_eq_det_inv_smul, map_orientation_eq_det_inv_smul, orientation_map, units_inv_smul, units_smul_eq_self_iff
-/
theorem orientation_comp_linearEquiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = e.orientation ↔ 0 < LinearMap.det (f : M ->ₗ[R] M) := by
  rw [orientation_map]; rw [e.map_orientation_eq_det_inv_smul]; rw [units_inv_smul]; rw [units_smul_eq_self_iff]; rw [LinearEquiv.coe_det]

/--
theorem `orientation_comp_linearEquiv_eq_neg_iff_det_neg` / 定理 `orientation_comp_linearEquiv_eq_neg_iff_det_neg`

English:
theorem orientation_comp_linearEquiv_eq_neg_iff_det_neg
  given: (e : Basis ι R M) (f : M ≃ₗ[R] M)
  proof: by
  rw [orientation_map]; rw [e.map_orientation_eq_det_inv_smul]; rw [units_inv_smul]; rw [units_smul_eq_neg_iff]; rw [LinearEquiv.coe_det]

中文:
定理 orientation_comp_linearEquiv_eq_neg_iff_det_neg
  条件: (e : Basis ι R M) (f : M ≃ₗ[R] M)
  证明: by
  rw [orientation_map]; rw [e.map_orientation_eq_det_inv_smul]; rw [units_inv_smul]; rw [units_smul_eq_neg_iff]; rw [LinearEquiv.coe_det]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_det, coe_det, e.map_orientation_eq_det_inv_smul, map_orientation_eq_det_inv_smul, orientation_map, units_inv_smul, units_smul_eq_neg_iff
-/
theorem orientation_comp_linearEquiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = -e.orientation ↔ LinearMap.det (f : M ->ₗ[R] M) < 0 := by
  rw [orientation_map]; rw [e.map_orientation_eq_det_inv_smul]; rw [units_inv_smul]; rw [units_smul_eq_neg_iff]; rw [LinearEquiv.coe_det]

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
/--
theorem `orientation_neg_single` / 定理 `orientation_neg_single`

English:
theorem orientation_neg_single
  given: (e : Basis ι R M) (i : ι)
  proof: by
  rw [orientation_unitsSMul]; rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

中文:
定理 orientation_neg_single
  条件: (e : Basis ι R M) (i : ι)
  证明: by
  rw [orientation_unitsSMul]; rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_update_of_mem, mem_univ, orientation_unitsSMul, prod_update_of_mem
-/
theorem orientation_neg_single (e : Basis ι R M) (i : ι) :
    (e.unitsSMul (Function.update 1 i (-1))).orientation = -e.orientation := by
  rw [orientation_unitsSMul]; rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

/--
Definition of `adjustToOrientation` / `adjustToOrientation` 的定义

English:
definition adjustToOrientation
  signature: [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι)
  body: haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))

中文:
定义 adjustToOrientation
  签名: [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι)
  定义体: haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))

Depends on / 依赖: Classical, Classical.arbitrary, Classical.decEq, Function, Function.update, Orientation, arbitrary, e.orientation, e.unitsSMul, orientation, unitsSMul, update
-/
def adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
/--
theorem `orientation_adjustToOrientation` / 定理 `orientation_adjustToOrientation`

English:
theorem orientation_adjustToOrientation
  statement: [Nonempty ι] (e : Basis ι R M)
  proof: by
  rw [adjustToOrientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h

中文:
定理 orientation_adjustToOrientation
  结论: [Nonempty ι] (e : Basis ι R M)
  证明: by
  rw [adjustToOrientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h

Depends on / 依赖: adjustToOrientation, eq_comm, ne_comm, orientation_ne_iff_eq_neg, orientation_neg_single, split_ifs
-/
theorem orientation_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) : (e.adjustToOrientation x).orientation = x := by
  rw [adjustToOrientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h

/--
theorem `adjustToOrientation_apply_eq_or_eq_neg` / 定理 `adjustToOrientation_apply_eq_or_eq_neg`

English:
theorem adjustToOrientation_apply_eq_or_eq_neg
  statement: [Nonempty ι] (e : Basis ι R M)
  proof: by
  rw [adjustToOrientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [unitsSMul_apply, hi]

中文:
定理 adjustToOrientation_apply_eq_or_eq_neg
  结论: [Nonempty ι] (e : Basis ι R M)
  证明: by
  rw [adjustToOrientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [unitsSMul_apply, hi]

Depends on / 依赖: Classical, Classical.arbitrary, adjustToOrientation, arbitrary, split_ifs, unitsSMul_apply
-/
theorem adjustToOrientation_apply_eq_or_eq_neg [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  rw [adjustToOrientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [unitsSMul_apply, hi]

/--
theorem `det_adjustToOrientation` / 定理 `det_adjustToOrientation`

English:
theorem det_adjustToOrientation
  statement: [Nonempty ι] (e : Basis ι R M)
  proof: by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp only [e.det_unitsSMul, Finset.mem_univ, Finset.prod_update_of_mem,
      Pi.one_apply, Finset.prod_const_one, mul_one, inv_neg, inv_one, Units.val_neg, Units.val_one]
    ext
    simp

@[simp]

中文:
定理 det_adjustToOrientation
  结论: [Nonempty ι] (e : Basis ι R M)
  证明: by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp only [e.det_unitsSMul, Finset.mem_univ, Finset.prod_update_of_mem,
      Pi.one_apply, Finset.prod_const_one, mul_one, inv_neg, inv_one, Units.val_neg, Units.val_one]
    ext
    simp

@[simp]

Depends on / 依赖: Basis.adjustToOrientation, Finset, Finset.mem_univ, Finset.prod_const_one, Finset.prod_update_of_mem, Pi.one_apply, Units.val_neg, Units.val_one, adjustToOrientation, det_unitsSMul, e.det_unitsSMul, inv_neg, inv_one, mem_univ, mul_one, one_apply, prod_const_one, prod_update_of_mem, split_ifs, val_neg
-/
theorem det_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) :
    (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -e.det := by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp only [e.det_unitsSMul, Finset.mem_univ, Finset.prod_update_of_mem,
      Pi.one_apply, Finset.prod_const_one, mul_one, inv_neg, inv_one, Units.val_neg, Units.val_one]
    ext
    simp

@[simp]
/--
theorem `abs_det_adjustToOrientation` / 定理 `abs_det_adjustToOrientation`

English:
theorem abs_det_adjustToOrientation
  statement: [Nonempty ι] (e : Basis ι R M)
  proof: by
  rcases e.det_adjustToOrientation x with h | h <;> simp [h]

中文:
定理 abs_det_adjustToOrientation
  结论: [Nonempty ι] (e : Basis ι R M)
  证明: by
  rcases e.det_adjustToOrientation x with h | h <;> simp [h]

Depends on / 依赖: det_adjustToOrientation, e.det_adjustToOrientation
-/
theorem abs_det_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (v : ι -> M) : |(e.adjustToOrientation x).det v| = |e.det v| := by
  rcases e.det_adjustToOrientation x with h | h <;> simp [h]

end Module.Basis

end LinearOrderedCommRing

section LinearOrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*}

namespace Orientation

variable [Fintype ι]

open FiniteDimensional Module

/--
theorem `eq_or_eq_neg` / 定理 `eq_or_eq_neg`

English:
theorem eq_or_eq_neg
  statement: [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
  proof: by
  have e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  let := Classical.decEq ι
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂]

中文:
定理 eq_or_eq_neg
  结论: [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
  证明: by
  have e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  let := Classical.decEq ι
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂]

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.equivFinOfCardEq, e.orientation_eq_or_eq_neg, equivFinOfCardEq, finBasis, orientation_eq_or_eq_neg, reindex
-/
theorem eq_or_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂ := by
  have e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  let := Classical.decEq ι
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂]

/--
theorem `ne_iff_eq_neg` / 定理 `ne_iff_eq_neg`

English:
theorem ne_iff_eq_neg
  statement: [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
  proof: ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩

中文:
定理 ne_iff_eq_neg
  结论: [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
  证明: ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩

Depends on / 依赖: Module, Module.Ray.ne_neg_self, eq_or_eq_neg, he.symm, ne_neg_self, resolve_left
-/
theorem ne_iff_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ != x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩

/--
theorem `map_eq_det_inv_smul` / 定理 `map_eq_det_inv_smul`

English:
theorem map_eq_det_inv_smul
  statement: [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  proof: haveI e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f

中文:
定理 map_eq_det_inv_smul
  结论: [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  证明: haveI e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f

Depends on / 依赖: Fintype, Fintype.equivFinOfCardEq, e.map_orientation_eq_det_inv_smul, equivFinOfCardEq, finBasis, map_orientation_eq_det_inv_smul, reindex
-/
theorem map_eq_det_inv_smul [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x :=
  haveI e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f

/--
theorem `map_eq_iff_det_pos` / 定理 `map_eq_iff_det_pos`

English:
theorem map_eq_iff_det_pos
  statement: [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  proof: by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  rw [map_eq_det_inv_smul _ _ h]; rw [units_inv_smul]; rw [units_smul_eq_self_iff]; rw [LinearEquiv.coe_det]

中文:
定理 map_eq_iff_det_pos
  结论: [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  证明: by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  rw [map_eq_det_inv_smul _ _ h]; rw [units_inv_smul]; rw [units_smul_eq_self_iff]; rw [LinearEquiv.coe_det]

Depends on / 依赖: Fintype, Fintype.card_eq_zero, LinearEquiv, LinearEquiv.coe_det, LinearMap, LinearMap.det_eq_one_of_finrank_eq_zero, card_eq_zero, coe_det, det_eq_one_of_finrank_eq_zero, finrank, h.symm.trans, isEmpty_or_nonempty, map_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff
-/
theorem map_eq_iff_det_pos [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < LinearMap.det (f : M ->ₗ[R] M) := by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  rw [map_eq_det_inv_smul _ _ h]; rw [units_inv_smul]; rw [units_smul_eq_self_iff]; rw [LinearEquiv.coe_det]

/--
theorem `map_eq_neg_iff_det_neg` / 定理 `map_eq_neg_iff_det_neg`

English:
theorem map_eq_neg_iff_det_neg
  statement: (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  proof: by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  have : FiniteDimensional R M := of_finrank_pos 

中文:
定理 map_eq_neg_iff_det_neg
  结论: (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  证明: by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  have : FiniteDimensional R M := of_finrank_pos 

Depends on / 依赖: FiniteDimensional, Fintype, Fintype.card_eq_zero, Fintype.card_pos, LinearEquiv, LinearEquiv.coe_det, LinearMap, LinearMap.det_eq_one_of_finrank_eq_zero, Module, Module.Ray.ne_neg_self, card_eq_zero, card_pos, coe_det, det_eq_one_of_finrank_eq_zero, finrank, h.symm.trans, isEmpty_or_nonempty, map_eq_det_inv_smul, ne_neg_self, of_finrank_pos
-/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = -x ↔ LinearMap.det (f : M ->ₗ[R] M) < 0 := by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  have : FiniteDimensional R M := of_finrank_pos H
  rw [map_eq_det_inv_smul _ _ h]; rw [units_inv_smul]; rw [units_smul_eq_neg_iff]; rw [LinearEquiv.coe_det]

/--
Definition of `someBasis` / `someBasis` 的定义

English:
definition someBasis
  signature: [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M] (x : Orientation R M ι)
  body: ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x

中文:
定义 someBasis
  签名: [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M] (x : Orientation R M ι)
  定义体: ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x

Depends on / 依赖: Fintype, Fintype.equivFinOfCardEq, adjustToOrientation, equivFinOfCardEq, finBasis, reindex
-/
def someBasis [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x

/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
/--
theorem `someBasis_orientation` / 定理 `someBasis_orientation`

English:
theorem someBasis_orientation
  statement: [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M]
  proof: Basis.orientation_adjustToOrientation _ _

中文:
定理 someBasis_orientation
  结论: [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M]
  证明: Basis.orientation_adjustToOrientation _ _

Depends on / 依赖: Basis.orientation_adjustToOrientation, orientation_adjustToOrientation
-/
theorem someBasis_orientation [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M]
    (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) : (x.someBasis h).orientation = x :=
  Basis.orientation_adjustToOrientation _ _

end Orientation

end LinearOrderedField
