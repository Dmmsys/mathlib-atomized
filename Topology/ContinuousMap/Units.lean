/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Units of continuous functions

This file concerns itself with `C(X, M)ˣ` and `C(X, Mˣ)` when `X` is a topological space
and `M` has some monoid structure compatible with its topology.
-/

@[expose] public section


variable {X M R 𝕜 : Type*} [TopologicalSpace X]

namespace ContinuousMap

section Monoid

variable [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
-- `simps` generates some lemmas here with LHS not in simp normal form,
-- so we write them out manually below.
@[to_additive (attr := simps apply_val_apply symm_apply_apply_val)
/-- Equivalence between continuous maps into the additive units of an additive monoid with
continuous addition and the additive units of the additive monoid of continuous maps. -/]
/--
Definition of `unitsLift` / `unitsLift` 的定义

English:
definition unitsLift
  signature: : C(X, Mˣ) ≃ C(X, M)ˣ where
  body: { val := ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_val.comp (continuous_inv.comp f.continuous)⟩
      val_inv := ext fun _ => Units.mul_inv _
      inv_val := ext fun _ => Units.inv_mul _ }
  invFun f :=
    { toFun := fun x =>
        ⟨

中文:
定义 unitsLift
  签名: : C(X, Mˣ) ≃ C(X, M)ˣ where
  定义体: { val := ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_val.comp (continuous_inv.comp f.continuous)⟩
      val_inv := ext fun _ => Units.mul_inv _
      inv_val := ext fun _ => Units.inv_mul _ }
  invFun f :=
    { toFun := fun x =>
        ⟨

Depends on / 依赖: ContinuousMap, ContinuousMap.congr_fun, MulOpposite, MulOpposite.continuous_op.comp, Units.continuous_val.comp, Units.inv_mul, Units.mul_inv, congr_fun, continuous, continuous.prodMk, continuous_induced_rng, continuous_inv, continuous_inv.comp, continuous_op, continuous_toFun, continuous_val, f.continuous, f.inv_mul, f.mul_inv, invFun
-/
def unitsLift : C(X, Mˣ) ≃ C(X, M)ˣ where
  toFun f :=
    { val := ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_val.comp (continuous_inv.comp f.continuous)⟩
      val_inv := ext fun _ => Units.mul_inv _
      inv_val := ext fun _ => Units.inv_mul _ }
  invFun f :=
    { toFun := fun x =>
        ⟨(f : C(X, M)) x, (↑f⁻¹ : C(X, M)) x,
          ContinuousMap.congr_fun f.mul_inv x, ContinuousMap.congr_fun f.inv_mul x⟩
continuous_toFun := continuous_induced_rng.2
(f : C(X, M)).continuous.prodMk
        MulOpposite.continuous_op.comp (↑f⁻¹ : C(X, M)).continuous }

@[to_additive (attr := simp)]
/--
lemma `unitsLift_apply_inv_apply` / 引理 `unitsLift_apply_inv_apply`

English:
lemma unitsLift_apply_inv_apply
  given: (f : C(X, Mˣ)) (x : X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 unitsLift_apply_inv_apply
  条件: (f : C(X, Mˣ)) (x : X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma unitsLift_apply_inv_apply (f : C(X, Mˣ)) (x : X) :
    (↑(ContinuousMap.unitsLift f)⁻¹ : C(X, M)) x = (f x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `unitsLift_symm_apply_apply_inv'` / 引理 `unitsLift_symm_apply_apply_inv'`

English:
lemma unitsLift_symm_apply_apply_inv'
  given: (f : C(X, M)ˣ) (x : X)
  proof: by
  rfl

中文:
引理 unitsLift_symm_apply_apply_inv'
  条件: (f : C(X, M)ˣ) (x : X)
  证明: by
  rfl
-/
lemma unitsLift_symm_apply_apply_inv' (f : C(X, M)ˣ) (x : X) :
    (ContinuousMap.unitsLift.symm f x)⁻¹ = (↑f⁻¹ : C(X, M)) x := by
  rfl

end Monoid

section NormedRing

variable [NormedRing R] [CompleteSpace R]

/--
theorem `continuous_isUnit_unit` / 定理 `continuous_isUnit_unit`

English:
theorem continuous_isUnit_unit
  given: {f : C(X, R)} (h : forall x, IsUnit (f x))
  proof: by
  refine
    continuous_induced_rng.2
      (Continuous.prodMk f.continuous
        (MulOpposite.continuous_op.comp (continuous_iff_continuousAt.mpr fun x => ?_)))
  have := NormedRing.inverse_continuousAt (h x).unit
  simp only
  simp only [← Ring.inverse_unit, IsUnit.unit_spec] at this ⊢
  exac

中文:
定理 continuous_isUnit_unit
  条件: {f : C(X, R)} (h : 对任意 x, IsUnit (f x))
  证明: by
  refine
    continuous_induced_rng.2
      (Continuous.prodMk f.continuous
        (MulOpposite.continuous_op.comp (continuous_iff_continuousAt.mpr fun x => ?_)))
  have := NormedRing.inverse_continuousAt (h x).unit
  simp only
  simp only [← Ring.inverse_unit, IsUnit.unit_spec] at this ⊢
  exac

Depends on / 依赖: Continuous, Continuous.prodMk, IsUnit, IsUnit.unit_spec, MulOpposite, MulOpposite.continuous_op.comp, NormedRing, NormedRing.inverse_continuousAt, Ring.inverse_unit, continuous, continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, continuous_induced_rng, continuous_op, f.continuous, f.continuousAt, inverse_continuousAt, inverse_unit, prodMk
-/
theorem continuous_isUnit_unit {f : C(X, R)} (h : forall x, IsUnit (f x)) :
    Continuous fun x => (h x).unit := by
  refine
    continuous_induced_rng.2
      (Continuous.prodMk f.continuous
        (MulOpposite.continuous_op.comp (continuous_iff_continuousAt.mpr fun x => ?_)))
  have := NormedRing.inverse_continuousAt (h x).unit
  simp only
  simp only [← Ring.inverse_unit, IsUnit.unit_spec] at this ⊢
  exact this.comp (f.continuousAt x)

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
/--
Definition of `unitsOfForallIsUnit` / `unitsOfForallIsUnit` 的定义

English:
definition unitsOfForallIsUnit
  signature: {f : C(X, R)} (h : forall x, IsUnit (f x))
  body: (h x).unit
  continuous_toFun := continuous_isUnit_unit h

中文:
定义 unitsOfForallIsUnit
  签名: {f : C(X, R)} (h : 对任意 x, IsUnit (f x))
  定义体: (h x).unit
  continuous_toFun := continuous_isUnit_unit h
-/
noncomputable def unitsOfForallIsUnit {f : C(X, R)} (h : forall x, IsUnit (f x)) : C(X, Rˣ) where
  toFun x := (h x).unit
  continuous_toFun := continuous_isUnit_unit h

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: :
  body: ⟨unitsOfForallIsUnit h, by ext; rfl⟩

中文:
实例 canLift
  签名: :
  定义体: ⟨unitsOfForallIsUnit h, by ext; rfl⟩

Depends on / 依赖: unitsOfForallIsUnit
-/
instance canLift :
    CanLift C(X, R) C(X, Rˣ) (fun f => ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩)
      fun f => forall x, IsUnit (f x) where
  prf f h := ⟨unitsOfForallIsUnit h, by ext; rfl⟩

/--
theorem `isUnit_iff_forall_isUnit` / 定理 `isUnit_iff_forall_isUnit`

English:
theorem isUnit_iff_forall_isUnit
  given: (f : C(X, R))
  statement: IsUnit f ↔ forall x, IsUnit (f x)
  proof: Iff.intro (fun h x => ⟨unitsLift.symm h.unit x, rfl⟩) fun h =>
    ⟨ContinuousMap.unitsLift (unitsOfForallIsUnit h), by ext; rfl⟩

中文:
定理 isUnit_iff_forall_isUnit
  条件: (f : C(X, R))
  结论: IsUnit f ↔ 对任意 x, IsUnit (f x)
  证明: Iff.intro (fun h x => ⟨unitsLift.symm h.unit x, rfl⟩) fun h =>
    ⟨ContinuousMap.unitsLift (unitsOfForallIsUnit h), by ext; rfl⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.unitsLift, Iff.intro, h.unit, unitsLift, unitsLift.symm, unitsOfForallIsUnit
-/
theorem isUnit_iff_forall_isUnit (f : C(X, R)) : IsUnit f ↔ forall x, IsUnit (f x) :=
  Iff.intro (fun h x => ⟨unitsLift.symm h.unit x, rfl⟩) fun h =>
    ⟨ContinuousMap.unitsLift (unitsOfForallIsUnit h), by ext; rfl⟩

end NormedRing

section NormedField

variable [NormedField 𝕜] [NormedDivisionRing R] [Algebra 𝕜 R] [CompleteSpace R]

/--
theorem `isUnit_iff_forall_ne_zero` / 定理 `isUnit_iff_forall_ne_zero`

English:
theorem isUnit_iff_forall_ne_zero
  given: (f : C(X, R))
  statement: IsUnit f ↔ forall x, f x != 0
  proof: by
  simp_rw [f.isUnit_iff_forall_isUnit, isUnit_iff_ne_zero]

中文:
定理 isUnit_iff_forall_ne_zero
  条件: (f : C(X, R))
  结论: IsUnit f ↔ 对任意 x, f x != 0
  证明: by
  simp_rw [f.isUnit_iff_forall_isUnit, isUnit_iff_ne_zero]

Depends on / 依赖: f.isUnit_iff_forall_isUnit, isUnit_iff_forall_isUnit, isUnit_iff_ne_zero, simp_rw
-/
theorem isUnit_iff_forall_ne_zero (f : C(X, R)) : IsUnit f ↔ forall x, f x != 0 := by
  simp_rw [f.isUnit_iff_forall_isUnit, isUnit_iff_ne_zero]

/--
theorem `spectrum_eq_preimage_range` / 定理 `spectrum_eq_preimage_range`

English:
theorem spectrum_eq_preimage_range
  given: (f : C(X, R))
  proof: by
  ext x
  simp only [spectrum.mem_iff, isUnit_iff_forall_ne_zero, not_forall, sub_apply,
    Classical.not_not, Set.mem_range,
    sub_eq_zero, @eq_comm _ (x • 1 : R) _, Set.mem_preimage, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply]

中文:
定理 spectrum_eq_preimage_range
  条件: (f : C(X, R))
  证明: by
  ext x
  simp only [spectrum.mem_iff, isUnit_iff_forall_ne_zero, not_forall, sub_apply,
    Classical.not_not, Set.mem_range,
    sub_eq_zero, @eq_comm _ (x • 1 : R) _, Set.mem_preimage, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Classical, Classical.not_not, Set.mem_preimage, Set.mem_range, algebraMap_eq_smul_one, eq_comm, isUnit_iff_forall_ne_zero, mem_iff, mem_preimage, mem_range, not_forall, not_not, one_apply, smul_apply, spectrum, spectrum.mem_iff, sub_apply, sub_eq_zero
-/
theorem spectrum_eq_preimage_range (f : C(X, R)) :
    spectrum 𝕜 f = algebraMap _ _ ⁻¹' Set.range f := by
  ext x
  simp only [spectrum.mem_iff, isUnit_iff_forall_ne_zero, not_forall, sub_apply,
    Classical.not_not, Set.mem_range,
    sub_eq_zero, @eq_comm _ (x • 1 : R) _, Set.mem_preimage, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply]

/--
theorem `spectrum_eq_range` / 定理 `spectrum_eq_range`

English:
theorem spectrum_eq_range
  given: [CompleteSpace 𝕜] (f : C(X, 𝕜))
  statement: spectrum 𝕜 f = Set.range f
  proof: by
  rw [spectrum_eq_preimage_range]; rw [Algebra.algebraMap_self]
  exact Set.preimage_id

中文:
定理 spectrum_eq_range
  条件: [CompleteSpace 𝕜] (f : C(X, 𝕜))
  结论: spectrum 𝕜 f = Set.range f
  证明: by
  rw [spectrum_eq_preimage_range]; rw [Algebra.algebraMap_self]
  exact Set.preimage_id

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Set.preimage_id, algebraMap_self, preimage_id, spectrum_eq_preimage_range
-/
theorem spectrum_eq_range [CompleteSpace 𝕜] (f : C(X, 𝕜)) : spectrum 𝕜 f = Set.range f := by
  rw [spectrum_eq_preimage_range]; rw [Algebra.algebraMap_self]
  exact Set.preimage_id

end NormedField

end ContinuousMap
