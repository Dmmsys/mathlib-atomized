/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary

/-!
# The ⋆-algebra automorphism given by a unitary element

This file defines the ⋆-algebra automorphism on `R` given by a unitary `u`,
which is `Unitary.conjStarAlgAut S R u`, defined to be `x ↦ u * x * star u`.
-/

@[expose] public section

namespace Unitary
variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (S R) in
/--
Definition of `conjStarAlgAut` / `conjStarAlgAut` 的定义

English:
definition conjStarAlgAut
  signature: : unitary R ->* (R ≃⋆ₐ[S] R) where
  body: { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
.symm map_smul' _ _ := smul_comm _ _ _
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

中文:
定义 conjStarAlgAut
  签名: : unitary R ->* (R ≃⋆ₐ[S] R) where
  定义体: { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
.symm map_smul' _ _ := smul_comm _ _ _
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

Depends on / 依赖: ConjAct, ConjAct.toConjAct, ConjAct.units_smul_def, MulSemiringAction, MulSemiringAction.toRingEquiv, Unitary, Unitary.star_eq_inv, map_mul, map_one, map_smul, map_star, mul_assoc, smul_comm, star_eq_inv, toConjAct, toRingEquiv, toUnits, units_smul_def
-/
def conjStarAlgAut : unitary R ->* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
.symm map_smul' _ _ := smul_comm _ _ _
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/--
theorem `conjStarAlgAut_apply` / 定理 `conjStarAlgAut_apply`

English:
theorem conjStarAlgAut_apply
  given: (u : unitary R) (x : R)
  proof: rfl

中文:
定理 conjStarAlgAut_apply
  条件: (u : unitary R) (x : R)
  证明: rfl
-/
@[simp] theorem conjStarAlgAut_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R u x = u * x * (star u : R) := rfl

/--
theorem `conjStarAlgAut_symm_apply` / 定理 `conjStarAlgAut_symm_apply`

English:
theorem conjStarAlgAut_symm_apply
  given: (u : unitary R) (x : R)
  proof: rfl

中文:
定理 conjStarAlgAut_symm_apply
  条件: (u : unitary R) (x : R)
  证明: rfl
-/
theorem conjStarAlgAut_symm_apply (u : unitary R) (x : R) :
    (conjStarAlgAut S R u).symm x = (star u : R) * x * u := rfl

/--
theorem `conjStarAlgAut_star_apply` / 定理 `conjStarAlgAut_star_apply`

English:
theorem conjStarAlgAut_star_apply
  given: (u : unitary R) (x : R)
  proof: by simp

中文:
定理 conjStarAlgAut_star_apply
  条件: (u : unitary R) (x : R)
  证明: by simp
-/
theorem conjStarAlgAut_star_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R (star u) x = (star u : R) * x * u := by simp

/--
theorem `conjStarAlgAut_symm` / 定理 `conjStarAlgAut_symm`

English:
theorem conjStarAlgAut_symm
  given: (u : unitary R)
  proof: by
  ext; simp [conjStarAlgAut_symm_apply]

中文:
定理 conjStarAlgAut_symm
  条件: (u : unitary R)
  证明: by
  ext; simp [conjStarAlgAut_symm_apply]
-/
@[simp] theorem conjStarAlgAut_symm (u : unitary R) :
    (conjStarAlgAut S R u).symm = conjStarAlgAut S R (star u) := by
  ext; simp [conjStarAlgAut_symm_apply]

/--
theorem `conjStarAlgAut_trans_conjStarAlgAut` / 定理 `conjStarAlgAut_trans_conjStarAlgAut`

English:
theorem conjStarAlgAut_trans_conjStarAlgAut
  given: (u₁ u₂ : unitary R)
  proof: .symm map_mul _ _ _

中文:
定理 conjStarAlgAut_trans_conjStarAlgAut
  条件: (u₁ u₂ : unitary R)
  证明: .symm map_mul _ _ _

Depends on / 依赖: map_mul
-/
theorem conjStarAlgAut_trans_conjStarAlgAut (u₁ u₂ : unitary R) :
    (conjStarAlgAut S R u₁).trans (conjStarAlgAut S R u₂) = conjStarAlgAut S R (u₂ * u₁) :=
.symm map_mul _ _ _

/--
theorem `conjStarAlgAut_mul_apply` / 定理 `conjStarAlgAut_mul_apply`

English:
theorem conjStarAlgAut_mul_apply
  given: (u₁ u₂ : unitary R) (x : R)
  proof: by simp

中文:
定理 conjStarAlgAut_mul_apply
  条件: (u₁ u₂ : unitary R) (x : R)
  证明: by simp
-/
theorem conjStarAlgAut_mul_apply (u₁ u₂ : unitary R) (x : R) :
    conjStarAlgAut S R (u₁ * u₂) x = conjStarAlgAut S R u₁ (conjStarAlgAut S R u₂ x) := by simp

/--
theorem `toRingEquiv_conjStarAlgAut` / 定理 `toRingEquiv_conjStarAlgAut`

English:
theorem toRingEquiv_conjStarAlgAut
  given: (u : unitary R)
  proof: rfl

中文:
定理 toRingEquiv_conjStarAlgAut
  条件: (u : unitary R)
  证明: rfl
-/
theorem toRingEquiv_conjStarAlgAut (u : unitary R) :
    (conjStarAlgAut S R u).toRingEquiv =
      MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

/--
theorem `toAlgEquiv_conjStarAlgAut` / 定理 `toAlgEquiv_conjStarAlgAut`

English:
theorem toAlgEquiv_conjStarAlgAut
  given: {S : Type*} [CommSemiring S] [Algebra S R] (u : unitary R)
  proof: rfl

中文:
定理 toAlgEquiv_conjStarAlgAut
  条件: {S : 类型} [交换半环 S] [代数 S R] (u : unitary R)
  证明: rfl

Depends on / 依赖: IsAffineHom
-/
theorem toAlgEquiv_conjStarAlgAut {S : Type*} [CommSemiring S] [Algebra S R] (u : unitary R) :
    (conjStarAlgAut S R u).toAlgEquiv =
      MulSemiringAction.toAlgEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

/--
theorem `conjStarAlgAut_ext_iff` / 定理 `conjStarAlgAut_ext_iff`

English:
theorem conjStarAlgAut_ext_iff
  statement: {S : Type*} [CommSemiring S] [Algebra S R] [Algebra.IsCentral S R]
  proof: by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm,
    mul_one, eq_comm]

中文:
定理 conjStarAlgAut_ext_iff
  结论: {S : 类型} [交换半环 S] [代数 S R] [代数.是中心 S R]
  证明: by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm,
    mul_one, eq_comm]

Depends on / 依赖: Algebra, Algebra.IsCentral.center_eq_bot, Algebra.algebraMap_eq_smul_one, Algebra.mem_bot, IsAffineHom, IsCentral, QuasiCompact, Set.mem_range, StarAlgEquiv, StarAlgEquiv.ext_iff, Subalgebra, Subalgebra.mem_center_iff, Units.eq_inv_mul_iff_mul_eq, Units.eq_mul_inv_iff_mul_eq, algebraMap_eq_smul_one, center_eq_bot, coe_star, conjStarAlgAut_apply, conv_lhs, eq_comm
-/
theorem conjStarAlgAut_ext_iff {S : Type*} [CommSemiring S] [Algebra S R] [Algebra.IsCentral S R]
    (u v : unitary R) : conjStarAlgAut S R u = conjStarAlgAut S R v ↔ exists α : S, (u : R) = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm,
    mul_one, eq_comm]

/--
theorem `conjStarAlgAut_ext_iff'` / 定理 `conjStarAlgAut_ext_iff'`

English:
theorem conjStarAlgAut_ext_iff'
  statement: {R S : Type*} [Ring R] [StarMul R] [CommRing S] [StarMul S]
  proof: by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, val_inv_toUnits_apply, val_toUnits_apply,
    ← star_eq_inv, coe_star]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : S), by
    simp only [h, coe_smul, mul_smul_comm, SetLike.coe_mem, star_mul_self_of_mem]; rfl⟩⟩
  have huv : (u : R) = y • (v : R) := by simpa [← mul_assoc] using congr(v * $h).symm
  have hvu : (v : R) = star y • (u : R) := by simpa [← mul_assoc] using congr(u * (star $h)).symm
  have hvy : (v : R) = (star y * y) • (v : R) := by simp [← smul_smul, ← huv, ← hvu]
  nth_rw 1 [← one_smul S (v : R)] at hvy
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [eq_comm] at hvy
  obtain (this | this) := hvy
  · exact ⟨⟨y, by simp [mem_iff, this, mul_comm y]⟩, by ext; exact huv⟩
  · exact ⟨1, by ext; simp [this, huv] at huv ⊢⟩

中文:
定理 conjStarAlgAut_ext_iff'
  结论: {R S : 类型} [环 R] [StarMul R] [交换环 S] [StarMul S]
  证明: by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, val_inv_toUnits_apply, val_toUnits_apply,
    ← star_eq_inv, coe_star]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : S), by
    simp only [h, coe_smul, mul_smul_comm, SetLike.coe_mem, star_mul_self_of_mem]; rfl⟩⟩
  have huv : (u : R) = y • (v : R) := by simpa [← mul_assoc] using congr(v * $h).symm
  have hvu : (v : R) = star y • (u : R) := by simpa [← mul_assoc] using congr(u * (star $h)).symm
  have hvy : (v : R) = (star y * y) • (v : R) := by simp [← smul_smul, ← huv, ← hvu]
  nth_rw 1 [← one_smul S (v : R)] at hvy
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [eq_comm] at hvy
  obtain (this | this) := hvy
  · exact ⟨⟨y, by simp [mem_iff, this, mul_comm y]⟩, by ext; exact huv⟩
  · exact ⟨1, by ext; simp [this, huv] at huv ⊢⟩

Depends on / 依赖: Algebra, Algebra.IsCentral.center_eq_bot, Algebra.algebraMap_eq_smul_one, Algebra.mem_bot, IsCentral, Set.mem_range, StarAlgEquiv, StarAlgEquiv.ext_iff, Subalgebra, Subalgebra.mem_center_iff, Units.eq_inv_mul_iff_mul_eq, Units.eq_mul_inv_iff_mul_eq, algebraMap_eq_smul_one, center_eq_bot, coe_star, conjStarAlgAut_apply, conv_lhs, eq_comm, eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq
-/
theorem conjStarAlgAut_ext_iff' {R S : Type*} [Ring R] [StarMul R] [CommRing S] [StarMul S]
    [Algebra S R] [StarModule S R] [Algebra.IsCentral S R] [IsCancelMulZero S]
    [Module.IsTorsionFree S R] (u v : unitary R) :
    conjStarAlgAut S R u = conjStarAlgAut S R v ↔ exists α : unitary S, u = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, val_inv_toUnits_apply, val_toUnits_apply,
    ← star_eq_inv, coe_star]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : S), by
    simp only [h, coe_smul, mul_smul_comm, SetLike.coe_mem, star_mul_self_of_mem]; rfl⟩⟩
  have huv : (u : R) = y • (v : R) := by simpa [← mul_assoc] using congr(v * $h).symm
  have hvu : (v : R) = star y • (u : R) := by simpa [← mul_assoc] using congr(u * (star $h)).symm
  have hvy : (v : R) = (star y * y) • (v : R) := by simp [← smul_smul, ← huv, ← hvu]
  nth_rw 1 [← one_smul S (v : R)] at hvy
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [eq_comm] at hvy
  obtain (this | this) := hvy
  · exact ⟨⟨y, by simp [mem_iff, this, mul_comm y]⟩, by ext; exact huv⟩
  · exact ⟨1, by ext; simp [this, huv] at huv ⊢⟩

end Unitary
