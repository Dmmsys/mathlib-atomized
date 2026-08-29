/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# Gauss sums for Dirichlet characters
-/

public section
variable {N : Nat} [NeZero N] {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

open AddChar DirichletCharacter

/--
lemma `gaussSum_aux_of_mulShift` / 引理 `gaussSum_aux_of_mulShift`

English:
lemma gaussSum_aux_of_mulShift
  statement: (χ : DirichletCharacter R N) {d : Nat}
  proof: by
  suffices e.mulShift u = e by conv_lhs => rw [← this, gaussSum_mulShift]
  rw [(by ring : u.val = (u - 1) + 1)]; rw [← mulShift_mul]; rw [mulShift_one]; rw [mul_eq_right]
  rsuffices ⟨a, ha⟩ : (d : Int) ∣ (u.val.val - 1 : Int)
  · have : u.val - 1 = ↑(u.val.val - 1 : Int) := by simp only [ZMod.natCast_val, Int.cast_sub,
      ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_one]
    rw [this]; rw [ha]
    ext1 y
    simpa only [Int.cast_mul, Int.cast_natCast, mulShift_apply, mul_assoc, one_apply]
      using DFunLike.ext_iff.mp he (a * y)
  rw [← Units.val_inj]; rw [Units.val_one]; rw [ZMod.unitsMap_def]; rw [Units.coe_map] at hu
  have : ZMod.castHom hd (ZMod d) u.val = ((u.val.val : Int) : ZMod d) := by simp
  rwa [MonoidHom.coe_coe, this, ← Int.cast_one, eq_comm,
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hu

中文:
引理 gaussSum_aux_of_mulShift
  结论: (χ : DirichletCharacter R N) {d : 自然数}
  证明: by
  suffices e.mulShift u = e by conv_lhs => rw [← this, gaussSum_mulShift]
  rw [(by ring : u.val = (u - 1) + 1)]; rw [← mulShift_mul]; rw [mulShift_one]; rw [mul_eq_right]
  rsuffices ⟨a, ha⟩ : (d : Int) ∣ (u.val.val - 1 : Int)
  · have : u.val - 1 = ↑(u.val.val - 1 : Int) := by simp only [ZMod.natCast_val, Int.cast_sub,
      ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_one]
    rw [this]; rw [ha]
    ext1 y
    simpa only [Int.cast_mul, Int.cast_natCast, mulShift_apply, mul_assoc, one_apply]
      using DFunLike.ext_iff.mp he (a * y)
  rw [← Units.val_inj]; rw [Units.val_one]; rw [ZMod.unitsMap_def]; rw [Units.coe_map] at hu
  have : ZMod.castHom hd (ZMod d) u.val = ((u.val.val : Int) : ZMod d) := by simp
  rwa [MonoidHom.coe_coe, this, ← Int.cast_one, eq_comm,
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hu

Depends on / 依赖: DFunLike, DFunLike.ext_, Int.cast_mul, Int.cast_natCast, Int.cast_one, Int.cast_sub, ZMod.cast_id, ZMod.intCast_cast, ZMod.natCast_val, cast_id, cast_mul, cast_natCast, cast_one, cast_sub, conv_lhs, e.mulShift, ext_, gaussSum_mulShift, id_eq, intCast_cast
-/
lemma gaussSum_aux_of_mulShift (χ : DirichletCharacter R N) {d : Nat}
    (hd : d ∣ N) (he : e.mulShift d = 1) {u : (ZMod N)ˣ} (hu : ZMod.unitsMap hd u = 1) :
    χ u * gaussSum χ e = gaussSum χ e := by
  suffices e.mulShift u = e by conv_lhs => rw [← this, gaussSum_mulShift]
  rw [(by ring : u.val = (u - 1) + 1)]; rw [← mulShift_mul]; rw [mulShift_one]; rw [mul_eq_right]
  rsuffices ⟨a, ha⟩ : (d : Int) ∣ (u.val.val - 1 : Int)
  · have : u.val - 1 = ↑(u.val.val - 1 : Int) := by simp only [ZMod.natCast_val, Int.cast_sub,
      ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_one]
    rw [this]; rw [ha]
    ext1 y
    simpa only [Int.cast_mul, Int.cast_natCast, mulShift_apply, mul_assoc, one_apply]
      using DFunLike.ext_iff.mp he (a * y)
  rw [← Units.val_inj]; rw [Units.val_one]; rw [ZMod.unitsMap_def]; rw [Units.coe_map] at hu
  have : ZMod.castHom hd (ZMod d) u.val = ((u.val.val : Int) : ZMod d) := by simp
  rwa [MonoidHom.coe_coe, this, ← Int.cast_one, eq_comm,
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hu

/--
lemma `factorsThrough_of_gaussSum_ne_zero` / 引理 `factorsThrough_of_gaussSum_ne_zero`

English:
lemma factorsThrough_of_gaussSum_ne_zero
  statement: [IsDomain R] {χ : DirichletCharacter R N} {d : Nat}
  proof: by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro _ hu
  simpa [← Units.val_inj, h_ne] using gaussSum_aux_of_mulShift e χ hd he hu

中文:
引理 factorsThrough_of_gaussSum_ne_zero
  结论: [是整环 R] {χ : DirichletCharacter R N} {d : 自然数}
  证明: by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro _ hu
  simpa [← Units.val_inj, h_ne] using gaussSum_aux_of_mulShift e χ hd he hu

Depends on / 依赖: DirichletCharacter, DirichletCharacter.factorsThrough_iff_ker_unitsMap, Units.val_inj, factorsThrough_iff_ker_unitsMap, gaussSum_aux_of_mulShift, h_ne, val_inj
-/
lemma factorsThrough_of_gaussSum_ne_zero [IsDomain R] {χ : DirichletCharacter R N} {d : Nat}
    (hd : d ∣ N) (he : e.mulShift d = 1) (h_ne : gaussSum χ e != 0) :
    χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro _ hu
  simpa [← Units.val_inj, h_ne] using gaussSum_aux_of_mulShift e χ hd he hu

/--
lemma `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive` / 引理 `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive`

English:
lemma gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive
  statement: [IsDomain R]
  proof: by
  contrapose! hχ
  rcases e.exists_divisor_of_not_isPrimitive he with ⟨d, hd₁, hd₂, hed⟩
have : χ.conductor <= d := Nat.sInf_le factorsThrough_of_gaussSum_ne_zero e hd₁ hed hχ
  exact (this.trans_lt hd₂).ne

中文:
引理 gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive
  结论: [是整环 R]
  证明: by
  contrapose! hχ
  rcases e.exists_divisor_of_not_isPrimitive he with ⟨d, hd₁, hd₂, hed⟩
have : χ.conductor <= d := Nat.sInf_le factorsThrough_of_gaussSum_ne_zero e hd₁ hed hχ
  exact (this.trans_lt hd₂).ne

Depends on / 依赖: Nat.sInf_le, conductor, contrapose, e.exists_divisor_of_not_isPrimitive, exists_divisor_of_not_isPrimitive, factorsThrough_of_gaussSum_ne_zero, sInf_le, this.trans_lt, trans_lt
-/
lemma gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive [IsDomain R]
    {χ : DirichletCharacter R N} (hχ : IsPrimitive χ) (he : ¬IsPrimitive e) :
    gaussSum χ e = 0 := by
  contrapose! hχ
  rcases e.exists_divisor_of_not_isPrimitive he with ⟨d, hd₁, hd₂, hed⟩
have : χ.conductor <= d := Nat.sInf_le factorsThrough_of_gaussSum_ne_zero e hd₁ hed hχ
  exact (this.trans_lt hd₂).ne

/--
lemma `gaussSum_mulShift_of_isPrimitive` / 引理 `gaussSum_mulShift_of_isPrimitive`

English:
lemma gaussSum_mulShift_of_isPrimitive
  statement: [IsDomain R] {χ : DirichletCharacter R N}
  proof: by
  by_cases ha : IsUnit a
  · simpa [ha.unit_spec] using gaussSum_mulShift_eq χ e ha.unit
  · rw [MulChar.map_nonunit _ ha, zero_mul]
    exact gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive _ hχ (not_isPrimitive_mulShift e ha)

中文:
引理 gaussSum_mulShift_of_isPrimitive
  结论: [是整环 R] {χ : DirichletCharacter R N}
  证明: by
  by_cases ha : IsUnit a
  · simpa [ha.unit_spec] using gaussSum_mulShift_eq χ e ha.unit
  · rw [MulChar.map_nonunit _ ha, zero_mul]
    exact gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive _ hχ (not_isPrimitive_mulShift e ha)

Depends on / 依赖: IsUnit, MulChar, MulChar.map_nonunit, gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive, gaussSum_mulShift_eq, ha.unit, ha.unit_spec, map_nonunit, not_isPrimitive_mulShift, unit_spec, zero_mul
-/
lemma gaussSum_mulShift_of_isPrimitive [IsDomain R] {χ : DirichletCharacter R N}
    (hχ : IsPrimitive χ) (a : ZMod N) :
    gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSum χ e := by
  by_cases ha : IsUnit a
  · simpa [ha.unit_spec] using gaussSum_mulShift_eq χ e ha.unit
  · rw [MulChar.map_nonunit _ ha, zero_mul]
    exact gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive _ hχ (not_isPrimitive_mulShift e ha)
