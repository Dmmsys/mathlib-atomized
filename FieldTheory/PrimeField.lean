/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra

/-!
# Prime fields

A prime field is a field that does not contain any nontrivial subfield. Prime fields are `ℚ` in
characteristic `0` and `ZMod p` in characteristic `p` with `p` a prime number. Any field `K`
contains a unique prime field: it is the smallest field contained in `K`.

## Results

* The fields `ℚ` and `ZMod p` are prime fields. These are stated as the instances that says that
  the corresponding `Subfield` type is a `Subsingleton`.
* `Subfield.bot_eq_of_charZero` : the smallest subfield of a field of characteristic `0` is (the
  image of) `ℚ`.
* `Subfield.bot_eq_of_zMod_algebra`: the smallest subfield of a field of characteristic `p` is (the
  image of) `ZMod p`.

-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (Subfield Rat)
  body: subsingleton_of_top_le_bot fun x _ =>
  have h := Subsingleton.elim ((⊥ : Subfield Rat).subtype.comp (Rat.castHom _)) (.id _ : Rat ->+* Rat)
  (congr($h x) : _ = x) ▸ Subtype.prop _

中文:
实例 :
  签名: Subsingleton (Subfield Rat)
  定义体: subsingleton_of_top_le_bot fun x _ =>
  have h := Subsingleton.elim ((⊥ : Subfield Rat).subtype.comp (Rat.castHom _)) (.id _ : Rat ->+* Rat)
  (congr($h x) : _ = x) ▸ Subtype.prop _

Depends on / 依赖: subsingleton_of_top_le_bot
-/
instance : Subsingleton (Subfield Rat) := subsingleton_of_top_le_bot fun x _ =>
  have h := Subsingleton.elim ((⊥ : Subfield Rat).subtype.comp (Rat.castHom _)) (.id _ : Rat ->+* Rat)
  (congr($h x) : _ = x) ▸ Subtype.prop _

instance (p : Nat) [hp : Fact (Nat.Prime p)] : Subsingleton (Subfield (ZMod p)) :=
  subsingleton_of_top_le_bot fun x _ =>
    have h := Subsingleton.elim ((⊥ : Subfield (ZMod p)).subtype.comp
      (ZMod.castHom dvd_rfl _)) (.id _ : ZMod p ->+* ZMod p)
    (congr($h x) : _ = x) ▸ Subtype.prop _

/--
theorem `Subfield.bot_eq_of_charZero` / 定理 `Subfield.bot_eq_of_charZero`

English:
theorem Subfield.bot_eq_of_charZero
  given: {K : Type*} [Field K] [CharZero K]
  proof: by
  rw [eq_comm]; rw [eq_bot_iff]; rw [← Subfield.map_bot (algebraMap Rat K)]; rw [subsingleton_iff_bot_eq_top.mpr inferInstance]; rw [← RingHom.fieldRange_eq_map]

中文:
定理 Subfield.bot_eq_of_charZero
  条件: {K : 类型} [Field K] [CharZero K]
  证明: by
  rw [eq_comm]; rw [eq_bot_iff]; rw [← Subfield.map_bot (algebraMap Rat K)]; rw [subsingleton_iff_bot_eq_top.mpr inferInstance]; rw [← RingHom.fieldRange_eq_map]

Depends on / 依赖: RingHom, RingHom.fieldRange_eq_map, Subfield, Subfield.map_bot, algebraMap, eq_bot_iff, eq_comm, fieldRange_eq_map, map_bot, subsingleton_iff_bot_eq_top, subsingleton_iff_bot_eq_top.mpr
-/
theorem Subfield.bot_eq_of_charZero {K : Type*} [Field K] [CharZero K] :
    (⊥ : Subfield K) = (algebraMap Rat K).fieldRange := by
  rw [eq_comm]; rw [eq_bot_iff]; rw [← Subfield.map_bot (algebraMap Rat K)]; rw [subsingleton_iff_bot_eq_top.mpr inferInstance]; rw [← RingHom.fieldRange_eq_map]

/--
theorem `Subfield.bot_eq_of_zMod_algebra` / 定理 `Subfield.bot_eq_of_zMod_algebra`

English:
theorem Subfield.bot_eq_of_zMod_algebra
  statement: {K : Type*} (p : Nat) [hp : Fact (Nat.Prime p)]
  proof: by
  rw [eq_comm]; rw [eq_bot_iff]; rw [← Subfield.map_bot (algebraMap (ZMod p) K)]; rw [subsingleton_iff_bot_eq_top.mpr inferInstance]; rw [← RingHom.fieldRange_eq_map]

中文:
定理 Subfield.bot_eq_of_zMod_algebra
  结论: {K : 类型} (p : 自然数) [hp : Fact (自然数.Prime p)]
  证明: by
  rw [eq_comm]; rw [eq_bot_iff]; rw [← Subfield.map_bot (algebraMap (ZMod p) K)]; rw [subsingleton_iff_bot_eq_top.mpr inferInstance]; rw [← RingHom.fieldRange_eq_map]

Depends on / 依赖: RingHom, RingHom.fieldRange_eq_map, Subfield, Subfield.map_bot, algebraMap, eq_bot_iff, eq_comm, fieldRange_eq_map, map_bot, subsingleton_iff_bot_eq_top, subsingleton_iff_bot_eq_top.mpr
-/
theorem Subfield.bot_eq_of_zMod_algebra {K : Type*} (p : Nat) [hp : Fact (Nat.Prime p)]
    [Field K] [Algebra (ZMod p) K] :
    (⊥ : Subfield K) = (algebraMap (ZMod p) K).fieldRange := by
  rw [eq_comm]; rw [eq_bot_iff]; rw [← Subfield.map_bot (algebraMap (ZMod p) K)]; rw [subsingleton_iff_bot_eq_top.mpr inferInstance]; rw [← RingHom.fieldRange_eq_map]
