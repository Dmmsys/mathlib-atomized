/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent elements in quotient rings
-/

public section

/--
theorem `Ideal.isRadical_iff_quotient_reduced` / 定理 `Ideal.isRadical_iff_quotient_reduced`

English:
theorem Ideal.isRadical_iff_quotient_reduced
  given: {R : Type*} [CommRing R] (I : Ideal R)
  proof: by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_isRadical_iff_reduced_of_surjective Quotient.mk_surjective

中文:
定理 理想.isRadical_iff_quotient_reduced
  条件: {R : 类型} [交换环 R] (I : 理想 R)
  证明: by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_isRadical_iff_reduced_of_surjective Quotient.mk_surjective

Depends on / 依赖: Ideal.mk_ker, Quotient, Quotient.mk_surjective, RingHom, RingHom.ker_isRadical_iff_reduced_of_surjective, conv_lhs, ker_isRadical_iff_reduced_of_surjective, mk_ker, mk_surjective
-/
theorem Ideal.isRadical_iff_quotient_reduced {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsRadical ↔ IsReduced (R ⧸ I) := by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_isRadical_iff_reduced_of_surjective Quotient.mk_surjective

variable {S : Type*} [CommRing S] (I : Ideal S)

/--
theorem `Ideal.IsNilpotent.induction_on` / 定理 `Ideal.IsNilpotent.induction_on`

English:
theorem Ideal.IsNilpotent.induction_on
  statement: (hI : IsNilpotent I)
  proof: by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  induction n using Nat.strong_induction_on generalizing S with | _ n H
  by_cases hI' : I = ⊥
  · subst hI'
    apply h₁
    rw [← Ideal.zero_eq_bot]; rw [zero_pow two_ne_zero]
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    have := subsingl

中文:
定理 理想.是幂零.induction_on
  结论: (hI : 是幂零 I)
  证明: by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  induction n using Nat.strong_induction_on generalizing S with | _ n H
  by_cases hI' : I = ⊥
  · subst hI'
    apply h₁
    rw [← Ideal.zero_eq_bot]; rw [zero_pow two_ne_zero]
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    have := subsingl

Depends on / 依赖: Ideal.one_eq_top, Ideal.pow_le_self, Ideal.zero_eq_bot, Nat.strong_induction_on, Subsingleton, Subsingleton.elim, generalizing, hI.symm, n.succ, one_eq_top, pow_le_self, pow_mul, pow_one, pow_zero, strong_induction_on, subsingleton_of_bot_eq_top, two_ne_zero, zero_eq_bot, zero_pow
-/
theorem Ideal.IsNilpotent.induction_on (hI : IsNilpotent I)
    {P : forall ⦃S : Type _⦄ [CommRing S], Ideal S -> Prop}
    (h₁ : forall ⦃S : Type _⦄ [CommRing S], forall I : Ideal S, I ^ 2 = ⊥ -> P I)
    (h₂ : forall ⦃S : Type _⦄ [CommRing S], forall I J : Ideal S, I <= J -> P I ->
      P (J.map (Ideal.Quotient.mk I)) -> P J) :
    P I := by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  induction n using Nat.strong_induction_on generalizing S with | _ n H
  by_cases hI' : I = ⊥
  · subst hI'
    apply h₁
    rw [← Ideal.zero_eq_bot]; rw [zero_pow two_ne_zero]
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    have := subsingleton_of_bot_eq_top hI.symm
    exact (hI' (Subsingleton.elim _ _)).elim
  rcases n with - | n
  · rw [pow_one] at hI
    exact (hI' hI).elim
  apply h₂ (I ^ 2) _ (Ideal.pow_le_self two_ne_zero)
  · apply H n.succ _ (I ^ 2)
    · rw [← pow_mul, eq_bot_iff, ← hI, Nat.succ_eq_add_one]
      apply Ideal.pow_le_pow_right (by lia)
    · exact n.succ.lt_succ_self
  · apply h₁
    rw [← Ideal.map_pow]; rw [Ideal.map_quotient_self]

/--
theorem `IsNilpotent.isUnit_quotient_mk_iff` / 定理 `IsNilpotent.isUnit_quotient_mk_iff`

English:
theorem IsNilpotent.isUnit_quotient_mk_iff
  statement: {R : Type*} [CommRing R] {I : Ideal R}
  proof: by
refine ⟨?_, fun h => h.map Ideal.Quotient.mk I⟩
  revert x
  apply Ideal.IsNilpotent.induction_on (S := R) I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup

中文:
定理 是幂零.isUnit_quotient_mk_iff
  结论: {R : 类型} [交换环 R] {I : 理想 R}
  证明: by
refine ⟨?_, fun h => h.map Ideal.Quotient.mk I⟩
  revert x
  apply Ideal.IsNilpotent.induction_on (S := R) I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup

Depends on / 依赖: DoubleQuot, DoubleQuot.quotQuotEquivQuotSup, H.unit, Ideal.IsNilpotent.induction_on, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.quotEquivOfEq, IsNilpotent, IsUnit, IsUnit.mul_val_inv, Quotient, h.map, induction_on, introv, map_mul, map_one, mk_surjective, mul_val_inv, quotEquivOfEq, quotQuotEquivQuotSup
-/
theorem IsNilpotent.isUnit_quotient_mk_iff {R : Type*} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x := by
refine ⟨?_, fun h => h.map Ideal.Quotient.mk I⟩
  revert x
  apply Ideal.IsNilpotent.induction_on (S := R) I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup_eq_right.mpr e))).symm.toRingHom
  · introv e H
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑H.unit⁻¹ : S ⧸ I)
    have : Ideal.Quotient.mk I (x * y) = Ideal.Quotient.mk I 1 := by
      rw [map_one]; rw [map_mul]; rw [hy]; rw [IsUnit.mul_val_inv]
    rw [Ideal.Quotient.eq] at this
    have : (x * y - 1) ^ 2 = 0 := by
      rw [← Ideal.mem_bot]; rw [← e]
      exact Ideal.pow_mem_pow this _
    have : x * (y * (2 - x * y)) = 1 := by
      rw [eq_comm]; rw [← sub_eq_zero]; rw [← this]
      ring
    exact .of_mul_eq_one _ this

/--
theorem `Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk` / 定理 `Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk`

English:
theorem Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk
  given: {x : S} {n : Nat} (hn : n != 0)
  proof: by
  rw [← IsNilpotent.isUnit_quotient_mk_iff (I := Ideal.map (Ideal.Quotient.mk (I ^ n)) I)]
  · rw [← isUnit_map_iff (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self hn))]
    rfl
  · use n
    simp [← Ideal.map_pow]

中文:
定理 理想.商.isUnit_mk_pow_iff_isUnit_mk
  条件: {x : S} {n : 自然数} (hn : n != 0)
  证明: by
  rw [← IsNilpotent.isUnit_quotient_mk_iff (I := Ideal.map (Ideal.Quotient.mk (I ^ n)) I)]
  · rw [← isUnit_map_iff (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self hn))]
    rfl
  · use n
    simp [← Ideal.map_pow]

Depends on / 依赖: DoubleQuot, DoubleQuot.quotQuotEquivQuotOfLE, Ideal.Quotient.mk, Ideal.map, Ideal.map_pow, Ideal.pow_le_self, IsNilpotent, IsNilpotent.isUnit_quotient_mk_iff, Quotient, isUnit_map_iff, isUnit_quotient_mk_iff, map_pow, pow_le_self, quotQuotEquivQuotOfLE
-/
theorem Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk {x : S} {n : Nat} (hn : n != 0) :
    IsUnit (Ideal.Quotient.mk (I ^ n) x) ↔ IsUnit (Ideal.Quotient.mk I x) := by
  rw [← IsNilpotent.isUnit_quotient_mk_iff (I := Ideal.map (Ideal.Quotient.mk (I ^ n)) I)]
  · rw [← isUnit_map_iff (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self hn))]
    rfl
  · use n
    simp [← Ideal.map_pow]

/--
theorem `Ideal.Quotient.isUnit_mk_pow_iff_notMem` / 定理 `Ideal.Quotient.isUnit_mk_pow_iff_notMem`

English:
theorem Ideal.Quotient.isUnit_mk_pow_iff_notMem
  given: [I.IsMaximal] {n : Nat} (hn : n != 0) {x : S}
  proof: by
  let := Ideal.Quotient.field I
  rw [isUnit_mk_pow_iff_isUnit_mk I hn]; rw [isUnit_iff_ne_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.not

中文:
定理 理想.商.isUnit_mk_pow_iff_notMem
  条件: [I.是极大] {n : 自然数} (hn : n != 0) {x : S}
  证明: by
  let := Ideal.Quotient.field I
  rw [isUnit_mk_pow_iff_isUnit_mk I hn]; rw [isUnit_iff_ne_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.not

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem.not, Ideal.Quotient.field, Quotient, eq_zero_iff_mem, isUnit_iff_ne_zero, isUnit_mk_pow_iff_isUnit_mk
-/
theorem Ideal.Quotient.isUnit_mk_pow_iff_notMem [I.IsMaximal] {n : Nat} (hn : n != 0) {x : S} :
    IsUnit (mk (I ^ n) x) ↔ x ∉ I := by
  let := Ideal.Quotient.field I
  rw [isUnit_mk_pow_iff_isUnit_mk I hn]; rw [isUnit_iff_ne_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.not

/--
theorem `Ideal.Quotient.isUnit_mk_pow_of_notMem` / 定理 `Ideal.Quotient.isUnit_mk_pow_of_notMem`

English:
theorem Ideal.Quotient.isUnit_mk_pow_of_notMem
  given: [I.IsMaximal] {n : Nat} {x : S} (hx : x ∉ I)
  proof: by
  by_cases! hn : n = 0
  · rw [pow_eq_top_iff.mpr (Or.inr hn)]
    exact isUnit_of_subsingleton _
  exact (isUnit_mk_pow_iff_notMem I hn).mpr hx

中文:
定理 理想.商.isUnit_mk_pow_of_notMem
  条件: [I.是极大] {n : 自然数} {x : S} (hx : x ∉ I)
  证明: by
  by_cases! hn : n = 0
  · rw [pow_eq_top_iff.mpr (Or.inr hn)]
    exact isUnit_of_subsingleton _
  exact (isUnit_mk_pow_iff_notMem I hn).mpr hx

Depends on / 依赖: Or.inr, isUnit_mk_pow_iff_notMem, isUnit_of_subsingleton, pow_eq_top_iff, pow_eq_top_iff.mpr
-/
theorem Ideal.Quotient.isUnit_mk_pow_of_notMem [I.IsMaximal] {n : Nat} {x : S} (hx : x ∉ I) :
    IsUnit (mk (I ^ n) x) := by
  by_cases! hn : n = 0
  · rw [pow_eq_top_iff.mpr (Or.inr hn)]
    exact isUnit_of_subsingleton _
  exact (isUnit_mk_pow_iff_notMem I hn).mpr hx
