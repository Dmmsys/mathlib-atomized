/-
Copyright (c) 2024 F. Nuccio, H. Zheng, W. He, S. Wu, Y. Yuan, W. Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Huanyu Zheng, Sihan Wu, Wanyi He, Weichen Jiao, Yi Yuan
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Algebra.GroupWithZero.Conj
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The Jacobson-Noether theorem

This file contains a proof of the Jacobson-Noether theorem and some auxiliary lemmas.
Here we discuss different cases of characteristics of
the noncommutative division algebra `D` with center `k`.

## Main Results

- `exists_separable_and_not_isCentral` : (Jacobson-Noether theorem) For a
  non-commutative algebraic division algebra `D` (with base ring
  being its center `k`), then there exist an element `x` of
  `D \ k` that is separable over its center.
- `exists_separable_and_not_isCentral'` : (Jacobson-Noether theorem) For a
  non-commutative algebraic division algebra `D` (with base ring
  being a field `L`), if the center of `D` over `L` is `L`,
  then there exist an element `x` of `D \ L` that is separable over `L`.

## Notation

- `D` is a noncommutative division algebra
- `k` is the center of `D`

## Implementation Notes

Mathematically, `exists_separable_and_not_isCentral` and `exists_separable_and_not_isCentral'`
are equivalent.

The difference however, is that the former takes `D` as the only variable
and fixing `D` would forces `k`. Whereas the later takes `D` and `L` as
separate variables constrained by certain relations.

## Reference
* <https://ysharifi.wordpress.com/2011/09/30/the-jacobson-noether-theorem/>
-/

public section

namespace JacobsonNoether

variable {D : Type*} [DivisionRing D] [Algebra.IsAlgebraic (Subring.center D) D]

local notation3 "k" => Subring.center D

open Polynomial LinearMap LieAlgebra

/--
lemma `exists_pow_mem_center_of_inseparable` / 引理 `exists_pow_mem_center_of_inseparable`

English:
lemma exists_pow_mem_center_of_inseparable
  statement: (p : Nat) [hchar : ExpChar D p] (a : D)
  proof: by
  have := (@isPurelyInseparable_iff_pow_mem k D _ _ _ _ p (ExpChar.expChar_center_iff.2 hchar)).1
  have pure : IsPurelyInseparable k D := ⟨Algebra.IsAlgebraic.isIntegral, fun x hx => by
    rw [RingHom.mem_range]; rw [Subtype.exists]
    exact ⟨x, ⟨hinsep x hx, rfl⟩⟩⟩
  obtain ⟨n, ⟨m, hm⟩⟩ := th

中文:
引理 存在_pow_mem_center_of_inseparable
  结论: (p : 自然数) [hchar : ExpChar D p] (a : D)
  证明: by
  have := (@isPurelyInseparable_iff_pow_mem k D _ _ _ _ p (ExpChar.expChar_center_iff.2 hchar)).1
  have pure : IsPurelyInseparable k D := ⟨Algebra.IsAlgebraic.isIntegral, fun x hx => by
    rw [RingHom.mem_range]; rw [Subtype.exists]
    exact ⟨x, ⟨hinsep x hx, rfl⟩⟩⟩
  obtain ⟨n, ⟨m, hm⟩⟩ := th

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isIntegral, ExpChar, ExpChar.expChar_center_iff, IsAlgebraic, IsPurelyInseparable, RingHom, RingHom.mem_range, Set.mem_of_subset_of_mem, Set.mem_range, Subalgebra, Subalgebra.range_subset, Subtype, Subtype.exists, expChar_center_iff, hinsep, isIntegral, isPurelyInseparable_iff_pow_mem, mem_of_subset_of_mem, mem_range
-/
lemma exists_pow_mem_center_of_inseparable (p : Nat) [hchar : ExpChar D p] (a : D)
    (hinsep : forall x : D, IsSeparable k x -> x in k) : exists n, a ^ (p ^ n) in k := by
  have := (@isPurelyInseparable_iff_pow_mem k D _ _ _ _ p (ExpChar.expChar_center_iff.2 hchar)).1
  have pure : IsPurelyInseparable k D := ⟨Algebra.IsAlgebraic.isIntegral, fun x hx => by
    rw [RingHom.mem_range]; rw [Subtype.exists]
    exact ⟨x, ⟨hinsep x hx, rfl⟩⟩⟩
  obtain ⟨n, ⟨m, hm⟩⟩ := this pure a
  have := Subalgebra.range_subset (R := k) ⟨(k).toSubsemiring, fun r => r.2⟩
exact ⟨n, Set.mem_of_subset_of_mem this Set.mem_range.2 ⟨m, hm⟩⟩

/--
lemma `exists_pow_mem_center_of_inseparable'` / 引理 `exists_pow_mem_center_of_inseparable'`

English:
lemma exists_pow_mem_center_of_inseparable'
  statement: (p : Nat) [ExpChar D p] {a : D}
  proof: by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_of_inseparable p a hinsep
  have nzero : n != 0 := by
    rintro rfl
    rw [pow_zero]; rw [pow_one] at hn
    exact ha hn
  exact ⟨n, ⟨Nat.one_le_iff_ne_zero.mpr nzero, hn⟩⟩

中文:
引理 存在_pow_mem_center_of_inseparable'
  结论: (p : 自然数) [ExpChar D p] {a : D}
  证明: by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_of_inseparable p a hinsep
  have nzero : n != 0 := by
    rintro rfl
    rw [pow_zero]; rw [pow_one] at hn
    exact ha hn
  exact ⟨n, ⟨Nat.one_le_iff_ne_zero.mpr nzero, hn⟩⟩

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, exists_pow_mem_center_of_inseparable, hinsep, one_le_iff_ne_zero, pow_one, pow_zero
-/
lemma exists_pow_mem_center_of_inseparable' (p : Nat) [ExpChar D p] {a : D}
    (ha : a ∉ k) (hinsep : forall x : D, IsSeparable k x -> x in k) : exists n, 1 <= n ∧ a ^ (p ^ n) in k := by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_of_inseparable p a hinsep
  have nzero : n != 0 := by
    rintro rfl
    rw [pow_zero]; rw [pow_one] at hn
    exact ha hn
  exact ⟨n, ⟨Nat.one_le_iff_ne_zero.mpr nzero, hn⟩⟩

attribute [local instance 100] LieRing.ofAssociativeRing

/--
lemma `exist_pow_eq_zero_of_le` / 引理 `exist_pow_eq_zero_of_le`

English:
lemma exist_pow_eq_zero_of_le
  statement: (p : Nat) [hchar : ExpChar D p]
  proof: by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_of_inseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, fun n hn => ?_⟩⟩
  have inter : (ad k D a)^[p ^ m] = 0 := by
    ext x
    rw [ad_eq_lmul_left_sub_lmul_right]; rw [← Module.End.pow_apply]; rw [Pi.sub_apply]; rw [sub_pow_expChar_pow_of_commute p m (commute

中文:
引理 exist_pow_eq_zero_of_le
  结论: (p : 自然数) [hchar : ExpChar D p]
  证明: by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_of_inseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, fun n hn => ?_⟩⟩
  have inter : (ad k D a)^[p ^ m] = 0 := by
    ext x
    rw [ad_eq_lmul_left_sub_lmul_right]; rw [← Module.End.pow_apply]; rw [Pi.sub_apply]; rw [sub_pow_expChar_pow_of_commute p m (commute

Depends on / 依赖: LinearMap, LinearMap.sub_apply, Module, Module.End.pow_apply, Pi.sub_apply, Pi.zero_apply, Subring, Subring.mem_center_iff, ad_eq_lmul_left_sub_lmul_right, commute_mulLeft_right, exists_pow_mem_center_of_inseparable, hinsep, mem_center_iff, mulLeft_apply, mulRight_apply, pow_apply, pow_mulLeft, pow_mulRight, sub_apply, sub_eq_zero_of_eq
-/
lemma exist_pow_eq_zero_of_le (p : Nat) [hchar : ExpChar D p]
    {a : D} (ha : a ∉ k) (hinsep : forall x : D, IsSeparable k x -> x in k) :
    exists m, 1 <= m ∧ forall n, p ^ m <= n -> (ad k D a)^[n] = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_of_inseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, fun n hn => ?_⟩⟩
  have inter : (ad k D a)^[p ^ m] = 0 := by
    ext x
    rw [ad_eq_lmul_left_sub_lmul_right]; rw [← Module.End.pow_apply]; rw [Pi.sub_apply]; rw [sub_pow_expChar_pow_of_commute p m (commute_mulLeft_right a a)]; rw [LinearMap.sub_apply]; rw [pow_mulLeft]; rw [mulLeft_apply]; rw [pow_mulRight]; rw [mulRight_apply]; rw [Pi.zero_apply]; rw [Subring.mem_center_iff.1 hm.2 x]
    exact sub_eq_zero_of_eq rfl
  rw [(Nat.sub_eq_iff_eq_add hn).1 rfl]; rw [Function.iterate_add]; rw [inter]; rw [Pi.comp_zero]; rw [iterate_map_zero]; rw [Function.const_zero]

variable (D) in
/--
theorem `exists_separable_and_not_isCentral` / 定理 `exists_separable_and_not_isCentral`

English:
theorem exists_separable_and_not_isCentral
  given: (H : k != (⊤ : Subring D))
  proof: by
  obtain ⟨p, hp⟩ := ExpChar.exists D
  by_contra! insep
  replace insep : forall x : D, IsSeparable k x -> x in k :=
    fun x h => Classical.byContradiction fun hx => insep x hx h
  -- The element `a` below is in `D` but not in `k`.
obtain ⟨a, ha⟩ := not_forall.mp mt (Subring.eq_top_iff' k).mpr 

中文:
定理 存在_separable_and_not_isCentral
  条件: (H : k != (⊤ : 子环 D))
  证明: by
  obtain ⟨p, hp⟩ := ExpChar.exists D
  by_contra! insep
  replace insep : forall x : D, IsSeparable k x -> x in k :=
    fun x h => Classical.byContradiction fun hx => insep x hx h
  -- The element `a` below is in `D` but not in `k`.
obtain ⟨a, ha⟩ := not_forall.mp mt (Subring.eq_top_iff' k).mpr 

Depends on / 依赖: Classical, Classical.byContradiction, ExpChar, ExpChar.exists, IsSeparable, byContradiction, replace
-/
theorem exists_separable_and_not_isCentral (H : k != (⊤ : Subring D)) :
    exists x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := ExpChar.exists D
  by_contra! insep
  replace insep : forall x : D, IsSeparable k x -> x in k :=
    fun x h => Classical.byContradiction fun hx => insep x hx h
  -- The element `a` below is in `D` but not in `k`.
obtain ⟨a, ha⟩ := not_forall.mp mt (Subring.eq_top_iff' k).mpr H
have ha₀ : a != 0 := fun nh => nh ▸ ha Subring.zero_mem k
  -- We construct another element `b` that does not commute with `a`.
  obtain ⟨b, hb1⟩ : exists b : D, ad k D a b != 0 := by
    rw [Subring.mem_center_iff]; rw [not_forall] at ha
    use ha.choose
    change a * ha.choose - ha.choose * a != 0
    simpa only [ne_eq, sub_eq_zero] using Ne.symm ha.choose_spec
  -- We find a maximum natural number `n` such that `(a * x - x * a) ^ n b ≠ 0`.
  obtain ⟨n, hn, hb⟩ : exists n, 0 < n ∧ (ad k D a)^[n] b != 0 ∧ (ad k D a)^[n + 1] b = 0 := by
    obtain ⟨m, -, hm2⟩ := exist_pow_eq_zero_of_le p ha insep
    have h_exist : exists n, 0 < n ∧ (ad k D a)^[n + 1] b = 0 := ⟨p ^ m,
      ⟨expChar_pow_pos D p m, by rw [hm2 (p ^ m + 1) (Nat.le_add_right _ _), Pi.zero_apply]⟩⟩
    classical
    refine ⟨Nat.find h_exist, ⟨(Nat.find_spec h_exist).1, ?_, (Nat.find_spec h_exist).2⟩⟩
    set t := (Nat.find h_exist - 1 : Nat) with ht
    by_cases! h_pos : 0 < t
    · convert! (ne_eq _ _) ▸ not_and.mp (Nat.find_min h_exist (m := t) (by lia)) h_pos
      lia
    · suffices h_find : Nat.find h_exist = 1 by
        rwa [h_find]
      rw [Nat.le_zero]; rw [ht]; rw [Nat.sub_eq_zero_iff_le] at h_pos
      linarith [(Nat.find_spec h_exist).1]
  -- We define `c` to be the value that we proved above to be non-zero.
  set c := (ad k D a)^[n] b with hc_def
  let _ : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ hb.1, mul_inv_cancel₀ hb.1⟩
  -- We prove that `c` commutes with `a`.
  have hc : a * c = c * a := by
    apply eq_of_sub_eq_zero
    rw [← mulLeft_apply (R := k)]; rw [← mulRight_apply (R := k)]
    suffices ad k D a c = 0 from by
      rw [← this]; simp [LieRing.of_associative_ring_bracket]
    rw [← Function.iterate_succ_apply' (ad k D a) n b]; rw [hb.2]
  -- We now make some computation to obtain the final equation.
  set d := c⁻¹ * a * (ad k D a)^[n - 1] b with hd_def
  have hc' : c⁻¹ * a = a * c⁻¹ := by
    apply_fun (c⁻¹ * · * c⁻¹) at hc
    rw [mul_assoc]; rw [mul_assoc]; rw [mul_inv_cancel₀ hb.1]; rw [mul_one]; rw [← mul_assoc]; rw [inv_mul_cancel₀ hb.1]; rw [one_mul] at hc
    exact hc
  have c_eq : a * (ad k D a)^[n - 1] b - (ad k D a)^[n - 1] b * a = c := by
    rw [hc_def]; rw [← Nat.sub_add_cancel hn]; rw [Function.iterate_succ_apply' (ad k D a) _ b]; rfl
  have eq1 : c⁻¹ * a * (ad k D a)^[n - 1] b - c⁻¹ * (ad k D a)^[n - 1] b * a = 1 := by
    simp_rw [mul_assoc, (mul_sub_left_distrib c⁻¹ _ _).symm, c_eq, inv_mul_cancel_of_invertible]
  -- We show that `a` commutes with `d`.
  have deq : a * d - d * a = a := by
    nth_rw 3 [← mul_one a]
    rw [hd_def]; rw [← eq1]; rw [mul_sub]; rw [mul_assoc _ _ a]; rw [sub_right_inj]; rw [hc']; rw [← mul_assoc]; rw [← mul_assoc]; rw [← mul_assoc]
  -- This then yields a contradiction.
  apply_fun (a⁻¹ * ·) at deq
  rw [mul_sub]; rw [← mul_assoc]; rw [inv_mul_cancel₀ ha₀]; rw [one_mul]; rw [← mul_assoc]; rw [sub_eq_iff_eq_add] at deq
  obtain ⟨r, hr⟩ := exists_pow_mem_center_of_inseparable p d insep
  apply_fun (· ^ (p ^ r)) at deq
  rw [add_pow_expChar_pow_of_commute p r (Commute.one_left _)]; rw [one_pow]; rw [GroupWithZero.conj_pow₀ ha₀]; rw [← hr.comm]; rw [mul_assoc]; rw [inv_mul_cancel₀ ha₀]; rw [mul_one]; rw [right_eq_add] at deq
  exact one_ne_zero deq

open Subring Algebra in
/--
theorem `exists_separable_and_not_isCentral'` / 定理 `exists_separable_and_not_isCentral'`

English:
theorem exists_separable_and_not_isCentral'
  statement: {L D : Type*} [Field L] [DivisionRing D]
  proof: by
  have hcenter : Subalgebra.center L D = ⊥ := le_bot_iff.mp IsCentral.out
  have ntrivial : Subring.center D != ⊤ :=
    congr(Subalgebra.toSubring $hcenter).trans_ne (Subalgebra.toSubring_injective.ne hneq)
  set φ := Subalgebra.equivOfEq (⊥ : Subalgebra L D) (.center L D) hcenter.symm
  set equ

中文:
定理 存在_separable_and_not_isCentral'
  结论: {L D : 类型} [域 L] [除环 D]
  证明: by
  have hcenter : Subalgebra.center L D = ⊥ := le_bot_iff.mp IsCentral.out
  have ntrivial : Subring.center D != ⊤ :=
    congr(Subalgebra.toSubring $hcenter).trans_ne (Subalgebra.toSubring_injective.ne hneq)
  set φ := Subalgebra.equivOfEq (⊥ : Subalgebra L D) (.center L D) hcenter.symm
  set equ

Depends on / 依赖: Algebra, IsCentral, IsCentral.out, IsScalarTower, Subalgebra, Subalgebra.center, Subalgebra.equivOfEq, Subalgebra.toSubring, Subalgebra.toSubring_injective.ne, Subring, Subring.center, botEquiv, center, equiv.symm.toRingHom.toAlgebra, equiv.toRingHom.toAlgebra, equivOfEq, hcenter, hcenter.symm, le_bot_iff, le_bot_iff.mp
-/
theorem exists_separable_and_not_isCentral' {L D : Type*} [Field L] [DivisionRing D]
    [Algebra L D] [Algebra.IsAlgebraic L D] [Algebra.IsCentral L D]
    (hneq : (⊥ : Subalgebra L D) != ⊤) :
    exists x : D, x ∉ (⊥ : Subalgebra L D) ∧ IsSeparable L x := by
  have hcenter : Subalgebra.center L D = ⊥ := le_bot_iff.mp IsCentral.out
  have ntrivial : Subring.center D != ⊤ :=
    congr(Subalgebra.toSubring $hcenter).trans_ne (Subalgebra.toSubring_injective.ne hneq)
  set φ := Subalgebra.equivOfEq (⊥ : Subalgebra L D) (.center L D) hcenter.symm
  set equiv : L ≃+* (center D) := ((botEquiv L D).symm.trans φ).toRingEquiv
  let _ : Algebra L (center D) := equiv.toRingHom.toAlgebra
  let _ : Algebra (center D) L := equiv.symm.toRingHom.toAlgebra
  have _ : IsScalarTower L (center D) D := .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower (center D) L D := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply L (center D)]
    congr
    exact (equiv.apply_symm_apply x).symm
  have _ : Algebra.IsAlgebraic (center D) D := .tower_top (K := L) _
  obtain ⟨x, hxd, hx⟩ := exists_separable_and_not_isCentral D ntrivial
  exact ⟨x, ⟨by rwa [← Subalgebra.center_toSubring L, hcenter] at hxd, IsSeparable.tower_top _ hx⟩⟩

end JacobsonNoether
