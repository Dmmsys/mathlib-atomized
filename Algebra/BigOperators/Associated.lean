/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `Algebra.Associated`
and products of multisets, finsets, and finsupps.

-/

public section

assert_not_exists Field

variable {ι M M₀ : Type*}

-- the same local notation used in `Algebra.Associated`
local infixl:50 " ~ᵤ " => Associated

namespace Prime

variable [CommMonoidWithZero M₀] {p : M₀}

/--
theorem `exists_mem_multiset_dvd` / 定理 `exists_mem_multiset_dvd`

English:
theorem exists_mem_multiset_dvd
  given: (hp : Prime p) {s : Multiset M₀}
  statement: p ∣ s.prod -> exists a in s, p ∣ a
  proof: Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

中文:
定理 存在_mem_multiset_dvd
  条件: (hp : 素 p) {s : Multiset M₀}
  结论: p ∣ s.乘积 -> 存在 a in s, p ∣ a
  证明: Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Or.inl, Or.inr, dvd_or_dvd, hp.dvd_or_dvd, hp.not_dvd_one, induction_on, mem_cons_of_mem, mem_cons_self, not_dvd_one, s.prod
-/
theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod -> exists a in s, p ∣ a :=
  Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

/--
theorem `exists_mem_multiset_map_dvd` / 定理 `exists_mem_multiset_map_dvd`

English:
theorem exists_mem_multiset_map_dvd
  given: (hp : Prime p) {s : Multiset ι} {f : ι -> M₀}
  proof: fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h

中文:
定理 存在_mem_multiset_map_dvd
  条件: (hp : 素 p) {s : Multiset ι} {f : ι -> M₀}
  证明: fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h

Depends on / 依赖: Multiset, Multiset.mem_map, exists_exists_and_eq_and, exists_mem_multiset_dvd, exists_prop, hp.exists_mem_multiset_dvd, mem_map
-/
theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι -> M₀} :
    p ∣ (s.map f).prod -> exists a in s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h

/--
theorem `exists_mem_finset_dvd` / 定理 `exists_mem_finset_dvd`

English:
theorem exists_mem_finset_dvd
  given: (hp : Prime p) {s : Finset ι} {f : ι -> M₀}
  proof: hp.exists_mem_multiset_map_dvd

中文:
定理 存在_mem_finset_dvd
  条件: (hp : 素 p) {s : 有限集 ι} {f : ι -> M₀}
  证明: hp.exists_mem_multiset_map_dvd

Depends on / 依赖: exists_mem_multiset_map_dvd, hp.exists_mem_multiset_map_dvd
-/
theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι -> M₀} :
    p ∣ s.prod f -> exists i in s, p ∣ f i :=
  hp.exists_mem_multiset_map_dvd

end Prime

/--
theorem `Prod.associated_iff` / 定理 `Prod.associated_iff`

English:
theorem Prod.associated_iff
  given: {M N : Type*} [Monoid M] [Monoid N] {x z : M × N}
  proof: ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

中文:
定理 积类型.associated_iff
  条件: {M N : 类型} [幺半群 M] [幺半群 N] {x z : M × N}
  证明: ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

Depends on / 依赖: MulEquiv, MulEquiv.prodUnits.invFun, MulEquiv.prodUnits.toFun, Prod.eq_iff_fst_eq_snd_eq, eq_iff_fst_eq_snd_eq, invFun, prodUnits
-/
theorem Prod.associated_iff {M N : Type*} [Monoid M] [Monoid N] {x z : M × N} :
    x ~ᵤ z ↔ x.1 ~ᵤ z.1 ∧ x.2 ~ᵤ z.2 :=
  ⟨fun ⟨u, hu⟩ => ⟨⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩,
    ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩⟩,
  fun ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ =>
    ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨h₁, h₂⟩⟩⟩

-- TODO: this seems to trigger a bug in the mergeWithGrind linter
set_option linter.tacticAnalysis.mergeWithGrind false in
/--
theorem `Associated.prod` / 定理 `Associated.prod`

English:
theorem Associated.prod
  statement: {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι -> M)
  proof: by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | insert j s hjs IH =>
    classical
    convert_to (∏ i in insert j s, f i) ~ᵤ (∏ i in insert j s, g i)
    grind [Associated.mul_mul]

中文:
定理 Associated.乘积
  结论: {M : 类型} [交换幺半群 M] {ι : 类型} (s : 有限集 ι) (f : ι -> M)
  证明: by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | insert j s hjs IH =>
    classical
    convert_to (∏ i in insert j s, f i) ~ᵤ (∏ i in insert j s, g i)
    grind [Associated.mul_mul]

Depends on / 依赖: Associated, Associated.mul_mul, Finset, Finset.induction, Finset.prod_empty, classical, convert_to, insert, mul_mul, prod_empty
-/
theorem Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι -> M)
    (g : ι -> M) (h : forall i, i in s -> (f i) ~ᵤ (g i)) : (∏ i in s, f i) ~ᵤ (∏ i in s, g i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | insert j s hjs IH =>
    classical
    convert_to (∏ i in insert j s, f i) ~ᵤ (∏ i in insert j s, g i)
    grind [Associated.mul_mul]

/--
theorem `exists_associated_mem_of_dvd_prod` / 定理 `exists_associated_mem_of_dvd_prod`

English:
theorem exists_associated_mem_of_dvd_prod
  statement: [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
  proof: Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_isUnit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    rcases hp.dvd_or_dvd hps with h | h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

中文:
定理 存在_associated_mem_of_dvd_prod
  结论: [带零交换幺半群 M₀] [是乘零消去 M₀]
  证明: Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_isUnit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    rcases hp.dvd_or_dvd hps with h | h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.mem_cons, Multiset.mem_cons_self, Multiset.prod_cons, Or.inl, Or.inr, associated_of_dvd, dvd_or_dvd, hp.associated_of_dvd, hp.dvd_or_dvd, hp.not_isUnit, induction_on, isUnit_iff_dvd_one, mem_cons, mem_cons_self, not_isUnit, prod_cons
-/
theorem exists_associated_mem_of_dvd_prod [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    {p : M₀} (hp : Prime p)
    {s : Multiset M₀} : (forall r in s, Prime r) -> p ∣ s.prod -> exists q in s, p ~ᵤ q :=
  Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_isUnit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    rcases hp.dvd_or_dvd hps with h | h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

open Submonoid in
/--
theorem `divisor_closure_eq_closure` / 定理 `divisor_closure_eq_closure`

English:
theorem divisor_closure_eq_closure
  statement: [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
  proof: by
  obtain ⟨m, hm, hprod⟩ := exists_multiset_of_mem_closure hxy
  induction m using Multiset.induction generalizing x y with
  | empty =>
    apply subset_closure
    push _ in _
    simp only [Multiset.prod_zero] at hprod
    left; exact .of_mul_eq_one _ hprod.symm
  | cons c s hind =>
    simp only [Multiset.mem_cons, forall_eq_or_imp, Set.mem_ofPred] at hm
    simp only [Multiset.prod_cons] at hprod
    simp only [Set.mem_ofPred_eq] at hind
    obtain ⟨ha₁ | ha₂, hs⟩ := hm
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y * k) ?_ hs ?_
      · simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
        refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure ?_,
          Multiset.forall_mem_cons.2 ⟨subset_closure ?_, fun t ht => subset_closure (hs t ht)⟩⟩)
        · left; exact .of_mul_eq_one_right _ hk
        · left; exact ha₁
      · rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
        left; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; rw [hc, mul_assoc] at hprod
        refine Submonoid.mul_mem _ (subset_closure ?_)
          (hind _ _ ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
        · right; exact ha₂
        rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
        exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc]; rw [mul_comm x _]; rw [mul_assoc]; rw [mul_comm c _] at hprod
      refine hind x c ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))

中文:
定理 divisor_closure_eq_closure
  结论: [带零交换幺半群 M₀] [是乘零消去 M₀]
  证明: by
  obtain ⟨m, hm, hprod⟩ := exists_multiset_of_mem_closure hxy
  induction m using Multiset.induction generalizing x y with
  | empty =>
    apply subset_closure
    push _ in _
    simp only [Multiset.prod_zero] at hprod
    left; exact .of_mul_eq_one _ hprod.symm
  | cons c s hind =>
    simp only [Multiset.mem_cons, forall_eq_or_imp, Set.mem_ofPred] at hm
    simp only [Multiset.prod_cons] at hprod
    simp only [Set.mem_ofPred_eq] at hind
    obtain ⟨ha₁ | ha₂, hs⟩ := hm
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y * k) ?_ hs ?_
      · simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
        refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure ?_,
          Multiset.forall_mem_cons.2 ⟨subset_closure ?_, fun t ht => subset_closure (hs t ht)⟩⟩)
        · left; exact .of_mul_eq_one_right _ hk
        · left; exact ha₁
      · rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
        left; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; rw [hc, mul_assoc] at hprod
        refine Submonoid.mul_mem _ (subset_closure ?_)
          (hind _ _ ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
        · right; exact ha₂
        rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
        exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc]; rw [mul_comm x _]; rw [mul_assoc]; rw [mul_comm c _] at hprod
      refine hind x c ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))

Depends on / 依赖: Multiset, Multiset.induction, Multiset.mem_cons, Multiset.prod_cons, Multiset.prod_zero, Set.mem_ofPred, Set.mem_ofPred_eq, exists_multiset_of_mem_closure, exists_right_inv, forall_eq_or_imp, generalizing, hprod.symm, mem_cons, mem_ofPred, mem_ofPred_eq, of_mul_eq_one, prod_cons, prod_zero, subset_closure
-/
theorem divisor_closure_eq_closure [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    (x y : M₀) (hxy : x * y in closure { r : M₀ | IsUnit r ∨ Prime r}) :
    x in closure { r : M₀ | IsUnit r ∨ Prime r} := by
  obtain ⟨m, hm, hprod⟩ := exists_multiset_of_mem_closure hxy
  induction m using Multiset.induction generalizing x y with
  | empty =>
    apply subset_closure
    push _ in _
    simp only [Multiset.prod_zero] at hprod
    left; exact .of_mul_eq_one _ hprod.symm
  | cons c s hind =>
    simp only [Multiset.mem_cons, forall_eq_or_imp, Set.mem_ofPred] at hm
    simp only [Multiset.prod_cons] at hprod
    simp only [Set.mem_ofPred_eq] at hind
    obtain ⟨ha₁ | ha₂, hs⟩ := hm
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y * k) ?_ hs ?_
      · simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
        refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure ?_,
          Multiset.forall_mem_cons.2 ⟨subset_closure ?_, fun t ht => subset_closure (hs t ht)⟩⟩)
        · left; exact .of_mul_eq_one_right _ hk
        · left; exact ha₁
      · rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
        left; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; rw [hc, mul_assoc] at hprod
        refine Submonoid.mul_mem _ (subset_closure ?_)
          (hind _ _ ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
        · right; exact ha₂
        rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
        exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc]; rw [mul_comm x _]; rw [mul_assoc]; rw [mul_comm c _] at hprod
      refine hind x c ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))

/--
theorem `Multiset.prod_primes_dvd` / 定理 `Multiset.prod_primes_dvd`

English:
theorem Multiset.prod_primes_dvd
  statement: [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
  proof: by
  induction s using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.prod_zero, one_dvd]
  | cons a s induct =>
    rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    gcongr
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
    have a_prime := h a (Multiset.mem_cons_self a s)
    have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
    refine (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => ?_
    have assoc := b_prime.associated_of_dvd a_prime b_div_a
    have := uniq a
    rw [Multiset.countP_cons_of_pos _ (Associated.refl _)]; rw [Nat.succ_le_succ_iff]; rw [← not_lt]; rw [Multiset.countP_pos] at this
    exact this ⟨b, b_in_s, assoc.symm⟩

中文:
定理 Multiset.prod_primes_dvd
  结论: [带零交换幺半群 M₀] [是乘零消去 M₀]
  证明: by
  induction s using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.prod_zero, one_dvd]
  | cons a s induct =>
    rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    gcongr
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
    have a_prime := h a (Multiset.mem_cons_self a s)
    have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
    refine (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => ?_
    have assoc := b_prime.associated_of_dvd a_prime b_div_a
    have := uniq a
    rw [Multiset.countP_cons_of_pos _ (Associated.refl _)]; rw [Nat.succ_le_succ_iff]; rw [← not_lt]; rw [Multiset.countP_pos] at this
    exact this ⟨b, b_in_s, assoc.symm⟩

Depends on / 依赖: Multiset, Multiset.countP_le_of_le, Multiset.induction_on, Multiset.le_cons_self, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Multiset.prod_cons, Multiset.prod_zero, a_prime, b_div_n, b_in_s, countP_le_of_le, generalizing, induct, induction_on, le_cons_self, mem_cons_of_mem, mem_cons_self, one_dvd, prod_cons
-/
theorem Multiset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    [forall a : M₀, DecidablePred (Associated a)] {s : Multiset M₀} (n : M₀) (h : forall a in s, Prime a)
    (div : forall a in s, a ∣ n) (uniq : forall a, s.countP (Associated a) <= 1) : s.prod ∣ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.prod_zero, one_dvd]
  | cons a s induct =>
    rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    gcongr
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
    have a_prime := h a (Multiset.mem_cons_self a s)
    have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
    refine (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => ?_
    have assoc := b_prime.associated_of_dvd a_prime b_div_a
    have := uniq a
    rw [Multiset.countP_cons_of_pos _ (Associated.refl _)]; rw [Nat.succ_le_succ_iff]; rw [← not_lt]; rw [Multiset.countP_pos] at this
    exact this ⟨b, b_in_s, assoc.symm⟩

/--
theorem `Finset.prod_primes_dvd` / 定理 `Finset.prod_primes_dvd`

English:
theorem Finset.prod_primes_dvd
  statement: [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Subsingleton M₀ˣ]
  proof: by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

中文:
定理 有限集.prod_primes_dvd
  结论: [带零交换幺半群 M₀] [是乘零消去 M₀] [子单例 M₀ˣ]
  证明: by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

Depends on / 依赖: Finset, Finset.mem_def, Multiset, Multiset.countP_eq_card_filter, Multiset.map_id, Multiset.nodup_iff_count_le_one, Multiset.prod_primes_dvd, associated_eq_eq, classical, countP_eq_card_filter, count_eq_card_filter_eq, map_id, mem_def, nodup_iff_count_le_one, prod_primes_dvd, s.nodup, s.val.count_eq_card_filter_eq
-/
theorem Finset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Subsingleton M₀ˣ]
    {s : Finset M₀} (n : M₀) (h : forall a in s, Prime a) (div : forall a in s, a ∣ n) : ∏ p in s, p ∣ n := by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

namespace Associates

section CommMonoid

variable [CommMonoid M]

/--
theorem `prod_mk` / 定理 `prod_mk`

English:
theorem prod_mk
  given: {p : Multiset M}
  statement: (p.map Associates.mk).prod = Associates.mk p.prod
  proof: Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

中文:
定理 prod_mk
  条件: {p : Multiset M}
  结论: (p.map Associates.mk).乘积 = Associates.mk p.乘积
  证明: Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

Depends on / 依赖: Associates, Associates.mk_mul_mk, Multiset, Multiset.induction_on, induction_on, mk_mul_mk
-/
theorem prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.prod :=
  Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

/--
theorem `finsetProd_mk` / 定理 `finsetProd_mk`

English:
theorem finsetProd_mk
  given: {p : Finset ι} {f : ι -> M}
  proof: by
  rw [Finset.prod_eq_multiset_prod]; rw [← Function.comp_def]; rw [← Multiset.map_map]; rw [prod_mk]; rw [← Finset.prod_eq_multiset_prod]

@[deprecated (since := "2026-04-08")] alias finset_prod_mk := finsetProd_mk

中文:
定理 finsetProd_mk
  条件: {p : 有限集 ι} {f : ι -> M}
  证明: by
  rw [Finset.prod_eq_multiset_prod]; rw [← Function.comp_def]; rw [← Multiset.map_map]; rw [prod_mk]; rw [← Finset.prod_eq_multiset_prod]

@[deprecated (since := "2026-04-08")] alias finset_prod_mk := finsetProd_mk

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Function, Function.comp_def, Multiset, Multiset.map_map, comp_def, map_map, prod_eq_multiset_prod, prod_mk
-/
theorem finsetProd_mk {p : Finset ι} {f : ι -> M} :
    (∏ i in p, Associates.mk (f i)) = Associates.mk (∏ i in p, f i) := by
  rw [Finset.prod_eq_multiset_prod]; rw [← Function.comp_def]; rw [← Multiset.map_map]; rw [prod_mk]; rw [← Finset.prod_eq_multiset_prod]

@[deprecated (since := "2026-04-08")] alias finset_prod_mk := finsetProd_mk

/--
theorem `rel_associated_iff_map_eq_map` / 定理 `rel_associated_iff_map_eq_map`

English:
theorem rel_associated_iff_map_eq_map
  given: {p q : Multiset M}
  proof: by
  rw [← Multiset.rel_eq]; rw [Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]

中文:
定理 rel_associated_iff_map_eq_map
  条件: {p q : Multiset M}
  证明: by
  rw [← Multiset.rel_eq]; rw [Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]

Depends on / 依赖: Multiset, Multiset.rel_eq, Multiset.rel_map, mk_eq_mk_iff_associated, rel_eq, rel_map
-/
theorem rel_associated_iff_map_eq_map {p q : Multiset M} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq]; rw [Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]

/--
theorem `prod_eq_one_iff` / 定理 `prod_eq_one_iff`

English:
theorem prod_eq_one_iff
  given: {p : Multiset (Associates M)}
  proof: Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])

中文:
定理 prod_eq_one_iff
  条件: {p : Multiset (Associates M)}
  证明: Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, forall_and, induction_on, mul_eq_one, or_imp
-/
theorem prod_eq_one_iff {p : Multiset (Associates M)} :
    p.prod = 1 ↔ forall a in p, (a : Associates M) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])

/--
theorem `prod_le_prod` / 定理 `prod_le_prod`

English:
theorem prod_le_prod
  given: {p q : Multiset (Associates M)} (h : p <= q)
  statement: p.prod <= q.prod
  proof: by
  have := Classical.decEq (Associates M)
  suffices p.prod <= (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 <= p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

中文:
定理 prod_le_prod
  条件: {p q : Multiset (Associates M)} (h : p <= q)
  结论: p.乘积 <= q.乘积
  证明: by
  have := Classical.decEq (Associates M)
  suffices p.prod <= (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 <= p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

Depends on / 依赖: Associates, Classical, Classical.decEq, add_tsub_cancel_of_le, le_refl, mul_mono, one_le, p.prod
-/
theorem prod_le_prod {p q : Multiset (Associates M)} (h : p <= q) : p.prod <= q.prod := by
  have := Classical.decEq (Associates M)
  suffices p.prod <= (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 <= p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

end CommMonoid

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M₀]

/--
theorem `exists_mem_multiset_le_of_prime` / 定理 `exists_mem_multiset_le_of_prime`

English:
theorem exists_mem_multiset_le_of_prime
  statement: {s : Multiset (Associates M₀)} {p : Associates M₀}
  proof: Multiset.induction_on s (fun ⟨_, eq⟩ => (hp.ne_one (mul_eq_one.1 eq.symm).1).elim)
    fun a s ih h =>
    have : p <= a * s.prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

中文:
定理 存在_mem_multiset_le_of_prime
  结论: {s : Multiset (Associates M₀)} {p : Associates M₀}
  证明: Multiset.induction_on s (fun ⟨_, eq⟩ => (hp.ne_one (mul_eq_one.1 eq.symm).1).elim)
    fun a s ih h =>
    have : p <= a * s.prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.mem_cons_of_mem, Multiset.mem_cons_self, Or.inl, Or.inr, Prime.le_or_le, eq.symm, hp.ne_one, induction_on, le_or_le, mem_cons_of_mem, mem_cons_self, mul_eq_one, ne_one, s.prod
-/
theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates M₀)} {p : Associates M₀}
    (hp : Prime p) : p <= s.prod -> exists a in s, p <= a :=
  Multiset.induction_on s (fun ⟨_, eq⟩ => (hp.ne_one (mul_eq_one.1 eq.symm).1).elim)
    fun a s ih h =>
    have : p <= a * s.prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

end CancelCommMonoidWithZero

end Associates

namespace Multiset

/--
theorem `prod_ne_zero_of_prime` / 定理 `prod_ne_zero_of_prime`

English:
theorem prod_ne_zero_of_prime
  statement: [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀]
  proof: Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

中文:
定理 prod_ne_zero_of_prime
  结论: [带零交换幺半群 M₀] [无零因子 M₀] [非平凡 M₀]
  证明: Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

Depends on / 依赖: IsScalarTower, Multiset, Multiset.prod_ne_zero, Prime.ne_zero, Subsemiring, ne_zero, prod_ne_zero, subsemiring
-/
theorem prod_ne_zero_of_prime [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀]
    (s : Multiset M₀) (h : forall x in s, Prime x) : s.prod != 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

/--
theorem `Prime.dvd_finsetProd_iff` / 定理 `Prime.dvd_finsetProd_iff`

English:
theorem Prime.dvd_finsetProd_iff
  given: {S : Finset M₀} {p : M} (pp : Prime p) (g : M₀ -> M)
  proof: ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

@[deprecated (since := "2026-04-08")] alias Prime.dvd_finset_prod_iff := Prime.dvd_finsetProd_iff

中文:
定理 素.dvd_finsetProd_iff
  条件: {S : 有限集 M₀} {p : M} (pp : 素 p) (g : M₀ -> M)
  证明: ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

@[deprecated (since := "2026-04-08")] alias Prime.dvd_finset_prod_iff := Prime.dvd_finsetProd_iff

Depends on / 依赖: CommSemiring, dvd_prod_of_mem, dvd_trans, exists_mem_finset_dvd, of_algHom, pp.exists_mem_finset_dvd
-/
theorem Prime.dvd_finsetProd_iff {S : Finset M₀} {p : M} (pp : Prime p) (g : M₀ -> M) :
    p ∣ S.prod g ↔ exists a in S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

@[deprecated (since := "2026-04-08")] alias Prime.dvd_finset_prod_iff := Prime.dvd_finsetProd_iff

/--
theorem `Prime.not_dvd_finsetProd` / 定理 `Prime.not_dvd_finsetProd`

English:
theorem Prime.not_dvd_finsetProd
  statement: {S : Finset M₀} {p : M} (pp : Prime p) {g : M₀ -> M}
  proof: by
exact mt (Prime.dvd_finsetProd_iff pp _).1 not_exists.2 fun a => not_and.2 (hS a)

@[deprecated (since := "2026-04-08")] alias Prime.not_dvd_finset_prod := Prime.not_dvd_finsetProd

中文:
定理 素.not_dvd_finsetProd
  结论: {S : 有限集 M₀} {p : M} (pp : 素 p) {g : M₀ -> M}
  证明: by
exact mt (Prime.dvd_finsetProd_iff pp _).1 not_exists.2 fun a => not_and.2 (hS a)

@[deprecated (since := "2026-04-08")] alias Prime.not_dvd_finset_prod := Prime.not_dvd_finsetProd

Depends on / 依赖: Prime.dvd_finsetProd_iff, dvd_finsetProd_iff, not_and, not_exists
-/
theorem Prime.not_dvd_finsetProd {S : Finset M₀} {p : M} (pp : Prime p) {g : M₀ -> M}
    (hS : forall a in S, ¬p ∣ g a) : ¬p ∣ S.prod g := by
exact mt (Prime.dvd_finsetProd_iff pp _).1 not_exists.2 fun a => not_and.2 (hS a)

@[deprecated (since := "2026-04-08")] alias Prime.not_dvd_finset_prod := Prime.not_dvd_finsetProd

/--
theorem `Prime.dvd_finsuppProd_iff` / 定理 `Prime.dvd_finsuppProd_iff`

English:
theorem Prime.dvd_finsuppProd_iff
  given: {f : M₀ ->₀ M} {g : M₀ -> M -> Nat} {p : Nat} (pp : Prime p)
  proof: Prime.dvd_finsetProd_iff pp _

中文:
定理 素.dvd_finsuppProd_iff
  条件: {f : M₀ ->₀ M} {g : M₀ -> M -> 自然数} {p : 自然数} (pp : 素 p)
  证明: Prime.dvd_finsetProd_iff pp _

Depends on / 依赖: Prime.dvd_finsetProd_iff, dvd_finsetProd_iff
-/
theorem Prime.dvd_finsuppProd_iff {f : M₀ ->₀ M} {g : M₀ -> M -> Nat} {p : Nat} (pp : Prime p) :
    p ∣ f.prod g ↔ exists a in f.support, p ∣ g a (f a) :=
  Prime.dvd_finsetProd_iff pp _

/--
theorem `Prime.not_dvd_finsuppProd` / 定理 `Prime.not_dvd_finsuppProd`

English:
theorem Prime.not_dvd_finsuppProd
  statement: {f : M₀ ->₀ M} {g : M₀ -> M -> Nat} {p : Nat} (pp : Prime p)
  proof: Prime.not_dvd_finsetProd pp hS

中文:
定理 素.not_dvd_finsuppProd
  结论: {f : M₀ ->₀ M} {g : M₀ -> M -> 自然数} {p : 自然数} (pp : 素 p)
  证明: Prime.not_dvd_finsetProd pp hS

Depends on / 依赖: Prime.not_dvd_finsetProd, not_dvd_finsetProd
-/
theorem Prime.not_dvd_finsuppProd {f : M₀ ->₀ M} {g : M₀ -> M -> Nat} {p : Nat} (pp : Prime p)
    (hS : forall a in f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g :=
  Prime.not_dvd_finsetProd pp hS

end CommMonoidWithZero
