/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Prime ideals in ℕ and ℤ

## Main results

* `Ideal.isPrime_nat_iff`: the prime ideals in ℕ are ⟨0⟩, ⟨p⟩ (for prime `p`), and `⟨2, 3⟩ = {1}ᶜ`.
  The proof follows https://math.stackexchange.com/a/4224486.

* `Ideal.isPrime_int_iff` : the prime ideals in ℤ are ⟨0⟩ and ⟨p⟩ (for prime `p`).
-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalRing Nat
  body: by
    have h : a = 1 ∨ b = 1 := by lia
    apply h.imp <;> simp +contextual

中文:
实例 :
  签名: 是局部环 自然数
  定义体: by
    have h : a = 1 ∨ b = 1 := by lia
    apply h.imp <;> simp +contextual

Depends on / 依赖: contextual, h.imp
-/
instance : IsLocalRing Nat where
  isUnit_or_isUnit_of_add_one {a b} hab := by
    have h : a = 1 ∨ b = 1 := by lia
    apply h.imp <;> simp +contextual

open IsLocalRing Ideal

/--
theorem `Nat.mem_maximalIdeal_iff` / 定理 `Nat.mem_maximalIdeal_iff`

English:
theorem Nat.mem_maximalIdeal_iff
  given: {n : Nat}
  statement: n in maximalIdeal Nat ↔ n != 1
  proof: by simp

中文:
定理 自然数.mem_maximalIdeal_iff
  条件: {n : 自然数}
  结论: n in maximalIdeal 自然数 ↔ n != 1
  证明: by simp
-/
theorem Nat.mem_maximalIdeal_iff {n : Nat} : n in maximalIdeal Nat ↔ n != 1 := by simp

/--
theorem `Nat.coe_maximalIdeal` / 定理 `Nat.coe_maximalIdeal`

English:
theorem Nat.coe_maximalIdeal
  statement: (maximalIdeal Nat : Set Nat) = {1}ᶜ
  proof: by ext; simp

中文:
定理 自然数.coe_maximalIdeal
  结论: (maximalIdeal 自然数 : 集合 自然数) = {1}ᶜ
  证明: by ext; simp

Depends on / 依赖: continuous_pi_iff
-/
theorem Nat.coe_maximalIdeal : (maximalIdeal Nat : Set Nat) = {1}ᶜ := by ext; simp

/--
theorem `Nat.maximalIdeal_eq_span_two_three` / 定理 `Nat.maximalIdeal_eq_span_two_three`

English:
theorem Nat.maximalIdeal_eq_span_two_three
  statement: maximalIdeal Nat = span {2, 3}
  proof: by
  refine le_antisymm (fun n h => ?_) (span_le.mpr <| Set.pair_subset (by simp) (by simp))
  obtain lt | lt := (mem_maximalIdeal_iff.mp h).lt_or_gt
  · obtain rfl := lt_one_iff.mp lt; exact zero_mem _
exact mem_span_pair.mpr
    exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 n (by simp) (show 2 <= n by lia)

中文:
定理 自然数.maximalIdeal_eq_span_two_three
  结论: maximalIdeal 自然数 = span {2, 3}
  证明: by
  refine le_antisymm (fun n h => ?_) (span_le.mpr <| Set.pair_subset (by simp) (by simp))
  obtain lt | lt := (mem_maximalIdeal_iff.mp h).lt_or_gt
  · obtain rfl := lt_one_iff.mp lt; exact zero_mem _
exact mem_span_pair.mpr
    exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 n (by simp) (show 2 <= n by lia)

Depends on / 依赖: Set.pair_subset, continuous_iInf_dom, continuous_induced_dom, exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le, le_antisymm, lt_one_iff, lt_one_iff.mp, lt_or_gt, mem_maximalIdeal_iff, mem_maximalIdeal_iff.mp, mem_span_pair, mem_span_pair.mpr, pair_subset, span_le, span_le.mpr, zero_mem
-/
theorem Nat.maximalIdeal_eq_span_two_three : maximalIdeal Nat = span {2, 3} := by
  refine le_antisymm (fun n h => ?_) (span_le.mpr <| Set.pair_subset (by simp) (by simp))
  obtain lt | lt := (mem_maximalIdeal_iff.mp h).lt_or_gt
  · obtain rfl := lt_one_iff.mp lt; exact zero_mem _
exact mem_span_pair.mpr
    exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le 2 3 n (by simp) (show 2 <= n by lia)

/--
theorem `Nat.one_mem_span_iff` / 定理 `Nat.one_mem_span_iff`

English:
theorem Nat.one_mem_span_iff
  given: {s : Set Nat}
  statement: 1 in span s ↔ 1 in s
  proof: by
  rw [← SetLike.mem_coe]; rw [← not_iff_not]
  simp_rw [← Set.mem_compl_iff, ← Set.singleton_subset_iff, Set.subset_compl_comm]
  rw [Set.subset_compl_comm]; rw [← coe_maximalIdeal]; rw [SetLike.coe_subset_coe]; rw [span_le]

中文:
定理 自然数.one_mem_span_iff
  条件: {s : 集合 自然数}
  结论: 1 in span s ↔ 1 in s
  证明: by
  rw [← SetLike.mem_coe]; rw [← not_iff_not]
  simp_rw [← Set.mem_compl_iff, ← Set.singleton_subset_iff, Set.subset_compl_comm]
  rw [Set.subset_compl_comm]; rw [← coe_maximalIdeal]; rw [SetLike.coe_subset_coe]; rw [span_le]

Depends on / 依赖: Set.mem_compl_iff, Set.singleton_subset_iff, Set.subset_compl_comm, SetLike, SetLike.coe_subset_coe, SetLike.mem_coe, coe_maximalIdeal, coe_subset_coe, mem_coe, mem_compl_iff, not_iff_not, simp_rw, singleton_subset_iff, span_le, subset_compl_comm
-/
theorem Nat.one_mem_span_iff {s : Set Nat} : 1 in span s ↔ 1 in s := by
  rw [← SetLike.mem_coe]; rw [← not_iff_not]
  simp_rw [← Set.mem_compl_iff, ← Set.singleton_subset_iff, Set.subset_compl_comm]
  rw [Set.subset_compl_comm]; rw [← coe_maximalIdeal]; rw [SetLike.coe_subset_coe]; rw [span_le]

/--
theorem `Nat.one_mem_closure_iff` / 定理 `Nat.one_mem_closure_iff`

English:
theorem Nat.one_mem_closure_iff
  given: {s : Set Nat}
  statement: 1 in AddSubmonoid.closure s ↔ 1 in s
  proof: by
  rw [← Submodule.span_nat_eq_addSubmonoidClosure]
  exact one_mem_span_iff

中文:
定理 自然数.one_mem_closure_iff
  条件: {s : 集合 自然数}
  结论: 1 in 加法子幺半群.closure s ↔ 1 in s
  证明: by
  rw [← Submodule.span_nat_eq_addSubmonoidClosure]
  exact one_mem_span_iff

Depends on / 依赖: Submodule, Submodule.span_nat_eq_addSubmonoidClosure, one_mem_span_iff, span_nat_eq_addSubmonoidClosure
-/
theorem Nat.one_mem_closure_iff {s : Set Nat} : 1 in AddSubmonoid.closure s ↔ 1 in s := by
  rw [← Submodule.span_nat_eq_addSubmonoidClosure]
  exact one_mem_span_iff

/--
theorem `Ideal.isPrime_nat_iff` / 定理 `Ideal.isPrime_nat_iff`

English:
theorem Ideal.isPrime_nat_iff
  given: {P : Ideal Nat}
  proof: by
  refine .symm ⟨?_, fun h => or_iff_not_imp_left.mpr fun h0 => or_iff_not_imp_right.mpr fun hsp =>
    (le_maximalIdeal h.ne_top).antisymm fun n hn => ?_⟩
  · rintro (rfl | rfl | ⟨p, hp, rfl⟩)
    · exact isPrime_bot
    · exact (maximalIdeal.isMaximal Nat).isPrime
    · rwa [span_singleton_prime (by simp [hp.ne_zero]), ← Nat.prime_iff]
  rw [← le_bot_iff]; rw [SetLike.not_le_iff_exists] at h0
  classical
  let p := Nat.find h0
  have ⟨(hp : p in P), (hp0 : p != 0)⟩ := Nat.find_spec h0
  have : p != 1 := ne_of_mem_of_not_mem hp P.one_notMem
have prime : p.Prime := Nat.prime_iff_not_exists_mul_eq.mpr .intro (by lia)
    fun ⟨m, n, hm, hn, eq⟩ => have := mul_ne_zero_iff.mp (eq ▸ hp0)
    (h.mem_or_mem (eq ▸ hp)).elim (Nat.find_min h0 hm ⟨·, this.1⟩) (Nat.find_min h0 hn ⟨·, this.2⟩)
  push Not at hsp
  have ⟨q, hq, hqp⟩ := SetLike.exists_of_lt
    ((P.span_singleton_le_iff_mem.mpr hp).lt_of_ne (hsp p prime).symm)
  obtain rfl | hn1 := eq_or_ne n 0
  · exact Ideal.zero_mem _
  have : n != 1 := Nat.mem_maximalIdeal_iff.mp hn
  have ⟨a, b, eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q _
    (by simp [prime.coprime_iff_not_dvd.mpr (Ideal.mem_span_singleton.not.mp hqp)])
    (Nat.lt_pow_self (show 1 < n by lia)).le
  exact h.mem_of_pow_mem _ (eq ▸ add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hq))

中文:
定理 理想.isPrime_nat_iff
  条件: {P : 理想 自然数}
  证明: by
  refine .symm ⟨?_, fun h => or_iff_not_imp_left.mpr fun h0 => or_iff_not_imp_right.mpr fun hsp =>
    (le_maximalIdeal h.ne_top).antisymm fun n hn => ?_⟩
  · rintro (rfl | rfl | ⟨p, hp, rfl⟩)
    · exact isPrime_bot
    · exact (maximalIdeal.isMaximal Nat).isPrime
    · rwa [span_singleton_prime (by simp [hp.ne_zero]), ← Nat.prime_iff]
  rw [← le_bot_iff]; rw [SetLike.not_le_iff_exists] at h0
  classical
  let p := Nat.find h0
  have ⟨(hp : p in P), (hp0 : p != 0)⟩ := Nat.find_spec h0
  have : p != 1 := ne_of_mem_of_not_mem hp P.one_notMem
have prime : p.Prime := Nat.prime_iff_not_exists_mul_eq.mpr .intro (by lia)
    fun ⟨m, n, hm, hn, eq⟩ => have := mul_ne_zero_iff.mp (eq ▸ hp0)
    (h.mem_or_mem (eq ▸ hp)).elim (Nat.find_min h0 hm ⟨·, this.1⟩) (Nat.find_min h0 hn ⟨·, this.2⟩)
  push Not at hsp
  have ⟨q, hq, hqp⟩ := SetLike.exists_of_lt
    ((P.span_singleton_le_iff_mem.mpr hp).lt_of_ne (hsp p prime).symm)
  obtain rfl | hn1 := eq_or_ne n 0
  · exact Ideal.zero_mem _
  have : n != 1 := Nat.mem_maximalIdeal_iff.mp hn
  have ⟨a, b, eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q _
    (by simp [prime.coprime_iff_not_dvd.mpr (Ideal.mem_span_singleton.not.mp hqp)])
    (Nat.lt_pow_self (show 1 < n by lia)).le
  exact h.mem_of_pow_mem _ (eq ▸ add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hq))

Depends on / 依赖: Nat.find, Nat.find_spec, Nat.prime_iff, SetLike, SetLike.not_le_iff_exists, antisymm, classical, find_spec, h.ne_top, hp.ne_zero, isMaximal, isPrime, isPrime_bot, le_bot_iff, le_maximalIdeal, maximalIdeal, maximalIdeal.isMaximal, ne_of_mem_of_not_, ne_top, ne_zero
-/
theorem Ideal.isPrime_nat_iff {P : Ideal Nat} :
    P.IsPrime ↔ P = ⊥ ∨ P = maximalIdeal Nat ∨ exists p : Nat, p.Prime ∧ P = span {p} := by
  refine .symm ⟨?_, fun h => or_iff_not_imp_left.mpr fun h0 => or_iff_not_imp_right.mpr fun hsp =>
    (le_maximalIdeal h.ne_top).antisymm fun n hn => ?_⟩
  · rintro (rfl | rfl | ⟨p, hp, rfl⟩)
    · exact isPrime_bot
    · exact (maximalIdeal.isMaximal Nat).isPrime
    · rwa [span_singleton_prime (by simp [hp.ne_zero]), ← Nat.prime_iff]
  rw [← le_bot_iff]; rw [SetLike.not_le_iff_exists] at h0
  classical
  let p := Nat.find h0
  have ⟨(hp : p in P), (hp0 : p != 0)⟩ := Nat.find_spec h0
  have : p != 1 := ne_of_mem_of_not_mem hp P.one_notMem
have prime : p.Prime := Nat.prime_iff_not_exists_mul_eq.mpr .intro (by lia)
    fun ⟨m, n, hm, hn, eq⟩ => have := mul_ne_zero_iff.mp (eq ▸ hp0)
    (h.mem_or_mem (eq ▸ hp)).elim (Nat.find_min h0 hm ⟨·, this.1⟩) (Nat.find_min h0 hn ⟨·, this.2⟩)
  push Not at hsp
  have ⟨q, hq, hqp⟩ := SetLike.exists_of_lt
    ((P.span_singleton_le_iff_mem.mpr hp).lt_of_ne (hsp p prime).symm)
  obtain rfl | hn1 := eq_or_ne n 0
  · exact Ideal.zero_mem _
  have : n != 1 := Nat.mem_maximalIdeal_iff.mp hn
  have ⟨a, b, eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le p q _
    (by simp [prime.coprime_iff_not_dvd.mpr (Ideal.mem_span_singleton.not.mp hqp)])
    (Nat.lt_pow_self (show 1 < n by lia)).le
  exact h.mem_of_pow_mem _ (eq ▸ add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hq))

/--
theorem `Ideal.map_comap_natCastRingHom_int` / 定理 `Ideal.map_comap_natCastRingHom_int`

English:
theorem Ideal.map_comap_natCastRingHom_int
  given: {I : Ideal Int}
  proof: map_comap_le.antisymm fun n hn => n.sign_mul_natAbs ▸ mul_mem_left _ _ mem_map_of_mem _
    (mem_comap.mpr <| show (n.natAbs : Int) in I from n.sign_mul_self ▸ mul_mem_left _ _ hn)

中文:
定理 理想.map_comap_natCastRingHom_int
  条件: {I : 理想 整数}
  证明: map_comap_le.antisymm fun n hn => n.sign_mul_natAbs ▸ mul_mem_left _ _ mem_map_of_mem _
    (mem_comap.mpr <| show (n.natAbs : Int) in I from n.sign_mul_self ▸ mul_mem_left _ _ hn)

Depends on / 依赖: antisymm, map_comap_le, map_comap_le.antisymm, mem_comap, mem_comap.mpr, mem_map_of_mem, mul_mem_left, n.natAbs, n.sign_mul_natAbs, n.sign_mul_self, natAbs, sign_mul_natAbs, sign_mul_self
-/
theorem Ideal.map_comap_natCastRingHom_int {I : Ideal Int} :
    (I.comap (Nat.castRingHom Int)).map (Nat.castRingHom Int) = I :=
map_comap_le.antisymm fun n hn => n.sign_mul_natAbs ▸ mul_mem_left _ _ mem_map_of_mem _
    (mem_comap.mpr <| show (n.natAbs : Int) in I from n.sign_mul_self ▸ mul_mem_left _ _ hn)

/--
theorem `Ideal.isPrime_int_iff` / 定理 `Ideal.isPrime_int_iff`

English:
theorem Ideal.isPrime_int_iff
  given: {P : Ideal Int}
  proof: isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors.trans or_congr_right
  ⟨fun ⟨p, hp, eq⟩ => ⟨_, Int.prime_iff_natAbs_prime.mp hp, eq.trans
    p.span_natAbs.symm⟩, fun ⟨_p, hp, eq⟩ => ⟨_, Nat.prime_iff_prime_int.mp hp, eq⟩⟩

中文:
定理 理想.isPrime_int_iff
  条件: {P : 理想 整数}
  证明: isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors.trans or_congr_right
  ⟨fun ⟨p, hp, eq⟩ => ⟨_, Int.prime_iff_natAbs_prime.mp hp, eq.trans
    p.span_natAbs.symm⟩, fun ⟨_p, hp, eq⟩ => ⟨_, Nat.prime_iff_prime_int.mp hp, eq⟩⟩

Depends on / 依赖: Int.prime_iff_natAbs_prime.mp, Nat.prime_iff_prime_int.mp, eq.trans, isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors, isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors.trans, or_congr_right, p.span_natAbs.symm, prime_iff_natAbs_prime, prime_iff_prime_int, span_natAbs
-/
theorem Ideal.isPrime_int_iff {P : Ideal Int} :
    P.IsPrime ↔ P = ⊥ ∨ exists p : Nat, p.Prime ∧ P = span {(p : Int)} :=
isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors.trans or_congr_right
  ⟨fun ⟨p, hp, eq⟩ => ⟨_, Int.prime_iff_natAbs_prime.mp hp, eq.trans
    p.span_natAbs.symm⟩, fun ⟨_p, hp, eq⟩ => ⟨_, Nat.prime_iff_prime_int.mp hp, eq⟩⟩

/--
theorem `ringKrullDim_nat` / 定理 `ringKrullDim_nat`

English:
theorem ringKrullDim_nat
  statement: ringKrullDim Nat = 2
  proof: by
  refine le_antisymm (iSup_le fun s => le_of_not_gt fun hs => ?_) ?_
  · replace hs : 2 < s.length := ENat.natCast_lt_natCast.mp (WithBot.coe_lt_coe.mp hs)
    let s := s.take ⟨3, by lia⟩
    have : NeZero s.length := ⟨three_ne_zero⟩
    have h1 : ⊥ < (s 1).asIdeal := bot_le.trans_lt (s.step 0)
    obtain hmax | ⟨p, hp, hsp⟩ := (Ideal.isPrime_nat_iff.mp (s 1).2).resolve_left h1.ne'
    · exact (le_maximalIdeal_of_isPrime (s 2).asIdeal).not_gt (hmax.symm.trans_lt (s.step 1))
    obtain hmax | ⟨q, hq, hsq⟩ :=
      (Ideal.isPrime_nat_iff.mp (s 2).2).resolve_left (h1.trans (s.step 1)).ne'
    · exact (le_maximalIdeal_of_isPrime (s 3).asIdeal).not_gt (hmax.symm.trans_lt (s.step 2))
· exact hq.not_isUnit (Ideal.span_singleton_lt_span_singleton.mp
        ((hsp.symm.trans_lt (s.step 1)).trans_eq hsq)).isUnit_of_irreducible_right hp
  · refine le_iSup_of_le ⟨2, ![⊥, ⟨_, (span_singleton_prime two_ne_zero).mpr <| Nat.prime_iff.mp
      Nat.prime_two⟩, ⟨_, (maximalIdeal.isMaximal Nat).isPrime⟩], fun i => ?_⟩ le_rfl
    fin_cases i
    · exact bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr two_ne_zero)
    · simp_rw [Nat.maximalIdeal_eq_span_two_three]
      exact SetLike.lt_iff_le_and_exists.mpr ⟨Ideal.span_mono (by simp),
3, Ideal.subset_span (by simp), Ideal.mem_span_singleton.not.mpr by simp⟩

中文:
定理 ringKrullDim_nat
  结论: ringKrullDim 自然数 = 2
  证明: by
  refine le_antisymm (iSup_le fun s => le_of_not_gt fun hs => ?_) ?_
  · replace hs : 2 < s.length := ENat.natCast_lt_natCast.mp (WithBot.coe_lt_coe.mp hs)
    let s := s.take ⟨3, by lia⟩
    have : NeZero s.length := ⟨three_ne_zero⟩
    have h1 : ⊥ < (s 1).asIdeal := bot_le.trans_lt (s.step 0)
    obtain hmax | ⟨p, hp, hsp⟩ := (Ideal.isPrime_nat_iff.mp (s 1).2).resolve_left h1.ne'
    · exact (le_maximalIdeal_of_isPrime (s 2).asIdeal).not_gt (hmax.symm.trans_lt (s.step 1))
    obtain hmax | ⟨q, hq, hsq⟩ :=
      (Ideal.isPrime_nat_iff.mp (s 2).2).resolve_left (h1.trans (s.step 1)).ne'
    · exact (le_maximalIdeal_of_isPrime (s 3).asIdeal).not_gt (hmax.symm.trans_lt (s.step 2))
· exact hq.not_isUnit (Ideal.span_singleton_lt_span_singleton.mp
        ((hsp.symm.trans_lt (s.step 1)).trans_eq hsq)).isUnit_of_irreducible_right hp
  · refine le_iSup_of_le ⟨2, ![⊥, ⟨_, (span_singleton_prime two_ne_zero).mpr <| Nat.prime_iff.mp
      Nat.prime_two⟩, ⟨_, (maximalIdeal.isMaximal Nat).isPrime⟩], fun i => ?_⟩ le_rfl
    fin_cases i
    · exact bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr two_ne_zero)
    · simp_rw [Nat.maximalIdeal_eq_span_two_three]
      exact SetLike.lt_iff_le_and_exists.mpr ⟨Ideal.span_mono (by simp),
3, Ideal.subset_span (by simp), Ideal.mem_span_singleton.not.mpr by simp⟩

Depends on / 依赖: ENat.natCast_lt_natCast.mp, Ideal.isPri, Ideal.isPrime_nat_iff.mp, NeZero, WithBot, WithBot.coe_lt_coe.mp, asIdeal, bot_le, bot_le.trans_lt, coe_lt_coe, h1.ne, hmax.symm.trans_lt, iSup_le, isPrime_nat_iff, le_antisymm, le_maximalIdeal_of_isPrime, le_of_not_gt, length, natCast_lt_natCast, not_gt
-/
theorem ringKrullDim_nat : ringKrullDim Nat = 2 := by
  refine le_antisymm (iSup_le fun s => le_of_not_gt fun hs => ?_) ?_
  · replace hs : 2 < s.length := ENat.natCast_lt_natCast.mp (WithBot.coe_lt_coe.mp hs)
    let s := s.take ⟨3, by lia⟩
    have : NeZero s.length := ⟨three_ne_zero⟩
    have h1 : ⊥ < (s 1).asIdeal := bot_le.trans_lt (s.step 0)
    obtain hmax | ⟨p, hp, hsp⟩ := (Ideal.isPrime_nat_iff.mp (s 1).2).resolve_left h1.ne'
    · exact (le_maximalIdeal_of_isPrime (s 2).asIdeal).not_gt (hmax.symm.trans_lt (s.step 1))
    obtain hmax | ⟨q, hq, hsq⟩ :=
      (Ideal.isPrime_nat_iff.mp (s 2).2).resolve_left (h1.trans (s.step 1)).ne'
    · exact (le_maximalIdeal_of_isPrime (s 3).asIdeal).not_gt (hmax.symm.trans_lt (s.step 2))
· exact hq.not_isUnit (Ideal.span_singleton_lt_span_singleton.mp
        ((hsp.symm.trans_lt (s.step 1)).trans_eq hsq)).isUnit_of_irreducible_right hp
  · refine le_iSup_of_le ⟨2, ![⊥, ⟨_, (span_singleton_prime two_ne_zero).mpr <| Nat.prime_iff.mp
      Nat.prime_two⟩, ⟨_, (maximalIdeal.isMaximal Nat).isPrime⟩], fun i => ?_⟩ le_rfl
    fin_cases i
    · exact bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr two_ne_zero)
    · simp_rw [Nat.maximalIdeal_eq_span_two_three]
      exact SetLike.lt_iff_le_and_exists.mpr ⟨Ideal.span_mono (by simp),
3, Ideal.subset_span (by simp), Ideal.mem_span_singleton.not.mpr by simp⟩
