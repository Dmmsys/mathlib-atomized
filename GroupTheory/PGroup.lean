/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning, Snir Broshi
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

@[expose] public section

open Fintype MulAction

variable (p : Nat) (G : Type*) [Group G]

/--
Definition of `IsPGroup` / `IsPGroup` 的定义

English:
definition IsPGroup
  signature: : Prop
  body: forall g : G, exists k : Nat, g ^ p ^ k = 1

中文:
定义 是p群
  签名: : 命题
  定义体: forall g : G, exists k : Nat, g ^ p ^ k = 1
-/
def IsPGroup : Prop :=
  forall g : G, exists k : Nat, g ^ p ^ k = 1

variable {p} {G}

namespace IsPGroup

/--
theorem `_root_.isPGroup_iff_pow_pow_eq_one` / 定理 `_root_.isPGroup_iff_pow_pow_eq_one`

English:
theorem _root_.isPGroup_iff_pow_pow_eq_one
  statement: IsPGroup p G ↔ forall g : G, exists k, g ^ p ^ k = 1
  proof: .rfl

alias ⟨exists_pow_pow_eq_one, _⟩ := isPGroup_iff_pow_pow_eq_one

中文:
定理 _root_.isPGroup_iff_pow_pow_eq_one
  结论: 是p群 p G ↔ 对任意 g : G, 存在 k, g ^ p ^ k = 1
  证明: .rfl

alias ⟨exists_pow_pow_eq_one, _⟩ := isPGroup_iff_pow_pow_eq_one
-/
theorem _root_.isPGroup_iff_pow_pow_eq_one : IsPGroup p G ↔ forall g : G, exists k, g ^ p ^ k = 1 :=
  .rfl

alias ⟨exists_pow_pow_eq_one, _⟩ := isPGroup_iff_pow_pow_eq_one

/--
theorem `_root_.isPGroup_iff_orderOf_dvd_pow` / 定理 `_root_.isPGroup_iff_orderOf_dvd_pow`

English:
theorem _root_.isPGroup_iff_orderOf_dvd_pow
  statement: IsPGroup p G ↔ forall g : G, exists k, orderOf g ∣ p ^ k
  proof: by
  simp_rw [isPGroup_iff_pow_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

alias ⟨exists_orderOf_dvd_pow, _⟩ := isPGroup_iff_orderOf_dvd_pow

中文:
定理 _root_.isPGroup_iff_orderOf_dvd_pow
  结论: 是p群 p G ↔ 对任意 g : G, 存在 k, orderOf g ∣ p ^ k
  证明: by
  simp_rw [isPGroup_iff_pow_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

alias ⟨exists_orderOf_dvd_pow, _⟩ := isPGroup_iff_orderOf_dvd_pow

Depends on / 依赖: isPGroup_iff_pow_pow_eq_one, orderOf_dvd_iff_pow_eq_one, simp_rw
-/
theorem _root_.isPGroup_iff_orderOf_dvd_pow : IsPGroup p G ↔ forall g : G, exists k, orderOf g ∣ p ^ k := by
  simp_rw [isPGroup_iff_pow_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

alias ⟨exists_orderOf_dvd_pow, _⟩ := isPGroup_iff_orderOf_dvd_pow

/--
theorem `iff_orderOf` / 定理 `iff_orderOf`

English:
theorem iff_orderOf
  given: [Fact p.Prime]
  statement: IsPGroup p G ↔ forall g : G, exists k, orderOf g = p ^ k
  proof: by
  simp_rw [isPGroup_iff_orderOf_dvd_pow, Nat.dvd_prime_pow Fact.out]
exact forall_congr' fun g => ⟨by grind, .imp by grind⟩

alias ⟨exists_orderOf_eq_pow, _⟩ := iff_orderOf

中文:
定理 iff_orderOf
  条件: [Fact p.素]
  结论: 是p群 p G ↔ 对任意 g : G, 存在 k, orderOf g = p ^ k
  证明: by
  simp_rw [isPGroup_iff_orderOf_dvd_pow, Nat.dvd_prime_pow Fact.out]
exact forall_congr' fun g => ⟨by grind, .imp by grind⟩

alias ⟨exists_orderOf_eq_pow, _⟩ := iff_orderOf

Depends on / 依赖: Fact.out, Nat.dvd_prime_pow, dvd_prime_pow, forall_congr, isPGroup_iff_orderOf_dvd_pow, simp_rw
-/
theorem iff_orderOf [Fact p.Prime] : IsPGroup p G ↔ forall g : G, exists k, orderOf g = p ^ k := by
  simp_rw [isPGroup_iff_orderOf_dvd_pow, Nat.dvd_prime_pow Fact.out]
exact forall_congr' fun g => ⟨by grind, .imp by grind⟩

alias ⟨exists_orderOf_eq_pow, _⟩ := iff_orderOf

/--
theorem `of_card_dvd_pow` / 定理 `of_card_dvd_pow`

English:
theorem of_card_dvd_pow
  given: {n : Nat} (hG : Nat.card G ∣ p ^ n)
  statement: IsPGroup p G
  proof: by
  refine fun g => ⟨n, ?_⟩
  grw [← orderOf_dvd_iff_pow_eq_one, ← hG, orderOf_dvd_natCard]

中文:
定理 of_card_dvd_pow
  条件: {n : 自然数} (hG : 自然数.card G ∣ p ^ n)
  结论: 是p群 p G
  证明: by
  refine fun g => ⟨n, ?_⟩
  grw [← orderOf_dvd_iff_pow_eq_one, ← hG, orderOf_dvd_natCard]

Depends on / 依赖: orderOf_dvd_iff_pow_eq_one, orderOf_dvd_natCard
-/
theorem of_card_dvd_pow {n : Nat} (hG : Nat.card G ∣ p ^ n) : IsPGroup p G := by
  refine fun g => ⟨n, ?_⟩
  grw [← orderOf_dvd_iff_pow_eq_one, ← hG, orderOf_dvd_natCard]

/--
theorem `_root_.isPGroup_iff_card_dvd_pow` / 定理 `_root_.isPGroup_iff_card_dvd_pow`

English:
theorem _root_.isPGroup_iff_card_dvd_pow
  given: [Finite G]
  statement: IsPGroup p G ↔ exists n, Nat.card G ∣ p ^ n
  proof: by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => of_card_dvd_pow hn⟩
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp⟩
.mpr fun q hq => ?_⟩ refine ⟨Nat.card G, Nat.dvd_pow_self_iff NeZero.out hp
  have ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
  have ⟨k, hk⟩ := h.exists_orderOf_dvd_pow g
exact Nat.mem_primeFactors.mpr ⟨hqp, hqp.dvd_of_dvd_pow hg ▸ hk, hp⟩

alias ⟨exists_card_dvd_pow, _⟩ := isPGroup_iff_card_dvd_pow

中文:
定理 _root_.isPGroup_iff_card_dvd_pow
  条件: [有限 G]
  结论: 是p群 p G ↔ 存在 n, 自然数.card G ∣ p ^ n
  证明: by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => of_card_dvd_pow hn⟩
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp⟩
.mpr fun q hq => ?_⟩ refine ⟨Nat.card G, Nat.dvd_pow_self_iff NeZero.out hp
  have ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
  have ⟨k, hk⟩ := h.exists_orderOf_dvd_pow g
exact Nat.mem_primeFactors.mpr ⟨hqp, hqp.dvd_of_dvd_pow hg ▸ hk, hp⟩

alias ⟨exists_card_dvd_pow, _⟩ := isPGroup_iff_card_dvd_pow

Depends on / 依赖: Nat.card, Nat.dvd_pow_self_iff, Nat.mem_primeFactors.mp, Nat.mem_primeFactors.mpr, NeZero, NeZero.out, dvd_of_dvd_pow, dvd_pow_self_iff, eq_or_ne, exists_orderOf_dvd_pow, exists_prime_orderOf_dvd_card, h.exists_orderOf_dvd_pow, hqp.dvd_of_dvd_pow, mem_primeFactors, of_card_dvd_pow
-/
theorem _root_.isPGroup_iff_card_dvd_pow [Finite G] : IsPGroup p G ↔ exists n, Nat.card G ∣ p ^ n := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => of_card_dvd_pow hn⟩
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp⟩
.mpr fun q hq => ?_⟩ refine ⟨Nat.card G, Nat.dvd_pow_self_iff NeZero.out hp
  have ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
  have ⟨k, hk⟩ := h.exists_orderOf_dvd_pow g
exact Nat.mem_primeFactors.mpr ⟨hqp, hqp.dvd_of_dvd_pow hg ▸ hk, hp⟩

alias ⟨exists_card_dvd_pow, _⟩ := isPGroup_iff_card_dvd_pow

/--
theorem `dvd_orderOf` / 定理 `dvd_orderOf`

English:
theorem dvd_orderOf
  given: [Fact p.Prime] (hG : IsPGroup p G) {g : G} (hg : g != 1)
  statement: p ∣ orderOf g
  proof: by
  have ⟨k, hk⟩ := hG.exists_orderOf_eq_pow g
  rw [hk]
  refine dvd_pow_self _ fun hk0 => hg ?_
  rw [← orderOf_eq_one_iff]; rw [hk]; rw [hk0]; rw [pow_zero]

中文:
定理 dvd_orderOf
  条件: [Fact p.素] (hG : 是p群 p G) {g : G} (hg : g != 1)
  结论: p ∣ orderOf g
  证明: by
  have ⟨k, hk⟩ := hG.exists_orderOf_eq_pow g
  rw [hk]
  refine dvd_pow_self _ fun hk0 => hg ?_
  rw [← orderOf_eq_one_iff]; rw [hk]; rw [hk0]; rw [pow_zero]

Depends on / 依赖: dvd_pow_self, exists_orderOf_eq_pow, hG.exists_orderOf_eq_pow, orderOf_eq_one_iff, pow_zero
-/
theorem dvd_orderOf [Fact p.Prime] (hG : IsPGroup p G) {g : G} (hg : g != 1) : p ∣ orderOf g := by
  have ⟨k, hk⟩ := hG.exists_orderOf_eq_pow g
  rw [hk]
  refine dvd_pow_self _ fun hk0 => hg ?_
  rw [← orderOf_eq_one_iff]; rw [hk]; rw [hk0]; rw [pow_zero]

/--
theorem `of_card` / 定理 `of_card`

English:
theorem of_card
  given: {n : Nat} (hG : Nat.card G = p ^ n)
  statement: IsPGroup p G
  proof: of_card_dvd_pow hG.dvd

中文:
定理 of_card
  条件: {n : 自然数} (hG : 自然数.card G = p ^ n)
  结论: 是p群 p G
  证明: of_card_dvd_pow hG.dvd

Depends on / 依赖: hG.dvd, of_card_dvd_pow
-/
theorem of_card {n : Nat} (hG : Nat.card G = p ^ n) : IsPGroup p G :=
  of_card_dvd_pow hG.dvd

variable (p G) in
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton G]
  statement: IsPGroup p G
  proof: of_card (n := 0) (by simp)

中文:
定理 of_subsingleton
  条件: [子单例 G]
  结论: 是p群 p G
  证明: of_card (n := 0) (by simp)

Depends on / 依赖: of_card
-/
theorem of_subsingleton [Subsingleton G] : IsPGroup p G :=
  of_card (n := 0) (by simp)

/--
theorem `of_bot` / 定理 `of_bot`

English:
theorem of_bot
  statement: IsPGroup p (⊥ : Subgroup G)
  proof: .of_subsingleton p _

中文:
定理 of_bot
  结论: 是p群 p (⊥ : 子群 G)
  证明: .of_subsingleton p _

Depends on / 依赖: of_subsingleton
-/
theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  .of_subsingleton p _

variable (G) in
@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: IsPGroup 0 G
  proof: fun g => ⟨1, by simp⟩

@[simp]

中文:
定理 zero
  结论: 是p群 0 G
  证明: fun g => ⟨1, by simp⟩

@[simp]
-/
protected theorem zero : IsPGroup 0 G :=
  fun g => ⟨1, by simp⟩

@[simp]
/--
theorem `_root_.isPGroup_one_iff_subsingleton` / 定理 `_root_.isPGroup_one_iff_subsingleton`

English:
theorem _root_.isPGroup_one_iff_subsingleton
  statement: IsPGroup 1 G ↔ Subsingleton G
  proof: by
  refine ⟨?_, fun h => .of_subsingleton 1 G⟩
  simpa [isPGroup_iff_pow_pow_eq_one] using subsingleton_of_forall_eq 1

中文:
定理 _root_.isPGroup_one_iff_subsingleton
  结论: 是p群 1 G ↔ 子单例 G
  证明: by
  refine ⟨?_, fun h => .of_subsingleton 1 G⟩
  simpa [isPGroup_iff_pow_pow_eq_one] using subsingleton_of_forall_eq 1

Depends on / 依赖: isPGroup_iff_pow_pow_eq_one, of_subsingleton, subsingleton_of_forall_eq
-/
theorem _root_.isPGroup_one_iff_subsingleton : IsPGroup 1 G ↔ Subsingleton G := by
  refine ⟨?_, fun h => .of_subsingleton 1 G⟩
  simpa [isPGroup_iff_pow_pow_eq_one] using subsingleton_of_forall_eq 1

/--
theorem `card` / 定理 `card`

English:
theorem card
  statement: IsPGroup (Nat.card G) G
  proof: fun g => ⟨1, by simp⟩

@[gcongr]

中文:
定理 card
  结论: 是p群 (自然数.card G) G
  证明: fun g => ⟨1, by simp⟩

@[gcongr]
-/
protected theorem card : IsPGroup (Nat.card G) G :=
  fun g => ⟨1, by simp⟩

@[gcongr]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {q : Nat} (hpq : p ∣ q) (hp : IsPGroup p G)
  statement: IsPGroup q G
  proof: by
  rw [isPGroup_iff_orderOf_dvd_pow] at hp ⊢
exact fun g => (hp g).imp fun k hk => hk.trans pow_dvd_pow_of_dvd hpq k

中文:
定理 mono
  条件: {q : 自然数} (hpq : p ∣ q) (hp : 是p群 p G)
  结论: 是p群 q G
  证明: by
  rw [isPGroup_iff_orderOf_dvd_pow] at hp ⊢
exact fun g => (hp g).imp fun k hk => hk.trans pow_dvd_pow_of_dvd hpq k
-/
protected theorem mono {q : Nat} (hpq : p ∣ q) (hp : IsPGroup p G) : IsPGroup q G := by
  rw [isPGroup_iff_orderOf_dvd_pow] at hp ⊢
exact fun g => (hp g).imp fun k hk => hk.trans pow_dvd_pow_of_dvd hpq k

/--
theorem `of_pow` / 定理 `of_pow`

English:
theorem of_pow
  given: {n : Nat} (h : IsPGroup (p ^ n) G)
  statement: IsPGroup p G
  proof: fun g => (h g).imp' (n * ·) by simp [pow_mul]

中文:
定理 of_pow
  条件: {n : 自然数} (h : 是p群 (p ^ n) G)
  结论: 是p群 p G
  证明: fun g => (h g).imp' (n * ·) by simp [pow_mul]

Depends on / 依赖: pow_mul
-/
theorem of_pow {n : Nat} (h : IsPGroup (p ^ n) G) : IsPGroup p G :=
fun g => (h g).imp' (n * ·) by simp [pow_mul]

/--
theorem `iff_card` / 定理 `iff_card`

English:
theorem iff_card
  given: [Fact p.Prime] [Finite G]
  statement: IsPGroup p G ↔ exists n : Nat, Nat.card G = p ^ n
  proof: by
  simp_rw [isPGroup_iff_card_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_card_eq, _⟩ := iff_card

中文:
定理 iff_card
  条件: [Fact p.素] [有限 G]
  结论: 是p群 p G ↔ 存在 n : 自然数, 自然数.card G = p ^ n
  证明: by
  simp_rw [isPGroup_iff_card_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_card_eq, _⟩ := iff_card

Depends on / 依赖: Fact.out, Nat.dvd_prime_pow, dvd_prime_pow, isPGroup_iff_card_dvd_pow, le_rfl, simp_rw
-/
theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ exists n : Nat, Nat.card G = p ^ n := by
  simp_rw [isPGroup_iff_card_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_card_eq, _⟩ := iff_card

/--
theorem `_root_.isPGroup_iff_exists_orderOf_dvd_pow` / 定理 `_root_.isPGroup_iff_exists_orderOf_dvd_pow`

English:
theorem _root_.isPGroup_iff_exists_orderOf_dvd_pow
  given: [Finite G]
  proof: by
  refine isPGroup_iff_orderOf_dvd_pow.trans ⟨fun h => ?_, fun ⟨k, hk⟩ => fun g => ⟨k, hk g⟩⟩
  choose k hk using h
  have := Fintype.ofFinite G
  have ⟨g, _, hg⟩ := Finset.exists_max_image .univ k Finset.univ_nonempty
  refine ⟨k g, fun g' => ?_⟩
  grw [← Nat.pow_dvd_pow p <| hg g' <| Finset.mem_univ g']
  exact hk g'

中文:
定理 _root_.isPGroup_iff_存在_orderOf_dvd_pow
  条件: [有限 G]
  证明: by
  refine isPGroup_iff_orderOf_dvd_pow.trans ⟨fun h => ?_, fun ⟨k, hk⟩ => fun g => ⟨k, hk g⟩⟩
  choose k hk using h
  have := Fintype.ofFinite G
  have ⟨g, _, hg⟩ := Finset.exists_max_image .univ k Finset.univ_nonempty
  refine ⟨k g, fun g' => ?_⟩
  grw [← Nat.pow_dvd_pow p <| hg g' <| Finset.mem_univ g']
  exact hk g'

Depends on / 依赖: Finset, Finset.exists_max_image, Finset.mem_univ, Finset.univ_nonempty, Fintype, Fintype.ofFinite, Nat.pow_dvd_pow, exists_max_image, isPGroup_iff_orderOf_dvd_pow, isPGroup_iff_orderOf_dvd_pow.trans, mem_univ, ofFinite, pow_dvd_pow, univ_nonempty
-/
theorem _root_.isPGroup_iff_exists_orderOf_dvd_pow [Finite G] :
    IsPGroup p G ↔ exists k, forall g : G, orderOf g ∣ p ^ k := by
  refine isPGroup_iff_orderOf_dvd_pow.trans ⟨fun h => ?_, fun ⟨k, hk⟩ => fun g => ⟨k, hk g⟩⟩
  choose k hk using h
  have := Fintype.ofFinite G
  have ⟨g, _, hg⟩ := Finset.exists_max_image .univ k Finset.univ_nonempty
  refine ⟨k g, fun g' => ?_⟩
  grw [← Nat.pow_dvd_pow p <| hg g' <| Finset.mem_univ g']
  exact hk g'

/--
theorem `_root_.isPGroup_iff_exists_pow_pow_eq_one` / 定理 `_root_.isPGroup_iff_exists_pow_pow_eq_one`

English:
theorem _root_.isPGroup_iff_exists_pow_pow_eq_one
  given: [Finite G]
  proof: by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, orderOf_dvd_iff_pow_eq_one]

中文:
定理 _root_.isPGroup_iff_存在_pow_pow_eq_one
  条件: [有限 G]
  证明: by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, orderOf_dvd_iff_pow_eq_one]

Depends on / 依赖: isPGroup_iff_exists_orderOf_dvd_pow, orderOf_dvd_iff_pow_eq_one, simp_rw
-/
theorem _root_.isPGroup_iff_exists_pow_pow_eq_one [Finite G] :
    IsPGroup p G ↔ exists k, forall g : G, g ^ p ^ k = 1 := by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, orderOf_dvd_iff_pow_eq_one]

/--
theorem `of_exponent_dvd_pow` / 定理 `of_exponent_dvd_pow`

English:
theorem of_exponent_dvd_pow
  given: {n : Nat} (h : Monoid.exponent G ∣ p ^ n)
  statement: IsPGroup p G
  proof: fun g => ⟨n, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h g⟩

中文:
定理 of_exponent_dvd_pow
  条件: {n : 自然数} (h : 幺半群.exponent G ∣ p ^ n)
  结论: 是p群 p G
  证明: fun g => ⟨n, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h g⟩

Depends on / 依赖: Monoid, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp, exponent_dvd_iff_forall_pow_eq_one
-/
theorem of_exponent_dvd_pow {n : Nat} (h : Monoid.exponent G ∣ p ^ n) : IsPGroup p G :=
  fun g => ⟨n, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h g⟩

/--
theorem `_root_.isPGroup_iff_exponent_dvd_pow` / 定理 `_root_.isPGroup_iff_exponent_dvd_pow`

English:
theorem _root_.isPGroup_iff_exponent_dvd_pow
  given: [Finite G]
  proof: by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, Monoid.exponent_dvd]

alias ⟨exists_exponent_dvd_pow, _⟩ := isPGroup_iff_exponent_dvd_pow

中文:
定理 _root_.isPGroup_iff_exponent_dvd_pow
  条件: [有限 G]
  证明: by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, Monoid.exponent_dvd]

alias ⟨exists_exponent_dvd_pow, _⟩ := isPGroup_iff_exponent_dvd_pow

Depends on / 依赖: Monoid, Monoid.exponent_dvd, exponent_dvd, isPGroup_iff_exists_orderOf_dvd_pow, simp_rw
-/
theorem _root_.isPGroup_iff_exponent_dvd_pow [Finite G] :
    IsPGroup p G ↔ exists n, Monoid.exponent G ∣ p ^ n := by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, Monoid.exponent_dvd]

alias ⟨exists_exponent_dvd_pow, _⟩ := isPGroup_iff_exponent_dvd_pow

/--
theorem `_root_.isPGroup_iff_exponent_eq_pow` / 定理 `_root_.isPGroup_iff_exponent_eq_pow`

English:
theorem _root_.isPGroup_iff_exponent_eq_pow
  given: [Finite G] [Fact p.Prime]
  proof: by
  simp_rw [isPGroup_iff_exponent_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_exponent_eq_pow, _⟩ := isPGroup_iff_exponent_eq_pow

中文:
定理 _root_.isPGroup_iff_exponent_eq_pow
  条件: [有限 G] [Fact p.素]
  证明: by
  simp_rw [isPGroup_iff_exponent_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_exponent_eq_pow, _⟩ := isPGroup_iff_exponent_eq_pow

Depends on / 依赖: Fact.out, Nat.dvd_prime_pow, dvd_prime_pow, isPGroup_iff_exponent_dvd_pow, le_rfl, simp_rw
-/
theorem _root_.isPGroup_iff_exponent_eq_pow [Finite G] [Fact p.Prime] :
    IsPGroup p G ↔ exists n, Monoid.exponent G = p ^ n := by
  simp_rw [isPGroup_iff_exponent_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_exponent_eq_pow, _⟩ := isPGroup_iff_exponent_eq_pow

/--
theorem `_root_.isPGroup_iff_isPGroup_prod_primeFactors` / 定理 `_root_.isPGroup_iff_isPGroup_prod_primeFactors`

English:
theorem _root_.isPGroup_iff_isPGroup_prod_primeFactors
  given: (h : p != 0)
  proof: ⟨(.of_pow <| ·.mono <| p.dvd_prod_primeFactors_pow_self h), .mono p.prod_primeFactors_dvd⟩

中文:
定理 _root_.isPGroup_iff_isPGroup_prod_primeFactors
  条件: (h : p != 0)
  证明: ⟨(.of_pow <| ·.mono <| p.dvd_prod_primeFactors_pow_self h), .mono p.prod_primeFactors_dvd⟩

Depends on / 依赖: dvd_prod_primeFactors_pow_self, of_pow, p.dvd_prod_primeFactors_pow_self, p.prod_primeFactors_dvd, prod_primeFactors_dvd
-/
theorem _root_.isPGroup_iff_isPGroup_prod_primeFactors (h : p != 0) :
    IsPGroup p G ↔ IsPGroup (p.primeFactors.prod id) G :=
  ⟨(.of_pow <| ·.mono <| p.dvd_prod_primeFactors_pow_self h), .mono p.prod_primeFactors_dvd⟩

/--
theorem `_root_.isPGroup_iff_primeFactors_card_subset` / 定理 `_root_.isPGroup_iff_primeFactors_card_subset`

English:
theorem _root_.isPGroup_iff_primeFactors_card_subset
  given: [Finite G] (h : p != 0)
  proof: by
  refine isPGroup_iff_card_dvd_pow.trans ⟨fun ⟨n, hn⟩ => ?_, fun hG => ?_⟩
  · rcases eq_or_ne n 0 with (rfl | hn0)
    · simp_all
    grw [← Nat.primeFactors_pow p hn0, Nat.primeFactors_mono hn <| pow_ne_zero n h]
.trans ?_⟩ · refine ⟨Nat.card G, Nat.dvd_prod_primeFactors_pow_self NeZero.out
    grw [Finset.prod_dvd_prod_of_subset _ _ (·) hG, p.prod_primeFactors_dvd]

中文:
定理 _root_.isPGroup_iff_primeFactors_card_subset
  条件: [有限 G] (h : p != 0)
  证明: by
  refine isPGroup_iff_card_dvd_pow.trans ⟨fun ⟨n, hn⟩ => ?_, fun hG => ?_⟩
  · rcases eq_or_ne n 0 with (rfl | hn0)
    · simp_all
    grw [← Nat.primeFactors_pow p hn0, Nat.primeFactors_mono hn <| pow_ne_zero n h]
.trans ?_⟩ · refine ⟨Nat.card G, Nat.dvd_prod_primeFactors_pow_self NeZero.out
    grw [Finset.prod_dvd_prod_of_subset _ _ (·) hG, p.prod_primeFactors_dvd]

Depends on / 依赖: Finset, Finset.prod_dvd_prod_of_subset, Nat.card, Nat.dvd_prod_primeFactors_pow_self, Nat.primeFactors_mono, Nat.primeFactors_pow, NeZero, NeZero.out, dvd_prod_primeFactors_pow_self, eq_or_ne, isPGroup_iff_card_dvd_pow, isPGroup_iff_card_dvd_pow.trans, p.prod_primeFactors_dvd, pow_ne_zero, primeFactors_mono, primeFactors_pow, prod_dvd_prod_of_subset, prod_primeFactors_dvd
-/
theorem _root_.isPGroup_iff_primeFactors_card_subset [Finite G] (h : p != 0) :
    IsPGroup p G ↔ (Nat.card G).primeFactors subseteq p.primeFactors := by
  refine isPGroup_iff_card_dvd_pow.trans ⟨fun ⟨n, hn⟩ => ?_, fun hG => ?_⟩
  · rcases eq_or_ne n 0 with (rfl | hn0)
    · simp_all
    grw [← Nat.primeFactors_pow p hn0, Nat.primeFactors_mono hn <| pow_ne_zero n h]
.trans ?_⟩ · refine ⟨Nat.card G, Nat.dvd_prod_primeFactors_pow_self NeZero.out
    grw [Finset.prod_dvd_prod_of_subset _ _ (·) hG, p.prod_primeFactors_dvd]

section GIsPGroup

variable (hG : IsPGroup p G)
include hG

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: {H : Type*} [Group H] (ϕ : H ->* G) (hϕ : Function.Injective ϕ)
  proof: by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)

中文:
定理 of_injective
  条件: {H : 类型} [群 H] (ϕ : H ->* G) (hϕ : 函数.单射 ϕ)
  证明: by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)

Depends on / 依赖: IsPGroup, eq_iff, map_one, map_pow, simp_rw
-/
theorem of_injective {H : Type*} [Group H] (ϕ : H ->* G) (hϕ : Function.Injective ϕ) :
    IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)

/--
theorem `to_subgroup` / 定理 `to_subgroup`

English:
theorem to_subgroup
  given: (H : Subgroup G)
  statement: IsPGroup p H
  proof: hG.of_injective H.subtype Subtype.coe_injective

中文:
定理 to_subgroup
  条件: (H : 子群 G)
  结论: 是p群 p H
  证明: hG.of_injective H.subtype Subtype.coe_injective

Depends on / 依赖: H.subtype, Subtype, Subtype.coe_injective, coe_injective, hG.of_injective, of_injective, subtype
-/
theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.subtype Subtype.coe_injective

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: {H : Type*} [Group H] (ϕ : G ->* H) (hϕ : Function.Surjective ϕ)
  proof: by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg]; rw [← ϕ.map_pow]; rw [hk]; rw [ϕ.map_one]

中文:
定理 of_surjective
  条件: {H : 类型} [群 H] (ϕ : G ->* H) (hϕ : 函数.满射 ϕ)
  证明: by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg]; rw [← ϕ.map_pow]; rw [hk]; rw [ϕ.map_one]

Depends on / 依赖: Exists, Exists.elim, Exists.imp, map_one, map_pow
-/
theorem of_surjective {H : Type*} [Group H] (ϕ : G ->* H) (hϕ : Function.Surjective ϕ) :
    IsPGroup p H := by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg]; rw [← ϕ.map_pow]; rw [hk]; rw [ϕ.map_one]

/--
theorem `to_quotient` / 定理 `to_quotient`

English:
theorem to_quotient
  given: (H : Subgroup G) [H.Normal]
  statement: IsPGroup p (G ⧸ H)
  proof: hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective

中文:
定理 to_quotient
  条件: (H : 子群 G) [H.正规]
  结论: 是p群 p (G ⧸ H)
  证明: hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective

Depends on / 依赖: Quotient, Quotient.mk, QuotientGroup, QuotientGroup.mk, _surjective, hG.of_surjective, of_surjective
-/
theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: {H : Type*} [Group H] (ϕ : G ≃* H)
  statement: IsPGroup p H
  proof: hG.of_surjective ϕ.toMonoidHom ϕ.surjective

中文:
定理 of_equiv
  条件: {H : 类型} [群 H] (ϕ : G ≃* H)
  结论: 是p群 p H
  证明: hG.of_surjective ϕ.toMonoidHom ϕ.surjective

Depends on / 依赖: hG.of_surjective, of_surjective, surjective, toMonoidHom
-/
theorem of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.of_surjective ϕ.toMonoidHom ϕ.surjective

/--
theorem `isOfFinOrder` / 定理 `isOfFinOrder`

English:
theorem isOfFinOrder
  given: (hp : p != 0) (g : G)
  statement: IsOfFinOrder g
  proof: .elim (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, pow_ne_zero · hp |>.pos, ·⟩) hG g

中文:
定理 isOfFinOrder
  条件: (hp : p != 0) (g : G)
  结论: IsOfFinOrder g
  证明: .elim (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, pow_ne_zero · hp |>.pos, ·⟩) hG g

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr, pow_ne_zero
-/
theorem isOfFinOrder (hp : p != 0) (g : G) : IsOfFinOrder g :=
.elim (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, pow_ne_zero · hp |>.pos, ·⟩) hG g

/--
theorem `orderOf_coprime` / 定理 `orderOf_coprime`

English:
theorem orderOf_coprime
  given: {n : Nat} (hn : p.Coprime n) (g : G)
  statement: (orderOf g).Coprime n
  proof: let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)

中文:
定理 orderOf_coprime
  条件: {n : 自然数} (hn : p.Coprime n) (g : G)
  结论: (orderOf g).Coprime n
  证明: let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)

Depends on / 依赖: coprime_dvd_left, hn.pow_left, orderOf_dvd_of_pow_eq_one, pow_left
-/
theorem orderOf_coprime {n : Nat} (hn : p.Coprime n) (g : G) : (orderOf g).Coprime n :=
  let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)

/--
Definition of `powEquiv` / `powEquiv` 的定义

English:
definition powEquiv
  signature: {n : Nat} (hn : p.Coprime n)
  body: let h : forall g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
Subtype.ext_iff.1
        (powCoprime (h (g ^ n))).left_inv
⟨g, _, Subtype.ext_iff.1 (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
Subtype.ext_iff.1 (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }

@[simp]

中文:
定义 powEquiv
  签名: {n : 自然数} (hn : p.Coprime n)
  定义体: let h : forall g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
Subtype.ext_iff.1
        (powCoprime (h (g ^ n))).left_inv
⟨g, _, Subtype.ext_iff.1 (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
Subtype.ext_iff.1 (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }

@[simp]

Depends on / 依赖: Coprime, Nat.card, Nat.card_zpowers, Subgroup, Subgroup.mem_zpowers, Subgroup.zpowers, Subtype, Subtype.ext_iff, card_zpowers, ext_iff, hG.orderOf_coprime, invFun, left_inv, mem_zpowers, orderOf_coprime, powCoprime, right_inv, zpowers
-/
noncomputable def powEquiv {n : Nat} (hn : p.Coprime n) : G ≃ G :=
  let h : forall g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
Subtype.ext_iff.1
        (powCoprime (h (g ^ n))).left_inv
⟨g, _, Subtype.ext_iff.1 (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
Subtype.ext_iff.1 (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }

@[simp]
/--
theorem `powEquiv_apply` / 定理 `powEquiv_apply`

English:
theorem powEquiv_apply
  given: {n : Nat} (hn : p.Coprime n) (g : G)
  statement: hG.powEquiv hn g = g ^ n
  proof: rfl

@[simp]

中文:
定理 powEquiv_apply
  条件: {n : 自然数} (hn : p.Coprime n) (g : G)
  结论: hG.powEquiv hn g = g ^ n
  证明: rfl

@[simp]
-/
theorem powEquiv_apply {n : Nat} (hn : p.Coprime n) (g : G) : hG.powEquiv hn g = g ^ n :=
  rfl

@[simp]
/--
theorem `powEquiv_symm_apply` / 定理 `powEquiv_symm_apply`

English:
theorem powEquiv_symm_apply
  given: {n : Nat} (hn : p.Coprime n) (g : G)
  proof: by rw [← Nat.card_zpowers]; rfl

中文:
定理 powEquiv_symm_apply
  条件: {n : 自然数} (hn : p.Coprime n) (g : G)
  证明: by rw [← Nat.card_zpowers]; rfl

Depends on / 依赖: Nat.card_zpowers, card_zpowers
-/
theorem powEquiv_symm_apply {n : Nat} (hn : p.Coprime n) (g : G) :
    (hG.powEquiv hn).symm g = g ^ (orderOf g).gcdB n := by rw [← Nat.card_zpowers]; rfl

variable [hp : Fact p.Prime]

/--
Definition of `powEquiv'` / `powEquiv'` 的定义

English:
abbreviation powEquiv'
  signature: {n : Nat} (hn : ¬p ∣ n)
  body: powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)

中文:
缩写 powEquiv'
  签名: {n : 自然数} (hn : ¬p ∣ n)
  定义体: powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)

Depends on / 依赖: coprime_iff_not_dvd, hp.out.coprime_iff_not_dvd.mpr, powEquiv
-/
noncomputable abbrev powEquiv' {n : Nat} (hn : ¬p ∣ n) : G ≃ G :=
  powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)

/--
theorem `index` / 定理 `index`

English:
theorem index
  given: (H : Subgroup G) [H.FiniteIndex]
  statement: exists n : Nat, H.index = p ^ n
  proof: by
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normalCore)
  obtain ⟨k, _, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normalCore.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normalCore_le))
  exact ⟨k, hk2⟩

中文:
定理 index
  条件: (H : 子群 G) [H.FiniteIndex]
  结论: 存在 n : 自然数, H.index = p ^ n
  证明: by
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normalCore)
  obtain ⟨k, _, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normalCore.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normalCore_le))
  exact ⟨k, hk2⟩

Depends on / 依赖: H.normalCore, H.normalCore.index_eq_card.trans, H.normalCore_le, Nat.dvd_prime_pow, Subgroup, Subgroup.index_dvd_of_le, congr_arg, dvd_prime_pow, hG.to_quotient, hp.out, iff_card, iff_card.mp, index_dvd_of_le, index_eq_card, normalCore, normalCore_le, to_quotient
-/
theorem index (H : Subgroup G) [H.FiniteIndex] : exists n : Nat, H.index = p ^ n := by
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normalCore)
  obtain ⟨k, _, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normalCore.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normalCore_le))
  exact ⟨k, hk2⟩

/--
theorem `card_eq_or_dvd` / 定理 `card_eq_or_dvd`

English:
theorem card_eq_or_dvd
  statement: Nat.card G = 1 ∨ p ∣ Nat.card G
  proof: by
  cases finite_or_infinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [hn]
    rcases n with - | n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, by rw [pow_succ']⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩

中文:
定理 card_eq_or_dvd
  结论: 自然数.card G = 1 ∨ p ∣ 自然数.card G
  证明: by
  cases finite_or_infinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [hn]
    rcases n with - | n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, by rw [pow_succ']⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩

Depends on / 依赖: Nat.card_eq_zero_of_infinite, Or.inl, Or.inr, card_eq_zero_of_infinite, finite_or_infinite, iff_card, iff_card.mp, pow_succ
-/
theorem card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card G := by
  cases finite_or_infinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [hn]
    rcases n with - | n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, by rw [pow_succ']⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩

/--
theorem `nontrivial_iff_card` / 定理 `nontrivial_iff_card`

English:
theorem nontrivial_iff_card
  given: [Finite G]
  statement: Nontrivial G ↔ exists n > 0, Nat.card G = p ^ n
  proof: ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0]; rw [pow_zero] at hk; exact Finite.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨_, hk0, hk⟩ =>
Finite.one_lt_card_iff_nontrivial.1
      hk.symm ▸ one_lt_pow₀ (Fact.out (p := p.Prime)).one_lt (ne_of_gt hk0)⟩

中文:
定理 nontrivial_iff_card
  条件: [有限 G]
  结论: 非平凡 G ↔ 存在 n > 0, 自然数.card G = p ^ n
  证明: ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0]; rw [pow_zero] at hk; exact Finite.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨_, hk0, hk⟩ =>
Finite.one_lt_card_iff_nontrivial.1
      hk.symm ▸ one_lt_pow₀ (Fact.out (p := p.Prime)).one_lt (ne_of_gt hk0)⟩

Depends on / 依赖: Fact.out, Finite, Finite.one_lt_card.ne, Finite.one_lt_card_iff_nontrivial, Nat.pos_of_ne_zero, hk.symm, iff_card, ne_of_gt, one_lt, one_lt_card, one_lt_card_iff_nontrivial, p.Prime, pos_of_ne_zero, pow_zero
-/
theorem nontrivial_iff_card [Finite G] : Nontrivial G ↔ exists n > 0, Nat.card G = p ^ n :=
  ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0]; rw [pow_zero] at hk; exact Finite.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨_, hk0, hk⟩ =>
Finite.one_lt_card_iff_nontrivial.1
      hk.symm ▸ one_lt_pow₀ (Fact.out (p := p.Prime)).one_lt (ne_of_gt hk0)⟩

variable {α : Type*} [MulAction G α]

/--
theorem `card_orbit` / 定理 `card_orbit`

English:
theorem card_orbit
  given: (a : α) [Finite (orbit G a)]
  statement: exists n : Nat, Nat.card (orbit G a) = p ^ n
  proof: by
  let ϕ := orbitEquivQuotientStabilizer G a
  have := Finite.of_equiv (orbit G a) ϕ
  have := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [Nat.card_congr ϕ]
  exact hG.index (stabilizer G a)

中文:
定理 card_orbit
  条件: (a : α) [有限 (orbit G a)]
  结论: 存在 n : 自然数, 自然数.card (orbit G a) = p ^ n
  证明: by
  let ϕ := orbitEquivQuotientStabilizer G a
  have := Finite.of_equiv (orbit G a) ϕ
  have := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [Nat.card_congr ϕ]
  exact hG.index (stabilizer G a)

Depends on / 依赖: Finite, Finite.of_equiv, Nat.card_congr, card_congr, finiteIndex_of_finite_quotient, hG.index, of_equiv, orbitEquivQuotientStabilizer, stabilizer
-/
theorem card_orbit (a : α) [Finite (orbit G a)] : exists n : Nat, Nat.card (orbit G a) = p ^ n := by
  let ϕ := orbitEquivQuotientStabilizer G a
  have := Finite.of_equiv (orbit G a) ϕ
  have := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [Nat.card_congr ϕ]
  exact hG.index (stabilizer G a)

variable (α) [Finite α]

/--
theorem `card_modEq_card_fixedPoints` / 定理 `card_modEq_card_fixedPoints`

English:
theorem card_modEq_card_fixedPoints
  statement: Nat.card α ≡ Nat.card (fixedPoints G α) [MOD p]
  proof: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite (fixedPoints G α)
  rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  classical
    calc
      card α = card (Σ y : Quotient (orbitRel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
      _ = ∑ a : Quotient (orbitRel G α), card { x // Quotient.mk'' x = a } := card_sigma
      _ ≡ ∑ _a : fixedPoints G α, 1 [MOD p] := ?_
      _ = _ := by simp
    rw [← ZMod.natCast_eq_natCast_iff _ _ p]; rw [Nat.cast_sum]; rw [Nat.cast_sum]
    have key :
      forall x,
        card { y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq'']; congr
    refine
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
          rw [key]; rw [mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    rw [Nat.card_eq_fintype_card] at hk
    have : k = 0 := by
      contrapose! hb
      simp [key, hk, hb]
    exact
⟨⟨b, mem_fixedPoints_iff_card_orbit_eq_one.2 by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩

中文:
定理 card_modEq_card_fixedPoints
  结论: 自然数.card α ≡ 自然数.card (fixedPoints G α) [MOD p]
  证明: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite (fixedPoints G α)
  rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  classical
    calc
      card α = card (Σ y : Quotient (orbitRel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
      _ = ∑ a : Quotient (orbitRel G α), card { x // Quotient.mk'' x = a } := card_sigma
      _ ≡ ∑ _a : fixedPoints G α, 1 [MOD p] := ?_
      _ = _ := by simp
    rw [← ZMod.natCast_eq_natCast_iff _ _ p]; rw [Nat.cast_sum]; rw [Nat.cast_sum]
    have key :
      forall x,
        card { y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq'']; congr
    refine
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
          rw [key]; rw [mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    rw [Nat.card_eq_fintype_card] at hk
    have : k = 0 := by
      contrapose! hb
      simp [key, hk, hb]
    exact
⟨⟨b, mem_fixedPoints_iff_card_orbit_eq_one.2 by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩

Depends on / 依赖: Equiv.sigmaFiberEquiv, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.cast, Quotient, Quotient.mk, ZMod.natCast_eq_natCast_iff, card_congr, card_eq_fintype_card, card_sigma, classical, fixedPoints, natCast_eq_natCast_iff, ofFinite, orbitRel, sigmaFiberEquiv
-/
theorem card_modEq_card_fixedPoints : Nat.card α ≡ Nat.card (fixedPoints G α) [MOD p] := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite (fixedPoints G α)
  rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  classical
    calc
      card α = card (Σ y : Quotient (orbitRel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
      _ = ∑ a : Quotient (orbitRel G α), card { x // Quotient.mk'' x = a } := card_sigma
      _ ≡ ∑ _a : fixedPoints G α, 1 [MOD p] := ?_
      _ = _ := by simp
    rw [← ZMod.natCast_eq_natCast_iff _ _ p]; rw [Nat.cast_sum]; rw [Nat.cast_sum]
    have key :
      forall x,
        card { y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq'']; congr
    refine
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
          rw [key]; rw [mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    rw [Nat.card_eq_fintype_card] at hk
    have : k = 0 := by
      contrapose! hb
      simp [key, hk, hb]
    exact
⟨⟨b, mem_fixedPoints_iff_card_orbit_eq_one.2 by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩

/--
theorem `nonempty_fixed_point_of_prime_not_dvd_card` / 定理 `nonempty_fixed_point_of_prime_not_dvd_card`

English:
theorem nonempty_fixed_point_of_prime_not_dvd_card
  given: (α) [MulAction G α] (hpα : ¬p ∣ Nat.card α)
  proof: have : Finite α := Nat.finite_of_card_ne_zero (fun h => (h ▸ hpα) (dvd_zero p))
  @Set.Nonempty.of_subtype _ _
    (by
      rw [← Finite.card_pos_iff]; rw [pos_iff_ne_zero]
      contrapose hpα
      rw [← Nat.modEq_zero_iff_dvd]; rw [← hpα]
      exact hG.card_modEq_card_fixedPoints α)

中文:
定理 nonempty_fixed_point_of_prime_not_dvd_card
  条件: (α) [乘法作用 G α] (hpα : ¬p ∣ 自然数.card α)
  证明: have : Finite α := Nat.finite_of_card_ne_zero (fun h => (h ▸ hpα) (dvd_zero p))
  @Set.Nonempty.of_subtype _ _
    (by
      rw [← Finite.card_pos_iff]; rw [pos_iff_ne_zero]
      contrapose hpα
      rw [← Nat.modEq_zero_iff_dvd]; rw [← hpα]
      exact hG.card_modEq_card_fixedPoints α)

Depends on / 依赖: Finite, Finite.card_pos_iff, Nat.finite_of_card_ne_zero, Nat.modEq_zero_iff_dvd, Nonempty, Set.Nonempty.of_subtype, card_modEq_card_fixedPoints, card_pos_iff, contrapose, dvd_zero, finite_of_card_ne_zero, hG.card_modEq_card_fixedPoints, modEq_zero_iff_dvd, of_subtype, pos_iff_ne_zero
-/
theorem nonempty_fixed_point_of_prime_not_dvd_card (α) [MulAction G α] (hpα : ¬p ∣ Nat.card α) :
    (fixedPoints G α).Nonempty :=
  have : Finite α := Nat.finite_of_card_ne_zero (fun h => (h ▸ hpα) (dvd_zero p))
  @Set.Nonempty.of_subtype _ _
    (by
      rw [← Finite.card_pos_iff]; rw [pos_iff_ne_zero]
      contrapose hpα
      rw [← Nat.modEq_zero_iff_dvd]; rw [← hpα]
      exact hG.card_modEq_card_fixedPoints α)

/--
theorem `exists_fixed_point_of_prime_dvd_card_of_fixed_point` / 定理 `exists_fixed_point_of_prime_dvd_card_of_fixed_point`

English:
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point
  statement: (hpα : p ∣ Nat.card α) {a : α}
  proof: by
  have hpf : p ∣ Nat.card (fixedPoints G α) :=
    Nat.modEq_zero_iff_dvd.mp ((hG.card_modEq_card_fixedPoints α).symm.trans hpα.modEq_zero_nat)
  have hα : 1 < Nat.card (fixedPoints G α) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le (Nat.le_of_dvd (Finite.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  rw [Finite.one_lt_card_iff_nontrivial] at hα
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne (⟨a, ha⟩ : fixedPoints G α)
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩

中文:
定理 存在_fixed_point_of_prime_dvd_card_of_fixed_point
  结论: (hpα : p ∣ 自然数.card α) {a : α}
  证明: by
  have hpf : p ∣ Nat.card (fixedPoints G α) :=
    Nat.modEq_zero_iff_dvd.mp ((hG.card_modEq_card_fixedPoints α).symm.trans hpα.modEq_zero_nat)
  have hα : 1 < Nat.card (fixedPoints G α) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le (Nat.le_of_dvd (Finite.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  rw [Finite.one_lt_card_iff_nontrivial] at hα
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne (⟨a, ha⟩ : fixedPoints G α)
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩

Depends on / 依赖: Fact.out, Finite, Finite.card_pos_iff, Finite.one_lt_card_iff_nontrivial, Nat.card, Nat.le_of_dvd, Nat.modEq_zero_iff_dvd.mp, card_modEq_card_fixedPoints, card_pos_iff, exists_ne, fixedPoints, hG.card_modEq_card_fixedPoints, le_of_dvd, modEq_zero_iff_dvd, modEq_zero_nat, one_lt, one_lt.trans_le, one_lt_card_iff_nontrivial, p.Prime, simp_rw
-/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ Nat.card α) {a : α}
    (ha : a in fixedPoints G α) : exists b, b in fixedPoints G α ∧ a != b := by
  have hpf : p ∣ Nat.card (fixedPoints G α) :=
    Nat.modEq_zero_iff_dvd.mp ((hG.card_modEq_card_fixedPoints α).symm.trans hpα.modEq_zero_nat)
  have hα : 1 < Nat.card (fixedPoints G α) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le (Nat.le_of_dvd (Finite.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  rw [Finite.one_lt_card_iff_nontrivial] at hα
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne (⟨a, ha⟩ : fixedPoints G α)
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩

/--
theorem `center_nontrivial` / 定理 `center_nontrivial`

English:
theorem center_nontrivial
  given: [Nontrivial G] [Finite G]
  statement: Nontrivial (Subgroup.center G)
  proof: by
  have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixedPoints_eq_center] at this
  have dvd : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
  exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩

中文:
定理 center_nontrivial
  条件: [非平凡 G] [有限 G]
  结论: 非平凡 (子群.center G)
  证明: by
  have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixedPoints_eq_center] at this
  have dvd : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
  exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩

Depends on / 依赖: ConjAct, ConjAct.fixedPoints_eq_center, ConjAct.toConjAct, Nat.card, Subgroup, Subgroup.center, Subtype, Subtype.ext_iff.mp, center, dvd_pow_self, exists_fixed_point_of_prime_dvd_card_of_fixed_point, ext_iff, fixedPoints_eq_center, hG.nontrivial_iff_card.mp, hG.of_equiv, hn.symm, ne_of_gt, nontrivial_iff_card, of_equiv, one_mem
-/
theorem center_nontrivial [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center G) := by
  have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixedPoints_eq_center] at this
  have dvd : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
  exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩

/--
theorem `bot_lt_center` / 定理 `bot_lt_center`

English:
theorem bot_lt_center
  given: [Nontrivial G] [Finite G]
  statement: ⊥ < Subgroup.center G
  proof: by
  have := center_nontrivial hG
  exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Finite.one_lt_card)

中文:
定理 bot_lt_center
  条件: [非平凡 G] [有限 G]
  结论: ⊥ < 子群.center G
  证明: by
  have := center_nontrivial hG
  exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Finite.one_lt_card)

Depends on / 依赖: Finite, Finite.one_lt_card, Subgroup, Subgroup.center, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, center, center_nontrivial, one_lt_card, one_lt_card_iff_ne_bot, one_lt_card_iff_ne_bot.mp
-/
theorem bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G := by
  have := center_nontrivial hG
  exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Finite.one_lt_card)

end GIsPGroup

/--
theorem `to_le` / 定理 `to_le`

English:
theorem to_le
  given: {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <= K)
  statement: IsPGroup p H
  proof: hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (by
      change ((Subgroup.inclusion hHK) a : G) = (Subgroup.inclusion hHK) b
      apply Subtype.ext_iff.mp h)

中文:
定理 to_le
  条件: {H K : 子群 G} (hK : 是p群 p K) (hHK : H <= K)
  结论: 是p群 p H
  证明: hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (by
      change ((Subgroup.inclusion hHK) a : G) = (Subgroup.inclusion hHK) b
      apply Subtype.ext_iff.mp h)

Depends on / 依赖: Subgroup, Subgroup.inclusion, Subtype, Subtype.ext, Subtype.ext_iff.mp, ext_iff, hK.of_injective, inclusion, of_injective
-/
theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <= K) : IsPGroup p H :=
  hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (by
      change ((Subgroup.inclusion hHK) a : G) = (Subgroup.inclusion hHK) b
      apply Subtype.ext_iff.mp h)

/--
theorem `to_inf_left` / 定理 `to_inf_left`

English:
theorem to_inf_left
  given: {H K : Subgroup G} (hH : IsPGroup p H)
  statement: IsPGroup p (H ⊓ K : Subgroup G)
  proof: hH.to_le inf_le_left

中文:
定理 to_inf_left
  条件: {H K : 子群 G} (hH : 是p群 p H)
  结论: 是p群 p (H ⊓ K : 子群 G)
  证明: hH.to_le inf_le_left

Depends on / 依赖: hH.to_le, inf_le_left, to_le
-/
theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hH.to_le inf_le_left

/--
theorem `to_inf_right` / 定理 `to_inf_right`

English:
theorem to_inf_right
  given: {H K : Subgroup G} (hK : IsPGroup p K)
  statement: IsPGroup p (H ⊓ K : Subgroup G)
  proof: hK.to_le inf_le_right

中文:
定理 to_inf_right
  条件: {H K : 子群 G} (hK : 是p群 p K)
  结论: 是p群 p (H ⊓ K : 子群 G)
  证明: hK.to_le inf_le_right

Depends on / 依赖: hK.to_le, inf_le_right, to_le
-/
theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hK.to_le inf_le_right

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : G ->* K)
  proof: by
  rw [← H.range_subtype]; rw [MonoidHom.map_range]
  exact hH.of_surjective (ϕ.domRestrict H).rangeRestrict (ϕ.domRestrict H).rangeRestrict_surjective

中文:
定理 map
  条件: {H : 子群 G} (hH : 是p群 p H) {K : 类型} [群 K] (ϕ : G ->* K)
  证明: by
  rw [← H.range_subtype]; rw [MonoidHom.map_range]
  exact hH.of_surjective (ϕ.domRestrict H).rangeRestrict (ϕ.domRestrict H).rangeRestrict_surjective

Depends on / 依赖: H.range_subtype, MonoidHom, MonoidHom.map_range, domRestrict, hH.of_surjective, map_range, of_surjective, rangeRestrict, rangeRestrict_surjective, range_subtype
-/
theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : G ->* K) :
    IsPGroup p (H.map ϕ) := by
  rw [← H.range_subtype]; rw [MonoidHom.map_range]
  exact hH.of_surjective (ϕ.domRestrict H).rangeRestrict (ϕ.domRestrict H).rangeRestrict_surjective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comap_of_ker_isPGroup` / 定理 `comap_of_ker_isPGroup`

English:
theorem comap_of_ker_isPGroup
  statement: {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K]
  proof: by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff]; rw [H.coe_pow]; rw [Subtype.coe_mk]; rw [← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rw [Subtype.ext_iff]; rw [ϕ.ker.coe_pow]; rw [Subtype.coe_mk]; rw [← pow_mul]; rw [← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩

中文:
定理 comap_of_ker_isPGroup
  结论: {H : 子群 G} (hH : 是p群 p H) {K : 类型} [群 K]
  证明: by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff]; rw [H.coe_pow]; rw [Subtype.coe_mk]; rw [← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rw [Subtype.ext_iff]; rw [ϕ.ker.coe_pow]; rw [Subtype.coe_mk]; rw [← pow_mul]; rw [← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩

Depends on / 依赖: H.coe_pow, H.comap, Subtype, Subtype.coe_mk, Subtype.ext_iff, coe_mk, coe_pow, ext_iff, ker.coe_pow, map_pow, pow_add, pow_mul
-/
theorem comap_of_ker_isPGroup {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K]
    (ϕ : K ->* G) (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) := by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff]; rw [H.coe_pow]; rw [Subtype.coe_mk]; rw [← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rw [Subtype.ext_iff]; rw [ϕ.ker.coe_pow]; rw [Subtype.coe_mk]; rw [← pow_mul]; rw [← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩

/--
theorem `ker_isPGroup_of_injective` / 定理 `ker_isPGroup_of_injective`

English:
theorem ker_isPGroup_of_injective
  given: {K : Type*} [Group K] {ϕ : K ->* G} (hϕ : Function.Injective ϕ)
  proof: (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot hϕ)).mpr IsPGroup.of_bot

中文:
定理 ker_isPGroup_of_injective
  条件: {K : 类型} [群 K] {ϕ : K ->* G} (hϕ : 函数.单射 ϕ)
  证明: (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot hϕ)).mpr IsPGroup.of_bot

Depends on / 依赖: IsPGroup, IsPGroup.of_bot, Subgroup, congr_arg, ker_eq_bot, of_bot
-/
theorem ker_isPGroup_of_injective {K : Type*} [Group K] {ϕ : K ->* G} (hϕ : Function.Injective ϕ) :
    IsPGroup p ϕ.ker :=
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot hϕ)).mpr IsPGroup.of_bot

/--
theorem `comap_of_injective` / 定理 `comap_of_injective`

English:
theorem comap_of_injective
  statement: {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K ->* G)
  proof: hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)

中文:
定理 comap_of_injective
  结论: {H : 子群 G} (hH : 是p群 p H) {K : 类型} [群 K] (ϕ : K ->* G)
  证明: hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)

Depends on / 依赖: comap_of_ker_isPGroup, hH.comap_of_ker_isPGroup, ker_isPGroup_of_injective
-/
theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K ->* G)
    (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)

/--
theorem `comap_subtype` / 定理 `comap_subtype`

English:
theorem comap_subtype
  given: {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G}
  proof: hH.comap_of_injective K.subtype Subtype.coe_injective

中文:
定理 comap_subtype
  条件: {H : 子群 G} (hH : 是p群 p H) {K : 子群 G}
  证明: hH.comap_of_injective K.subtype Subtype.coe_injective

Depends on / 依赖: K.subtype, Subtype, Subtype.coe_injective, coe_injective, comap_of_injective, hH.comap_of_injective, subtype
-/
theorem comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} :
    IsPGroup p (H.comap K.subtype) :=
  hH.comap_of_injective K.subtype Subtype.coe_injective

/--
theorem `to_sup_of_normal_right` / 定理 `to_sup_of_normal_right`

English:
theorem to_sup_of_normal_right
  statement: {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
  proof: by
  rw [← QuotientGroup.ker_mk' K]; rw [← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']

中文:
定理 to_sup_of_normal_right
  结论: {H K : 子群 G} (hH : 是p群 p H) (hK : 是p群 p K)
  证明: by
  rw [← QuotientGroup.ker_mk' K]; rw [← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']

Depends on / 依赖: QuotientGroup, QuotientGroup.ker_mk, QuotientGroup.mk, Subgroup, Subgroup.comap_map_eq, comap_map_eq, comap_of_ker_isPGroup, hH.map, ker_mk
-/
theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [K.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := by
  rw [← QuotientGroup.ker_mk' K]; rw [← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']

/--
theorem `to_sup_of_normal_left` / 定理 `to_sup_of_normal_left`

English:
theorem to_sup_of_normal_left
  statement: {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
  proof: sup_comm H K ▸ to_sup_of_normal_right hK hH

中文:
定理 to_sup_of_normal_left
  结论: {H K : 子群 G} (hH : 是p群 p H) (hK : 是p群 p K)
  证明: sup_comm H K ▸ to_sup_of_normal_right hK hH

Depends on / 依赖: sup_comm, to_sup_of_normal_right
-/
theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [H.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := sup_comm H K ▸ to_sup_of_normal_right hK hH

/--
theorem `to_sup_of_normal_right'` / 定理 `to_sup_of_normal_right'`

English:
theorem to_sup_of_normal_right'
  statement: {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
  proof: let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup (Subgroup.normalizer K) => IsPGroup p H)
            ((Subgroup.subgroupOf_sup hHK Subgroup.le_normalizer).symm)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))

中文:
定理 to_sup_of_normal_right'
  结论: {H K : 子群 G} (hH : 是p群 p H) (hK : 是p群 p K)
  证明: let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup (Subgroup.normalizer K) => IsPGroup p H)
            ((Subgroup.subgroupOf_sup hHK Subgroup.le_normalizer).symm)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))

Depends on / 依赖: IsPGroup, Subgroup, Subgroup.le_normalizer, Subgroup.normalizer, Subgroup.subgroupOfEquivOfLe, Subgroup.subgroupOf_sup, congr_arg, hH.of_equiv, hK.of_equiv, le_normalizer, normalizer, of_equiv, subgroupOfEquivOfLe, subgroupOf_sup, sup_le, to_sup_of_normal_right
-/
theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : H <= Subgroup.normalizer K) : IsPGroup p (H ⊔ K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup (Subgroup.normalizer K) => IsPGroup p H)
            ((Subgroup.subgroupOf_sup hHK Subgroup.le_normalizer).symm)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))

/--
theorem `to_sup_of_normal_left'` / 定理 `to_sup_of_normal_left'`

English:
theorem to_sup_of_normal_left'
  statement: {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
  proof: sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK

中文:
定理 to_sup_of_normal_left'
  结论: {H K : 子群 G} (hH : 是p群 p H) (hK : 是p群 p K)
  证明: sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK

Depends on / 依赖: sup_comm, to_sup_of_normal_right
-/
theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : K <= Subgroup.normalizer H) : IsPGroup p (H ⊔ K : Subgroup G) :=
  sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK

/--
theorem `coprime_card_of_ne` / 定理 `coprime_card_of_ne`

English:
theorem coprime_card_of_ne
  statement: {G₂ : Type*} [Group G₂] (p₁ p₂ : Nat) [hp₁ : Fact p₁.Prime]
  proof: by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne

中文:
定理 coprime_card_of_ne
  结论: {G₂ : 类型} [群 G₂] (p₁ p₂ : 自然数) [hp₁ : Fact p₁.素]
  证明: by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne

Depends on / 依赖: Nat.coprime_pow_primes, coprime_pow_primes, iff_card, iff_card.mp
-/
theorem coprime_card_of_ne {G₂ : Type*} [Group G₂] (p₁ p₂ : Nat) [hp₁ : Fact p₁.Prime]
    [hp₂ : Fact p₂.Prime] (hne : p₁ != p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Finite H₁]
    [Finite H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) :
    Nat.Coprime (Nat.card H₁) (Nat.card H₂) := by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne

/--
theorem `disjoint_of_coprime` / 定理 `disjoint_of_coprime`

English:
theorem disjoint_of_coprime
  statement: {p₁ p₂ : Nat} {H₁ H₂ : Subgroup G} (hH₁ : IsPGroup p₁ H₁)
  proof: by
  refine Subgroup.disjoint_def.mpr fun {g} hg₁ hg₂ => ?_
  have ⟨k₁, hk₁⟩ := hH₁ ⟨g, hg₁⟩
  have hg₁ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₁
  have ⟨k₂, hk₂⟩ := hH₂ ⟨g, hg₂⟩
  have hg₂ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₂
exact orderOf_eq_one_iff.mp Nat.eq_one_of_dvd_coprimes (h.pow k₁ k₂) hg₁ hg₂

中文:
定理 disjoint_of_coprime
  结论: {p₁ p₂ : 自然数} {H₁ H₂ : 子群 G} (hH₁ : 是p群 p₁ H₁)
  证明: by
  refine Subgroup.disjoint_def.mpr fun {g} hg₁ hg₂ => ?_
  have ⟨k₁, hk₁⟩ := hH₁ ⟨g, hg₁⟩
  have hg₁ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₁
  have ⟨k₂, hk₂⟩ := hH₂ ⟨g, hg₂⟩
  have hg₂ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₂
exact orderOf_eq_one_iff.mp Nat.eq_one_of_dvd_coprimes (h.pow k₁ k₂) hg₁ hg₂

Depends on / 依赖: Nat.eq_one_of_dvd_coprimes, Subgroup, Subgroup.disjoint_def.mpr, Subgroup.orderOf_mk, disjoint_def, eq_one_of_dvd_coprimes, h.pow, orderOf_dvd_of_pow_eq_one, orderOf_eq_one_iff, orderOf_eq_one_iff.mp, orderOf_mk
-/
theorem disjoint_of_coprime {p₁ p₂ : Nat} {H₁ H₂ : Subgroup G} (hH₁ : IsPGroup p₁ H₁)
    (hH₂ : IsPGroup p₂ H₂) (h : p₁.Coprime p₂) : Disjoint H₁ H₂ := by
  refine Subgroup.disjoint_def.mpr fun {g} hg₁ hg₂ => ?_
  have ⟨k₁, hk₁⟩ := hH₁ ⟨g, hg₁⟩
  have hg₁ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₁
  have ⟨k₂, hk₂⟩ := hH₂ ⟨g, hg₂⟩
  have hg₂ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₂
exact orderOf_eq_one_iff.mp Nat.eq_one_of_dvd_coprimes (h.pow k₁ k₂) hg₁ hg₂

/--
theorem `disjoint_of_ne` / 定理 `disjoint_of_ne`

English:
theorem disjoint_of_ne
  statement: (p₁ p₂ : Nat) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ != p₂)
  proof: disjoint_of_coprime hH₁ hH₂ .mpr hne Nat.coprime_primes hp₁.elim hp₂.elim

中文:
定理 disjoint_of_ne
  结论: (p₁ p₂ : 自然数) [hp₁ : Fact p₁.素] [hp₂ : Fact p₂.素] (hne : p₁ != p₂)
  证明: disjoint_of_coprime hH₁ hH₂ .mpr hne Nat.coprime_primes hp₁.elim hp₂.elim

Depends on / 依赖: Nat.coprime_primes, coprime_primes, disjoint_of_coprime
-/
theorem disjoint_of_ne (p₁ p₂ : Nat) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ != p₂)
    (H₁ H₂ : Subgroup G) (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Disjoint H₁ H₂ :=
disjoint_of_coprime hH₁ hH₂ .mpr hne Nat.coprime_primes hp₁.elim hp₂.elim

/--
theorem `le_or_disjoint_of_coprime` / 定理 `le_or_disjoint_of_coprime`

English:
theorem le_or_disjoint_of_coprime
  statement: [hp : Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
  proof: by
  by_cases h1 : Nat.card H = 0
  · rw [h1, Nat.coprime_zero_left, Subgroup.index_eq_one] at h_cop
    rw [h_cop]
    exact Or.inl le_top
  by_cases h2 : H.index = 0
  · rw [h2, Nat.coprime_zero_right, Subgroup.card_eq_one] at h_cop
    rw [h_cop]
    exact Or.inr disjoint_bot_left
  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← H.card_mul_index]
    exact mul_ne_zero h1 h2
  have h3 : (Nat.card H).Coprime (Nat.card P) ∨ H.index.Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    refine hk ▸ Or.imp hp.out.coprime_pow_of_not_dvd hp.out.coprime_pow_of_not_dvd ?_
    contrapose! h_cop
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, h_cop⟩
  refine h3.symm.imp (fun h4 => ?_) (fun h4 => ?_)
  · rw [← Subgroup.relIndex_eq_one]
    exact Nat.eq_one_of_dvd_coprimes h4 (H.relIndex_dvd_index_of_normal P)
      (Subgroup.relIndex_dvd_card H P)
  · exact Subgroup.disjoint_of_coprime_natCard h4

中文:
定理 le_or_disjoint_of_coprime
  结论: [hp : Fact p.素] {P : 子群 G} (hP : 是p群 p P)
  证明: by
  by_cases h1 : Nat.card H = 0
  · rw [h1, Nat.coprime_zero_left, Subgroup.index_eq_one] at h_cop
    rw [h_cop]
    exact Or.inl le_top
  by_cases h2 : H.index = 0
  · rw [h2, Nat.coprime_zero_right, Subgroup.card_eq_one] at h_cop
    rw [h_cop]
    exact Or.inr disjoint_bot_left
  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← H.card_mul_index]
    exact mul_ne_zero h1 h2
  have h3 : (Nat.card H).Coprime (Nat.card P) ∨ H.index.Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    refine hk ▸ Or.imp hp.out.coprime_pow_of_not_dvd hp.out.coprime_pow_of_not_dvd ?_
    contrapose! h_cop
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, h_cop⟩
  refine h3.symm.imp (fun h4 => ?_) (fun h4 => ?_)
  · rw [← Subgroup.relIndex_eq_one]
    exact Nat.eq_one_of_dvd_coprimes h4 (H.relIndex_dvd_index_of_normal P)
      (Subgroup.relIndex_dvd_card H P)
  · exact Subgroup.disjoint_of_coprime_natCard h4

Depends on / 依赖: Coprime, Finite, H.card_mul_index, H.index, H.index.Coprime, Nat.card, Nat.coprime_zero_left, Nat.coprime_zero_right, Nat.finite_of_card_ne_zero, Or.imp, Or.inl, Or.inr, Subgroup, Subgroup.card_eq_one, Subgroup.index_eq_one, card_eq_one, card_mul_index, coprime_zero_left, coprime_zero_right, disjoint_bot_left
-/
theorem le_or_disjoint_of_coprime [hp : Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    {H : Subgroup G} [H.Normal] (h_cop : (Nat.card H).Coprime H.index) :
    P <= H ∨ Disjoint H P := by
  by_cases h1 : Nat.card H = 0
  · rw [h1, Nat.coprime_zero_left, Subgroup.index_eq_one] at h_cop
    rw [h_cop]
    exact Or.inl le_top
  by_cases h2 : H.index = 0
  · rw [h2, Nat.coprime_zero_right, Subgroup.card_eq_one] at h_cop
    rw [h_cop]
    exact Or.inr disjoint_bot_left
  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← H.card_mul_index]
    exact mul_ne_zero h1 h2
  have h3 : (Nat.card H).Coprime (Nat.card P) ∨ H.index.Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    refine hk ▸ Or.imp hp.out.coprime_pow_of_not_dvd hp.out.coprime_pow_of_not_dvd ?_
    contrapose! h_cop
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, h_cop⟩
  refine h3.symm.imp (fun h4 => ?_) (fun h4 => ?_)
  · rw [← Subgroup.relIndex_eq_one]
    exact Nat.eq_one_of_dvd_coprimes h4 (H.relIndex_dvd_index_of_normal P)
      (Subgroup.relIndex_dvd_card H P)
  · exact Subgroup.disjoint_of_coprime_natCard h4

section P2comm

variable [Fact p.Prime] {n : Nat}

open Subgroup

/--
theorem `card_center_eq_prime_pow` / 定理 `card_center_eq_prime_pow`

English:
theorem card_center_eq_prime_pow
  given: (hGpn : Nat.card G = p ^ n) (hn : 0 < n)
  proof: by
  have : Finite G := Nat.finite_of_card_ne_zero (hGpn ▸ pow_ne_zero n (NeZero.ne p))
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  have : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))

中文:
定理 card_center_eq_prime_pow
  条件: (hGpn : 自然数.card G = p ^ n) (hn : 0 < n)
  证明: by
  have : Finite G := Nat.finite_of_card_ne_zero (hGpn ▸ pow_ne_zero n (NeZero.ne p))
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  have : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))

Depends on / 依赖: Finite, Nat.finite_of_card_ne_zero, NeZero, NeZero.ne, Nontrivial, center, center_nontrivial, finite_of_card_ne_zero, iff_card, nontrivial_iff_card, of_card, pow_ne_zero, to_subgroup
-/
theorem card_center_eq_prime_pow (hGpn : Nat.card G = p ^ n) (hn : 0 < n) :
    exists k > 0, Nat.card (center G) = p ^ k := by
  have : Finite G := Nat.finite_of_card_ne_zero (hGpn ▸ pow_ne_zero n (NeZero.ne p))
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  have : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))

/--
theorem `cyclic_center_quotient_of_card_eq_prime_sq` / 定理 `cyclic_center_quotient_of_card_eq_prime_sq`

English:
theorem cyclic_center_quotient_of_card_eq_prime_sq
  given: (hG : Nat.card G = p ^ 2)
  proof: by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [← mul_dvd_mul_iff_left (NeZero.ne p)]; rw [← sq]; rw [← hG]; rw [← (center G).card_mul_index]
  apply mul_dvd_mul_right
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
  rw [hk]
  exact dvd_pow_self p hk0.ne'

中文:
定理 cyclic_center_quotient_of_card_eq_prime_sq
  条件: (hG : 自然数.card G = p ^ 2)
  证明: by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [← mul_dvd_mul_iff_left (NeZero.ne p)]; rw [← sq]; rw [← hG]; rw [← (center G).card_mul_index]
  apply mul_dvd_mul_right
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
  rw [hk]
  exact dvd_pow_self p hk0.ne'

Depends on / 依赖: NeZero, NeZero.ne, card_center_eq_prime_pow, card_mul_index, center, dvd_pow_self, hk0.ne, isCyclic_of_card_dvd_prime, mul_dvd_mul_iff_left, mul_dvd_mul_right, zero_lt_two
-/
theorem cyclic_center_quotient_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) :
    IsCyclic (G ⧸ center G) := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [← mul_dvd_mul_iff_left (NeZero.ne p)]; rw [← sq]; rw [← hG]; rw [← (center G).card_mul_index]
  apply mul_dvd_mul_right
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
  rw [hk]
  exact dvd_pow_self p hk0.ne'

/--
theorem `isMulCommutative_of_card_eq_prime_sq` / 定理 `isMulCommutative_of_card_eq_prime_sq`

English:
theorem isMulCommutative_of_card_eq_prime_sq
  given: (hG : Nat.card G = p ^ 2)
  statement: IsMulCommutative G
  proof: let := cyclic_center_quotient_of_card_eq_prime_sq hG
  isMulCommutative_of_isCyclic_quotient_center_self G

中文:
定理 isMulCommutative_of_card_eq_prime_sq
  条件: (hG : 自然数.card G = p ^ 2)
  结论: 是MulCommutative G
  证明: let := cyclic_center_quotient_of_card_eq_prime_sq hG
  isMulCommutative_of_isCyclic_quotient_center_self G

Depends on / 依赖: cyclic_center_quotient_of_card_eq_prime_sq, isMulCommutative_of_isCyclic_quotient_center_self
-/
theorem isMulCommutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsMulCommutative G :=
  let := cyclic_center_quotient_of_card_eq_prime_sq hG
  isMulCommutative_of_isCyclic_quotient_center_self G

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
@[instance_reducible]
/--
Definition of `commGroupOfCardEqPrimeSq` / `commGroupOfCardEqPrimeSq` 的定义

English:
definition commGroupOfCardEqPrimeSq
  signature: (hG : Nat.card G = p ^ 2)
  body: let := cyclic_center_quotient_of_card_eq_prime_sq hG
  commGroupOfCyclicCenterQuotient _ (QuotientGroup.ker_mk' <| center G).le

@[deprecated isMulCommutative_of_card_eq_prime_sq (since := "2026-05-26")]

中文:
定义 commGroupOfCardEqPrimeSq
  签名: (hG : 自然数.card G = p ^ 2)
  定义体: let := cyclic_center_quotient_of_card_eq_prime_sq hG
  commGroupOfCyclicCenterQuotient _ (QuotientGroup.ker_mk' <| center G).le

@[deprecated isMulCommutative_of_card_eq_prime_sq (since := "2026-05-26")]

Depends on / 依赖: QuotientGroup, QuotientGroup.ker_mk, center, commGroupOfCyclicCenterQuotient, cyclic_center_quotient_of_card_eq_prime_sq, ker_mk
-/
def commGroupOfCardEqPrimeSq (hG : Nat.card G = p ^ 2) : CommGroup G :=
  let := cyclic_center_quotient_of_card_eq_prime_sq hG
  commGroupOfCyclicCenterQuotient _ (QuotientGroup.ker_mk' <| center G).le

@[deprecated isMulCommutative_of_card_eq_prime_sq (since := "2026-05-26")]
/--
theorem `commutative_of_card_eq_prime_sq` / 定理 `commutative_of_card_eq_prime_sq`

English:
theorem commutative_of_card_eq_prime_sq
  given: (hG : Nat.card G = p ^ 2)
  statement: forall a b : G, a * b = b * a
  proof: .is_comm.comm isMulCommutative_of_card_eq_prime_sq hG

中文:
定理 commutative_of_card_eq_prime_sq
  条件: (hG : 自然数.card G = p ^ 2)
  结论: 对任意 a b : G, a * b = b * a
  证明: .is_comm.comm isMulCommutative_of_card_eq_prime_sq hG

Depends on / 依赖: isMulCommutative_of_card_eq_prime_sq, is_comm, is_comm.comm
-/
theorem commutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : forall a b : G, a * b = b * a :=
.is_comm.comm isMulCommutative_of_card_eq_prime_sq hG

end P2comm

end IsPGroup

namespace ZModModule
variable {n : Nat} {G : Type*} [AddCommGroup G] [Module (ZMod n) G]

/--
lemma `isPGroup_multiplicative` / 引理 `isPGroup_multiplicative`

English:
lemma isPGroup_multiplicative
  statement: IsPGroup n (Multiplicative G)
  proof: by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ => ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

中文:
引理 isPGroup_multiplicative
  结论: 是p群 n (Multiplicative G)
  证明: by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ => ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

Depends on / 依赖: IsPGroup, Multiplicative, Multiplicative.forall, ZModModule, ZModModule.char_nsmul_eq_zero, char_nsmul_eq_zero, ofAdd_nsmul
-/
lemma isPGroup_multiplicative : IsPGroup n (Multiplicative G) := by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ => ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

end ZModModule
