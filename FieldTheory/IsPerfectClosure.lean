/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PerfectClosure

/-!

# `IsPerfectClosure` predicate

This file contains `IsPerfectClosure` which asserts that `L` is a perfect closure of `K` under a
ring homomorphism `i : K →+* L`, as well as its basic properties.

## Main definitions

- `pNilradical`: given a natural number `p`, the `p`-nilradical of a ring is defined to be the
  nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
  (`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
  `x ^ p ^ n = 0` for some `n` (`mem_pNilradical`).

- `IsPRadical`: a ring homomorphism `i : K →+* L` of characteristic `p` rings is called `p`-radical,
  if or any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`,
  and the kernel of `i` is contained in the `p`-nilradical of `K`.
  A generalization of purely inseparable extension for fields.

- `IsPerfectClosure`: if `i : K →+* L` is `p`-radical ring homomorphism, then it makes `L` a
  perfect closure of `K`, if `L` is perfect.

  Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
  that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
  `PerfectRing` which has `ExpChar` as a prerequisite.

- `PerfectRing.lift`: if a `p`-radical ring homomorphism `K →+* L` is given, `M` is a perfect ring,
  then any ring homomorphism `K →+* M` can be lifted to `L →+* M`.
  This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`.

- `PerfectRing.liftEquiv`: `K →+* M` is in one-to-one correspondence with `L →+* M`,
  given by `PerfectRing.lift`. This generalizes `PerfectClosure.lift`.

- `IsPerfectClosure.equiv`: perfect closures of a ring are isomorphic.

## Main results

- `IsPRadical.trans`: composition of `p`-radical ring homomorphisms is also `p`-radical.

- `PerfectClosure.isPRadical`: the absolute perfect closure `PerfectClosure` is a `p`-radical
  extension over the base ring, in particular, it is a perfect closure of the base ring.

- `IsPRadical.isPurelyInseparable`, `IsPurelyInseparable.isPRadical`: `p`-radical and
  purely inseparable are equivalent for fields.

- The (relative) perfect closure `perfectClosure` is a perfect closure
  (inferred from `IsPurelyInseparable.isPRadical` automatically by Lean).

## Tags

perfect ring, perfect closure, purely inseparable

-/

@[expose] public section

open Module Polynomial IntermediateField Field

noncomputable section

/--
Definition of `pNilradical` / `pNilradical` 的定义

English:
definition pNilradical
  signature: (R : Type*) [CommSemiring R] (p : Nat)
  body: if 1 < p then nilradical R else ⊥

中文:
定义 pNilradical
  签名: (R : 类型) [CommSemiring R] (p : 自然数)
  定义体: if 1 < p then nilradical R else ⊥

Depends on / 依赖: nilradical
-/
def pNilradical (R : Type*) [CommSemiring R] (p : Nat) : Ideal R := if 1 < p then nilradical R else ⊥

/--
theorem `pNilradical_le_nilradical` / 定理 `pNilradical_le_nilradical`

English:
theorem pNilradical_le_nilradical
  given: {R : Type*} [CommSemiring R] {p : Nat}
  proof: by
  by_cases hp : 1 < p
  · rw [pNilradical, if_pos hp]
  simp_rw [pNilradical, if_neg hp, bot_le]

中文:
定理 pNilradical_le_nilradical
  条件: {R : 类型} [CommSemiring R] {p : 自然数}
  证明: by
  by_cases hp : 1 < p
  · rw [pNilradical, if_pos hp]
  simp_rw [pNilradical, if_neg hp, bot_le]

Depends on / 依赖: bot_le, if_neg, if_pos, pNilradical, simp_rw
-/
theorem pNilradical_le_nilradical {R : Type*} [CommSemiring R] {p : Nat} :
    pNilradical R p <= nilradical R := by
  by_cases hp : 1 < p
  · rw [pNilradical, if_pos hp]
  simp_rw [pNilradical, if_neg hp, bot_le]

/--
theorem `pNilradical_eq_nilradical` / 定理 `pNilradical_eq_nilradical`

English:
theorem pNilradical_eq_nilradical
  given: {R : Type*} [CommSemiring R] {p : Nat} (hp : 1 < p)
  proof: by rw [pNilradical, if_pos hp]

中文:
定理 pNilradical_eq_nilradical
  条件: {R : 类型} [CommSemiring R] {p : 自然数} (hp : 1 < p)
  证明: by rw [pNilradical, if_pos hp]

Depends on / 依赖: if_pos, pNilradical
-/
theorem pNilradical_eq_nilradical {R : Type*} [CommSemiring R] {p : Nat} (hp : 1 < p) :
    pNilradical R p = nilradical R := by rw [pNilradical, if_pos hp]

/--
theorem `pNilradical_eq_bot` / 定理 `pNilradical_eq_bot`

English:
theorem pNilradical_eq_bot
  given: {R : Type*} [CommSemiring R] {p : Nat} (hp : ¬ 1 < p)
  proof: by rw [pNilradical, if_neg hp]

中文:
定理 pNilradical_eq_bot
  条件: {R : 类型} [CommSemiring R] {p : 自然数} (hp : ¬ 1 < p)
  证明: by rw [pNilradical, if_neg hp]

Depends on / 依赖: if_neg, pNilradical
-/
theorem pNilradical_eq_bot {R : Type*} [CommSemiring R] {p : Nat} (hp : ¬ 1 < p) :
    pNilradical R p = ⊥ := by rw [pNilradical, if_neg hp]

/--
theorem `pNilradical_eq_bot'` / 定理 `pNilradical_eq_bot'`

English:
theorem pNilradical_eq_bot'
  given: {R : Type*} [CommSemiring R] {p : Nat} (hp : p <= 1)
  proof: pNilradical_eq_bot (not_lt.2 hp)

中文:
定理 pNilradical_eq_bot'
  条件: {R : 类型} [CommSemiring R] {p : 自然数} (hp : p <= 1)
  证明: pNilradical_eq_bot (not_lt.2 hp)

Depends on / 依赖: not_lt, pNilradical_eq_bot
-/
theorem pNilradical_eq_bot' {R : Type*} [CommSemiring R] {p : Nat} (hp : p <= 1) :
    pNilradical R p = ⊥ := pNilradical_eq_bot (not_lt.2 hp)

/--
theorem `pNilradical_prime` / 定理 `pNilradical_prime`

English:
theorem pNilradical_prime
  given: {R : Type*} [CommSemiring R] {p : Nat} (hp : p.Prime)
  proof: pNilradical_eq_nilradical hp.one_lt

中文:
定理 pNilradical_prime
  条件: {R : 类型} [CommSemiring R] {p : 自然数} (hp : p.Prime)
  证明: pNilradical_eq_nilradical hp.one_lt

Depends on / 依赖: hp.one_lt, one_lt, pNilradical_eq_nilradical
-/
theorem pNilradical_prime {R : Type*} [CommSemiring R] {p : Nat} (hp : p.Prime) :
    pNilradical R p = nilradical R := pNilradical_eq_nilradical hp.one_lt

/--
theorem `pNilradical_one` / 定理 `pNilradical_one`

English:
theorem pNilradical_one
  given: {R : Type*} [CommSemiring R]
  proof: pNilradical_eq_bot' rfl.le

中文:
定理 pNilradical_one
  条件: {R : 类型} [CommSemiring R]
  证明: pNilradical_eq_bot' rfl.le

Depends on / 依赖: pNilradical_eq_bot, rfl.le
-/
theorem pNilradical_one {R : Type*} [CommSemiring R] :
    pNilradical R 1 = ⊥ := pNilradical_eq_bot' rfl.le

/--
theorem `mem_pNilradical` / 定理 `mem_pNilradical`

English:
theorem mem_pNilradical
  given: {R : Type*} [CommSemiring R] {p : Nat} {x : R}
  proof: by
  by_cases hp : 1 < p
  · rw [pNilradical_eq_nilradical hp]
    refine ⟨fun ⟨n, h⟩ => ⟨n, ?_⟩, fun ⟨n, h⟩ => ⟨p ^ n, h⟩⟩
    rw [← Nat.sub_add_cancel ((n.lt_pow_self hp).le)]; rw [pow_add]; rw [h]; rw [mul_zero]
  rw [pNilradical_eq_bot hp]; rw [Ideal.mem_bot]
  refine ⟨fun h => ⟨0, by rw [pow_ze

中文:
定理 mem_pNilradical
  条件: {R : 类型} [CommSemiring R] {p : 自然数} {x : R}
  证明: by
  by_cases hp : 1 < p
  · rw [pNilradical_eq_nilradical hp]
    refine ⟨fun ⟨n, h⟩ => ⟨n, ?_⟩, fun ⟨n, h⟩ => ⟨p ^ n, h⟩⟩
    rw [← Nat.sub_add_cancel ((n.lt_pow_self hp).le)]; rw [pow_add]; rw [h]; rw [mul_zero]
  rw [pNilradical_eq_bot hp]; rw [Ideal.mem_bot]
  refine ⟨fun h => ⟨0, by rw [pow_ze

Depends on / 依赖: Ideal.mem_bot, Nat.le_one_iff_eq_zero_or_eq_one, Nat.sub_add_cancel, le_one_iff_eq_zero_or_eq_one, lt_pow_self, mem_bot, mul_zero, n.lt_pow_self, not_lt, pNilradical_eq_bot, pNilradical_eq_nilradical, pow_add, pow_one, pow_zero, sub_add_cancel, subsingl, zero_pow
-/
theorem mem_pNilradical {R : Type*} [CommSemiring R] {p : Nat} {x : R} :
    x in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = 0 := by
  by_cases hp : 1 < p
  · rw [pNilradical_eq_nilradical hp]
    refine ⟨fun ⟨n, h⟩ => ⟨n, ?_⟩, fun ⟨n, h⟩ => ⟨p ^ n, h⟩⟩
    rw [← Nat.sub_add_cancel ((n.lt_pow_self hp).le)]; rw [pow_add]; rw [h]; rw [mul_zero]
  rw [pNilradical_eq_bot hp]; rw [Ideal.mem_bot]
  refine ⟨fun h => ⟨0, by rw [pow_zero, pow_one, h]⟩, fun ⟨n, h⟩ => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hp) with hp | hp
  · by_cases hn : n = 0
    · rwa [hn, pow_zero, pow_one] at h
    rw [hp]; rw [zero_pow hn]; rw [pow_zero] at h
    subsingleton [subsingleton_of_zero_eq_one h.symm]
  rwa [hp, one_pow, pow_one] at h

/--
theorem `sub_mem_pNilradical_iff_pow_expChar_pow_eq` / 定理 `sub_mem_pNilradical_iff_pow_expChar_pow_eq`

English:
theorem sub_mem_pNilradical_iff_pow_expChar_pow_eq
  statement: {R : Type*} [CommRing R] {p : Nat} [ExpChar R p]
  proof: by
  simp_rw [mem_pNilradical, sub_pow_expChar_pow, sub_eq_zero]

中文:
定理 sub_mem_pNilradical_iff_pow_expChar_pow_eq
  结论: {R : 类型} [CommRing R] {p : 自然数} [ExpChar R p]
  证明: by
  simp_rw [mem_pNilradical, sub_pow_expChar_pow, sub_eq_zero]

Depends on / 依赖: mem_pNilradical, simp_rw, sub_eq_zero, sub_pow_expChar_pow
-/
theorem sub_mem_pNilradical_iff_pow_expChar_pow_eq {R : Type*} [CommRing R] {p : Nat} [ExpChar R p]
    {x y : R} : x - y in pNilradical R p ↔ exists n : Nat, x ^ p ^ n = y ^ p ^ n := by
  simp_rw [mem_pNilradical, sub_pow_expChar_pow, sub_eq_zero]

/--
theorem `pow_expChar_pow_inj_of_pNilradical_eq_bot` / 定理 `pow_expChar_pow_inj_of_pNilradical_eq_bot`

English:
theorem pow_expChar_pow_inj_of_pNilradical_eq_bot
  statement: (R : Type*) [CommRing R] (p : Nat) [ExpChar R p]
  proof: fun _ _ H =>
sub_eq_zero.1 Ideal.mem_bot.1 h ▸ sub_mem_pNilradical_iff_pow_expChar_pow_eq.2 ⟨n, H⟩

中文:
定理 pow_expChar_pow_inj_of_pNilradical_eq_bot
  结论: (R : 类型) [CommRing R] (p : 自然数) [ExpChar R p]
  证明: fun _ _ H =>
sub_eq_zero.1 Ideal.mem_bot.1 h ▸ sub_mem_pNilradical_iff_pow_expChar_pow_eq.2 ⟨n, H⟩
-/
theorem pow_expChar_pow_inj_of_pNilradical_eq_bot (R : Type*) [CommRing R] (p : Nat) [ExpChar R p]
    (h : pNilradical R p = ⊥) (n : Nat) : Function.Injective fun x : R => x ^ p ^ n := fun _ _ H =>
sub_eq_zero.1 Ideal.mem_bot.1 h ▸ sub_mem_pNilradical_iff_pow_expChar_pow_eq.2 ⟨n, H⟩

/--
theorem `pNilradical_eq_bot_of_frobenius_inj` / 定理 `pNilradical_eq_bot_of_frobenius_inj`

English:
theorem pNilradical_eq_bot_of_frobenius_inj
  statement: (R : Type*) [CommSemiring R] (p : Nat) [ExpChar R p]
  proof: bot_unique fun x => by
  rw [mem_pNilradical]; rw [Ideal.mem_bot]
  exact fun ⟨n, _⟩ => h.iterate n (by rwa [← coe_iterateFrobenius, map_zero])

中文:
定理 pNilradical_eq_bot_of_frobenius_inj
  结论: (R : 类型) [CommSemiring R] (p : 自然数) [ExpChar R p]
  证明: bot_unique fun x => by
  rw [mem_pNilradical]; rw [Ideal.mem_bot]
  exact fun ⟨n, _⟩ => h.iterate n (by rwa [← coe_iterateFrobenius, map_zero])

Depends on / 依赖: Ideal.mem_bot, bot_unique, coe_iterateFrobenius, h.iterate, iterate, map_zero, mem_bot, mem_pNilradical
-/
theorem pNilradical_eq_bot_of_frobenius_inj (R : Type*) [CommSemiring R] (p : Nat) [ExpChar R p]
    (h : Function.Injective (frobenius R p)) : pNilradical R p = ⊥ := bot_unique fun x => by
  rw [mem_pNilradical]; rw [Ideal.mem_bot]
  exact fun ⟨n, _⟩ => h.iterate n (by rwa [← coe_iterateFrobenius, map_zero])

/--
theorem `PerfectRing.pNilradical_eq_bot` / 定理 `PerfectRing.pNilradical_eq_bot`

English:
theorem PerfectRing.pNilradical_eq_bot
  statement: (R : Type*) [CommSemiring R] (p : Nat) [ExpChar R p]
  proof: pNilradical_eq_bot_of_frobenius_inj R p (injective_frobenius R p)

中文:
定理 PerfectRing.pNilradical_eq_bot
  结论: (R : 类型) [CommSemiring R] (p : 自然数) [ExpChar R p]
  证明: pNilradical_eq_bot_of_frobenius_inj R p (injective_frobenius R p)

Depends on / 依赖: injective_frobenius, pNilradical_eq_bot_of_frobenius_inj
-/
theorem PerfectRing.pNilradical_eq_bot (R : Type*) [CommSemiring R] (p : Nat) [ExpChar R p]
    [PerfectRing R p] : pNilradical R p = ⊥ :=
  pNilradical_eq_bot_of_frobenius_inj R p (injective_frobenius R p)

section IsPerfectClosure

variable {K L M N : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K ->+* L) (j : K ->+* M) (f : L ->+* M) (p : Nat)

/-- If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it is called
`p`-radical if the following conditions are satisfied:

- For any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`.
- The kernel of `i` is contained in the `p`-nilradical of `K`.

It is a generalization of purely inseparable extension for fields. -/
@[mk_iff]
/--
Definition of `IsPRadical` / `IsPRadical` 的定义

English:
class IsPRadical
  parameters: : Prop where
  axioms and operations (2):
    - pow_mem' : forall x : L, exists (n : Nat) (y : K), i y = x ^ p ^ n
    - ker_le' : RingHom.ker i <= pNilradical K p

中文:
类 IsPRadical
  参数: : 命题 where
  公理与运算 (2 个):
    - pow_mem' : 对任意 x : L, 存在 (n : 自然数) (y : K), i y = x ^ p ^ n
    - ker_le' : RingHom.ker i <= pNilradical K p
-/
class IsPRadical : Prop where
  pow_mem' : forall x : L, exists (n : Nat) (y : K), i y = x ^ p ^ n
  ker_le' : RingHom.ker i <= pNilradical K p

/--
theorem `IsPRadical.pow_mem` / 定理 `IsPRadical.pow_mem`

English:
theorem IsPRadical.pow_mem
  given: [IsPRadical i p] (x : L)
  proof: pow_mem' x

中文:
定理 IsPRadical.pow_mem
  条件: [IsPRadical i p] (x : L)
  证明: pow_mem' x

Depends on / 依赖: pow_mem
-/
theorem IsPRadical.pow_mem [IsPRadical i p] (x : L) :
    exists (n : Nat) (y : K), i y = x ^ p ^ n := pow_mem' x

/--
theorem `IsPRadical.ker_le` / 定理 `IsPRadical.ker_le`

English:
theorem IsPRadical.ker_le
  given: [IsPRadical i p]
  proof: ker_le'

中文:
定理 IsPRadical.ker_le
  条件: [IsPRadical i p]
  证明: ker_le'

Depends on / 依赖: ker_le
-/
theorem IsPRadical.ker_le [IsPRadical i p] :
    RingHom.ker i <= pNilradical K p := ker_le'

/--
theorem `IsPRadical.comap_pNilradical` / 定理 `IsPRadical.comap_pNilradical`

English:
theorem IsPRadical.comap_pNilradical
  given: [IsPRadical i p]
  proof: by
  refine le_antisymm (fun x h => mem_pNilradical.2 ?_) (fun x h => ?_)
· obtain ⟨n, h⟩ := mem_pNilradical.1 Ideal.mem_comap.1 h
obtain ⟨m, h⟩ := mem_pNilradical.1 ker_le i p ((map_pow i x _).symm ▸ h)
    exact ⟨n + m, by rwa [pow_add, pow_mul]⟩
  simp only [Ideal.mem_comap, mem_pNilradical] at h

中文:
定理 IsPRadical.comap_pNilradical
  条件: [IsPRadical i p]
  证明: by
  refine le_antisymm (fun x h => mem_pNilradical.2 ?_) (fun x h => ?_)
· obtain ⟨n, h⟩ := mem_pNilradical.1 Ideal.mem_comap.1 h
obtain ⟨m, h⟩ := mem_pNilradical.1 ker_le i p ((map_pow i x _).symm ▸ h)
    exact ⟨n + m, by rwa [pow_add, pow_mul]⟩
  simp only [Ideal.mem_comap, mem_pNilradical] at h

Depends on / 依赖: Ideal.mem_comap, ker_le, le_antisymm, map_pow, map_zero, mem_comap, mem_pNilradical, pow_add, pow_mul
-/
theorem IsPRadical.comap_pNilradical [IsPRadical i p] :
    (pNilradical L p).comap i = pNilradical K p := by
  refine le_antisymm (fun x h => mem_pNilradical.2 ?_) (fun x h => ?_)
· obtain ⟨n, h⟩ := mem_pNilradical.1 Ideal.mem_comap.1 h
obtain ⟨m, h⟩ := mem_pNilradical.1 ker_le i p ((map_pow i x _).symm ▸ h)
    exact ⟨n + m, by rwa [pow_add, pow_mul]⟩
  simp only [Ideal.mem_comap, mem_pNilradical] at h ⊢
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simpa only [map_pow, map_zero] using congr(i $h)⟩

variable (K) in
/--
Instance `IsPRadical.of_id` / 实例 `IsPRadical.of_id`

English:
instance IsPRadical.of_id
  signature: : IsPRadical (RingHom.id K) p where
  body: ⟨0, x, by simp⟩
  ker_le' x h := by convert! Ideal.zero_mem _

中文:
实例 IsPRadical.of_id
  签名: : IsPRadical (RingHom.id K) p where
  定义体: ⟨0, x, by simp⟩
  ker_le' x h := by convert! Ideal.zero_mem _

Depends on / 依赖: Disjoint, Equiv.swap, Int.units_eq_one_, IsSwap, Perm.notMem_support, Perm.smul_def, Set.disjoint_left.mp, _root_, _root_.Disjoint, classical, convert, disjoint_left, hk_support, hk_swap, k.support, mem_smul_set, mem_stabilizer_iff, mem_stabilizer_set_iff_smul_set_subset, notMem_support, s.toFinite
-/
instance IsPRadical.of_id : IsPRadical (RingHom.id K) p where
  pow_mem' x := ⟨0, x, by simp⟩
  ker_le' x h := by convert! Ideal.zero_mem _

/--
theorem `IsPRadical.trans` / 定理 `IsPRadical.trans`

English:
theorem IsPRadical.trans
  given: [IsPRadical i p] [IsPRadical f p]
  proof: by
    obtain ⟨n, y, hy⟩ := pow_mem f p x
    obtain ⟨m, z, hz⟩ := pow_mem i p y
    exact ⟨n + m, z, by rw [RingHom.comp_apply, hz, map_pow, hy, pow_add, pow_mul]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker]; rw [RingHom.comp_apply]; rw [← RingHom.mem_ker] at h
    simpa only [← Ideal.mem_comap, c

中文:
定理 IsPRadical.trans
  条件: [IsPRadical i p] [IsPRadical f p]
  证明: by
    obtain ⟨n, y, hy⟩ := pow_mem f p x
    obtain ⟨m, z, hz⟩ := pow_mem i p y
    exact ⟨n + m, z, by rw [RingHom.comp_apply, hz, map_pow, hy, pow_add, pow_mul]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker]; rw [RingHom.comp_apply]; rw [← RingHom.mem_ker] at h
    simpa only [← Ideal.mem_comap, c

Depends on / 依赖: Ideal.mem_comap, RingHom, RingHom.comp_apply, RingHom.mem_ker, comap_pNilradical, comp_apply, ker_le, map_pow, mem_comap, mem_ker, pow_add, pow_mem, pow_mul
-/
theorem IsPRadical.trans [IsPRadical i p] [IsPRadical f p] :
    IsPRadical (f.comp i) p where
  pow_mem' x := by
    obtain ⟨n, y, hy⟩ := pow_mem f p x
    obtain ⟨m, z, hz⟩ := pow_mem i p y
    exact ⟨n + m, z, by rw [RingHom.comp_apply, hz, map_pow, hy, pow_add, pow_mul]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker]; rw [RingHom.comp_apply]; rw [← RingHom.mem_ker] at h
    simpa only [← Ideal.mem_comap, comap_pNilradical] using ker_le f p h

/-- If `i : K →+* L` is a `p`-radical ring homomorphism, then it makes `L` a perfect closure
of `K`, if `L` is perfect.
In this case the kernel of `i` is equal to the `p`-nilradical of `K`
(see `IsPerfectClosure.ker_eq`).

Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
`PerfectRing` which has `ExpChar` as a prerequisite. -/
@[nolint unusedArguments]
/--
Definition of `IsPerfectClosure` / `IsPerfectClosure` 的定义

English:
abbreviation IsPerfectClosure
  signature: [ExpChar L p] [PerfectRing L p]
  body: IsPRadical i p

中文:
缩写 IsPerfectClosure
  签名: [ExpChar L p] [PerfectRing L p]
  定义体: IsPRadical i p

Depends on / 依赖: IsPRadical
-/
abbrev IsPerfectClosure [ExpChar L p] [PerfectRing L p] := IsPRadical i p

/--
theorem `RingHom.pNilradical_le_ker_of_perfectRing` / 定理 `RingHom.pNilradical_le_ker_of_perfectRing`

English:
theorem RingHom.pNilradical_le_ker_of_perfectRing
  given: [ExpChar L p] [PerfectRing L p]
  proof: fun x h => by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

中文:
定理 RingHom.pNilradical_le_ker_of_perfectRing
  条件: [ExpChar L p] [PerfectRing L p]
  证明: fun x h => by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

Depends on / 依赖: RingEquiv, RingEquiv.symm_apply_apply, iterateFrobeniusEquiv, iterateFrobeniusEquiv_apply, iterateFrobenius_def, map_pow, map_zero, mem_pNilradical, replace, symm_apply_apply
-/
theorem RingHom.pNilradical_le_ker_of_perfectRing [ExpChar L p] [PerfectRing L p] :
    pNilradical K p <= RingHom.ker i := fun x h => by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

variable [ExpChar L p] in
/--
theorem `IsPerfectClosure.ker_eq` / 定理 `IsPerfectClosure.ker_eq`

English:
theorem IsPerfectClosure.ker_eq
  given: [PerfectRing L p] [IsPerfectClosure i p]
  proof: IsPRadical.ker_le'.antisymm (i.pNilradical_le_ker_of_perfectRing p)

中文:
定理 IsPerfectClosure.ker_eq
  条件: [PerfectRing L p] [IsPerfectClosure i p]
  证明: IsPRadical.ker_le'.antisymm (i.pNilradical_le_ker_of_perfectRing p)

Depends on / 依赖: IsPRadical, IsPRadical.ker_le, antisymm, i.pNilradical_le_ker_of_perfectRing, ker_le, pNilradical_le_ker_of_perfectRing
-/
theorem IsPerfectClosure.ker_eq [PerfectRing L p] [IsPerfectClosure i p] :
    RingHom.ker i = pNilradical K p :=
  IsPRadical.ker_le'.antisymm (i.pNilradical_le_ker_of_perfectRing p)

namespace PerfectRing

/- NOTE: To define `PerfectRing.lift_aux`, only the `IsPRadical.pow_mem` is required, but not
`IsPRadical.ker_le`. But in order to use typeclass, here we require the whole `IsPRadical`. -/

variable [ExpChar M p] [PerfectRing M p] [IsPRadical i p]

/--
theorem `lift_aux` / 定理 `lift_aux`

English:
theorem lift_aux
  given: (x : L)
  statement: exists y : Nat × K, i y.2 = x ^ p ^ y.1
  proof: by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

中文:
定理 lift_aux
  条件: (x : L)
  结论: 存在 y : 自然数 × K, i y.2 = x ^ p ^ y.1
  证明: by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

Depends on / 依赖: IsPRadical, IsPRadical.pow_mem, pow_mem
-/
theorem lift_aux (x : L) : exists y : Nat × K, i y.2 = x ^ p ^ y.1 := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: (x : L)
  body: (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
  (j (Classical.choose (lift_aux i p x)).2)

@[simp]

中文:
定义 liftAux
  签名: (x : L)
  定义体: (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
  (j (Classical.choose (lift_aux i p x)).2)

@[simp]

Depends on / 依赖: Classical, Classical.choose, iterateFrobeniusEquiv, lift_aux
-/
def liftAux (x : L) : M := (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
  (j (Classical.choose (lift_aux i p x)).2)

@[simp]
/--
theorem `liftAux_self_apply` / 定理 `liftAux_self_apply`

English:
theorem liftAux_self_apply
  given: [ExpChar L p] [PerfectRing L p] (x : L)
  statement: liftAux i i p x = x
  proof: by
  rw [liftAux]; rw [Classical.choose_spec (lift_aux i p x)]; rw [← iterateFrobenius_def]; rw [← iterateFrobeniusEquiv_apply]; rw [RingEquiv.symm_apply_apply]

@[simp]

中文:
定理 liftAux_self_apply
  条件: [ExpChar L p] [PerfectRing L p] (x : L)
  结论: liftAux i i p x = x
  证明: by
  rw [liftAux]; rw [Classical.choose_spec (lift_aux i p x)]; rw [← iterateFrobenius_def]; rw [← iterateFrobeniusEquiv_apply]; rw [RingEquiv.symm_apply_apply]

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, RingEquiv, RingEquiv.symm_apply_apply, choose_spec, iterateFrobeniusEquiv_apply, iterateFrobenius_def, liftAux, lift_aux, symm_apply_apply
-/
theorem liftAux_self_apply [ExpChar L p] [PerfectRing L p] (x : L) : liftAux i i p x = x := by
  rw [liftAux]; rw [Classical.choose_spec (lift_aux i p x)]; rw [← iterateFrobenius_def]; rw [← iterateFrobeniusEquiv_apply]; rw [RingEquiv.symm_apply_apply]

@[simp]
/--
theorem `liftAux_self` / 定理 `liftAux_self`

English:
theorem liftAux_self
  given: [ExpChar L p] [PerfectRing L p]
  statement: liftAux i i p = id
  proof: funext (liftAux_self_apply i p)

@[simp]

中文:
定理 liftAux_self
  条件: [ExpChar L p] [PerfectRing L p]
  结论: liftAux i i p = id
  证明: funext (liftAux_self_apply i p)

@[simp]

Depends on / 依赖: liftAux_self_apply
-/
theorem liftAux_self [ExpChar L p] [PerfectRing L p] : liftAux i i p = id :=
  funext (liftAux_self_apply i p)

@[simp]
/--
theorem `liftAux_id_apply` / 定理 `liftAux_id_apply`

English:
theorem liftAux_id_apply
  given: (x : K)
  statement: liftAux (RingHom.id K) j p x = j x
  proof: by
  have := RingHom.id_apply _ ▸ Classical.choose_spec (lift_aux (RingHom.id K) p x)
  rw [liftAux]; rw [this]; rw [map_pow]; rw [← iterateFrobenius_def]; rw [← iterateFrobeniusEquiv_apply]; rw [RingEquiv.symm_apply_apply]

@[simp]

中文:
定理 liftAux_id_apply
  条件: (x : K)
  结论: liftAux (RingHom.id K) j p x = j x
  证明: by
  have := RingHom.id_apply _ ▸ Classical.choose_spec (lift_aux (RingHom.id K) p x)
  rw [liftAux]; rw [this]; rw [map_pow]; rw [← iterateFrobenius_def]; rw [← iterateFrobeniusEquiv_apply]; rw [RingEquiv.symm_apply_apply]

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, RingEquiv, RingEquiv.symm_apply_apply, RingHom, RingHom.id, RingHom.id_apply, choose_spec, id_apply, iterateFrobeniusEquiv_apply, iterateFrobenius_def, liftAux, lift_aux, map_pow, symm_apply_apply
-/
theorem liftAux_id_apply (x : K) : liftAux (RingHom.id K) j p x = j x := by
  have := RingHom.id_apply _ ▸ Classical.choose_spec (lift_aux (RingHom.id K) p x)
  rw [liftAux]; rw [this]; rw [map_pow]; rw [← iterateFrobenius_def]; rw [← iterateFrobeniusEquiv_apply]; rw [RingEquiv.symm_apply_apply]

@[simp]
/--
theorem `liftAux_id` / 定理 `liftAux_id`

English:
theorem liftAux_id
  statement: liftAux (RingHom.id K) j p = j
  proof: funext (liftAux_id_apply j p)

中文:
定理 liftAux_id
  结论: liftAux (RingHom.id K) j p = j
  证明: funext (liftAux_id_apply j p)

Depends on / 依赖: liftAux_id_apply
-/
theorem liftAux_id : liftAux (RingHom.id K) j p = j := funext (liftAux_id_apply j p)

end PerfectRing

end CommSemiring

section CommRing

variable [CommRing K] [CommRing L] [CommRing M] [CommRing N]
  (i : K ->+* L) (j : K ->+* M) (k : K ->+* N) (f : L ->+* M) (g : L ->+* N)
  (p : Nat) [ExpChar M p]


namespace IsPRadical

/--
theorem `injective_comp_of_pNilradical_eq_bot` / 定理 `injective_comp_of_pNilradical_eq_bot`

English:
theorem injective_comp_of_pNilradical_eq_bot
  given: [IsPRadical i p] (h : pNilradical M p = ⊥)
  proof: fun f g heq => by
  ext x
  obtain ⟨n, y, hx⟩ := IsPRadical.pow_mem i p x
  apply_fun _ using pow_expChar_pow_inj_of_pNilradical_eq_bot M p h n
  simpa only [← map_pow, ← hx] using! congr($(heq) y)

中文:
定理 injective_comp_of_pNilradical_eq_bot
  条件: [IsPRadical i p] (h : pNilradical M p = ⊥)
  证明: fun f g heq => by
  ext x
  obtain ⟨n, y, hx⟩ := IsPRadical.pow_mem i p x
  apply_fun _ using pow_expChar_pow_inj_of_pNilradical_eq_bot M p h n
  simpa only [← map_pow, ← hx] using! congr($(heq) y)

Depends on / 依赖: IsPRadical, IsPRadical.pow_mem, apply_fun, map_pow, pow_expChar_pow_inj_of_pNilradical_eq_bot, pow_mem
-/
theorem injective_comp_of_pNilradical_eq_bot [IsPRadical i p] (h : pNilradical M p = ⊥) :
    Function.Injective fun f : L ->+* M => f.comp i := fun f g heq => by
  ext x
  obtain ⟨n, y, hx⟩ := IsPRadical.pow_mem i p x
  apply_fun _ using pow_expChar_pow_inj_of_pNilradical_eq_bot M p h n
  simpa only [← map_pow, ← hx] using! congr($(heq) y)

variable (M)

/--
theorem `injective_comp` / 定理 `injective_comp`

English:
theorem injective_comp
  given: [IsPRadical i p] [IsReduced M]
  proof: injective_comp_of_pNilradical_eq_bot i p bot_unique
    pNilradical_le_nilradical.trans (nilradical_eq_zero M).le

中文:
定理 injective_comp
  条件: [IsPRadical i p] [IsReduced M]
  证明: injective_comp_of_pNilradical_eq_bot i p bot_unique
    pNilradical_le_nilradical.trans (nilradical_eq_zero M).le

Depends on / 依赖: bot_unique, injective_comp_of_pNilradical_eq_bot, nilradical_eq_zero, pNilradical_le_nilradical, pNilradical_le_nilradical.trans
-/
theorem injective_comp [IsPRadical i p] [IsReduced M] :
    Function.Injective fun f : L ->+* M => f.comp i :=
injective_comp_of_pNilradical_eq_bot i p bot_unique
    pNilradical_le_nilradical.trans (nilradical_eq_zero M).le

/--
theorem `injective_comp_of_perfect` / 定理 `injective_comp_of_perfect`

English:
theorem injective_comp_of_perfect
  given: [IsPRadical i p] [PerfectRing M p]
  proof: injective_comp_of_pNilradical_eq_bot i p (PerfectRing.pNilradical_eq_bot M p)

中文:
定理 injective_comp_of_perfect
  条件: [IsPRadical i p] [PerfectRing M p]
  证明: injective_comp_of_pNilradical_eq_bot i p (PerfectRing.pNilradical_eq_bot M p)

Depends on / 依赖: PerfectRing, PerfectRing.pNilradical_eq_bot, injective_comp_of_pNilradical_eq_bot, pNilradical_eq_bot
-/
theorem injective_comp_of_perfect [IsPRadical i p] [PerfectRing M p] :
    Function.Injective fun f : L ->+* M => f.comp i :=
  injective_comp_of_pNilradical_eq_bot i p (PerfectRing.pNilradical_eq_bot M p)

end IsPRadical

namespace PerfectRing

variable [ExpChar K p] [PerfectRing M p] [IsPRadical i p]

/--
theorem `liftAux_apply` / 定理 `liftAux_apply`

English:
theorem liftAux_apply
  given: (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n)
  proof: by
  rw [liftAux]
  have h' := Classical.choose_spec (lift_aux i p x)
  set n' := (Classical.choose (lift_aux i p x)).1
  replace h := congr($(h.symm) ^ p ^ n')
  rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [← h']; rw [← map_pow]; rw [← map_pow]; rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom

中文:
定理 liftAux_apply
  条件: (x : L) (n : 自然数) (y : K) (h : i y = x ^ p ^ n)
  证明: by
  rw [liftAux]
  have h' := Classical.choose_spec (lift_aux i p x)
  set n' := (Classical.choose (lift_aux i p x)).1
  replace h := congr($(h.symm) ^ p ^ n')
  rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [← h']; rw [← map_pow]; rw [← map_pow]; rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, IsPRadical, IsPRadical.ker_le, RingEquiv, RingEquiv.apply_symm_app, RingHom, RingHom.mem_ker, apply_symm_app, choose_spec, conv_lhs, h.symm, injective, iterateFrobeniusEquiv, iterateFrobeniusEquiv_add_apply, ker_le, liftAux, lift_aux, map_pow
-/
theorem liftAux_apply (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n) :
    liftAux i j p x = (iterateFrobeniusEquiv M p n).symm (j y) := by
  rw [liftAux]
  have h' := Classical.choose_spec (lift_aux i p x)
  set n' := (Classical.choose (lift_aux i p x)).1
  replace h := congr($(h.symm) ^ p ^ n')
  rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [← h']; rw [← map_pow]; rw [← map_pow]; rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom.mem_ker] at h
  obtain ⟨m, h⟩ := mem_pNilradical.1 (IsPRadical.ker_le i p h)
  refine (iterateFrobeniusEquiv M p (m + n + n')).injective ?_
  conv_lhs => rw [iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply]
  rw [add_assoc]; rw [add_comm n n']; rw [← add_assoc]; rw [iterateFrobeniusEquiv_add_apply (m := m + n')]; rw [RingEquiv.apply_symm_apply]; rw [iterateFrobeniusEquiv_def]; rw [iterateFrobeniusEquiv_def]; rw [← sub_eq_zero]; rw [← map_pow]; rw [← map_pow]; rw [← map_sub]; rw [add_comm m]; rw [add_comm m]; rw [pow_add]; rw [pow_mul]; rw [pow_add]; rw [pow_mul]; rw [← sub_pow_expChar_pow]; rw [h]; rw [map_zero]

variable [ExpChar L p]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : L ->+* M where
  body: liftAux i j p
  map_one' := by simp [liftAux_apply i j p 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1]; rw [liftAux_apply i j p _ _ _ h2]; rw [li

中文:
定义 lift
  签名: : L ->+* M where
  定义体: liftAux i j p
  map_one' := by simp [liftAux_apply i j p 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1]; rw [liftAux_apply i j p _ _ _ h2]; rw [li

Depends on / 依赖: liftAux
-/
def lift : L ->+* M where
  toFun := liftAux i j p
  map_one' := by simp [liftAux_apply i j p 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1]; rw [liftAux_apply i j p _ _ _ h2]; rw [liftAux_apply i j p (x1 * x2) (n1 + n2) (y1 ^ p ^ n2 * y2 ^ p ^ n1) (by rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [h1]; rw [h2]; rw [← pow_mul]; rw [← pow_add]; rw [← pow_mul]; rw [← pow_add]; rw [add_comm n2]; rw [mul_pow]),
      map_mul, map_pow, map_pow, map_mul, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply]; rw [add_comm n1]; rw [iterateFrobeniusEquiv_symm_add_apply]; rw [← iterateFrobeniusEquiv_def]; rw [RingEquiv.symm_apply_apply]
  map_zero' := by simp [liftAux_apply i j p 0 0 0 (by rw [pow_zero, pow_one, map_zero])]
  map_add' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1]; rw [liftAux_apply i j p _ _ _ h2]; rw [liftAux_apply i j p (x1 + x2) (n1 + n2) (y1 ^ p ^ n2 + y2 ^ p ^ n1) (by rw [map_add]; rw [map_pow]; rw [map_pow]; rw [h1]; rw [h2]; rw [← pow_mul]; rw [← pow_add]; rw [← pow_mul]; rw [← pow_add]; rw [add_comm n2]; rw [add_pow_expChar_pow]),
      map_add, map_pow, map_pow, map_add, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply]; rw [add_comm n1]; rw [iterateFrobeniusEquiv_symm_add_apply]; rw [← iterateFrobeniusEquiv_def]; rw [RingEquiv.symm_apply_apply]

/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n)
  proof: liftAux_apply i j p _ _ _ h

@[simp]

中文:
定理 lift_apply
  条件: (x : L) (n : 自然数) (y : K) (h : i y = x ^ p ^ n)
  证明: liftAux_apply i j p _ _ _ h

@[simp]

Depends on / 依赖: liftAux_apply
-/
theorem lift_apply (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n) :
    lift i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  liftAux_apply i j p _ _ _ h

@[simp]
/--
theorem `lift_comp_apply` / 定理 `lift_comp_apply`

English:
theorem lift_comp_apply
  given: (x : K)
  statement: lift i j p (i x) = j x
  proof: by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero]; rw [pow_one]), iterateFrobeniusEquiv_zero]; rfl

@[simp]

中文:
定理 lift_comp_apply
  条件: (x : K)
  结论: lift i j p (i x) = j x
  证明: by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero]; rw [pow_one]), iterateFrobeniusEquiv_zero]; rfl

@[simp]

Depends on / 依赖: iterateFrobeniusEquiv_zero, lift_apply, pow_one, pow_zero
-/
theorem lift_comp_apply (x : K) : lift i j p (i x) = j x := by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero]; rw [pow_one]), iterateFrobeniusEquiv_zero]; rfl

@[simp]
/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  statement: (lift i j p).comp i = j
  proof: RingHom.ext (lift_comp_apply i j p)

中文:
定理 lift_comp
  结论: (lift i j p).comp i = j
  证明: RingHom.ext (lift_comp_apply i j p)

Depends on / 依赖: RingHom, RingHom.ext, lift_comp_apply
-/
theorem lift_comp : (lift i j p).comp i = j := RingHom.ext (lift_comp_apply i j p)

/--
theorem `lift_self_apply` / 定理 `lift_self_apply`

English:
theorem lift_self_apply
  given: [PerfectRing L p] (x : L)
  statement: lift i i p x = x
  proof: liftAux_self_apply i p x

@[simp]

中文:
定理 lift_self_apply
  条件: [PerfectRing L p] (x : L)
  结论: lift i i p x = x
  证明: liftAux_self_apply i p x

@[simp]

Depends on / 依赖: liftAux_self_apply
-/
theorem lift_self_apply [PerfectRing L p] (x : L) : lift i i p x = x := liftAux_self_apply i p x

@[simp]
/--
theorem `lift_self` / 定理 `lift_self`

English:
theorem lift_self
  given: [PerfectRing L p]
  statement: lift i i p = RingHom.id L
  proof: RingHom.ext (liftAux_self_apply i p)

中文:
定理 lift_self
  条件: [PerfectRing L p]
  结论: lift i i p = RingHom.id L
  证明: RingHom.ext (liftAux_self_apply i p)

Depends on / 依赖: RingHom, RingHom.ext, liftAux_self_apply
-/
theorem lift_self [PerfectRing L p] : lift i i p = RingHom.id L :=
  RingHom.ext (liftAux_self_apply i p)

/--
theorem `lift_id_apply` / 定理 `lift_id_apply`

English:
theorem lift_id_apply
  given: (x : K)
  statement: lift (RingHom.id K) j p x = j x
  proof: liftAux_id_apply j p x

@[simp]

中文:
定理 lift_id_apply
  条件: (x : K)
  结论: lift (RingHom.id K) j p x = j x
  证明: liftAux_id_apply j p x

@[simp]

Depends on / 依赖: liftAux_id_apply
-/
theorem lift_id_apply (x : K) : lift (RingHom.id K) j p x = j x := liftAux_id_apply j p x

@[simp]
/--
theorem `lift_id` / 定理 `lift_id`

English:
theorem lift_id
  statement: lift (RingHom.id K) j p = j
  proof: RingHom.ext (liftAux_id_apply j p)

@[simp]

中文:
定理 lift_id
  结论: lift (RingHom.id K) j p = j
  证明: RingHom.ext (liftAux_id_apply j p)

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, liftAux_id_apply
-/
theorem lift_id : lift (RingHom.id K) j p = j := RingHom.ext (liftAux_id_apply j p)

@[simp]
/--
theorem `comp_lift` / 定理 `comp_lift`

English:
theorem comp_lift
  statement: lift i (f.comp i) p = f
  proof: IsPRadical.injective_comp_of_perfect _ i p (lift_comp i _ p)

中文:
定理 comp_lift
  结论: lift i (f.comp i) p = f
  证明: IsPRadical.injective_comp_of_perfect _ i p (lift_comp i _ p)

Depends on / 依赖: IsPRadical, IsPRadical.injective_comp_of_perfect, injective_comp_of_perfect, lift_comp
-/
theorem comp_lift : lift i (f.comp i) p = f :=
  IsPRadical.injective_comp_of_perfect _ i p (lift_comp i _ p)

/--
theorem `comp_lift_apply` / 定理 `comp_lift_apply`

English:
theorem comp_lift_apply
  given: (x : L)
  statement: lift i (f.comp i) p x = f x
  proof: congr($(comp_lift i f p) x)

中文:
定理 comp_lift_apply
  条件: (x : L)
  结论: lift i (f.comp i) p x = f x
  证明: congr($(comp_lift i f p) x)

Depends on / 依赖: comp_lift
-/
theorem comp_lift_apply (x : L) : lift i (f.comp i) p x = f x := congr($(comp_lift i f p) x)

variable (M) in
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : (K ->+* M) ≃ (L ->+* M) where
  body: lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv f := comp_lift i f p

中文:
定义 liftEquiv
  签名: : (K ->+* M) ≃ (L ->+* M) where
  定义体: lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv f := comp_lift i f p
-/
def liftEquiv : (K ->+* M) ≃ (L ->+* M) where
  toFun j := lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv f := comp_lift i f p

/--
theorem `liftEquiv_apply` / 定理 `liftEquiv_apply`

English:
theorem liftEquiv_apply
  statement: liftEquiv M i p j = lift i j p
  proof: rfl

中文:
定理 liftEquiv_apply
  结论: liftEquiv M i p j = lift i j p
  证明: rfl
-/
theorem liftEquiv_apply : liftEquiv M i p j = lift i j p := rfl

/--
theorem `liftEquiv_symm_apply` / 定理 `liftEquiv_symm_apply`

English:
theorem liftEquiv_symm_apply
  statement: (liftEquiv M i p).symm f = f.comp i
  proof: rfl

中文:
定理 liftEquiv_symm_apply
  结论: (liftEquiv M i p).symm f = f.comp i
  证明: rfl

Depends on / 依赖: IsCyclic, Subsingleton, isCyclic_of_subsingleton
-/
theorem liftEquiv_symm_apply : (liftEquiv M i p).symm f = f.comp i := rfl

/--
theorem `liftEquiv_id_apply` / 定理 `liftEquiv_id_apply`

English:
theorem liftEquiv_id_apply
  statement: liftEquiv M (RingHom.id K) p j = j
  proof: lift_id j p

@[simp]

中文:
定理 liftEquiv_id_apply
  结论: liftEquiv M (RingHom.id K) p j = j
  证明: lift_id j p

@[simp]

Depends on / 依赖: lift_id
-/
theorem liftEquiv_id_apply : liftEquiv M (RingHom.id K) p j = j :=
  lift_id j p

@[simp]
/--
theorem `liftEquiv_id` / 定理 `liftEquiv_id`

English:
theorem liftEquiv_id
  statement: liftEquiv M (RingHom.id K) p = Equiv.refl _
  proof: Equiv.ext (liftEquiv_id_apply · p)

中文:
定理 liftEquiv_id
  结论: liftEquiv M (RingHom.id K) p = Equiv.refl _
  证明: Equiv.ext (liftEquiv_id_apply · p)

Depends on / 依赖: Equiv.ext, liftEquiv_id_apply
-/
theorem liftEquiv_id : liftEquiv M (RingHom.id K) p = Equiv.refl _ :=
  Equiv.ext (liftEquiv_id_apply · p)

section comp

variable [ExpChar N p] [PerfectRing N p] [IsPRadical j p]

@[simp]
/--
theorem `lift_comp_lift` / 定理 `lift_comp_lift`

English:
theorem lift_comp_lift
  statement: (lift j k p).comp (lift i j p) = lift i k p
  proof: IsPRadical.injective_comp_of_perfect _ i p (by ext; simp)

@[simp]

中文:
定理 lift_comp_lift
  结论: (lift j k p).comp (lift i j p) = lift i k p
  证明: IsPRadical.injective_comp_of_perfect _ i p (by ext; simp)

@[simp]

Depends on / 依赖: IsPRadical, IsPRadical.injective_comp_of_perfect, injective_comp_of_perfect
-/
theorem lift_comp_lift : (lift j k p).comp (lift i j p) = lift i k p :=
  IsPRadical.injective_comp_of_perfect _ i p (by ext; simp)

@[simp]
/--
theorem `lift_comp_lift_apply` / 定理 `lift_comp_lift_apply`

English:
theorem lift_comp_lift_apply
  given: (x : L)
  statement: lift j k p (lift i j p x) = lift i k p x
  proof: congr($(lift_comp_lift i j k p) x)

中文:
定理 lift_comp_lift_apply
  条件: (x : L)
  结论: lift j k p (lift i j p x) = lift i k p x
  证明: congr($(lift_comp_lift i j k p) x)

Depends on / 依赖: lift_comp_lift
-/
theorem lift_comp_lift_apply (x : L) : lift j k p (lift i j p x) = lift i k p x :=
  congr($(lift_comp_lift i j k p) x)

/--
theorem `lift_comp_lift_apply_eq_self` / 定理 `lift_comp_lift_apply_eq_self`

English:
theorem lift_comp_lift_apply_eq_self
  given: [PerfectRing L p] (x : L)
  proof: by
  rw [lift_comp_lift_apply]; rw [lift_self_apply]

中文:
定理 lift_comp_lift_apply_eq_self
  条件: [PerfectRing L p] (x : L)
  证明: by
  rw [lift_comp_lift_apply]; rw [lift_self_apply]

Depends on / 依赖: lift_comp_lift_apply, lift_self_apply
-/
theorem lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) :
    lift j i p (lift i j p x) = x := by
  rw [lift_comp_lift_apply]; rw [lift_self_apply]

/--
theorem `lift_comp_lift_eq_id` / 定理 `lift_comp_lift_eq_id`

English:
theorem lift_comp_lift_eq_id
  given: [PerfectRing L p]
  proof: RingHom.ext (lift_comp_lift_apply_eq_self i j p)

中文:
定理 lift_comp_lift_eq_id
  条件: [PerfectRing L p]
  证明: RingHom.ext (lift_comp_lift_apply_eq_self i j p)

Depends on / 依赖: RingHom, RingHom.ext, lift_comp_lift_apply_eq_self
-/
theorem lift_comp_lift_eq_id [PerfectRing L p] :
    (lift j i p).comp (lift i j p) = RingHom.id L :=
  RingHom.ext (lift_comp_lift_apply_eq_self i j p)

end comp

section liftEquiv_comp

variable [ExpChar N p] [IsPRadical g p] [IsPRadical (g.comp i) p]

@[simp]
/--
theorem `lift_lift` / 定理 `lift_lift`

English:
theorem lift_lift
  statement: lift g (lift i j p) p = lift (g.comp i) j p
  proof: by
  refine IsPRadical.injective_comp_of_perfect _ (g.comp i) p ?_
  simp_rw [← RingHom.comp_assoc _ _ (lift g _ p), lift_comp]

中文:
定理 lift_lift
  结论: lift g (lift i j p) p = lift (g.comp i) j p
  证明: by
  refine IsPRadical.injective_comp_of_perfect _ (g.comp i) p ?_
  simp_rw [← RingHom.comp_assoc _ _ (lift g _ p), lift_comp]

Depends on / 依赖: IsPRadical, IsPRadical.injective_comp_of_perfect, RingHom, RingHom.comp_assoc, comp_assoc, g.comp, injective_comp_of_perfect, lift_comp, simp_rw
-/
theorem lift_lift : lift g (lift i j p) p = lift (g.comp i) j p := by
  refine IsPRadical.injective_comp_of_perfect _ (g.comp i) p ?_
  simp_rw [← RingHom.comp_assoc _ _ (lift g _ p), lift_comp]

/--
theorem `lift_lift_apply` / 定理 `lift_lift_apply`

English:
theorem lift_lift_apply
  given: (x : N)
  statement: lift g (lift i j p) p x = lift (g.comp i) j p x
  proof: congr($(lift_lift i j g p) x)

@[simp]

中文:
定理 lift_lift_apply
  条件: (x : N)
  结论: lift g (lift i j p) p x = lift (g.comp i) j p x
  证明: congr($(lift_lift i j g p) x)

@[simp]

Depends on / 依赖: lift_lift
-/
theorem lift_lift_apply (x : N) : lift g (lift i j p) p x = lift (g.comp i) j p x :=
  congr($(lift_lift i j g p) x)

@[simp]
/--
theorem `liftEquiv_comp_apply` / 定理 `liftEquiv_comp_apply`

English:
theorem liftEquiv_comp_apply
  proof: lift_lift i j g p

@[simp]

中文:
定理 liftEquiv_comp_apply
  证明: lift_lift i j g p

@[simp]

Depends on / 依赖: lift_lift
-/
theorem liftEquiv_comp_apply :
    liftEquiv M g p (liftEquiv M i p j) = liftEquiv M (g.comp i) p j := lift_lift i j g p

@[simp]
/--
theorem `liftEquiv_trans` / 定理 `liftEquiv_trans`

English:
theorem liftEquiv_trans
  proof: Equiv.ext (liftEquiv_comp_apply i · g p)

中文:
定理 liftEquiv_trans
  证明: Equiv.ext (liftEquiv_comp_apply i · g p)

Depends on / 依赖: Equiv.ext, liftEquiv_comp_apply
-/
theorem liftEquiv_trans :
    (liftEquiv M i p).trans (liftEquiv M g p) = liftEquiv M (g.comp i) p :=
  Equiv.ext (liftEquiv_comp_apply i · g p)

end liftEquiv_comp

end PerfectRing

namespace IsPerfectClosure

variable [ExpChar K p] [ExpChar L p] [PerfectRing L p] [IsPerfectClosure i p] [PerfectRing M p]
  [IsPerfectClosure j p]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : L ≃+* M where
  body: PerfectRing.lift i j p
  invFun := PerfectRing.liftAux j i p
  left_inv := PerfectRing.lift_comp_lift_apply_eq_self i j p
  right_inv := PerfectRing.lift_comp_lift_apply_eq_self j i p

中文:
定义 equiv
  签名: : L ≃+* M where
  定义体: PerfectRing.lift i j p
  invFun := PerfectRing.liftAux j i p
  left_inv := PerfectRing.lift_comp_lift_apply_eq_self i j p
  right_inv := PerfectRing.lift_comp_lift_apply_eq_self j i p

Depends on / 依赖: PerfectRing, PerfectRing.lift
-/
def equiv : L ≃+* M where
  __ := PerfectRing.lift i j p
  invFun := PerfectRing.liftAux j i p
  left_inv := PerfectRing.lift_comp_lift_apply_eq_self i j p
  right_inv := PerfectRing.lift_comp_lift_apply_eq_self j i p

/--
theorem `equiv_toRingHom` / 定理 `equiv_toRingHom`

English:
theorem equiv_toRingHom
  statement: (equiv i j p).toRingHom = PerfectRing.lift i j p
  proof: rfl

@[simp]

中文:
定理 equiv_toRingHom
  结论: (equiv i j p).toRingHom = PerfectRing.lift i j p
  证明: rfl

@[simp]
-/
theorem equiv_toRingHom : (equiv i j p).toRingHom = PerfectRing.lift i j p := rfl

@[simp]
/--
theorem `equiv_symm` / 定理 `equiv_symm`

English:
theorem equiv_symm
  statement: (equiv i j p).symm = equiv j i p
  proof: rfl

中文:
定理 equiv_symm
  结论: (equiv i j p).symm = equiv j i p
  证明: rfl
-/
theorem equiv_symm : (equiv i j p).symm = equiv j i p := rfl

/--
theorem `equiv_symm_toRingHom` / 定理 `equiv_symm_toRingHom`

English:
theorem equiv_symm_toRingHom
  proof: rfl

中文:
定理 equiv_symm_toRingHom
  证明: rfl
-/
theorem equiv_symm_toRingHom :
    (equiv i j p).symm.toRingHom = PerfectRing.lift j i p := rfl

/--
theorem `equiv_apply` / 定理 `equiv_apply`

English:
theorem equiv_apply
  given: (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n)
  proof: PerfectRing.liftAux_apply i j p _ _ _ h

中文:
定理 equiv_apply
  条件: (x : L) (n : 自然数) (y : K) (h : i y = x ^ p ^ n)
  证明: PerfectRing.liftAux_apply i j p _ _ _ h

Depends on / 依赖: PerfectRing, PerfectRing.liftAux_apply, liftAux_apply
-/
theorem equiv_apply (x : L) (n : Nat) (y : K) (h : i y = x ^ p ^ n) :
    equiv i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  PerfectRing.liftAux_apply i j p _ _ _ h

/--
theorem `equiv_symm_apply` / 定理 `equiv_symm_apply`

English:
theorem equiv_symm_apply
  given: (x : M) (n : Nat) (y : K) (h : j y = x ^ p ^ n)
  proof: by
  rw [equiv_symm]; rw [equiv_apply j i p _ _ _ h]

中文:
定理 equiv_symm_apply
  条件: (x : M) (n : 自然数) (y : K) (h : j y = x ^ p ^ n)
  证明: by
  rw [equiv_symm]; rw [equiv_apply j i p _ _ _ h]

Depends on / 依赖: equiv_apply, equiv_symm
-/
theorem equiv_symm_apply (x : M) (n : Nat) (y : K) (h : j y = x ^ p ^ n) :
    (equiv i j p).symm x = (iterateFrobeniusEquiv L p n).symm (i y) := by
  rw [equiv_symm]; rw [equiv_apply j i p _ _ _ h]

/--
theorem `equiv_self_apply` / 定理 `equiv_self_apply`

English:
theorem equiv_self_apply
  given: (x : L)
  statement: equiv i i p x = x
  proof: PerfectRing.liftAux_self_apply i p x

@[simp]

中文:
定理 equiv_self_apply
  条件: (x : L)
  结论: equiv i i p x = x
  证明: PerfectRing.liftAux_self_apply i p x

@[simp]

Depends on / 依赖: PerfectRing, PerfectRing.liftAux_self_apply, liftAux_self_apply
-/
theorem equiv_self_apply (x : L) : equiv i i p x = x :=
  PerfectRing.liftAux_self_apply i p x

@[simp]
/--
theorem `equiv_self` / 定理 `equiv_self`

English:
theorem equiv_self
  statement: equiv i i p = RingEquiv.refl L
  proof: RingEquiv.ext (equiv_self_apply i p)

@[simp]

中文:
定理 equiv_self
  结论: equiv i i p = RingEquiv.refl L
  证明: RingEquiv.ext (equiv_self_apply i p)

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ext, equiv_self_apply
-/
theorem equiv_self : equiv i i p = RingEquiv.refl L :=
  RingEquiv.ext (equiv_self_apply i p)

@[simp]
/--
theorem `equiv_comp_apply` / 定理 `equiv_comp_apply`

English:
theorem equiv_comp_apply
  given: (x : K)
  statement: equiv i j p (i x) = j x
  proof: PerfectRing.lift_comp_apply i j p x

@[simp]

中文:
定理 equiv_comp_apply
  条件: (x : K)
  结论: equiv i j p (i x) = j x
  证明: PerfectRing.lift_comp_apply i j p x

@[simp]

Depends on / 依赖: PerfectRing, PerfectRing.lift_comp_apply, lift_comp_apply
-/
theorem equiv_comp_apply (x : K) : equiv i j p (i x) = j x :=
  PerfectRing.lift_comp_apply i j p x

@[simp]
/--
theorem `equiv_comp` / 定理 `equiv_comp`

English:
theorem equiv_comp
  statement: RingHom.comp (equiv i j p) i = j
  proof: RingHom.ext (equiv_comp_apply i j p)

中文:
定理 equiv_comp
  结论: RingHom.comp (equiv i j p) i = j
  证明: RingHom.ext (equiv_comp_apply i j p)

Depends on / 依赖: RingHom, RingHom.ext, equiv_comp_apply
-/
theorem equiv_comp : RingHom.comp (equiv i j p) i = j :=
  RingHom.ext (equiv_comp_apply i j p)

section comp

variable [ExpChar N p] [PerfectRing N p] [IsPerfectClosure k p]

@[simp]
/--
theorem `equiv_comp_equiv_apply` / 定理 `equiv_comp_equiv_apply`

English:
theorem equiv_comp_equiv_apply
  given: (x : L)
  proof: PerfectRing.lift_comp_lift_apply i j k p x

@[simp]

中文:
定理 equiv_comp_equiv_apply
  条件: (x : L)
  证明: PerfectRing.lift_comp_lift_apply i j k p x

@[simp]

Depends on / 依赖: PerfectRing, PerfectRing.lift_comp_lift_apply, lift_comp_lift_apply
-/
theorem equiv_comp_equiv_apply (x : L) :
    equiv j k p (equiv i j p x) = equiv i k p x :=
  PerfectRing.lift_comp_lift_apply i j k p x

@[simp]
/--
theorem `equiv_comp_equiv` / 定理 `equiv_comp_equiv`

English:
theorem equiv_comp_equiv
  statement: (equiv i j p).trans (equiv j k p) = equiv i k p
  proof: RingEquiv.ext (equiv_comp_equiv_apply i j k p)

中文:
定理 equiv_comp_equiv
  结论: (equiv i j p).trans (equiv j k p) = equiv i k p
  证明: RingEquiv.ext (equiv_comp_equiv_apply i j k p)

Depends on / 依赖: RingEquiv, RingEquiv.ext, equiv_comp_equiv_apply
-/
theorem equiv_comp_equiv : (equiv i j p).trans (equiv j k p) = equiv i k p :=
  RingEquiv.ext (equiv_comp_equiv_apply i j k p)

/--
theorem `equiv_comp_equiv_apply_eq_self` / 定理 `equiv_comp_equiv_apply_eq_self`

English:
theorem equiv_comp_equiv_apply_eq_self
  given: (x : L)
  proof: by
  rw [equiv_comp_equiv_apply]; rw [equiv_self_apply]

中文:
定理 equiv_comp_equiv_apply_eq_self
  条件: (x : L)
  证明: by
  rw [equiv_comp_equiv_apply]; rw [equiv_self_apply]

Depends on / 依赖: equiv_comp_equiv_apply, equiv_self_apply
-/
theorem equiv_comp_equiv_apply_eq_self (x : L) :
    equiv j i p (equiv i j p x) = x := by
  rw [equiv_comp_equiv_apply]; rw [equiv_self_apply]

/--
theorem `equiv_comp_equiv_eq_id` / 定理 `equiv_comp_equiv_eq_id`

English:
theorem equiv_comp_equiv_eq_id
  proof: RingEquiv.ext (equiv_comp_equiv_apply_eq_self i j p)

中文:
定理 equiv_comp_equiv_eq_id
  证明: RingEquiv.ext (equiv_comp_equiv_apply_eq_self i j p)

Depends on / 依赖: RingEquiv, RingEquiv.ext, equiv_comp_equiv_apply_eq_self
-/
theorem equiv_comp_equiv_eq_id :
    (equiv i j p).trans (equiv j i p) = RingEquiv.refl L :=
  RingEquiv.ext (equiv_comp_equiv_apply_eq_self i j p)

end comp

end IsPerfectClosure

end CommRing

namespace PerfectClosure

variable [CommRing K] (p : Nat) [Fact p.Prime] [CharP K p]
variable (K)

/--
Instance `isPRadical` / 实例 `isPRadical`

English:
instance isPRadical
  signature: : IsPRadical (PerfectClosure.of K p) p where
  body: PerfectClosure.induction_on x fun x => ⟨x.1, x.2, by
    rw [← iterate_frobenius]; rw [iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker]; rw [of_apply]; rw [zero_def]; rw [mk_eq_iff] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at

中文:
实例 isPRadical
  签名: : IsPRadical (PerfectClosure.of K p) p where
  定义体: PerfectClosure.induction_on x fun x => ⟨x.1, x.2, by
    rw [← iterate_frobenius]; rw [iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker]; rw [of_apply]; rw [zero_def]; rw [mk_eq_iff] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at

Depends on / 依赖: PerfectClosure, PerfectClosure.induction_on, RingHom, RingHom.mem_ker, coe_iterateFrobenius, induction_on, iterate_frobenius, iterate_frobenius_mk, ker_le, map_zero, mem_ker, mem_pNilradical, mk_eq_iff, of_apply, simp_rw, zero_add, zero_def
-/
instance isPRadical : IsPRadical (PerfectClosure.of K p) p where
  pow_mem' x := PerfectClosure.induction_on x fun x => ⟨x.1, x.2, by
    rw [← iterate_frobenius]; rw [iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker]; rw [of_apply]; rw [zero_def]; rw [mk_eq_iff] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at h
    exact mem_pNilradical.2 ⟨n, h⟩

end PerfectClosure

section Field

variable [Field K] [Field L] [Algebra K L] (p : Nat) [ExpChar K p]
variable (K L)

/--
theorem `IsPRadical.isPurelyInseparable` / 定理 `IsPRadical.isPurelyInseparable`

English:
theorem IsPRadical.isPurelyInseparable
  given: [IsPRadical (algebraMap K L) p]
  proof: (isPurelyInseparable_iff_pow_mem K p).2 (IsPRadical.pow_mem (algebraMap K L) p)

中文:
定理 IsPRadical.isPurelyInseparable
  条件: [IsPRadical (algebraMap K L) p]
  证明: (isPurelyInseparable_iff_pow_mem K p).2 (IsPRadical.pow_mem (algebraMap K L) p)

Depends on / 依赖: IsPRadical, IsPRadical.pow_mem, algebraMap, isPurelyInseparable_iff_pow_mem, pow_mem
-/
theorem IsPRadical.isPurelyInseparable [IsPRadical (algebraMap K L) p] :
    IsPurelyInseparable K L :=
  (isPurelyInseparable_iff_pow_mem K p).2 (IsPRadical.pow_mem (algebraMap K L) p)

/--
Instance `IsPurelyInseparable.isPRadical` / 实例 `IsPurelyInseparable.isPRadical`

English:
instance IsPurelyInseparable.isPRadical
  signature: [IsPurelyInseparable K L]
  body: (isPurelyInseparable_iff_pow_mem K p).1 ‹_›
  ker_le' := (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K L).injective ▸ bot_le

中文:
实例 IsPurelyInseparable.isPRadical
  签名: [IsPurelyInseparable K L]
  定义体: (isPurelyInseparable_iff_pow_mem K p).1 ‹_›
  ker_le' := (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K L).injective ▸ bot_le

Depends on / 依赖: isPurelyInseparable_iff_pow_mem
-/
instance IsPurelyInseparable.isPRadical [IsPurelyInseparable K L] :
    IsPRadical (algebraMap K L) p where
  pow_mem' := (isPurelyInseparable_iff_pow_mem K p).1 ‹_›
  ker_le' := (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K L).injective ▸ bot_le

end Field

end IsPerfectClosure
