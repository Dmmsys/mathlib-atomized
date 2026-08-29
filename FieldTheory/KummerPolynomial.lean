/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs

/-!
# Irreducibility of X ^ p - a

## Main result
- `X_pow_sub_C_irreducible_iff_of_prime`: For `p` prime, `X ^ p - C a` is irreducible iff `a` is not
  a `p`-power. This is not true for composite `n`. For example, `x^4+4=(x^2-2x+2)(x^2+2x+2)` but
  `-4` is not a 4th power.

-/

public section
universe u

variable {K : Type u} [Field K]

open Polynomial AdjoinRoot

section Splits

/--
lemma `root_X_pow_sub_C_pow` / 引理 `root_X_pow_sub_C_pow`

English:
lemma root_X_pow_sub_C_pow
  given: (n : Nat) (a : K)
  proof: by
  rw [← sub_eq_zero]; rw [← AdjoinRoot.eval₂_root]; rw [eval₂_sub]; rw [eval₂_C]; rw [eval₂_pow]; rw [eval₂_X]

中文:
引理 root_X_pow_sub_C_pow
  条件: (n : 自然数) (a : K)
  证明: by
  rw [← sub_eq_zero]; rw [← AdjoinRoot.eval₂_root]; rw [eval₂_sub]; rw [eval₂_C]; rw [eval₂_pow]; rw [eval₂_X]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.eval, sub_eq_zero
-/
lemma root_X_pow_sub_C_pow (n : Nat) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a := by
  rw [← sub_eq_zero]; rw [← AdjoinRoot.eval₂_root]; rw [eval₂_sub]; rw [eval₂_C]; rw [eval₂_pow]; rw [eval₂_X]

/--
lemma `root_X_pow_sub_C_ne_zero` / 引理 `root_X_pow_sub_C_ne_zero`

English:
lemma root_X_pow_sub_C_ne_zero
  given: {n : Nat} (hn : 1 < n) (a : K)
  proof: mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.ne_zero_of_lt hn))
X_ne_zero by rwa [natDegree_X_pow_sub_C, natDegree_X]

中文:
引理 root_X_pow_sub_C_ne_zero
  条件: {n : 自然数} (hn : 1 < n) (a : K)
  证明: mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.ne_zero_of_lt hn))
X_ne_zero by rwa [natDegree_X_pow_sub_C, natDegree_X]

Depends on / 依赖: Nat.ne_zero_of_lt, X_ne_zero, mk_ne_zero_of_natDegree_lt, monic_X_pow_sub_C, natDegree_X, natDegree_X_pow_sub_C, ne_zero_of_lt
-/
lemma root_X_pow_sub_C_ne_zero {n : Nat} (hn : 1 < n) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) != 0 :=
  mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.ne_zero_of_lt hn))
X_ne_zero by rwa [natDegree_X_pow_sub_C, natDegree_X]

/--
lemma `root_X_pow_sub_C_ne_zero'` / 引理 `root_X_pow_sub_C_ne_zero'`

English:
lemma root_X_pow_sub_C_ne_zero'
  given: {n : Nat} {a : K} (hn : 0 < n) (ha : a != 0)
  proof: by
  obtain (rfl | hn) := (Nat.succ_le_iff.mpr hn).eq_or_lt
  · rw [pow_one]
    intro e
    refine mk_ne_zero_of_natDegree_lt (monic_X_sub_C a) (C_ne_zero.mpr ha) (by simp) ?_
    trans AdjoinRoot.mk (X - C a) (X - (X - C a))
    · rw [sub_sub_cancel]
    · rw [map_sub, mk_self, sub_zero, mk_X, e]


中文:
引理 root_X_pow_sub_C_ne_zero'
  条件: {n : 自然数} {a : K} (hn : 0 < n) (ha : a != 0)
  证明: by
  obtain (rfl | hn) := (Nat.succ_le_iff.mpr hn).eq_or_lt
  · rw [pow_one]
    intro e
    refine mk_ne_zero_of_natDegree_lt (monic_X_sub_C a) (C_ne_zero.mpr ha) (by simp) ?_
    trans AdjoinRoot.mk (X - C a) (X - (X - C a))
    · rw [sub_sub_cancel]
    · rw [map_sub, mk_self, sub_zero, mk_X, e]


Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, C_ne_zero, C_ne_zero.mpr, Nat.succ_le_iff.mpr, eq_or_lt, map_sub, mk_X, mk_ne_zero_of_natDegree_lt, mk_self, monic_X_sub_C, pow_one, root_X_pow_sub_C_ne_zero, sub_sub_cancel, sub_zero, succ_le_iff
-/
lemma root_X_pow_sub_C_ne_zero' {n : Nat} {a : K} (hn : 0 < n) (ha : a != 0) :
    (AdjoinRoot.root (X ^ n - C a)) != 0 := by
  obtain (rfl | hn) := (Nat.succ_le_iff.mpr hn).eq_or_lt
  · rw [pow_one]
    intro e
    refine mk_ne_zero_of_natDegree_lt (monic_X_sub_C a) (C_ne_zero.mpr ha) (by simp) ?_
    trans AdjoinRoot.mk (X - C a) (X - (X - C a))
    · rw [sub_sub_cancel]
    · rw [map_sub, mk_self, sub_zero, mk_X, e]
  · exact root_X_pow_sub_C_ne_zero hn a

end Splits

section Irreducible

/--
lemma `ne_zero_of_irreducible_X_pow_sub_C` / 引理 `ne_zero_of_irreducible_X_pow_sub_C`

English:
lemma ne_zero_of_irreducible_X_pow_sub_C
  given: {n : Nat} {a : K} (H : Irreducible (X ^ n - C a))
  proof: by
  rintro rfl
  rw [pow_zero]; rw [← C.map_one]; rw [← map_sub] at H
  exact not_irreducible_C _ H

中文:
引理 ne_zero_of_irreducible_X_pow_sub_C
  条件: {n : 自然数} {a : K} (H : 不可约 (X ^ n - C a))
  证明: by
  rintro rfl
  rw [pow_zero]; rw [← C.map_one]; rw [← map_sub] at H
  exact not_irreducible_C _ H

Depends on / 依赖: C.map_one, map_one, map_sub, not_irreducible_C, pow_zero
-/
lemma ne_zero_of_irreducible_X_pow_sub_C {n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) :
    n != 0 := by
  rintro rfl
  rw [pow_zero]; rw [← C.map_one]; rw [← map_sub] at H
  exact not_irreducible_C _ H

/--
lemma `ne_zero_of_irreducible_X_pow_sub_C'` / 引理 `ne_zero_of_irreducible_X_pow_sub_C'`

English:
lemma ne_zero_of_irreducible_X_pow_sub_C'
  statement: {n : Nat} (hn : n != 1) {a : K}
  proof: by
  rintro rfl
  rw [map_zero]; rw [sub_zero] at H
  exact not_irreducible_pow hn H

中文:
引理 ne_zero_of_irreducible_X_pow_sub_C'
  结论: {n : 自然数} (hn : n != 1) {a : K}
  证明: by
  rintro rfl
  rw [map_zero]; rw [sub_zero] at H
  exact not_irreducible_pow hn H

Depends on / 依赖: map_zero, not_irreducible_pow, sub_zero
-/
lemma ne_zero_of_irreducible_X_pow_sub_C' {n : Nat} (hn : n != 1) {a : K}
    (H : Irreducible (X ^ n - C a)) : a != 0 := by
  rintro rfl
  rw [map_zero]; rw [sub_zero] at H
  exact not_irreducible_pow hn H

/--
lemma `root_X_pow_sub_C_eq_zero_iff` / 引理 `root_X_pow_sub_C_eq_zero_iff`

English:
lemma root_X_pow_sub_C_eq_zero_iff
  given: {n : Nat} {a : K} (H : Irreducible (X ^ n - C a))
  proof: by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn => ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this]; rw [pow_one]; rw [map_zero]; rw [sub_zero]; rw [← mk

中文:
引理 root_X_pow_sub_C_eq_zero_iff
  条件: {n : 自然数} {a : K} (H : 不可约 (X ^ n - C a))
  证明: by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn => ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this]; rw [pow_one]; rw [map_zero]; rw [sub_zero]; rw [← mk

Depends on / 依赖: Nat.pos_iff_ne_zero.mpr, map_zero, mk_X, mk_self, ne_zero_of_irreducible_X_pow_sub_C, not_imp_not, not_imp_not.mp, pos_iff_ne_zero, pow_one, root_X_pow_sub_C_ne_zero, sub_zero
-/
lemma root_X_pow_sub_C_eq_zero_iff {n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a = 0 := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn => ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this]; rw [pow_one]; rw [map_zero]; rw [sub_zero]; rw [← mk_X]; rw [mk_self]

/--
lemma `root_X_pow_sub_C_ne_zero_iff` / 引理 `root_X_pow_sub_C_ne_zero_iff`

English:
lemma root_X_pow_sub_C_ne_zero_iff
  given: {n : Nat} {a : K} (H : Irreducible (X ^ n - C a))
  proof: (root_X_pow_sub_C_eq_zero_iff H).not

中文:
引理 root_X_pow_sub_C_ne_zero_iff
  条件: {n : 自然数} {a : K} (H : 不可约 (X ^ n - C a))
  证明: (root_X_pow_sub_C_eq_zero_iff H).not

Depends on / 依赖: root_X_pow_sub_C_eq_zero_iff
-/
lemma root_X_pow_sub_C_ne_zero_iff {n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) != 0 ↔ a != 0 :=
  (root_X_pow_sub_C_eq_zero_iff H).not

/--
theorem `pow_ne_of_irreducible_X_pow_sub_C` / 定理 `pow_ne_of_irreducible_X_pow_sub_C`

English:
theorem pow_ne_of_irreducible_X_pow_sub_C
  statement: {n : Nat} {a : K}
  proof: by
  have hn : n != 0 := fun e => not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm]; rw [pow_mul]; rw [map_pow]; rw [hq] at H
  have : degree q = 0 :

中文:
定理 pow_ne_of_irreducible_X_pow_sub_C
  结论: {n : 自然数} {a : K}
  证明: by
  have hn : n != 0 := fun e => not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm]; rw [pow_mul]; rw [map_pow]; rw [hq] at H
  have : degree q = 0 :

Depends on / 依赖: C.map_one, Nat.pos_if, Nat.pos_iff_ne_zero, apply_fun, degree, degree_X_pow_sub_C, isUnit_iff_degree_eq_zero, map_one, map_pow, map_sub, mul_comm, mul_ne_zero_iff, mul_ne_zero_iff.mp, not_irreducible_C, pos_if, pos_iff_ne_zero, pow_mul, pow_zero, sub_dvd_pow_sub_pow
-/
theorem pow_ne_of_irreducible_X_pow_sub_C {n : Nat} {a : K}
    (H : Irreducible (X ^ n - C a)) {m : Nat} (hm : m ∣ n) (hm' : m != 1) (b : K) : b ^ m != a := by
  have hn : n != 0 := fun e => not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm]; rw [pow_mul]; rw [map_pow]; rw [hq] at H
  have : degree q = 0 := by
    simpa [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C,
      Nat.pos_iff_ne_zero, (mul_ne_zero_iff.mp hn).2] using H.2 rfl
  apply_fun degree at hq
  simp only [this, ← pow_mul, mul_comm k m, degree_X_pow_sub_C, Nat.pos_iff_ne_zero.mpr hn,
    Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2, degree_mul, ← map_pow, add_zero,
    Nat.cast_injective.eq_iff] at hq
  exact hm' ((mul_eq_right₀ (mul_ne_zero_iff.mp hn).2).mp hq)

/-- Let `p` be a prime number. Let `K` be a field.
Let `t ∈ K` be an element which does not have a `p`th root in `K`.
Then the polynomial `x ^ p - t` is irreducible over `K`. -/
@[stacks 09HF "We proved the result without the condition that `K` is char p in 09HF."]
/--
theorem `X_pow_sub_C_irreducible_of_prime` / 定理 `X_pow_sub_C_irreducible_of_prime`

English:
theorem X_pow_sub_C_irreducible_of_prime
  given: {p : Nat} (hp : p.Prime) {a : K} (ha : forall b : K, b ^ p != a)
  proof: by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]; rw [degree_X_pow_sub_C hp.pos]; rw [Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor t

中文:
定理 X_pow_sub_C_irreducible_of_prime
  条件: {p : 自然数} (hp : p.素) {a : K} (ha : 对任意 b : K, b ^ p != a)
  证明: by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]; rw [degree_X_pow_sub_C hp.pos]; rw [Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor t
-/
theorem X_pow_sub_C_irreducible_of_prime {p : Nat} (hp : p.Prime) {a : K} (ha : forall b : K, b ^ p != a) :
    Irreducible (X ^ p - C a) := by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]; rw [degree_X_pow_sub_C hp.pos]; rw [Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  -- It suffices to show that `deg g = p`.
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_le hg'
    (X_pow_sub_C_ne_zero hp.pos a) (this.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg
  -- Suppose `deg g ≠ p`.
  by_contra h
  -- Let `r` be a root of `g`, then `N_K(r) ^ p = N_K(r ^ p) = N_K(a) = a ^ (deg g)`.
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree := by
    have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub]; rw [eval₂_pow]; rw [eval₂_C]; rw [eval₂_X]; rw [sub_eq_zero] at this
    rw [← map_pow]; rw [this]; rw [← AdjoinRoot.algebraMap_eq]; rw [Algebra.norm_algebraMap]; rw [(powerBasis hg.ne_zero).finrank]; rw [powerBasis_dim hg.ne_zero]
  -- Since `a ^ (deg g)` is a `p`-power, and `p` is coprime to `deg g`, we conclude that `a` is
  -- also a `p`-power, contradicting the hypothesis
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e => h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ ((pow_mem_range_pow_of_coprime this.symm a).mp ⟨_, key⟩).choose_spec

/--
theorem `X_pow_sub_C_irreducible_iff_of_prime` / 定理 `X_pow_sub_C_irreducible_iff_of_prime`

English:
theorem X_pow_sub_C_irreducible_iff_of_prime
  given: {p : Nat} (hp : p.Prime) {a : K}
  proof: ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩

中文:
定理 X_pow_sub_C_irreducible_iff_of_prime
  条件: {p : 自然数} (hp : p.素) {a : K}
  证明: ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩

Depends on / 依赖: X_pow_sub_C_irreducible_of_prime, dvd_rfl, hp.ne_one, ne_one, pow_ne_of_irreducible_X_pow_sub_C
-/
theorem X_pow_sub_C_irreducible_iff_of_prime {p : Nat} (hp : p.Prime) {a : K} :
    Irreducible (X ^ p - C a) ↔ forall b, b ^ p != a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩

end Irreducible
