/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary submodules

A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.

## Main results

* `Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`:
  A `N : Submodule R M` is primary if any zero divisor on `M ⧸ N` is nilpotent.
  See https://mathoverflow.net/questions/3910/primary-decomposition-for-modules
  for a comparison of this definition (a la Atiyah-Macdonald) vs "locally nilpotent" (Matsumura).

## Implementation details

This is a generalization of `Ideal.IsPrimary`. For brevity, the pointwise instances are used
to define the nilpotency of `r : R`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
  Chapter 4, Exercise 21.

-/

@[expose] public section

open scoped Pointwise

namespace Submodule

open Ideal

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `IsPrimary` / `IsPrimary` 的定义

English:
definition IsPrimary
  signature: (S : Submodule R M)
  body: S != ⊤ ∧ forall {r : R} {x : M}, r • x in S -> x in S ∨ exists n : Nat, (r ^ n • ⊤ : Submodule R M) <= S

中文:
定义 是准素
  签名: (S : 子模 R M)
  定义体: S != ⊤ ∧ forall {r : R} {x : M}, r • x in S -> x in S ∨ exists n : Nat, (r ^ n • ⊤ : Submodule R M) <= S
-/
protected def IsPrimary (S : Submodule R M) : Prop :=
  S != ⊤ ∧ forall {r : R} {x : M}, r • x in S -> x in S ∨ exists n : Nat, (r ^ n • ⊤ : Submodule R M) <= S

variable {S T : Submodule R M}

/--
lemma `IsPrimary.ne_top` / 引理 `IsPrimary.ne_top`

English:
lemma IsPrimary.ne_top
  given: (h : S.IsPrimary)
  statement: S != ⊤
  proof: h.left

中文:
引理 是准素.ne_top
  条件: (h : S.是准素)
  结论: S != ⊤
  证明: h.left

Depends on / 依赖: h.left
-/
lemma IsPrimary.ne_top (h : S.IsPrimary) : S != ⊤ := h.left

/--
lemma `IsPrimary.mem_or_mem` / 引理 `IsPrimary.mem_or_mem`

English:
lemma IsPrimary.mem_or_mem
  given: (h : S.IsPrimary) {r : R} {m : M} (hrm : r • m in S)
  proof: h.right hrm

中文:
引理 是准素.mem_or_mem
  条件: (h : S.是准素) {r : R} {m : M} (hrm : r • m in S)
  证明: h.right hrm

Depends on / 依赖: h.right
-/
lemma IsPrimary.mem_or_mem (h : S.IsPrimary) {r : R} {m : M} (hrm : r • m in S) :
    m in S ∨ r in (S.colon Set.univ).radical :=
  h.right hrm

/--
lemma `IsPrimary.inf` / 引理 `IsPrimary.inf`

English:
lemma IsPrimary.inf
  statement: (hS : S.IsPrimary) (hT : T.IsPrimary)
  proof: by
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  refine ⟨by grind, fun ⟨hS', hT'⟩ => ?_⟩
  simp_rw [← mem_colon_iff_le, ← Ideal.mem_radical_iff, inf_colon, Ideal.radical_inf,
    top_coe, h, inf_idem, mem_inf, and_or_right] at hS hT ⊢
  exact ⟨hS hS', hT hT'⟩

中文:
引理 是准素.下确界
  结论: (hS : S.是准素) (hT : T.是准素)
  证明: by
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  refine ⟨by grind, fun ⟨hS', hT'⟩ => ?_⟩
  simp_rw [← mem_colon_iff_le, ← Ideal.mem_radical_iff, inf_colon, Ideal.radical_inf,
    top_coe, h, inf_idem, mem_inf, and_or_right] at hS hT ⊢
  exact ⟨hS hS', hT hT'⟩
-/
protected lemma IsPrimary.inf (hS : S.IsPrimary) (hT : T.IsPrimary)
    (h : (S.colon Set.univ).radical = (T.colon Set.univ).radical) :
    (S ⊓ T).IsPrimary := by
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  refine ⟨by grind, fun ⟨hS', hT'⟩ => ?_⟩
  simp_rw [← mem_colon_iff_le, ← Ideal.mem_radical_iff, inf_colon, Ideal.radical_inf,
    top_coe, h, inf_idem, mem_inf, and_or_right] at hS hT ⊢
  exact ⟨hS hS', hT hT'⟩

open Finset in
/--
lemma `isPrimary_finsetInf` / 引理 `isPrimary_finsetInf`

English:
lemma isPrimary_finsetInf
  statement: {ι : Type*} {s : Finset ι} {f : ι -> Submodule R M} {i : ι} (hi : i in s)
  proof: by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simp at hi
  | insert a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [insert_empty_eq, mem_singleton] at hi
      simpa [hi] using hs
    simp only [inf_insert]
    have H ⦃x⦄ (hx : x in s) : ((f x).colon Set.univ).radical = ((f y).colon Set.univ).radical := by
      rw [hs' (mem_insert_of_mem hx)]; rw [hs' (mem_insert_of_mem hy)]
    refine IsPrimary.inf (hs (by simp)) (IH hy (fun x hx => hs (by simp [hx])) H) ?_
    rw [colon_finsetInf]; rw [Ideal.radical_finset_inf hy H]; rw [hs' (mem_insert_self _ _)]; rw [hs' (mem_insert_of_mem hy)]

中文:
引理 isPrimary_finsetInf
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 子模 R M} {i : ι} (hi : i in s)
  证明: by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simp at hi
  | insert a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [insert_empty_eq, mem_singleton] at hi
      simpa [hi] using hs
    simp only [inf_insert]
    have H ⦃x⦄ (hx : x in s) : ((f x).colon Set.univ).radical = ((f y).colon Set.univ).radical := by
      rw [hs' (mem_insert_of_mem hx)]; rw [hs' (mem_insert_of_mem hy)]
    refine IsPrimary.inf (hs (by simp)) (IH hy (fun x hx => hs (by simp [hx])) H) ?_
    rw [colon_finsetInf]; rw [Ideal.radical_finset_inf hy H]; rw [hs' (mem_insert_self _ _)]; rw [hs' (mem_insert_of_mem hy)]

Depends on / 依赖: Finset, Finset.induction_on, IsPrimary, IsPrimary.inf, Set.univ, classical, eq_empty_or_nonempty, generalizing, induction_on, inf_insert, insert, insert_empty_eq, mem_insert_of_mem, mem_singleton, radical, s.eq_empty_or_nonempty
-/
lemma isPrimary_finsetInf {ι : Type*} {s : Finset ι} {f : ι -> Submodule R M} {i : ι} (hi : i in s)
    (hs : forall ⦃y⦄, y in s -> (f y).IsPrimary)
    (hs' : forall ⦃y⦄, y in s -> ((f y).colon Set.univ).radical = ((f i).colon Set.univ).radical) :
    (s.inf f).IsPrimary := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simp at hi
  | insert a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [insert_empty_eq, mem_singleton] at hi
      simpa [hi] using hs
    simp only [inf_insert]
    have H ⦃x⦄ (hx : x in s) : ((f x).colon Set.univ).radical = ((f y).colon Set.univ).radical := by
      rw [hs' (mem_insert_of_mem hx)]; rw [hs' (mem_insert_of_mem hy)]
    refine IsPrimary.inf (hs (by simp)) (IH hy (fun x hx => hs (by simp [hx])) H) ?_
    rw [colon_finsetInf]; rw [Ideal.radical_finset_inf hy H]; rw [hs' (mem_insert_self _ _)]; rw [hs' (mem_insert_of_mem hy)]

/--
theorem `IsPrimary.isPrime_radical_colon` / 定理 `IsPrimary.isPrime_radical_colon`

English:
theorem IsPrimary.isPrime_radical_colon
  given: (hI : S.IsPrimary)
  statement: (S.colon .univ).radical.IsPrime
  proof: by
refine isPrime_iff.mpr hI.imp (by simp) fun h x y ⟨n, hn⟩ => ?_
  simp_rw [← mem_colon_iff_le, ← mem_radical_iff] at h
  refine or_iff_not_imp_left.mpr fun hx => ⟨n, ?_⟩
  simp only [mul_pow, mem_colon, Set.mem_univ, true_imp_iff, mul_smul] at hn ⊢
  exact fun p => (h (hn p)).resolve_right (mt mem_radical_of_pow_mem hx)

中文:
定理 是准素.isPrime_radical_colon
  条件: (hI : S.是准素)
  结论: (S.colon .univ).radical.是素
  证明: by
refine isPrime_iff.mpr hI.imp (by simp) fun h x y ⟨n, hn⟩ => ?_
  simp_rw [← mem_colon_iff_le, ← mem_radical_iff] at h
  refine or_iff_not_imp_left.mpr fun hx => ⟨n, ?_⟩
  simp only [mul_pow, mem_colon, Set.mem_univ, true_imp_iff, mul_smul] at hn ⊢
  exact fun p => (h (hn p)).resolve_right (mt mem_radical_of_pow_mem hx)

Depends on / 依赖: Set.mem_univ, hI.imp, isPrime_iff, isPrime_iff.mpr, mem_colon, mem_colon_iff_le, mem_radical_iff, mem_radical_of_pow_mem, mem_univ, mul_pow, mul_smul, or_iff_not_imp_left, or_iff_not_imp_left.mpr, resolve_right, simp_rw, true_imp_iff
-/
theorem IsPrimary.isPrime_radical_colon (hI : S.IsPrimary) : (S.colon .univ).radical.IsPrime := by
refine isPrime_iff.mpr hI.imp (by simp) fun h x y ⟨n, hn⟩ => ?_
  simp_rw [← mem_colon_iff_le, ← mem_radical_iff] at h
  refine or_iff_not_imp_left.mpr fun hx => ⟨n, ?_⟩
  simp only [mul_pow, mem_colon, Set.mem_univ, true_imp_iff, mul_smul] at hn ⊢
  exact fun p => (h (hn p)).resolve_right (mt mem_radical_of_pow_mem hx)

/--
theorem `IsPrimary.radical_colon_singleton_of_notMem` / 定理 `IsPrimary.radical_colon_singleton_of_notMem`

English:
theorem IsPrimary.radical_colon_singleton_of_notMem
  given: (hI : S.IsPrimary) {m : M} (hm : m ∉ S)
  proof: le_antisymm (radical_le_radical_iff.mpr fun _ hy =>
    (hI.2 (Submodule.mem_colon_singleton.mp hy)).resolve_left hm)
    (radical_mono (Submodule.colon_mono le_rfl (Set.subset_univ {m})))

中文:
定理 是准素.radical_colon_singleton_of_notMem
  条件: (hI : S.是准素) {m : M} (hm : m ∉ S)
  证明: le_antisymm (radical_le_radical_iff.mpr fun _ hy =>
    (hI.2 (Submodule.mem_colon_singleton.mp hy)).resolve_left hm)
    (radical_mono (Submodule.colon_mono le_rfl (Set.subset_univ {m})))

Depends on / 依赖: Set.subset_univ, Submodule, Submodule.colon_mono, Submodule.mem_colon_singleton.mp, colon_mono, le_antisymm, le_rfl, mem_colon_singleton, radical_le_radical_iff, radical_le_radical_iff.mpr, radical_mono, resolve_left, subset_univ
-/
theorem IsPrimary.radical_colon_singleton_of_notMem (hI : S.IsPrimary) {m : M} (hm : m ∉ S) :
    (S.colon {m}).radical = (S.colon Set.univ).radical :=
  le_antisymm (radical_le_radical_iff.mpr fun _ hy =>
    (hI.2 (Submodule.mem_colon_singleton.mp hy)).resolve_left hm)
    (radical_mono (Submodule.colon_mono le_rfl (Set.subset_univ {m})))

/--
theorem `IsPrimary.radical_colon_singleton_eq_ite` / 定理 `IsPrimary.radical_colon_singleton_eq_ite`

English:
theorem IsPrimary.radical_colon_singleton_eq_ite
  given: (hS : S.IsPrimary) (m : M) [Decidable (m in S)]
  proof: by
  split_ifs with hm
  · rwa [radical_eq_top, colon_eq_top_iff_subset, Set.singleton_subset_iff]
  · exact hS.radical_colon_singleton_of_notMem hm

中文:
定理 是准素.radical_colon_singleton_eq_ite
  条件: (hS : S.是准素) (m : M) [可判定 (m in S)]
  证明: by
  split_ifs with hm
  · rwa [radical_eq_top, colon_eq_top_iff_subset, Set.singleton_subset_iff]
  · exact hS.radical_colon_singleton_of_notMem hm

Depends on / 依赖: Set.singleton_subset_iff, colon_eq_top_iff_subset, hS.radical_colon_singleton_of_notMem, radical_colon_singleton_of_notMem, radical_eq_top, singleton_subset_iff, split_ifs
-/
theorem IsPrimary.radical_colon_singleton_eq_ite (hS : S.IsPrimary) (m : M) [Decidable (m in S)] :
    radical (S.colon {m}) = if m in S then ⊤ else radical (S.colon Set.univ) := by
  split_ifs with hm
  · rwa [radical_eq_top, colon_eq_top_iff_subset, Set.singleton_subset_iff]
  · exact hS.radical_colon_singleton_of_notMem hm

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul` / 引理 `isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`

English:
lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul
  proof: by
  refine (and_congr_right fun _ => ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm]; rw [← or_iff_not_imp_left]; rw [← LinearMap.range_eq_top.mpr S.mkQ_surjective]; rw [← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]

中文:
引理 isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul
  证明: by
  refine (and_congr_right fun _ => ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm]; rw [← or_iff_not_imp_left]; rw [← LinearMap.range_eq_top.mpr S.mkQ_surjective]; rw [← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, LinearMap.range_eq_top.mpr, S.mkQ_surjective, S.mkQ_surjective.forall, and_congr_right, comap_bot, eq_bot_iff, forall_comm, ker_mkQ, map_le_iff_le_comap, map_pointwise_smul, map_smul, map_top, mem_ker, mkQ_surjective, ne_eq, or_iff_not_imp_left, range_eq_top, simp_rw
-/
lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul :
    S.IsPrimary ↔ S != ⊤ ∧ forall (r : R) (x : M ⧸ S), x != 0 -> r • x = 0 ->
      exists n : Nat, r ^ n • (⊤ : Submodule R (M ⧸ S)) = ⊥ := by
  refine (and_congr_right fun _ => ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm]; rw [← or_iff_not_imp_left]; rw [← LinearMap.range_eq_top.mpr S.mkQ_surjective]; rw [← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]

end CommRing

end Submodule
