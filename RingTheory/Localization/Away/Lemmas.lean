/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-!
# More lemmas on localization away

This file contains lemmas on localization away from an element requiring more imports.

-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace IsLocalization.Away

/--
Definition of `mulNumerator` / `mulNumerator` 的定义

English:
definition mulNumerator
  signature: (s : Set R)
  body: x.1 * (IsLocalization.Away.sec x.1.1 x.2.1).1

中文:
定义 mulNumerator
  签名: (s : 集合 R)
  定义体: x.1 * (IsLocalization.Away.sec x.1.1 x.2.1).1

Depends on / 依赖: IsLocalization, IsLocalization.Away.sec
-/
noncomputable def mulNumerator (s : Set R)
    {Rₜ : s -> Type*} [forall t, CommRing (Rₜ t)] [forall t, Algebra R (Rₜ t)]
    [forall t, IsLocalization.Away t.val (Rₜ t)]
    (p : (t : s) -> Set (Rₜ t)) (x : (t : s) × p t) : R :=
  x.1 * (IsLocalization.Away.sec x.1.1 x.2.1).1

/--
lemma `span_range_mulNumerator_eq_top` / 引理 `span_range_mulNumerator_eq_top`

English:
lemma span_range_mulNumerator_eq_top
  statement: {s : Set R}
  proof: by
  rw [← Ideal.radical_eq_top]; rw [eq_top_iff]; rw [← hsone]; rw [Ideal.span_le]
  intro a ha
  have : IsLocalization (Submonoid.powers a) (Rₜ ⟨a, ha⟩) :=
inferInstanceAs IsLocalization.Away (⟨a, ha⟩ : s).val (Rₜ ⟨a, ha⟩)
  have h₁ : Ideal.span (p ⟨a, ha⟩) <= Ideal.span
      (algebraMap R (Rₜ ⟨a

中文:
引理 span_range_mulNumerator_eq_top
  结论: {s : 集合 R}
  证明: by
  rw [← Ideal.radical_eq_top]; rw [eq_top_iff]; rw [← hsone]; rw [Ideal.span_le]
  intro a ha
  have : IsLocalization (Submonoid.powers a) (Rₜ ⟨a, ha⟩) :=
inferInstanceAs IsLocalization.Away (⟨a, ha⟩ : s).val (Rₜ ⟨a, ha⟩)
  have h₁ : Ideal.span (p ⟨a, ha⟩) <= Ideal.span
      (algebraMap R (Rₜ ⟨a

Depends on / 依赖: Ideal.radical_eq_top, Ideal.span, Ideal.span_le, IsLocalization, IsLocalization.Away, IsLocalization.Away.mulNumerator, IsLocalization.Away.sec, IsLocalization.mem_span_map, Set.range, SetLike, SetLike.mem_coe, Submonoid, Submonoid.powers, algebraMap, eq_top_iff, mem_coe, mem_span_map, mulNumerator, powers, radical_eq_top
-/
lemma span_range_mulNumerator_eq_top {s : Set R}
    (hsone : Ideal.span s = ⊤) {Rₜ : s -> Type*} [forall t, CommRing (Rₜ t)] [forall t, Algebra R (Rₜ t)]
    [forall t, IsLocalization.Away t.val (Rₜ t)]
    {p : (t : s) -> Set (Rₜ t)} (htone : forall (r : s), Ideal.span (p r) = ⊤) :
    Ideal.span (Set.range (IsLocalization.Away.mulNumerator s p)) = ⊤ := by
  rw [← Ideal.radical_eq_top]; rw [eq_top_iff]; rw [← hsone]; rw [Ideal.span_le]
  intro a ha
  have : IsLocalization (Submonoid.powers a) (Rₜ ⟨a, ha⟩) :=
inferInstanceAs IsLocalization.Away (⟨a, ha⟩ : s).val (Rₜ ⟨a, ha⟩)
  have h₁ : Ideal.span (p ⟨a, ha⟩) <= Ideal.span
      (algebraMap R (Rₜ ⟨a, ha⟩) '' Set.range (IsLocalization.Away.mulNumerator s p)) := by
    rw [Ideal.span_le]
    intro x hx
    rw [SetLike.mem_coe]; rw [IsLocalization.mem_span_map (Submonoid.powers a)]
    refine ⟨a * (IsLocalization.Away.sec a x).1, Ideal.subset_span ⟨⟨⟨a, ha⟩, ⟨x, hx⟩⟩, rfl⟩, ?_⟩
    use ⟨a ^ ((IsLocalization.Away.sec a x).2 + 1), _, rfl⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [map_pow]; rw [map_mul]; rw [← map_pow]; rw [pow_add]; rw [map_mul]; rw [← mul_assoc]; rw [IsLocalization.Away.sec_spec a x]; rw [mul_comm]; rw [pow_one]
  have h₂ : IsLocalization.mk' (Rₜ ⟨a, ha⟩) 1 (1 : Submonoid.powers a) in Ideal.span
      (algebraMap R (Rₜ ⟨a, ha⟩) ''
        (Set.range <| IsLocalization.Away.mulNumerator s p)) := by
    rw [IsLocalization.mk'_one]
    apply h₁
    simp [htone]
  rw [IsLocalization.mem_span_map (Submonoid.powers a)] at h₂
  obtain ⟨y, hy, ⟨-, m, rfl⟩, hyz⟩ := h₂
  rw [IsLocalization.eq] at hyz
  obtain ⟨⟨-, n, rfl⟩, hc⟩ := hyz
  simp only [OneMemClass.coe_one, one_mul, mul_one] at hc
  use n + m
  simpa [pow_add, hc] using Ideal.mul_mem_left _ _ hy

/--
lemma `quotient_of_isIdempotentElem` / 引理 `quotient_of_isIdempotentElem`

English:
lemma quotient_of_isIdempotentElem
  given: {e : R} (he : IsIdempotentElem e)
  proof: away_of_isIdempotentElem he Ideal.mk_ker Quotient.mk_surjective

中文:
引理 quotient_of_isIdempotentElem
  条件: {e : R} (he : IsIdempotentElem e)
  证明: away_of_isIdempotentElem he Ideal.mk_ker Quotient.mk_surjective

Depends on / 依赖: Ideal.mk_ker, Quotient, Quotient.mk_surjective, away_of_isIdempotentElem, completeSpace_coe, isClosed_closure, isClosed_closure.completeSpace_coe, mk_ker, mk_surjective
-/
lemma quotient_of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    IsLocalization.Away e (R ⧸ Ideal.span {1 - e}) :=
  away_of_isIdempotentElem he Ideal.mk_ker Quotient.mk_surjective

end IsLocalization.Away

section saturated

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
  [Algebra R S] (x : R) [IsLocalization.Away x S] {I J : Ideal R}

/--
lemma `Ideal.le_of_map_algebraMap_le` / 引理 `Ideal.le_of_map_algebraMap_le`

English:
lemma Ideal.le_of_map_algebraMap_le
  statement: (hle : I.map (algebraMap R S) <= J.map (algebraMap R S))
  proof: by
  intro y hy
  have hin : algebraMap R S y in I.map (algebraMap R S) := Ideal.mem_map_of_mem (algebraMap R S) hy
  grw [hle, IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers x)] at hin
  obtain ⟨m, ⟨n, hn, rfl⟩, h⟩ := hin
  dsimp at h
  induction n with
  | zero => simpa using h

中文:
引理 理想.le_of_map_algebraMap_le
  结论: (hle : I.map (algebraMap R S) <= J.map (algebraMap R S))
  证明: by
  intro y hy
  have hin : algebraMap R S y in I.map (algebraMap R S) := Ideal.mem_map_of_mem (algebraMap R S) hy
  grw [hle, IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers x)] at hin
  obtain ⟨m, ⟨n, hn, rfl⟩, h⟩ := hin
  dsimp at h
  induction n with
  | zero => simpa using h

Depends on / 依赖: I.map, Ideal.mem_map_of_mem, IsLocalization, IsLocalization.algebraMap_mem_map_algebraMap_iff, Submonoid, Submonoid.powers, add_comm, algebraMap, algebraMap_mem_map_algebraMap_iff, mem_map_of_mem, mul_assoc, pow_add, pow_one, powers
-/
lemma Ideal.le_of_map_algebraMap_le (hle : I.map (algebraMap R S) <= J.map (algebraMap R S))
    (hxJ : forall y : R, x * y in J -> y in J) : I <= J := by
  intro y hy
  have hin : algebraMap R S y in I.map (algebraMap R S) := Ideal.mem_map_of_mem (algebraMap R S) hy
  grw [hle, IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers x)] at hin
  obtain ⟨m, ⟨n, hn, rfl⟩, h⟩ := hin
  dsimp at h
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [add_comm]; rw [pow_add]; rw [pow_one]; rw [mul_assoc] at h
exact ih hxJ _ h

/--
lemma `Ideal.eq_of_map_algebraMap_le` / 引理 `Ideal.eq_of_map_algebraMap_le`

English:
lemma Ideal.eq_of_map_algebraMap_le
  statement: (heq : I.map (algebraMap R S) = J.map (algebraMap R S))
  proof: le_antisymm (le_of_map_algebraMap_le S x heq.le hxJ) (le_of_map_algebraMap_le S x heq.ge hxI)

中文:
引理 理想.eq_of_map_algebraMap_le
  结论: (heq : I.map (algebraMap R S) = J.map (algebraMap R S))
  证明: le_antisymm (le_of_map_algebraMap_le S x heq.le hxJ) (le_of_map_algebraMap_le S x heq.ge hxI)

Depends on / 依赖: heq.ge, heq.le, le_antisymm, le_of_map_algebraMap_le
-/
lemma Ideal.eq_of_map_algebraMap_le (heq : I.map (algebraMap R S) = J.map (algebraMap R S))
    (hxI : forall y : R, x * y in I -> y in I) (hxJ : forall y : R, x * y in J -> y in J) : I = J :=
  le_antisymm (le_of_map_algebraMap_le S x heq.le hxJ) (le_of_map_algebraMap_le S x heq.ge hxI)

end saturated
