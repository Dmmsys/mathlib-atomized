/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals in polynomial rings
-/

public section

noncomputable section

open Polynomial

open Finset

universe u v w

namespace Polynomial

variable {R : Type*} [CommRing R] {a : R}

/--
theorem `mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero` / 定理 `mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero`

English:
theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
  given: {b : R[X]} {P : R[X][X]}
  proof: by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩

中文:
定理 mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
  条件: {b : R[X]} {P : R[X][X]}
  证明: by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩

Depends on / 依赖: C_mul, Ideal.mem_span_pair, X_sub_C_dvd_sub_C_eval, dvd_iff_isRoot, dvd_iff_isRoot.mpr, eq_add_of_sub_eq, mem_span_pair, mul_comm
-/
theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} :
    P in Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0 := by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩

/--
theorem `ker_evalRingHom` / 定理 `ker_evalRingHom`

English:
theorem ker_evalRingHom
  given: (x : R)
  statement: RingHom.ker (evalRingHom x) = Ideal.span {X - C x}
  proof: by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]

@[simp]

中文:
定理 ker_evalRingHom
  条件: (x : R)
  结论: 环态射.ker (evalRingHom x) = 理想.span {X - C x}
  证明: by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]

@[simp]

Depends on / 依赖: Ideal.mem_span_singleton, RingHom, RingHom.mem_ker, dvd_iff_isRoot, mem_ker, mem_span_singleton
-/
theorem ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C x} := by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]

@[simp]
/--
theorem `ker_modByMonicHom` / 定理 `ker_modByMonicHom`

English:
theorem ker_modByMonicHom
  given: {q : R[X]} (hq : q.Monic)
  proof: Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm

@[simp]

中文:
定理 ker_modByMonicHom
  条件: {q : R[X]} (hq : q.Monic)
  证明: Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm

@[simp]

Depends on / 依赖: Ideal.mem_span_singleton.symm, Submodule, Submodule.ext, mem_ker_modByMonic, mem_span_singleton
-/
theorem ker_modByMonicHom {q : R[X]} (hq : q.Monic) :
    LinearMap.ker (Polynomial.modByMonicHom q) = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm

@[simp]
/--
lemma `ker_constantCoeff` / 引理 `ker_constantCoeff`

English:
lemma ker_constantCoeff
  statement: RingHom.ker constantCoeff = .span {(X : R[X])}
  proof: by
  refine le_antisymm (fun p hp => ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, constantCoeff_apply, ← Polynomial.X_dvd_iff] at hp
  rwa [Ideal.mem_span_singleton]

中文:
引理 ker_constantCoeff
  结论: 环态射.ker constantCoeff = .span {(X : R[X])}
  证明: by
  refine le_antisymm (fun p hp => ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, constantCoeff_apply, ← Polynomial.X_dvd_iff] at hp
  rwa [Ideal.mem_span_singleton]

Depends on / 依赖: Ideal.mem_span_singleton, Ideal.span_le, Polynomial, Polynomial.X_dvd_iff, RingHom, RingHom.mem_ker, X_dvd_iff, constantCoeff_apply, le_antisymm, mem_ker, mem_span_singleton, span_le
-/
lemma ker_constantCoeff : RingHom.ker constantCoeff = .span {(X : R[X])} := by
  refine le_antisymm (fun p hp => ?_) (by simp [Ideal.span_le])
  simp only [RingHom.mem_ker, constantCoeff_apply, ← Polynomial.X_dvd_iff] at hp
  rwa [Ideal.mem_span_singleton]

end Polynomial

namespace Algebra

variable {R S : Type*}

/--
lemma `mem_ideal_map_adjoin` / 引理 `mem_ideal_map_adjoin`

English:
lemma mem_ideal_map_adjoin
  statement: [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (I : Ideal R)
  proof: by
  constructor
  · intro H
    induction H using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨C a, fun i => by rw [coeff_C]; aesop, aeval_C _ _⟩
    | zero => exact ⟨0, by simp, aeval_zero _⟩
    | add a b ha hb ha' hb' =>
      obtain ⟨a, ha, ha'⟩ :

中文:
引理 mem_ideal_map_adjoin
  结论: [交换半环 R] [半环 S] [代数 R S] (x : S) (I : 理想 R)
  证明: by
  constructor
  · intro H
    induction H using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨C a, fun i => by rw [coeff_C]; aesop, aeval_C _ _⟩
    | zero => exact ⟨0, by simp, aeval_zero _⟩
    | add a b ha hb ha' hb' =>
      obtain ⟨a, ha, ha'⟩ :

Depends on / 依赖: Submodule, Submodule.span_induction, add_mem, adjoin_eq_exists_aeval, aeval_C, aeval_zero, coeff_C, span_induction
-/
lemma mem_ideal_map_adjoin [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (I : Ideal R)
    {y : R[x]} :
    y in I.map (algebraMap R (R[x])) ↔
      exists p : R[X], (forall i, p.coeff i in I) ∧ Polynomial.aeval x p = y := by
  constructor
  · intro H
    induction H using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨C a, fun i => by rw [coeff_C]; aesop, aeval_C _ _⟩
    | zero => exact ⟨0, by simp, aeval_zero _⟩
    | add a b ha hb ha' hb' =>
      obtain ⟨a, ha, ha'⟩ := ha'
      obtain ⟨b, hb, hb'⟩ := hb'
      exact ⟨a + b, fun i => by simpa using add_mem (ha i) (hb i), by simp [ha', hb']⟩
    | smul a b hb hb' =>
      obtain ⟨b', hb, hb'⟩ := hb'
      have ⟨p, hp⟩ := adjoin_eq_exists_aeval R x a
      refine ⟨p * b', fun i => ?_, by simp [hp, hb']⟩
      rw [coeff_mul]
      exact sum_mem fun i hi => Ideal.mul_mem_left _ _ (hb _)
  · rintro ⟨p, hp, hp'⟩
    have : y = ∑ i in p.support, p.coeff i • ⟨_, (X ^ i).aeval_mem_adjoin_singleton _ x⟩ := by
      trans ∑ i in p.support, ⟨_, (C (p.coeff i) * X ^ i).aeval_mem_adjoin_singleton _ x⟩
      · ext1
        simp only [AddSubmonoidClass.coe_finsetSum, ← map_sum, ← hp', ← as_sum_support_C_mul_X_pow]
      · congr with i
        simp [Algebra.smul_def]
    simp_rw [this, Algebra.smul_def]
    exact sum_mem fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hp i))

/--
lemma `exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top` / 引理 `exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top`

English:
lemma exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
  statement: [CommRing R] [CommRing S]
  proof: by
  rw [← Ideal.one_eq_top]; rw [← Ideal.add_eq_sup]; rw [Ideal.add_eq_one_iff] at h
  have ⟨y, hy, z, hz, eq⟩ := h
  have ⟨p, hp⟩ := (mem_ideal_map_adjoin ..).mp hy
  have ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  have ⟨q, hq⟩ := adjoin_eq_exists_aeval R x w
  use (1 - p - X * q).reverse
  have 

中文:
引理 存在_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
  结论: [交换环 R] [交换环 S]
  证明: by
  rw [← Ideal.one_eq_top]; rw [← Ideal.add_eq_sup]; rw [Ideal.add_eq_one_iff] at h
  have ⟨y, hy, z, hz, eq⟩ := h
  have ⟨p, hp⟩ := (mem_ideal_map_adjoin ..).mp hy
  have ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  have ⟨q, hq⟩ := adjoin_eq_exists_aeval R x w
  use (1 - p - X * q).reverse
  have 

Depends on / 依赖: Ideal.add_eq_one_iff, Ideal.add_eq_sup, Ideal.mem_span_singleton.mp, Ideal.one_eq_top, add_eq_one_iff, add_eq_sup, adjoin_eq_exists_aeval, apply_fun, mem_ideal_map_adjoin, mem_span_singleton, one_eq_top, reverse, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero
-/
lemma exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (I : Ideal R) (hI : I != ⊤) [Invertible x]
    (h : I.map (algebraMap R (R[x])) ⊔ .span {⟨x, subset_adjoin rfl⟩} = ⊤) :
    exists p : R[X], p.leadingCoeff - 1 in I ∧ p.aeval ⅟x = 0 := by
  rw [← Ideal.one_eq_top]; rw [← Ideal.add_eq_sup]; rw [Ideal.add_eq_one_iff] at h
  have ⟨y, hy, z, hz, eq⟩ := h
  have ⟨p, hp⟩ := (mem_ideal_map_adjoin ..).mp hy
  have ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  have ⟨q, hq⟩ := adjoin_eq_exists_aeval R x w
  use (1 - p - X * q).reverse
  have : (1 - p - X * q).coeff 0 - 1 in I := by simpa using hp.1 0
  apply_fun (·.1) at eq hw
  dsimp at eq
  rw [reverse_leadingCoeff]; rw [trailingCoeff_eq_coeff_zero]
· exact ⟨this, (eval₂_reverse_eq_zero_iff ..).mpr by simp [← aeval_def, hp.2, hq, ← eq, hw]⟩
· exact fun h => hI by simpa [h, Ideal.eq_top_iff_one]

end Algebra
