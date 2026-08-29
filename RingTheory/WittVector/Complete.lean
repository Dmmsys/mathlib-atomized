/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# The ring of Witt vectors is p-torsion free and p-adically complete

In this file, we prove that the ring of Witt vectors `𝕎 k` is p-torsion free and p-adically complete
when `k` is a perfect ring of characteristic `p`.

## Main declarations

* `WittVector.eq_zero_of_p_mul_eq_zero` : If `k` is a perfect ring of characteristic `p`,
  then the Witt vector `𝕎 k` is `p`-torsion free.
* `isAdicCompleteIdealSpanP` : If `k` is a perfect ring of characteristic `p`,
  then the Witt vector `𝕎 k` is `p`-adically complete.
-/

@[expose] public section

namespace WittVector

variable {p : Nat} [hp : Fact (Nat.Prime p)] {k : Type*} [CommRing k]

local notation "𝕎" => WittVector p

/--
theorem `le_coeff_eq_iff_le_sub_coeff_eq_zero` / 定理 `le_coeff_eq_iff_le_sub_coeff_eq_zero`

English:
theorem le_coeff_eq_iff_le_sub_coeff_eq_zero
  given: {x y : 𝕎 k} {n : Nat}
  proof: by
  calc
  _ ↔ x.truncate n = y.truncate n := by
    refine ⟨fun h => ?_, fun h i hi => ?_⟩
    · ext i
      simp [h i]
    · rw [← coeff_truncate x ⟨i, hi⟩, ← coeff_truncate y ⟨i, hi⟩, h]
  _ ↔ (x - y).truncate n = 0 := by
    simp only [map_sub, sub_eq_zero]
  _ ↔ _ := by simp only [← mem_ker_tr

中文:
定理 le_coeff_eq_iff_le_sub_coeff_eq_zero
  条件: {x y : 𝕎 k} {n : 自然数}
  证明: by
  calc
  _ ↔ x.truncate n = y.truncate n := by
    refine ⟨fun h => ?_, fun h i hi => ?_⟩
    · ext i
      simp [h i]
    · rw [← coeff_truncate x ⟨i, hi⟩, ← coeff_truncate y ⟨i, hi⟩, h]
  _ ↔ (x - y).truncate n = 0 := by
    simp only [map_sub, sub_eq_zero]
  _ ↔ _ := by simp only [← mem_ker_tr

Depends on / 依赖: RingHom, RingHom.mem_ker, coeff_truncate, map_sub, mem_ker, mem_ker_truncate, sub_eq_zero, truncate, x.truncate, y.truncate
-/
theorem le_coeff_eq_iff_le_sub_coeff_eq_zero {x y : 𝕎 k} {n : Nat} :
    (forall i < n, x.coeff i = y.coeff i) ↔ forall i < n, (x - y).coeff i = 0 := by
  calc
  _ ↔ x.truncate n = y.truncate n := by
    refine ⟨fun h => ?_, fun h i hi => ?_⟩
    · ext i
      simp [h i]
    · rw [← coeff_truncate x ⟨i, hi⟩, ← coeff_truncate y ⟨i, hi⟩, h]
  _ ↔ (x - y).truncate n = 0 := by
    simp only [map_sub, sub_eq_zero]
  _ ↔ _ := by simp only [← mem_ker_truncate, RingHom.mem_ker]

section PerfectRing

variable [CharP k p] [PerfectRing k p]

/--
theorem `eq_zero_of_p_mul_eq_zero` / 定理 `eq_zero_of_p_mul_eq_zero`

English:
theorem eq_zero_of_p_mul_eq_zero
  given: (x : 𝕎 k) (h : x * p = 0)
  statement: x = 0
  proof: by
  rwa [← frobenius_verschiebung, _root_.map_eq_zero_iff _ (frobenius_bijective p k).injective,
      _root_.map_eq_zero_iff _ (verschiebung_injective p k)] at h

中文:
定理 eq_zero_of_p_mul_eq_zero
  条件: (x : 𝕎 k) (h : x * p = 0)
  结论: x = 0
  证明: by
  rwa [← frobenius_verschiebung, _root_.map_eq_zero_iff _ (frobenius_bijective p k).injective,
      _root_.map_eq_zero_iff _ (verschiebung_injective p k)] at h

Depends on / 依赖: _root_, _root_.map_eq_zero_iff, frobenius_bijective, frobenius_verschiebung, injective, map_eq_zero_iff, verschiebung_injective
-/
theorem eq_zero_of_p_mul_eq_zero (x : 𝕎 k) (h : x * p = 0) : x = 0 := by
  rwa [← frobenius_verschiebung, _root_.map_eq_zero_iff _ (frobenius_bijective p k).injective,
      _root_.map_eq_zero_iff _ (verschiebung_injective p k)] at h

/--
theorem `mem_span_p_iff_coeff_zero_eq_zero` / 定理 `mem_span_p_iff_coeff_zero_eq_zero`

English:
theorem mem_span_p_iff_coeff_zero_eq_zero
  given: (x : 𝕎 k)
  proof: by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ => ?_, fun h => ?_⟩
  · rw [hu, mul_charP_coeff_zero]
  · use (frobeniusEquiv p k).symm (x.shift 1)
    calc
    _ = verschiebung (x.shift 1) := by
      simpa using eq_iterate_verschiebung (n := 1) (by simp [h])
    _ 

中文:
定理 mem_span_p_iff_coeff_zero_eq_zero
  条件: (x : 𝕎 k)
  证明: by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ => ?_, fun h => ?_⟩
  · rw [hu, mul_charP_coeff_zero]
  · use (frobeniusEquiv p k).symm (x.shift 1)
    calc
    _ = verschiebung (x.shift 1) := by
      simpa using eq_iterate_verschiebung (n := 1) (by simp [h])
    _ 

Depends on / 依赖: Ideal.mem_span_singleton, RingEquiv, RingEquiv.apply_symm_apply, apply_symm_apply, dvd_def, eq_iterate_verschiebung, frobeniusEquiv, frobeniusEquiv_apply, mem_span_singleton, mul_charP_coeff_zero, mul_comm, simp_rw, verschiebung, verschiebung_frobenius, x.shift
-/
theorem mem_span_p_iff_coeff_zero_eq_zero (x : 𝕎 k) :
    x in (Ideal.span {(p : 𝕎 k)}) ↔ x.coeff 0 = 0 := by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ => ?_, fun h => ?_⟩
  · rw [hu, mul_charP_coeff_zero]
  · use (frobeniusEquiv p k).symm (x.shift 1)
    calc
    _ = verschiebung (x.shift 1) := by
      simpa using eq_iterate_verschiebung (n := 1) (by simp [h])
    _ = _ := by
      rw [← verschiebung_frobenius]; rw [← frobeniusEquiv_apply]; rw [RingEquiv.apply_symm_apply (frobeniusEquiv p k) _]

/--
theorem `mem_span_p_pow_iff_le_coeff_eq_zero` / 定理 `mem_span_p_pow_iff_le_coeff_eq_zero`

English:
theorem mem_span_p_pow_iff_le_coeff_eq_zero
  given: (x : 𝕎 k) (n : Nat)
  proof: by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ m hm => ?_, fun h => ?_⟩
  · rw [hu, mul_pow_charP_coeff_zero _ hm]
  · use (frobeniusEquiv p k).symm^[n] (x.shift n)
    rw [← iterate_verschiebung_iterate_frobenius]
    calc
    _ = verschiebung^[n] (x.shift n) := by

中文:
定理 mem_span_p_pow_iff_le_coeff_eq_zero
  条件: (x : 𝕎 k) (n : 自然数)
  证明: by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ m hm => ?_, fun h => ?_⟩
  · rw [hu, mul_pow_charP_coeff_zero _ hm]
  · use (frobeniusEquiv p k).symm^[n] (x.shift n)
    rw [← iterate_verschiebung_iterate_frobenius]
    calc
    _ = verschiebung^[n] (x.shift n) := by

Depends on / 依赖: Commute, Function, Function.Commute.comp_iterate, Function.comp_apply, Ideal.mem_span_singleton, RingEquiv, RingEquiv.coe_trans, WittVector, WittVector.frobeniusEquiv_apply, coe_trans, comp_apply, comp_iterate, dvd_def, eq_iterate_verschiebung, frobenius, frobeniusEquiv, frobeniusEquiv_apply, iterate_verschiebung_iterate_frobenius, mem_span_singleton, mul_comm
-/
theorem mem_span_p_pow_iff_le_coeff_eq_zero (x : 𝕎 k) (n : Nat) :
    x in (Ideal.span {(p ^ n : 𝕎 k)}) ↔ forall m, m < n -> x.coeff m = 0 := by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ m hm => ?_, fun h => ?_⟩
  · rw [hu, mul_pow_charP_coeff_zero _ hm]
  · use (frobeniusEquiv p k).symm^[n] (x.shift n)
    rw [← iterate_verschiebung_iterate_frobenius]
    calc
    _ = verschiebung^[n] (x.shift n) := by
      simpa using eq_iterate_verschiebung (x := x) (n := n) h
    _ = _ := by
      congr
      rw [← Function.comp_apply (f := frobenius^[n]), ← Function.Commute.comp_iterate]
      · rw [← WittVector.frobeniusEquiv_apply, ← RingEquiv.coe_trans]
        simp
      · rw [Function.Commute, Function.Semiconj, ← WittVector.frobeniusEquiv_apply]
        simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply, implies_true]

/--
lemma `ker_constantCoeff` / 引理 `ker_constantCoeff`

English:
lemma ker_constantCoeff
  statement: RingHom.ker constantCoeff = Ideal.span {(p : 𝕎 k)}
  proof: by
  ext
  simp [mem_span_p_iff_coeff_zero_eq_zero]

中文:
引理 ker_constantCoeff
  结论: 环态射.ker constantCoeff = 理想.span {(p : 𝕎 k)}
  证明: by
  ext
  simp [mem_span_p_iff_coeff_zero_eq_zero]

Depends on / 依赖: mem_span_p_iff_coeff_zero_eq_zero
-/
lemma ker_constantCoeff : RingHom.ker constantCoeff = Ideal.span {(p : 𝕎 k)} := by
  ext
  simp [mem_span_p_iff_coeff_zero_eq_zero]

/--
Definition of `quotientPEquiv` / `quotientPEquiv` 的定义

English:
definition quotientPEquiv
  signature: : 𝕎 k ⧸ Ideal.span {(p : 𝕎 k)} ≃+* k
  body: (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective p))

@[simp]

中文:
定义 quotientPEquiv
  签名: : 𝕎 k ⧸ 理想.span {(p : 𝕎 k)} ≃+* k
  定义体: (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective p))

@[simp]

Depends on / 依赖: Ideal.quotEquivOfEq, RingHom, RingHom.quotientKerEquivOfSurjective, constantCoeff_surjective, ker_constantCoeff, ker_constantCoeff.symm, quotEquivOfEq, quotientKerEquivOfSurjective
-/
noncomputable def quotientPEquiv : 𝕎 k ⧸ Ideal.span {(p : 𝕎 k)} ≃+* k :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective p))

@[simp]
/--
lemma `quotientPEquiv_mk` / 引理 `quotientPEquiv_mk`

English:
lemma quotientPEquiv_mk
  given: (x : 𝕎 k)
  statement: quotientPEquiv (Quot.mk _ x) = constantCoeff x
  proof: rfl

中文:
引理 quotientPEquiv_mk
  条件: (x : 𝕎 k)
  结论: quotientPEquiv (商.mk _ x) = constantCoeff x
  证明: rfl
-/
lemma quotientPEquiv_mk (x : 𝕎 k) : quotientPEquiv (Quot.mk _ x) = constantCoeff x := rfl

/--
Instance `isAdicCompleteIdealSpanP` / 实例 `isAdicCompleteIdealSpanP`

English:
instance isAdicCompleteIdealSpanP
  signature: : IsAdicComplete (Ideal.span {(p : 𝕎 k)}) (𝕎 k) where
  body: by
    intro _ h
    ext n
    simp only [smul_eq_mul, Ideal.mul_top] at h
    have := h (n + 1)
    simp only [Ideal.span_singleton_pow, SModEq.zero,
        mem_span_p_pow_iff_le_coeff_eq_zero] at this
    simpa using this n
  prec' := by
    intro x h
    -- construct the limit Witt vector w diag

中文:
实例 isAdicCompleteIdealSpanP
  签名: : 是AdicComplete (理想.span {(p : 𝕎 k)}) (𝕎 k) where
  定义体: by
    intro _ h
    ext n
    simp only [smul_eq_mul, Ideal.mul_top] at h
    have := h (n + 1)
    simp only [Ideal.span_singleton_pow, SModEq.zero,
        mem_span_p_pow_iff_le_coeff_eq_zero] at this
    simpa using this n
  prec' := by
    intro x h
    -- construct the limit Witt vector w diag

Depends on / 依赖: Ideal.mul_top, Ideal.span_singleton_pow, SModEq, SModEq.zero, mem_span_p_pow_iff_le_coeff_eq_zero, mul_top, smul_eq_mul, span_singleton_pow
-/
instance isAdicCompleteIdealSpanP : IsAdicComplete (Ideal.span {(p : 𝕎 k)}) (𝕎 k) where
  haus' := by
    intro _ h
    ext n
    simp only [smul_eq_mul, Ideal.mul_top] at h
    have := h (n + 1)
    simp only [Ideal.span_singleton_pow, SModEq.zero,
        mem_span_p_pow_iff_le_coeff_eq_zero] at this
    simpa using this n
  prec' := by
    intro x h
    -- construct the limit Witt vector w diagonally
    use .mk p (fun n => (x (n + 1)).coeff n)
    intro n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      mem_span_p_pow_iff_le_coeff_eq_zero, ← le_coeff_eq_iff_le_sub_coeff_eq_zero] at h ⊢
    intro i hi
    exact (h hi i (Nat.lt_succ_self i)).symm

end PerfectRing

end WittVector
