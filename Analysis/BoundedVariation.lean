/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Almost everywhere differentiability of functions with locally bounded variation

In this file we show that a bounded variation function is differentiable almost everywhere.
This implies that Lipschitz functions from the real line into finite-dimensional vector spaces
are also differentiable almost everywhere.

## Main definitions and results

* `LocallyBoundedVariationOn.ae_differentiableWithinAt` shows that a bounded variation
  function on a subset of ℝ into a finite-dimensional real vector space is differentiable almost
  everywhere, with `DifferentiableWithinAt` in its conclusion.
* `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` shows that a bounded variation function on
  an interval of ℝ into a finite-dimensional real vector space is differentiable almost everywhere,
  with `DifferentiableAt` in its conclusion.
* `LipschitzOnWith.ae_differentiableWithinAt` is the same result for Lipschitz functions.

We also give several variations around these results.

-/

public section

open scoped NNReal Topology ENNReal
open Set MeasureTheory Filter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [FiniteDimensional Real V]

section

open Finset

variable {α : Type*} [LinearOrder α] {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]
  {s : Set α} {f : α -> E} {g : α -> F} {C D : Real>=0∞} {B : E ->L[Real] F ->L[Real] G}

/--
lemma `eVariationOn_bilinear_comp_le` / 引理 `eVariationOn_bilinear_comp_le`

English:
lemma eVariationOn_bilinear_comp_le
  statement: (hf : forall x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D)
  proof: by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i in range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u i)))
  _ <= ∑ i in range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u (i + 1)))) +
      ∑ i in range n, edist (B (f (u i)) (g (u (i + 1)))) (B (f (u i)) (g (u i))) := by
    rw [← Finset.sum_add_distrib]
    gcongr with i hi
    apply edist_triangle
  _ = ∑ i in range n, ‖B (f (u (i + 1)) - f (u i)) (g (u (i + 1)))‖ₑ +
      ∑ i in range n, ‖B (f (u i)) (g (u (i + 1)) - g (u i))‖ₑ := by simp [edist_eq_enorm_sub]
  _ <= ∑ i in range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * ‖g (u (i + 1))‖ₑ +
      ∑ i in range n, ‖B‖ₑ * ‖f (u i)‖ₑ * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply ContinuousLinearMap.le_opENorm₂
    · apply ContinuousLinearMap.le_opENorm₂
  _ <= ∑ i in range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * D +
      ∑ i in range n, ‖B‖ₑ * C * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply hg _ (u_mem _)
    · apply hf _ (u_mem _)
  _ = ‖B‖ₑ * D * ∑ i in range n, ‖f (u (i + 1)) - f (u i)‖ₑ +
      ‖B‖ₑ * C * ∑ i in range n, ‖g (u (i + 1)) - g (u i)‖ₑ := by
    simp only [← sum_mul, ← mul_sum]
    ring
  _ <= ‖B‖ₑ * D * eVariationOn f s + ‖B‖ₑ * C * eVariationOn g s := by
    simp only [← edist_eq_enorm_sub]
    gcongr
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi => u_mem i)
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi => u_mem i)
  _ = ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by ring

@[to_fun eVariationOn_fun_smul_le]

中文:
引理 eVariationOn_bilinear_comp_le
  结论: (hf : 对任意 x in s, ‖f x‖ₑ <= C) (hg : 对任意 x in s, ‖g x‖ₑ <= D)
  证明: by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i in range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u i)))
  _ <= ∑ i in range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u (i + 1)))) +
      ∑ i in range n, edist (B (f (u i)) (g (u (i + 1)))) (B (f (u i)) (g (u i))) := by
    rw [← Finset.sum_add_distrib]
    gcongr with i hi
    apply edist_triangle
  _ = ∑ i in range n, ‖B (f (u (i + 1)) - f (u i)) (g (u (i + 1)))‖ₑ +
      ∑ i in range n, ‖B (f (u i)) (g (u (i + 1)) - g (u i))‖ₑ := by simp [edist_eq_enorm_sub]
  _ <= ∑ i in range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * ‖g (u (i + 1))‖ₑ +
      ∑ i in range n, ‖B‖ₑ * ‖f (u i)‖ₑ * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply ContinuousLinearMap.le_opENorm₂
    · apply ContinuousLinearMap.le_opENorm₂
  _ <= ∑ i in range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * D +
      ∑ i in range n, ‖B‖ₑ * C * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply hg _ (u_mem _)
    · apply hf _ (u_mem _)
  _ = ‖B‖ₑ * D * ∑ i in range n, ‖f (u (i + 1)) - f (u i)‖ₑ +
      ‖B‖ₑ * C * ∑ i in range n, ‖g (u (i + 1)) - g (u i)‖ₑ := by
    simp only [← sum_mul, ← mul_sum]
    ring
  _ <= ‖B‖ₑ * D * eVariationOn f s + ‖B‖ₑ * C * eVariationOn g s := by
    simp only [← edist_eq_enorm_sub]
    gcongr
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi => u_mem i)
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi => u_mem i)
  _ = ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by ring

@[to_fun eVariationOn_fun_smul_le]

Depends on / 依赖: Finset, Finset.sum_add_distrib, edist_triangle, iSup_le, sum_add_distrib, u_mem, u_mono
-/
lemma eVariationOn_bilinear_comp_le (hf : forall x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D)
    (B : E ->L[Real] F ->L[Real] G) :
    eVariationOn (fun x => B (f x) (g x) : α -> G) s <=
      ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i in range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u i)))
  _ <= ∑ i in range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u (i + 1)))) +
      ∑ i in range n, edist (B (f (u i)) (g (u (i + 1)))) (B (f (u i)) (g (u i))) := by
    rw [← Finset.sum_add_distrib]
    gcongr with i hi
    apply edist_triangle
  _ = ∑ i in range n, ‖B (f (u (i + 1)) - f (u i)) (g (u (i + 1)))‖ₑ +
      ∑ i in range n, ‖B (f (u i)) (g (u (i + 1)) - g (u i))‖ₑ := by simp [edist_eq_enorm_sub]
  _ <= ∑ i in range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * ‖g (u (i + 1))‖ₑ +
      ∑ i in range n, ‖B‖ₑ * ‖f (u i)‖ₑ * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply ContinuousLinearMap.le_opENorm₂
    · apply ContinuousLinearMap.le_opENorm₂
  _ <= ∑ i in range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * D +
      ∑ i in range n, ‖B‖ₑ * C * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply hg _ (u_mem _)
    · apply hf _ (u_mem _)
  _ = ‖B‖ₑ * D * ∑ i in range n, ‖f (u (i + 1)) - f (u i)‖ₑ +
      ‖B‖ₑ * C * ∑ i in range n, ‖g (u (i + 1)) - g (u i)‖ₑ := by
    simp only [← sum_mul, ← mul_sum]
    ring
  _ <= ‖B‖ₑ * D * eVariationOn f s + ‖B‖ₑ * C * eVariationOn g s := by
    simp only [← edist_eq_enorm_sub]
    gcongr
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi => u_mem i)
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi => u_mem i)
  _ = ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by ring

@[to_fun eVariationOn_fun_smul_le]
/--
lemma `eVariationOn_smul_le` / 引理 `eVariationOn_smul_le`

English:
lemma eVariationOn_smul_le
  statement: {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F}
  proof: by
  apply (eVariationOn_bilinear_comp_le hf hg (B := ContinuousLinearMap.lsmul Real 𝕜)).trans
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul]

@[to_fun eVariationOn_fun_mul_le]

中文:
引理 eVariationOn_smul_le
  结论: {𝕜 : 类型} {f : α -> 𝕜} {g : α -> F}
  证明: by
  apply (eVariationOn_bilinear_comp_le hf hg (B := ContinuousLinearMap.lsmul Real 𝕜)).trans
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul]

@[to_fun eVariationOn_fun_mul_le]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, ContinuousLinearMap.opENorm_lsmul_le, eVariationOn_bilinear_comp_le, one_mul, opENorm_lsmul_le
-/
lemma eVariationOn_smul_le {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F}
    [NormedRing 𝕜] [NormedAlgebra Real 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower Real 𝕜 F]
    {C D : Real>=0∞} {s : Set α} (hf : forall x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D) :
    eVariationOn (f • g) s <= C * eVariationOn g s + D * eVariationOn f s := by
  apply (eVariationOn_bilinear_comp_le hf hg (B := ContinuousLinearMap.lsmul Real 𝕜)).trans
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul]

@[to_fun eVariationOn_fun_mul_le]
/--
lemma `eVariation_mul_le` / 引理 `eVariation_mul_le`

English:
lemma eVariation_mul_le
  statement: {f g : α -> Real}
  proof: by
  simpa using eVariationOn_smul_le hf hg

中文:
引理 eVariation_mul_le
  结论: {f g : α -> 实数}
  证明: by
  simpa using eVariationOn_smul_le hf hg

Depends on / 依赖: eVariationOn_smul_le
-/
lemma eVariation_mul_le {f g : α -> Real}
    {C D : Real>=0∞} {s : Set α} (hf : forall x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D) :
    eVariationOn (f * g) s <= C * eVariationOn g s + D * eVariationOn f s := by
  simpa using eVariationOn_smul_le hf hg

/--
lemma `BoundedVariationOn.bilinear_comp` / 引理 `BoundedVariationOn.bilinear_comp`

English:
lemma BoundedVariationOn.bilinear_comp
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x, hx⟩⟩
  · simp
  suffices eVariationOn (fun x => (B (f x)) (g x)) s < ∞ from ne_of_lt this
  have A (y) (hy : y in s) : ‖f y‖ₑ <= ‖f x‖ₑ + eVariationOn f s := by
    grw [show f y = f x + (f y - f x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  have A' (y) (hy : y in s) : ‖g y‖ₑ <= ‖g x‖ₑ + eVariationOn g s := by
    grw [show g y = g x + (g y - g x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  grw [eVariationOn_bilinear_comp_le A A']
  simp [mul_add, ENNReal.mul_lt_top_iff, hf.lt_top, hg.lt_top]

@[to_fun]

中文:
引理 BoundedVariationOn.bilinear_comp
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x, hx⟩⟩
  · simp
  suffices eVariationOn (fun x => (B (f x)) (g x)) s < ∞ from ne_of_lt this
  have A (y) (hy : y in s) : ‖f y‖ₑ <= ‖f x‖ₑ + eVariationOn f s := by
    grw [show f y = f x + (f y - f x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  have A' (y) (hy : y in s) : ‖g y‖ₑ <= ‖g x‖ₑ + eVariationOn g s := by
    grw [show g y = g x + (g y - g x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  grw [eVariationOn_bilinear_comp_le A A']
  simp [mul_add, ENNReal.mul_lt_top_iff, hf.lt_top, hg.lt_top]

@[to_fun]

Depends on / 依赖: eVariationOn, eVariationOn.edist_le, edist_eq_enorm_sub, edist_le, enorm_add_le, eq_empty_or_nonempty, ne_of_lt, s.eq_empty_or_nonempty
-/
lemma BoundedVariationOn.bilinear_comp
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) (B : E ->L[Real] F ->L[Real] G) :
    BoundedVariationOn (fun x => B (f x) (g x)) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x, hx⟩⟩
  · simp
  suffices eVariationOn (fun x => (B (f x)) (g x)) s < ∞ from ne_of_lt this
  have A (y) (hy : y in s) : ‖f y‖ₑ <= ‖f x‖ₑ + eVariationOn f s := by
    grw [show f y = f x + (f y - f x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  have A' (y) (hy : y in s) : ‖g y‖ₑ <= ‖g x‖ₑ + eVariationOn g s := by
    grw [show g y = g x + (g y - g x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  grw [eVariationOn_bilinear_comp_le A A']
  simp [mul_add, ENNReal.mul_lt_top_iff, hf.lt_top, hg.lt_top]

@[to_fun]
/--
lemma `BoundedVariationOn.smul` / 引理 `BoundedVariationOn.smul`

English:
lemma BoundedVariationOn.smul
  statement: {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F}
  proof: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real 𝕜)

@[to_fun]

中文:
引理 BoundedVariationOn.smul
  结论: {𝕜 : 类型} {f : α -> 𝕜} {g : α -> F}
  证明: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real 𝕜)

@[to_fun]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, bilinear_comp, hf.bilinear_comp
-/
lemma BoundedVariationOn.smul {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F}
    [NormedRing 𝕜] [NormedAlgebra Real 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower Real 𝕜 F]
    {s : Set α} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f • g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real 𝕜)

@[to_fun]
/--
lemma `BoundedVariationOn.mul` / 引理 `BoundedVariationOn.mul`

English:
lemma BoundedVariationOn.mul
  statement: {f g : α -> Real} {s : Set α}
  proof: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real Real)

中文:
引理 BoundedVariationOn.mul
  结论: {f g : α -> 实数} {s : 集合 α}
  证明: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real Real)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, bilinear_comp, hf.bilinear_comp
-/
lemma BoundedVariationOn.mul {f g : α -> Real} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f * g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real Real)

/--
lemma `LocallyBoundedVariationOn.bilinear_comp` / 引理 `LocallyBoundedVariationOn.bilinear_comp`

English:
lemma LocallyBoundedVariationOn.bilinear_comp
  statement: (hf : LocallyBoundedVariationOn f s)
  proof: fun a b ha hb => (hf a b ha hb).bilinear_comp (hg a b ha hb) B

@[to_fun]

中文:
引理 LocallyBoundedVariationOn.bilinear_comp
  结论: (hf : LocallyBoundedVariationOn f s)
  证明: fun a b ha hb => (hf a b ha hb).bilinear_comp (hg a b ha hb) B

@[to_fun]

Depends on / 依赖: bilinear_comp
-/
lemma LocallyBoundedVariationOn.bilinear_comp (hf : LocallyBoundedVariationOn f s)
    (hg : LocallyBoundedVariationOn g s) (B : E ->L[Real] F ->L[Real] G) :
    LocallyBoundedVariationOn (fun x => B (f x) (g x)) s :=
  fun a b ha hb => (hf a b ha hb).bilinear_comp (hg a b ha hb) B

@[to_fun]
/--
lemma `LocallyBoundedVariationOn.smul` / 引理 `LocallyBoundedVariationOn.smul`

English:
lemma LocallyBoundedVariationOn.smul
  statement: {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F}
  proof: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real 𝕜)

@[to_fun]

中文:
引理 LocallyBoundedVariationOn.smul
  结论: {𝕜 : 类型} {f : α -> 𝕜} {g : α -> F}
  证明: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real 𝕜)

@[to_fun]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, bilinear_comp, hf.bilinear_comp
-/
lemma LocallyBoundedVariationOn.smul {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F}
    [NormedRing 𝕜] [NormedAlgebra Real 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower Real 𝕜 F]
    {s : Set α} (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f • g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real 𝕜)

@[to_fun]
/--
lemma `LocallyBoundedVariationOn.mul` / 引理 `LocallyBoundedVariationOn.mul`

English:
lemma LocallyBoundedVariationOn.mul
  statement: {f g : α -> Real} {s : Set α}
  proof: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real Real)

中文:
引理 LocallyBoundedVariationOn.mul
  结论: {f g : α -> 实数} {s : 集合 α}
  证明: hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real Real)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, bilinear_comp, hf.bilinear_comp
-/
lemma LocallyBoundedVariationOn.mul {f g : α -> Real} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f * g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul Real Real)

end

namespace LocallyBoundedVariationOn

/--
theorem `ae_differentiableWithinAt_of_mem_real` / 定理 `ae_differentiableWithinAt_of_mem_real`

English:
theorem ae_differentiableWithinAt_of_mem_real
  statement: {f : Real -> Real} {s : Set Real}
  proof: by
  obtain ⟨p, q, hp, hq, rfl⟩ : exists p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q :=
    h.exists_monotoneOn_sub_monotoneOn
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem] with
    x hxp hxq xs
  exact (hxp xs).sub (hxq xs)

中文:
定理 ae_differentiableWithinAt_of_mem_real
  结论: {f : 实数 -> 实数} {s : 集合 实数}
  证明: by
  obtain ⟨p, q, hp, hq, rfl⟩ : exists p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q :=
    h.exists_monotoneOn_sub_monotoneOn
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem] with
    x hxp hxq xs
  exact (hxp xs).sub (hxq xs)

Depends on / 依赖: MonotoneOn, ae_differentiableWithinAt_of_mem, exists_monotoneOn_sub_monotoneOn, filter_upwards, h.exists_monotoneOn_sub_monotoneOn, hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem
-/
theorem ae_differentiableWithinAt_of_mem_real {f : Real -> Real} {s : Set Real}
    (h : LocallyBoundedVariationOn f s) : forallᵐ x, x in s -> DifferentiableWithinAt Real f s x := by
  obtain ⟨p, q, hp, hq, rfl⟩ : exists p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q :=
    h.exists_monotoneOn_sub_monotoneOn
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem] with
    x hxp hxq xs
  exact (hxp xs).sub (hxq xs)

/--
theorem `ae_differentiableWithinAt_of_mem_pi` / 定理 `ae_differentiableWithinAt_of_mem_pi`

English:
theorem ae_differentiableWithinAt_of_mem_pi
  statement: {ι : Type*} [Fintype ι] {f : Real -> ι -> Real} {s : Set Real}
  proof: by
  have A : forall i : ι, LipschitzWith 1 fun x : ι -> Real => x i := fun i => LipschitzWith.eval i
  have : forall i : ι, forallᵐ x, x in s -> DifferentiableWithinAt Real (fun x : Real => f x i) s x := fun i => by
    apply ae_differentiableWithinAt_of_mem_real
    exact LipschitzWith.comp_locallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

中文:
定理 ae_differentiableWithinAt_of_mem_pi
  结论: {ι : 类型} [有限类型 ι] {f : 实数 -> ι -> 实数} {s : 集合 实数}
  证明: by
  have A : forall i : ι, LipschitzWith 1 fun x : ι -> Real => x i := fun i => LipschitzWith.eval i
  have : forall i : ι, forallᵐ x, x in s -> DifferentiableWithinAt Real (fun x : Real => f x i) s x := fun i => by
    apply ae_differentiableWithinAt_of_mem_real
    exact LipschitzWith.comp_locallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

Depends on / 依赖: DifferentiableWithinAt, LipschitzWith, LipschitzWith.comp_locallyBoundedVariationOn, LipschitzWith.eval, ae_all_iff, ae_differentiableWithinAt_of_mem_real, comp_locallyBoundedVariationOn, differentiableWithinAt_pi, filter_upwards
-/
theorem ae_differentiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : Real -> ι -> Real} {s : Set Real}
    (h : LocallyBoundedVariationOn f s) : forallᵐ x, x in s -> DifferentiableWithinAt Real f s x := by
  have A : forall i : ι, LipschitzWith 1 fun x : ι -> Real => x i := fun i => LipschitzWith.eval i
  have : forall i : ι, forallᵐ x, x in s -> DifferentiableWithinAt Real (fun x : Real => f x i) s x := fun i => by
    apply ae_differentiableWithinAt_of_mem_real
    exact LipschitzWith.comp_locallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

/--
theorem `ae_differentiableWithinAt_of_mem` / 定理 `ae_differentiableWithinAt_of_mem`

English:
theorem ae_differentiableWithinAt_of_mem
  statement: {f : Real -> V} {s : Set Real}
  proof: by
  let A := (Module.Basis.ofVectorSpace Real V).equivFun.toContinuousLinearEquiv
  suffices H : forallᵐ x, x in s -> DifferentiableWithinAt Real (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    exact (ContinuousLinearEquiv.comp_differentiableWithinAt_iff _).mp (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_locallyBoundedVariationOn h

中文:
定理 ae_differentiableWithinAt_of_mem
  结论: {f : 实数 -> V} {s : 集合 实数}
  证明: by
  let A := (Module.Basis.ofVectorSpace Real V).equivFun.toContinuousLinearEquiv
  suffices H : forallᵐ x, x in s -> DifferentiableWithinAt Real (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    exact (ContinuousLinearEquiv.comp_differentiableWithinAt_iff _).mp (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_locallyBoundedVariationOn h

Depends on / 依赖: A.lipschitz.comp_locallyBoundedVariationOn, ContinuousLinearEquiv, ContinuousLinearEquiv.comp_differentiableWithinAt_iff, DifferentiableWithinAt, Module, Module.Basis.ofVectorSpace, ae_differentiableWithinAt_of_mem_pi, comp_differentiableWithinAt_iff, comp_locallyBoundedVariationOn, equivFun, equivFun.toContinuousLinearEquiv, filter_upwards, lipschitz, ofVectorSpace, toContinuousLinearEquiv
-/
theorem ae_differentiableWithinAt_of_mem {f : Real -> V} {s : Set Real}
    (h : LocallyBoundedVariationOn f s) : forallᵐ x, x in s -> DifferentiableWithinAt Real f s x := by
  let A := (Module.Basis.ofVectorSpace Real V).equivFun.toContinuousLinearEquiv
  suffices H : forallᵐ x, x in s -> DifferentiableWithinAt Real (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    exact (ContinuousLinearEquiv.comp_differentiableWithinAt_iff _).mp (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_locallyBoundedVariationOn h

/--
theorem `_root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` / 定理 `_root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`

English:
theorem _root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc
  statement: {f : Real -> V} {a b : Real}
  proof: by
  have h₁ : forallᵐ x, x != min a b := by simp [ae_iff, measure_singleton]
  have h₂ : forallᵐ x, x != max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, h₁, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc]; rw [mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hx₄.left hx₂.symm) (lt_of_le_of_ne hx₄.right hx₃))

中文:
定理 _root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc
  结论: {f : 实数 -> V} {a b : 实数}
  证明: by
  have h₁ : forallᵐ x, x != min a b := by simp [ae_iff, measure_singleton]
  have h₂ : forallᵐ x, x != max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, h₁, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc]; rw [mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hx₄.left hx₂.symm) (lt_of_le_of_ne hx₄.right hx₃))

Depends on / 依赖: Icc_mem_nhds, ae_differentiableWithinAt_of_mem, ae_iff, differentiableAt, filter_upwards, h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, locallyBoundedVariationOn, lt_of_le_of_ne, measure_singleton, mem_Icc
-/
theorem _root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc {f : Real -> V} {a b : Real}
    (h : BoundedVariationOn f (uIcc a b)) : forallᵐ x, x in uIcc a b -> DifferentiableAt Real f x := by
  have h₁ : forallᵐ x, x != min a b := by simp [ae_iff, measure_singleton]
  have h₂ : forallᵐ x, x != max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, h₁, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc]; rw [mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hx₄.left hx₂.symm) (lt_of_le_of_ne hx₄.right hx₃))

/--
theorem `ae_differentiableWithinAt` / 定理 `ae_differentiableWithinAt`

English:
theorem ae_differentiableWithinAt
  statement: {f : Real -> V} {s : Set Real} (h : LocallyBoundedVariationOn f s)
  proof: by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiableWithinAt_of_mem

中文:
定理 ae_differentiableWithinAt
  结论: {f : 实数 -> V} {s : 集合 实数} (h : LocallyBoundedVariationOn f s)
  证明: by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiableWithinAt_of_mem

Depends on / 依赖: ae_differentiableWithinAt_of_mem, ae_restrict_iff, h.ae_differentiableWithinAt_of_mem
-/
theorem ae_differentiableWithinAt {f : Real -> V} {s : Set Real} (h : LocallyBoundedVariationOn f s)
    (hs : MeasurableSet s) : forallᵐ x ∂volume.restrict s, DifferentiableWithinAt Real f s x := by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiableWithinAt_of_mem

/--
theorem `ae_differentiableAt` / 定理 `ae_differentiableAt`

English:
theorem ae_differentiableAt
  given: {f : Real -> V} (h : LocallyBoundedVariationOn f univ)
  proof: by
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx
  exact hx (mem_univ _)

中文:
定理 ae_differentiableAt
  条件: {f : 实数 -> V} (h : LocallyBoundedVariationOn f univ)
  证明: by
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx
  exact hx (mem_univ _)

Depends on / 依赖: ae_differentiableWithinAt_of_mem, differentiableWithinAt_univ, filter_upwards, h.ae_differentiableWithinAt_of_mem, mem_univ
-/
theorem ae_differentiableAt {f : Real -> V} (h : LocallyBoundedVariationOn f univ) :
    forallᵐ x, DifferentiableAt Real f x := by
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx
  exact hx (mem_univ _)

end LocallyBoundedVariationOn

/--
theorem `LipschitzOnWith.ae_differentiableWithinAt_of_mem_real` / 定理 `LipschitzOnWith.ae_differentiableWithinAt_of_mem_real`

English:
theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem_real
  statement: {C : Real>=0} {f : Real -> V} {s : Set Real}
  proof: h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

中文:
定理 LipschitzOnWith.ae_differentiableWithinAt_of_mem_real
  结论: {C : 实数>=0} {f : 实数 -> V} {s : 集合 实数}
  证明: h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

Depends on / 依赖: ae_differentiableWithinAt_of_mem, h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, locallyBoundedVariationOn
-/
theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem_real {C : Real>=0} {f : Real -> V} {s : Set Real}
    (h : LipschitzOnWith C f s) : forallᵐ x, x in s -> DifferentiableWithinAt Real f s x :=
  h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

/--
theorem `LipschitzOnWith.ae_differentiableWithinAt_real` / 定理 `LipschitzOnWith.ae_differentiableWithinAt_real`

English:
theorem LipschitzOnWith.ae_differentiableWithinAt_real
  statement: {C : Real>=0} {f : Real -> V} {s : Set Real}
  proof: h.locallyBoundedVariationOn.ae_differentiableWithinAt hs

中文:
定理 LipschitzOnWith.ae_differentiableWithinAt_real
  结论: {C : 实数>=0} {f : 实数 -> V} {s : 集合 实数}
  证明: h.locallyBoundedVariationOn.ae_differentiableWithinAt hs

Depends on / 依赖: ae_differentiableWithinAt, h.locallyBoundedVariationOn.ae_differentiableWithinAt, locallyBoundedVariationOn
-/
theorem LipschitzOnWith.ae_differentiableWithinAt_real {C : Real>=0} {f : Real -> V} {s : Set Real}
    (h : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    forallᵐ x ∂volume.restrict s, DifferentiableWithinAt Real f s x :=
  h.locallyBoundedVariationOn.ae_differentiableWithinAt hs

/--
theorem `LipschitzWith.ae_differentiableAt_real` / 定理 `LipschitzWith.ae_differentiableAt_real`

English:
theorem LipschitzWith.ae_differentiableAt_real
  given: {C : Real>=0} {f : Real -> V} (h : LipschitzWith C f)
  proof: (h.locallyBoundedVariationOn univ).ae_differentiableAt

中文:
定理 LipschitzWith.ae_differentiableAt_real
  条件: {C : 实数>=0} {f : 实数 -> V} (h : LipschitzWith C f)
  证明: (h.locallyBoundedVariationOn univ).ae_differentiableAt

Depends on / 依赖: ae_differentiableAt, h.locallyBoundedVariationOn, locallyBoundedVariationOn
-/
theorem LipschitzWith.ae_differentiableAt_real {C : Real>=0} {f : Real -> V} (h : LipschitzWith C f) :
    forallᵐ x, DifferentiableAt Real f x :=
  (h.locallyBoundedVariationOn univ).ae_differentiableAt
