/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Integrability in `WithLp`

We prove that `f : X → PiLp q E` is in `Lᵖ` if and only if for all `i`, `f · i` is in `Lᵖ`.
We do the same for `f : X → WithLp q (E × F)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p q : Real>=0∞} [Fact (1 <= q)]

section Pi

variable {ι : Type*} [Fintype ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] {f : X -> PiLp q E}

/--
lemma `memLp_piLp_iff` / 引理 `memLp_piLp_iff`

English:
lemma memLp_piLp_iff
  statement: MemLp f p μ ↔ forall i, MemLp (f · i) p μ
  proof: by
  simp_rw [← memLp_pi_iff, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
.symm (PiLp.antilipschitzWith_ofLp q E) (by simp)

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff

中文:
引理 memLp_piLp_iff
  结论: MemLp f p μ ↔ 对任意 i, MemLp (f · i) p μ
  证明: by
  simp_rw [← memLp_pi_iff, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
.symm (PiLp.antilipschitzWith_ofLp q E) (by simp)

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff

Depends on / 依赖: Function, Function.comp_apply, PiLp.antilipschitzWith_ofLp, PiLp.lipschitzWith_ofLp, WithLp, WithLp.ofLp, antilipschitzWith_ofLp, comp_apply, lipschitzWith_ofLp, memLp_comp_iff_of_antilipschitz, memLp_pi_iff, simp_rw
-/
lemma memLp_piLp_iff : MemLp f p μ ↔ forall i, MemLp (f · i) p μ := by
  simp_rw [← memLp_pi_iff, ← Function.comp_apply (f := WithLp.ofLp)]
  exact (PiLp.lipschitzWith_ofLp q E).memLp_comp_iff_of_antilipschitz
.symm (PiLp.antilipschitzWith_ofLp q E) (by simp)

alias ⟨MemLp.eval_piLp, MemLp.of_eval_piLp⟩ := memLp_piLp_iff

/--
lemma `integrable_piLp_iff` / 引理 `integrable_piLp_iff`

English:
lemma integrable_piLp_iff
  statement: Integrable f μ ↔ forall i, Integrable (f · i) μ
  proof: by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

中文:
引理 integrable_piLp_iff
  结论: 整数egrable f μ ↔ 对任意 i, 整数egrable (f · i) μ
  证明: by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

Depends on / 依赖: memLp_one_iff_integrable, memLp_piLp_iff, simp_rw
-/
lemma integrable_piLp_iff : Integrable f μ ↔ forall i, Integrable (f · i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_piLp_iff]

alias ⟨Integrable.eval_piLp, Integrable.of_eval_piLp⟩ := integrable_piLp_iff

variable [forall i, NormedSpace Real (E i)] [forall i, CompleteSpace (E i)]

/--
lemma `eval_integral_piLp` / 引理 `eval_integral_piLp`

English:
lemma eval_integral_piLp
  given: (hf : forall i, Integrable (f · i) μ) (i : ι)
  proof: by
  rw [← PiLp.proj_apply (𝕜 := Real) q E i (∫ x]; rw [f x ∂μ)]; rw [← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hf

中文:
引理 eval_integral_piLp
  条件: (hf : 对任意 i, 整数egrable (f · i) μ) (i : ι)
  证明: by
  rw [← PiLp.proj_apply (𝕜 := Real) q E i (∫ x]; rw [f x ∂μ)]; rw [← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, Integrable, Integrable.of_eval_piLp, PiLp.proj_apply, integral_comp_comm, of_eval_piLp, proj_apply
-/
lemma eval_integral_piLp (hf : forall i, Integrable (f · i) μ) (i : ι) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  rw [← PiLp.proj_apply (𝕜 := Real) q E i (∫ x]; rw [f x ∂μ)]; rw [← ContinuousLinearMap.integral_comp_comm]
  · simp
  exact Integrable.of_eval_piLp hf

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : X -> WithLp q (E × F)}

/--
lemma `memLp_prodLp_iff` / 引理 `memLp_prodLp_iff`

English:
lemma memLp_prodLp_iff
  proof: by
  simp_rw [← WithLp.ofLp_fst, ← WithLp.ofLp_snd, ← memLp_prod_iff]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
.symm (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp)

中文:
引理 memLp_prodLp_iff
  证明: by
  simp_rw [← WithLp.ofLp_fst, ← WithLp.ofLp_snd, ← memLp_prod_iff]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
.symm (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp)

Depends on / 依赖: WithLp, WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.prod_antilipschitzWith_ofLp, WithLp.prod_lipschitzWith_ofLp, memLp_comp_iff_of_antilipschitz, memLp_prod_iff, ofLp_fst, ofLp_snd, prod_antilipschitzWith_ofLp, prod_lipschitzWith_ofLp, simp_rw
-/
lemma memLp_prodLp_iff :
    MemLp f p μ ↔ MemLp (fun x => (f x).fst) p μ ∧ MemLp (fun x => (f x).snd) p μ := by
  simp_rw [← WithLp.ofLp_fst, ← WithLp.ofLp_snd, ← memLp_prod_iff]
  exact (WithLp.prod_lipschitzWith_ofLp q E F).memLp_comp_iff_of_antilipschitz
.symm (WithLp.prod_antilipschitzWith_ofLp q E F) (by simp)

/--
lemma `MemLp.prodLp_fst` / 引理 `MemLp.prodLp_fst`

English:
lemma MemLp.prodLp_fst
  given: (h : MemLp f p μ)
  statement: MemLp (fun x => (f x).fst) p μ
  proof: .1 memLp_prodLp_iff.1 h

中文:
引理 MemLp.prodLp_fst
  条件: (h : MemLp f p μ)
  结论: MemLp (fun x => (f x).fst) p μ
  证明: .1 memLp_prodLp_iff.1 h

Depends on / 依赖: memLp_prodLp_iff
-/
lemma MemLp.prodLp_fst (h : MemLp f p μ) : MemLp (fun x => (f x).fst) p μ :=
.1 memLp_prodLp_iff.1 h

/--
lemma `MemLp.prodLp_snd` / 引理 `MemLp.prodLp_snd`

English:
lemma MemLp.prodLp_snd
  given: (h : MemLp f p μ)
  statement: MemLp (fun x => (f x).snd) p μ
  proof: .2 memLp_prodLp_iff.1 h

alias ⟨_, MemLp.of_fst_of_snd_prodLp⟩ := memLp_prodLp_iff

中文:
引理 MemLp.prodLp_snd
  条件: (h : MemLp f p μ)
  结论: MemLp (fun x => (f x).snd) p μ
  证明: .2 memLp_prodLp_iff.1 h

alias ⟨_, MemLp.of_fst_of_snd_prodLp⟩ := memLp_prodLp_iff

Depends on / 依赖: memLp_prodLp_iff
-/
lemma MemLp.prodLp_snd (h : MemLp f p μ) : MemLp (fun x => (f x).snd) p μ :=
.2 memLp_prodLp_iff.1 h

alias ⟨_, MemLp.of_fst_of_snd_prodLp⟩ := memLp_prodLp_iff

/--
lemma `integrable_prodLp_iff` / 引理 `integrable_prodLp_iff`

English:
lemma integrable_prodLp_iff
  proof: by
  simp_rw [← memLp_one_iff_integrable, memLp_prodLp_iff]

中文:
引理 integrable_prodLp_iff
  证明: by
  simp_rw [← memLp_one_iff_integrable, memLp_prodLp_iff]

Depends on / 依赖: memLp_one_iff_integrable, memLp_prodLp_iff, simp_rw
-/
lemma integrable_prodLp_iff :
    Integrable f μ ↔
    Integrable (fun x => (f x).fst) μ ∧
    Integrable (fun x => (f x).snd) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_prodLp_iff]

/--
lemma `Integrable.prodLp_fst` / 引理 `Integrable.prodLp_fst`

English:
lemma Integrable.prodLp_fst
  given: (h : Integrable f μ)
  statement: Integrable (fun x => (f x).fst) μ
  proof: .1 integrable_prodLp_iff.1 h

中文:
引理 Integrable.prodLp_fst
  条件: (h : 整数egrable f μ)
  结论: 整数egrable (fun x => (f x).fst) μ
  证明: .1 integrable_prodLp_iff.1 h

Depends on / 依赖: integrable_prodLp_iff
-/
lemma Integrable.prodLp_fst (h : Integrable f μ) : Integrable (fun x => (f x).fst) μ :=
.1 integrable_prodLp_iff.1 h

/--
lemma `Integrable.prodLp_snd` / 引理 `Integrable.prodLp_snd`

English:
lemma Integrable.prodLp_snd
  given: (h : Integrable f μ)
  statement: Integrable (fun x => (f x).snd) μ
  proof: .2 integrable_prodLp_iff.1 h

alias ⟨_, Integrable.of_fst_of_snd_prodLp⟩ := integrable_prodLp_iff

中文:
引理 Integrable.prodLp_snd
  条件: (h : 整数egrable f μ)
  结论: 整数egrable (fun x => (f x).snd) μ
  证明: .2 integrable_prodLp_iff.1 h

alias ⟨_, Integrable.of_fst_of_snd_prodLp⟩ := integrable_prodLp_iff

Depends on / 依赖: integrable_prodLp_iff
-/
lemma Integrable.prodLp_snd (h : Integrable f μ) : Integrable (fun x => (f x).snd) μ :=
.2 integrable_prodLp_iff.1 h

alias ⟨_, Integrable.of_fst_of_snd_prodLp⟩ := integrable_prodLp_iff

variable [NormedSpace Real E] [NormedSpace Real F]

/--
theorem `fst_integral_withLp` / 定理 `fst_integral_withLp`

English:
theorem fst_integral_withLp
  given: [CompleteSpace F] (hf : Integrable f μ)
  proof: by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q Real E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm]; rw [fst_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

中文:
定理 fst_integral_withLp
  条件: [CompleteSpace F] (hf : 整数egrable f μ)
  证明: by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q Real E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm]; rw [fst_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.integrable_comp_iff, ContinuousLinearEquiv.integral_comp_comm, WithLp, WithLp.ofLp_fst, WithLp.prodContinuousLinearEquiv, fst_integral, integrable_comp_iff, integral_comp_comm, ofLp_fst, prodContinuousLinearEquiv
-/
theorem fst_integral_withLp [CompleteSpace F] (hf : Integrable f μ) :
    (∫ x, f x ∂μ).fst = ∫ x, (f x).fst ∂μ := by
  rw [← WithLp.ofLp_fst]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q Real E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm]; rw [fst_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

/--
theorem `snd_integral_withLp` / 定理 `snd_integral_withLp`

English:
theorem snd_integral_withLp
  given: [CompleteSpace E] (hf : Integrable f μ)
  proof: by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q Real E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm]; rw [snd_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

中文:
定理 snd_integral_withLp
  条件: [CompleteSpace E] (hf : 整数egrable f μ)
  证明: by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q Real E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm]; rw [snd_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.integrable_comp_iff, ContinuousLinearEquiv.integral_comp_comm, WithLp, WithLp.ofLp_snd, WithLp.prodContinuousLinearEquiv, integrable_comp_iff, integral_comp_comm, ofLp_snd, prodContinuousLinearEquiv, snd_integral
-/
theorem snd_integral_withLp [CompleteSpace E] (hf : Integrable f μ) :
    (∫ x, f x ∂μ).snd = ∫ x, (f x).snd ∂μ := by
  rw [← WithLp.ofLp_snd]
  conv => enter [1, 1]; change WithLp.prodContinuousLinearEquiv q Real E F _
  rw [← ContinuousLinearEquiv.integral_comp_comm]; rw [snd_integral]
  · rfl
  · exact (ContinuousLinearEquiv.integrable_comp_iff _).2 hf

end Prod

end MeasureTheory
