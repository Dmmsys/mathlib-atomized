/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability in a product space

We prove that `f : X → Π i, E i` is in `Lᵖ` if and only if for all `i`, `f · i` is in `Lᵖ`.
We do the same for `f : X → (E × F)`.
-/

public section

namespace MeasureTheory

open scoped ENNReal

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} {p : Real>=0∞}

section Pi

variable {ι : Type*} [Fintype ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)]
    {f : X -> Π i, E i}

/--
lemma `memLp_pi_iff` / 引理 `memLp_pi_iff`

English:
lemma memLp_pi_iff
  statement: MemLp f p μ ↔ forall i, MemLp (f · i) p μ where
  proof: (LipschitzWith.eval (α := E) i).comp_memLp rfl hf
  mpr hf := by
    classical
    have : f = ∑ i, (Pi.single i) ∘ (f · i) := by ext; simp
    rw [this]
    refine memLp_finsetSum' _ fun i _ => ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hf i)

alias ⟨MemLp.eval, MemLp.of_eval⟩ 

中文:
引理 memLp_pi_iff
  结论: MemLp f p μ ↔ 对任意 i, MemLp (f · i) p μ where
  证明: (LipschitzWith.eval (α := E) i).comp_memLp rfl hf
  mpr hf := by
    classical
    have : f = ∑ i, (Pi.single i) ∘ (f · i) := by ext; simp
    rw [this]
    refine memLp_finsetSum' _ fun i _ => ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hf i)

alias ⟨MemLp.eval, MemLp.of_eval⟩ 

Depends on / 依赖: LipschitzWith, LipschitzWith.eval, comp_memLp
-/
lemma memLp_pi_iff : MemLp f p μ ↔ forall i, MemLp (f · i) p μ where
  mp hf i := (LipschitzWith.eval (α := E) i).comp_memLp rfl hf
  mpr hf := by
    classical
    have : f = ∑ i, (Pi.single i) ∘ (f · i) := by ext; simp
    rw [this]
    refine memLp_finsetSum' _ fun i _ => ?_
    exact (Isometry.single i).lipschitz.comp_memLp (by simp) (hf i)

alias ⟨MemLp.eval, MemLp.of_eval⟩ := memLp_pi_iff

/--
lemma `integrable_pi_iff` / 引理 `integrable_pi_iff`

English:
lemma integrable_pi_iff
  statement: Integrable f μ ↔ forall i, Integrable (f · i) μ
  proof: by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

中文:
引理 integrable_pi_iff
  结论: 整数egrable f μ ↔ 对任意 i, 整数egrable (f · i) μ
  证明: by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

Depends on / 依赖: memLp_one_iff_integrable, memLp_pi_iff, simp_rw
-/
lemma integrable_pi_iff : Integrable f μ ↔ forall i, Integrable (f · i) μ := by
  simp_rw [← memLp_one_iff_integrable, memLp_pi_iff]

alias ⟨Integrable.eval, Integrable.of_eval⟩ := integrable_pi_iff

variable [forall i, NormedSpace Real (E i)] [forall i, CompleteSpace (E i)]

/--
lemma `eval_integral` / 引理 `eval_integral`

English:
lemma eval_integral
  given: (hf : forall i, Integrable (f · i) μ) (i : ι)
  proof: by
  simp [← ContinuousLinearMap.proj_apply (R := Real) i (∫ x, f x ∂μ),
    ← ContinuousLinearMap.integral_comp_comm _ (Integrable.of_eval hf)]

中文:
引理 eval_integral
  条件: (hf : 对任意 i, 整数egrable (f · i) μ) (i : ι)
  证明: by
  simp [← ContinuousLinearMap.proj_apply (R := Real) i (∫ x, f x ∂μ),
    ← ContinuousLinearMap.integral_comp_comm _ (Integrable.of_eval hf)]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, ContinuousLinearMap.proj_apply, Integrable, Integrable.of_eval, integral_comp_comm, of_eval, proj_apply
-/
lemma eval_integral (hf : forall i, Integrable (f · i) μ) (i : ι) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  simp [← ContinuousLinearMap.proj_apply (R := Real) i (∫ x, f x ∂μ),
    ← ContinuousLinearMap.integral_comp_comm _ (Integrable.of_eval hf)]

end Pi

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : X -> E × F}

/--
lemma `memLp_prod_iff` / 引理 `memLp_prod_iff`

English:
lemma memLp_prod_iff
  proof: ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
    LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : f = (AddMonoidHom.inl E F) ∘ (fun x => (f x).fst) +
        (AddMonoidHom.inr E F) ∘ (fun x => (f x).snd) := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Iso

中文:
引理 memLp_prod_iff
  证明: ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
    LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : f = (AddMonoidHom.inl E F) ∘ (fun x => (f x).fst) +
        (AddMonoidHom.inr E F) ∘ (fun x => (f x).snd) := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Iso

Depends on / 依赖: LipschitzWith, LipschitzWith.prod_fst.comp_memLp, comp_memLp, prod_fst
-/
lemma memLp_prod_iff :
    MemLp f p μ ↔ MemLp (fun x => (f x).fst) p μ ∧ MemLp (fun x => (f x).snd) p μ where
  mp h := ⟨LipschitzWith.prod_fst.comp_memLp (by simp) h,
    LipschitzWith.prod_snd.comp_memLp (by simp) h⟩
  mpr h := by
    have : f = (AddMonoidHom.inl E F) ∘ (fun x => (f x).fst) +
        (AddMonoidHom.inr E F) ∘ (fun x => (f x).snd) := by
      ext; all_goals simp
    rw [this]
    exact MemLp.add (Isometry.inl.lipschitz.comp_memLp (by simp) h.1)
      (Isometry.inr.lipschitz.comp_memLp (by simp) h.2)

/--
lemma `MemLp.fst` / 引理 `MemLp.fst`

English:
lemma MemLp.fst
  given: (h : MemLp f p μ)
  statement: MemLp (fun x => (f x).fst) p μ
  proof: .1 memLp_prod_iff.1 h

中文:
引理 MemLp.fst
  条件: (h : MemLp f p μ)
  结论: MemLp (fun x => (f x).fst) p μ
  证明: .1 memLp_prod_iff.1 h

Depends on / 依赖: memLp_prod_iff
-/
lemma MemLp.fst (h : MemLp f p μ) : MemLp (fun x => (f x).fst) p μ :=
.1 memLp_prod_iff.1 h

/--
lemma `MemLp.snd` / 引理 `MemLp.snd`

English:
lemma MemLp.snd
  given: (h : MemLp f p μ)
  statement: MemLp (fun x => (f x).snd) p μ
  proof: .2 memLp_prod_iff.1 h

alias ⟨_, MemLp.of_fst_snd⟩ := memLp_prod_iff

中文:
引理 MemLp.snd
  条件: (h : MemLp f p μ)
  结论: MemLp (fun x => (f x).snd) p μ
  证明: .2 memLp_prod_iff.1 h

alias ⟨_, MemLp.of_fst_snd⟩ := memLp_prod_iff

Depends on / 依赖: Irrefl, IsTrans, Std.Asymm, Std.Irrefl, asymm_of_isTrans_of_irrefl, memLp_prod_iff
-/
lemma MemLp.snd (h : MemLp f p μ) : MemLp (fun x => (f x).snd) p μ :=
.2 memLp_prod_iff.1 h

alias ⟨_, MemLp.of_fst_snd⟩ := memLp_prod_iff

end Prod

end MeasureTheory
