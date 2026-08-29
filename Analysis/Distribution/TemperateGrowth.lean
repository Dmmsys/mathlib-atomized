/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.MoveAdd

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Functions and measures of temperate growth -/

@[expose] public section

noncomputable section

open scoped Nat NNReal ContDiff

open Asymptotics

variable {ι 𝕜 R D E F G H : Type*}

namespace Function

variable [NormedAddCommGroup E] [NormedSpace Real E]
variable [NormedAddCommGroup F] [NormedSpace Real F]

/-- A function is called of temperate growth if it is smooth and all iterated derivatives are
polynomially bounded. -/
@[fun_prop]
/--
Definition of `HasTemperateGrowth` / `HasTemperateGrowth` 的定义

English:
definition HasTemperateGrowth
  signature: (f : E -> F)
  body: ContDiff Real ∞ f ∧ forall n : Nat, exists (k : Nat) (C : Real), forall x, ‖iteratedFDeriv Real n f x‖ <= C * (1 + ‖x‖) ^ k

中文:
定义 有TemperateGrowth
  签名: (f : E -> F)
  定义体: ContDiff Real ∞ f ∧ forall n : Nat, exists (k : Nat) (C : Real), forall x, ‖iteratedFDeriv Real n f x‖ <= C * (1 + ‖x‖) ^ k

Depends on / 依赖: ContDiff, iteratedFDeriv
-/
def HasTemperateGrowth (f : E -> F) : Prop :=
  ContDiff Real ∞ f ∧ forall n : Nat, exists (k : Nat) (C : Real), forall x, ‖iteratedFDeriv Real n f x‖ <= C * (1 + ‖x‖) ^ k

/--
theorem `hasTemperateGrowth_iff_isBigO` / 定理 `hasTemperateGrowth_iff_isBigO`

English:
theorem hasTemperateGrowth_iff_isBigO
  given: {f : E -> F}
  proof: by
  simp_rw [Asymptotics.isBigO_top]
  congrm ContDiff Real ∞ f ∧ (forall n, exists k C, forall x, _ <= C * ?_)
  rw [norm_pow]; rw [Real.norm_of_nonneg (by positivity)]

中文:
定理 hasTemperateGrowth_iff_isBigO
  条件: {f : E -> F}
  证明: by
  simp_rw [Asymptotics.isBigO_top]
  congrm ContDiff Real ∞ f ∧ (forall n, exists k C, forall x, _ <= C * ?_)
  rw [norm_pow]; rw [Real.norm_of_nonneg (by positivity)]

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_top, ContDiff, Real.norm_of_nonneg, congrm, isBigO_top, norm_of_nonneg, norm_pow, simp_rw
-/
theorem hasTemperateGrowth_iff_isBigO {f : E -> F} :
    f.HasTemperateGrowth ↔ ContDiff Real ∞ f ∧
      forall n, exists k, iteratedFDeriv Real n f =O[⊤] (fun x => (1 + ‖x‖) ^ k) := by
  simp_rw [Asymptotics.isBigO_top]
  congrm ContDiff Real ∞ f ∧ (forall n, exists k C, forall x, _ <= C * ?_)
  rw [norm_pow]; rw [Real.norm_of_nonneg (by positivity)]

/--
theorem `HasTemperateGrowth.isBigO` / 定理 `HasTemperateGrowth.isBigO`

English:
theorem HasTemperateGrowth.isBigO
  statement: {f : E -> F}
  proof: .2 n Function.hasTemperateGrowth_iff_isBigO.mp hf_temperate

中文:
定理 有TemperateGrowth.isBigO
  结论: {f : E -> F}
  证明: .2 n Function.hasTemperateGrowth_iff_isBigO.mp hf_temperate

Depends on / 依赖: Function, Function.hasTemperateGrowth_iff_isBigO.mp, hasTemperateGrowth_iff_isBigO, hf_temperate
-/
theorem HasTemperateGrowth.isBigO {f : E -> F}
    (hf_temperate : f.HasTemperateGrowth) (n : Nat) :
    exists k, iteratedFDeriv Real n f =O[⊤] (fun x => (1 + ‖x‖) ^ k) :=
.2 n Function.hasTemperateGrowth_iff_isBigO.mp hf_temperate

/--
theorem `HasTemperateGrowth.isBigO_uniform` / 定理 `HasTemperateGrowth.isBigO_uniform`

English:
theorem HasTemperateGrowth.isBigO_uniform
  statement: {f : E -> F}
  proof: by
  choose k hk using hf_temperate.isBigO
  use (Finset.range (N + 1)).sup k
  intro n hn
  refine (hk n).trans (isBigO_of_le _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  · simp
  · exact Finset.le_sup (by simpa using hn)

中文:
定理 有TemperateGrowth.isBigO_uniform
  结论: {f : E -> F}
  证明: by
  choose k hk using hf_temperate.isBigO
  use (Finset.range (N + 1)).sup k
  intro n hn
  refine (hk n).trans (isBigO_of_le _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  · simp
  · exact Finset.le_sup (by simpa using hn)

Depends on / 依赖: Finset, Finset.le_sup, Finset.range, Real.norm_of_nonneg, hf_temperate, hf_temperate.isBigO, isBigO, isBigO_of_le, le_sup, norm_of_nonneg
-/
theorem HasTemperateGrowth.isBigO_uniform {f : E -> F}
    (hf_temperate : f.HasTemperateGrowth) (N : Nat) :
    exists k, forall n <= N, iteratedFDeriv Real n f =O[⊤] (fun x => (1 + ‖x‖) ^ k) := by
  choose k hk using hf_temperate.isBigO
  use (Finset.range (N + 1)).sup k
  intro n hn
  refine (hk n).trans (isBigO_of_le _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  · simp
  · exact Finset.le_sup (by simpa using hn)

/--
theorem `HasTemperateGrowth.norm_iteratedFDeriv_le_uniform` / 定理 `HasTemperateGrowth.norm_iteratedFDeriv_le_uniform`

English:
theorem HasTemperateGrowth.norm_iteratedFDeriv_le_uniform
  statement: {f : E -> F}
  proof: by
  rcases hf_temperate.isBigO_uniform n with ⟨k, hk⟩
  set F := fun x (N : Fin (n + 1)) => iteratedFDeriv Real N f x
  have : F =O[⊤] (fun x => (1 + ‖x‖) ^ k) := by
    simp_rw [F, isBigO_pi, Fin.forall_iff, Nat.lt_succ_iff]
    exact hk
  rcases this.exists_nonneg with ⟨C, C_nonneg, hC⟩
  simp (d

中文:
定理 有TemperateGrowth.norm_iteratedFDeriv_le_uniform
  结论: {f : E -> F}
  证明: by
  rcases hf_temperate.isBigO_uniform n with ⟨k, hk⟩
  set F := fun x (N : Fin (n + 1)) => iteratedFDeriv Real N f x
  have : F =O[⊤] (fun x => (1 + ‖x‖) ^ k) := by
    simp_rw [F, isBigO_pi, Fin.forall_iff, Nat.lt_succ_iff]
    exact hk
  rcases this.exists_nonneg with ⟨C, C_nonneg, hC⟩
  simp (d

Depends on / 依赖: C_nonneg, Fin.forall_iff, Nat.lt_succ_iff, Real.norm_of_nonneg, discharger, exists_nonneg, forall_iff, hf_temperate, hf_temperate.isBigO_uniform, isBigOWith_top, isBigO_pi, isBigO_uniform, iteratedFDeriv, lt_succ_iff, norm_of_nonneg, pi_norm_le_iff_of_nonneg, simp_rw, this.exists_nonneg
-/
theorem HasTemperateGrowth.norm_iteratedFDeriv_le_uniform {f : E -> F}
    (hf_temperate : f.HasTemperateGrowth) (n : Nat) :
    exists (k : Nat) (C : Real), 0 <= C ∧ forall N <= n, forall x : E, ‖iteratedFDeriv Real N f x‖ <= C * (1 + ‖x‖) ^ k := by
  rcases hf_temperate.isBigO_uniform n with ⟨k, hk⟩
  set F := fun x (N : Fin (n + 1)) => iteratedFDeriv Real N f x
  have : F =O[⊤] (fun x => (1 + ‖x‖) ^ k) := by
    simp_rw [F, isBigO_pi, Fin.forall_iff, Nat.lt_succ_iff]
    exact hk
  rcases this.exists_nonneg with ⟨C, C_nonneg, hC⟩
  simp (discharger := positivity) only [isBigOWith_top, Real.norm_of_nonneg,
    pi_norm_le_iff_of_nonneg, Fin.forall_iff, Nat.lt_succ_iff] at hC
  exact ⟨k, C, C_nonneg, fun N hN x => hC x N hN⟩

/--
lemma `HasTemperateGrowth.of_fderiv` / 引理 `HasTemperateGrowth.of_fderiv`

English:
lemma HasTemperateGrowth.of_fderiv
  statement: {f : E -> F}
  proof: by
  refine ⟨contDiff_succ_iff_fderiv.2 ⟨hf, by simp, h'f.1⟩, fun n => ?_⟩
  rcases n with rfl | m
  · exact ⟨k, C, fun x => by simpa using h x⟩
  · rcases h'f.2 m with ⟨k', C', h'⟩
    refine ⟨k', C', ?_⟩
    simpa [iteratedFDeriv_succ_eq_comp_right] using h'

@[fun_prop]

中文:
引理 有TemperateGrowth.of_fderiv
  结论: {f : E -> F}
  证明: by
  refine ⟨contDiff_succ_iff_fderiv.2 ⟨hf, by simp, h'f.1⟩, fun n => ?_⟩
  rcases n with rfl | m
  · exact ⟨k, C, fun x => by simpa using h x⟩
  · rcases h'f.2 m with ⟨k', C', h'⟩
    refine ⟨k', C', ?_⟩
    simpa [iteratedFDeriv_succ_eq_comp_right] using h'

@[fun_prop]

Depends on / 依赖: contDiff_succ_iff_fderiv, iteratedFDeriv_succ_eq_comp_right
-/
lemma HasTemperateGrowth.of_fderiv {f : E -> F}
    (h'f : Function.HasTemperateGrowth (fderiv Real f)) (hf : Differentiable Real f) {k : Nat} {C : Real}
    (h : forall x, ‖f x‖ <= C * (1 + ‖x‖) ^ k) :
    Function.HasTemperateGrowth f := by
  refine ⟨contDiff_succ_iff_fderiv.2 ⟨hf, by simp, h'f.1⟩, fun n => ?_⟩
  rcases n with rfl | m
  · exact ⟨k, C, fun x => by simpa using h x⟩
  · rcases h'f.2 m with ⟨k', C', h'⟩
    refine ⟨k', C', ?_⟩
    simpa [iteratedFDeriv_succ_eq_comp_right] using h'

@[fun_prop]
/--
lemma `HasTemperateGrowth.zero` / 引理 `HasTemperateGrowth.zero`

English:
lemma HasTemperateGrowth.zero
  proof: by
  refine ⟨contDiff_const, fun n => ⟨0, 0, fun x => ?_⟩⟩
  simp

@[fun_prop, simp]

中文:
引理 有TemperateGrowth.zero
  证明: by
  refine ⟨contDiff_const, fun n => ⟨0, 0, fun x => ?_⟩⟩
  simp

@[fun_prop, simp]

Depends on / 依赖: contDiff_const
-/
lemma HasTemperateGrowth.zero :
    Function.HasTemperateGrowth (fun _ : E => (0 : F)) := by
  refine ⟨contDiff_const, fun n => ⟨0, 0, fun x => ?_⟩⟩
  simp

@[fun_prop, simp]
/--
lemma `HasTemperateGrowth.const` / 引理 `HasTemperateGrowth.const`

English:
lemma HasTemperateGrowth.const
  given: (c : F)
  proof: .of_fderiv (by simpa using .zero) (differentiable_const c) (k := 0) (C := ‖c‖) (fun x => by simp)

@[fun_prop]

中文:
引理 有TemperateGrowth.const
  条件: (c : F)
  证明: .of_fderiv (by simpa using .zero) (differentiable_const c) (k := 0) (C := ‖c‖) (fun x => by simp)

@[fun_prop]

Depends on / 依赖: differentiable_const, of_fderiv
-/
lemma HasTemperateGrowth.const (c : F) :
    Function.HasTemperateGrowth (fun _ : E => c) :=
  .of_fderiv (by simpa using .zero) (differentiable_const c) (k := 0) (C := ‖c‖) (fun x => by simp)

@[fun_prop]
/--
lemma `_root_.HasCompactSupport.hasTemperateGrowth` / 引理 `_root_.HasCompactSupport.hasTemperateGrowth`

English:
lemma _root_.HasCompactSupport.hasTemperateGrowth
  statement: {f : E -> F} (h₁ : HasCompactSupport f)
  proof: by
  refine ⟨h₂, fun n => ?_⟩
  set g := fun x => ‖iteratedFDeriv Real n f x‖
  have hg : Continuous g := (h₂.continuous_iteratedFDeriv <| mod_cast le_top).norm
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge_of_hasCompactSupport ((h₁.iteratedFDeriv _).norm)
  refine ⟨0, g x₀, fun x => ?_⟩
  simpa using h

中文:
引理 _root_.HasCompactSupport.hasTemperateGrowth
  结论: {f : E -> F} (h₁ : HasCompactSupport f)
  证明: by
  refine ⟨h₂, fun n => ?_⟩
  set g := fun x => ‖iteratedFDeriv Real n f x‖
  have hg : Continuous g := (h₂.continuous_iteratedFDeriv <| mod_cast le_top).norm
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge_of_hasCompactSupport ((h₁.iteratedFDeriv _).norm)
  refine ⟨0, g x₀, fun x => ?_⟩
  simpa using h

Depends on / 依赖: Continuous, continuous_iteratedFDeriv, exists_forall_ge_of_hasCompactSupport, hg.exists_forall_ge_of_hasCompactSupport, iteratedFDeriv, le_top, mod_cast
-/
lemma _root_.HasCompactSupport.hasTemperateGrowth {f : E -> F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff Real ∞ f) : f.HasTemperateGrowth := by
  refine ⟨h₂, fun n => ?_⟩
  set g := fun x => ‖iteratedFDeriv Real n f x‖
  have hg : Continuous g := (h₂.continuous_iteratedFDeriv <| mod_cast le_top).norm
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge_of_hasCompactSupport ((h₁.iteratedFDeriv _).norm)
  refine ⟨0, g x₀, fun x => ?_⟩
  simpa using hx₀ x

/--
theorem `HasTemperateGrowth.comp'` / 定理 `HasTemperateGrowth.comp'`

English:
theorem HasTemperateGrowth.comp'
  statement: [NormedAddCommGroup D] [NormedSpace Real D] {g : E -> F} {f : D -> E}
  proof: by
  refine ⟨hg₁.comp_contDiff hf.1 (ht ⟨·, rfl⟩), fun n => ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg₂ n
  have h₁' : forall x, ‖f x‖ <= C₁ * (1 + ‖x‖) ^ k₁ := by simpa using h₁ 0
  set C₃ := ∑ k in Finset.range (k₂ + 1), C₂ * (k₂.choose k

中文:
定理 有TemperateGrowth.comp'
  结论: [赋范交换加群 D] [赋范空间 实数 D] {g : E -> F} {f : D -> E}
  证明: by
  refine ⟨hg₁.comp_contDiff hf.1 (ht ⟨·, rfl⟩), fun n => ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg₂ n
  have h₁' : forall x, ‖f x‖ <= C₁ * (1 + ‖x‖) ^ k₁ := by simpa using h₁ 0
  set C₃ := ∑ k in Finset.range (k₂ + 1), C₂ * (k₂.choose k

Depends on / 依赖: Finset, Finset.range, comp_contDiff, hf.norm_iteratedFDeriv_le_uniform, iteratedFDerivWithin, norm_iteratedFDeriv_le_uniform
-/
theorem HasTemperateGrowth.comp' [NormedAddCommGroup D] [NormedSpace Real D] {g : E -> F} {f : D -> E}
    {t : Set E} (ht : Set.range f subseteq t) (ht' : UniqueDiffOn Real t) (hg₁ : ContDiffOn Real ∞ g t)
    (hg₂ : forall N, exists k C, exists (_hC : 0 <= C), forall n <= N, forall x in t,
    ‖iteratedFDerivWithin Real n g t x‖ <= C * (1 + ‖x‖) ^ k)
    (hf : f.HasTemperateGrowth) : (g ∘ f).HasTemperateGrowth := by
  refine ⟨hg₁.comp_contDiff hf.1 (ht ⟨·, rfl⟩), fun n => ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg₂ n
  have h₁' : forall x, ‖f x‖ <= C₁ * (1 + ‖x‖) ^ k₁ := by simpa using h₁ 0
  set C₃ := ∑ k in Finset.range (k₂ + 1), C₂ * (k₂.choose k : Real) * (C₁ ^ k)
  use k₁ * k₂ + k₁ * n, n ! * C₃ * (1 + C₁) ^ n
  intro x
  have hg' : forall i, i <= n -> ‖iteratedFDerivWithin Real i g t (f x)‖ <= C₃ * (1 + ‖x‖) ^ (k₁ * k₂) := by
    intro i hi
    calc _ <= C₂ * (1 + ‖f x‖) ^ k₂ := h₂ i hi (f x) (ht ⟨x, rfl⟩)
      _ = ∑ i in Finset.range (k₂ + 1), C₂ * (‖f x‖ ^ i * (k₂.choose i)) := by
        rw [add_comm]; rw [add_pow]; rw [Finset.mul_sum]
        simp
      _ <= ∑ i in Finset.range (k₂ + 1), C₂ * (k₂.choose i) * C₁ ^ i * (1 + ‖x‖) ^ (k₁ * k₂) := by
        apply Finset.sum_le_sum
        intro i hi
        grw [h₁']
        simp_rw [mul_pow, ← pow_mul]
        move_mul [← (k₂.choose _ : Real), C₂]
        gcongr
        · simp
        · grind
      _ = _ := by simp [C₃, Finset.sum_mul]
  have hf' : forall i, 1 <= i -> i <= n -> ‖iteratedFDeriv Real i f x‖ <= ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ i := by
    intro i hi hi'
    calc _ <= C₁ * (1 + ‖x‖) ^ k₁ := h₁ i hi' x
      _ <= (1 + C₁) * (1 + ‖x‖) ^ k₁ := by gcongr; simp
      _ <= _ := by
        apply le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC₁]) (by simp [one_le_pow₀]))
        grind
  calc _ <= n ! * (C₃ * (1 + ‖x‖) ^ (k₁ * k₂)) * ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ n :=
      norm_iteratedFDeriv_comp_le' ht ht' hg₁ hf.1 (mod_cast le_top) x hg' hf'
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- Composition of two temperate growth functions is of temperate growth. -/
@[fun_prop]
/--
theorem `HasTemperateGrowth.comp` / 定理 `HasTemperateGrowth.comp`

English:
theorem HasTemperateGrowth.comp
  statement: [NormedAddCommGroup D] [NormedSpace Real D] {g : E -> F} {f : D -> E}
  proof: by
  apply hf.comp' (t := Set.univ)
  · simp
  · simp
  · rw [contDiffOn_univ]
    exact hg.1
  · simpa [iteratedFDerivWithin_univ] using hg.norm_iteratedFDeriv_le_uniform

中文:
定理 有TemperateGrowth.comp
  结论: [赋范交换加群 D] [赋范空间 实数 D] {g : E -> F} {f : D -> E}
  证明: by
  apply hf.comp' (t := Set.univ)
  · simp
  · simp
  · rw [contDiffOn_univ]
    exact hg.1
  · simpa [iteratedFDerivWithin_univ] using hg.norm_iteratedFDeriv_le_uniform

Depends on / 依赖: Set.univ, contDiffOn_univ, hf.comp, hg.norm_iteratedFDeriv_le_uniform, iteratedFDerivWithin_univ, norm_iteratedFDeriv_le_uniform
-/
theorem HasTemperateGrowth.comp [NormedAddCommGroup D] [NormedSpace Real D] {g : E -> F} {f : D -> E}
    (hg : g.HasTemperateGrowth) (hf : f.HasTemperateGrowth) : (g ∘ f).HasTemperateGrowth := by
  apply hf.comp' (t := Set.univ)
  · simp
  · simp
  · rw [contDiffOn_univ]
    exact hg.1
  · simpa [iteratedFDerivWithin_univ] using hg.norm_iteratedFDeriv_le_uniform

section Addition

variable {f g : E -> F}

@[to_fun (attr := fun_prop)]
/--
theorem `HasTemperateGrowth.neg` / 定理 `HasTemperateGrowth.neg`

English:
theorem HasTemperateGrowth.neg
  given: (hf : f.HasTemperateGrowth)
  statement: (-f).HasTemperateGrowth
  proof: by
  refine ⟨hf.1.neg, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 n
  exact ⟨k, C, fun x => by simpa [iteratedFDeriv_neg_apply] using h x⟩

@[to_fun (attr := fun_prop)]

中文:
定理 有TemperateGrowth.neg
  条件: (hf : f.有TemperateGrowth)
  结论: (-f).有TemperateGrowth
  证明: by
  refine ⟨hf.1.neg, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 n
  exact ⟨k, C, fun x => by simpa [iteratedFDeriv_neg_apply] using h x⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: iteratedFDeriv_neg_apply
-/
theorem HasTemperateGrowth.neg (hf : f.HasTemperateGrowth) : (-f).HasTemperateGrowth := by
  refine ⟨hf.1.neg, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 n
  exact ⟨k, C, fun x => by simpa [iteratedFDeriv_neg_apply] using h x⟩

@[to_fun (attr := fun_prop)]
/--
theorem `HasTemperateGrowth.add` / 定理 `HasTemperateGrowth.add`

English:
theorem HasTemperateGrowth.add
  given: (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth)
  proof: by
  rw [hasTemperateGrowth_iff_isBigO] at *
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨k₁, h₁⟩ := hf.2 n
  obtain ⟨k₂, h₂⟩ := hg.2 n
  use max k₁ k₂
  rw [iteratedFDeriv_add (hf.1.of_le <| mod_cast le_top) (hg.1.of_le <| mod_cast le_top)]
  have : 1 <=ᶠ[⊤] fun (x : E) => 1 + ‖x‖ := by
    filt

中文:
定理 有TemperateGrowth.add
  条件: (hf : f.有TemperateGrowth) (hg : g.有TemperateGrowth)
  证明: by
  rw [hasTemperateGrowth_iff_isBigO] at *
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨k₁, h₁⟩ := hf.2 n
  obtain ⟨k₂, h₂⟩ := hg.2 n
  use max k₁ k₂
  rw [iteratedFDeriv_add (hf.1.of_le <| mod_cast le_top) (hg.1.of_le <| mod_cast le_top)]
  have : 1 <=ᶠ[⊤] fun (x : E) => 1 + ‖x‖ := by
    filt

Depends on / 依赖: IsBigO, IsBigO.pow_of_le_right, filter_upwards, hasTemperateGrowth_iff_isBigO, iteratedFDeriv_add, le_add_iff_nonneg_right, le_max_left, le_max_right, le_top, mod_cast, of_le, pow_of_le_right
-/
theorem HasTemperateGrowth.add (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (f + g).HasTemperateGrowth := by
  rw [hasTemperateGrowth_iff_isBigO] at *
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨k₁, h₁⟩ := hf.2 n
  obtain ⟨k₂, h₂⟩ := hg.2 n
  use max k₁ k₂
  rw [iteratedFDeriv_add (hf.1.of_le <| mod_cast le_top) (hg.1.of_le <| mod_cast le_top)]
  have : 1 <=ᶠ[⊤] fun (x : E) => 1 + ‖x‖ := by
    filter_upwards with _ using (le_add_iff_nonneg_right _).mpr (by positivity)
  exact (h₁.trans (IsBigO.pow_of_le_right this (k₁.le_max_left k₂))).add
    (h₂.trans (IsBigO.pow_of_le_right this (k₁.le_max_right k₂)))

@[to_fun (attr := fun_prop)]
/--
theorem `HasTemperateGrowth.sub` / 定理 `HasTemperateGrowth.sub`

English:
theorem HasTemperateGrowth.sub
  given: (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth)
  proof: by
  convert hf.add hg.neg
  grind

@[fun_prop]

中文:
定理 有TemperateGrowth.sub
  条件: (hf : f.有TemperateGrowth) (hg : g.有TemperateGrowth)
  证明: by
  convert hf.add hg.neg
  grind

@[fun_prop]

Depends on / 依赖: convert, hf.add, hg.neg
-/
theorem HasTemperateGrowth.sub (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (f - g).HasTemperateGrowth := by
  convert hf.add hg.neg
  grind

@[fun_prop]
/--
theorem `HasTemperateGrowth.sum` / 定理 `HasTemperateGrowth.sum`

English:
theorem HasTemperateGrowth.sum
  statement: {f : ι -> E -> F} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨hf, h⟩ := by simpa using! hf
    simpa [has] using! hf.add (ih h)

中文:
定理 有TemperateGrowth.求和
  结论: {f : ι -> E -> F} {s : 有限集 ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨hf, h⟩ := by simpa using! hf
    simpa [has] using! hf.add (ih h)

Depends on / 依赖: Finset, Finset.induction_on, classical, hf.add, induction_on, insert
-/
theorem HasTemperateGrowth.sum {f : ι -> E -> F} {s : Finset ι}
    (hf : forall i in s, (f i).HasTemperateGrowth) : (∑ i in s, f i ·).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨hf, h⟩ := by simpa using! hf
    simpa [has] using! hf.add (ih h)

end Addition

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra Real 𝕜]
  [NormedAddCommGroup D] [NormedSpace Real D]
  [NormedAddCommGroup G] [NormedSpace Real G]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The product of two functions of temperate growth is again of temperate growth.

Version for bilinear maps. -/
@[fun_prop]
/--
theorem `_root_.ContinuousLinearMap.bilinear_hasTemperateGrowth` / 定理 `_root_.ContinuousLinearMap.bilinear_hasTemperateGrowth`

English:
theorem _root_.ContinuousLinearMap.bilinear_hasTemperateGrowth
  statement: [NormedSpace 𝕜 E]
  proof: by
  rw [Function.hasTemperateGrowth_iff_isBigO]
  constructor
  · apply (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1)
  intro n
  rcases hf.isBigO_uniform n with ⟨k1, h1⟩
  rcases hg.isBigO_uniform n with ⟨k2, h2⟩
  use k1 + k2
  have estimate (x : D) : ‖ite

中文:
定理 _root_.连续线性映射.bilinear_hasTemperateGrowth
  结论: [赋范空间 𝕜 E]
  证明: by
  rw [Function.hasTemperateGrowth_iff_isBigO]
  constructor
  · apply (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1)
  intro n
  rcases hf.isBigO_uniform n with ⟨k1, h1⟩
  rcases hg.isBigO_uniform n with ⟨k2, h2⟩
  use k1 + k2
  have estimate (x : D) : ‖ite

Depends on / 依赖: B.bilinearRestrictScalars, Finset, Finset.range, Function, Function.hasTemperateGrowth_iff_isBigO, bilinearRestrictScalars, contDiff, estimate, hasTemperateGrowth_iff_isBigO, hf.isBigO_uniform, hg.isBigO_uniform, isBigO_uniform, isBoundedBilinearMap, isBoundedBilinearMap.contDiff.comp, iteratedFDeriv, n.choose, norm_iteratedFDe, prodMk
-/
theorem _root_.ContinuousLinearMap.bilinear_hasTemperateGrowth [NormedSpace 𝕜 E]
    (B : E ->L[𝕜] F ->L[𝕜] G) {f : D -> E} {g : D -> F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (fun x => B (f x) (g x)).HasTemperateGrowth := by
  rw [Function.hasTemperateGrowth_iff_isBigO]
  constructor
  · apply (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1)
  intro n
  rcases hf.isBigO_uniform n with ⟨k1, h1⟩
  rcases hg.isBigO_uniform n with ⟨k2, h2⟩
  use k1 + k2
  have estimate (x : D) : ‖iteratedFDeriv Real n (fun x => B (f x) (g x)) x‖ <=
      ‖B‖ * ∑ i in Finset.range (n + 1), (n.choose i) *
        ‖iteratedFDeriv Real i f x‖ * ‖iteratedFDeriv Real (n - i) g x‖ :=
    (B.bilinearRestrictScalars Real).norm_iteratedFDeriv_le_of_bilinear hf.1 hg.1 x (mod_cast le_top)
  refine (IsBigO.of_norm_le estimate).trans (.const_mul_left (.fun_sum fun i hi => ?_) _)
  simp_rw [mul_assoc, pow_add]
  refine .const_mul_left (.mul (h1 i ?_).norm_left (h2 (n - i) ?_).norm_left) _ <;>
  grind

/--
lemma `HasTemperateGrowth.id` / 引理 `HasTemperateGrowth.id`

English:
lemma HasTemperateGrowth.id
  statement: Function.HasTemperateGrowth (id : E -> E)
  proof: by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1)
  · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id Real E)
    exact fderiv_fun_id
  · apply differentiable_id
  · simp

@[fun_prop]

中文:
引理 有TemperateGrowth.id
  结论: 函数.有TemperateGrowth (id : E -> E)
  证明: by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1)
  · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id Real E)
    exact fderiv_fun_id
  · apply differentiable_id
  · simp

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, Function, Function.HasTemperateGrowth.const, Function.HasTemperateGrowth.of_fderiv, HasTemperateGrowth, convert, differentiable_id, fderiv_fun_id, of_fderiv
-/
lemma HasTemperateGrowth.id : Function.HasTemperateGrowth (id : E -> E) := by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1)
  · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id Real E)
    exact fderiv_fun_id
  · apply differentiable_id
  · simp

@[fun_prop]
/--
lemma `HasTemperateGrowth.id'` / 引理 `HasTemperateGrowth.id'`

English:
lemma HasTemperateGrowth.id'
  statement: Function.HasTemperateGrowth (fun (x : E) => x)
  proof: Function.HasTemperateGrowth.id

中文:
引理 有TemperateGrowth.id'
  结论: 函数.有TemperateGrowth (fun (x : E) => x)
  证明: Function.HasTemperateGrowth.id

Depends on / 依赖: Function, Function.HasTemperateGrowth.id, HasTemperateGrowth
-/
lemma HasTemperateGrowth.id' : Function.HasTemperateGrowth (fun (x : E) => x) :=
  Function.HasTemperateGrowth.id

/-- The product of two functions of temperate growth is again of temperate growth.

Version for scalar multiplication. -/
@[to_fun (attr := fun_prop)]
/--
theorem `HasTemperateGrowth.smul` / 定理 `HasTemperateGrowth.smul`

English:
theorem HasTemperateGrowth.smul
  statement: {f : E -> 𝕜} {g : E -> F} (hf : f.HasTemperateGrowth)
  proof: (ContinuousLinearMap.lsmul Real 𝕜).bilinear_hasTemperateGrowth hf hg

中文:
定理 有TemperateGrowth.smul
  结论: {f : E -> 𝕜} {g : E -> F} (hf : f.有TemperateGrowth)
  证明: (ContinuousLinearMap.lsmul Real 𝕜).bilinear_hasTemperateGrowth hf hg

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, bilinear_hasTemperateGrowth
-/
theorem HasTemperateGrowth.smul {f : E -> 𝕜} {g : E -> F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f • g).HasTemperateGrowth :=
  (ContinuousLinearMap.lsmul Real 𝕜).bilinear_hasTemperateGrowth hf hg

variable [NormedRing R] [NormedAlgebra Real R]

/-- The product of two functions of temperate growth is again of temperate growth. -/
@[to_fun (attr := fun_prop)]
/--
theorem `HasTemperateGrowth.mul` / 定理 `HasTemperateGrowth.mul`

English:
theorem HasTemperateGrowth.mul
  statement: {f g : E -> R} (hf : f.HasTemperateGrowth)
  proof: (ContinuousLinearMap.mul Real R).bilinear_hasTemperateGrowth hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 有TemperateGrowth.mul
  结论: {f g : E -> R} (hf : f.有TemperateGrowth)
  证明: (ContinuousLinearMap.mul Real R).bilinear_hasTemperateGrowth hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, bilinear_hasTemperateGrowth
-/
theorem HasTemperateGrowth.mul {f g : E -> R} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f * g).HasTemperateGrowth :=
  (ContinuousLinearMap.mul Real R).bilinear_hasTemperateGrowth hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `HasTemperateGrowth.pow` / 定理 `HasTemperateGrowth.pow`

English:
theorem HasTemperateGrowth.pow
  given: {f : E -> R} (hf : f.HasTemperateGrowth) (k : Nat)
  proof: by
  induction k with
  | zero => simpa only [pow_zero] using! HasTemperateGrowth.const 1
  | succ k IH => rw [pow_succ]; fun_prop

中文:
定理 有TemperateGrowth.pow
  条件: {f : E -> R} (hf : f.有TemperateGrowth) (k : 自然数)
  证明: by
  induction k with
  | zero => simpa only [pow_zero] using! HasTemperateGrowth.const 1
  | succ k IH => rw [pow_succ]; fun_prop

Depends on / 依赖: HasTemperateGrowth, HasTemperateGrowth.const, fun_prop, pow_succ, pow_zero
-/
theorem HasTemperateGrowth.pow {f : E -> R} (hf : f.HasTemperateGrowth) (k : Nat) :
    (f ^ k).HasTemperateGrowth := by
  induction k with
  | zero => simpa only [pow_zero] using! HasTemperateGrowth.const 1
  | succ k IH => rw [pow_succ]; fun_prop

end Multiplication

@[fun_prop]
/--
lemma `_root_.ContinuousLinearMap.hasTemperateGrowth` / 引理 `_root_.ContinuousLinearMap.hasTemperateGrowth`

English:
lemma _root_.ContinuousLinearMap.hasTemperateGrowth
  given: (f : E ->L[Real] F)
  proof: by
  apply Function.HasTemperateGrowth.of_fderiv ?_ f.differentiable (k := 1) (C := ‖f‖) (fun x => ?_)
  · have : fderiv Real f = fun _ => f := by ext1 v; simp only [ContinuousLinearMap.fderiv]
    simp [this]
  · exact (f.le_opNorm x).trans (by simp [mul_add])

@[fun_prop]

中文:
引理 _root_.连续线性映射.hasTemperateGrowth
  条件: (f : E ->L[实数] F)
  证明: by
  apply Function.HasTemperateGrowth.of_fderiv ?_ f.differentiable (k := 1) (C := ‖f‖) (fun x => ?_)
  · have : fderiv Real f = fun _ => f := by ext1 v; simp only [ContinuousLinearMap.fderiv]
    simp [this]
  · exact (f.le_opNorm x).trans (by simp [mul_add])

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fderiv, Function, Function.HasTemperateGrowth.of_fderiv, HasTemperateGrowth, differentiable, f.differentiable, f.le_opNorm, fderiv, le_opNorm, mul_add, of_fderiv
-/
lemma _root_.ContinuousLinearMap.hasTemperateGrowth (f : E ->L[Real] F) :
    Function.HasTemperateGrowth f := by
  apply Function.HasTemperateGrowth.of_fderiv ?_ f.differentiable (k := 1) (C := ‖f‖) (fun x => ?_)
  · have : fderiv Real f = fun _ => f := by ext1 v; simp only [ContinuousLinearMap.fderiv]
    simp [this]
  · exact (f.le_opNorm x).trans (by simp [mul_add])

@[fun_prop]
/--
lemma `_root_.ContinuousLinearEquiv.hasTemperateGrowth` / 引理 `_root_.ContinuousLinearEquiv.hasTemperateGrowth`

English:
lemma _root_.ContinuousLinearEquiv.hasTemperateGrowth
  given: (f : E ≃L[Real] F)
  proof: f.toContinuousLinearMap.hasTemperateGrowth

@[fun_prop]

中文:
引理 _root_.连续线性等价.hasTemperateGrowth
  条件: (f : E ≃L[实数] F)
  证明: f.toContinuousLinearMap.hasTemperateGrowth

@[fun_prop]

Depends on / 依赖: f.toContinuousLinearMap.hasTemperateGrowth, hasTemperateGrowth, toContinuousLinearMap
-/
lemma _root_.ContinuousLinearEquiv.hasTemperateGrowth (f : E ≃L[Real] F) :
    Function.HasTemperateGrowth f :=
  f.toContinuousLinearMap.hasTemperateGrowth

@[fun_prop]
/--
theorem `Complex.hasTemperateGrowth_ofReal` / 定理 `Complex.hasTemperateGrowth_ofReal`

English:
theorem Complex.hasTemperateGrowth_ofReal
  statement: Complex.ofReal.HasTemperateGrowth
  proof: (Complex.ofRealCLM).hasTemperateGrowth

中文:
定理 复形.hasTemperateGrowth_of实数
  结论: 复形.of实数.有TemperateGrowth
  证明: (Complex.ofRealCLM).hasTemperateGrowth

Depends on / 依赖: Complex.ofRealCLM, hasTemperateGrowth, ofRealCLM
-/
theorem Complex.hasTemperateGrowth_ofReal : Complex.ofReal.HasTemperateGrowth :=
  (Complex.ofRealCLM).hasTemperateGrowth

variable (𝕜) in
@[fun_prop]
/--
theorem `RCLike.hasTemperateGrowth_ofReal` / 定理 `RCLike.hasTemperateGrowth_ofReal`

English:
theorem RCLike.hasTemperateGrowth_ofReal
  given: [RCLike 𝕜]
  statement: (RCLike.ofReal (K := 𝕜)).HasTemperateGrowth
  proof: (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth

中文:
定理 RCLike.hasTemperateGrowth_of实数
  条件: [RCLike 𝕜]
  结论: (RCLike.of实数 (K := 𝕜)).有TemperateGrowth
  证明: (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth

Depends on / 依赖: HasTemperateGrowth
-/
theorem RCLike.hasTemperateGrowth_ofReal [RCLike 𝕜] : (RCLike.ofReal (K := 𝕜)).HasTemperateGrowth :=
  (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth

variable [NormedAddCommGroup H] [InnerProductSpace Real H]

@[fun_prop]
/--
theorem `hasTemperateGrowth_inner_left` / 定理 `hasTemperateGrowth_inner_left`

English:
theorem hasTemperateGrowth_inner_left
  given: (c : H)
  statement: (inner Real · c).HasTemperateGrowth
  proof: ((innerSL Real).flip c).hasTemperateGrowth

@[fun_prop]

中文:
定理 hasTemperateGrowth_inner_left
  条件: (c : H)
  结论: (inner 实数 · c).有TemperateGrowth
  证明: ((innerSL Real).flip c).hasTemperateGrowth

@[fun_prop]

Depends on / 依赖: hasTemperateGrowth, innerSL
-/
theorem hasTemperateGrowth_inner_left (c : H) : (inner Real · c).HasTemperateGrowth :=
  ((innerSL Real).flip c).hasTemperateGrowth

@[fun_prop]
/--
theorem `hasTemperateGrowth_inner_right` / 定理 `hasTemperateGrowth_inner_right`

English:
theorem hasTemperateGrowth_inner_right
  given: (c : H)
  statement: (inner Real c ·).HasTemperateGrowth
  proof: (innerSL Real c).hasTemperateGrowth

中文:
定理 hasTemperateGrowth_inner_right
  条件: (c : H)
  结论: (inner 实数 c ·).有TemperateGrowth
  证明: (innerSL Real c).hasTemperateGrowth

Depends on / 依赖: hasTemperateGrowth, innerSL
-/
theorem hasTemperateGrowth_inner_right (c : H) : (inner Real c ·).HasTemperateGrowth :=
  (innerSL Real c).hasTemperateGrowth

variable (H) in
@[fun_prop]
/--
theorem `hasTemperateGrowth_norm_sq` / 定理 `hasTemperateGrowth_norm_sq`

English:
theorem hasTemperateGrowth_norm_sq
  statement: (fun (x : H) => ‖x‖ ^ 2).HasTemperateGrowth
  proof: by
  apply _root_.Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · rw [fderiv_norm_sq]
    convert! (2 • innerSL Real).hasTemperateGrowth
  · exact .norm_sq Real differentiable_id
  · intro x
    rw [norm_pow]; rw [norm_norm]; rw [one_mul]; rw [add_pow_two]
    exact le_add_of_nonneg_left

中文:
定理 hasTemperateGrowth_norm_sq
  结论: (fun (x : H) => ‖x‖ ^ 2).有TemperateGrowth
  证明: by
  apply _root_.Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · rw [fderiv_norm_sq]
    convert! (2 • innerSL Real).hasTemperateGrowth
  · exact .norm_sq Real differentiable_id
  · intro x
    rw [norm_pow]; rw [norm_norm]; rw [one_mul]; rw [add_pow_two]
    exact le_add_of_nonneg_left

Depends on / 依赖: Function, HasTemperateGrowth, _root_, _root_.Function.HasTemperateGrowth.of_fderiv, add_pow_two, convert, differentiable_id, fderiv_norm_sq, hasTemperateGrowth, innerSL, le_add_of_nonneg_left, norm_norm, norm_pow, norm_sq, of_fderiv, one_mul
-/
theorem hasTemperateGrowth_norm_sq : (fun (x : H) => ‖x‖ ^ 2).HasTemperateGrowth := by
  apply _root_.Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · rw [fderiv_norm_sq]
    convert! (2 • innerSL Real).hasTemperateGrowth
  · exact .norm_sq Real differentiable_id
  · intro x
    rw [norm_pow]; rw [norm_norm]; rw [one_mul]; rw [add_pow_two]
    exact le_add_of_nonneg_left (by positivity)

variable (H) in
/-- The Bessel potential `x ↦ (1 + ‖x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
/--
theorem `hasTemperateGrowth_one_add_norm_sq_rpow` / 定理 `hasTemperateGrowth_one_add_norm_sq_rpow`

English:
theorem hasTemperateGrowth_one_add_norm_sq_rpow
  given: (r : Real)
  proof: by
  /- We prove this using that the composition of temperate functions is temperate.
  Since `x ^ r` is not smooth at the origin, we have to use `HasTemperateGrowth.comp'`, with any
  open set `t` that is contains the complement of the unit ball and does not contain the origin. -/
  set t := {y : R

中文:
定理 hasTemperateGrowth_one_add_norm_sq_rpow
  条件: (r : 实数)
  证明: by
  /- We prove this using that the composition of temperate functions is temperate.
  Since `x ^ r` is not smooth at the origin, we have to use `HasTemperateGrowth.comp'`, with any
  open set `t` that is contains the complement of the unit ball and does not contain the origin. -/
  set t := {y : R
-/
theorem hasTemperateGrowth_one_add_norm_sq_rpow (r : Real) :
    (fun (x : H) => (1 + ‖x‖ ^ 2) ^ r).HasTemperateGrowth := by
  /- We prove this using that the composition of temperate functions is temperate.
  Since `x ^ r` is not smooth at the origin, we have to use `HasTemperateGrowth.comp'`, with any
  open set `t` that is contains the complement of the unit ball and does not contain the origin. -/
  set t := {y : Real | 1 / 2 < y}
  have ht : Set.range (fun (x : H) => (1 + ‖x‖ ^ 2)) subseteq t := by
    rintro - ⟨y, rfl⟩
    simp only [Set.mem_ofPred_eq, t]
    exact lt_add_of_lt_add_left (c := 0) (by norm_num) (by positivity)
  have hdiff : ContDiffOn Real ∞ (fun x => x ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx => (lt_trans (by norm_num) hx).ne'
  have hunique : UniqueDiffOn Real t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  apply HasTemperateGrowth.comp' ht hunique hdiff _ (by fun_prop)
  -- The remaining part of the proof is proving that `x ↦ x ^ r` has temperate growth on `t`.
  -- This could be generalized to `t := {y : ℝ | ε < y}` for any `0 < ε < 1` if necessary.
  intro N
  /- Since `x ^ r` for negative `r` blows up near the origin (and we can't take
  `t := {y : ℝ | 1 / 2 < y}`), we have to choose `k` later than `N - r` times some factor depending
  on `t`. -/
  obtain ⟨k, hk⟩ := exists_nat_ge (max r <| (N - r) * Real.log 2 / (Real.log (3 / 2)))
  have hk₁ : r <= k := le_sup_left.trans hk
  have hk₂ : Real.log 2 * (N - r) <= (Real.log (3 / 2)) * k := by
    have := le_sup_right.trans hk
    field_simp at this
    grind
  use k, ∑ k in Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer Real k)‖, by positivity
  intro n hn x hx
  have : ContDiffAt Real n (fun x => x ^ r) x :=
Real.contDiffAt_rpow_const Or.inl (lt_trans (by norm_num) hx).ne'
  -- We calculate the derivative of `x ^ r`.
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]; rw [iteratedDerivWithin_eq_iteratedDeriv hunique this hx]; rw [iteratedDeriv_eq_iterate]; rw [Real.iter_deriv_rpow_const]; rw [norm_mul]
  gcongr 1
  · have : n in Finset.range (N + 1) := by grind
    apply Finset.single_le_sum (fun _ _ => by positivity) this
  -- It remains to show that `‖x ^ (r - n)‖ ≤ (1 + ‖x‖) ^ k`:
  have hx' : 1 / 2 < x := by simpa [t] using hx
  have hx'' : 0 < x := lt_of_lt_of_le (by norm_num) hx'.le
  simp only [Real.norm_eq_abs]
  apply (Real.abs_rpow_le_abs_rpow _ _).trans
  -- We consider the two cases `n ≤ r` and `r < n`.
  by_cases! h : 0 <= r - n
  · have : r - n <= k := by simpa using hk₁.trans (by simp)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
      (Real.rpow_le_rpow_of_exponent_le (by simp) this)
  have h : 0 < n - r := by grind
  calc
    /- In the case `0 < n - r`, we need the factor `Real.log 2 / (Real.log (3 / 2))` to control
    the growth near `‖x‖ = 1/2`. -/
    _ = x ^ (-(n - r)) := by
      rw [neg_sub]
      congr
      simpa using hx''.le
    _ <= (2 : Real) ^ (n - r) := by
      simp only [one_div, Set.mem_ofPred_eq, t] at hx
      rw [Real.rpow_neg_eq_inv_rpow]
      gcongr
      exact ((inv_lt_comm₀ hx'' (by norm_num)).mpr hx).le
    _ = Real.exp (Real.log 2 * (n - r)) := by
      rw [Real.rpow_def_of_pos]
      norm_num
    _ <= Real.exp (Real.log (3 / 2) * k) := by
      gcongr 1
      apply le_trans _ hk₂
      gcongr
    _ <= (3 / 2) ^ k := by
      rw [← Real.rpow_natCast]; rw [Real.rpow_def_of_pos]
      norm_num
    _ <= _ := by
      gcongr
      grind

end Function

namespace MeasureTheory.Measure

variable [NormedAddCommGroup E] [MeasurableSpace E]

open Module
open scoped ENNReal

/--
Definition of `HasTemperateGrowth` / `HasTemperateGrowth` 的定义

English:
class HasTemperateGrowth
  parameters: (μ : Measure E)
  axioms and operations (1):
    - exists_integrable : exists (n : Nat), Integrable (fun x => (1 + ‖x‖) ^ (- (n : Real))) μ

中文:
类 有TemperateGrowth
  参数: (μ : 测度 E)
  公理与运算 (1 个):
    - exists_integrable : 存在 (n : 自然数), 可积 (fun x => (1 + ‖x‖) ^ (- (n : 实数))) μ
-/
class HasTemperateGrowth (μ : Measure E) : Prop where
  exists_integrable : exists (n : Nat), Integrable (fun x => (1 + ‖x‖) ^ (- (n : Real))) μ

open scoped Classical in
/--
Definition of `integrablePower` / `integrablePower` 的定义

English:
definition integrablePower
  signature: (μ : Measure E)
  body: if h : μ.HasTemperateGrowth then h.exists_integrable.choose else 0

中文:
定义 integrablePower
  签名: (μ : 测度 E)
  定义体: if h : μ.HasTemperateGrowth then h.exists_integrable.choose else 0

Depends on / 依赖: HasTemperateGrowth, exists_integrable, h.exists_integrable.choose
-/
def integrablePower (μ : Measure E) : Nat :=
  if h : μ.HasTemperateGrowth then h.exists_integrable.choose else 0

/--
lemma `integrable_pow_neg_integrablePower` / 引理 `integrable_pow_neg_integrablePower`

English:
lemma integrable_pow_neg_integrablePower
  proof: by
  simpa [Measure.integrablePower, h] using h.exists_integrable.choose_spec

中文:
引理 integrable_pow_neg_integrablePower
  证明: by
  simpa [Measure.integrablePower, h] using h.exists_integrable.choose_spec

Depends on / 依赖: Measure, Measure.integrablePower, choose_spec, exists_integrable, h.exists_integrable.choose_spec, integrablePower
-/
lemma integrable_pow_neg_integrablePower
    (μ : Measure E) [h : μ.HasTemperateGrowth] :
    Integrable (fun x => (1 + ‖x‖) ^ (- (μ.integrablePower : Real))) μ := by
  simpa [Measure.integrablePower, h] using h.exists_integrable.choose_spec

/--
Instance `_root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth` / 实例 `_root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth`

English:
instance _root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth
  signature: {μ : Measure E}
  body: ⟨⟨0, by simp⟩⟩

中文:
实例 _root_.测度论.是有限测度.instHasTemperateGrowth
  签名: {μ : 测度 E}
  定义体: ⟨⟨0, by simp⟩⟩
-/
instance _root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth {μ : Measure E}
    [h : IsFiniteMeasure μ] : μ.HasTemperateGrowth := ⟨⟨0, by simp⟩⟩

variable [NormedSpace Real E] [FiniteDimensional Real E] [BorelSpace E] in
/--
Instance `IsAddHaarMeasure.instHasTemperateGrowth` / 实例 `IsAddHaarMeasure.instHasTemperateGrowth`

English:
instance IsAddHaarMeasure.instHasTemperateGrowth
  signature: {μ : Measure E}
  body: ⟨⟨finrank Real E + 1, by apply integrable_one_add_norm; norm_num⟩⟩

中文:
实例 是加法Haar测度.instHasTemperateGrowth
  签名: {μ : 测度 E}
  定义体: ⟨⟨finrank Real E + 1, by apply integrable_one_add_norm; norm_num⟩⟩

Depends on / 依赖: finrank, integrable_one_add_norm
-/
instance IsAddHaarMeasure.instHasTemperateGrowth {μ : Measure E}
    [h : μ.IsAddHaarMeasure] : μ.HasTemperateGrowth :=
  ⟨⟨finrank Real E + 1, by apply integrable_one_add_norm; norm_num⟩⟩

/--
lemma `_root_.pow_mul_le_of_le_of_pow_mul_le` / 引理 `_root_.pow_mul_le_of_le_of_pow_mul_le`

English:
lemma _root_.pow_mul_le_of_le_of_pow_mul_le
  statement: {C₁ C₂ : Real} {k l : Nat} {x f : Real} (hx : 0 <= x)
  proof: by
  have : 0 <= C₂ := le_trans (by positivity) h₂
  have : 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : Real)) = ((1 + x) / 2) ^ (-(l : Real)) * (C₁ + C₂) := by
    rw [Real.div_rpow (by positivity) zero_le_two]
    simp [div_eq_inv_mul, ← Real.rpow_neg_one, ← Real.rpow_mul]
    ring
  rw [this]
  rcases 

中文:
引理 _root_.pow_mul_le_of_le_of_pow_mul_le
  结论: {C₁ C₂ : 实数} {k l : 自然数} {x f : 实数} (hx : 0 <= x)
  证明: by
  have : 0 <= C₂ := le_trans (by positivity) h₂
  have : 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : Real)) = ((1 + x) / 2) ^ (-(l : Real)) * (C₁ + C₂) := by
    rw [Real.div_rpow (by positivity) zero_le_two]
    simp [div_eq_inv_mul, ← Real.rpow_neg_one, ← Real.rpow_mul]
    ring
  rw [this]
  rcases 

Depends on / 依赖: Real.div_rpow, Real.one_le_rpow_of_pos_of_le_one_of_nonpos, Real.rpow_mul, Real.rpow_neg_one, div_eq_inv_mul, div_rpow, le_total, le_trans, one_le_rpow_of_pos_of_le_one_of_nonpos, rpow_mul, rpow_neg_one, zero_le_two
-/
lemma _root_.pow_mul_le_of_le_of_pow_mul_le {C₁ C₂ : Real} {k l : Nat} {x f : Real} (hx : 0 <= x)
    (hf : 0 <= f) (h₁ : f <= C₁) (h₂ : x ^ (k + l) * f <= C₂) :
    x ^ k * f <= 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : Real)) := by
  have : 0 <= C₂ := le_trans (by positivity) h₂
  have : 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : Real)) = ((1 + x) / 2) ^ (-(l : Real)) * (C₁ + C₂) := by
    rw [Real.div_rpow (by positivity) zero_le_two]
    simp [div_eq_inv_mul, ← Real.rpow_neg_one, ← Real.rpow_mul]
    ring
  rw [this]
  rcases le_total x 1 with h'x | h'x
  · gcongr
    · apply (pow_le_one₀ hx h'x).trans
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      · positivity
      · linarith
      · simp
    · linarith
  · calc
    x ^ k * f = x ^ (-(l : Real)) * (x ^ (k + l) * f) := by
      rw [← Real.rpow_natCast]; rw [← Real.rpow_natCast]; rw [← mul_assoc]; rw [← Real.rpow_add (by positivity)]
      simp
    _ <= ((1 + x) / 2) ^ (-(l : Real)) * (C₁ + C₂) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
      · exact h₂.trans (by linarith)

variable [NormedAddCommGroup F]

variable [BorelSpace E] [SecondCountableTopology E] in
/--
lemma `_root_.integrable_of_le_of_pow_mul_le` / 引理 `_root_.integrable_of_le_of_pow_mul_le`

English:
lemma _root_.integrable_of_le_of_pow_mul_le
  statement: {μ : Measure E} [μ.HasTemperateGrowth] {f : E -> F}
  proof: by
  apply ((integrable_pow_neg_integrablePower μ).const_mul (2 ^ μ.integrablePower * (C₁ + C₂))).mono'
  · exact AEStronglyMeasurable.mul (aestronglyMeasurable_id.norm.pow _) h''f.norm
  · filter_upwards with v
    simp only [norm_mul, norm_pow, norm_norm]
    apply pow_mul_le_of_le_of_pow_mul_le (

中文:
引理 _root_.integrable_of_le_of_pow_mul_le
  结论: {μ : 测度 E} [μ.有TemperateGrowth] {f : E -> F}
  证明: by
  apply ((integrable_pow_neg_integrablePower μ).const_mul (2 ^ μ.integrablePower * (C₁ + C₂))).mono'
  · exact AEStronglyMeasurable.mul (aestronglyMeasurable_id.norm.pow _) h''f.norm
  · filter_upwards with v
    simp only [norm_mul, norm_pow, norm_norm]
    apply pow_mul_le_of_le_of_pow_mul_le (

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mul, aestronglyMeasurable_id, aestronglyMeasurable_id.norm.pow, const_mul, f.norm, filter_upwards, integrablePower, integrable_pow_neg_integrablePower, norm_mul, norm_nonneg, norm_norm, norm_pow, pow_mul_le_of_le_of_pow_mul_le
-/
lemma _root_.integrable_of_le_of_pow_mul_le {μ : Measure E} [μ.HasTemperateGrowth] {f : E -> F}
    {C₁ C₂ : Real} {k : Nat} (hf : forall x, ‖f x‖ <= C₁)
    (h'f : forall x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ <= C₂) (h''f : AEStronglyMeasurable f μ) :
    Integrable (fun x => ‖x‖ ^ k * ‖f x‖) μ := by
  apply ((integrable_pow_neg_integrablePower μ).const_mul (2 ^ μ.integrablePower * (C₁ + C₂))).mono'
  · exact AEStronglyMeasurable.mul (aestronglyMeasurable_id.norm.pow _) h''f.norm
  · filter_upwards with v
    simp only [norm_mul, norm_pow, norm_norm]
    apply pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)

/--
lemma `_root_.integral_pow_mul_le_of_le_of_pow_mul_le` / 引理 `_root_.integral_pow_mul_le_of_le_of_pow_mul_le`

English:
lemma _root_.integral_pow_mul_le_of_le_of_pow_mul_le
  proof: by
  rw [← integral_const_mul]; rw [← integral_mul_const]
  apply integral_mono_of_nonneg
  · filter_upwards with v using by positivity
  · exact ((integrable_pow_neg_integrablePower μ).const_mul _).mul_const _
  filter_upwards with v
  exact (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_non

中文:
引理 _root_.integral_pow_mul_le_of_le_of_pow_mul_le
  证明: by
  rw [← integral_const_mul]; rw [← integral_mul_const]
  apply integral_mono_of_nonneg
  · filter_upwards with v using by positivity
  · exact ((integrable_pow_neg_integrablePower μ).const_mul _).mul_const _
  filter_upwards with v
  exact (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_non

Depends on / 依赖: const_mul, filter_upwards, integrable_pow_neg_integrablePower, integral_const_mul, integral_mono_of_nonneg, integral_mul_const, le_of_eq, mul_const, norm_nonneg, pow_mul_le_of_le_of_pow_mul_le
-/
lemma _root_.integral_pow_mul_le_of_le_of_pow_mul_le
    {μ : Measure E} [μ.HasTemperateGrowth] {f : E -> F} {C₁ C₂ : Real} {k : Nat}
    (hf : forall x, ‖f x‖ <= C₁) (h'f : forall x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ <= C₂) :
    ∫ x, ‖x‖ ^ k * ‖f x‖ ∂μ <= 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : Real)) ∂μ) * (C₁ + C₂) := by
  rw [← integral_const_mul]; rw [← integral_mul_const]
  apply integral_mono_of_nonneg
  · filter_upwards with v using by positivity
  · exact ((integrable_pow_neg_integrablePower μ).const_mul _).mul_const _
  filter_upwards with v
  exact (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)).trans
    (le_of_eq (by ring))

/--
theorem `HasTemperateGrowth.exists_eLpNorm_lt_top` / 定理 `HasTemperateGrowth.exists_eLpNorm_lt_top`

English:
theorem HasTemperateGrowth.exists_eLpNorm_lt_top
  statement: (p : Real>=0∞)
  proof: by
  cases p with
  | top => exact ⟨0, eLpNormEssSup_lt_top_of_ae_bound (C := 1) (by simp)⟩
  | coe p =>
    cases eq_or_ne (p : Real>=0∞) 0 with
    | inl hp => exact ⟨0, by simp [hp]⟩
    | inr hp =>
      have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
    

中文:
定理 有TemperateGrowth.存在_eLpNorm_lt_top
  结论: (p : 实数>=0∞)
  证明: by
  cases p with
  | top => exact ⟨0, eLpNormEssSup_lt_top_of_ae_bound (C := 1) (by simp)⟩
  | coe p =>
    cases eq_or_ne (p : Real>=0∞) 0 with
    | inl hp => exact ⟨0, by simp [hp]⟩
    | inr hp =>
      have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
    

Depends on / 依赖: Nat.le_ceil, eLpNormEssSup_lt_top_of_ae_bound, eq_or_ne, exists_integrable, h_one_add, hp_pos, le_ceil, lt_add_of_pos_of_le, norm_nonneg, zero_lt_iff, zero_lt_one
-/
theorem HasTemperateGrowth.exists_eLpNorm_lt_top (p : Real>=0∞)
    {μ : Measure E} (hμ : μ.HasTemperateGrowth) :
    exists k : Nat, eLpNorm (fun x => (1 + ‖x‖) ^ (-k : Real)) p μ < ⊤ := by
  cases p with
  | top => exact ⟨0, eLpNormEssSup_lt_top_of_ae_bound (C := 1) (by simp)⟩
  | coe p =>
    cases eq_or_ne (p : Real>=0∞) 0 with
    | inl hp => exact ⟨0, by simp [hp]⟩
    | inr hp =>
      have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
      have hp_pos : 0 < (p : Real) := by simpa [zero_lt_iff] using hp
      rcases hμ.exists_integrable with ⟨l, hl⟩
      let k := ⌈(l / p : Real)⌉₊
      have hlk : l <= k * (p : Real) := by simpa [div_le_iff₀ hp_pos] using Nat.le_ceil (l / p : Real)
      use k
      suffices HasFiniteIntegral (fun x => ((1 + ‖x‖) ^ (-(k * p) : Real))) μ by
        rw [hasFiniteIntegral_iff_enorm] at this
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp ENNReal.coe_ne_top]
        simp only [ENNReal.coe_toReal]
        refine Eq.subst (motive := (∫⁻ x, · x ∂μ < ⊤)) (funext fun x => ?_) this
        rw [← neg_mul]; rw [Real.rpow_mul (h_one_add x).le]
        exact Real.enorm_rpow_of_nonneg (by positivity) NNReal.zero_le_coe
      refine hl.hasFiniteIntegral.mono' (ae_of_all μ fun x => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (h_one_add x).le _)]
      gcongr
      simp

end MeasureTheory.Measure
