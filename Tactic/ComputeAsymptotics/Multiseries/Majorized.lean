/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `Majorized` predicate

This file defines the `Majorized` predicate, along with a few basic lemmas.

## Main definitions

* `Majorized f b exp` means that `f =o[atTop] (b ^ exp')` for any `exp' > exp`.
  Intuitively, this means that the right order of `f` in terms of `b` is at most `b ^ exp`.
  This predicate is used in the definition of the `MultiseriesExpansion.Approximates` predicate.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Topology Filter Asymptotics

/--
Definition of `Majorized` / `Majorized` 的定义

English:
definition Majorized
  signature: (f b : Real -> Real) (exp : Real)
  body: forall exp' > exp, f =o[atTop] (b ^ exp')

中文:
定义 Majorized
  签名: (f b : 实数 -> 实数) (exp : 实数)
  定义体: forall exp' > exp, f =o[atTop] (b ^ exp')
-/
def Majorized (f b : Real -> Real) (exp : Real) : Prop :=
  forall exp' > exp, f =o[atTop] (b ^ exp')

namespace Majorized

variable {f g b : Real -> Real} {exp : Real}

/--
theorem `of_eventuallyEq` / 定理 `of_eventuallyEq`

English:
theorem of_eventuallyEq
  given: (h_eq : g =ᶠ[atTop] f) (h : Majorized f b exp)
  proof: by
  simp only [Majorized] at *
  intro exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq (h exp' h_exp)

中文:
定理 of_eventuallyEq
  条件: (h_eq : g =ᶠ[atTop] f) (h : Majorized f b exp)
  证明: by
  simp only [Majorized] at *
  intro exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq (h exp' h_exp)

Depends on / 依赖: EventuallyEq, EventuallyEq.trans_isLittleO, Majorized, h_eq, h_exp, trans_isLittleO
-/
theorem of_eventuallyEq (h_eq : g =ᶠ[atTop] f) (h : Majorized f b exp) :
    Majorized g b exp := by
  simp only [Majorized] at *
  intro exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq (h exp' h_exp)

/--
theorem `self` / 定理 `self`

English:
theorem self
  given: (h : Tendsto f atTop atTop)
  proof: by
  simp only [Majorized]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t => f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t => (f t) ^ (exp - exp') :=
      (h.eventually_gt_atTop 0).mono (fun _ h => by simp [← Real.rpow_sub h])
    apply Tendsto.congr' this.symm
    conv =>
  

中文:
定理 self
  条件: (h : 收敛 f atTop atTop)
  证明: by
  simp only [Majorized]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t => f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t => (f t) ^ (exp - exp') :=
      (h.eventually_gt_atTop 0).mono (fun _ h => by simp [← Real.rpow_sub h])
    apply Tendsto.congr' this.symm
    conv =>
  

Depends on / 依赖: Majorized, Real.rpow_sub, Tendsto, Tendsto.congr, Tendsto.eventually_gt_atTop, absurd, eventually_gt_atTop, h.eventually_gt_atTop, h_exp, isLittleO_iff_tendsto, rpow_sub, tendsto_rpow_neg_atTop, this.symm
-/
theorem self (h : Tendsto f atTop atTop) :
    Majorized (f ^ exp) f exp := by
  simp only [Majorized]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t => f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t => (f t) ^ (exp - exp') :=
      (h.eventually_gt_atTop 0).mono (fun _ h => by simp [← Real.rpow_sub h])
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun t => f t ^ (exp - exp')) = ((fun t => t ^ (-(exp' - exp))) ∘ f) by ext; simp]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h
  · apply (Tendsto.eventually_gt_atTop h 0).mono
    intro t h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: {exp1 exp2 : Real} (h_lt : exp1 <= exp2) (h : Majorized f b exp1)
  proof: by
  simp only [Majorized] at *
  exact fun exp' h_exp => h _ (by linarith)

中文:
定理 of_le
  条件: {exp1 exp2 : 实数} (h_lt : exp1 <= exp2) (h : Majorized f b exp1)
  证明: by
  simp only [Majorized] at *
  exact fun exp' h_exp => h _ (by linarith)

Depends on / 依赖: Majorized, h_exp
-/
theorem of_le {exp1 exp2 : Real} (h_lt : exp1 <= exp2) (h : Majorized f b exp1) :
    Majorized f b exp2 := by
  simp only [Majorized] at *
  exact fun exp' h_exp => h _ (by linarith)

/--
theorem `tendsto_zero_of_neg` / 定理 `tendsto_zero_of_neg`

English:
theorem tendsto_zero_of_neg
  given: (h_lt : exp < 0) (h : Majorized f b exp)
  proof: by
  simpa [Pi.pow_def, Majorized] using h 0 (by linarith)

中文:
定理 tendsto_zero_of_neg
  条件: (h_lt : exp < 0) (h : Majorized f b exp)
  证明: by
  simpa [Pi.pow_def, Majorized] using h 0 (by linarith)

Depends on / 依赖: Majorized, Pi.pow_def, pow_def
-/
theorem tendsto_zero_of_neg (h_lt : exp < 0) (h : Majorized f b exp) :
    Tendsto f atTop (𝓝 0) := by
  simpa [Pi.pow_def, Majorized] using h 0 (by linarith)

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (h_tendsto : Tendsto b atTop atTop) {c : Real}
  proof: by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply tendsto_norm_atTop_atTop.comp
  exact (tendsto_rpow_atTop h_exp).comp h_tendsto

中文:
定理 const
  条件: (h_tendsto : 收敛 b atTop atTop) {c : 实数}
  证明: by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply tendsto_norm_atTop_atTop.comp
  exact (tendsto_rpow_atTop h_exp).comp h_tendsto

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_const_left.mpr, h_exp, h_tendsto, isLittleO_const_left, tendsto_norm_atTop_atTop, tendsto_norm_atTop_atTop.comp, tendsto_rpow_atTop
-/
theorem const (h_tendsto : Tendsto b atTop atTop) {c : Real} :
    Majorized (fun _ => c) b 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply tendsto_norm_atTop_atTop.comp
  exact (tendsto_rpow_atTop h_exp).comp h_tendsto

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: Majorized 0 b exp
  proof: fun _ _ => Asymptotics.isLittleO_zero _ _

中文:
定理 zero
  结论: Majorized 0 b exp
  证明: fun _ _ => Asymptotics.isLittleO_zero _ _

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_zero, isLittleO_zero
-/
theorem zero : Majorized 0 b exp :=
  fun _ _ => Asymptotics.isLittleO_zero _ _

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (h : Majorized f b exp) {c : Real}
  proof: fun exp h_exp => (h exp h_exp).const_mul_left _

中文:
定理 smul
  条件: (h : Majorized f b exp) {c : 实数}
  证明: fun exp h_exp => (h exp h_exp).const_mul_left _

Depends on / 依赖: const_mul_left, h_exp
-/
theorem smul (h : Majorized f b exp) {c : Real} :
    Majorized (c • f) b exp :=
  fun exp h_exp => (h exp h_exp).const_mul_left _

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: {f_exp g_exp : Real} (hf : Majorized f b f_exp)
  proof: by
  simp only [Majorized] at *
  intro exp' h_exp'
  exact (hf _ (by order)).add (hg _ (by order))

中文:
定理 add
  结论: {f_exp g_exp : 实数} (hf : Majorized f b f_exp)
  证明: by
  simp only [Majorized] at *
  intro exp' h_exp'
  exact (hf _ (by order)).add (hg _ (by order))

Depends on / 依赖: Majorized, h_exp
-/
theorem add {f_exp g_exp : Real} (hf : Majorized f b f_exp)
    (hg : Majorized g b g_exp) (hf_exp : f_exp <= exp) (hg_exp : g_exp <= exp) :
    Majorized (f + g) b exp := by
  simp only [Majorized] at *
  intro exp' h_exp'
  exact (hf _ (by order)).add (hg _ (by order))

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: {f_exp g_exp : Real} (hf : Majorized f b f_exp)
  proof: by
  simp only [Majorized] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply (hf.mul hg).trans_eventuallyEq (g₁ := fun t => b t ^ (f_exp + ε) * b t ^ (g_exp + ε))
  apply h_pos

中文:
定理 mul
  结论: {f_exp g_exp : 实数} (hf : Majorized f b f_exp)
  证明: by
  simp only [Majorized] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply (hf.mul hg).trans_eventuallyEq (g₁ := fun t => b t ^ (f_exp + ε) * b t ^ (g_exp + ε))
  apply h_pos

Depends on / 依赖: Majorized, Pi.pow_apply, Real.rpow_add, conv_rhs, f_exp, g_exp, h_exp, h_pos, h_pos.mono, hf.mul, pow_apply, ring_nf, rpow_add, specialize, trans_eventuallyEq
-/
theorem mul {f_exp g_exp : Real} (hf : Majorized f b f_exp)
    (hg : Majorized g b g_exp) (h_pos : forallᶠ t in atTop, 0 < b t) :
    Majorized (f * g) b (f_exp + g_exp) := by
  simp only [Majorized] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply (hf.mul hg).trans_eventuallyEq (g₁ := fun t => b t ^ (f_exp + ε) * b t ^ (g_exp + ε))
  apply h_pos.mono
  intro t hx
  simp only [Pi.pow_apply]
  conv_rhs => rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf, Real.rpow_add hx]

/--
theorem `mul_bounded` / 定理 `mul_bounded`

English:
theorem mul_bounded
  statement: {f g basis_hd : Real -> Real} {exp : Real} (hf : Majorized f basis_hd exp)
  proof: by
  intro exp h_exp
  convert! IsLittleO.mul_isBigO (hf _ h_exp) hg using 1
  simp
  rfl

中文:
定理 mul_bounded
  结论: {f g basis_hd : 实数 -> 实数} {exp : 实数} (hf : Majorized f basis_hd exp)
  证明: by
  intro exp h_exp
  convert! IsLittleO.mul_isBigO (hf _ h_exp) hg using 1
  simp
  rfl

Depends on / 依赖: IsLittleO, IsLittleO.mul_isBigO, convert, h_exp, mul_isBigO
-/
theorem mul_bounded {f g basis_hd : Real -> Real} {exp : Real} (hf : Majorized f basis_hd exp)
    (hg : g =O[atTop] (fun _ => (1 : Real))) :
    Majorized (f * g) basis_hd exp := by
  intro exp h_exp
  convert! IsLittleO.mul_isBigO (hf _ h_exp) hg using 1
  simp
  rfl

end Majorized

end Tactic.ComputeAsymptotics
