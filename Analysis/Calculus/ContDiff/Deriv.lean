/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Higher differentiability in one dimension

The general theory of higher derivatives in Mathlib is developed using the Fréchet derivative
`fderiv`; but for maps defined on the field, the one-dimensional derivative `deriv` is often easier
to use. In this file, we reformulate some higher smoothness results in terms of `deriv`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open scoped ContDiff

open Set

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {m n : Nat∞ω} {f : 𝕜 -> F} {s : Set 𝕜}

/--
theorem `contDiffOn_succ_iff_derivWithin` / 定理 `contDiffOn_succ_iff_derivWithin`

English:
theorem contDiffOn_succ_iff_derivWithin
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: by
  have : derivWithin f s =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f s := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]

中文:
定理 contDiffOn_succ_iff_derivWithin
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: by
  have : derivWithin f s =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f s := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.comp_contDiffOn_iff, ContinuousLinearMap, ContinuousLinearMap.toSpanSingletonCLE.symm, comp_contDiffOn_iff, contDiffOn_succ_iff_fderivWithin, derivWithin, fderivWithin, fderivWithin_derivWithin, toSpanSingletonCLE
-/
theorem contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (derivWithin f s) s := by
  have : derivWithin f s =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f s := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]

/--
theorem `contDiffOn_one_iff_derivWithin` / 定理 `contDiffOn_one_iff_derivWithin`

English:
theorem contDiffOn_one_iff_derivWithin
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl]; rw [contDiffOn_succ_iff_derivWithin hs]
  simp

中文:
定理 contDiffOn_one_iff_derivWithin
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl]; rw [contDiffOn_succ_iff_derivWithin hs]
  simp

Depends on / 依赖: contDiffOn_succ_iff_derivWithin
-/
theorem contDiffOn_one_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 1 f s ↔ DifferentiableOn 𝕜 f s ∧ ContinuousOn (derivWithin f s) s := by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl]; rw [contDiffOn_succ_iff_derivWithin hs]
  simp

/--
theorem `contDiffOn_infty_iff_derivWithin` / 定理 `contDiffOn_infty_iff_derivWithin`

English:
theorem contDiffOn_infty_iff_derivWithin
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [show ∞ = ∞ + 1 by rfl]; rw [contDiffOn_succ_iff_derivWithin hs]
  simp

中文:
定理 contDiffOn_infty_iff_derivWithin
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [show ∞ = ∞ + 1 by rfl]; rw [contDiffOn_succ_iff_derivWithin hs]
  simp

Depends on / 依赖: contDiffOn_succ_iff_derivWithin
-/
theorem contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (derivWithin f s) s := by
  rw [show ∞ = ∞ + 1 by rfl]; rw [contDiffOn_succ_iff_derivWithin hs]
  simp

/--
theorem `contDiffOn_succ_iff_deriv_of_isOpen` / 定理 `contDiffOn_succ_iff_deriv_of_isOpen`

English:
theorem contDiffOn_succ_iff_deriv_of_isOpen
  given: (hs : IsOpen s)
  proof: by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))

中文:
定理 contDiffOn_succ_iff_deriv_of_isOpen
  条件: (hs : 是开集 s)
  证明: by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))

Depends on / 依赖: Iff.rfl.and, contDiffOn_congr, contDiffOn_succ_iff_derivWithin, derivWithin_of_isOpen, hs.uniqueDiffOn, uniqueDiffOn
-/
theorem contDiffOn_succ_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧ ContDiffOn 𝕜 n (deriv f) s := by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))

/--
theorem `contDiffOn_infty_iff_deriv_of_isOpen` / 定理 `contDiffOn_infty_iff_deriv_of_isOpen`

English:
theorem contDiffOn_infty_iff_deriv_of_isOpen
  given: (hs : IsOpen s)
  proof: by
  rw [show ∞ = ∞ + 1 by rfl]; rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp

中文:
定理 contDiffOn_infty_iff_deriv_of_isOpen
  条件: (hs : 是开集 s)
  证明: by
  rw [show ∞ = ∞ + 1 by rfl]; rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp

Depends on / 依赖: contDiffOn_succ_iff_deriv_of_isOpen
-/
theorem contDiffOn_infty_iff_deriv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (deriv f) s := by
  rw [show ∞ = ∞ + 1 by rfl]; rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp

/--
theorem `ContDiffOn.derivWithin` / 定理 `ContDiffOn.derivWithin`

English:
theorem ContDiffOn.derivWithin
  statement: (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  proof: ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2

中文:
定理 ContDiffOn.derivWithin
  结论: (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  证明: ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2
-/
protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 <= n) : ContDiffOn 𝕜 m (derivWithin f s) s :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2

/--
theorem `ContDiffOn.deriv_of_isOpen` / 定理 `ContDiffOn.deriv_of_isOpen`

English:
theorem ContDiffOn.deriv_of_isOpen
  given: (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 <= n)
  proof: (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

中文:
定理 ContDiffOn.deriv_of_isOpen
  条件: (hf : ContDiffOn 𝕜 n f s) (hs : 是开集 s) (hmn : m + 1 <= n)
  证明: (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

Depends on / 依赖: derivWithin, derivWithin_of_isOpen, hf.derivWithin, hs.uniqueDiffOn, uniqueDiffOn
-/
theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 <= n) :
    ContDiffOn 𝕜 m (deriv f) s :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

/--
theorem `ContDiffOn.continuousOn_derivWithin` / 定理 `ContDiffOn.continuousOn_derivWithin`

English:
theorem ContDiffOn.continuousOn_derivWithin
  statement: (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

中文:
定理 ContDiffOn.continuousOn_derivWithin
  结论: (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

Depends on / 依赖: contDiffOn_succ_iff_derivWithin, continuousOn, h.of_le, of_le
-/
theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 <= n) : ContinuousOn (derivWithin f s) s := by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

/--
theorem `ContDiffOn.continuousOn_deriv_of_isOpen` / 定理 `ContDiffOn.continuousOn_deriv_of_isOpen`

English:
theorem ContDiffOn.continuousOn_deriv_of_isOpen
  statement: (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
  proof: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

@[fun_prop]

中文:
定理 ContDiffOn.continuousOn_deriv_of_isOpen
  结论: (h : ContDiffOn 𝕜 n f s) (hs : 是开集 s)
  证明: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

@[fun_prop]

Depends on / 依赖: contDiffOn_succ_iff_deriv_of_isOpen, continuousOn, h.of_le, of_le
-/
theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 <= n) : ContinuousOn (deriv f) s := by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

@[fun_prop]
/--
lemma `ContDiffWithinAt.derivWithin` / 引理 `ContDiffWithinAt.derivWithin`

English:
lemma ContDiffWithinAt.derivWithin
  statement: {x : 𝕜}
  proof: by
  exact ContDiffWithinAt.comp _ (by fun_prop) (g := fun f => f 1) (t := .univ)
    (H.fderivWithin_right hs hmn hx) (fun _ _ => trivial)

中文:
引理 ContDiffWithinAt.derivWithin
  结论: {x : 𝕜}
  证明: by
  exact ContDiffWithinAt.comp _ (by fun_prop) (g := fun f => f 1) (t := .univ)
    (H.fderivWithin_right hs hmn hx) (fun _ _ => trivial)
-/
protected lemma ContDiffWithinAt.derivWithin {x : 𝕜}
    (H : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 <= n) (hx : x in s) :
    ContDiffWithinAt 𝕜 m (derivWithin f s) s x := by
  exact ContDiffWithinAt.comp _ (by fun_prop) (g := fun f => f 1) (t := .univ)
    (H.fderivWithin_right hs hmn hx) (fun _ _ => trivial)

/--
theorem `contDiff_succ_iff_deriv` / 定理 `contDiff_succ_iff_deriv`

English:
theorem contDiff_succ_iff_deriv
  proof: by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]

中文:
定理 contDiff_succ_iff_deriv
  证明: by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]

Depends on / 依赖: contDiffOn_succ_iff_deriv_of_isOpen, contDiffOn_univ, differentiableOn_univ, isOpen_univ
-/
theorem contDiff_succ_iff_deriv :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOn 𝕜 f univ) ∧
      ContDiff 𝕜 n (deriv f) := by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]

/--
theorem `contDiff_one_iff_deriv` / 定理 `contDiff_one_iff_deriv`

English:
theorem contDiff_one_iff_deriv
  proof: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl]; rw [contDiff_succ_iff_deriv]
  simp

中文:
定理 contDiff_one_iff_deriv
  证明: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl]; rw [contDiff_succ_iff_deriv]
  simp

Depends on / 依赖: contDiff_succ_iff_deriv
-/
theorem contDiff_one_iff_deriv :
    ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (deriv f) := by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl]; rw [contDiff_succ_iff_deriv]
  simp

/--
theorem `contDiff_infty_iff_deriv` / 定理 `contDiff_infty_iff_deriv`

English:
theorem contDiff_infty_iff_deriv
  proof: by
  rw [show (∞ : Nat∞ω) = ∞ + 1 from rfl]; rw [contDiff_succ_iff_deriv]
  simp

中文:
定理 contDiff_infty_iff_deriv
  证明: by
  rw [show (∞ : Nat∞ω) = ∞ + 1 from rfl]; rw [contDiff_succ_iff_deriv]
  simp

Depends on / 依赖: contDiff_succ_iff_deriv
-/
theorem contDiff_infty_iff_deriv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (deriv f) := by
  rw [show (∞ : Nat∞ω) = ∞ + 1 from rfl]; rw [contDiff_succ_iff_deriv]
  simp

/--
theorem `ContDiff.continuous_deriv` / 定理 `ContDiff.continuous_deriv`

English:
theorem ContDiff.continuous_deriv
  given: (h : ContDiff 𝕜 n f) (hn : 1 <= n)
  statement: Continuous (deriv f)
  proof: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

@[fun_prop]

中文:
定理 连续可微.continuous_deriv
  条件: (h : 连续可微 𝕜 n f) (hn : 1 <= n)
  结论: 连续 (deriv f)
  证明: by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

@[fun_prop]

Depends on / 依赖: contDiff_succ_iff_deriv, contDiff_succ_iff_deriv.mp, continuous, h.of_le, of_le
-/
theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f) (hn : 1 <= n) : Continuous (deriv f) := by
  rw [show (1 : Nat∞ω) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

@[fun_prop]
/--
theorem `ContDiff.continuous_deriv_one` / 定理 `ContDiff.continuous_deriv_one`

English:
theorem ContDiff.continuous_deriv_one
  given: (h : ContDiff 𝕜 1 f)
  statement: Continuous (deriv f)
  proof: ContDiff.continuous_deriv h (le_refl 1)

@[fun_prop]

中文:
定理 连续可微.continuous_deriv_one
  条件: (h : 连续可微 𝕜 1 f)
  结论: 连续 (deriv f)
  证明: ContDiff.continuous_deriv h (le_refl 1)

@[fun_prop]

Depends on / 依赖: ContDiff, ContDiff.continuous_deriv, continuous_deriv, le_refl
-/
theorem ContDiff.continuous_deriv_one (h : ContDiff 𝕜 1 f) : Continuous (deriv f) :=
  ContDiff.continuous_deriv h (le_refl 1)

@[fun_prop]
/--
theorem `ContDiff.differentiable_deriv_two` / 定理 `ContDiff.differentiable_deriv_two`

English:
theorem ContDiff.differentiable_deriv_two
  given: (h : ContDiff 𝕜 2 f)
  statement: Differentiable 𝕜 (deriv f)
  proof: by
  unfold deriv; fun_prop

@[fun_prop]

中文:
定理 连续可微.differentiable_deriv_two
  条件: (h : 连续可微 𝕜 2 f)
  结论: 可微 𝕜 (deriv f)
  证明: by
  unfold deriv; fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem ContDiff.differentiable_deriv_two (h : ContDiff 𝕜 2 f) : Differentiable 𝕜 (deriv f) := by
  unfold deriv; fun_prop

@[fun_prop]
/--
lemma `ContDiffAt.derivWithin` / 引理 `ContDiffAt.derivWithin`

English:
lemma ContDiffAt.derivWithin
  given: {x : 𝕜} (H : ContDiffAt 𝕜 n f x) (hmn : m + 1 <= n)
  proof: by
  simpa using! ContDiffWithinAt.derivWithin (s := .univ) H.contDiffWithinAt (by simp) hmn

@[fun_prop]

中文:
引理 ContDiffAt.derivWithin
  条件: {x : 𝕜} (H : ContDiffAt 𝕜 n f x) (hmn : m + 1 <= n)
  证明: by
  simpa using! ContDiffWithinAt.derivWithin (s := .univ) H.contDiffWithinAt (by simp) hmn

@[fun_prop]
-/
protected lemma ContDiffAt.derivWithin {x : 𝕜} (H : ContDiffAt 𝕜 n f x) (hmn : m + 1 <= n) :
    ContDiffAt 𝕜 m (deriv f) x := by
  simpa using! ContDiffWithinAt.derivWithin (s := .univ) H.contDiffWithinAt (by simp) hmn

@[fun_prop]
/--
theorem `ContDiff.deriv'` / 定理 `ContDiff.deriv'`

English:
theorem ContDiff.deriv'
  given: (h : ContDiff 𝕜 (n + 1) f)
  statement: ContDiff 𝕜 n (deriv f)
  proof: by
  unfold deriv; fun_prop

@[fun_prop]

中文:
定理 连续可微.deriv'
  条件: (h : 连续可微 𝕜 (n + 1) f)
  结论: 连续可微 𝕜 n (deriv f)
  证明: by
  unfold deriv; fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem ContDiff.deriv' (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n (deriv f) := by
  unfold deriv; fun_prop

@[fun_prop]
/--
theorem `ContDiff.iterate_deriv` / 定理 `ContDiff.iterate_deriv`

English:
theorem ContDiff.iterate_deriv

中文:
定理 连续可微.iterate_deriv
-/
theorem ContDiff.iterate_deriv :
    forall (n : Nat) {f : 𝕜 -> F}, ContDiff 𝕜 ∞ f -> ContDiff 𝕜 ∞ (deriv^[n] f)
  | 0, _, hf => hf
  | n + 1, _, hf => ContDiff.iterate_deriv n (contDiff_infty_iff_deriv.mp hf).2

@[fun_prop]
/--
theorem `ContDiff.iterate_deriv'` / 定理 `ContDiff.iterate_deriv'`

English:
theorem ContDiff.iterate_deriv'
  given: (n : Nat)

中文:
定理 连续可微.iterate_deriv'
  条件: (n : 自然数)
-/
theorem ContDiff.iterate_deriv' (n : Nat) :
    forall (k : Nat) {f : 𝕜 -> F}, ContDiff 𝕜 (n + k : Nat) f -> ContDiff 𝕜 n (deriv^[k] f)
  | 0, _, hf => hf
  | k + 1, _, hf => ContDiff.iterate_deriv' _ k (contDiff_succ_iff_deriv.mp hf).2.2

end
