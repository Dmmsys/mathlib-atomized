/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

public section


noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

section CpowLimits

/-!
## Continuity for complex powers
-/


open Complex

variable {α : Type*}

/--
theorem `zero_cpow_eq_nhds` / 定理 `zero_cpow_eq_nhds`

English:
theorem zero_cpow_eq_nhds
  given: {b : Complex} (hb : b != 0)
  statement: (fun x : Complex => (0 : Complex) ^ x) =ᶠ[𝓝 b] 0
  proof: by
  suffices forallᶠ x : Complex in 𝓝 b, x != 0 from
    this.mono fun x hx => by
      dsimp only
      rw [zero_cpow hx]; rw [Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb

中文:
定理 zero_cpow_eq_nhds
  条件: {b : 复形} (hb : b != 0)
  结论: (fun x : 复形 => (0 : 复形) ^ x) =ᶠ[𝓝 b] 0
  证明: by
  suffices forallᶠ x : Complex in 𝓝 b, x != 0 from
    this.mono fun x hx => by
      dsimp only
      rw [zero_cpow hx]; rw [Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb

Depends on / 依赖: IsOpen, IsOpen.eventually_mem, Pi.zero_apply, eventually_mem, isOpen_ne, this.mono, zero_apply, zero_cpow
-/
theorem zero_cpow_eq_nhds {b : Complex} (hb : b != 0) : (fun x : Complex => (0 : Complex) ^ x) =ᶠ[𝓝 b] 0 := by
  suffices forallᶠ x : Complex in 𝓝 b, x != 0 from
    this.mono fun x hx => by
      dsimp only
      rw [zero_cpow hx]; rw [Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb

/--
theorem `cpow_eq_nhds` / 定理 `cpow_eq_nhds`

English:
theorem cpow_eq_nhds
  given: {a b : Complex} (ha : a != 0)
  proof: by
  suffices forallᶠ x : Complex in 𝓝 a, x != 0 from
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha

中文:
定理 cpow_eq_nhds
  条件: {a b : 复形} (ha : a != 0)
  证明: by
  suffices forallᶠ x : Complex in 𝓝 a, x != 0 from
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha

Depends on / 依赖: IsOpen, IsOpen.eventually_mem, cpow_def_of_ne_zero, eventually_mem, isOpen_ne, this.mono
-/
theorem cpow_eq_nhds {a b : Complex} (ha : a != 0) :
    (fun x => x ^ b) =ᶠ[𝓝 a] fun x => exp (log x * b) := by
  suffices forallᶠ x : Complex in 𝓝 a, x != 0 from
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha

/--
theorem `cpow_eq_nhds'` / 定理 `cpow_eq_nhds'`

English:
theorem cpow_eq_nhds'
  given: {p : Complex × Complex} (hp_fst : p.fst != 0)
  proof: by
  suffices IsOpen {x : Complex × Complex | x.1 = 0}ᶜ from
    mem_nhds_iff.mpr ⟨_, fun x hx => by simp_all [cpow_def_of_ne_zero], this, hp_fst⟩
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const

中文:
定理 cpow_eq_nhds'
  条件: {p : 复形 × 复形} (hp_fst : p.fst != 0)
  证明: by
  suffices IsOpen {x : Complex × Complex | x.1 = 0}ᶜ from
    mem_nhds_iff.mpr ⟨_, fun x hx => by simp_all [cpow_def_of_ne_zero], this, hp_fst⟩
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const

Depends on / 依赖: IsOpen, continuous_const, continuous_fst, cpow_def_of_ne_zero, hp_fst, isClosed_eq, isOpen_compl_iff, mem_nhds_iff, mem_nhds_iff.mpr
-/
theorem cpow_eq_nhds' {p : Complex × Complex} (hp_fst : p.fst != 0) :
    (fun x => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices IsOpen {x : Complex × Complex | x.1 = 0}ᶜ from
    mem_nhds_iff.mpr ⟨_, fun x hx => by simp_all [cpow_def_of_ne_zero], this, hp_fst⟩
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const

-- Continuity of `fun x => a ^ x`: union of these two lemmas is optimal.
/--
theorem `continuousAt_const_cpow` / 定理 `continuousAt_const_cpow`

English:
theorem continuousAt_const_cpow
  given: {a b : Complex} (ha : a != 0)
  statement: ContinuousAt (fun x : Complex => a ^ x) b
  proof: by
  have cpow_eq : (fun x : Complex => a ^ x) = fun x => exp (log a * x) := by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuousAt.comp (ContinuousAt.mul continuousAt_const continuousAt_id)

中文:
定理 continuousAt_const_cpow
  条件: {a b : 复形} (ha : a != 0)
  结论: ContinuousAt (fun x : 复形 => a ^ x) b
  证明: by
  have cpow_eq : (fun x : Complex => a ^ x) = fun x => exp (log a * x) := by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuousAt.comp (ContinuousAt.mul continuousAt_const continuousAt_id)

Depends on / 依赖: ContinuousAt, ContinuousAt.mul, continuousAt, continuousAt_const, continuousAt_id, continuous_exp, continuous_exp.continuousAt.comp, cpow_def_of_ne_zero, cpow_eq
-/
theorem continuousAt_const_cpow {a b : Complex} (ha : a != 0) : ContinuousAt (fun x : Complex => a ^ x) b := by
  have cpow_eq : (fun x : Complex => a ^ x) = fun x => exp (log a * x) := by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuousAt.comp (ContinuousAt.mul continuousAt_const continuousAt_id)

/--
theorem `continuousAt_const_cpow'` / 定理 `continuousAt_const_cpow'`

English:
theorem continuousAt_const_cpow'
  given: {a b : Complex} (h : b != 0)
  statement: ContinuousAt (fun x : Complex => a ^ x) b
  proof: by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha

中文:
定理 continuousAt_const_cpow'
  条件: {a b : 复形} (h : b != 0)
  结论: ContinuousAt (fun x : 复形 => a ^ x) b
  证明: by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha

Depends on / 依赖: continuousAt_congr, continuousAt_const, continuousAt_const_cpow, zero_cpow_eq_nhds
-/
theorem continuousAt_const_cpow' {a b : Complex} (h : b != 0) : ContinuousAt (fun x : Complex => a ^ x) b := by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha

/--
theorem `continuousAt_cpow` / 定理 `continuousAt_cpow`

English:
theorem continuousAt_cpow
  given: {p : Complex × Complex} (hp_fst : p.fst in slitPlane)
  proof: by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt

中文:
定理 continuousAt_cpow
  条件: {p : 复形 × 复形} (hp_fst : p.fst in slitPlane)
  证明: by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, ContinuousAt.mul, continuousAt, continuousAt_clog, continuousAt_congr, continuous_exp, continuous_exp.continuousAt.comp, continuous_fst, continuous_fst.continuousAt, continuous_snd, continuous_snd.continuousAt, cpow_eq_nhds, hp_fst, slitPlane_ne_zero
-/
theorem continuousAt_cpow {p : Complex × Complex} (hp_fst : p.fst in slitPlane) :
    ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p := by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt

/--
theorem `continuousAt_cpow_const` / 定理 `continuousAt_cpow_const`

English:
theorem continuousAt_cpow_const
  given: {a b : Complex} (ha : a in slitPlane)
  proof: Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prodMk continuousAt_const)

中文:
定理 continuousAt_cpow_const
  条件: {a b : 复形} (ha : a in slitPlane)
  证明: Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prodMk continuousAt_const)

Depends on / 依赖: Tendsto, Tendsto.comp, continuousAt_const, continuousAt_cpow, continuousAt_id, continuousAt_id.prodMk, prodMk
-/
theorem continuousAt_cpow_const {a b : Complex} (ha : a in slitPlane) :
    ContinuousAt (· ^ b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prodMk continuousAt_const)

/--
theorem `Filter.Tendsto.cpow` / 定理 `Filter.Tendsto.cpow`

English:
theorem Filter.Tendsto.cpow
  statement: {l : Filter α} {f g : α -> Complex} {a b : Complex} (hf : Tendsto f l (𝓝 a))
  proof: (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prodMk_nhds hg)

中文:
定理 滤子.收敛.cpow
  结论: {l : 滤子 α} {f g : α -> 复形} {a b : 复形} (hf : 收敛 f l (𝓝 a))
  证明: (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuousAt_cpow, hf.prodMk_nhds, prodMk_nhds, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.cpow {l : Filter α} {f g : α -> Complex} {a b : Complex} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : a in slitPlane) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prodMk_nhds hg)

/--
theorem `Filter.Tendsto.const_cpow` / 定理 `Filter.Tendsto.const_cpow`

English:
theorem Filter.Tendsto.const_cpow
  statement: {l : Filter α} {f : α -> Complex} {a b : Complex} (hf : Tendsto f l (𝓝 b))
  proof: by
  cases h with
  | inl h => exact (continuousAt_const_cpow h).tendsto.comp hf
  | inr h => exact (continuousAt_const_cpow' h).tendsto.comp hf

中文:
定理 滤子.收敛.const_cpow
  结论: {l : 滤子 α} {f : α -> 复形} {a b : 复形} (hf : 收敛 f l (𝓝 b))
  证明: by
  cases h with
  | inl h => exact (continuousAt_const_cpow h).tendsto.comp hf
  | inr h => exact (continuousAt_const_cpow' h).tendsto.comp hf

Depends on / 依赖: continuousAt_const_cpow, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.const_cpow {l : Filter α} {f : α -> Complex} {a b : Complex} (hf : Tendsto f l (𝓝 b))
    (h : a != 0 ∨ b != 0) : Tendsto (fun x => a ^ f x) l (𝓝 (a ^ b)) := by
  cases h with
  | inl h => exact (continuousAt_const_cpow h).tendsto.comp hf
  | inr h => exact (continuousAt_const_cpow' h).tendsto.comp hf

variable [TopologicalSpace α] {f g : α -> Complex} {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h0 : f a in slitPlane) :
    ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0

nonrec theorem ContinuousWithinAt.const_cpow {b : Complex} (hf : ContinuousWithinAt f s a)
    (h : b != 0 ∨ f a != 0) : ContinuousWithinAt (fun x => b ^ f x) s a :=
  hf.const_cpow h

nonrec theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : f a in slitPlane) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0

nonrec theorem ContinuousAt.const_cpow {b : Complex} (hf : ContinuousAt f a) (h : b != 0 ∨ f a != 0) :
    ContinuousAt (fun x => b ^ f x) a :=
  hf.const_cpow h

/--
theorem `ContinuousOn.cpow` / 定理 `ContinuousOn.cpow`

English:
theorem ContinuousOn.cpow
  statement: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)

中文:
定理 ContinuousOn.cpow
  结论: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)
-/
theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : forall a in s, f a in slitPlane) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)

/--
theorem `ContinuousOn.const_cpow` / 定理 `ContinuousOn.const_cpow`

English:
theorem ContinuousOn.const_cpow
  given: {b : Complex} (hf : ContinuousOn f s) (h : b != 0 ∨ forall a in s, f a != 0)
  proof: fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)

中文:
定理 ContinuousOn.const_cpow
  条件: {b : 复形} (hf : ContinuousOn f s) (h : b != 0 ∨ 对任意 a in s, f a != 0)
  证明: fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)

Depends on / 依赖: const_cpow, h.imp
-/
theorem ContinuousOn.const_cpow {b : Complex} (hf : ContinuousOn f s) (h : b != 0 ∨ forall a in s, f a != 0) :
    ContinuousOn (fun x => b ^ f x) s := fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)

/--
theorem `Continuous.cpow` / 定理 `Continuous.cpow`

English:
theorem Continuous.cpow
  statement: (hf : Continuous f) (hg : Continuous g)
  proof: continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)

中文:
定理 连续.cpow
  结论: (hf : 连续 f) (hg : 连续 g)
  证明: continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, hf.continuousAt.cpow, hg.continuousAt
-/
theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : forall a, f a in slitPlane) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)

/--
theorem `Continuous.const_cpow` / 定理 `Continuous.const_cpow`

English:
theorem Continuous.const_cpow
  given: {b : Complex} (hf : Continuous f) (h : b != 0 ∨ forall a, f a != 0)
  proof: continuous_iff_continuousAt.2 fun a => hf.continuousAt.const_cpow h.imp id fun h => h a

中文:
定理 连续.const_cpow
  条件: {b : 复形} (hf : 连续 f) (h : b != 0 ∨ 对任意 a, f a != 0)
  证明: continuous_iff_continuousAt.2 fun a => hf.continuousAt.const_cpow h.imp id fun h => h a

Depends on / 依赖: const_cpow, continuousAt, continuous_iff_continuousAt, h.imp, hf.continuousAt.const_cpow
-/
theorem Continuous.const_cpow {b : Complex} (hf : Continuous f) (h : b != 0 ∨ forall a, f a != 0) :
    Continuous fun x => b ^ f x :=
continuous_iff_continuousAt.2 fun a => hf.continuousAt.const_cpow h.imp id fun h => h a

/--
theorem `ContinuousOn.cpow_const` / 定理 `ContinuousOn.cpow_const`

English:
theorem ContinuousOn.cpow_const
  statement: {b : Complex} (hf : ContinuousOn f s)
  proof: hf.cpow continuousOn_const h

@[fun_prop]

中文:
定理 ContinuousOn.cpow_const
  结论: {b : 复形} (hf : ContinuousOn f s)
  证明: hf.cpow continuousOn_const h

@[fun_prop]

Depends on / 依赖: continuousOn_const, hf.cpow
-/
theorem ContinuousOn.cpow_const {b : Complex} (hf : ContinuousOn f s)
    (h : forall a : α, a in s -> f a in slitPlane) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h

@[fun_prop]
/--
lemma `continuous_const_cpow` / 引理 `continuous_const_cpow`

English:
lemma continuous_const_cpow
  given: (z : Complex) [NeZero z]
  statement: Continuous fun s : Complex => z ^ s
  proof: continuous_id.const_cpow (.inl <| NeZero.ne z)

中文:
引理 continuous_const_cpow
  条件: (z : 复形) [NeZero z]
  结论: 连续 fun s : 复形 => z ^ s
  证明: continuous_id.const_cpow (.inl <| NeZero.ne z)

Depends on / 依赖: NeZero, NeZero.ne, const_cpow, continuous_id, continuous_id.const_cpow
-/
lemma continuous_const_cpow (z : Complex) [NeZero z] : Continuous fun s : Complex => z ^ s :=
  continuous_id.const_cpow (.inl <| NeZero.ne z)

end CpowLimits

section RpowLimits

/-!
## Continuity for real powers
-/


namespace Real

/--
theorem `continuousAt_const_rpow` / 定理 `continuousAt_const_rpow`

English:
theorem continuousAt_const_rpow
  given: {a b : Real} (h : a != 0)
  statement: ContinuousAt (a ^ ·) b
  proof: by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

中文:
定理 continuousAt_const_rpow
  条件: {a b : 实数} (h : a != 0)
  结论: ContinuousAt (a ^ ·) b
  证明: by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

Depends on / 依赖: Complex.continuous_ofReal.continuousAt, Complex.continuous_re.continuousAt.comp, continuousAt, continuousAt_const_cpow, continuous_ofReal, continuous_re, rpow_def
-/
theorem continuousAt_const_rpow {a b : Real} (h : a != 0) : ContinuousAt (a ^ ·) b := by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

/--
theorem `continuousAt_const_rpow'` / 定理 `continuousAt_const_rpow'`

English:
theorem continuousAt_const_rpow'
  given: {a b : Real} (h : b != 0)
  statement: ContinuousAt (a ^ ·) b
  proof: by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow' ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

中文:
定理 continuousAt_const_rpow'
  条件: {a b : 实数} (h : b != 0)
  结论: ContinuousAt (a ^ ·) b
  证明: by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow' ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

Depends on / 依赖: Complex.continuous_ofReal.continuousAt, Complex.continuous_re.continuousAt.comp, continuousAt, continuousAt_const_cpow, continuous_ofReal, continuous_re, rpow_def
-/
theorem continuousAt_const_rpow' {a b : Real} (h : b != 0) : ContinuousAt (a ^ ·) b := by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow' ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

/--
theorem `rpow_eq_nhds_of_neg` / 定理 `rpow_eq_nhds_of_neg`

English:
theorem rpow_eq_nhds_of_neg
  given: {p : Real × Real} (hp_fst : p.fst < 0)
  proof: by
  suffices forallᶠ x : Real × Real in 𝓝 p, x.1 < 0 from
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst

中文:
定理 rpow_eq_nhds_of_neg
  条件: {p : 实数 × 实数} (hp_fst : p.fst < 0)
  证明: by
  suffices forallᶠ x : Real × Real in 𝓝 p, x.1 < 0 from
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst

Depends on / 依赖: IsOpen, IsOpen.eventually_mem, continuous_const, continuous_fst, eventually_mem, hp_fst, isOpen_lt, rpow_def_of_neg, this.mono
-/
theorem rpow_eq_nhds_of_neg {p : Real × Real} (hp_fst : p.fst < 0) :
    (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) := by
  suffices forallᶠ x : Real × Real in 𝓝 p, x.1 < 0 from
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst

/--
theorem `rpow_eq_nhds_of_pos` / 定理 `rpow_eq_nhds_of_pos`

English:
theorem rpow_eq_nhds_of_pos
  given: {p : Real × Real} (hp_fst : 0 < p.fst)
  proof: by
  suffices forallᶠ x : Real × Real in 𝓝 p, 0 < x.1 from
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst

中文:
定理 rpow_eq_nhds_of_pos
  条件: {p : 实数 × 实数} (hp_fst : 0 < p.fst)
  证明: by
  suffices forallᶠ x : Real × Real in 𝓝 p, 0 < x.1 from
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst

Depends on / 依赖: IsOpen, IsOpen.eventually_mem, continuous_const, continuous_fst, eventually_mem, hp_fst, isOpen_lt, rpow_def_of_pos, this.mono
-/
theorem rpow_eq_nhds_of_pos {p : Real × Real} (hp_fst : 0 < p.fst) :
    (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices forallᶠ x : Real × Real in 𝓝 p, 0 < x.1 from
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst

/--
theorem `continuousAt_rpow_of_ne` / 定理 `continuousAt_rpow_of_ne`

English:
theorem continuousAt_rpow_of_ne
  given: (p : Real × Real) (hp : p.1 != 0)
  proof: by
  rw [ne_iff_lt_or_gt] at hp
  cases hp with
  | inl hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine ContinuousAt.mul ?_ (by fun_prop)
    · refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
      exact (continuousAt_log hp.ne).comp continuous_fst.continuousAt
  | inr hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
    refine (continuousAt_log ?_).comp continuous_fst.continuousAt
    exact hp.ne'

中文:
定理 continuousAt_rpow_of_ne
  条件: (p : 实数 × 实数) (hp : p.1 != 0)
  证明: by
  rw [ne_iff_lt_or_gt] at hp
  cases hp with
  | inl hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine ContinuousAt.mul ?_ (by fun_prop)
    · refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
      exact (continuousAt_log hp.ne).comp continuous_fst.continuousAt
  | inr hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
    refine (continuousAt_log ?_).comp continuous_fst.continuousAt
    exact hp.ne'

Depends on / 依赖: ContinuousAt, ContinuousAt.mul, continuousAt, continuousAt_congr, continuousAt_log, continuous_exp, continuous_exp.continuousAt.comp, continuous_fs, continuous_fst, continuous_fst.continuousAt, continuous_snd, continuous_snd.continuousAt, fun_prop, hp.ne, ne_iff_lt_or_gt, rpow_eq_nhds_of_neg, rpow_eq_nhds_of_pos
-/
theorem continuousAt_rpow_of_ne (p : Real × Real) (hp : p.1 != 0) :
    ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p := by
  rw [ne_iff_lt_or_gt] at hp
  cases hp with
  | inl hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine ContinuousAt.mul ?_ (by fun_prop)
    · refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
      exact (continuousAt_log hp.ne).comp continuous_fst.continuousAt
  | inr hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
    refine (continuousAt_log ?_).comp continuous_fst.continuousAt
    exact hp.ne'

/--
theorem `continuousAt_rpow_of_pos` / 定理 `continuousAt_rpow_of_pos`

English:
theorem continuousAt_rpow_of_pos
  given: (p : Real × Real) (hp : 0 < p.2)
  proof: by
  obtain ⟨x, y⟩ := p
  dsimp only at hp
  obtain hx | rfl := ne_or_eq x 0
  · exact continuousAt_rpow_of_ne (x, y) hx
  have A : Tendsto (fun p : Real × Real => exp (log p.1 * p.2)) (𝓝[!=] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_log_nhdsNE_zero.comp tendsto_fst).atBot_mul_pos hp tendsto_snd)
  have B : Tendsto (fun p : Real × Real => p.1 ^ p.2) (𝓝[!=] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : Tendsto (fun p : Real × Real => p.1 ^ p.2) (𝓝[{0}] 0 ×ˢ 𝓝 y) (pure 0) := by
    rw [nhdsWithin_singleton]; rw [tendsto_pure]; rw [pure_prod]; rw [eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))

中文:
定理 continuousAt_rpow_of_pos
  条件: (p : 实数 × 实数) (hp : 0 < p.2)
  证明: by
  obtain ⟨x, y⟩ := p
  dsimp only at hp
  obtain hx | rfl := ne_or_eq x 0
  · exact continuousAt_rpow_of_ne (x, y) hx
  have A : Tendsto (fun p : Real × Real => exp (log p.1 * p.2)) (𝓝[!=] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_log_nhdsNE_zero.comp tendsto_fst).atBot_mul_pos hp tendsto_snd)
  have B : Tendsto (fun p : Real × Real => p.1 ^ p.2) (𝓝[!=] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : Tendsto (fun p : Real × Real => p.1 ^ p.2) (𝓝[{0}] 0 ×ˢ 𝓝 y) (pure 0) := by
    rw [nhdsWithin_singleton]; rw [tendsto_pure]; rw [pure_prod]; rw [eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))

Depends on / 依赖: Tendsto, abs_rpow_le_exp_log_mul, atBot_mul_pos, continuousAt_rpow_of_ne, ne_or_eq, squeeze_zero_norm, tendsto_exp_atBot, tendsto_exp_atBot.comp, tendsto_fst, tendsto_log_nhdsNE_zero, tendsto_log_nhdsNE_zero.comp, tendsto_snd
-/
theorem continuousAt_rpow_of_pos (p : Real × Real) (hp : 0 < p.2) :
    ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p := by
  obtain ⟨x, y⟩ := p
  dsimp only at hp
  obtain hx | rfl := ne_or_eq x 0
  · exact continuousAt_rpow_of_ne (x, y) hx
  have A : Tendsto (fun p : Real × Real => exp (log p.1 * p.2)) (𝓝[!=] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_log_nhdsNE_zero.comp tendsto_fst).atBot_mul_pos hp tendsto_snd)
  have B : Tendsto (fun p : Real × Real => p.1 ^ p.2) (𝓝[!=] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : Tendsto (fun p : Real × Real => p.1 ^ p.2) (𝓝[{0}] 0 ×ˢ 𝓝 y) (pure 0) := by
    rw [nhdsWithin_singleton]; rw [tendsto_pure]; rw [pure_prod]; rw [eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))

/--
theorem `continuousAt_rpow` / 定理 `continuousAt_rpow`

English:
theorem continuousAt_rpow
  given: (p : Real × Real) (h : p.1 != 0 ∨ 0 < p.2)
  proof: h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h

@[fun_prop]

中文:
定理 continuousAt_rpow
  条件: (p : 实数 × 实数) (h : p.1 != 0 ∨ 0 < p.2)
  证明: h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h

@[fun_prop]

Depends on / 依赖: continuousAt_rpow_of_ne, continuousAt_rpow_of_pos, h.elim
-/
theorem continuousAt_rpow (p : Real × Real) (h : p.1 != 0 ∨ 0 < p.2) :
    ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p :=
  h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h

@[fun_prop]
/--
theorem `continuousAt_rpow_const` / 定理 `continuousAt_rpow_const`

English:
theorem continuousAt_rpow_const
  given: (x : Real) (q : Real) (h : x != 0 ∨ 0 <= q)
  proof: by
  rw [le_iff_lt_or_eq]; rw [← or_assoc] at h
  obtain h | rfl := h
  · exact (continuousAt_rpow (x, q) h).comp₂ continuousAt_id continuousAt_const
  · simp_rw [rpow_zero]; exact continuousAt_const

@[fun_prop]

中文:
定理 continuousAt_rpow_const
  条件: (x : 实数) (q : 实数) (h : x != 0 ∨ 0 <= q)
  证明: by
  rw [le_iff_lt_or_eq]; rw [← or_assoc] at h
  obtain h | rfl := h
  · exact (continuousAt_rpow (x, q) h).comp₂ continuousAt_id continuousAt_const
  · simp_rw [rpow_zero]; exact continuousAt_const

@[fun_prop]

Depends on / 依赖: continuousAt_const, continuousAt_id, continuousAt_rpow, le_iff_lt_or_eq, or_assoc, rpow_zero, simp_rw
-/
theorem continuousAt_rpow_const (x : Real) (q : Real) (h : x != 0 ∨ 0 <= q) :
    ContinuousAt (fun x : Real => x ^ q) x := by
  rw [le_iff_lt_or_eq]; rw [← or_assoc] at h
  obtain h | rfl := h
  · exact (continuousAt_rpow (x, q) h).comp₂ continuousAt_id continuousAt_const
  · simp_rw [rpow_zero]; exact continuousAt_const

@[fun_prop]
/--
theorem `continuous_rpow_const` / 定理 `continuous_rpow_const`

English:
theorem continuous_rpow_const
  given: {q : Real} (h : 0 <= q)
  statement: Continuous (fun x : Real => x ^ q)
  proof: continuous_iff_continuousAt.mpr fun x => continuousAt_rpow_const x q (.inr h)

@[fun_prop]

中文:
定理 continuous_rpow_const
  条件: {q : 实数} (h : 0 <= q)
  结论: 连续 (fun x : 实数 => x ^ q)
  证明: continuous_iff_continuousAt.mpr fun x => continuousAt_rpow_const x q (.inr h)

@[fun_prop]

Depends on / 依赖: continuousAt_rpow_const, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
theorem continuous_rpow_const {q : Real} (h : 0 <= q) : Continuous (fun x : Real => x ^ q) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_rpow_const x q (.inr h)

@[fun_prop]
/--
lemma `continuous_const_rpow` / 引理 `continuous_const_rpow`

English:
lemma continuous_const_rpow
  given: {a : Real} (h : a != 0)
  statement: Continuous (fun x : Real => a ^ x)
  proof: continuous_iff_continuousAt.mpr fun _ => continuousAt_const_rpow h

中文:
引理 continuous_const_rpow
  条件: {a : 实数} (h : a != 0)
  结论: 连续 (fun x : 实数 => a ^ x)
  证明: continuous_iff_continuousAt.mpr fun _ => continuousAt_const_rpow h

Depends on / 依赖: continuousAt_const_rpow, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
lemma continuous_const_rpow {a : Real} (h : a != 0) : Continuous (fun x : Real => a ^ x) :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_const_rpow h

end Real

section

variable {α : Type*}

/--
theorem `Filter.Tendsto.rpow` / 定理 `Filter.Tendsto.rpow`

English:
theorem Filter.Tendsto.rpow
  statement: {l : Filter α} {f g : α -> Real} {x y : Real} (hf : Tendsto f l (𝓝 x))
  proof: (Real.continuousAt_rpow (x, y) h).tendsto.comp (hf.prodMk_nhds hg)

中文:
定理 滤子.收敛.rpow
  结论: {l : 滤子 α} {f g : α -> 实数} {x y : 实数} (hf : 收敛 f l (𝓝 x))
  证明: (Real.continuousAt_rpow (x, y) h).tendsto.comp (hf.prodMk_nhds hg)

Depends on / 依赖: Real.continuousAt_rpow, continuousAt_rpow, hf.prodMk_nhds, prodMk_nhds, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.rpow {l : Filter α} {f g : α -> Real} {x y : Real} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) (h : x != 0 ∨ 0 < y) : Tendsto (fun t => f t ^ g t) l (𝓝 (x ^ y)) :=
  (Real.continuousAt_rpow (x, y) h).tendsto.comp (hf.prodMk_nhds hg)

/--
theorem `Filter.Tendsto.rpow_const` / 定理 `Filter.Tendsto.rpow_const`

English:
theorem Filter.Tendsto.rpow_const
  statement: {l : Filter α} {f : α -> Real} {x p : Real} (hf : Tendsto f l (𝓝 x))
  proof: if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)

中文:
定理 滤子.收敛.rpow_const
  结论: {l : 滤子 α} {f : α -> 实数} {x p : 实数} (hf : 收敛 f l (𝓝 x))
  证明: if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)

Depends on / 依赖: h.imp, hf.rpow, lt_of_ne, tendsto_const_nhds
-/
theorem Filter.Tendsto.rpow_const {l : Filter α} {f : α -> Real} {x p : Real} (hf : Tendsto f l (𝓝 x))
    (h : x != 0 ∨ 0 <= p) : Tendsto (fun a => f a ^ p) l (𝓝 (x ^ p)) :=
  if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)

/--
theorem `Filter.Tendsto.rpow_const_nhds_zero` / 定理 `Filter.Tendsto.rpow_const_nhds_zero`

English:
theorem Filter.Tendsto.rpow_const_nhds_zero
  statement: {l : Filter α} {f : α -> Real} {p : Real}
  proof: Real.zero_rpow hp.ne' ▸ hf.rpow_const (.inr hp.le)

中文:
定理 滤子.收敛.rpow_const_nhds_zero
  结论: {l : 滤子 α} {f : α -> 实数} {p : 实数}
  证明: Real.zero_rpow hp.ne' ▸ hf.rpow_const (.inr hp.le)

Depends on / 依赖: Real.zero_rpow, hf.rpow_const, hp.le, hp.ne, rpow_const, zero_rpow
-/
theorem Filter.Tendsto.rpow_const_nhds_zero {l : Filter α} {f : α -> Real} {p : Real}
    (hf : Tendsto f l (𝓝 0)) (hp : 0 < p) :
    Tendsto (fun t => f t ^ p) l (𝓝 0) :=
  Real.zero_rpow hp.ne' ▸ hf.rpow_const (.inr hp.le)

variable [TopologicalSpace α] {f g : α -> Real} {s : Set α} {x : α} {p : Real}

nonrec theorem ContinuousAt.rpow (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f x != 0 ∨ 0 < g x) : ContinuousAt (fun t => f t ^ g t) x :=
  hf.rpow hg h

nonrec theorem ContinuousWithinAt.rpow (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) (h : f x != 0 ∨ 0 < g x) :
    ContinuousWithinAt (fun t => f t ^ g t) s x :=
  hf.rpow hg h

/--
theorem `ContinuousOn.rpow` / 定理 `ContinuousOn.rpow`

English:
theorem ContinuousOn.rpow
  statement: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)

中文:
定理 ContinuousOn.rpow
  结论: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)
-/
theorem ContinuousOn.rpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : forall x in s, f x != 0 ∨ 0 < g x) : ContinuousOn (fun t => f t ^ g t) s := fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)

/--
theorem `Continuous.rpow` / 定理 `Continuous.rpow`

English:
theorem Continuous.rpow
  given: (hf : Continuous f) (hg : Continuous g) (h : forall x, f x != 0 ∨ 0 < g x)
  proof: continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow hg.continuousAt (h x)

nonrec theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x != 0 ∨ 0 <= p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h

nonrec theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x != 0 ∨ 0 <= p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h

中文:
定理 连续.rpow
  条件: (hf : 连续 f) (hg : 连续 g) (h : 对任意 x, f x != 0 ∨ 0 < g x)
  证明: continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow hg.continuousAt (h x)

nonrec theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x != 0 ∨ 0 <= p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h

nonrec theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x != 0 ∨ 0 <= p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, hf.continuousAt.rpow, hg.continuousAt
-/
theorem Continuous.rpow (hf : Continuous f) (hg : Continuous g) (h : forall x, f x != 0 ∨ 0 < g x) :
    Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow hg.continuousAt (h x)

nonrec theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x != 0 ∨ 0 <= p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h

nonrec theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x != 0 ∨ 0 <= p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h

/--
theorem `ContinuousOn.rpow_const` / 定理 `ContinuousOn.rpow_const`

English:
theorem ContinuousOn.rpow_const
  given: (hf : ContinuousOn f s) (h : forall x in s, f x != 0 ∨ 0 <= p)
  proof: fun x hx => (hf x hx).rpow_const (h x hx)

中文:
定理 ContinuousOn.rpow_const
  条件: (hf : ContinuousOn f s) (h : 对任意 x in s, f x != 0 ∨ 0 <= p)
  证明: fun x hx => (hf x hx).rpow_const (h x hx)

Depends on / 依赖: rpow_const
-/
theorem ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : forall x in s, f x != 0 ∨ 0 <= p) :
    ContinuousOn (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)

/--
theorem `Continuous.rpow_const` / 定理 `Continuous.rpow_const`

English:
theorem Continuous.rpow_const
  given: (hf : Continuous f) (h : forall x, f x != 0 ∨ 0 <= p)
  proof: continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow_const (h x)

中文:
定理 连续.rpow_const
  条件: (hf : 连续 f) (h : 对任意 x, f x != 0 ∨ 0 <= p)
  证明: continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow_const (h x)

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, hf.continuousAt.rpow_const, rpow_const
-/
theorem Continuous.rpow_const (hf : Continuous f) (h : forall x, f x != 0 ∨ 0 <= p) :
    Continuous fun x => f x ^ p :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow_const (h x)

end

end RpowLimits

/-! ## Continuity results for `cpow`, part II

These results involve relating real and complex powers, so cannot be done higher up.
-/


section CpowLimits2

namespace Complex

/--
theorem `continuousAt_cpow_zero_of_re_pos` / 定理 `continuousAt_cpow_zero_of_re_pos`

English:
theorem continuousAt_cpow_zero_of_re_pos
  given: {z : Complex} (hz : 0 < z.re)
  proof: by
  have hz₀ : z != 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt]; rw [zero_cpow hz₀]; rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_cpow_le _ _) ?_
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · convert!
    (continuous_fst.norm.tendsto ((0 : Complex), z)).rpow ((continuous_re.comp continuous_snd).tendsto _)
      _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt |im z| with ⟨C, hC⟩
    refine ⟨Real.exp (π * C), eventually_map.2 ?_⟩
    refine
      (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually (gt_mem_nhds hC)).mono
fun z hz => Real.exp_le_exp.2 (neg_le_abs _).trans ?_
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        Real.pi_pos.le

中文:
定理 continuousAt_cpow_zero_of_re_pos
  条件: {z : 复形} (hz : 0 < z.re)
  证明: by
  have hz₀ : z != 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt]; rw [zero_cpow hz₀]; rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_cpow_le _ _) ?_
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · convert!
    (continuous_fst.norm.tendsto ((0 : Complex), z)).rpow ((continuous_re.comp continuous_snd).tendsto _)
      _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt |im z| with ⟨C, hC⟩
    refine ⟨Real.exp (π * C), eventually_map.2 ?_⟩
    refine
      (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually (gt_mem_nhds hC)).mono
fun z hz => Real.exp_le_exp.2 (neg_le_abs _).trans ?_
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        Real.pi_pos.le

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, Real.exp_neg, Real.norm_eq_abs, Real.zero_rpow, Tendsto, Tendsto.zero_mul_isBoundedUnder_le, comp_def, continuous_fst, continuous_fst.norm.tendsto, continuous_re, continuous_re.comp, continuous_snd, convert, div_eq_mul_inv, exp_neg, hz.ne, ne_of_apply_ne, norm_cpow_le
-/
theorem continuousAt_cpow_zero_of_re_pos {z : Complex} (hz : 0 < z.re) :
    ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) (0, z) := by
  have hz₀ : z != 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt]; rw [zero_cpow hz₀]; rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_cpow_le _ _) ?_
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · convert!
    (continuous_fst.norm.tendsto ((0 : Complex), z)).rpow ((continuous_re.comp continuous_snd).tendsto _)
      _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt |im z| with ⟨C, hC⟩
    refine ⟨Real.exp (π * C), eventually_map.2 ?_⟩
    refine
      (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually (gt_mem_nhds hC)).mono
fun z hz => Real.exp_le_exp.2 (neg_le_abs _).trans ?_
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        Real.pi_pos.le

open ComplexOrder in
/--
theorem `continuousAt_cpow_of_re_pos` / 定理 `continuousAt_cpow_of_re_pos`

English:
theorem continuousAt_cpow_of_re_pos
  given: {p : Complex × Complex} (h₁ : 0 <= p.1.re ∨ p.1.im != 0) (h₂ : 0 < p.2.re)
  proof: by
  obtain ⟨z, w⟩ := p
  rw [← not_lt_zero_iff]; rw [lt_iff_le_and_ne]; rw [not_and_or]; rw [Ne]; rw [Classical.not_not]; rw [not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts [continuousAt_cpow h₁, continuousAt_cpow_zero_of_re_pos h₂]

中文:
定理 continuousAt_cpow_of_re_pos
  条件: {p : 复形 × 复形} (h₁ : 0 <= p.1.re ∨ p.1.im != 0) (h₂ : 0 < p.2.re)
  证明: by
  obtain ⟨z, w⟩ := p
  rw [← not_lt_zero_iff]; rw [lt_iff_le_and_ne]; rw [not_and_or]; rw [Ne]; rw [Classical.not_not]; rw [not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts [continuousAt_cpow h₁, continuousAt_cpow_zero_of_re_pos h₂]

Depends on / 依赖: Classical, Classical.not_not, continuousAt_cpow, continuousAt_cpow_zero_of_re_pos, exacts, lt_iff_le_and_ne, not_and_or, not_le_zero_iff, not_lt_zero_iff, not_not
-/
theorem continuousAt_cpow_of_re_pos {p : Complex × Complex} (h₁ : 0 <= p.1.re ∨ p.1.im != 0) (h₂ : 0 < p.2.re) :
    ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p := by
  obtain ⟨z, w⟩ := p
  rw [← not_lt_zero_iff]; rw [lt_iff_le_and_ne]; rw [not_and_or]; rw [Ne]; rw [Classical.not_not]; rw [not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts [continuousAt_cpow h₁, continuousAt_cpow_zero_of_re_pos h₂]

/--
theorem `continuousAt_cpow_const_of_re_pos` / 定理 `continuousAt_cpow_const_of_re_pos`

English:
theorem continuousAt_cpow_const_of_re_pos
  given: {z w : Complex} (hz : 0 <= re z ∨ im z != 0) (hw : 0 < re w)
  proof: Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw)
    (continuousAt_id.prodMk continuousAt_const)

中文:
定理 continuousAt_cpow_const_of_re_pos
  条件: {z w : 复形} (hz : 0 <= re z ∨ im z != 0) (hw : 0 < re w)
  证明: Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw)
    (continuousAt_id.prodMk continuousAt_const)

Depends on / 依赖: Tendsto, Tendsto.comp, continuousAt_const, continuousAt_cpow_of_re_pos, continuousAt_id, continuousAt_id.prodMk, prodMk
-/
theorem continuousAt_cpow_const_of_re_pos {z w : Complex} (hz : 0 <= re z ∨ im z != 0) (hw : 0 < re w) :
    ContinuousAt (fun x => x ^ w) z :=
  Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw)
    (continuousAt_id.prodMk continuousAt_const)

/--
theorem `continuousAt_ofReal_cpow` / 定理 `continuousAt_ofReal_cpow`

English:
theorem continuousAt_ofReal_cpow
  given: (x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0)
  proof: by
  rcases lt_trichotomy (0 : Real) x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) (x, y) := by fun_prop
    refine (continuousAt_cpow (Or.inl ?_)).comp this
    rwa [ofReal_re]
  · -- x = 0 : reduce to continuousAt_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : Complex × Complex -> Complex) ⟨↑(0 : Real), y⟩ := by
      rw [ofReal_zero]
      apply continuousAt_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) ⟨0, y⟩ := by fun_prop
    exact A.comp_of_eq B rfl
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-(p.1 : Complex)) ^ p.2 * exp (π * I * p.2) : Real × Complex -> Complex) (x, y) by
      refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) ?_)
      exact fun p hp => (ofReal_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) (x, y) := by fun_prop
    apply ContinuousAt.mul
    · refine (continuousAt_cpow (Or.inl ?_)).comp A
      rwa [neg_re, ofReal_re, neg_pos]
    · fun_prop

中文:
定理 continuousAt_of实数_cpow
  条件: (x : 实数) (y : 复形) (h : 0 < y.re ∨ x != 0)
  证明: by
  rcases lt_trichotomy (0 : Real) x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) (x, y) := by fun_prop
    refine (continuousAt_cpow (Or.inl ?_)).comp this
    rwa [ofReal_re]
  · -- x = 0 : reduce to continuousAt_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : Complex × Complex -> Complex) ⟨↑(0 : Real), y⟩ := by
      rw [ofReal_zero]
      apply continuousAt_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) ⟨0, y⟩ := by fun_prop
    exact A.comp_of_eq B rfl
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-(p.1 : Complex)) ^ p.2 * exp (π * I * p.2) : Real × Complex -> Complex) (x, y) by
      refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) ?_)
      exact fun p hp => (ofReal_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) (x, y) := by fun_prop
    apply ContinuousAt.mul
    · refine (continuousAt_cpow (Or.inl ?_)).comp A
      rwa [neg_re, ofReal_re, neg_pos]
    · fun_prop

Depends on / 依赖: ContinuousAt, Or.inl, continuousAt_cpow, continuousAt_cpow_zero_of_re_pos, fun_prop, lt_trichotomy, ofReal_re, ofReal_zero
-/
theorem continuousAt_ofReal_cpow (x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) :
    ContinuousAt (fun p => (p.1 : Complex) ^ p.2 : Real × Complex -> Complex) (x, y) := by
  rcases lt_trichotomy (0 : Real) x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) (x, y) := by fun_prop
    refine (continuousAt_cpow (Or.inl ?_)).comp this
    rwa [ofReal_re]
  · -- x = 0 : reduce to continuousAt_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : Complex × Complex -> Complex) ⟨↑(0 : Real), y⟩ := by
      rw [ofReal_zero]
      apply continuousAt_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) ⟨0, y⟩ := by fun_prop
    exact A.comp_of_eq B rfl
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-(p.1 : Complex)) ^ p.2 * exp (π * I * p.2) : Real × Complex -> Complex) (x, y) by
      refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) ?_)
      exact fun p hp => (ofReal_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : Real × Complex -> Complex × Complex) (x, y) := by fun_prop
    apply ContinuousAt.mul
    · refine (continuousAt_cpow (Or.inl ?_)).comp A
      rwa [neg_re, ofReal_re, neg_pos]
    · fun_prop

/--
theorem `continuousAt_ofReal_cpow_const` / 定理 `continuousAt_ofReal_cpow_const`

English:
theorem continuousAt_ofReal_cpow_const
  given: (x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0)
  proof: (continuousAt_ofReal_cpow x y h).comp₂_of_eq (by fun_prop) (by fun_prop) rfl

中文:
定理 continuousAt_of实数_cpow_const
  条件: (x : 实数) (y : 复形) (h : 0 < y.re ∨ x != 0)
  证明: (continuousAt_ofReal_cpow x y h).comp₂_of_eq (by fun_prop) (by fun_prop) rfl

Depends on / 依赖: continuousAt_ofReal_cpow, fun_prop
-/
theorem continuousAt_ofReal_cpow_const (x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) :
    ContinuousAt (fun a => (a : Complex) ^ y : Real -> Complex) x :=
  (continuousAt_ofReal_cpow x y h).comp₂_of_eq (by fun_prop) (by fun_prop) rfl

/--
theorem `continuous_ofReal_cpow_const` / 定理 `continuous_ofReal_cpow_const`

English:
theorem continuous_ofReal_cpow_const
  given: {y : Complex} (hs : 0 < y.re)
  proof: continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x y (Or.inl hs)

中文:
定理 continuous_of实数_cpow_const
  条件: {y : 复形} (hs : 0 < y.re)
  证明: continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x y (Or.inl hs)

Depends on / 依赖: Or.inl, continuousAt_ofReal_cpow_const, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
theorem continuous_ofReal_cpow_const {y : Complex} (hs : 0 < y.re) :
    Continuous (fun x => (x : Complex) ^ y : Real -> Complex) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x y (Or.inl hs)

end Complex

end CpowLimits2

/-! ## Limits and continuity for `ℝ≥0` powers -/


namespace NNReal

/--
theorem `continuousAt_rpow` / 定理 `continuousAt_rpow`

English:
theorem continuousAt_rpow
  given: {x : Real>=0} {y : Real} (h : x != 0 ∨ 0 < y)
  proof: by
  have :
    (fun p : Real>=0 × Real => p.1 ^ p.2) =
      Real.toNNReal ∘ (fun p : Real × Real => p.1 ^ p.2) ∘ fun p : Real>=0 × Real => (p.1.1, p.2) := by
    ext p
    simp only [coe_rpow, val_eq_coe, Function.comp_apply, coe_toNNReal', left_eq_sup]
    positivity
  rw [this]
  refine continuous_real_toNNReal.continuousAt.comp (ContinuousAt.comp ?_ ?_)
  · apply Real.continuousAt_rpow
    simpa using h
  · fun_prop

中文:
定理 continuousAt_rpow
  条件: {x : 实数>=0} {y : 实数} (h : x != 0 ∨ 0 < y)
  证明: by
  have :
    (fun p : Real>=0 × Real => p.1 ^ p.2) =
      Real.toNNReal ∘ (fun p : Real × Real => p.1 ^ p.2) ∘ fun p : Real>=0 × Real => (p.1.1, p.2) := by
    ext p
    simp only [coe_rpow, val_eq_coe, Function.comp_apply, coe_toNNReal', left_eq_sup]
    positivity
  rw [this]
  refine continuous_real_toNNReal.continuousAt.comp (ContinuousAt.comp ?_ ?_)
  · apply Real.continuousAt_rpow
    simpa using h
  · fun_prop

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, Function, Function.comp_apply, Real.continuousAt_rpow, Real.toNNReal, coe_rpow, coe_toNNReal, comp_apply, continuousAt, continuousAt_rpow, continuous_real_toNNReal, continuous_real_toNNReal.continuousAt.comp, fun_prop, left_eq_sup, toNNReal, val_eq_coe
-/
theorem continuousAt_rpow {x : Real>=0} {y : Real} (h : x != 0 ∨ 0 < y) :
    ContinuousAt (fun p : Real>=0 × Real => p.1 ^ p.2) (x, y) := by
  have :
    (fun p : Real>=0 × Real => p.1 ^ p.2) =
      Real.toNNReal ∘ (fun p : Real × Real => p.1 ^ p.2) ∘ fun p : Real>=0 × Real => (p.1.1, p.2) := by
    ext p
    simp only [coe_rpow, val_eq_coe, Function.comp_apply, coe_toNNReal', left_eq_sup]
    positivity
  rw [this]
  refine continuous_real_toNNReal.continuousAt.comp (ContinuousAt.comp ?_ ?_)
  · apply Real.continuousAt_rpow
    simpa using h
  · fun_prop

/--
theorem `eventually_pow_one_div_le` / 定理 `eventually_pow_one_div_le`

English:
theorem eventually_pow_one_div_le
  given: (x : Real>=0) {y : Real>=0} (hy : 1 < y)
  proof: by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩
  simp only [one_div]
  simpa only [NNReal.rpow_inv_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_natCast] using hm.le.trans (pow_right_mono₀ hy.le (m.le_succ.trans hn))

中文:
定理 eventually_pow_one_div_le
  条件: (x : 实数>=0) {y : 实数>=0} (hy : 1 < y)
  证明: by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩
  simp only [one_div]
  simpa only [NNReal.rpow_inv_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_natCast] using hm.le.trans (pow_right_mono₀ hy.le (m.le_succ.trans hn))

Depends on / 依赖: NNReal, NNReal.rpow_inv_le_iff, NNReal.rpow_natCast, Nat.cast_pos, add_one_pow_unbounded_of_pos, cast_pos, eventually_atTop, hm.le.trans, hy.le, le_succ, m.le_succ.trans, m.succ_pos.trans_le, one_div, rpow_inv_le_iff, rpow_natCast, succ_pos, trans_le, tsub_add_cancel_of_le, tsub_pos_of_lt
-/
theorem eventually_pow_one_div_le (x : Real>=0) {y : Real>=0} (hy : 1 < y) :
    forallᶠ n : Nat in atTop, x ^ (1 / n : Real) <= y := by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩
  simp only [one_div]
  simpa only [NNReal.rpow_inv_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_natCast] using hm.le.trans (pow_right_mono₀ hy.le (m.le_succ.trans hn))

end NNReal

open Filter

/--
theorem `Filter.Tendsto.nnrpow` / 定理 `Filter.Tendsto.nnrpow`

English:
theorem Filter.Tendsto.nnrpow
  statement: {α : Type*} {f : Filter α} {u : α -> Real>=0} {v : α -> Real} {x : Real>=0}
  proof: Tendsto.comp (NNReal.continuousAt_rpow h) (hx.prodMk_nhds hy)

中文:
定理 滤子.收敛.nnrpow
  结论: {α : 类型} {f : 滤子 α} {u : α -> 实数>=0} {v : α -> 实数} {x : 实数>=0}
  证明: Tendsto.comp (NNReal.continuousAt_rpow h) (hx.prodMk_nhds hy)

Depends on / 依赖: NNReal, NNReal.continuousAt_rpow, Tendsto, Tendsto.comp, continuousAt_rpow, hx.prodMk_nhds, prodMk_nhds
-/
theorem Filter.Tendsto.nnrpow {α : Type*} {f : Filter α} {u : α -> Real>=0} {v : α -> Real} {x : Real>=0}
    {y : Real} (hx : Tendsto u f (𝓝 x)) (hy : Tendsto v f (𝓝 y)) (h : x != 0 ∨ 0 < y) :
    Tendsto (fun a => u a ^ v a) f (𝓝 (x ^ y)) :=
  Tendsto.comp (NNReal.continuousAt_rpow h) (hx.prodMk_nhds hy)

namespace NNReal

/--
theorem `continuousAt_rpow_const` / 定理 `continuousAt_rpow_const`

English:
theorem continuousAt_rpow_const
  given: {x : Real>=0} {y : Real} (h : x != 0 ∨ 0 <= y)
  proof: h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)

@[fun_prop]

中文:
定理 continuousAt_rpow_const
  条件: {x : 实数>=0} {y : 实数} (h : x != 0 ∨ 0 <= y)
  证明: h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)

@[fun_prop]

Depends on / 依赖: Or.inl, Or.inr, continuousAt_const, eq_or_lt, h.elim, h.eq_or_lt.elim, nnrpow, rpow_zero, tendsto_const_nhds, tendsto_id, tendsto_id.nnrpow
-/
theorem continuousAt_rpow_const {x : Real>=0} {y : Real} (h : x != 0 ∨ 0 <= y) :
    ContinuousAt (fun z => z ^ y) x :=
  h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)

@[fun_prop]
/--
theorem `continuous_rpow_const` / 定理 `continuous_rpow_const`

English:
theorem continuous_rpow_const
  given: {y : Real} (h : 0 <= y)
  statement: Continuous fun x : Real>=0 => x ^ y
  proof: continuous_iff_continuousAt.2 fun _ => continuousAt_rpow_const (Or.inr h)

@[fun_prop]

中文:
定理 continuous_rpow_const
  条件: {y : 实数} (h : 0 <= y)
  结论: 连续 fun x : 实数>=0 => x ^ y
  证明: continuous_iff_continuousAt.2 fun _ => continuousAt_rpow_const (Or.inr h)

@[fun_prop]

Depends on / 依赖: Or.inr, continuousAt_rpow_const, continuous_iff_continuousAt
-/
theorem continuous_rpow_const {y : Real} (h : 0 <= y) : Continuous fun x : Real>=0 => x ^ y :=
  continuous_iff_continuousAt.2 fun _ => continuousAt_rpow_const (Or.inr h)

@[fun_prop]
/--
theorem `continuousOn_rpow_const_compl_zero` / 定理 `continuousOn_rpow_const_compl_zero`

English:
theorem continuousOn_rpow_const_compl_zero
  given: {r : Real}
  proof: fun _ h => ContinuousAt.continuousWithinAt NNReal.continuousAt_rpow_const (.inl h)

中文:
定理 continuousOn_rpow_const_compl_zero
  条件: {r : 实数}
  证明: fun _ h => ContinuousAt.continuousWithinAt NNReal.continuousAt_rpow_const (.inl h)

Depends on / 依赖: ContinuousAt, ContinuousAt.continuousWithinAt, NNReal, NNReal.continuousAt_rpow_const, continuousAt_rpow_const, continuousWithinAt
-/
theorem continuousOn_rpow_const_compl_zero {r : Real} :
    ContinuousOn (fun z : Real>=0 => z ^ r) {0}ᶜ :=
fun _ h => ContinuousAt.continuousWithinAt NNReal.continuousAt_rpow_const (.inl h)

-- even though this follows from `ContinuousOn.mono` and the previous lemma, we include it for
-- automation purposes with `fun_prop`, because the side goal `0 ∉ s ∨ 0 ≤ r` is often easy to check
@[fun_prop]
/--
theorem `continuousOn_rpow_const` / 定理 `continuousOn_rpow_const`

English:
theorem continuousOn_rpow_const
  statement: {r : Real} {s : Set Real>=0}
  proof: h.elim (fun _ => ContinuousOn.mono (s := {0}ᶜ) (by fun_prop) (by simp_all))
    (NNReal.continuous_rpow_const · |>.continuousOn)

中文:
定理 continuousOn_rpow_const
  结论: {r : 实数} {s : 集合 实数>=0}
  证明: h.elim (fun _ => ContinuousOn.mono (s := {0}ᶜ) (by fun_prop) (by simp_all))
    (NNReal.continuous_rpow_const · |>.continuousOn)

Depends on / 依赖: ContinuousOn, ContinuousOn.mono, NNReal, NNReal.continuous_rpow_const, continuousOn, continuous_rpow_const, fun_prop, h.elim
-/
theorem continuousOn_rpow_const {r : Real} {s : Set Real>=0}
    (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s :=
  h.elim (fun _ => ContinuousOn.mono (s := {0}ᶜ) (by fun_prop) (by simp_all))
    (NNReal.continuous_rpow_const · |>.continuousOn)

end NNReal

/-! ## Continuity for `ℝ≥0∞` powers -/


namespace ENNReal

/--
theorem `eventually_pow_one_div_le` / 定理 `eventually_pow_one_div_le`

English:
theorem eventually_pow_one_div_le
  given: {x : Real>=0∞} (hx : x != ∞) {y : Real>=0∞} (hy : 1 < y)
  proof: by
  lift x to Real>=0 using hx
  by_cases h : y = ∞
  · exact Eventually.of_forall fun n => h.symm ▸ le_top
  · lift y to Real>=0 using h
    have := NNReal.eventually_pow_one_div_le x (mod_cast hy : 1 < y)
    refine this.congr (Eventually.of_forall fun n => ?_)
    rw [← coe_rpow_of_nonneg x (by positivity : 0 <= (1 / n : Real))]; rw [coe_le_coe]

中文:
定理 eventually_pow_one_div_le
  条件: {x : 实数>=0∞} (hx : x != ∞) {y : 实数>=0∞} (hy : 1 < y)
  证明: by
  lift x to Real>=0 using hx
  by_cases h : y = ∞
  · exact Eventually.of_forall fun n => h.symm ▸ le_top
  · lift y to Real>=0 using h
    have := NNReal.eventually_pow_one_div_le x (mod_cast hy : 1 < y)
    refine this.congr (Eventually.of_forall fun n => ?_)
    rw [← coe_rpow_of_nonneg x (by positivity : 0 <= (1 / n : Real))]; rw [coe_le_coe]

Depends on / 依赖: Eventually, Eventually.of_forall, NNReal, NNReal.eventually_pow_one_div_le, coe_le_coe, coe_rpow_of_nonneg, eventually_pow_one_div_le, h.symm, le_top, mod_cast, of_forall, this.congr
-/
theorem eventually_pow_one_div_le {x : Real>=0∞} (hx : x != ∞) {y : Real>=0∞} (hy : 1 < y) :
    forallᶠ n : Nat in atTop, x ^ (1 / n : Real) <= y := by
  lift x to Real>=0 using hx
  by_cases h : y = ∞
  · exact Eventually.of_forall fun n => h.symm ▸ le_top
  · lift y to Real>=0 using h
    have := NNReal.eventually_pow_one_div_le x (mod_cast hy : 1 < y)
    refine this.congr (Eventually.of_forall fun n => ?_)
    rw [← coe_rpow_of_nonneg x (by positivity : 0 <= (1 / n : Real))]; rw [coe_le_coe]

/--
theorem `continuousAt_rpow_const_of_pos` / 定理 `continuousAt_rpow_const_of_pos`

English:
theorem continuousAt_rpow_const_of_pos
  given: {x : Real>=0∞} {y : Real} (h : 0 < y)
  proof: by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert! ENNReal.tendsto_rpow_at_top h
    simp [h]
  lift x to Real>=0 using hx
  rw [continuousAt_coe_iff]
  convert! continuous_coe.continuousAt.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [← coe_rpow_of_nonneg _ h.le]

@[continuity, fun_prop]

中文:
定理 continuousAt_rpow_const_of_pos
  条件: {x : 实数>=0∞} {y : 实数} (h : 0 < y)
  证明: by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert! ENNReal.tendsto_rpow_at_top h
    simp [h]
  lift x to Real>=0 using hx
  rw [continuousAt_coe_iff]
  convert! continuous_coe.continuousAt.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [← coe_rpow_of_nonneg _ h.le]

@[continuity, fun_prop]
-/
private theorem continuousAt_rpow_const_of_pos {x : Real>=0∞} {y : Real} (h : 0 < y) :
    ContinuousAt (fun a : Real>=0∞ => a ^ y) x := by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert! ENNReal.tendsto_rpow_at_top h
    simp [h]
  lift x to Real>=0 using hx
  rw [continuousAt_coe_iff]
  convert! continuous_coe.continuousAt.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [← coe_rpow_of_nonneg _ h.le]

@[continuity, fun_prop]
/--
theorem `continuous_rpow_const` / 定理 `continuous_rpow_const`

English:
theorem continuous_rpow_const
  given: {y : Real}
  statement: Continuous fun a : Real>=0∞ => a ^ y
  proof: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy (0 : Real) y with (hy | rfl | hy)
  · exact continuousAt_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : exists z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuousAt.comp (continuousAt_rpow_const_of_pos z_pos)

中文:
定理 continuous_rpow_const
  条件: {y : 实数}
  结论: 连续 fun a : 实数>=0∞ => a ^ y
  证明: by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy (0 : Real) y with (hy | rfl | hy)
  · exact continuousAt_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : exists z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuousAt.comp (continuousAt_rpow_const_of_pos z_pos)

Depends on / 依赖: continuousAt, continuousAt_const, continuousAt_rpow_const_of_pos, continuous_iff_continuousAt, continuous_inv, continuous_inv.continuousAt.comp, lt_trichotomy, neg_neg, rpow_neg, rpow_zero, simp_rw, z_pos
-/
theorem continuous_rpow_const {y : Real} : Continuous fun a : Real>=0∞ => a ^ y := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy (0 : Real) y with (hy | rfl | hy)
  · exact continuousAt_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : exists z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuousAt.comp (continuousAt_rpow_const_of_pos z_pos)

/--
theorem `tendsto_const_mul_rpow_nhds_zero_of_pos` / 定理 `tendsto_const_mul_rpow_nhds_zero_of_pos`

English:
theorem tendsto_const_mul_rpow_nhds_zero_of_pos
  given: {c : Real>=0∞} (hc : c != ∞) {y : Real} (hy : 0 < y)
  proof: by
  convert! ENNReal.Tendsto.const_mul (ENNReal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc

中文:
定理 tendsto_const_mul_rpow_nhds_zero_of_pos
  条件: {c : 实数>=0∞} (hc : c != ∞) {y : 实数} (hy : 0 < y)
  证明: by
  convert! ENNReal.Tendsto.const_mul (ENNReal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc

Depends on / 依赖: ENNReal, ENNReal.Tendsto.const_mul, ENNReal.continuous_rpow_const.tendsto, Or.inr, Tendsto, const_mul, continuous_rpow_const, convert, tendsto
-/
theorem tendsto_const_mul_rpow_nhds_zero_of_pos {c : Real>=0∞} (hc : c != ∞) {y : Real} (hy : 0 < y) :
    Tendsto (fun x : Real>=0∞ => c * x ^ y) (𝓝 0) (𝓝 0) := by
  convert! ENNReal.Tendsto.const_mul (ENNReal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc

end ENNReal

/--
theorem `Filter.Tendsto.ennrpow_const` / 定理 `Filter.Tendsto.ennrpow_const`

English:
theorem Filter.Tendsto.ennrpow_const
  statement: {α : Type*} {f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞} (r : Real)
  proof: (ENNReal.continuous_rpow_const.tendsto a).comp hm

中文:
定理 滤子.收敛.ennrpow_const
  结论: {α : 类型} {f : 滤子 α} {m : α -> 实数>=0∞} {a : 实数>=0∞} (r : 实数)
  证明: (ENNReal.continuous_rpow_const.tendsto a).comp hm

Depends on / 依赖: ENNReal, ENNReal.continuous_rpow_const.tendsto, continuous_rpow_const, tendsto
-/
theorem Filter.Tendsto.ennrpow_const {α : Type*} {f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞} (r : Real)
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r) f (𝓝 (a ^ r)) :=
  (ENNReal.continuous_rpow_const.tendsto a).comp hm
