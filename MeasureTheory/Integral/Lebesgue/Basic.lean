/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.Algebra.Order.Pi

/-!
# Lower Lebesgue integral for `ℝ≥0∞`-valued functions

We define the lower Lebesgue integral of an `ℝ≥0∞`-valued function.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.
-/

@[expose] public section

assert_not_exists Module.Basis Norm MeasureTheory.MeasurePreserving MeasureTheory.Measure.dirac

open Set hiding restrict restrict_apply

open Filter ENNReal Topology NNReal

namespace MeasureTheory

local infixr:25 " ->ₛ " => SimpleFunc

variable {α β γ : Type*}

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
noncomputable irreducible_def lintegral (μ : Measure α) (f : α -> Real>=0∞) : Real>=0∞ :=
  ⨆ (g : α ->ₛ Real>=0∞) (_ : ⇑g <= f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => lintegral μ r

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => lintegral volume f) => r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => lintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => lintegral (Measure.restrict volume s) f) => r

/--
theorem `SimpleFunc.lintegral_eq_lintegral` / 定理 `SimpleFunc.lintegral_eq_lintegral`

English:
theorem SimpleFunc.lintegral_eq_lintegral
  given: {m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (μ : Measure α)
  proof: by
  rw [MeasureTheory.lintegral]
  exact le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[gcongr, mono]

中文:
定理 SimpleFunc.lintegral_eq_lintegral
  条件: {m : 可测空间 α} (f : α ->ₛ 实数>=0∞) (μ : 测度 α)
  证明: by
  rw [MeasureTheory.lintegral]
  exact le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[gcongr, mono]

Depends on / 依赖: MeasureTheory, MeasureTheory.lintegral, le_antisymm, le_rfl, lintegral, lintegral_mono
-/
theorem SimpleFunc.lintegral_eq_lintegral {m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ = f.lintegral μ := by
  rw [MeasureTheory.lintegral]
  exact le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[gcongr, mono]
/--
theorem `lintegral_mono'` / 定理 `lintegral_mono'`

English:
theorem lintegral_mono'
  given: {m : MeasurableSpace α} ⦃μ ν
  statement: Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄
  proof: by
  rw [lintegral]; rw [lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

中文:
定理 lintegral_mono'
  条件: {m : 可测空间 α} ⦃μ ν
  结论: 测度 α⦄ (hμν : μ <= ν) ⦃f g : α -> 实数>=0∞⦄
  证明: by
  rw [lintegral]; rw [lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

Depends on / 依赖: iSup_mono, le_refl, le_trans, lintegral, lintegral_mono
-/
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄
    (hfg : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂ν := by
  rw [lintegral]; rw [lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

-- version where `hfg` is an explicit forall, so that `@[gcongr]` can recognize it
/--
theorem `lintegral_mono_fn'` / 定理 `lintegral_mono_fn'`

English:
theorem lintegral_mono_fn'
  given: (h2 : μ <= ν) ⦃f g
  statement: α -> Real>=0∞⦄ (hfg : forall x, f x <= g x) :
  proof: lintegral_mono' h2 hfg

中文:
定理 lintegral_mono_fn'
  条件: (h2 : μ <= ν) ⦃f g
  结论: α -> 实数>=0∞⦄ (hfg : 对任意 x, f x <= g x) :
  证明: lintegral_mono' h2 hfg
-/
@[gcongr] theorem lintegral_mono_fn' (h2 : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : forall x, f x <= g x) :
    ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂ν :=
  lintegral_mono' h2 hfg

/--
theorem `lintegral_mono` / 定理 `lintegral_mono`

English:
theorem lintegral_mono
  given: ⦃f g
  statement: α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
  proof: lintegral_mono' (le_refl μ) hfg

中文:
定理 lintegral_mono
  条件: ⦃f g
  结论: α -> 实数>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
  证明: lintegral_mono' (le_refl μ) hfg

Depends on / 依赖: le_refl, lintegral_mono
-/
theorem lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg

/--
theorem `lintegral_mono_nnreal` / 定理 `lintegral_mono_nnreal`

English:
theorem lintegral_mono_nnreal
  given: {f g : α -> Real>=0} (h : f <= g)
  statement: ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
  proof: lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)

中文:
定理 lintegral_mono_nnreal
  条件: {f g : α -> 实数>=0} (h : f <= g)
  结论: ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
  证明: lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, lintegral_mono
-/
theorem lintegral_mono_nnreal {f g : α -> Real>=0} (h : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)

/--
theorem `iSup_lintegral_measurable_le_eq_lintegral` / 定理 `iSup_lintegral_measurable_le_eq_lintegral`

English:
theorem iSup_lintegral_measurable_le_eq_lintegral
  given: (f : α -> Real>=0∞)
  proof: by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
refine iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable le_iSup_of_le hi ?_
    exact le_of_eq (i.lintegral_eq_lintegral _).symm

中文:
定理 iSup_lintegral_measurable_le_eq_lintegral
  条件: (f : α -> 实数>=0∞)
  证明: by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
refine iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable le_iSup_of_le hi ?_
    exact le_of_eq (i.lintegral_eq_lintegral _).symm

Depends on / 依赖: i.lintegral_eq_lintegral, i.measurable, iSup_le, le_antisymm, le_iSup_of_le, le_of_eq, lintegral, lintegral_eq_lintegral, lintegral_mono, measurable
-/
theorem iSup_lintegral_measurable_le_eq_lintegral (f : α -> Real>=0∞) :
    ⨆ (g : α -> Real>=0∞) (_ : Measurable g) (_ : g <= f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
refine iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable le_iSup_of_le hi ?_
    exact le_of_eq (i.lintegral_eq_lintegral _).symm

/--
theorem `lintegral_mono_set` / 定理 `lintegral_mono_set`

English:
theorem lintegral_mono_set
  given: {_ : MeasurableSpace α} ⦃μ
  statement: Measure α⦄ {s t : Set α} {f : α -> Real>=0∞}
  proof: lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)

中文:
定理 lintegral_mono_set
  条件: {_ : 可测空间 α} ⦃μ
  结论: 测度 α⦄ {s t : 集合 α} {f : α -> 实数>=0∞}
  证明: lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)

Depends on / 依赖: Measure, Measure.restrict_mono, le_refl, lintegral_mono, restrict_mono
-/
theorem lintegral_mono_set {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α -> Real>=0∞}
    (hst : s subseteq t) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)

/--
theorem `lintegral_mono_set'` / 定理 `lintegral_mono_set'`

English:
theorem lintegral_mono_set'
  given: {_ : MeasurableSpace α} ⦃μ
  statement: Measure α⦄ {s t : Set α} {f : α -> Real>=0∞}
  proof: lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)

中文:
定理 lintegral_mono_set'
  条件: {_ : 可测空间 α} ⦃μ
  结论: 测度 α⦄ {s t : 集合 α} {f : α -> 实数>=0∞}
  证明: lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)

Depends on / 依赖: Measure, Measure.restrict_mono, le_refl, lintegral_mono, restrict_mono
-/
theorem lintegral_mono_set' {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α -> Real>=0∞}
    (hst : s <=ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)

/--
theorem `monotone_lintegral` / 定理 `monotone_lintegral`

English:
theorem monotone_lintegral
  given: {_ : MeasurableSpace α} (μ : Measure α)
  statement: Monotone (lintegral μ)
  proof: lintegral_mono

@[simp]

中文:
定理 monotone_lintegral
  条件: {_ : 可测空间 α} (μ : 测度 α)
  结论: 递增 (lintegral μ)
  证明: lintegral_mono

@[simp]

Depends on / 依赖: lintegral_mono
-/
theorem monotone_lintegral {_ : MeasurableSpace α} (μ : Measure α) : Monotone (lintegral μ) :=
  lintegral_mono

@[simp]
/--
theorem `lintegral_const` / 定理 `lintegral_const`

English:
theorem lintegral_const
  given: (c : Real>=0∞)
  statement: ∫⁻ _, c ∂μ = c * μ univ
  proof: by
  rw [← SimpleFunc.const_lintegral]; rw [← SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.coe_const]
  rfl

中文:
定理 lintegral_const
  条件: (c : 实数>=0∞)
  结论: ∫⁻ _, c ∂μ = c * μ univ
  证明: by
  rw [← SimpleFunc.const_lintegral]; rw [← SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.coe_const]
  rfl

Depends on / 依赖: SimpleFunc, SimpleFunc.coe_const, SimpleFunc.const_lintegral, SimpleFunc.lintegral_eq_lintegral, coe_const, const_lintegral, lintegral_eq_lintegral
-/
theorem lintegral_const (c : Real>=0∞) : ∫⁻ _, c ∂μ = c * μ univ := by
  rw [← SimpleFunc.const_lintegral]; rw [← SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.coe_const]
  rfl

/--
theorem `lintegral_zero` / 定理 `lintegral_zero`

English:
theorem lintegral_zero
  statement: ∫⁻ _ : α, 0 ∂μ = 0
  proof: by simp

中文:
定理 lintegral_zero
  结论: ∫⁻ _ : α, 0 ∂μ = 0
  证明: by simp
-/
theorem lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0 := by simp

/--
theorem `lintegral_zero_fun` / 定理 `lintegral_zero_fun`

English:
theorem lintegral_zero_fun
  statement: lintegral μ (0 : α -> Real>=0∞) = 0
  proof: lintegral_zero

中文:
定理 lintegral_zero_fun
  结论: lintegral μ (0 : α -> 实数>=0∞) = 0
  证明: lintegral_zero

Depends on / 依赖: lintegral_zero
-/
theorem lintegral_zero_fun : lintegral μ (0 : α -> Real>=0∞) = 0 :=
  lintegral_zero

/--
theorem `lintegral_one` / 定理 `lintegral_one`

English:
theorem lintegral_one
  statement: ∫⁻ _, (1 : Real>=0∞) ∂μ = μ univ
  proof: by rw [lintegral_const, one_mul]

中文:
定理 lintegral_one
  结论: ∫⁻ _, (1 : 实数>=0∞) ∂μ = μ univ
  证明: by rw [lintegral_const, one_mul]

Depends on / 依赖: lintegral_const, one_mul
-/
theorem lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ univ := by rw [lintegral_const, one_mul]

/--
theorem `setLIntegral_const` / 定理 `setLIntegral_const`

English:
theorem setLIntegral_const
  given: (s : Set α) (c : Real>=0∞)
  statement: ∫⁻ _ in s, c ∂μ = c * μ s
  proof: by
  rw [lintegral_const]; rw [Measure.restrict_apply_univ]

中文:
定理 setL整数egral_const
  条件: (s : 集合 α) (c : 实数>=0∞)
  结论: ∫⁻ _ in s, c ∂μ = c * μ s
  证明: by
  rw [lintegral_const]; rw [Measure.restrict_apply_univ]

Depends on / 依赖: Measure, Measure.restrict_apply_univ, lintegral_const, restrict_apply_univ
-/
theorem setLIntegral_const (s : Set α) (c : Real>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by
  rw [lintegral_const]; rw [Measure.restrict_apply_univ]

/--
theorem `setLIntegral_one` / 定理 `setLIntegral_one`

English:
theorem setLIntegral_one
  given: (s)
  statement: ∫⁻ _ in s, 1 ∂μ = μ s
  proof: by rw [setLIntegral_const, one_mul]

中文:
定理 setL整数egral_one
  条件: (s)
  结论: ∫⁻ _ in s, 1 ∂μ = μ s
  证明: by rw [setLIntegral_const, one_mul]

Depends on / 依赖: one_mul, setLIntegral_const
-/
theorem setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s := by rw [setLIntegral_const, one_mul]

/--
lemma `iInf_mul_le_lintegral` / 引理 `iInf_mul_le_lintegral`

English:
lemma iInf_mul_le_lintegral
  given: (f : α -> Real>=0∞)
  statement: (⨅ x, f x) * μ .univ <= ∫⁻ x, f x ∂μ
  proof: by
  calc (⨅ x, f x) * μ .univ
  _ = ∫⁻ y, ⨅ x, f x ∂μ := by simp
  _ <= ∫⁻ x, f x ∂μ := by gcongr; exact iInf_le _ _

中文:
引理 iInf_mul_le_lintegral
  条件: (f : α -> 实数>=0∞)
  结论: (⨅ x, f x) * μ .univ <= ∫⁻ x, f x ∂μ
  证明: by
  calc (⨅ x, f x) * μ .univ
  _ = ∫⁻ y, ⨅ x, f x ∂μ := by simp
  _ <= ∫⁻ x, f x ∂μ := by gcongr; exact iInf_le _ _

Depends on / 依赖: iInf_le
-/
lemma iInf_mul_le_lintegral (f : α -> Real>=0∞) : (⨅ x, f x) * μ .univ <= ∫⁻ x, f x ∂μ := by
  calc (⨅ x, f x) * μ .univ
  _ = ∫⁻ y, ⨅ x, f x ∂μ := by simp
  _ <= ∫⁻ x, f x ∂μ := by gcongr; exact iInf_le _ _

/--
lemma `lintegral_le_iSup_mul` / 引理 `lintegral_le_iSup_mul`

English:
lemma lintegral_le_iSup_mul
  given: (f : α -> Real>=0∞)
  statement: ∫⁻ x, f x ∂μ <= (⨆ x, f x) * μ .univ
  proof: by
  calc ∫⁻ x, f x ∂μ
  _ <= ∫⁻ y, ⨆ x, f x ∂μ := by gcongr; exact le_iSup _ _
  _ = (⨆ x, f x) * μ .univ := by simp

中文:
引理 lintegral_le_iSup_mul
  条件: (f : α -> 实数>=0∞)
  结论: ∫⁻ x, f x ∂μ <= (⨆ x, f x) * μ .univ
  证明: by
  calc ∫⁻ x, f x ∂μ
  _ <= ∫⁻ y, ⨆ x, f x ∂μ := by gcongr; exact le_iSup _ _
  _ = (⨆ x, f x) * μ .univ := by simp

Depends on / 依赖: le_iSup
-/
lemma lintegral_le_iSup_mul (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ <= (⨆ x, f x) * μ .univ := by
  calc ∫⁻ x, f x ∂μ
  _ <= ∫⁻ y, ⨆ x, f x ∂μ := by gcongr; exact le_iSup _ _
  _ = (⨆ x, f x) * μ .univ := by simp

variable (μ) in
/--
theorem `exists_measurable_le_lintegral_eq` / 定理 `exists_measurable_le_lintegral_eq`

English:
theorem exists_measurable_le_lintegral_eq
  given: (f : α -> Real>=0∞)
  proof: by
  rcases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ | h₀
  · exact ⟨0, measurable_zero, zero_le, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  have : forall n, exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using this
  refine
    ⟨fun x => ⨆ n, g n x, .iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm ?_ ?_⟩
· refine le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans lintegral_mono fun x => ?_
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x

中文:
定理 存在_measurable_le_lintegral_eq
  条件: (f : α -> 实数>=0∞)
  证明: by
  rcases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ | h₀
  · exact ⟨0, measurable_zero, zero_le, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  have : forall n, exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using this
  refine
    ⟨fun x => ⨆ n, g n x, .iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm ?_ ?_⟩
· refine le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans lintegral_mono fun x => ?_
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x

Depends on / 依赖: Measurable, bot_lt, eq_or_ne, exists_prop, exists_seq_strictMono_tendsto, hL_tendsto, iSup_le, iSup_lintegral_measurable_le_eq_lintegral, lintegral_zero, lintegral_zero.symm, lt_iSup_iff, measurable_zero, zero_le
-/
theorem exists_measurable_le_lintegral_eq (f : α -> Real>=0∞) :
    exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  rcases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ | h₀
  · exact ⟨0, measurable_zero, zero_le, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  have : forall n, exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using this
  refine
    ⟨fun x => ⨆ n, g n x, .iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm ?_ ?_⟩
· refine le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans lintegral_mono fun x => ?_
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x

/--
theorem `lintegral_eq_nnreal` / 定理 `lintegral_eq_nnreal`

English:
theorem lintegral_eq_nnreal
  given: {m : MeasurableSpace α} (f : α -> Real>=0∞) (μ : Measure α)
  proof: by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun φ hφ => ?_) (iSup_mono' fun φ => ⟨φ.map ((↑) : Real>=0 -> Real>=0∞), le_rfl⟩)
  by_cases h : forallᵐ a ∂μ, φ a != ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map ((↑) : Real>=0 -> Real>=0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : forall x, ↑(ψ x) <= f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact le_iSup₂_of_le (φ.map ENNReal.toNNReal) this (ge_of_eq <| lintegral_congr h)
  · have h_meas : μ (φ ⁻¹' {∞}) != 0 := mt measure_eq_zero_iff_ae_notMem.1 h
    refine le_trans le_top (ge_of_eq <| iSup_eq_top.2 fun b hb => ?_)
    obtain ⟨n, hn⟩ : exists n : Nat, b < n * μ (φ ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : Real>=0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_natCast,
      restrict_const_lintegral]
    refine ⟨indicator_le fun x hx => le_trans ?_ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]

中文:
定理 lintegral_eq_nnreal
  条件: {m : 可测空间 α} (f : α -> 实数>=0∞) (μ : 测度 α)
  证明: by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun φ hφ => ?_) (iSup_mono' fun φ => ⟨φ.map ((↑) : Real>=0 -> Real>=0∞), le_rfl⟩)
  by_cases h : forallᵐ a ∂μ, φ a != ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map ((↑) : Real>=0 -> Real>=0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : forall x, ↑(ψ x) <= f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact le_iSup₂_of_le (φ.map ENNReal.toNNReal) this (ge_of_eq <| lintegral_congr h)
  · have h_meas : μ (φ ⁻¹' {∞}) != 0 := mt measure_eq_zero_iff_ae_notMem.1 h
    refine le_trans le_top (ge_of_eq <| iSup_eq_top.2 fun b hb => ?_)
    obtain ⟨n, hn⟩ : exists n : Nat, b < n * μ (φ ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : Real>=0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_natCast,
      restrict_const_lintegral]
    refine ⟨indicator_le fun x hx => le_trans ?_ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, ENNReal.coe_toNNReal_le_self, ENNReal.toNNReal, coe_toNNReal, coe_toNNReal_le_self, ge_of_eq, h.mono, h_meas, iSup_mono, le_antisymm, le_rfl, le_trans, lintegral, lintegral_congr, replace, toNNReal
-/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α -> Real>=0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ =
      ⨆ (φ : α ->ₛ Real>=0) (_ : forall x, ↑(φ x) <= f x), (φ.map ((↑) : Real>=0 -> Real>=0∞)).lintegral μ := by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun φ hφ => ?_) (iSup_mono' fun φ => ⟨φ.map ((↑) : Real>=0 -> Real>=0∞), le_rfl⟩)
  by_cases h : forallᵐ a ∂μ, φ a != ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map ((↑) : Real>=0 -> Real>=0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : forall x, ↑(ψ x) <= f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact le_iSup₂_of_le (φ.map ENNReal.toNNReal) this (ge_of_eq <| lintegral_congr h)
  · have h_meas : μ (φ ⁻¹' {∞}) != 0 := mt measure_eq_zero_iff_ae_notMem.1 h
    refine le_trans le_top (ge_of_eq <| iSup_eq_top.2 fun b hb => ?_)
    obtain ⟨n, hn⟩ : exists n : Nat, b < n * μ (φ ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : Real>=0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_natCast,
      restrict_const_lintegral]
    refine ⟨indicator_le fun x hx => le_trans ?_ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]

/--
theorem `exists_simpleFunc_forall_lintegral_sub_lt_of_pos` / 定理 `exists_simpleFunc_forall_lintegral_sub_lt_of_pos`

English:
theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos
  statement: {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞)
  proof: by
  rw [lintegral_eq_nnreal] at h
  have := ENNReal.lt_add_right h hε
  erw [ENNReal.biSup_add] at this <;> [skip; exact ⟨0, fun x => zero_le⟩]
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  rcases this with ⟨φ, hle : forall x, ↑(φ x) <= f x, b, hbφ, hb⟩
  refine ⟨φ, hle, fun ψ hψ => ?_⟩
  have : (map (↑) φ).lintegral μ != ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := Real>=0∞) φ hle)
  rw [← ENNReal.add_lt_add_iff_left this]; rw [← add_lintegral]; rw [← SimpleFunc.map_add @ENNReal.coe_add]
  refine (hb _ fun x => le_trans ?_ (max_le (hle x) (hψ x))).trans_lt hbφ
  simp only [SimpleFunc.add_apply, SimpleFunc.sub_apply, add_tsub_eq_max]
  rfl

中文:
定理 存在_simpleFunc_对任意_lintegral_sub_lt_of_pos
  结论: {f : α -> 实数>=0∞} (h : ∫⁻ x, f x ∂μ != ∞)
  证明: by
  rw [lintegral_eq_nnreal] at h
  have := ENNReal.lt_add_right h hε
  erw [ENNReal.biSup_add] at this <;> [skip; exact ⟨0, fun x => zero_le⟩]
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  rcases this with ⟨φ, hle : forall x, ↑(φ x) <= f x, b, hbφ, hb⟩
  refine ⟨φ, hle, fun ψ hψ => ?_⟩
  have : (map (↑) φ).lintegral μ != ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := Real>=0∞) φ hle)
  rw [← ENNReal.add_lt_add_iff_left this]; rw [← add_lintegral]; rw [← SimpleFunc.map_add @ENNReal.coe_add]
  refine (hb _ fun x => le_trans ?_ (max_le (hle x) (hψ x))).trans_lt hbφ
  simp only [SimpleFunc.add_apply, SimpleFunc.sub_apply, add_tsub_eq_max]
  rfl

Depends on / 依赖: ENNReal, ENNReal.add_lt_add_iff_left, ENNReal.biSup_add, ENNReal.coe_add, ENNReal.lt_add_right, SimpleFunc, SimpleFunc.map_add, add_lintegral, add_lt_add_iff_left, biSup_add, coe_add, iSup_le_iff, iSup_lt_iff, lintegral, lintegral_eq_nnreal, lt_add_right, lt_iSup_iff, map_add, ne_top_of_le_ne_top, simp_rw
-/
theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞)
    {ε : Real>=0∞} (hε : ε != 0) :
    exists φ : α ->ₛ Real>=0,
      (forall x, ↑(φ x) <= f x) ∧
        forall ψ : α ->ₛ Real>=0, (forall x, ↑(ψ x) <= f x) -> (map (↑) (ψ - φ)).lintegral μ < ε := by
  rw [lintegral_eq_nnreal] at h
  have := ENNReal.lt_add_right h hε
  erw [ENNReal.biSup_add] at this <;> [skip; exact ⟨0, fun x => zero_le⟩]
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  rcases this with ⟨φ, hle : forall x, ↑(φ x) <= f x, b, hbφ, hb⟩
  refine ⟨φ, hle, fun ψ hψ => ?_⟩
  have : (map (↑) φ).lintegral μ != ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := Real>=0∞) φ hle)
  rw [← ENNReal.add_lt_add_iff_left this]; rw [← add_lintegral]; rw [← SimpleFunc.map_add @ENNReal.coe_add]
  refine (hb _ fun x => le_trans ?_ (max_le (hle x) (hψ x))).trans_lt hbφ
  simp only [SimpleFunc.add_apply, SimpleFunc.sub_apply, add_tsub_eq_max]
  rfl

/--
theorem `iSup_lintegral_le` / 定理 `iSup_lintegral_le`

English:
theorem iSup_lintegral_le
  given: {ι : Sort*} (f : ι -> α -> Real>=0∞)
  proof: by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup

中文:
定理 iSup_lintegral_le
  条件: {ι : 类型层*} (f : ι -> α -> 实数>=0∞)
  证明: by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup

Depends on / 依赖: iSup_apply, le_map_iSup, monotone_lintegral
-/
theorem iSup_lintegral_le {ι : Sort*} (f : ι -> α -> Real>=0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ <= ∫⁻ a, ⨆ i, f i a ∂μ := by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup

/--
theorem `iSup₂_lintegral_le` / 定理 `iSup₂_lintegral_le`

English:
theorem iSup₂_lintegral_le
  given: {ι : Sort*} {ι' : ι -> Sort*} (f : forall i, ι' i -> α -> Real>=0∞)
  proof: by
  convert! (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]

中文:
定理 iSup₂_lintegral_le
  条件: {ι : 类型层*} {ι' : ι -> 类型层*} (f : 对任意 i, ι' i -> α -> 实数>=0∞)
  证明: by
  convert! (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]

Depends on / 依赖: convert, iSup_apply, monotone_lintegral
-/
theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι -> Sort*} (f : forall i, ι' i -> α -> Real>=0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ <= ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by
  convert! (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]

/--
theorem `le_iInf_lintegral` / 定理 `le_iInf_lintegral`

English:
theorem le_iInf_lintegral
  given: {ι : Sort*} (f : ι -> α -> Real>=0∞)
  proof: by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le

中文:
定理 le_iInf_lintegral
  条件: {ι : 类型层*} (f : ι -> α -> 实数>=0∞)
  证明: by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le

Depends on / 依赖: iInf_apply, map_iInf_le, monotone_lintegral
-/
theorem le_iInf_lintegral {ι : Sort*} (f : ι -> α -> Real>=0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ <= ⨅ i, ∫⁻ a, f i a ∂μ := by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le

/--
theorem `le_iInf₂_lintegral` / 定理 `le_iInf₂_lintegral`

English:
theorem le_iInf₂_lintegral
  given: {ι : Sort*} {ι' : ι -> Sort*} (f : forall i, ι' i -> α -> Real>=0∞)
  proof: by
  convert! (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]

中文:
定理 le_iInf₂_lintegral
  条件: {ι : 类型层*} {ι' : ι -> 类型层*} (f : 对任意 i, ι' i -> α -> 实数>=0∞)
  证明: by
  convert! (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]

Depends on / 依赖: convert, iInf_apply, monotone_lintegral
-/
theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι -> Sort*} (f : forall i, ι' i -> α -> Real>=0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ <= ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by
  convert! (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]

/--
theorem `lintegral_mono_ae` / 定理 `lintegral_mono_ae`

English:
theorem lintegral_mono_ae
  given: {f g : α -> Real>=0∞} (h : forallᵐ a ∂μ, f a <= g a)
  proof: by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : forallᵐ x ∂μ, x ∉ t := measure_eq_zero_iff_ae_notMem.1 ht0
  rw [lintegral]; rw [lintegral]
  refine iSup₂_le fun s hfs => le_iSup₂_of_le (s.restrict tᶜ) ?_ ?_
  · intro a
    by_cases h : a in t <;>
      simp only [restrict_apply s ht.compl, mem_compl_iff, h, not_true, not_false_eq_true,
        indicator_of_notMem, zero_le, not_false_eq_true, indicator_of_mem]
    exact le_trans (hfs a) (by_contradiction fun hnfg => h (hts hnfg))
· exact le_of_eq SimpleFunc.lintegral_congr this.mono fun a hnt => by
      simp [restrict_apply s ht.compl, hnt]

中文:
定理 lintegral_mono_ae
  条件: {f g : α -> 实数>=0∞} (h : 对任意ᵐ a ∂μ, f a <= g a)
  证明: by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : forallᵐ x ∂μ, x ∉ t := measure_eq_zero_iff_ae_notMem.1 ht0
  rw [lintegral]; rw [lintegral]
  refine iSup₂_le fun s hfs => le_iSup₂_of_le (s.restrict tᶜ) ?_ ?_
  · intro a
    by_cases h : a in t <;>
      simp only [restrict_apply s ht.compl, mem_compl_iff, h, not_true, not_false_eq_true,
        indicator_of_notMem, zero_le, not_false_eq_true, indicator_of_mem]
    exact le_trans (hfs a) (by_contradiction fun hnfg => h (hts hnfg))
· exact le_of_eq SimpleFunc.lintegral_congr this.mono fun a hnt => by
      simp [restrict_apply s ht.compl, hnt]

Depends on / 依赖: by_contradiction, exists_measurable_superset_of_null, ht.compl, indicator_of_mem, indicator_of_notMem, le_of_, le_trans, lintegral, measure_eq_zero_iff_ae_notMem, mem_compl_iff, not_false_eq_true, not_true, restrict, restrict_apply, s.restrict, zero_le
-/
theorem lintegral_mono_ae {f g : α -> Real>=0∞} (h : forallᵐ a ∂μ, f a <= g a) :
    ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : forallᵐ x ∂μ, x ∉ t := measure_eq_zero_iff_ae_notMem.1 ht0
  rw [lintegral]; rw [lintegral]
  refine iSup₂_le fun s hfs => le_iSup₂_of_le (s.restrict tᶜ) ?_ ?_
  · intro a
    by_cases h : a in t <;>
      simp only [restrict_apply s ht.compl, mem_compl_iff, h, not_true, not_false_eq_true,
        indicator_of_notMem, zero_le, not_false_eq_true, indicator_of_mem]
    exact le_trans (hfs a) (by_contradiction fun hnfg => h (hts hnfg))
· exact le_of_eq SimpleFunc.lintegral_congr this.mono fun a hnt => by
      simp [restrict_apply s ht.compl, hnt]

/--
theorem `setLIntegral_mono_ae` / 定理 `setLIntegral_mono_ae`

English:
theorem setLIntegral_mono_ae
  statement: {s : Set α} {f g : α -> Real>=0∞} (hg : AEMeasurable g (μ.restrict s))
  proof: by
  rcases exists_measurable_le_lintegral_eq (μ.restrict s) f with ⟨f', hf'm, hle, hf'⟩
  rw [hf']
  apply lintegral_mono_ae
  rw [ae_restrict_iff₀]
  · exact hfg.mono fun x hx hxs => (hle x).trans (hx hxs)
  · exact nullMeasurableSet_le hf'm.aemeasurable hg

中文:
定理 setL整数egral_mono_ae
  结论: {s : 集合 α} {f g : α -> 实数>=0∞} (hg : 几乎处处可测 g (μ.restrict s))
  证明: by
  rcases exists_measurable_le_lintegral_eq (μ.restrict s) f with ⟨f', hf'm, hle, hf'⟩
  rw [hf']
  apply lintegral_mono_ae
  rw [ae_restrict_iff₀]
  · exact hfg.mono fun x hx hxs => (hle x).trans (hx hxs)
  · exact nullMeasurableSet_le hf'm.aemeasurable hg

Depends on / 依赖: aemeasurable, exists_measurable_le_lintegral_eq, hfg.mono, lintegral_mono_ae, m.aemeasurable, nullMeasurableSet_le, restrict
-/
theorem setLIntegral_mono_ae {s : Set α} {f g : α -> Real>=0∞} (hg : AEMeasurable g (μ.restrict s))
    (hfg : forallᵐ x ∂μ, x in s -> f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s, g x ∂μ := by
  rcases exists_measurable_le_lintegral_eq (μ.restrict s) f with ⟨f', hf'm, hle, hf'⟩
  rw [hf']
  apply lintegral_mono_ae
  rw [ae_restrict_iff₀]
  · exact hfg.mono fun x hx hxs => (hle x).trans (hx hxs)
  · exact nullMeasurableSet_le hf'm.aemeasurable hg

/--
theorem `setLIntegral_mono` / 定理 `setLIntegral_mono`

English:
theorem setLIntegral_mono
  statement: {s : Set α} {f g : α -> Real>=0∞} (hg : Measurable g)
  proof: setLIntegral_mono_ae hg.aemeasurable (ae_of_all _ hfg)

中文:
定理 setL整数egral_mono
  结论: {s : 集合 α} {f g : α -> 实数>=0∞} (hg : 可测 g)
  证明: setLIntegral_mono_ae hg.aemeasurable (ae_of_all _ hfg)

Depends on / 依赖: ae_of_all, aemeasurable, hg.aemeasurable, setLIntegral_mono_ae
-/
theorem setLIntegral_mono {s : Set α} {f g : α -> Real>=0∞} (hg : Measurable g)
    (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae hg.aemeasurable (ae_of_all _ hfg)

/--
theorem `setLIntegral_mono_ae'` / 定理 `setLIntegral_mono_ae'`

English:
theorem setLIntegral_mono_ae'
  statement: {s : Set α} {f g : α -> Real>=0∞} (hs : MeasurableSet s)
  proof: lintegral_mono_ae (ae_restrict_iff' hs).2 hfg

中文:
定理 setL整数egral_mono_ae'
  结论: {s : 集合 α} {f g : α -> 实数>=0∞} (hs : 可测集 s)
  证明: lintegral_mono_ae (ae_restrict_iff' hs).2 hfg

Depends on / 依赖: ae_restrict_iff, lintegral_mono_ae
-/
theorem setLIntegral_mono_ae' {s : Set α} {f g : α -> Real>=0∞} (hs : MeasurableSet s)
    (hfg : forallᵐ x ∂μ, x in s -> f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s, g x ∂μ :=
lintegral_mono_ae (ae_restrict_iff' hs).2 hfg

/--
theorem `setLIntegral_mono'` / 定理 `setLIntegral_mono'`

English:
theorem setLIntegral_mono'
  statement: {s : Set α} {f g : α -> Real>=0∞} (hs : MeasurableSet s)
  proof: setLIntegral_mono_ae' hs (ae_of_all _ hfg)

中文:
定理 setL整数egral_mono'
  结论: {s : 集合 α} {f g : α -> 实数>=0∞} (hs : 可测集 s)
  证明: setLIntegral_mono_ae' hs (ae_of_all _ hfg)

Depends on / 依赖: ae_of_all, setLIntegral_mono_ae
-/
theorem setLIntegral_mono' {s : Set α} {f g : α -> Real>=0∞} (hs : MeasurableSet s)
    (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae' hs (ae_of_all _ hfg)

/--
theorem `setLIntegral_le_lintegral` / 定理 `setLIntegral_le_lintegral`

English:
theorem setLIntegral_le_lintegral
  given: (s : Set α) (f : α -> Real>=0∞)
  proof: lintegral_mono' Measure.restrict_le_self le_rfl

中文:
定理 setL整数egral_le_lintegral
  条件: (s : 集合 α) (f : α -> 实数>=0∞)
  证明: lintegral_mono' Measure.restrict_le_self le_rfl

Depends on / 依赖: Measure, Measure.restrict_le_self, le_rfl, lintegral_mono, restrict_le_self
-/
theorem setLIntegral_le_lintegral (s : Set α) (f : α -> Real>=0∞) :
    ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ :=
  lintegral_mono' Measure.restrict_le_self le_rfl

/--
lemma `iInf_mul_le_setLIntegral` / 引理 `iInf_mul_le_setLIntegral`

English:
lemma iInf_mul_le_setLIntegral
  given: (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s)
  proof: by
  calc (⨅ x in s, f x) * μ s
  _ = ∫⁻ y in s, ⨅ x in s, f x ∂μ := by simp
  _ <= ∫⁻ x in s, f x ∂μ := setLIntegral_mono' hs fun x hx => iInf₂_le x hx

中文:
引理 iInf_mul_le_setL整数egral
  条件: (f : α -> 实数>=0∞) {s : 集合 α} (hs : 可测集 s)
  证明: by
  calc (⨅ x in s, f x) * μ s
  _ = ∫⁻ y in s, ⨅ x in s, f x ∂μ := by simp
  _ <= ∫⁻ x in s, f x ∂μ := setLIntegral_mono' hs fun x hx => iInf₂_le x hx

Depends on / 依赖: setLIntegral_mono
-/
lemma iInf_mul_le_setLIntegral (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s) :
    (⨅ x in s, f x) * μ s <= ∫⁻ x in s, f x ∂μ := by
  calc (⨅ x in s, f x) * μ s
  _ = ∫⁻ y in s, ⨅ x in s, f x ∂μ := by simp
  _ <= ∫⁻ x in s, f x ∂μ := setLIntegral_mono' hs fun x hx => iInf₂_le x hx

/--
lemma `setLIntegral_le_iSup_mul` / 引理 `setLIntegral_le_iSup_mul`

English:
lemma setLIntegral_le_iSup_mul
  given: (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s)
  proof: by
  calc ∫⁻ x in s, f x ∂μ
  _ <= ∫⁻ y in s, ⨆ x in s, f x ∂μ :=
    setLIntegral_mono' hs fun x hx => le_iSup₂ (f := fun x _ => f x) x hx
  _ = (⨆ x in s, f x) * μ s := by simp

中文:
引理 setL整数egral_le_iSup_mul
  条件: (f : α -> 实数>=0∞) {s : 集合 α} (hs : 可测集 s)
  证明: by
  calc ∫⁻ x in s, f x ∂μ
  _ <= ∫⁻ y in s, ⨆ x in s, f x ∂μ :=
    setLIntegral_mono' hs fun x hx => le_iSup₂ (f := fun x _ => f x) x hx
  _ = (⨆ x in s, f x) * μ s := by simp

Depends on / 依赖: setLIntegral_mono
-/
lemma setLIntegral_le_iSup_mul (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, f x ∂μ <= (⨆ x in s, f x) * μ s := by
  calc ∫⁻ x in s, f x ∂μ
  _ <= ∫⁻ y in s, ⨆ x in s, f x ∂μ :=
    setLIntegral_mono' hs fun x hx => le_iSup₂ (f := fun x _ => f x) x hx
  _ = (⨆ x in s, f x) * μ s := by simp

/--
theorem `lintegral_congr_ae` / 定理 `lintegral_congr_ae`

English:
theorem lintegral_congr_ae
  given: {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g)
  statement: ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
  proof: le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)

中文:
定理 lintegral_congr_ae
  条件: {f g : α -> 实数>=0∞} (h : f =ᵐ[μ] g)
  结论: ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
  证明: le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)

Depends on / 依赖: h.le, h.symm.le, le_antisymm, lintegral_mono_ae
-/
theorem lintegral_congr_ae {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)

/--
theorem `lintegral_congr` / 定理 `lintegral_congr`

English:
theorem lintegral_congr
  given: {f g : α -> Real>=0∞} (h : forall a, f a = g a)
  statement: ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
  proof: by
  simp only [h]

中文:
定理 lintegral_congr
  条件: {f g : α -> 实数>=0∞} (h : 对任意 a, f a = g a)
  结论: ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
  证明: by
  simp only [h]
-/
theorem lintegral_congr {f g : α -> Real>=0∞} (h : forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  simp only [h]

/--
theorem `setLIntegral_congr` / 定理 `setLIntegral_congr`

English:
theorem setLIntegral_congr
  given: {f : α -> Real>=0∞} {s t : Set α} (h : s =ᵐ[μ] t)
  proof: by rw [Measure.restrict_congr_set h]

中文:
定理 setL整数egral_congr
  条件: {f : α -> 实数>=0∞} {s t : 集合 α} (h : s =ᵐ[μ] t)
  证明: by rw [Measure.restrict_congr_set h]

Depends on / 依赖: Measure, Measure.restrict_congr_set, restrict_congr_set
-/
theorem setLIntegral_congr {f : α -> Real>=0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by rw [Measure.restrict_congr_set h]

/--
theorem `setLIntegral_congr_fun_ae` / 定理 `setLIntegral_congr_fun_ae`

English:
theorem setLIntegral_congr_fun_ae
  statement: {f g : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [lintegral_congr_ae]
  rw [EventuallyEq]
  rwa [ae_restrict_iff' hs]

中文:
定理 setL整数egral_congr_fun_ae
  结论: {f g : α -> 实数>=0∞} {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [lintegral_congr_ae]
  rw [EventuallyEq]
  rwa [ae_restrict_iff' hs]

Depends on / 依赖: EventuallyEq, ae_restrict_iff, lintegral_congr_ae
-/
theorem setLIntegral_congr_fun_ae {f g : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : forallᵐ x ∂μ, x in s -> f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  rw [lintegral_congr_ae]
  rw [EventuallyEq]
  rwa [ae_restrict_iff' hs]

/--
theorem `setLIntegral_congr_fun` / 定理 `setLIntegral_congr_fun`

English:
theorem setLIntegral_congr_fun
  statement: {f g : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s)
  proof: setLIntegral_congr_fun_ae hs Eventually.of_forall hfg

中文:
定理 setL整数egral_congr_fun
  结论: {f g : α -> 实数>=0∞} {s : 集合 α} (hs : 可测集 s)
  证明: setLIntegral_congr_fun_ae hs Eventually.of_forall hfg

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, setLIntegral_congr_fun_ae
-/
theorem setLIntegral_congr_fun {f g : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : EqOn f g s) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
setLIntegral_congr_fun_ae hs Eventually.of_forall hfg

/--
lemma `setLIntegral_eq_zero` / 引理 `setLIntegral_eq_zero`

English:
lemma setLIntegral_eq_zero
  given: {f : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (h's : EqOn f 0 s)
  proof: by
  simp [setLIntegral_congr_fun hs h's]

中文:
引理 setL整数egral_eq_zero
  条件: {f : α -> 实数>=0∞} {s : 集合 α} (hs : 可测集 s) (h's : EqOn f 0 s)
  证明: by
  simp [setLIntegral_congr_fun hs h's]

Depends on / 依赖: setLIntegral_congr_fun
-/
lemma setLIntegral_eq_zero {f : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (h's : EqOn f 0 s) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  simp [setLIntegral_congr_fun hs h's]

section

/--
theorem `lintegral_eq_zero_of_ae_eq_zero` / 定理 `lintegral_eq_zero_of_ae_eq_zero`

English:
theorem lintegral_eq_zero_of_ae_eq_zero
  given: {f : α -> Real>=0∞} (h : f =ᵐ[μ] 0)
  proof: (lintegral_congr_ae h).trans lintegral_zero

中文:
定理 lintegral_eq_zero_of_ae_eq_zero
  条件: {f : α -> 实数>=0∞} (h : f =ᵐ[μ] 0)
  证明: (lintegral_congr_ae h).trans lintegral_zero

Depends on / 依赖: lintegral_congr_ae, lintegral_zero
-/
theorem lintegral_eq_zero_of_ae_eq_zero {f : α -> Real>=0∞} (h : f =ᵐ[μ] 0) :
    ∫⁻ a, f a ∂μ = 0 :=
  (lintegral_congr_ae h).trans lintegral_zero

/-- The Lebesgue integral is zero iff the function is a.e. zero.

The measurability assumption is necessary, otherwise there are counterexamples: for instance, the
conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
/--
theorem `lintegral_eq_zero_iff'` / 定理 `lintegral_eq_zero_iff'`

English:
theorem lintegral_eq_zero_iff'
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  -- The proof implicitly uses Markov's inequality,
  -- but it has been inlined for the sake of imports
  refine ⟨fun h => ?_, lintegral_eq_zero_of_ae_eq_zero⟩
  have meas_levels_0 : forall ε > 0, μ { x | ε <= f x } = 0 := fun ε εpos => by
    by_contra! h'
    refine ((ENNReal.mul_pos εpos.ne' h').trans_le ?_).ne' h
    calc
      _ >= ∫⁻ a in {x | ε <= f x}, f a ∂μ := setLIntegral_le_lintegral _ _
      _ >= ∫⁻ _ in {x | ε <= f x}, ε ∂μ :=
        setLIntegral_mono_ae hf.restrict (ae_of_all μ fun _ => id)
      _ = _ := setLIntegral_const _ _
  obtain ⟨u, -, bu, tu⟩ := exists_seq_strictAnti_tendsto' (α := Real>=0∞) zero_lt_one
  have u_union : {x | f x != 0} = ⋃ n, {x | u n <= f x} := by
    ext x
    rw [mem_iUnion]; rw [mem_ofPred_eq]; rw [← pos_iff_ne_zero]
    rw [ENNReal.tendsto_atTop_zero] at tu
    constructor <;> intro h'
    · obtain ⟨n, hn⟩ := tu _ h'; use n, hn _ le_rfl
    · obtain ⟨n, hn⟩ := h'; exact (bu n).1.trans_le hn
  have res := measure_iUnion_null_iff.mpr fun n => meas_levels_0 _ (bu n).1
  rwa [← u_union] at res

中文:
定理 lintegral_eq_zero_iff'
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  -- The proof implicitly uses Markov's inequality,
  -- but it has been inlined for the sake of imports
  refine ⟨fun h => ?_, lintegral_eq_zero_of_ae_eq_zero⟩
  have meas_levels_0 : forall ε > 0, μ { x | ε <= f x } = 0 := fun ε εpos => by
    by_contra! h'
    refine ((ENNReal.mul_pos εpos.ne' h').trans_le ?_).ne' h
    calc
      _ >= ∫⁻ a in {x | ε <= f x}, f a ∂μ := setLIntegral_le_lintegral _ _
      _ >= ∫⁻ _ in {x | ε <= f x}, ε ∂μ :=
        setLIntegral_mono_ae hf.restrict (ae_of_all μ fun _ => id)
      _ = _ := setLIntegral_const _ _
  obtain ⟨u, -, bu, tu⟩ := exists_seq_strictAnti_tendsto' (α := Real>=0∞) zero_lt_one
  have u_union : {x | f x != 0} = ⋃ n, {x | u n <= f x} := by
    ext x
    rw [mem_iUnion]; rw [mem_ofPred_eq]; rw [← pos_iff_ne_zero]
    rw [ENNReal.tendsto_atTop_zero] at tu
    constructor <;> intro h'
    · obtain ⟨n, hn⟩ := tu _ h'; use n, hn _ le_rfl
    · obtain ⟨n, hn⟩ := h'; exact (bu n).1.trans_le hn
  have res := measure_iUnion_null_iff.mpr fun n => meas_levels_0 _ (bu n).1
  rwa [← u_union] at res
-/
theorem lintegral_eq_zero_iff' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  -- The proof implicitly uses Markov's inequality,
  -- but it has been inlined for the sake of imports
  refine ⟨fun h => ?_, lintegral_eq_zero_of_ae_eq_zero⟩
  have meas_levels_0 : forall ε > 0, μ { x | ε <= f x } = 0 := fun ε εpos => by
    by_contra! h'
    refine ((ENNReal.mul_pos εpos.ne' h').trans_le ?_).ne' h
    calc
      _ >= ∫⁻ a in {x | ε <= f x}, f a ∂μ := setLIntegral_le_lintegral _ _
      _ >= ∫⁻ _ in {x | ε <= f x}, ε ∂μ :=
        setLIntegral_mono_ae hf.restrict (ae_of_all μ fun _ => id)
      _ = _ := setLIntegral_const _ _
  obtain ⟨u, -, bu, tu⟩ := exists_seq_strictAnti_tendsto' (α := Real>=0∞) zero_lt_one
  have u_union : {x | f x != 0} = ⋃ n, {x | u n <= f x} := by
    ext x
    rw [mem_iUnion]; rw [mem_ofPred_eq]; rw [← pos_iff_ne_zero]
    rw [ENNReal.tendsto_atTop_zero] at tu
    constructor <;> intro h'
    · obtain ⟨n, hn⟩ := tu _ h'; use n, hn _ le_rfl
    · obtain ⟨n, hn⟩ := h'; exact (bu n).1.trans_le hn
  have res := measure_iUnion_null_iff.mpr fun n => meas_levels_0 _ (bu n).1
  rwa [← u_union] at res

/-- The measurability assumption is necessary, otherwise there are counterexamples: for instance,
the conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
/--
theorem `lintegral_eq_zero_iff` / 定理 `lintegral_eq_zero_iff`

English:
theorem lintegral_eq_zero_iff
  given: {f : α -> Real>=0∞} (hf : Measurable f)
  statement: ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
  proof: lintegral_eq_zero_iff' hf.aemeasurable

中文:
定理 lintegral_eq_zero_iff
  条件: {f : α -> 实数>=0∞} (hf : 可测 f)
  结论: ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
  证明: lintegral_eq_zero_iff' hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, lintegral_eq_zero_iff
-/
theorem lintegral_eq_zero_iff {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.aemeasurable

/--
theorem `setLIntegral_eq_zero_iff'` / 定理 `setLIntegral_eq_zero_iff'`

English:
theorem setLIntegral_eq_zero_iff'
  statement: {s : Set α} (hs : MeasurableSet s)
  proof: (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

中文:
定理 setL整数egral_eq_zero_iff'
  结论: {s : 集合 α} (hs : 可测集 s)
  证明: (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

Depends on / 依赖: ae_restrict_iff, lintegral_eq_zero_iff
-/
theorem setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s)
    {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁻ a in s, f a ∂μ = 0 ↔ forallᵐ x ∂μ, x in s -> f x = 0 :=
  (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

/--
theorem `setLIntegral_eq_zero_iff` / 定理 `setLIntegral_eq_zero_iff`

English:
theorem setLIntegral_eq_zero_iff
  statement: {s : Set α} (hs : MeasurableSet s) {f : α -> Real>=0∞}
  proof: setLIntegral_eq_zero_iff' hs hf.aemeasurable

中文:
定理 setL整数egral_eq_zero_iff
  结论: {s : 集合 α} (hs : 可测集 s) {f : α -> 实数>=0∞}
  证明: setLIntegral_eq_zero_iff' hs hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, setLIntegral_eq_zero_iff
-/
theorem setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α -> Real>=0∞}
    (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ forallᵐ x ∂μ, x in s -> f x = 0 :=
  setLIntegral_eq_zero_iff' hs hf.aemeasurable

/--
theorem `lintegral_pos_iff_support` / 定理 `lintegral_pos_iff_support`

English:
theorem lintegral_pos_iff_support
  given: {f : α -> Real>=0∞} (hf : Measurable f)
  proof: by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]

中文:
定理 lintegral_pos_iff_support
  条件: {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Function, Function.support, ae_iff, pos_iff_ne_zero, support
-/
theorem lintegral_pos_iff_support {f : α -> Real>=0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]

/--
theorem `setLIntegral_pos_iff` / 定理 `setLIntegral_pos_iff`

English:
theorem setLIntegral_pos_iff
  given: {f : α -> Real>=0∞} (hf : Measurable f) {s : Set α}
  proof: by
  rw [lintegral_pos_iff_support hf]; rw [Measure.restrict_apply (measurableSet_support hf)]

中文:
定理 setL整数egral_pos_iff
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) {s : 集合 α}
  证明: by
  rw [lintegral_pos_iff_support hf]; rw [Measure.restrict_apply (measurableSet_support hf)]

Depends on / 依赖: Measure, Measure.restrict_apply, lintegral_pos_iff_support, measurableSet_support, restrict_apply
-/
theorem setLIntegral_pos_iff {f : α -> Real>=0∞} (hf : Measurable f) {s : Set α} :
    0 < ∫⁻ a in s, f a ∂μ ↔ 0 < μ (Function.support f inter s) := by
  rw [lintegral_pos_iff_support hf]; rw [Measure.restrict_apply (measurableSet_support hf)]

end

/--
theorem `exists_pos_setLIntegral_lt_of_measure_lt` / 定理 `exists_pos_setLIntegral_lt_of_measure_lt`

English:
theorem exists_pos_setLIntegral_lt_of_measure_lt
  statement: {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {ε : Real>=0∞}
  proof: by
  rcases exists_between (pos_iff_ne_zero.mpr hε) with ⟨ε₂, hε₂0, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine fun s hs => lt_of_le_of_lt ?_ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map (↑) ψ).lintegral (μ.restrict s) <=
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral]; rw [← SimpleFunc.map_add @ENNReal.coe_add]
      refine SimpleFunc.lintegral_mono (fun x => ?_) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, ENNReal.coe_max (φ x) (ψ x)]
    _ <= (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      refine le_trans ?_ (hφ _ hψ).le
      exact SimpleFunc.lintegral_mono le_rfl Measure.restrict_le_self
    _ <= (SimpleFunc.const α (C : Real>=0∞)).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      exact fun x => ENNReal.coe_le_coe.2 (hC x)
    _ = C * μ s + ε₁ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral, coe_const, lintegral_const,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter, Function.const]
    _ <= C * ((ε₂ - ε₁) / C) + ε₁ := by gcongr
    _ <= ε₂ - ε₁ + ε₁ := by gcongr; apply mul_div_le
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le

中文:
定理 存在_pos_setL整数egral_lt_of_measure_lt
  结论: {f : α -> 实数>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {ε : 实数>=0∞}
  证明: by
  rcases exists_between (pos_iff_ne_zero.mpr hε) with ⟨ε₂, hε₂0, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine fun s hs => lt_of_le_of_lt ?_ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map (↑) ψ).lintegral (μ.restrict s) <=
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral]; rw [← SimpleFunc.map_add @ENNReal.coe_add]
      refine SimpleFunc.lintegral_mono (fun x => ?_) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, ENNReal.coe_max (φ x) (ψ x)]
    _ <= (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      refine le_trans ?_ (hφ _ hψ).le
      exact SimpleFunc.lintegral_mono le_rfl Measure.restrict_le_self
    _ <= (SimpleFunc.const α (C : Real>=0∞)).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      exact fun x => ENNReal.coe_le_coe.2 (hC x)
    _ = C * μ s + ε₁ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral, coe_const, lintegral_const,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter, Function.const]
    _ <= C * ((ε₂ - ε₁) / C) + ε₁ := by gcongr
    _ <= ε₂ - ε₁ + ε₁ := by gcongr; apply mul_div_le
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.div_pos_iff, coe_ne_top, div_pos_iff, exists_between, exists_forall_le, exists_simpleFunc_forall_lintegral_sub_lt_of_pos, iSup_le_iff, lintegral, lintegral_eq_nnreal, lt_of_le_of_lt, pos_iff_ne_zero, pos_iff_ne_zero.mpr, restrict, tsub_pos_iff_lt
-/
theorem exists_pos_setLIntegral_lt_of_measure_lt {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {ε : Real>=0∞}
    (hε : ε != 0) : exists δ > 0, forall s, μ s < δ -> ∫⁻ x in s, f x ∂μ < ε := by
  rcases exists_between (pos_iff_ne_zero.mpr hε) with ⟨ε₂, hε₂0, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine fun s hs => lt_of_le_of_lt ?_ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map (↑) ψ).lintegral (μ.restrict s) <=
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral]; rw [← SimpleFunc.map_add @ENNReal.coe_add]
      refine SimpleFunc.lintegral_mono (fun x => ?_) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, ENNReal.coe_max (φ x) (ψ x)]
    _ <= (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      refine le_trans ?_ (hφ _ hψ).le
      exact SimpleFunc.lintegral_mono le_rfl Measure.restrict_le_self
    _ <= (SimpleFunc.const α (C : Real>=0∞)).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      exact fun x => ENNReal.coe_le_coe.2 (hC x)
    _ = C * μ s + ε₁ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral, coe_const, lintegral_const,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter, Function.const]
    _ <= C * ((ε₂ - ε₁) / C) + ε₁ := by gcongr
    _ <= ε₂ - ε₁ + ε₁ := by gcongr; apply mul_div_le
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le

/--
theorem `tendsto_setLIntegral_zero` / 定理 `tendsto_setLIntegral_zero`

English:
theorem tendsto_setLIntegral_zero
  statement: {ι} {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {l : Filter ι}
  proof: by
  simp only [ENNReal.nhds_zero, tendsto_iInf, tendsto_principal, mem_Iio,
    ← pos_iff_ne_zero] at hl ⊢
  intro ε ε0
  rcases exists_pos_setLIntegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _

@[simp]

中文:
定理 tendsto_setL整数egral_zero
  结论: {ι} {f : α -> 实数>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {l : 滤子 ι}
  证明: by
  simp only [ENNReal.nhds_zero, tendsto_iInf, tendsto_principal, mem_Iio,
    ← pos_iff_ne_zero] at hl ⊢
  intro ε ε0
  rcases exists_pos_setLIntegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _

@[simp]

Depends on / 依赖: ENNReal, ENNReal.nhds_zero, exists_pos_setLIntegral_lt_of_measure_lt, mem_Iio, nhds_zero, pos_iff_ne_zero, tendsto_iInf, tendsto_principal
-/
theorem tendsto_setLIntegral_zero {ι} {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {l : Filter ι}
    {s : ι -> Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x in s i, f x ∂μ) l (𝓝 0) := by
  simp only [ENNReal.nhds_zero, tendsto_iInf, tendsto_principal, mem_Iio,
    ← pos_iff_ne_zero] at hl ⊢
  intro ε ε0
  rcases exists_pos_setLIntegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _

@[simp]
/--
theorem `lintegral_smul_measure` / 定理 `lintegral_smul_measure`

English:
theorem lintegral_smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_smul, ENNReal.smul_iSup]

中文:
定理 lintegral_smul_measure
  结论: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_smul, ENNReal.smul_iSup]

Depends on / 依赖: ENNReal, ENNReal.smul_iSup, SimpleFunc, SimpleFunc.lintegral_smul, iSup_subtype, lintegral, lintegral_smul, smul_iSup
-/
theorem lintegral_smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (c : R) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂c • μ = c • ∫⁻ a, f a ∂μ := by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_smul, ENNReal.smul_iSup]

/--
lemma `setLIntegral_smul_measure` / 引理 `setLIntegral_smul_measure`

English:
lemma setLIntegral_smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  rw [Measure.restrict_smul]; rw [lintegral_smul_measure]

@[simp]

中文:
引理 setL整数egral_smul_measure
  结论: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: by
  rw [Measure.restrict_smul]; rw [lintegral_smul_measure]

@[simp]

Depends on / 依赖: Measure, Measure.restrict_smul, lintegral_smul_measure, restrict_smul
-/
lemma setLIntegral_smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (c : R) (f : α -> Real>=0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂(c • μ) = c • ∫⁻ a in s, f a ∂μ := by
  rw [Measure.restrict_smul]; rw [lintegral_smul_measure]

@[simp]
/--
theorem `lintegral_zero_measure` / 定理 `lintegral_zero_measure`

English:
theorem lintegral_zero_measure
  given: {m : MeasurableSpace α} (f : α -> Real>=0∞)
  proof: by
  simp [lintegral]

中文:
定理 lintegral_zero_measure
  条件: {m : 可测空间 α} (f : α -> 实数>=0∞)
  证明: by
  simp [lintegral]

Depends on / 依赖: lintegral
-/
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α -> Real>=0∞) :
    ∫⁻ a, f a ∂(0 : Measure α) = 0 := by
  simp [lintegral]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lintegral_add_measure` / 定理 `lintegral_add_measure`

English:
theorem lintegral_add_measure
  given: (f : α -> Real>=0∞) (μ ν : Measure α)
  proof: by
  simp only [lintegral, SimpleFunc.lintegral_add, iSup_subtype']
  refine (ENNReal.iSup_add_iSup ?_).symm
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  refine ⟨⟨φ ⊔ ψ, sup_le hφ hψ⟩, ?_⟩
  gcongr
  exacts [le_sup_left, le_sup_right]

@[simp]

中文:
定理 lintegral_add_measure
  条件: (f : α -> 实数>=0∞) (μ ν : 测度 α)
  证明: by
  simp only [lintegral, SimpleFunc.lintegral_add, iSup_subtype']
  refine (ENNReal.iSup_add_iSup ?_).symm
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  refine ⟨⟨φ ⊔ ψ, sup_le hφ hψ⟩, ?_⟩
  gcongr
  exacts [le_sup_left, le_sup_right]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.iSup_add_iSup, SimpleFunc, SimpleFunc.lintegral_add, exacts, iSup_add_iSup, iSup_subtype, le_sup_left, le_sup_right, lintegral, lintegral_add, sup_le
-/
theorem lintegral_add_measure (f : α -> Real>=0∞) (μ ν : Measure α) :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simp only [lintegral, SimpleFunc.lintegral_add, iSup_subtype']
  refine (ENNReal.iSup_add_iSup ?_).symm
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  refine ⟨⟨φ ⊔ ψ, sup_le hφ hψ⟩, ?_⟩
  gcongr
  exacts [le_sup_left, le_sup_right]

@[simp]
/--
theorem `lintegral_finsetSum_measure` / 定理 `lintegral_finsetSum_measure`

English:
theorem lintegral_finsetSum_measure
  given: {ι} (s : Finset ι) (f : α -> Real>=0∞) (μ : ι -> Measure α)
  proof: let F : Measure α ->+ Real>=0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_sum F μ s

@[deprecated (since := "2026-04-08")]
alias lintegral_finset_sum_measure := lintegral_finsetSum_measure

@[simp]

中文:
定理 lintegral_finsetSum_measure
  条件: {ι} (s : 有限集 ι) (f : α -> 实数>=0∞) (μ : ι -> 测度 α)
  证明: let F : Measure α ->+ Real>=0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_sum F μ s

@[deprecated (since := "2026-04-08")]
alias lintegral_finset_sum_measure := lintegral_finsetSum_measure

@[simp]

Depends on / 依赖: Measure, lintegral, lintegral_add_measure, lintegral_zero_measure, map_add, map_sum, map_zero
-/
theorem lintegral_finsetSum_measure {ι} (s : Finset ι) (f : α -> Real>=0∞) (μ : ι -> Measure α) :
    ∫⁻ a, f a ∂(∑ i in s, μ i) = ∑ i in s, ∫⁻ a, f a ∂μ i :=
  let F : Measure α ->+ Real>=0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_sum F μ s

@[deprecated (since := "2026-04-08")]
alias lintegral_finset_sum_measure := lintegral_finsetSum_measure

@[simp]
/--
theorem `lintegral_sum_measure` / 定理 `lintegral_sum_measure`

English:
theorem lintegral_sum_measure
  given: {m : MeasurableSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α)
  proof: by
  simp_rw [ENNReal.tsum_eq_iSup_sum, ← lintegral_finsetSum_measure,
    lintegral, SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum,
    SimpleFunc.lintegral_finsetSum, iSup_comm (ι := Finset ι)]

中文:
定理 lintegral_sum_measure
  条件: {m : 可测空间 α} {ι} (f : α -> 实数>=0∞) (μ : ι -> 测度 α)
  证明: by
  simp_rw [ENNReal.tsum_eq_iSup_sum, ← lintegral_finsetSum_measure,
    lintegral, SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum,
    SimpleFunc.lintegral_finsetSum, iSup_comm (ι := Finset ι)]

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_iSup_sum, Finset, SimpleFunc, SimpleFunc.lintegral_finsetSum, SimpleFunc.lintegral_sum, iSup_comm, lintegral, lintegral_finsetSum, lintegral_finsetSum_measure, lintegral_sum, simp_rw, tsum_eq_iSup_sum
-/
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) :
    ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum, ← lintegral_finsetSum_measure,
    lintegral, SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum,
    SimpleFunc.lintegral_finsetSum, iSup_comm (ι := Finset ι)]

/--
theorem `hasSum_lintegral_measure` / 定理 `hasSum_lintegral_measure`

English:
theorem hasSum_lintegral_measure
  given: {ι} {_ : MeasurableSpace α} (f : α -> Real>=0∞) (μ : ι -> Measure α)
  proof: (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum

@[simp]

中文:
定理 hasSum_lintegral_measure
  条件: {ι} {_ : 可测空间 α} (f : α -> 实数>=0∞) (μ : ι -> 测度 α)
  证明: (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum

@[simp]

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum, hasSum, lintegral_sum_measure, summable
-/
theorem hasSum_lintegral_measure {ι} {_ : MeasurableSpace α} (f : α -> Real>=0∞) (μ : ι -> Measure α) :
    HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ) :=
  (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum

@[simp]
/--
theorem `lintegral_of_isEmpty` / 定理 `lintegral_of_isEmpty`

English:
theorem lintegral_of_isEmpty
  given: {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α -> Real>=0∞)
  proof: by
  have : Subsingleton (Measure α) := inferInstance
  convert! lintegral_zero_measure f

中文:
定理 lintegral_of_isEmpty
  条件: {α} [可测空间 α] [是空 α] (μ : 测度 α) (f : α -> 实数>=0∞)
  证明: by
  have : Subsingleton (Measure α) := inferInstance
  convert! lintegral_zero_measure f

Depends on / 依赖: Measure, Subsingleton, convert, lintegral_zero_measure
-/
theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α -> Real>=0∞) :
    ∫⁻ x, f x ∂μ = 0 := by
  have : Subsingleton (Measure α) := inferInstance
  convert! lintegral_zero_measure f

/--
theorem `setLIntegral_empty` / 定理 `setLIntegral_empty`

English:
theorem setLIntegral_empty
  given: (f : α -> Real>=0∞)
  statement: ∫⁻ x in ∅, f x ∂μ = 0
  proof: by
  rw [Measure.restrict_empty]; rw [lintegral_zero_measure]

中文:
定理 setL整数egral_empty
  条件: (f : α -> 实数>=0∞)
  结论: ∫⁻ x in ∅, f x ∂μ = 0
  证明: by
  rw [Measure.restrict_empty]; rw [lintegral_zero_measure]

Depends on / 依赖: Measure, Measure.restrict_empty, lintegral_zero_measure, restrict_empty
-/
theorem setLIntegral_empty (f : α -> Real>=0∞) : ∫⁻ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty]; rw [lintegral_zero_measure]

/--
theorem `setLIntegral_univ` / 定理 `setLIntegral_univ`

English:
theorem setLIntegral_univ
  given: (f : α -> Real>=0∞)
  statement: ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
  proof: by
  rw [Measure.restrict_univ]

中文:
定理 setL整数egral_univ
  条件: (f : α -> 实数>=0∞)
  结论: ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
  证明: by
  rw [Measure.restrict_univ]

Depends on / 依赖: Measure, Measure.restrict_univ, restrict_univ
-/
theorem setLIntegral_univ (f : α -> Real>=0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [Measure.restrict_univ]

/--
theorem `setLIntegral_measure_zero` / 定理 `setLIntegral_measure_zero`

English:
theorem setLIntegral_measure_zero
  given: (s : Set α) (f : α -> Real>=0∞) (hs' : μ s = 0)
  proof: by
  convert! lintegral_zero_measure _
  exact Measure.restrict_eq_zero.2 hs'

中文:
定理 setL整数egral_measure_zero
  条件: (s : 集合 α) (f : α -> 实数>=0∞) (hs' : μ s = 0)
  证明: by
  convert! lintegral_zero_measure _
  exact Measure.restrict_eq_zero.2 hs'

Depends on / 依赖: Measure, Measure.restrict_eq_zero, convert, lintegral_zero_measure, restrict_eq_zero
-/
theorem setLIntegral_measure_zero (s : Set α) (f : α -> Real>=0∞) (hs' : μ s = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  convert! lintegral_zero_measure _
  exact Measure.restrict_eq_zero.2 hs'

-- TODO: Need a better way of rewriting inside of an integral
/--
theorem `lintegral_rw₁` / 定理 `lintegral_rw₁`

English:
theorem lintegral_rw₁
  given: {f f' : α -> β} (h : f =ᵐ[μ] f') (g : β -> Real>=0∞)
  proof: lintegral_congr_ae h.mono fun a h => by dsimp only; rw [h]

中文:
定理 lintegral_rw₁
  条件: {f f' : α -> β} (h : f =ᵐ[μ] f') (g : β -> 实数>=0∞)
  证明: lintegral_congr_ae h.mono fun a h => by dsimp only; rw [h]

Depends on / 依赖: h.mono, lintegral_congr_ae
-/
theorem lintegral_rw₁ {f f' : α -> β} (h : f =ᵐ[μ] f') (g : β -> Real>=0∞) :
    ∫⁻ a, g (f a) ∂μ = ∫⁻ a, g (f' a) ∂μ :=
lintegral_congr_ae h.mono fun a h => by dsimp only; rw [h]

-- TODO: Need a better way of rewriting inside of an integral
/--
theorem `lintegral_rw₂` / 定理 `lintegral_rw₂`

English:
theorem lintegral_rw₂
  statement: {f₁ f₁' : α -> β} {f₂ f₂' : α -> γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
  proof: lintegral_congr_ae h₁.mp h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]

中文:
定理 lintegral_rw₂
  结论: {f₁ f₁' : α -> β} {f₂ f₂' : α -> γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
  证明: lintegral_congr_ae h₁.mp h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]

Depends on / 依赖: lintegral_congr_ae
-/
theorem lintegral_rw₂ {f₁ f₁' : α -> β} {f₂ f₂' : α -> γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β -> γ -> Real>=0∞) : ∫⁻ a, g (f₁ a) (f₂ a) ∂μ = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
lintegral_congr_ae h₁.mp h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]

/--
theorem `lintegral_indicator_le` / 定理 `lintegral_indicator_le`

English:
theorem lintegral_indicator_le
  given: (f : α -> Real>=0∞) (s : Set α)
  proof: by
  simp only [lintegral]
  apply iSup_le (fun g => (iSup_le (fun hg => ?_)))
  have : g <= f := hg.trans (indicator_le_self s f)
  refine le_iSup_of_le g (le_iSup_of_le this (le_of_eq ?_))
  rw [lintegral_restrict]; rw [SimpleFunc.lintegral]
  congr with t
  by_cases H : t = 0
  · simp [H]
  congr with x
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, iff_self_and]
  rintro rfl
  contrapose H
  simpa [H] using hg x

@[simp]

中文:
定理 lintegral_indicator_le
  条件: (f : α -> 实数>=0∞) (s : 集合 α)
  证明: by
  simp only [lintegral]
  apply iSup_le (fun g => (iSup_le (fun hg => ?_)))
  have : g <= f := hg.trans (indicator_le_self s f)
  refine le_iSup_of_le g (le_iSup_of_le this (le_of_eq ?_))
  rw [lintegral_restrict]; rw [SimpleFunc.lintegral]
  congr with t
  by_cases H : t = 0
  · simp [H]
  congr with x
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, iff_self_and]
  rintro rfl
  contrapose H
  simpa [H] using hg x

@[simp]

Depends on / 依赖: SimpleFunc, SimpleFunc.lintegral, contrapose, hg.trans, iSup_le, iff_self_and, indicator_le_self, le_iSup_of_le, le_of_eq, lintegral, lintegral_restrict, mem_inter_iff, mem_preimage, mem_singleton_iff
-/
theorem lintegral_indicator_le (f : α -> Real>=0∞) (s : Set α) :
    ∫⁻ a, s.indicator f a ∂μ <= ∫⁻ a in s, f a ∂μ := by
  simp only [lintegral]
  apply iSup_le (fun g => (iSup_le (fun hg => ?_)))
  have : g <= f := hg.trans (indicator_le_self s f)
  refine le_iSup_of_le g (le_iSup_of_le this (le_of_eq ?_))
  rw [lintegral_restrict]; rw [SimpleFunc.lintegral]
  congr with t
  by_cases H : t = 0
  · simp [H]
  congr with x
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, iff_self_and]
  rintro rfl
  contrapose H
  simpa [H] using hg x

@[simp]
/--
theorem `lintegral_indicator` / 定理 `lintegral_indicator`

English:
theorem lintegral_indicator
  given: {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
  proof: by
  apply le_antisymm (lintegral_indicator_le f s)
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  refine iSup_mono' (Subtype.forall.2 fun φ hφ => ?_)
  refine ⟨⟨φ.restrict s, fun x => ?_⟩, le_rfl⟩
  simp [hφ x, hs, indicator_le_indicator]

中文:
定理 lintegral_indicator
  条件: {s : 集合 α} (hs : 可测集 s) (f : α -> 实数>=0∞)
  证明: by
  apply le_antisymm (lintegral_indicator_le f s)
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  refine iSup_mono' (Subtype.forall.2 fun φ hφ => ?_)
  refine ⟨⟨φ.restrict s, fun x => ?_⟩, le_rfl⟩
  simp [hφ x, hs, indicator_le_indicator]

Depends on / 依赖: Subtype, Subtype.forall, iSup_mono, iSup_subtype, indicator_le_indicator, le_antisymm, le_rfl, lintegral, lintegral_indicator_le, restrict, restrict_lintegral_eq_lintegral_restrict
-/
theorem lintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  apply le_antisymm (lintegral_indicator_le f s)
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  refine iSup_mono' (Subtype.forall.2 fun φ hφ => ?_)
  refine ⟨⟨φ.restrict s, fun x => ?_⟩, le_rfl⟩
  simp [hφ x, hs, indicator_le_indicator]

/--
lemma `setLIntegral_indicator` / 引理 `setLIntegral_indicator`

English:
lemma setLIntegral_indicator
  given: {s t : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
  proof: by
  rw [lintegral_indicator hs]; rw [Measure.restrict_restrict hs]

中文:
引理 setL整数egral_indicator
  条件: {s t : 集合 α} (hs : 可测集 s) (f : α -> 实数>=0∞)
  证明: by
  rw [lintegral_indicator hs]; rw [Measure.restrict_restrict hs]

Depends on / 依赖: Measure, Measure.restrict_restrict, lintegral_indicator, restrict_restrict
-/
lemma setLIntegral_indicator {s t : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s inter t, f a ∂μ := by
  rw [lintegral_indicator hs]; rw [Measure.restrict_restrict hs]

/--
theorem `lintegral_indicator₀` / 定理 `lintegral_indicator₀`

English:
theorem lintegral_indicator₀
  given: {s : Set α} (hs : NullMeasurableSet s μ) (f : α -> Real>=0∞)
  proof: by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [lintegral_indicator (measurableSet_toMeasurable _ _)]; rw [Measure.restrict_congr_set hs.toMeasurable_ae_eq]

中文:
定理 lintegral_indicator₀
  条件: {s : 集合 α} (hs : NullMeasurableSet s μ) (f : α -> 实数>=0∞)
  证明: by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [lintegral_indicator (measurableSet_toMeasurable _ _)]; rw [Measure.restrict_congr_set hs.toMeasurable_ae_eq]

Depends on / 依赖: Measure, Measure.restrict_congr_set, hs.toMeasurable_ae_eq, indicator_ae_eq_of_ae_eq_set, lintegral_congr_ae, lintegral_indicator, measurableSet_toMeasurable, restrict_congr_set, toMeasurable_ae_eq
-/
theorem lintegral_indicator₀ {s : Set α} (hs : NullMeasurableSet s μ) (f : α -> Real>=0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [lintegral_indicator (measurableSet_toMeasurable _ _)]; rw [Measure.restrict_congr_set hs.toMeasurable_ae_eq]

/--
lemma `setLIntegral_indicator₀` / 引理 `setLIntegral_indicator₀`

English:
lemma setLIntegral_indicator₀
  statement: (f : α -> Real>=0∞) {s t : Set α}
  proof: by
  rw [lintegral_indicator₀ hs]; rw [Measure.restrict_restrict₀ hs]

中文:
引理 setL整数egral_indicator₀
  结论: (f : α -> 实数>=0∞) {s t : 集合 α}
  证明: by
  rw [lintegral_indicator₀ hs]; rw [Measure.restrict_restrict₀ hs]

Depends on / 依赖: Measure, Measure.restrict_restrict
-/
lemma setLIntegral_indicator₀ (f : α -> Real>=0∞) {s t : Set α}
    (hs : NullMeasurableSet s (μ.restrict t)) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s inter t, f a ∂μ := by
  rw [lintegral_indicator₀ hs]; rw [Measure.restrict_restrict₀ hs]

/--
theorem `lintegral_indicator_const_le` / 定理 `lintegral_indicator_const_le`

English:
theorem lintegral_indicator_const_le
  given: (s : Set α) (c : Real>=0∞)
  proof: (lintegral_indicator_le _ _).trans (setLIntegral_const s c).le

中文:
定理 lintegral_indicator_const_le
  条件: (s : 集合 α) (c : 实数>=0∞)
  证明: (lintegral_indicator_le _ _).trans (setLIntegral_const s c).le

Depends on / 依赖: lintegral_indicator_le, setLIntegral_const
-/
theorem lintegral_indicator_const_le (s : Set α) (c : Real>=0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ <= c * μ s :=
  (lintegral_indicator_le _ _).trans (setLIntegral_const s c).le

/--
theorem `lintegral_indicator_const₀` / 定理 `lintegral_indicator_const₀`

English:
theorem lintegral_indicator_const₀
  given: {s : Set α} (hs : NullMeasurableSet s μ) (c : Real>=0∞)
  proof: by
  rw [lintegral_indicator₀ hs]; rw [setLIntegral_const]

中文:
定理 lintegral_indicator_const₀
  条件: {s : 集合 α} (hs : NullMeasurableSet s μ) (c : 实数>=0∞)
  证明: by
  rw [lintegral_indicator₀ hs]; rw [setLIntegral_const]

Depends on / 依赖: setLIntegral_const
-/
theorem lintegral_indicator_const₀ {s : Set α} (hs : NullMeasurableSet s μ) (c : Real>=0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s := by
  rw [lintegral_indicator₀ hs]; rw [setLIntegral_const]

/--
theorem `lintegral_indicator_const` / 定理 `lintegral_indicator_const`

English:
theorem lintegral_indicator_const
  given: {s : Set α} (hs : MeasurableSet s) (c : Real>=0∞)
  proof: lintegral_indicator_const₀ hs.nullMeasurableSet c

中文:
定理 lintegral_indicator_const
  条件: {s : 集合 α} (hs : 可测集 s) (c : 实数>=0∞)
  证明: lintegral_indicator_const₀ hs.nullMeasurableSet c

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : Real>=0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const₀ hs.nullMeasurableSet c

/--
lemma `setLIntegral_eq_of_support_subset` / 引理 `setLIntegral_eq_of_support_subset`

English:
lemma setLIntegral_eq_of_support_subset
  given: {s : Set α} {f : α -> Real>=0∞} (hsf : f.support subseteq s)
  proof: by
  apply le_antisymm (setLIntegral_le_lintegral s fun x => f x)
  apply le_trans (le_of_eq _) (lintegral_indicator_le _ _)
  congr with x
  simp only [indicator]
  split_ifs with h
  · rfl
  · exact Function.support_subset_iff'.1 hsf x h

中文:
引理 setL整数egral_eq_of_support_subset
  条件: {s : 集合 α} {f : α -> 实数>=0∞} (hsf : f.support subseteq s)
  证明: by
  apply le_antisymm (setLIntegral_le_lintegral s fun x => f x)
  apply le_trans (le_of_eq _) (lintegral_indicator_le _ _)
  congr with x
  simp only [indicator]
  split_ifs with h
  · rfl
  · exact Function.support_subset_iff'.1 hsf x h

Depends on / 依赖: Function, Function.support_subset_iff, indicator, le_antisymm, le_of_eq, le_trans, lintegral_indicator_le, setLIntegral_le_lintegral, split_ifs, support_subset_iff
-/
lemma setLIntegral_eq_of_support_subset {s : Set α} {f : α -> Real>=0∞} (hsf : f.support subseteq s) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂μ := by
  apply le_antisymm (setLIntegral_le_lintegral s fun x => f x)
  apply le_trans (le_of_eq _) (lintegral_indicator_le _ _)
  congr with x
  simp only [indicator]
  split_ifs with h
  · rfl
  · exact Function.support_subset_iff'.1 hsf x h

/--
theorem `setLIntegral_eq_const` / 定理 `setLIntegral_eq_const`

English:
theorem setLIntegral_eq_const
  given: {f : α -> Real>=0∞} (hf : Measurable f) (r : Real>=0∞)
  proof: by
  have : forall x in { x | f x = r }, f x = r := fun _ hx => hx
  rw [setLIntegral_congr_fun _ this]
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  · exact hf (measurableSet_singleton r)

@[to_fun lintegral_indicator_fun_one_le]

中文:
定理 setL整数egral_eq_const
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (r : 实数>=0∞)
  证明: by
  have : forall x in { x | f x = r }, f x = r := fun _ hx => hx
  rw [setLIntegral_congr_fun _ this]
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  · exact hf (measurableSet_singleton r)

@[to_fun lintegral_indicator_fun_one_le]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, Set.univ_inter, lintegral_const, measurableSet_singleton, restrict_apply, setLIntegral_congr_fun, univ_inter
-/
theorem setLIntegral_eq_const {f : α -> Real>=0∞} (hf : Measurable f) (r : Real>=0∞) :
    ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r } := by
  have : forall x in { x | f x = r }, f x = r := fun _ hx => hx
  rw [setLIntegral_congr_fun _ this]
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  · exact hf (measurableSet_singleton r)

@[to_fun lintegral_indicator_fun_one_le]
/--
theorem `lintegral_indicator_one_le` / 定理 `lintegral_indicator_one_le`

English:
theorem lintegral_indicator_one_le
  given: (s : Set α)
  statement: ∫⁻ a, s.indicator 1 a ∂μ <= μ s
  proof: (lintegral_indicator_const_le _ _).trans (one_mul _).le

@[to_fun (attr := simp) lintegral_indicator_fun_one₀]

中文:
定理 lintegral_indicator_one_le
  条件: (s : 集合 α)
  结论: ∫⁻ a, s.indicator 1 a ∂μ <= μ s
  证明: (lintegral_indicator_const_le _ _).trans (one_mul _).le

@[to_fun (attr := simp) lintegral_indicator_fun_one₀]

Depends on / 依赖: lintegral_indicator_const_le, one_mul
-/
theorem lintegral_indicator_one_le (s : Set α) : ∫⁻ a, s.indicator 1 a ∂μ <= μ s :=
(lintegral_indicator_const_le _ _).trans (one_mul _).le

@[to_fun (attr := simp) lintegral_indicator_fun_one₀]
/--
theorem `lintegral_indicator_one₀` / 定理 `lintegral_indicator_one₀`

English:
theorem lintegral_indicator_one₀
  given: {s : Set α} (hs : NullMeasurableSet s μ)
  proof: (lintegral_indicator_const₀ hs _).trans one_mul _

@[to_fun lintegral_indicator_fun_one]

中文:
定理 lintegral_indicator_one₀
  条件: {s : 集合 α} (hs : NullMeasurableSet s μ)
  证明: (lintegral_indicator_const₀ hs _).trans one_mul _

@[to_fun lintegral_indicator_fun_one]

Depends on / 依赖: one_mul
-/
theorem lintegral_indicator_one₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
(lintegral_indicator_const₀ hs _).trans one_mul _

@[to_fun lintegral_indicator_fun_one]
/--
theorem `lintegral_indicator_one` / 定理 `lintegral_indicator_one`

English:
theorem lintegral_indicator_one
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  simp [hs]

中文:
定理 lintegral_indicator_one
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: by
  simp [hs]
-/
theorem lintegral_indicator_one {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s := by
  simp [hs]

/--
theorem `Measure.ext_iff_lintegral` / 定理 `Measure.ext_iff_lintegral`

English:
theorem Measure.ext_iff_lintegral
  given: (ν : Measure α)
  proof: by
  refine ⟨fun h _ _ => by rw [h], ?_⟩
  intro h
  ext s hs
  simp only [← lintegral_indicator_one hs]
  exact h (s.indicator 1) ((measurable_indicator_const_iff 1).mpr hs)

中文:
定理 测度.ext_iff_lintegral
  条件: (ν : 测度 α)
  证明: by
  refine ⟨fun h _ _ => by rw [h], ?_⟩
  intro h
  ext s hs
  simp only [← lintegral_indicator_one hs]
  exact h (s.indicator 1) ((measurable_indicator_const_iff 1).mpr hs)

Depends on / 依赖: indicator, lintegral_indicator_one, measurable_indicator_const_iff, s.indicator
-/
theorem Measure.ext_iff_lintegral (ν : Measure α) :
    μ = ν ↔ forall f : α -> Real>=0∞, Measurable f -> ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν := by
  refine ⟨fun h _ _ => by rw [h], ?_⟩
  intro h
  ext s hs
  simp only [← lintegral_indicator_one hs]
  exact h (s.indicator 1) ((measurable_indicator_const_iff 1).mpr hs)

/--
theorem `Measure.ext_of_lintegral` / 定理 `Measure.ext_of_lintegral`

English:
theorem Measure.ext_of_lintegral
  statement: (ν : Measure α)
  proof: (μ.ext_iff_lintegral ν).mpr hμν

中文:
定理 测度.ext_of_lintegral
  结论: (ν : 测度 α)
  证明: (μ.ext_iff_lintegral ν).mpr hμν

Depends on / 依赖: ext_iff_lintegral
-/
theorem Measure.ext_of_lintegral (ν : Measure α)
    (hμν : forall f : α -> Real>=0∞, Measurable f -> ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν) : μ = ν :=
  (μ.ext_iff_lintegral ν).mpr hμν

open Measure

open scoped Function -- required for scoped `on` notation

/--
theorem `lintegral_iUnion₀` / 定理 `lintegral_iUnion₀`

English:
theorem lintegral_iUnion₀
  statement: [Countable β] {s : β -> Set α} (hm : forall i, NullMeasurableSet (s i) μ)
  proof: by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]

中文:
定理 lintegral_iUnion₀
  结论: [可数 β] {s : β -> 集合 α} (hm : 对任意 i, NullMeasurableSet (s i) μ)
  证明: by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]

Depends on / 依赖: Measure, Measure.restrict_iUnion_ae, lintegral_sum_measure, restrict_iUnion_ae
-/
theorem lintegral_iUnion₀ [Countable β] {s : β -> Set α} (hm : forall i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α -> Real>=0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ := by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]

/--
theorem `lintegral_iUnion` / 定理 `lintegral_iUnion`

English:
theorem lintegral_iUnion
  statement: [Countable β] {s : β -> Set α} (hm : forall i, MeasurableSet (s i))
  proof: lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f

中文:
定理 lintegral_iUnion
  结论: [可数 β] {s : β -> 集合 α} (hm : 对任意 i, 可测集 (s i))
  证明: lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet
-/
theorem lintegral_iUnion [Countable β] {s : β -> Set α} (hm : forall i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : α -> Real>=0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
  lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f

/--
theorem `lintegral_biUnion₀` / 定理 `lintegral_biUnion₀`

English:
theorem lintegral_biUnion₀
  statement: {t : Set β} {s : β -> Set α} (ht : t.Countable)
  proof: by
  have := ht.toEncodable
  rw [biUnion_eq_iUnion]; rw [lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]

中文:
定理 lintegral_biUnion₀
  结论: {t : 集合 β} {s : β -> 集合 α} (ht : t.可数)
  证明: by
  have := ht.toEncodable
  rw [biUnion_eq_iUnion]; rw [lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]

Depends on / 依赖: SetCoe, SetCoe.forall, biUnion_eq_iUnion, hd.subtype, ht.toEncodable, subtype, toEncodable
-/
theorem lintegral_biUnion₀ {t : Set β} {s : β -> Set α} (ht : t.Countable)
    (hm : forall i in t, NullMeasurableSet (s i) μ) (hd : t.Pairwise (AEDisjoint μ on s)) (f : α -> Real>=0∞) :
    ∫⁻ a in ⋃ i in t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ := by
  have := ht.toEncodable
  rw [biUnion_eq_iUnion]; rw [lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]

/--
theorem `lintegral_biUnion` / 定理 `lintegral_biUnion`

English:
theorem lintegral_biUnion
  statement: {t : Set β} {s : β -> Set α} (ht : t.Countable)
  proof: lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f

中文:
定理 lintegral_biUnion
  结论: {t : 集合 β} {s : β -> 集合 α} (ht : t.可数)
  证明: lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet
-/
theorem lintegral_biUnion {t : Set β} {s : β -> Set α} (ht : t.Countable)
    (hm : forall i in t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α -> Real>=0∞) :
    ∫⁻ a in ⋃ i in t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f

/--
theorem `lintegral_biUnion_finset₀` / 定理 `lintegral_biUnion_finset₀`

English:
theorem lintegral_biUnion_finset₀
  statement: {s : Finset β} {t : β -> Set α}
  proof: by
  simp only [← Finset.mem_coe, lintegral_biUnion₀ s.countable_toSet hm hd, ← Finset.tsum_subtype']

中文:
定理 lintegral_biUnion_finset₀
  结论: {s : 有限集 β} {t : β -> 集合 α}
  证明: by
  simp only [← Finset.mem_coe, lintegral_biUnion₀ s.countable_toSet hm hd, ← Finset.tsum_subtype']

Depends on / 依赖: Finset, Finset.mem_coe, Finset.tsum_subtype, countable_toSet, mem_coe, s.countable_toSet, tsum_subtype
-/
theorem lintegral_biUnion_finset₀ {s : Finset β} {t : β -> Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : forall b in s, NullMeasurableSet (t b) μ)
    (f : α -> Real>=0∞) : ∫⁻ a in ⋃ b in s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ := by
  simp only [← Finset.mem_coe, lintegral_biUnion₀ s.countable_toSet hm hd, ← Finset.tsum_subtype']

/--
theorem `lintegral_biUnion_finset` / 定理 `lintegral_biUnion_finset`

English:
theorem lintegral_biUnion_finset
  statement: {s : Finset β} {t : β -> Set α} (hd : Set.PairwiseDisjoint (↑s) t)
  proof: lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f

中文:
定理 lintegral_biUnion_finset
  结论: {s : 有限集 β} {t : β -> 集合 α} (hd : 集合.PairwiseDisjoint (↑s) t)
  证明: lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet
-/
theorem lintegral_biUnion_finset {s : Finset β} {t : β -> Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : forall b in s, MeasurableSet (t b)) (f : α -> Real>=0∞) :
    ∫⁻ a in ⋃ b in s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f

/--
theorem `lintegral_iUnion_le` / 定理 `lintegral_iUnion_le`

English:
theorem lintegral_iUnion_le
  given: [Countable β] (s : β -> Set α) (f : α -> Real>=0∞)
  proof: by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_iUnion_le le_rfl

中文:
定理 lintegral_iUnion_le
  条件: [可数 β] (s : β -> 集合 α) (f : α -> 实数>=0∞)
  证明: by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_iUnion_le le_rfl

Depends on / 依赖: le_rfl, lintegral_mono, lintegral_sum_measure, restrict_iUnion_le
-/
theorem lintegral_iUnion_le [Countable β] (s : β -> Set α) (f : α -> Real>=0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ <= ∑' i, ∫⁻ a in s i, f a ∂μ := by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_iUnion_le le_rfl

/--
theorem `lintegral_union` / 定理 `lintegral_union`

English:
theorem lintegral_union
  given: {f : α -> Real>=0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B)
  proof: by
  rw [restrict_union hAB hB]; rw [lintegral_add_measure]

中文:
定理 lintegral_union
  条件: {f : α -> 实数>=0∞} {A B : 集合 α} (hB : 可测集 B) (hAB : Disjoint A B)
  证明: by
  rw [restrict_union hAB hB]; rw [lintegral_add_measure]

Depends on / 依赖: lintegral_add_measure, restrict_union
-/
theorem lintegral_union {f : α -> Real>=0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ∫⁻ a in A union B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ := by
  rw [restrict_union hAB hB]; rw [lintegral_add_measure]

/--
theorem `lintegral_union_le` / 定理 `lintegral_union_le`

English:
theorem lintegral_union_le
  given: (f : α -> Real>=0∞) (s t : Set α)
  proof: by
  rw [← lintegral_add_measure]
  exact lintegral_mono' (restrict_union_le _ _) le_rfl

中文:
定理 lintegral_union_le
  条件: (f : α -> 实数>=0∞) (s t : 集合 α)
  证明: by
  rw [← lintegral_add_measure]
  exact lintegral_mono' (restrict_union_le _ _) le_rfl

Depends on / 依赖: le_rfl, lintegral_add_measure, lintegral_mono, restrict_union_le
-/
theorem lintegral_union_le (f : α -> Real>=0∞) (s t : Set α) :
    ∫⁻ a in s union t, f a ∂μ <= ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ := by
  rw [← lintegral_add_measure]
  exact lintegral_mono' (restrict_union_le _ _) le_rfl

/--
theorem `lintegral_inter_add_sdiff` / 定理 `lintegral_inter_add_sdiff`

English:
theorem lintegral_inter_add_sdiff
  given: {B : Set α} (f : α -> Real>=0∞) (A : Set α) (hB : MeasurableSet B)
  proof: by
  rw [← lintegral_add_measure]; rw [restrict_inter_add_sdiff _ hB]

@[deprecated (since := "2026-06-03")] alias lintegral_inter_add_diff := lintegral_inter_add_sdiff

中文:
定理 lintegral_inter_add_sdiff
  条件: {B : 集合 α} (f : α -> 实数>=0∞) (A : 集合 α) (hB : 可测集 B)
  证明: by
  rw [← lintegral_add_measure]; rw [restrict_inter_add_sdiff _ hB]

@[deprecated (since := "2026-06-03")] alias lintegral_inter_add_diff := lintegral_inter_add_sdiff

Depends on / 依赖: lintegral_add_measure, restrict_inter_add_sdiff
-/
theorem lintegral_inter_add_sdiff {B : Set α} (f : α -> Real>=0∞) (A : Set α) (hB : MeasurableSet B) :
    ∫⁻ x in A inter B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ := by
  rw [← lintegral_add_measure]; rw [restrict_inter_add_sdiff _ hB]

@[deprecated (since := "2026-06-03")] alias lintegral_inter_add_diff := lintegral_inter_add_sdiff

/--
theorem `lintegral_add_compl` / 定理 `lintegral_add_compl`

English:
theorem lintegral_add_compl
  given: (f : α -> Real>=0∞) {A : Set α} (hA : MeasurableSet A)
  proof: by
  rw [← lintegral_add_measure]; rw [Measure.restrict_add_restrict_compl hA]

中文:
定理 lintegral_add_compl
  条件: (f : α -> 实数>=0∞) {A : 集合 α} (hA : 可测集 A)
  证明: by
  rw [← lintegral_add_measure]; rw [Measure.restrict_add_restrict_compl hA]

Depends on / 依赖: Measure, Measure.restrict_add_restrict_compl, lintegral_add_measure, restrict_add_restrict_compl
-/
theorem lintegral_add_compl (f : α -> Real>=0∞) {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_add_measure]; rw [Measure.restrict_add_restrict_compl hA]

/--
lemma `lintegral_piecewise` / 引理 `lintegral_piecewise`

English:
lemma lintegral_piecewise
  given: (hs : MeasurableSet s) (f g : α -> Real>=0∞) [forall j, Decidable (j in s)]
  proof: by
  rw [← lintegral_add_compl _ hs]
  congr 1
· exact setLIntegral_congr_fun hs fun _ => Set.piecewise_eq_of_mem _ _ _
· exact setLIntegral_congr_fun hs.compl fun _ => Set.piecewise_eq_of_notMem _ _ _

中文:
引理 lintegral_piecewise
  条件: (hs : 可测集 s) (f g : α -> 实数>=0∞) [对任意 j, 可判定 (j in s)]
  证明: by
  rw [← lintegral_add_compl _ hs]
  congr 1
· exact setLIntegral_congr_fun hs fun _ => Set.piecewise_eq_of_mem _ _ _
· exact setLIntegral_congr_fun hs.compl fun _ => Set.piecewise_eq_of_notMem _ _ _

Depends on / 依赖: Set.piecewise_eq_of_mem, Set.piecewise_eq_of_notMem, hs.compl, lintegral_add_compl, piecewise_eq_of_mem, piecewise_eq_of_notMem, setLIntegral_congr_fun
-/
lemma lintegral_piecewise (hs : MeasurableSet s) (f g : α -> Real>=0∞) [forall j, Decidable (j in s)] :
    ∫⁻ a, s.piecewise f g a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in sᶜ, g a ∂μ := by
  rw [← lintegral_add_compl _ hs]
  congr 1
· exact setLIntegral_congr_fun hs fun _ => Set.piecewise_eq_of_mem _ _ _
· exact setLIntegral_congr_fun hs.compl fun _ => Set.piecewise_eq_of_notMem _ _ _

/--
theorem `setLIntegral_compl` / 定理 `setLIntegral_compl`

English:
theorem setLIntegral_compl
  statement: {f : α -> Real>=0∞} {s : Set α} (hsm : MeasurableSet s)
  proof: by
  rw [← lintegral_add_compl (μ := μ) f hsm]; rw [ENNReal.add_sub_cancel_left hfs]

中文:
定理 setL整数egral_compl
  结论: {f : α -> 实数>=0∞} {s : 集合 α} (hsm : 可测集 s)
  证明: by
  rw [← lintegral_add_compl (μ := μ) f hsm]; rw [ENNReal.add_sub_cancel_left hfs]

Depends on / 依赖: ENNReal, ENNReal.add_sub_cancel_left, add_sub_cancel_left, lintegral_add_compl
-/
theorem setLIntegral_compl {f : α -> Real>=0∞} {s : Set α} (hsm : MeasurableSet s)
    (hfs : ∫⁻ x in s, f x ∂μ != ∞) :
    ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ - ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_add_compl (μ := μ) f hsm]; rw [ENNReal.add_sub_cancel_left hfs]

/--
theorem `setLIntegral_iUnion_of_directed` / 定理 `setLIntegral_iUnion_of_directed`

English:
theorem setLIntegral_iUnion_of_directed
  statement: {ι : Type*} [Countable ι]
  proof: by
  simp only [lintegral_def, iSup_comm (ι := ι),
    SimpleFunc.lintegral_restrict_iUnion_of_directed _ hd]

中文:
定理 setL整数egral_iUnion_of_directed
  结论: {ι : 类型} [可数 ι]
  证明: by
  simp only [lintegral_def, iSup_comm (ι := ι),
    SimpleFunc.lintegral_restrict_iUnion_of_directed _ hd]

Depends on / 依赖: SimpleFunc, SimpleFunc.lintegral_restrict_iUnion_of_directed, iSup_comm, lintegral_def, lintegral_restrict_iUnion_of_directed
-/
theorem setLIntegral_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α -> Real>=0∞) {s : ι -> Set α} (hd : Directed (· subseteq ·) s) :
    ∫⁻ x in ⋃ i, s i, f x ∂μ = ⨆ i, ∫⁻ x in s i, f x ∂μ := by
  simp only [lintegral_def, iSup_comm (ι := ι),
    SimpleFunc.lintegral_restrict_iUnion_of_directed _ hd]

/--
theorem `lintegral_max` / 定理 `lintegral_max`

English:
theorem lintegral_max
  given: {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g)
  proof: by
  have hm : MeasurableSet { x | f x <= g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_ofPred, ← not_le]
  refine congr_arg₂ (· + ·) (setLIntegral_congr_fun hm ?_) (setLIntegral_congr_fun hm.compl ?_)
  exacts [fun x => max_eq_right (a := f x) (b := g x),
    fun x (hx : ¬ f x <= g x) => max_eq_left (not_le.1 hx).le]

中文:
定理 lintegral_max
  条件: {f g : α -> 实数>=0∞} (hf : 可测 f) (hg : 可测 g)
  证明: by
  have hm : MeasurableSet { x | f x <= g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_ofPred, ← not_le]
  refine congr_arg₂ (· + ·) (setLIntegral_congr_fun hm ?_) (setLIntegral_congr_fun hm.compl ?_)
  exacts [fun x => max_eq_right (a := f x) (b := g x),
    fun x (hx : ¬ f x <= g x) => max_eq_left (not_le.1 hx).le]

Depends on / 依赖: MeasurableSet, compl_ofPred, exacts, hm.compl, lintegral_add_compl, max_eq_left, max_eq_right, measurableSet_le, not_le, setLIntegral_congr_fun
-/
theorem lintegral_max {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, max (f x) (g x) ∂μ =
      ∫⁻ x in { x | f x <= g x }, g x ∂μ + ∫⁻ x in { x | g x < f x }, f x ∂μ := by
  have hm : MeasurableSet { x | f x <= g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_ofPred, ← not_le]
  refine congr_arg₂ (· + ·) (setLIntegral_congr_fun hm ?_) (setLIntegral_congr_fun hm.compl ?_)
  exacts [fun x => max_eq_right (a := f x) (b := g x),
    fun x (hx : ¬ f x <= g x) => max_eq_left (not_le.1 hx).le]

/--
theorem `setLIntegral_max` / 定理 `setLIntegral_max`

English:
theorem setLIntegral_max
  given: {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α)
  proof: by
  rw [lintegral_max hf hg]; rw [restrict_restrict]; rw [restrict_restrict]; rw [inter_comm s]; rw [inter_comm s]
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]

中文:
定理 setL整数egral_max
  条件: {f g : α -> 实数>=0∞} (hf : 可测 f) (hg : 可测 g) (s : 集合 α)
  证明: by
  rw [lintegral_max hf hg]; rw [restrict_restrict]; rw [restrict_restrict]; rw [inter_comm s]; rw [inter_comm s]
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]

Depends on / 依赖: exacts, inter_comm, lintegral_max, measurableSet_le, measurableSet_lt, restrict_restrict
-/
theorem setLIntegral_max {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    ∫⁻ x in s, max (f x) (g x) ∂μ =
      ∫⁻ x in s inter { x | f x <= g x }, g x ∂μ + ∫⁻ x in s inter { x | g x < f x }, f x ∂μ := by
  rw [lintegral_max hf hg]; rw [restrict_restrict]; rw [restrict_restrict]; rw [inter_comm s]; rw [inter_comm s]
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]

/--
theorem `setLIntegral_lt_top_of_le_nnreal` / 定理 `setLIntegral_lt_top_of_le_nnreal`

English:
theorem setLIntegral_lt_top_of_le_nnreal
  statement: {s : Set α} (hs : μ s != ∞) {f : α -> Real>=0∞}
  proof: by
  obtain ⟨M, hM⟩ := hbdd
  refine lt_of_le_of_lt (setLIntegral_mono measurable_const hM) ?_
  simp [ENNReal.mul_lt_top, hs.lt_top]

中文:
定理 setL整数egral_lt_top_of_le_nnreal
  结论: {s : 集合 α} (hs : μ s != ∞) {f : α -> 实数>=0∞}
  证明: by
  obtain ⟨M, hM⟩ := hbdd
  refine lt_of_le_of_lt (setLIntegral_mono measurable_const hM) ?_
  simp [ENNReal.mul_lt_top, hs.lt_top]

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, hs.lt_top, lt_of_le_of_lt, lt_top, measurable_const, mul_lt_top, setLIntegral_mono
-/
theorem setLIntegral_lt_top_of_le_nnreal {s : Set α} (hs : μ s != ∞) {f : α -> Real>=0∞}
    (hbdd : exists y : Real>=0, forall x in s, f x <= y) : ∫⁻ x in s, f x ∂μ < ∞ := by
  obtain ⟨M, hM⟩ := hbdd
  refine lt_of_le_of_lt (setLIntegral_mono measurable_const hM) ?_
  simp [ENNReal.mul_lt_top, hs.lt_top]

/--
theorem `setLIntegral_lt_top_of_bddAbove` / 定理 `setLIntegral_lt_top_of_bddAbove`

English:
theorem setLIntegral_lt_top_of_bddAbove
  statement: {s : Set α} (hs : μ s != ∞) {f : α -> Real>=0}
  proof: setLIntegral_lt_top_of_le_nnreal hs hbdd.imp fun _M hM _x hx =>
ENNReal.coe_le_coe.2 hM (mem_image_of_mem f hx)

中文:
定理 setL整数egral_lt_top_of_bddAbove
  结论: {s : 集合 α} (hs : μ s != ∞) {f : α -> 实数>=0}
  证明: setLIntegral_lt_top_of_le_nnreal hs hbdd.imp fun _M hM _x hx =>
ENNReal.coe_le_coe.2 hM (mem_image_of_mem f hx)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, hbdd.imp, mem_image_of_mem, setLIntegral_lt_top_of_le_nnreal
-/
theorem setLIntegral_lt_top_of_bddAbove {s : Set α} (hs : μ s != ∞) {f : α -> Real>=0}
    (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞ :=
setLIntegral_lt_top_of_le_nnreal hs hbdd.imp fun _M hM _x hx =>
ENNReal.coe_le_coe.2 hM (mem_image_of_mem f hx)

/--
theorem `setLIntegral_lt_top_of_isCompact` / 定理 `setLIntegral_lt_top_of_isCompact`

English:
theorem setLIntegral_lt_top_of_isCompact
  statement: [TopologicalSpace α] {s : Set α}
  proof: setLIntegral_lt_top_of_bddAbove hs (hsc.image hf).bddAbove

中文:
定理 setL整数egral_lt_top_of_isCompact
  结论: [拓扑空间 α] {s : 集合 α}
  证明: setLIntegral_lt_top_of_bddAbove hs (hsc.image hf).bddAbove

Depends on / 依赖: bddAbove, hsc.image, setLIntegral_lt_top_of_bddAbove
-/
theorem setLIntegral_lt_top_of_isCompact [TopologicalSpace α] {s : Set α}
    (hs : μ s != ∞) (hsc : IsCompact s) {f : α -> Real>=0} (hf : Continuous f) :
    ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_bddAbove hs (hsc.image hf).bddAbove

end MeasureTheory
