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

local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ : Type*}

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
noncomputable irreducible_def lintegral (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ

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

/-
**MeasureTheory.SimpleFunc.lintegral_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} (f : MeasureTheory.SimpleFunc α E
NNReal) (μ : MeasureTheory.Measure α),   ∫⁻ (a : α), f a ∂μ = f.lintegral μ
参数：f : MeasureTheory.SimpleFunc α ENNReal；μ : MeasureTheory.Measure α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono`：lintegral_mono {f g : α ->ₛ Rea
l>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.lintegral μ <= g.lintegral ν
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
-/
theorem SimpleFunc.lintegral_eq_lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ = f.lintegral μ := by
  rw [MeasureTheory.lintegral]
  exact le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[gcongr, mono]
/-
**MeasureTheory.lintegral_mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ <= ν) ⦃
f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono`：lintegral_mono {f g : α ->ₛ Rea
l>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.lintegral μ <= g.lintegral ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄
    (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν := by
  rw [lintegral, lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

-- version where `hfg` is an explicit forall, so that `@[gcongr]` can recognize it
/-
**MeasureTheory.lintegral_mono_fn'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}, 
  μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α), f x ≤ g x) → ∫⁻ (a : α), f a ∂μ ≤ ∫
⁻ (a : α), g a ∂ν
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
-/
@[gcongr] theorem lintegral_mono_fn' (h2 : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν :=
  lintegral_mono' h2 hfg
/-
**MeasureTheory.lintegral_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a
, g a ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg
/-
**MeasureTheory.lintegral_mono_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mono_nnreal {f g : α -> Real>=0} (h : f <= g) : ∫⁻ a, f a ∂μ <= 
∫⁻ a, g a ∂μ
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)
/-
**MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：iSup_lintegral_measurable_le_eq_lintegral (f : α -> Real>=0∞) : ⨆ (g : α -
> Real>=0∞) (_ : Measurable g) (_ : g <= f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
-/
theorem iSup_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
    ⨆ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun _ => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
    refine iSup₂_le fun i hi => le_iSup₂_of_le i i.measurable <| le_iSup_of_le hi ?_
    exact le_of_eq (i.lintegral_eq_lintegral _).symm
/-
**MeasureTheory.lintegral_mono_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mono_set {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {
f : α -> Real>=0∞} (hst : s subseteq t) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in t, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_mono_set {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ⊆ t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)
/-
**MeasureTheory.lintegral_mono_set'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mono_set' {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} 
{f : α -> Real>=0∞} (hst : s <=ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in t, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_mono'`：restrict_mono' {_m0 : MeasurableSp
ace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s <=ᵐ[μ] s') (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_mono_set' {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ≤ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)
/-
**MeasureTheory.monotone_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：monotone_lintegral {_ : MeasurableSpace α} (μ : Measure α) : Monotone (lin
tegral μ)
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
-/
theorem monotone_lintegral {_ : MeasurableSpace α} (μ : Measure α) : Monotone (lintegral μ) :=
  lintegral_mono

@[simp]
/-
**MeasureTheory.lintegral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_const (c : Real>=0∞) : ∫⁻ _, c ∂μ = c * μ univ
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.const_lintegral`：const_lintegral (c : Real>=0∞)
 : (const α c).lintegral μ = c * μ univ
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.SimpleFunc.coe_const`：coe_const (b : β) : ⇑(const α b) = F
unction.const α b
-/
theorem lintegral_const (c : ℝ≥0∞) : ∫⁻ _, c ∂μ = c * μ univ := by
  rw [← SimpleFunc.const_lintegral, ← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_const]
  rfl
/-
**MeasureTheory.lintegral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0 := by simp
/-
**MeasureTheory.lintegral_zero_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_zero_fun : lintegral μ (0 : α -> Real>=0∞) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
-/
theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero
/-
**MeasureTheory.lintegral_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem lintegral_one : ∫⁻ _, (1 : ℝ≥0∞) ∂μ = μ univ := by rw [lintegral_const, one_mul]
/-
**MeasureTheory.setLIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_const (s : Set α) (c : Real>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
参数：s : Set α；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
-/
theorem setLIntegral_const (s : Set α) (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by
  rw [lintegral_const, Measure.restrict_apply_univ]
/-
**MeasureTheory.setLIntegral_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s := by rw [setLIntegral_const, one_mul]
/-
**MeasureTheory.iInf_mul_le_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：iInf_mul_le_lintegral (f : α -> Real>=0∞) : (⨅ x, f x) * μ .univ <= ∫⁻ x, 
f x ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma iInf_mul_le_lintegral (f : α → ℝ≥0∞) : (⨅ x, f x) * μ .univ ≤ ∫⁻ x, f x ∂μ := by
  calc (⨅ x, f x) * μ .univ
  _ = ∫⁻ y, ⨅ x, f x ∂μ := by simp
  _ ≤ ∫⁻ x, f x ∂μ := by gcongr; exact iInf_le _ _
/-
**MeasureTheory.lintegral_le_iSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_le_iSup_mul (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ <= (⨆ x, f x) * μ
 .univ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lintegral_le_iSup_mul (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ (⨆ x, f x) * μ .univ := by
  calc ∫⁻ x, f x ∂μ
  _ ≤ ∫⁻ y, ⨆ x, f x ∂μ := by gcongr; exact le_iSup _ _
  _ = (⨆ x, f x) * μ .univ := by simp

variable (μ) in
/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral. -/
/-
**MeasureTheory.exists_measurable_le_lintegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：exists_measurable_le_lintegral_eq (f : α -> Real>=0∞) : exists g : α -> Re
al>=0∞, Measurable g ∧ g <= f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Pi.instCanonicallyOrderedAddForall`：∀ {ι : Type u_6} {Z : ι → Type u_7} 
[inst : (i : ι) → AddMonoid (Z i)] [inst_1 : (i : ι) → PartialOrder (Z i)]   [∀ 
(i : ι), CanonicallyOrde…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
· 使用定理 `exists_seq_strictMono_tendsto'`：exists_seq_strictMono_tendsto' {α : Type
*} [LinearOrder α] [TopologicalSpace α] [DenselyOrdered α] [OrderTopology α] [Fi
rstCountableTopology…
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral`：iSup_lintegral_
measurable_le_eq_lintegral (f : α -> Real>=0∞) : ⨆ (g : α -> Real>=0∞) (_ : Meas
urable g) (_ : g <= f), ∫⁻ a, g a ∂μ = ∫⁻ a, …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Measurable.iSup`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with
 the same
integral.
-/
theorem exists_measurable_le_lintegral_eq (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  rcases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ | h₀
  · exact ⟨0, measurable_zero, zero_le, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using this
  refine
    ⟨fun x => ⨆ n, g n x, .iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm ?_ ?_⟩
  · refine le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans <| lintegral_mono fun x => ?_
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
/-
**MeasureTheory.lintegral_eq_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_eq_nnreal {m : MeasurableSpace α} (f : α -> Real>=0∞) (μ : Measu
re α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0) (_ : forall x, ↑(φ x) <= f x), (φ.m
ap ((↑) : Real>=0 -> Real>=0∞)).lintegral μ
参数：f : α -> Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ENNReal.coe_toNNReal_le_self`：∀ {a : ENNReal}, ↑a.toNNReal ≤ a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_congr`：lintegral_congr {f g : α ->ₛ R
eal>=0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `ENNReal.exists_nat_mul_gt`：exists_nat_mul_gt (ha : a != 0) (hb : b != ∞)
 : exists n : Nat, b < n * a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
`∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`.
-/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ =
      ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ x, ↑(φ x) ≤ f x), (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ := by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun φ hφ ↦ ?_) (iSup_mono' fun φ ↦ ⟨φ.map ((↑) : ℝ≥0 → ℝ≥0∞), le_rfl⟩)
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map ((↑) : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : ∀ x, ↑(ψ x) ≤ f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact le_iSup₂_of_le (φ.map ENNReal.toNNReal) this (ge_of_eq <| lintegral_congr h)
  · have h_meas : μ (φ ⁻¹' {∞}) ≠ 0 := mt measure_eq_zero_iff_ae_notMem.1 h
    refine le_trans le_top (ge_of_eq <| iSup_eq_top.2 fun b hb => ?_)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurableSet_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, SimpleFunc.map_const, ENNReal.coe_natCast,
      restrict_const_lintegral]
    refine ⟨indicator_le fun x hx => le_trans ?_ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]
/-
**MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_pos** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α -> Real>=0∞} (h : 
∫⁻ x, f x ∂μ != ∞) {ε : Real>=0∞} (hε : ε != 0) : exists φ : α ->ₛ Real>=0, (for
all x, ↑(φ x) <= f x) ∧ forall ψ : α ->ₛ Real>=0, (forall x, ↑(ψ x) <= f x) -> (
map (↑) (ψ - φ)).lintegral μ < ε
参数：h : ∫⁻ x, f x ∂μ != ∞；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_nnreal`：lintegral_eq_nnreal {m : MeasurableSp
ace α} (f : α -> Real>=0∞) (μ : Measure α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0
) (_ : forall x, ↑(φ x)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENNReal.biSup_add`：biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (
f : ι -> Real>=0∞) : (⨆ i in s, f i) + a = ⨆ i in s, f i + a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_lt_add_iff_left`：∀ {a b c : ENNReal}, a ≠ ⊤ → (a + b < a + c
 ↔ b < c)
· 使用定理 `MeasureTheory.SimpleFunc.add_lintegral`：add_lintegral (f g : α ->ₛ Real>
=0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ
· 使用定理 `MeasureTheory.SimpleFunc.map_add`：∀ {α : Type u_1} {β : Type u_2} {γ : T
ype u_3} [inst : MeasurableSpace α] [inst_1 : Add β] [inst_2 : Add γ] {g : β → γ
},   (∀ (x y : β), g (…
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_eq_max`：add_tsub_eq_max : a + (b - a) = max a b
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : α →ₛ ℝ≥0,
      (∀ x, ↑(φ x) ≤ f x) ∧
        ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) → (map (↑) (ψ - φ)).lintegral μ < ε := by
  rw [lintegral_eq_nnreal] at h
  have := ENNReal.lt_add_right h hε
  erw [ENNReal.biSup_add] at this <;> [skip; exact ⟨0, fun x => zero_le⟩]
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩
  refine ⟨φ, hle, fun ψ hψ => ?_⟩
  have : (map (↑) φ).lintegral μ ≠ ∞ := ne_top_of_le_ne_top h (by exact le_iSup₂ (α := ℝ≥0∞) φ hle)
  rw [← ENNReal.add_lt_add_iff_left this, ← add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
  refine (hb _ fun x => le_trans ?_ (max_le (hle x) (hψ x))).trans_lt hbφ
  simp only [SimpleFunc.add_apply, SimpleFunc.sub_apply, add_tsub_eq_max]
  rfl
/-
**MeasureTheory.iSup_lintegral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：iSup_lintegral_le {ι : Sort*} (f : ι -> α -> Real>=0∞) : ⨆ i, ∫⁻ a, f i a 
∂μ <= ∫⁻ a, ⨆ i, f i a ∂μ
参数：f : ι -> α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
· 使用定理 `MeasureTheory.monotone_lintegral`：monotone_lintegral {_ : MeasurableSpac
e α} (μ : Measure α) : Monotone (lintegral μ)
-/
theorem iSup_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ⨆ i, f i a ∂μ := by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup
/-
**MeasureTheory.iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by
  convert! (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]
/-
**MeasureTheory.le_iInf_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_iInf_lintegral {ι : Sort*} (f : ι -> α -> Real>=0∞) : ∫⁻ a, ⨅ i, f i a 
∂μ <= ⨅ i, ∫⁻ a, f i a ∂μ
参数：f : ι -> α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Monotone.map_iInf_le`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [in
st : CompleteLattice α] {s : ι → α} [inst_1 : CompleteLattice β]   {f : α → β}, 
Monotone f…
· 使用定理 `MeasureTheory.monotone_lintegral`：monotone_lintegral {_ : MeasurableSpac
e α} (μ : Measure α) : Monotone (lintegral μ)
-/
theorem le_iInf_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ ≤ ⨅ i, ∫⁻ a, f i a ∂μ := by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le
/-
**MeasureTheory.le_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by
  convert! (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]
/-
**MeasureTheory.lintegral_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mono_ae {f g : α -> Real>=0∞} (h : forallᵐ a ∂μ, f a <= g a) : ∫
⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
参数：h : forallᵐ a ∂μ, f a <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.restrict_apply`：restrict_apply (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) (a) : restrict f s a = indicator s f a
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_congr`：lintegral_congr {f g : α ->ₛ R
eal>=0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : ∀ᵐ x ∂μ, x ∉ t := measure_eq_zero_iff_ae_notMem.1 ht0
  rw [lintegral, lintegral]
  refine iSup₂_le fun s hfs ↦ le_iSup₂_of_le (s.restrict tᶜ) ?_ ?_
  · intro a
    by_cases h : a ∈ t <;>
      simp only [restrict_apply s ht.compl, mem_compl_iff, h, not_true, not_false_eq_true,
        indicator_of_notMem, zero_le, not_false_eq_true, indicator_of_mem]
    exact le_trans (hfs a) (by_contradiction fun hnfg => h (hts hnfg))
  · exact le_of_eq <| SimpleFunc.lintegral_congr <| this.mono fun a hnt => by
      simp [restrict_apply s ht.compl, hnt]

/-- Lebesgue integral over a set is monotone in function.

This version assumes that the upper estimate is an a.e. measurable function
and the estimate holds a.e. on the set.
See also `setLIntegral_mono_ae'` for a version that assumes measurability of the set
but assumes no regularity of either function. -/
/-
**MeasureTheory.setLIntegral_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_mono_ae {s : Set α} {f g : α -> Real>=0∞} (hg : AEMeasurable 
g (μ.restrict s)) (hfg : forallᵐ x ∂μ, x in s -> f x <= g x) : ∫⁻ x in s, f x ∂μ
 <= ∫⁻ x in s, g x ∂μ
参数：hg : AEMeasurable g (μ.restrict s)；hfg : forallᵐ x ∂μ, x in s -> f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_iff₀`：ae_restrict_iff₀ {p : α -> Prop} (hp : N
ullMeasurableSet { x | p x } (μ.restrict s)) : (forallᵐ x ∂μ.restrict s, p x) ↔ 
forallᵐ x ∂μ, x in s…
· 使用定理 `nullMeasurableSet_le`：nullMeasurableSet_le [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
Lebesgue integral over a set is monotone in function.

This version assumes that the upper estimate is an a.e. measurable function
and the estimate holds a.e. on the set.
See also `setLIntegral_mono_ae'` for a version that assumes measurability of the
 set
but assumes no regularity of either function.
-/
theorem setLIntegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.restrict s))
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ := by
  rcases exists_measurable_le_lintegral_eq (μ.restrict s) f with ⟨f', hf'm, hle, hf'⟩
  rw [hf']
  apply lintegral_mono_ae
  rw [ae_restrict_iff₀]
  · exact hfg.mono fun x hx hxs ↦ (hle x).trans (hx hxs)
  · exact nullMeasurableSet_le hf'm.aemeasurable hg
/-
**MeasureTheory.setLIntegral_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_mono {s : Set α} {f g : α -> Real>=0∞} (hg : Measurable g) (h
fg : forall x in s, f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s, g x ∂μ
参数：hg : Measurable g；hfg : forall x in s, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_mono_ae`：setLIntegral_mono_ae {s : Set α} {f 
g : α -> Real>=0∞} (hg : AEMeasurable g (μ.restrict s)) (hfg : forallᵐ x ∂μ, x i
n s -> f x <= g x) : ∫⁻ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setLIntegral_mono {s : Set α} {f g : α → ℝ≥0∞} (hg : Measurable g)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae hg.aemeasurable (ae_of_all _ hfg)
/-
**MeasureTheory.setLIntegral_mono_ae'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_mono_ae' {s : Set α} {f g : α -> Real>=0∞} (hs : MeasurableSe
t s) (hfg : forallᵐ x ∂μ, x in s -> f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s
, g x ∂μ
参数：hs : MeasurableSet s；hfg : forallᵐ x ∂μ, x in s -> f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setLIntegral_mono_ae' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff' hs).2 hfg
/-
**MeasureTheory.setLIntegral_mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_mono' {s : Set α} {f g : α -> Real>=0∞} (hs : MeasurableSet s
) (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x in s, g x ∂μ
参数：hs : MeasurableSet s；hfg : forall x in s, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_mono_ae'`：setLIntegral_mono_ae' {s : Set α} {
f g : α -> Real>=0∞} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s -> f x <
= g x) : ∫⁻ x in s, f x ∂…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setLIntegral_mono' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae' hs (ae_of_all _ hfg)
/-
**MeasureTheory.setLIntegral_le_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setLIntegral_le_lintegral (s : Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x
 ∂μ <= ∫⁻ x, f x ∂μ
参数：s : Set α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem setLIntegral_le_lintegral (s : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x, f x ∂μ :=
  lintegral_mono' Measure.restrict_le_self le_rfl
/-
**MeasureTheory.iInf_mul_le_setLIntegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：iInf_mul_le_setLIntegral (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableS
et s) : (⨅ x in s, f x) * μ s <= ∫⁻ x in s, f x ∂μ
参数：f : α -> Real>=0∞；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setLIntegral_mono'`：setLIntegral_mono' {s : Set α} {f g : 
α -> Real>=0∞} (hs : MeasurableSet s) (hfg : forall x in s, f x <= g x) : ∫⁻ x i
n s, f x ∂μ <= ∫⁻ x in…
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma iInf_mul_le_setLIntegral (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (⨅ x ∈ s, f x) * μ s ≤ ∫⁻ x in s, f x ∂μ := by
  calc (⨅ x ∈ s, f x) * μ s
  _ = ∫⁻ y in s, ⨅ x ∈ s, f x ∂μ := by simp
  _ ≤ ∫⁻ x in s, f x ∂μ := setLIntegral_mono' hs fun x hx ↦ iInf₂_le x hx
/-
**MeasureTheory.setLIntegral_le_iSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setLIntegral_le_iSup_mul (f : α -> Real>=0∞) {s : Set α} (hs : MeasurableS
et s) : ∫⁻ x in s, f x ∂μ <= (⨆ x in s, f x) * μ s
参数：f : α -> Real>=0∞；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_mono'`：setLIntegral_mono' {s : Set α} {f g : 
α -> Real>=0∞} (hs : MeasurableSet s) (hfg : forall x in s, f x <= g x) : ∫⁻ x i
n s, f x ∂μ <= ∫⁻ x in…
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_le_iSup_mul (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, f x ∂μ ≤ (⨆ x ∈ s, f x) * μ s := by
  calc ∫⁻ x in s, f x ∂μ
  _ ≤ ∫⁻ y in s, ⨆ x ∈ s, f x ∂μ :=
    setLIntegral_mono' hs fun x hx ↦ le_iSup₂ (f := fun x _ ↦ f x) x hx
  _ = (⨆ x ∈ s, f x) * μ s := by simp
/-
**MeasureTheory.lintegral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_congr_ae {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = 
∫⁻ a, g a ∂μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)
/-
**MeasureTheory.lintegral_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_congr {f g : α -> Real>=0∞} (h : forall a, f a = g a) : ∫⁻ a, f 
a ∂μ = ∫⁻ a, g a ∂μ
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  simp only [h]
/-
**MeasureTheory.setLIntegral_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_congr {f : α -> Real>=0∞} {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ 
x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
参数：h : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
-/
theorem setLIntegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by rw [Measure.restrict_congr_set h]
/-
**MeasureTheory.setLIntegral_congr_fun_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setLIntegral_congr_fun_ae {f g : α -> Real>=0∞} {s : Set α} (hs : Measurab
leSet s) (hfg : forallᵐ x ∂μ, x in s -> f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in
 s, g x ∂μ
参数：hs : MeasurableSet s；hfg : forallᵐ x ∂μ, x in s -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setLIntegral_congr_fun_ae {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  rw [lintegral_congr_ae]
  rw [EventuallyEq]
  rwa [ae_restrict_iff' hs]
/-
**MeasureTheory.setLIntegral_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setLIntegral_congr_fun {f g : α -> Real>=0∞} {s : Set α} (hs : MeasurableS
et s) (hfg : EqOn f g s) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ
参数：hs : MeasurableSet s；hfg : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setLIntegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : EqOn f g s) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
  setLIntegral_congr_fun_ae hs <| Eventually.of_forall hfg
/-
**MeasureTheory.setLIntegral_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_eq_zero {f : α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s
) (h's : EqOn f 0 s) : ∫⁻ x in s, f x ∂μ = 0
参数：hs : MeasurableSet s；h's : EqOn f 0 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_eq_zero {f : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (h's : EqOn f 0 s) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  simp [setLIntegral_congr_fun hs h's]

section

/-
**MeasureTheory.lintegral_eq_zero_of_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：lintegral_eq_zero_of_ae_eq_zero {f : α -> Real>=0∞} (h : f =ᵐ[μ] 0) : ∫⁻ a
, f a ∂μ = 0
参数：h : f =ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
-/
theorem lintegral_eq_zero_of_ae_eq_zero {f : α → ℝ≥0∞} (h : f =ᵐ[μ] 0) :
    ∫⁻ a, f a ∂μ = 0 :=
  (lintegral_congr_ae h).trans lintegral_zero

/-- The Lebesgue integral is zero iff the function is a.e. zero.

The measurability assumption is necessary, otherwise there are counterexamples: for instance, the
conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
/-
**MeasureTheory.lintegral_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_eq_zero_iff' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a,
 f a ∂μ = 0 ↔ f =ᵐ[μ] 0
参数：hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ENNReal.mul_pos`：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
· 使用定理 `MeasureTheory.setLIntegral_le_lintegral`：setLIntegral_le_lintegral (s : 
Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.setLIntegral_mono_ae`：setLIntegral_mono_ae {s : Set α} {f 
g : α -> Real>=0∞} (hg : AEMeasurable g (μ.restrict s)) (hfg : forallᵐ x ∂μ, x i
n s -> f x <= g x) : ∫⁻ …
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_rfl`：le_rfl : a <= a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The Lebesgue integral is zero iff the function is a.e. zero.

The measurability assumption is necessary, otherwise there are counterexamples: 
for instance, the
conclusion fails if `f` is the characteristic function of a Vitali set.
-/
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  -- The proof implicitly uses Markov's inequality,
  -- but it has been inlined for the sake of imports
  refine ⟨fun h ↦ ?_, lintegral_eq_zero_of_ae_eq_zero⟩
  have meas_levels_0 : ∀ ε > 0, μ { x | ε ≤ f x } = 0 := fun ε εpos ↦ by
    by_contra! h'
    refine ((ENNReal.mul_pos εpos.ne' h').trans_le ?_).ne' h
    calc
      _ ≥ ∫⁻ a in {x | ε ≤ f x}, f a ∂μ := setLIntegral_le_lintegral _ _
      _ ≥ ∫⁻ _ in {x | ε ≤ f x}, ε ∂μ :=
        setLIntegral_mono_ae hf.restrict (ae_of_all μ fun _ ↦ id)
      _ = _ := setLIntegral_const _ _
  obtain ⟨u, -, bu, tu⟩ := exists_seq_strictAnti_tendsto' (α := ℝ≥0∞) zero_lt_one
  have u_union : {x | f x ≠ 0} = ⋃ n, {x | u n ≤ f x} := by
    ext x
    rw [mem_iUnion, mem_ofPred_eq, ← pos_iff_ne_zero]
    rw [ENNReal.tendsto_atTop_zero] at tu
    constructor <;> intro h'
    · obtain ⟨n, hn⟩ := tu _ h'; use n, hn _ le_rfl
    · obtain ⟨n, hn⟩ := h'; exact (bu n).1.trans_le hn
  have res := measure_iUnion_null_iff.mpr fun n ↦ meas_levels_0 _ (bu n).1
  rwa [← u_union] at res

/-- The measurability assumption is necessary, otherwise there are counterexamples: for instance,
the conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
/-
**MeasureTheory.lintegral_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_eq_zero_iff {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a 
∂μ = 0 ↔ f =ᵐ[μ] 0
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
The measurability assumption is necessary, otherwise there are counterexamples: 
for instance,
the conclusion fails if `f` is the characteristic function of a Vitali set.
-/
theorem lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.aemeasurable

/-- The measurability assumption is necessary, otherwise there are counterexamples: for instance,
the conclusion fails if `s = univ` and `f` is the characteristic function of a Vitali set. -/
/-
**MeasureTheory.setLIntegral_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s) {f : α -> Rea
l>=0∞} (hf : AEMeasurable f (μ.restrict s)) : ∫⁻ a in s, f a ∂μ = 0 ↔ forallᵐ x 
∂μ, x in s -> f x = 0
参数：hs : MeasurableSet s；hf : AEMeasurable f (μ.restrict s)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x

--- 原说明 ---
The measurability assumption is necessary, otherwise there are counterexamples: 
for instance,
the conclusion fails if `s = univ` and `f` is the characteristic function of a V
itali set.
-/
theorem setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)
/-
**MeasureTheory.setLIntegral_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α -> Real
>=0∞} (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ forallᵐ x ∂μ, x in s -> f x 
= 0
参数：hs : MeasurableSet s；hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_eq_zero_iff'`：setLIntegral_eq_zero_iff' {s : 
Set α} (hs : MeasurableSet s) {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.restri
ct s)) : ∫⁻ a in s, f a ∂μ = …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  setLIntegral_eq_zero_iff' hs hf.aemeasurable
/-
**MeasureTheory.lintegral_pos_iff_support** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_pos_iff_support {f : α -> Real>=0∞} (hf : Measurable f) : (0 < ∫
⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f)
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]
/-
**MeasureTheory.setLIntegral_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_pos_iff {f : α -> Real>=0∞} (hf : Measurable f) {s : Set α} :
 0 < ∫⁻ a in s, f a ∂μ ↔ 0 < μ (Function.support f inter s)
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_pos_iff_support`：lintegral_pos_iff_support {f : 
α -> Real>=0∞} (hf : Measurable f) : (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.suppor
t f)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `measurableSet_support`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : 
MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Zero β]   [MeasurableSinglet
onClass β],…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem setLIntegral_pos_iff {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} :
    0 < ∫⁻ a in s, f a ∂μ ↔ 0 < μ (Function.support f ∩ s) := by
  rw [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf)]

end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states this fact in terms of `ε` and `δ`. -/
/-
**MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：exists_pos_setLIntegral_lt_of_measure_lt {f : α -> Real>=0∞} (h : ∫⁻ x, f 
x ∂μ != ∞) {ε : Real>=0∞} (hε : ε != 0) : exists δ > 0, forall s, μ s < δ -> ∫⁻ 
x in s, f x ∂μ < ε
参数：h : ∫⁻ x, f x ∂μ != ∞；hε : ε != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_pos`：exists_s
impleFunc_forall_lintegral_sub_lt_of_pos {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ !
= ∞) {ε : Real>=0∞} (hε : ε != 0) : exists φ : α ->ₛ…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.SimpleFunc.exists_forall_le`：exists_forall_le [Nonempty β]
 [Preorder β] [IsDirectedOrder β] (f : α ->ₛ β) : exists C, forall x, f x <= C
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `ENNReal.div_pos_iff`：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_nnreal`：lintegral_eq_nnreal {m : MeasurableSp
ace α} (f : α -> Real>=0∞) (μ : Measure α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0
) (_ : forall x, ↑(φ x)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.add_lintegral`：add_lintegral (f g : α ->ₛ Real>
=0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ
· 使用定理 `MeasureTheory.SimpleFunc.map_add`：∀ {α : Type u_1} {β : Type u_2} {γ : T
ype u_3} [inst : MeasurableSpace α] [inst_1 : Add β] [inst_2 : Add γ] {g : β → γ
},   (∀ (x y : β), g (…
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono`：lintegral_mono {f g : α ->ₛ Rea
l>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.lintegral μ <= g.lintegral ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_tsub_eq_max`：add_tsub_eq_max : a + (b - a) = max a b
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in
 `s`: it tends
to zero as `μ s` tends to zero. This lemma states this fact in terms of `ε` and 
`δ`.
-/
theorem exists_pos_setLIntegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε := by
  rcases exists_between (pos_iff_ne_zero.mpr hε) with ⟨ε₂, hε₂0, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simpleFunc_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, _, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine fun s hs => lt_of_le_of_lt ?_ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map (↑) ψ).lintegral (μ.restrict s) ≤
        (map (↑) φ).lintegral (μ.restrict s) + (map (↑) (ψ - φ)).lintegral (μ.restrict s) := by
      rw [← SimpleFunc.add_lintegral, ← SimpleFunc.map_add @ENNReal.coe_add]
      refine SimpleFunc.lintegral_mono (fun x => ?_) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, SimpleFunc.coe_add,
        SimpleFunc.coe_sub, Pi.add_apply, Pi.sub_apply, ENNReal.coe_max (φ x) (ψ x)]
    _ ≤ (map (↑) φ).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      refine le_trans ?_ (hφ _ hψ).le
      exact SimpleFunc.lintegral_mono le_rfl Measure.restrict_le_self
    _ ≤ (SimpleFunc.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ := by
      gcongr
      exact fun x ↦ ENNReal.coe_le_coe.2 (hC x)
    _ = C * μ s + ε₁ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral, coe_const, lintegral_const,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter, Function.const]
    _ ≤ C * ((ε₂ - ε₁) / C) + ε₁ := by gcongr
    _ ≤ ε₂ - ε₁ + ε₁ := by gcongr; apply mul_div_le
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
/-
**MeasureTheory.tendsto_setLIntegral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_setLIntegral_zero {ι} {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) 
{l : Filter ι} {s : ι -> Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) : Tendsto (fun i 
=> ∫⁻ x in s i, f x ∂μ) l (𝓝 0)
参数：h : ∫⁻ x, f x ∂μ != ∞；hl : Tendsto (μ ∘ s) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.nhds_zero`：nhds_zero : 𝓝 (0 : Real>=0∞) = ⨅ (a) (_ : a != 0), 𝓟 
(Iio a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt`：exists_pos_setLI
ntegral_lt_of_measure_lt {f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {ε : Real>=
0∞} (hε : ε != 0) : exists δ > 0, forall s, …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in
 `s`: it tends
to zero as `μ s` tends to zero.
-/
theorem tendsto_setLIntegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {l : Filter ι}
    {s : ι → Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x in s i, f x ∂μ) l (𝓝 0) := by
  simp only [ENNReal.nhds_zero, tendsto_iInf, tendsto_principal, mem_Iio,
    ← pos_iff_ne_zero] at hl ⊢
  intro ε ε0
  rcases exists_pos_setLIntegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _

@[simp]
/-
**MeasureTheory.lintegral_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real
>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂c • μ = c • ∫⁻ a, f a ∂μ
参数：c : R；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_smul`：lintegral_smul {R : Type*} [SMu
l R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (f : α ->ₛ Real>=0∞) (c : R) :
 f.lintegral (c • μ) = c • f.…
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用引理 `ENNReal.smul_iSup`：smul_iSup {R} [SMul R Real>=0∞] [IsScalarTower R Real
>=0∞ Real>=0∞] (f : ι -> Real>=0∞) (c : R) : c • ⨆ i, f i = ⨆ i, c • f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂c • μ = c • ∫⁻ a, f a ∂μ := by
  simp only [lintegral, iSup_subtype', SimpleFunc.lintegral_smul, ENNReal.smul_iSup]
/-
**MeasureTheory.setLIntegral_smul_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setLIntegral_smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R R
eal>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0∞) (s : Set α) : ∫⁻ a in s, f a ∂(c •
 μ) = c • ∫⁻ a in s, f a ∂μ
参数：c : R；f : α -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_smul`：restrict_smul {_m0 : MeasurableSpac
e α} {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (
μ : Measure α) (s : Set α…
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
-/
lemma setLIntegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂(c • μ) = c • ∫⁻ a in s, f a ∂μ := by
  rw [Measure.restrict_smul, lintegral_smul_measure]

@[simp]
/-
**MeasureTheory.lintegral_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_zero_measure {m : MeasurableSpace α} (f : α -> Real>=0∞) : ∫⁻ a,
 f a ∂(0 : Measure α) = 0
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_zero`：lintegral_zero [MeasurableSpace
 α] (f : α ->ₛ Real>=0∞) : f.lintegral 0 = 0
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(0 : Measure α) = 0 := by
  simp [lintegral]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MeasureTheory.lintegral_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_measure (f : α -> Real>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(
μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
参数：f : α -> Real>=0∞；μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_add`：lintegral_add {ν} (f : α ->ₛ Rea
l>=0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.iSup_add_iSup`：iSup_add_iSup (h : forall i j, exists k, f i + g 
j <= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono`：lintegral_mono {f g : α ->ₛ Rea
l>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.lintegral μ <= g.lintegral ν
· 使用定理 `Subtype.coe_le_coe._gcongr_2`：∀ {α : Type u_2} [inst : LE α] {p : α → Pr
op} {x y : Subtype p}, x ≤ y → ↑x ≤ ↑y
· 使用定理 `Subtype.mk_le_mk._gcongr_1`：∀ {α : Type u_2} [inst : LE α] {p : α → Prop
} {x y : α} {hx : p x} {hy : p y}, x ≤ y → ⟨x, hx⟩ ≤ ⟨y, hy⟩
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem lintegral_add_measure (f : α → ℝ≥0∞) (μ ν : Measure α) :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simp only [lintegral, SimpleFunc.lintegral_add, iSup_subtype']
  refine (ENNReal.iSup_add_iSup ?_).symm
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
  refine ⟨⟨φ ⊔ ψ, sup_le hφ hψ⟩, ?_⟩
  gcongr
  exacts [le_sup_left, le_sup_right]

@[simp]
/-
**MeasureTheory.lintegral_finsetSum_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lintegral_finsetSum_measure {ι} (s : Finset ι) (f : α -> Real>=0∞) (μ : ι 
-> Measure α) : ∫⁻ a, f a ∂(∑ i in s, μ i) = ∑ i in s, ∫⁻ a, f a ∂μ i
参数：s : Finset ι；f : α -> Real>=0∞；μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem lintegral_finsetSum_measure {ι} (s : Finset ι) (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫⁻ a, f a ∂μ i :=
  let F : Measure α →+ ℝ≥0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_sum F μ s

@[deprecated (since := "2026-04-08")]
alias lintegral_finset_sum_measure := lintegral_finsetSum_measure

@[simp]
/-
**MeasureTheory.lintegral_sum_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α -> Real>=0∞) (μ :
 ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i
参数：f : α -> Real>=0∞；μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_eq_iSup_sum`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α)
, f a = ⨆ s, ∑ a ∈ s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_sum`：lintegral_sum {m : MeasurableSpa
ce α} {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> Measure α) : f.lintegral (Measure.sum μ
) = ∑' i, f.lintegral (μ i)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_finsetSum`：lintegral_finsetSum {ι} (f
 : α ->ₛ Real>=0∞) (μ : ι -> Measure α) (s : Finset ι) : f.lintegral (∑ i in s, 
μ i) = ∑ i in s, f.lintegral (μ i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum, ← lintegral_finsetSum_measure,
    lintegral, SimpleFunc.lintegral_sum, ENNReal.tsum_eq_iSup_sum,
    SimpleFunc.lintegral_finsetSum, iSup_comm (ι := Finset ι)]
/-
**MeasureTheory.hasSum_lintegral_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：hasSum_lintegral_measure {ι} {_ : MeasurableSpace α} (f : α -> Real>=0∞) (
μ : ι -> Measure α) : HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ
)
参数：f : α -> Real>=0∞；μ : ι -> Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
-/
theorem hasSum_lintegral_measure {ι} {_ : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ) :=
  (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum

@[simp]
/-
**MeasureTheory.lintegral_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (
f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = 0
参数：μ : Measure α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
-/
theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by
  have : Subsingleton (Measure α) := inferInstance
  convert! lintegral_zero_measure f
/-
**MeasureTheory.setLIntegral_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_empty (f : α -> Real>=0∞) : ∫⁻ x in ∅, f x ∂μ = 0
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
-/
theorem setLIntegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, lintegral_zero_measure]
/-
**MeasureTheory.setLIntegral_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_univ (f : α -> Real>=0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂
μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem setLIntegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [Measure.restrict_univ]
/-
**MeasureTheory.setLIntegral_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setLIntegral_measure_zero (s : Set α) (f : α -> Real>=0∞) (hs' : μ s = 0) 
: ∫⁻ x in s, f x ∂μ = 0
参数：s : Set α；f : α -> Real>=0∞；hs' : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
-/
theorem setLIntegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by
  convert! lintegral_zero_measure _
  exact Measure.restrict_eq_zero.2 hs'

-- TODO: Need a better way of rewriting inside of an integral
/-
**MeasureTheory.lintegral_rw** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
    ∫⁻ a, g (f a) ∂μ = ∫⁻ a, g (f' a) ∂μ :=
  lintegral_congr_ae <| h.mono fun a h => by dsimp only; rw [h]

-- TODO: Need a better way of rewriting inside of an integral
/-
**MeasureTheory.lintegral_rw** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β → γ → ℝ≥0∞) : ∫⁻ a, g (f₁ a) (f₂ a) ∂μ = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae <| h₁.mp <| h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]
/-
**MeasureTheory.lintegral_indicator_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_indicator_le (f : α -> Real>=0∞) (s : Set α) : ∫⁻ a, s.indicator
 f a ∂μ <= ∫⁻ a in s, f a ∂μ
参数：f : α -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.indicator_le_self`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoid
 M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] (s : Set α)   (f : α → M
), s.indica…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_restrict`：lintegral_restrict {m : Mea
surableSpace α} (f : α ->ₛ Real>=0∞) (s : Set α) (μ : Measure α) : f.lintegral (
μ.restrict s) = ∑ y in f.range, y…
· 使用定理 `MeasureTheory.SimpleFunc.lintegral.eq_1`：∀ {α : Type u_1} {_m : Measurab
leSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Measure α
),   f.lintegral μ = ∑ x ∈ f.…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem lintegral_indicator_le (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a, s.indicator f a ∂μ ≤ ∫⁻ a in s, f a ∂μ := by
  simp only [lintegral]
  apply iSup_le (fun g ↦ (iSup_le (fun hg ↦ ?_)))
  have : g ≤ f := hg.trans (indicator_le_self s f)
  refine le_iSup_of_le g (le_iSup_of_le this (le_of_eq ?_))
  rw [lintegral_restrict, SimpleFunc.lintegral]
  congr with t
  by_cases H : t = 0
  · simp [H]
  congr with x
  simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, iff_self_and]
  rintro rfl
  contrapose H
  simpa [H] using hg x

@[simp]
/-
**MeasureTheory.lintegral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
 : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ
参数：hs : MeasurableSet s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_indicator_le`：lintegral_indicator_le (f : α -> R
eal>=0∞) (s : Set α) : ∫⁻ a, s.indicator f a ∂μ <= ∫⁻ a in s, f a ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict`：restr
ict_lintegral_eq_lintegral_restrict (f : α ->ₛ Real>=0∞) {s : Set α} (hs : Measu
rableSet s) : (restrict f s).lintegral μ = f.lintegral …
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  apply le_antisymm (lintegral_indicator_le f s)
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  refine iSup_mono' (Subtype.forall.2 fun φ hφ => ?_)
  refine ⟨⟨φ.restrict s, fun x => ?_⟩, le_rfl⟩
  simp [hφ x, hs, indicator_le_indicator]
/-
**MeasureTheory.setLIntegral_indicator** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：setLIntegral_indicator {s t : Set α} (hs : MeasurableSet s) (f : α -> Real
>=0∞) : ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s inter t, f a ∂μ
参数：hs : MeasurableSet s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
-/
lemma setLIntegral_indicator {s t : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [lintegral_indicator hs, Measure.restrict_restrict hs]
/-
**MeasureTheory.lintegral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α -> Real>=0∞)
 : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ
参数：hs : MeasurableSet s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_indicator_le`：lintegral_indicator_le (f : α -> R
eal>=0∞) (s : Set α) : ∫⁻ a, s.indicator f a ∂μ <= ∫⁻ a in s, f a ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict`：restr
ict_lintegral_eq_lintegral_restrict (f : α ->ₛ Real>=0∞) {s : Set α} (hs : Measu
rableSet s) : (restrict f s).lintegral μ = f.lintegral …
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lintegral_indicator₀ {s : Set α} (hs : NullMeasurableSet s μ) (f : α → ℝ≥0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    lintegral_indicator (measurableSet_toMeasurable _ _),
    Measure.restrict_congr_set hs.toMeasurable_ae_eq]
/-
**MeasureTheory.setLIntegral_indicator** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：setLIntegral_indicator {s t : Set α} (hs : MeasurableSet s) (f : α -> Real
>=0∞) : ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s inter t, f a ∂μ
参数：hs : MeasurableSet s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
-/
lemma setLIntegral_indicator₀ (f : α → ℝ≥0∞) {s t : Set α}
    (hs : NullMeasurableSet s (μ.restrict t)) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by
  rw [lintegral_indicator₀ hs, Measure.restrict_restrict₀ hs]
/-
**MeasureTheory.lintegral_indicator_const_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lintegral_indicator_const_le (s : Set α) (c : Real>=0∞) : ∫⁻ a, s.indicato
r (fun _ => c) a ∂μ <= c * μ s
参数：s : Set α；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_indicator_le`：lintegral_indicator_le (f : α -> R
eal>=0∞) (s : Set α) : ∫⁻ a, s.indicator f a ∂μ <= ∫⁻ a in s, f a ∂μ
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
-/
theorem lintegral_indicator_const_le (s : Set α) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ ≤ c * μ s :=
  (lintegral_indicator_le _ _).trans (setLIntegral_const s c).le
/-
**MeasureTheory.lintegral_indicator_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : Real>=0∞
) : ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s
参数：hs : MeasurableSet s；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_indicator_const₀`：lintegral_indicator_const₀ {s 
: Set α} (hs : NullMeasurableSet s μ) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ 
=> c) a ∂μ = c * μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem lintegral_indicator_const₀ {s : Set α} (hs : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s := by
  rw [lintegral_indicator₀ hs, setLIntegral_const]
/-
**MeasureTheory.lintegral_indicator_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : Real>=0∞
) : ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s
参数：hs : MeasurableSet s；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_indicator_const₀`：lintegral_indicator_const₀ {s 
: Set α} (hs : NullMeasurableSet s μ) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ 
=> c) a ∂μ = c * μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const₀ hs.nullMeasurableSet c
/-
**MeasureTheory.setLIntegral_eq_of_support_subset** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：setLIntegral_eq_of_support_subset {s : Set α} {f : α -> Real>=0∞} (hsf : f
.support subseteq s) : ∫⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂μ
参数：hsf : f.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.setLIntegral_le_lintegral`：setLIntegral_le_lintegral (s : 
Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `MeasureTheory.lintegral_indicator_le`：lintegral_indicator_le (f : α -> R
eal>=0∞) (s : Set α) : ∫⁻ a, s.indicator f a ∂μ <= ∫⁻ a in s, f a ∂μ
-/
lemma setLIntegral_eq_of_support_subset {s : Set α} {f : α → ℝ≥0∞} (hsf : f.support ⊆ s) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂μ := by
  apply le_antisymm (setLIntegral_le_lintegral s fun x ↦ f x)
  apply le_trans (le_of_eq _) (lintegral_indicator_le _ _)
  congr with x
  simp only [indicator]
  split_ifs with h
  · rfl
  · exact Function.support_subset_iff'.1 hsf x h
/-
**MeasureTheory.setLIntegral_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_eq_const {f : α -> Real>=0∞} (hf : Measurable f) (r : Real>=0
∞) : ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r }
参数：hf : Measurable f；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem setLIntegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
    ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r } := by
  have : ∀ x ∈ { x | f x = r }, f x = r := fun _ hx => hx
  rw [setLIntegral_congr_fun _ this]
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  · exact hf (measurableSet_singleton r)

@[to_fun lintegral_indicator_fun_one_le]
/-
**MeasureTheory.lintegral_indicator_one_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lintegral_indicator_one_le (s : Set α) : ∫⁻ a, s.indicator 1 a ∂μ <= μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_indicator_const_le`：lintegral_indicator_const_le
 (s : Set α) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ => c) a ∂μ <= c * μ s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem lintegral_indicator_one_le (s : Set α) : ∫⁻ a, s.indicator 1 a ∂μ ≤ μ s :=
  (lintegral_indicator_const_le _ _).trans <| (one_mul _).le

@[to_fun (attr := simp) lintegral_indicator_fun_one₀]
/-
**MeasureTheory.lintegral_indicator_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：lintegral_indicator_one {s : Set α} (hs : MeasurableSet s) : ∫⁻ a, s.indic
ator 1 a ∂μ = μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_indicator_one₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
  (lintegral_indicator_const₀ hs _).trans <| one_mul _

@[to_fun lintegral_indicator_fun_one]
/-
**MeasureTheory.lintegral_indicator_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：lintegral_indicator_one {s : Set α} (hs : MeasurableSet s) : ∫⁻ a, s.indic
ator 1 a ∂μ = μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_indicator_one {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s := by
  simp [hs]
/-
**MeasureTheory.Measure.ext_iff_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} (ν 
: MeasureTheory.Measure α),   μ = ν ↔ ∀ (f : α → ENNReal), Measurable f → ∫⁻ (a 
: α), f a ∂μ = ∫⁻ (a : α), f a ∂ν
参数：ν : MeasureTheory.Measure α；f : α → ENNReal；a : α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `measurable_indicator_const_iff`：measurable_indicator_const_iff [Zero β] 
[MeasurableSingletonClass β] (b : β) [NeZero b] : Measurable (s.indicator (fun (
_ : α) => b)) ↔ Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem Measure.ext_iff_lintegral (ν : Measure α) :
    μ = ν ↔ ∀ f : α → ℝ≥0∞, Measurable f → ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν := by
  refine ⟨fun h _ _ ↦ by rw [h], ?_⟩
  intro h
  ext s hs
  simp only [← lintegral_indicator_one hs]
  exact h (s.indicator 1) ((measurable_indicator_const_iff 1).mpr hs)
/-
**MeasureTheory.Measure.ext_of_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} (ν 
: MeasureTheory.Measure α),   (∀ (f : α → ENNReal), Measurable f → ∫⁻ (a : α), f
 a ∂μ = ∫⁻ (a : α), f a ∂ν) → μ = ν
参数：ν : MeasureTheory.Measure α；∀ (f : α → ENNReal), Measurable f → ∫⁻ (a : α), f
 a ∂μ = ∫⁻ (a : α), f a ∂ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.ext_iff_lintegral`：∀ {α : Type u_1} {m : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} (ν : MeasureTheory.Measure α),   μ = ν ↔
 ∀ (f : α → ENNReal), Measura…
-/
theorem Measure.ext_of_lintegral (ν : Measure α)
    (hμν : ∀ f : α → ℝ≥0∞, Measurable f → ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν) : μ = ν :=
  (μ.ext_iff_lintegral ν).mpr hμν

open Measure

open scoped Function -- required for scoped `on` notation
/-
**MeasureTheory.lintegral_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iUnion [Countable β] {s : β -> Set α} (hm : forall i, Measurable
Set (s i)) (hd : Pairwise (Disjoint on s)) (f : α -> Real>=0∞) : ∫⁻ a in ⋃ i, s 
i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ
参数：hm : forall i, MeasurableSet (s i)；hd : Pairwise (Disjoint on s)；f : α -> Rea
l>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_iUnion₀`：lintegral_iUnion₀ [Countable β] {s : β 
-> Set α} (hm : forall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint 
μ on s)) (f : α -> Re…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Pairwise.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {f : ι → Set α},   Pairwise (Function.onFun D
isjoint f…
-/
theorem lintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ := by
  simp only [Measure.restrict_iUnion_ae hd hm, lintegral_sum_measure]
/-
**MeasureTheory.lintegral_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iUnion [Countable β] {s : β -> Set α} (hm : forall i, Measurable
Set (s i)) (hd : Pairwise (Disjoint on s)) (f : α -> Real>=0∞) : ∫⁻ a in ⋃ i, s 
i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ
参数：hm : forall i, MeasurableSet (s i)；hd : Pairwise (Disjoint on s)；f : α -> Rea
l>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_iUnion₀`：lintegral_iUnion₀ [Countable β] {s : β 
-> Set α} (hm : forall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint 
μ on s)) (f : α -> Re…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Pairwise.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {f : ι → Set α},   Pairwise (Function.onFun D
isjoint f…
-/
theorem lintegral_iUnion [Countable β] {s : β → Set α} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
  lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f
/-
**MeasureTheory.lintegral_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_biUnion {t : Set β} {s : β -> Set α} (ht : t.Countable) (hm : fo
rall i in t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α -> Real>=0∞
) : ∫⁻ a in ⋃ i in t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ
参数：ht : t.Countable；hm : forall i in t, MeasurableSet (s i)；hd : t.PairwiseDisjo
int s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_biUnion₀`：lintegral_biUnion₀ {t : Set β} {s : β 
-> Set α} (ht : t.Countable) (hm : forall i in t, NullMeasurableSet (s i) μ) (hd
 : t.Pairwise (AEDisjo…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
-/
theorem lintegral_biUnion₀ {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, NullMeasurableSet (s i) μ) (hd : t.Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ := by
  have := ht.toEncodable
  rw [biUnion_eq_iUnion, lintegral_iUnion₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]
/-
**MeasureTheory.lintegral_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_biUnion {t : Set β} {s : β -> Set α} (ht : t.Countable) (hm : fo
rall i in t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α -> Real>=0∞
) : ∫⁻ a in ⋃ i in t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ
参数：ht : t.Countable；hm : forall i in t, MeasurableSet (s i)；hd : t.PairwiseDisjo
int s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_biUnion₀`：lintegral_biUnion₀ {t : Set β} {s : β 
-> Set α} (ht : t.Countable) (hm : forall i in t, NullMeasurableSet (s i) μ) (hd
 : t.Pairwise (AEDisjo…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
-/
theorem lintegral_biUnion {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f
/-
**MeasureTheory.lintegral_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lintegral_biUnion_finset {s : Finset β} {t : β -> Set α} (hd : Set.Pairwis
eDisjoint (↑s) t) (hm : forall b in s, MeasurableSet (t b)) (f : α -> Real>=0∞) 
: ∫⁻ a in ⋃ b in s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ
参数：hd : Set.PairwiseDisjoint (↑s) t；hm : forall b in s, MeasurableSet (t b)；f : 
α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_biUnion_finset₀`：lintegral_biUnion_finset₀ {s : 
Finset β} {t : β -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : fo
rall b in s, NullMeasurableSe…
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem lintegral_biUnion_finset₀ {s : Finset β} {t : β → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : ∀ b ∈ s, NullMeasurableSet (t b) μ)
    (f : α → ℝ≥0∞) : ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ := by
  simp only [← Finset.mem_coe, lintegral_biUnion₀ s.countable_toSet hm hd, ← Finset.tsum_subtype']
/-
**MeasureTheory.lintegral_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lintegral_biUnion_finset {s : Finset β} {t : β -> Set α} (hd : Set.Pairwis
eDisjoint (↑s) t) (hm : forall b in s, MeasurableSet (t b)) (f : α -> Real>=0∞) 
: ∫⁻ a in ⋃ b in s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ
参数：hd : Set.PairwiseDisjoint (↑s) t；hm : forall b in s, MeasurableSet (t b)；f : 
α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_biUnion_finset₀`：lintegral_biUnion_finset₀ {s : 
Finset β} {t : β -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : fo
rall b in s, NullMeasurableSe…
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem lintegral_biUnion_finset {s : Finset β} {t : β → Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : ∀ b ∈ s, MeasurableSet (t b)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f
/-
**MeasureTheory.lintegral_iUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iUnion_le [Countable β] (s : β -> Set α) (f : α -> Real>=0∞) : ∫
⁻ a in ⋃ i, s i, f a ∂μ <= ∑' i, ∫⁻ a in s i, f a ∂μ
参数：s : β -> Set α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_le`：restrict_iUnion_le [Countable 
ι] {s : ι -> Set α} : μ.restrict (⋃ i, s i) <= sum fun i => μ.restrict (s i)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ := by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_iUnion_le le_rfl
/-
**MeasureTheory.lintegral_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_union {f : α -> Real>=0∞} {A B : Set α} (hB : MeasurableSet B) (
hAB : Disjoint A B) : ∫⁻ a in A union B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B,
 f a ∂μ
参数：hB : MeasurableSet B；hAB : Disjoint A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_union`：restrict_union (h : Disjoint s t) 
(ht : MeasurableSet t) : μ.restrict (s union t) = μ.restrict s + μ.restrict t
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
-/
theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ := by
  rw [restrict_union hAB hB, lintegral_add_measure]
/-
**MeasureTheory.lintegral_union_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_union_le (f : α -> Real>=0∞) (s t : Set α) : ∫⁻ a in s union t, 
f a ∂μ <= ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ
参数：f : α -> Real>=0∞；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_union_le`：restrict_union_le (s s' : Set α
) : μ.restrict (s union s') <= μ.restrict s + μ.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lintegral_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∫⁻ a in s ∪ t, f a ∂μ ≤ ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ := by
  rw [← lintegral_add_measure]
  exact lintegral_mono' (restrict_union_le _ _) le_rfl
/-
**MeasureTheory.lintegral_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_inter_add_sdiff {B : Set α} (f : α -> Real>=0∞) (A : Set α) (hB 
: MeasurableSet B) : ∫⁻ x in A inter B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in
 A, f x ∂μ
参数：f : α -> Real>=0∞；A : Set α；hB : MeasurableSet B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_inter_add_sdiff`：restrict_inter_add_sdiff
 (s : Set α) (ht : MeasurableSet t) : μ.restrict (s inter t) + μ.restrict (s \ t
) = μ.restrict s
-/
theorem lintegral_inter_add_sdiff {B : Set α} (f : α → ℝ≥0∞) (A : Set α) (hB : MeasurableSet B) :
    ∫⁻ x in A ∩ B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ := by
  rw [← lintegral_add_measure, restrict_inter_add_sdiff _ hB]

@[deprecated (since := "2026-06-03")] alias lintegral_inter_add_diff := lintegral_inter_add_sdiff
/-
**MeasureTheory.lintegral_add_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_compl (f : α -> Real>=0∞) {A : Set α} (hA : MeasurableSet A)
 : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ
参数：f : α -> Real>=0∞；hA : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_add_restrict_compl`：restrict_add_restrict
_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict sᶜ = μ
-/
theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_add_measure, Measure.restrict_add_restrict_compl hA]
/-
**MeasureTheory.lintegral_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_piecewise (hs : MeasurableSet s) (f g : α -> Real>=0∞) [forall j
, Decidable (j in s)] : ∫⁻ a, s.piecewise f g a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in
 sᶜ, g a ∂μ
参数：hs : MeasurableSet s；f g : α -> Real>=0∞；j in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_compl`：lintegral_add_compl (f : α -> Real>=0
∞) {A : Set α} (hA : MeasurableSet A) : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ =
 ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
-/
lemma lintegral_piecewise (hs : MeasurableSet s) (f g : α → ℝ≥0∞) [∀ j, Decidable (j ∈ s)] :
    ∫⁻ a, s.piecewise f g a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in sᶜ, g a ∂μ := by
  rw [← lintegral_add_compl _ hs]
  congr 1
  · exact setLIntegral_congr_fun hs <| fun _ ↦ Set.piecewise_eq_of_mem _ _ _
  · exact setLIntegral_congr_fun hs.compl <| fun _ ↦ Set.piecewise_eq_of_notMem _ _ _
/-
**MeasureTheory.setLIntegral_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_compl {f : α -> Real>=0∞} {s : Set α} (hsm : MeasurableSet s)
 (hfs : ∫⁻ x in s, f x ∂μ != ∞) : ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ - ∫⁻ x in s,
 f x ∂μ
参数：hsm : MeasurableSet s；hfs : ∫⁻ x in s, f x ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_compl`：lintegral_add_compl (f : α -> Real>=0
∞) {A : Set α} (hA : MeasurableSet A) : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ =
 ∫⁻ x, f x ∂μ
· 使用定理 `ENNReal.add_sub_cancel_left`：∀ {a b : ENNReal}, a ≠ ⊤ → a + b - a = b
-/
theorem setLIntegral_compl {f : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hfs : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ - ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_add_compl (μ := μ) f hsm, ENNReal.add_sub_cancel_left hfs]
/-
**MeasureTheory.setLIntegral_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：setLIntegral_iUnion_of_directed {ι : Type*} [Countable ι] (f : α -> Real>=
0∞) {s : ι -> Set α} (hd : Directed (· subseteq ·) s) : ∫⁻ x in ⋃ i, s i, f x ∂μ
 = ⨆ i, ∫⁻ x in s i, f x ∂μ
参数：f : α -> Real>=0∞；hd : Directed (· subseteq ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_restrict_iUnion_of_directed`：lintegra
l_restrict_iUnion_of_directed {ι : Type*} [Countable ι] (f : α ->ₛ Real>=0∞) {s 
: ι -> Set α} (hd : Directed (· subseteq ·) s) (μ : …
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLIntegral_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α → ℝ≥0∞) {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    ∫⁻ x in ⋃ i, s i, f x ∂μ = ⨆ i, ∫⁻ x in s i, f x ∂μ := by
  simp only [lintegral_def, iSup_comm (ι := ι),
    SimpleFunc.lintegral_restrict_iUnion_of_directed _ hd]
/-
**MeasureTheory.lintegral_max** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_max {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurable g
) : ∫⁻ x, max (f x) (g x) ∂μ = ∫⁻ x in { x | f x <= g x }, g x ∂μ + ∫⁻ x in { x 
| g x < f x }, f x ∂μ
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_compl`：lintegral_add_compl (f : α -> Real>=0
∞) {A : Set α} (hA : MeasurableSet A) : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ =
 ∫⁻ x, f x ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, max (f x) (g x) ∂μ =
      ∫⁻ x in { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in { x | g x < f x }, f x ∂μ := by
  have hm : MeasurableSet { x | f x ≤ g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_ofPred, ← not_le]
  refine congr_arg₂ (· + ·) (setLIntegral_congr_fun hm ?_) (setLIntegral_congr_fun hm.compl ?_)
  exacts [fun x => max_eq_right (a := f x) (b := g x),
    fun x (hx : ¬ f x ≤ g x) => max_eq_left (not_le.1 hx).le]
/-
**MeasureTheory.setLIntegral_max** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_max {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurabl
e g) (s : Set α) : ∫⁻ x in s, max (f x) (g x) ∂μ = ∫⁻ x in s inter { x | f x <= 
g x }, g x ∂μ + ∫⁻ x in s inter { x | g x < f x }, f x ∂μ
参数：hf : Measurable f；hg : Measurable g；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_max`：lintegral_max {f g : α -> Real>=0∞} (hf : M
easurable f) (hg : Measurable g) : ∫⁻ x, max (f x) (g x) ∂μ = ∫⁻ x in { x | f x 
<= g x }, g x ∂μ …
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem setLIntegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    ∫⁻ x in s, max (f x) (g x) ∂μ =
      ∫⁻ x in s ∩ { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in s ∩ { x | g x < f x }, f x ∂μ := by
  rw [lintegral_max hf hg, restrict_restrict, restrict_restrict, inter_comm s, inter_comm s]
  exacts [measurableSet_lt hg hf, measurableSet_le hf hg]

/-- Lebesgue integral of a bounded function over a set of finite measure is finite.
Note that this lemma assumes no regularity of either `f` or `s`. -/
/-
**MeasureTheory.setLIntegral_lt_top_of_le_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：setLIntegral_lt_top_of_le_nnreal {s : Set α} (hs : μ s != ∞) {f : α -> Rea
l>=0∞} (hbdd : exists y : Real>=0, forall x in s, f x <= y) : ∫⁻ x in s, f x ∂μ 
< ∞
参数：hs : μ s != ∞；hbdd : exists y : Real>=0, forall x in s, f x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.setLIntegral_mono`：setLIntegral_mono {s : Set α} {f g : α 
-> Real>=0∞} (hg : Measurable g) (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, 
f x ∂μ <= ∫⁻ x in s, …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤

--- 原说明 ---
Lebesgue integral of a bounded function over a set of finite measure is finite.
Note that this lemma assumes no regularity of either `f` or `s`.
-/
theorem setLIntegral_lt_top_of_le_nnreal {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0∞}
    (hbdd : ∃ y : ℝ≥0, ∀ x ∈ s, f x ≤ y) : ∫⁻ x in s, f x ∂μ < ∞ := by
  obtain ⟨M, hM⟩ := hbdd
  refine lt_of_le_of_lt (setLIntegral_mono measurable_const hM) ?_
  simp [ENNReal.mul_lt_top, hs.lt_top]

/-- Lebesgue integral of a bounded function over a set of finite measure is finite.
Note that this lemma assumes no regularity of either `f` or `s`. -/
/-
**MeasureTheory.setLIntegral_lt_top_of_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：setLIntegral_lt_top_of_bddAbove {s : Set α} (hs : μ s != ∞) {f : α -> Real
>=0} (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞
参数：hs : μ s != ∞；hbdd : BddAbove (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_lt_top_of_le_nnreal`：setLIntegral_lt_top_of_l
e_nnreal {s : Set α} (hs : μ s != ∞) {f : α -> Real>=0∞} (hbdd : exists y : Real
>=0, forall x in s, f x <= y) : ∫⁻ x…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
Lebesgue integral of a bounded function over a set of finite measure is finite.
Note that this lemma assumes no regularity of either `f` or `s`.
-/
theorem setLIntegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_le_nnreal hs <| hbdd.imp fun _M hM _x hx ↦
    ENNReal.coe_le_coe.2 <| hM (mem_image_of_mem f hx)
/-
**MeasureTheory.setLIntegral_lt_top_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：setLIntegral_lt_top_of_isCompact [TopologicalSpace α] {s : Set α} (hs : μ 
s != ∞) (hsc : IsCompact s) {f : α -> Real>=0} (hf : Continuous f) : ∫⁻ x in s, 
f x ∂μ < ∞
参数：hs : μ s != ∞；hsc : IsCompact s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_lt_top_of_bddAbove`：setLIntegral_lt_top_of_bd
dAbove {s : Set α} (hs : μ s != ∞) {f : α -> Real>=0} (hbdd : BddAbove (f '' s))
 : ∫⁻ x in s, f x ∂μ < ∞
· 使用定理 `IsCompact.bddAbove`：IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddAbove s
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
-/
theorem setLIntegral_lt_top_of_isCompact [TopologicalSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : Continuous f) :
    ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_bddAbove hs (hsc.image hf).bddAbove

end MeasureTheory

