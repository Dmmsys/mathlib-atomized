/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Map

/-!
# Absolute Continuity of Measures

We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
if `ν(A) = 0` implies that `μ(A) = 0`. We denote that by `μ ≪ ν`.

It is equivalent to an inequality of the almost everywhere filters of the measures:
`μ ≪ ν ↔ ae μ ≤ ae ν`.

## Main definitions

* `MeasureTheory.Measure.AbsolutelyContinuous μ ν`: `μ` is absolutely continuous with respect to `ν`

## Main statements

* `ae_le_iff_absolutelyContinuous`: `ae μ ≤ ae ν ↔ μ ≪ ν`

## Notation

* `μ ≪ ν`: `MeasureTheory.Measure.AbsolutelyContinuous μ ν`. That is: `μ` is absolutely continuous
  with respect to `ν`

-/

@[expose] public section

variable {α β δ ι R : Type*}

namespace MeasureTheory

open Set ENNReal NNReal

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ μ₁ μ₂ μ₃ ν ν' : Measure α} {s t : Set α}

namespace Measure

/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
/-
**MeasureTheory.Measure.AbsolutelyContinuous** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop
参数：μ ν : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dom
inated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`.
-/
def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0

@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous
/-
**MeasureTheory.Measure.absolutelyContinuous_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：absolutelyContinuous_of_le (h : μ <= ν) : μ ≪ ν
参数：h : μ <= ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
-/
theorem absolutelyContinuous_of_le (h : μ ≤ ν) : μ ≪ ν := fun s hs =>
  nonpos_iff_eq_zero.1 <| hs ▸ le_iff'.1 h s

alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le
/-
**MeasureTheory.Measure.absolutelyContinuous_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν
参数：h : μ = ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν :=
  h.le.absolutelyContinuous

alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq

namespace AbsolutelyContinuous

/-
**MeasureTheory.Measure.AbsolutelyContinuous.mk** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure.AbsolutelyContinuous`。
形式化陈述：mk (h : forall ⦃s : Set α⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
参数：h : forall ⦃s : Set α⦄, MeasurableSet s -> ν s = 0 -> μ s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → ν s = 0 → μ s = 0) : μ ≪ ν := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)

@[refl]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.refl** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {_m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α), 
μ.AbsolutelyContinuous μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
-/
protected theorem refl {_m0 : MeasurableSpace α} (μ : Measure α) : μ ≪ μ :=
  rfl.absolutelyContinuous
/-
**MeasureTheory.Measure.AbsolutelyContinuous.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ
.AbsolutelyContinuous μ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem rfl : μ ≪ μ := fun _s hs => hs
/-
**MeasureTheory.Measure.AbsolutelyContinuous.instRefl** 是 Mathlib 中的一个实例，位于命名空间 
`MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：instRefl {_ : MeasurableSpace α} : @Std.Refl (Measure α) (· ≪ ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
instance instRefl {_ : MeasurableSpace α} : @Std.Refl (Measure α) (· ≪ ·) :=
  ⟨fun _ => AbsolutelyContinuous.rfl⟩

@[simp]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ : MeasureTheory.Measure α), M
easureTheory.Measure.AbsolutelyContinuous 0 μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma zero (μ : Measure α) : 0 ≪ μ := fun _ _ ↦ by simp

@[trans]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.trans** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measur
e α},   μ₁.AbsolutelyContinuous μ₂ → μ₂.AbsolutelyContinuous μ₃ → μ₁.AbsolutelyC
ontinuous μ₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun _s hs => h1 <| h2 hs

@[gcongr, mono]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.map** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν →     ∀ {f :
 α → β}, Measurable f → (MeasureTheory.Measure.map f μ).AbsolutelyContinuous (Me
asureTheory.Measure.map f ν)
参数：MeasureTheory.Measure.map f μ；MeasureTheory.Measure.map f ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
protected theorem map (h : μ ≪ ν) {f : α → β} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _
/-
**MeasureTheory.Measure.AbsolutelyContinuous.smul_left** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureThe
ory.Measure α} [inst : SMul R ENNReal]   [inst_1 : IsScalarTower R ENNReal ENNRe
al], μ.AbsolutelyContinuous ν → ∀ (c : R), (c • μ).AbsolutelyContinuous ν
参数：c : R；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem smul_left [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ ν := fun s hνs => by
  simp only [h hνs, smul_apply, smul_zero, ← smul_one_smul ℝ≥0∞ c (0 : ℝ≥0∞)]

/-- If `μ ≪ ν`, then `c • μ ≪ c • ν`.

Earlier, this name was used for what's now called `AbsolutelyContinuous.smul_left`. -/
/-
**MeasureTheory.Measure.AbsolutelyContinuous.smul** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureThe
ory.Measure α} [inst : SMul R ENNReal]   [inst_1 : IsScalarTower R ENNReal ENNRe
al], μ.AbsolutelyContinuous ν → ∀ (c : R), (c • μ).AbsolutelyContinuous (c • ν)
参数：c : R；c • μ；c • ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c

--- 原说明 ---
If `μ ≪ ν`, then `c • μ ≪ c • ν`.

Earlier, this name was used for what's now called `AbsolutelyContinuous.smul_lef
t`.
-/
protected theorem smul [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ c • ν := by
  intro s hνs
  rw [smul_apply, ← smul_one_smul ℝ≥0∞, smul_eq_mul, mul_eq_zero] at hνs ⊢
  exact hνs.imp_right fun hs ↦ h hs
/-
**MeasureTheory.Measure.AbsolutelyContinuous.add** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ₁ μ₂ ν ν' : MeasureTheory.Meas
ure α},   μ₁.AbsolutelyContinuous ν → μ₂.AbsolutelyContinuous ν' → (μ₁ + μ₂).Abs
olutelyContinuous (ν + ν')
参数：μ₁ + μ₂；ν + ν'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma add (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν') : μ₁ + μ₂ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩
/-
**MeasureTheory.Measure.AbsolutelyContinuous.add_left_iff** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：add_left_iff {μ₁ μ₂ ν : Measure α} : μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.add`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ₁ μ₂ ν ν' : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous ν → μ₂.AbsolutelyContinuous ν' →…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
lemma add_left_iff {μ₁ μ₂ ν : Measure α} :
    μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.1.add h.2).trans ?_⟩
  · have : ∀ s, ν s = 0 → μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 ↦ (this s hs0).1, fun s hs0 ↦ (this s hs0).2⟩
  · rw [← two_smul ℝ≥0]
    exact AbsolutelyContinuous.rfl.smul_left 2
/-
**MeasureTheory.Measure.AbsolutelyContinuous.add_left** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：add_left {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) : μ₁ + μ₂ ≪ ν
参数：h₁ : μ₁ ≪ ν；h₂ : μ₂ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_left_iff`：add_left_iff {μ
₁ μ₂ ν : Measure α} : μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν
-/
lemma add_left {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) : μ₁ + μ₂ ≪ ν :=
  Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩
/-
**MeasureTheory.Measure.AbsolutelyContinuous.add_right** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：add_right (h1 : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
参数：h1 : μ ≪ ν；ν' : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma add_right (h1 : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1
/-
**MeasureTheory.Measure.AbsolutelyContinuous.add_right'** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：add_right' (h : μ ≪ ν') (ν : Measure α) : μ ≪ ν + ν'
参数：h : μ ≪ ν'；ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
-/
lemma add_right' (h : μ ≪ ν') (ν : Measure α) : μ ≪ ν + ν' := by
  simp [add_comm, add_right h]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.null_mono** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：null_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄ (ht : ν t = 0) : μ t
 = 0
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma null_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄
    (ht : ν t = 0) : μ t = 0 :=
  hμν ht
/-
**MeasureTheory.Measure.AbsolutelyContinuous.pos_mono** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：pos_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄ (ht : 0 < μ t) : 0 < 
ν t
参数：hμν : μ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.null_mono`：null_mono {μ ν : M
easure α} (hμν : μ ≪ ν) ⦃t : Set α⦄ (ht : ν t = 0) : μ t = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pos_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄
    (ht : 0 < μ t) : 0 < ν t := by
  contrapose! ht
  simp_all [hμν.null_mono]

end AbsolutelyContinuous

@[simp]
/-
**MeasureTheory.Measure.absolutelyContinuous_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.zero`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} (μ : MeasureTheory.Measure α), MeasureTheory.Measure.Absolute
lyContinuous 0 μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0 :=
  ⟨fun h ↦ measure_univ_eq_zero.mp (h rfl), fun h ↦ h.symm ▸ AbsolutelyContinuous.zero _⟩

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl
/-
**MeasureTheory.Measure.absolutelyContinuous_sum_left** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_sum_left {μs : ι -> Measure α} (hμs : forall i, μs i 
≪ ν) : Measure.sum μs ≪ ν
参数：hμs : forall i, μs i ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma absolutelyContinuous_sum_left {μs : ι → Measure α} (hμs : ∀ i, μs i ≪ ν) :
    Measure.sum μs ≪ ν :=
  AbsolutelyContinuous.mk fun s hs hs0 ↦ by simp [sum_apply _ hs, fun i ↦ hμs i hs0]
/-
**MeasureTheory.Measure.absolutelyContinuous_sum_right** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_sum_right {μs : ι -> Measure α} (i : ι) (hνμ : ν ≪ μs
 i) : ν ≪ Measure.sum μs
参数：i : ι；hνμ : ν ≪ μs i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
-/
lemma absolutelyContinuous_sum_right {μs : ι → Measure α} (i : ι) (hνμ : ν ≪ μs i) :
    ν ≪ Measure.sum μs := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)
/-
**MeasureTheory.Measure.smul_absolutelyContinuous** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：smul_absolutelyContinuous {c : Real>=0∞} : c • μ ≪ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
lemma smul_absolutelyContinuous {c : ℝ≥0∞} : c • μ ≪ μ := .smul_left .rfl _
/-
**MeasureTheory.Measure.absolutelyContinuous_of_le_smul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_of_le_smul {μ' : Measure α} {c : Real>=0∞} (hμ'_le : 
μ' <= c • μ) : μ' ≪ μ
参数：hμ'_le : μ' <= c • μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
-/
theorem absolutelyContinuous_of_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hμ'_le : μ' ≤ c • μ) :
    μ' ≪ μ :=
  (Measure.absolutelyContinuous_of_le hμ'_le).trans smul_absolutelyContinuous
/-
**MeasureTheory.Measure.absolutelyContinuous_smul** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：absolutelyContinuous_smul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
参数：hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma absolutelyContinuous_smul {c : ℝ≥0∞} (hc : c ≠ 0) : μ ≪ c • μ := by
  simp [AbsolutelyContinuous, hc]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.smul_right** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},
   μ.AbsolutelyContinuous ν → ∀ {c : ENNReal}, c ≠ 0 → μ.AbsolutelyContinuous (c
 • ν)
参数：c • ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul`：∀ {α : Type u_1} {R : T
ype u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : SMul R
 ENNReal]   [inst_1 : IsScalarTower R…
-/
lemma AbsolutelyContinuous.smul_right (hμν : μ ≪ ν) {c : ℝ≥0∞} (hc : c ≠ 0) : μ ≪ c • ν :=
  (absolutelyContinuous_smul hc).trans (hμν.smul c)
/-
**MeasureTheory.Measure.ae_le_iff_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：ae_le_iff_absolutelyContinuous : ae μ <= ae ν ↔ μ ≪ ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
-/
theorem ae_le_iff_absolutelyContinuous : ae μ ≤ ae ν ↔ μ ≪ ν :=
  ⟨fun h s => by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem]
    exact fun hs => h hs, fun h _ hs => h hs⟩

alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous

alias ae_mono' := AbsolutelyContinuous.ae_le
/-
**MeasureTheory.Measure.AbsolutelyContinuous.ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {δ : Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureThe
ory.Measure α},   μ.AbsolutelyContinuous ν → ∀ {f g : α → δ}, f =ᵐ[ν] g → f =ᵐ[μ
] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
-/
theorem AbsolutelyContinuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'

end Measure

/-
**MeasureTheory.AEDisjoint.of_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AEDisjoint`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.AEDisjoint μ s t →     ∀ {ν : MeasureTheory.Measure
 α}, ν.AbsolutelyContinuous μ → MeasureTheory.AEDisjoint ν s t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem AEDisjoint.of_absolutelyContinuous
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≪ μ) :
    AEDisjoint ν s t := h' h
/-
**MeasureTheory.AEDisjoint.of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEDisj
oint`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.AEDisjoint μ s t → ∀ {ν : MeasureTheory.Measure α},
 ν ≤ μ → MeasureTheory.AEDisjoint ν s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEDisjoint.of_absolutelyContinuous`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory
.AEDisjoint μ s t →     ∀ {ν : Measure…
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
-/
protected theorem AEDisjoint.of_le
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≤ μ) :
    AEDisjoint ν s t :=
  h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')

@[gcongr, mono]
/-
**MeasureTheory.ae_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_mono (h : μ <= ν) : ae μ <= ae ν
参数：h : μ <= ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
-/
theorem ae_mono (h : μ ≤ ν) : ae μ ≤ ae ν :=
  h.absolutelyContinuous.ae_le

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} {μ ν : Measure α}

/-
**MeasurableEmbedding.absolutelyContinuous_map** 是 Mathlib 中的一个引理，位于命名空间 `Measur
ableEmbedding`。
形式化陈述：absolutelyContinuous_map (hf : MeasurableEmbedding f) (hμν : μ ≪ ν) : μ.ma
p f ≪ ν.map f
参数：hf : MeasurableEmbedding f；hμν : μ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
-/
lemma absolutelyContinuous_map (hf : MeasurableEmbedding f) (hμν : μ ≪ ν) :
    μ.map f ≪ ν.map f := by
  intro t ht
  rw [hf.map_apply] at ht ⊢
  exact hμν ht

end MeasurableEmbedding

