/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Exhaustion
public import Mathlib.Probability.ConditionalProbability

/-!
# s-finite measures can be written as `withDensity` of a finite measure

If `μ` is an s-finite measure, then there exists a finite measure `μ.toFinite`
such that a set is `μ`-null iff it is `μ.toFinite`-null.
In particular, `MeasureTheory.ae μ.toFinite = MeasureTheory.ae μ` and `μ.toFinite = 0` iff `μ = 0`.
As a corollary, `μ` can be represented as `μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`.

Our definition of `MeasureTheory.Measure.toFinite` ensures some extra properties:

- if `μ` is a finite measure, then `μ.toFinite = μ[|univ] = (μ univ)⁻¹ • μ`;
- in particular, `μ.toFinite = μ` for a probability measure;
- if `μ ≠ 0`, then `μ.toFinite` is a probability measure.

## Main definitions

In this definition and the results below, `μ` is an s-finite measure (`SFinite μ`).

* `MeasureTheory.Measure.toFinite`: a finite measure with `μ ≪ μ.toFinite` and `μ.toFinite ≪ μ`.
  If `μ ≠ 0`, this is a probability measure.

## Main statements

* `absolutelyContinuous_toFinite`: `μ ≪ μ.toFinite`.
* `toFinite_absolutelyContinuous`: `μ.toFinite ≪ μ`.
* `ae_toFinite`: `ae μ.toFinite = ae μ`.

-/

@[expose] public section

open Set
open scoped ENNReal ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- Auxiliary definition for `MeasureTheory.Measure.toFinite`. -/
/-
**MeasureTheory.Measure.toFiniteAux** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：{α : Type u_1} →   {mα : MeasurableSpace α} → (μ : MeasureTheory.Measure α
) → [MeasureTheory.SFinite μ] → MeasureTheory.Measure α
参数：μ : MeasureTheory.Measure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_isFiniteMeasure_absolutelyContinuous`：exists_isFini
teMeasure_absolutelyContinuous [SFinite μ] : exists ν : Measure α, IsFiniteMeasu
re ν ∧ μ ≪ ν ∧ ν ≪ μ

--- 原说明 ---
Auxiliary definition for `MeasureTheory.Measure.toFinite`.
-/
noncomputable def Measure.toFiniteAux (μ : Measure α) [SFinite μ] : Measure α :=
  letI := Classical.dec
  if IsFiniteMeasure μ then μ else (exists_isFiniteMeasure_absolutelyContinuous μ).choose

/-- A finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`
(see `MeasureTheory.Measure.withDensity_rnDeriv_eq` along with
`MeasureTheory.absolutelyContinuous_toFinite`). If `μ` is non-zero, then `μ.toFinite` is a
probability measure. -/
/-
**MeasureTheory.Measure.toFinite** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：{α : Type u_1} →   {mα : MeasurableSpace α} → (μ : MeasureTheory.Measure α
) → [MeasureTheory.SFinite μ] → MeasureTheory.Measure α
参数：μ : MeasureTheory.Measure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite measure obtained from an s-finite measure `μ`, such that
`μ = μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`
(see `MeasureTheory.Measure.withDensity_rnDeriv_eq` along with
`MeasureTheory.absolutelyContinuous_toFinite`). If `μ` is non-zero, then `μ.toFi
nite` is a
probability measure.
-/
noncomputable def Measure.toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  μ.toFiniteAux[|univ]

@[local simp]
/-
**MeasureTheory.ae_toFiniteAux** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_toFiniteAux [SFinite μ] : ae μ.toFiniteAux = ae μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_isFiniteMeasure_absolutelyContinuous`：exists_isFini
teMeasure_absolutelyContinuous [SFinite μ] : exists ν : Measure α, IsFiniteMeasu
re ν ∧ μ ≪ ν ∧ ν ≪ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toFiniteAux.eq_1`：∀ {α : Type u_1} {mα : Measurabl
eSpace α} (μ : MeasureTheory.Measure α) [inst : MeasureTheory.SFinite μ],   μ.to
FiniteAux = if MeasureTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
-/
lemma ae_toFiniteAux [SFinite μ] : ae μ.toFiniteAux = ae μ := by
  rw [Measure.toFiniteAux]
  split_ifs
  · simp
  · obtain ⟨_, h₁, h₂⟩ := (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec
    exact h₂.ae_le.antisymm h₁.ae_le

@[local instance]
/-
**MeasureTheory.isFiniteMeasure_toFiniteAux** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：isFiniteMeasure_toFiniteAux [SFinite μ] : IsFiniteMeasure μ.toFiniteAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_isFiniteMeasure_absolutelyContinuous`：exists_isFini
teMeasure_absolutelyContinuous [SFinite μ] : exists ν : Measure α, IsFiniteMeasu
re ν ∧ μ ≪ ν ∧ ν ≪ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toFiniteAux.eq_1`：∀ {α : Type u_1} {mα : Measurabl
eSpace α} (μ : MeasureTheory.Measure α) [inst : MeasureTheory.SFinite μ],   μ.to
FiniteAux = if MeasureTheory…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem isFiniteMeasure_toFiniteAux [SFinite μ] : IsFiniteMeasure μ.toFiniteAux := by
  rw [Measure.toFiniteAux]
  split_ifs
  · assumption
  · exact (exists_isFiniteMeasure_absolutelyContinuous μ).choose_spec.1

@[simp]
/-
**MeasureTheory.ae_toFinite** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_toFinite [SFinite μ] : ae μ.toFinite = ae μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.Measure.ae_ennreal_smul_measure_eq`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {c : ENNReal},   c ≠ 0 → ∀ (μ : MeasureTheory.Measure α), Me
asureTheory.ae (c • μ) = MeasureTheory…
· 使用定理 `MeasureTheory.isFiniteMeasure_toFiniteAux`：isFiniteMeasure_toFiniteAux [
SFinite μ] : IsFiniteMeasure μ.toFiniteAux
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MeasureTheory.ae_toFiniteAux`：ae_toFiniteAux [SFinite μ] : ae μ.toFinite
Aux = ae μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ae_toFinite [SFinite μ] : ae μ.toFinite = ae μ := by
  simp [Measure.toFinite, ProbabilityTheory.cond]

@[simp]
/-
**MeasureTheory.toFinite_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：toFinite_apply_eq_zero_iff [SFinite μ] {s : Set α} : μ.toFinite s = 0 ↔ μ 
s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.ae_toFinite`：ae_toFinite [SFinite μ] : ae μ.toFinite = ae 
μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toFinite_apply_eq_zero_iff [SFinite μ] {s : Set α} : μ.toFinite s = 0 ↔ μ s = 0 := by
  simp only [← compl_mem_ae_iff, ae_toFinite]

@[simp]
/-
**MeasureTheory.toFinite_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toFinite_eq_zero_iff [SFinite μ] : μ.toFinite = 0 ↔ μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toFinite_eq_zero_iff [SFinite μ] : μ.toFinite = 0 ↔ μ = 0 := by
  simp_rw [← Measure.measure_univ_eq_zero, toFinite_apply_eq_zero_iff]

@[simp]
/-
**MeasureTheory.toFinite_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toFinite_zero : Measure.toFinite (0 : Measure α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.instSFiniteOfNatMeasure`：∀ {α : Type u_1} {m0 : Measurable
Space α}, MeasureTheory.SFinite 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toFinite_zero : Measure.toFinite (0 : Measure α) = 0 := by simp
/-
**MeasureTheory.toFinite_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toFinite_eq_self [IsProbabilityMeasure μ] : μ.toFinite = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toFinite.eq_1`：∀ {α : Type u_1} {mα : MeasurableSp
ace α} (μ : MeasureTheory.Measure α) [inst : MeasureTheory.SFinite μ],   μ.toFin
ite = μ.toFiniteAux[|Set.…
· 使用定理 `MeasureTheory.exists_isFiniteMeasure_absolutelyContinuous`：exists_isFini
teMeasure_absolutelyContinuous [SFinite μ] : exists ν : Measure α, IsFiniteMeasu
re ν ∧ μ ≪ ν ∧ ν ≪ μ
· 使用定理 `MeasureTheory.Measure.toFiniteAux.eq_1`：∀ {α : Type u_1} {mα : Measurabl
eSpace α} (μ : MeasureTheory.Measure α) [inst : MeasureTheory.SFinite μ],   μ.to
FiniteAux = if MeasureTheory…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ProbabilityTheory.cond_univ`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ
 : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ],   μ[|Set.uni
v] = μ
-/
lemma toFinite_eq_self [IsProbabilityMeasure μ] : μ.toFinite = μ := by
  rw [Measure.toFinite, Measure.toFiniteAux, if_pos, ProbabilityTheory.cond_univ]
  infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite μ] : IsFiniteMeasure μ.toFinite := by
  rw [Measure.toFinite]
  infer_instance
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite μ] [NeZero μ] : IsProbabilityMeasure μ.toFinite := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  simp [ne_eq, ← compl_mem_ae_iff, ae_toFiniteAux]
/-
**MeasureTheory.absolutelyContinuous_toFinite** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_le_iff_absolutelyContinuous`：ae_le_iff_absolute
lyContinuous : ae μ <= ae ν ↔ μ ≪ ν
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `MeasureTheory.ae_toFinite`：ae_toFinite [SFinite μ] : ae μ.toFinite = ae 
μ
-/
lemma absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite :=
  Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.ge
/-
**MeasureTheory.sfiniteSeq_absolutelyContinuous_toFinite** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory`。
形式化陈述：sfiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : 
Nat) : sfiniteSeq μ n ≪ μ.toFinite
参数：μ : Measure α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用引理 `MeasureTheory.sfiniteSeq_le`：sfiniteSeq_le (μ : Measure α) [SFinite μ] (
n : Nat) : sfiniteSeq μ n <= μ
· 使用引理 `MeasureTheory.absolutelyContinuous_toFinite`：absolutelyContinuous_toFini
te (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite
-/
lemma sfiniteSeq_absolutelyContinuous_toFinite (μ : Measure α) [SFinite μ] (n : ℕ) :
    sfiniteSeq μ n ≪ μ.toFinite :=
  (sfiniteSeq_le μ n).absolutelyContinuous.trans (absolutelyContinuous_toFinite μ)
/-
**MeasureTheory.toFinite_absolutelyContinuous** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_le_iff_absolutelyContinuous`：ae_le_iff_absolute
lyContinuous : ae μ <= ae ν ↔ μ ≪ ν
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `MeasureTheory.ae_toFinite`：ae_toFinite [SFinite μ] : ae μ.toFinite = ae 
μ
-/
lemma toFinite_absolutelyContinuous (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ :=
  Measure.ae_le_iff_absolutelyContinuous.mp ae_toFinite.le
/-
**MeasureTheory.restrict_compl_sigmaFiniteSet** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：restrict_compl_sigmaFiniteSet [SFinite μ] : μ.restrict μ.sigmaFiniteSetᶜ =
 ∞ • μ.toFinite.restrict μ.sigmaFiniteSetᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sigmaFiniteSet.eq_1`：∀ {α : Type u_1} {mα : Measur
ableSpace α} (μ : MeasureTheory.Measure α), μ.sigmaFiniteSet = μ.sigmaFiniteSetW
RT μ
· 使用引理 `MeasureTheory.restrict_compl_sigmaFiniteSetWRT`：restrict_compl_sigmaFini
teSetWRT [SFinite ν] (hμν : μ ≪ ν) : μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν
.restrict (μ.sigmaFiniteSetWRT ν)ᶜ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.refl`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α), μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用引理 `MeasureTheory.toFinite_absolutelyContinuous`：toFinite_absolutelyContinuo
us (μ : Measure α) [SFinite μ] : μ.toFinite ≪ μ
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用引理 `MeasureTheory.absolutelyContinuous_toFinite`：absolutelyContinuous_toFini
te (μ : Measure α) [SFinite μ] : μ ≪ μ.toFinite
-/
lemma restrict_compl_sigmaFiniteSet [SFinite μ] :
    μ.restrict μ.sigmaFiniteSetᶜ = ∞ • μ.toFinite.restrict μ.sigmaFiniteSetᶜ := by
  rw [Measure.sigmaFiniteSet,
    restrict_compl_sigmaFiniteSetWRT (Measure.AbsolutelyContinuous.refl μ)]
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  by_cases hμt : μ (t ∩ (μ.sigmaFiniteSetWRT μ)ᶜ) = 0
  · rw [hμt, toFinite_absolutelyContinuous μ hμt]
  · rw [ENNReal.top_mul hμt, ENNReal.top_mul]
    exact fun h ↦ hμt (absolutelyContinuous_toFinite μ h)

end MeasureTheory

