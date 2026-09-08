/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-! # Mutually singular measures

Two measures `μ`, `ν` are said to be mutually singular (`MeasureTheory.Measure.MutuallySingular`,
localized notation `μ ⟂ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`MeasureTheory.Measure.MutuallySingular.mk`) but we keep it because this way `rcases (h : μ ⟂ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `MeasureTheory.Measure.MutuallySingular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/

@[expose] public section


open Set

open MeasureTheory NNReal ENNReal Filter

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m0 : MeasurableSpace α} {μ μ₁ μ₂ ν ν₁ ν₂ : Measure α}

/-- Two measures `μ`, `ν` are said to be mutually singular if there exists a measurable set `s`
such that `μ s = 0` and `ν sᶜ = 0`. -/
/-
**MeasureTheory.Measure.MutuallySingular** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：MutuallySingular {_ : MeasurableSpace α} (μ ν : Measure α) : Prop
参数：μ ν : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two measures `μ`, `ν` are said to be mutually singular if there exists a measura
ble set `s`
such that `μ s = 0` and `ν sᶜ = 0`.
-/
def MutuallySingular {_ : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0

@[inherit_doc MeasureTheory.Measure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ₘ " => MeasureTheory.Measure.MutuallySingular

namespace MutuallySingular

/-
**MeasureTheory.Measure.MutuallySingular.mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.MutuallySingular`。
形式化陈述：mk {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ subseteq s unio
n t) : MutuallySingular μ ν
参数：hs : μ s = 0；ht : ν t = 0；hst : univ subseteq s union t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `trivial`：True
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
-/
theorem mk {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ ⊆ s ∪ t) :
    MutuallySingular μ ν := by
  use toMeasurable μ s, measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans hs
  refine measure_mono_null (fun x hx => (hst trivial).resolve_left fun hxs => hx ?_) ht
  exact subset_toMeasurable _ _ hxs

/-- A set such that `μ h.nullSet = 0` and `ν h.nullSetᶜ = 0`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.MutuallySingular.nullSet** 是 Mathlib 中的一个定义，位于命名空间 `Meas
ureTheory.Measure.MutuallySingular`。
形式化陈述：nullSet (h : μ ⟂ₘ ν) : Set α
参数：h : μ ⟂ₘ ν。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def nullSet (h : μ ⟂ₘ ν) : Set α := h.choose
/-
**MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：measurableSet_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
参数：h : μ ⟂ₘ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma measurableSet_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet := h.choose_spec.1

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.measure_nullSet** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：measure_nullSet (h : μ ⟂ₘ ν) : μ h.nullSet = 0
参数：h : μ ⟂ₘ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma measure_nullSet (h : μ ⟂ₘ ν) : μ h.nullSet = 0 := h.choose_spec.2.1

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：measure_compl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
参数：h : μ ⟂ₘ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma measure_compl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0 := h.choose_spec.2.2

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.restrict_nullSet** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：restrict_nullSet (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0
参数：h : μ ⟂ₘ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_nullSet`：measure_nullSet 
(h : μ ⟂ₘ ν) : μ h.nullSet = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_nullSet (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0 := by simp

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.restrict_compl_nullSet** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：restrict_compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0
参数：h : μ ⟂ₘ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet`：measure_co
mpl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0 := by simp

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.MutuallySingular`。
形式化陈述：zero_right : μ ⟂ₘ 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem zero_right : μ ⟂ₘ 0 :=
  ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩

@[symm]
/-
**MeasureTheory.Measure.MutuallySingular.symm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.MutuallySingular`。
形式化陈述：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
参数：h : ν ⟂ₘ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
  let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩
/-
**MeasureTheory.Measure.MutuallySingular.comm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.MutuallySingular`。
形式化陈述：comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
-/
theorem comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.MutuallySingular`。
形式化陈述：zero_left : 0 ⟂ₘ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_right`：zero_right : μ ⟂ₘ 0
-/
theorem zero_left : 0 ⟂ₘ μ :=
  zero_right.symm
/-
**MeasureTheory.Measure.MutuallySingular.mono_ac** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.MutuallySingular`。
形式化陈述：mono_ac (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
参数：h : μ₁ ⟂ₘ ν₁；hμ : μ₂ ≪ μ₁；hν : ν₂ ≪ ν₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_ac (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂ :=
  let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩
/-
**MeasureTheory.Measure.MutuallySingular.congr_ac** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure.MutuallySingular`。
形式化陈述：congr_ac (hμμ₂ : μ ≪ μ₂) (hμ₂μ : μ₂ ≪ μ) (hνν₂ : ν ≪ ν₂) (hν₂ν : ν₂ ≪ ν) :
 μ ⟂ₘ ν ↔ μ₂ ⟂ₘ ν₂
参数：hμμ₂ : μ ≪ μ₂；hμ₂μ : μ₂ ≪ μ；hνν₂ : ν ≪ ν₂；hν₂ν : ν₂ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
-/
lemma congr_ac (hμμ₂ : μ ≪ μ₂) (hμ₂μ : μ₂ ≪ μ) (hνν₂ : ν ≪ ν₂) (hν₂ν : ν₂ ≪ ν) :
    μ ⟂ₘ ν ↔ μ₂ ⟂ₘ ν₂ :=
  ⟨fun h ↦ h.mono_ac hμ₂μ hν₂ν, fun h ↦ h.mono_ac hμμ₂ hνν₂⟩
/-
**MeasureTheory.Measure.MutuallySingular.mono** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.MutuallySingular`。
形式化陈述：mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ <= μ₁) (hν : ν₂ <= ν₁) : μ₂ ⟂ₘ ν₂
参数：h : μ₁ ⟂ₘ ν₁；hμ : μ₂ <= μ₁；hν : ν₂ <= ν₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
-/
theorem mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⟂ₘ ν₂ :=
  h.mono_ac hμ.absolutelyContinuous hν.absolutelyContinuous

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure.MutuallySingular`。
形式化陈述：self_iff (μ : Measure α) : μ ⟂ₘ μ ↔ μ = 0
参数：μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
-/
lemma self_iff (μ : Measure α) : μ ⟂ₘ μ ↔ μ = 0 := by
  refine ⟨?_, fun h ↦ by (rw [h]; exact zero_left)⟩
  rintro ⟨s, hs, hμs, hμs_compl⟩
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s, measure_union disjoint_compl_right hs.compl, hμs, hμs_compl,
    add_zero]

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.sum_left** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.MutuallySingular`。
形式化陈述：sum_left {ι : Type*} [Countable ι] {μ : ι -> Measure α} : sum μ ⟂ₘ ν ↔ for
all i, μ i ⟂ₘ ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono`：mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ
₂ <= μ₁) (hν : ν₂ <= ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.le_sum`：le_sum (μ : ι -> Measure α) (i : ι) : μ i 
<= sum μ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `ENNReal.tsum_eq_zero`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (i : α), f 
i = 0 ↔ ∀ (i : α), f i = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `MeasureTheory.measure_iUnion_null_iff`：measure_iUnion_null_iff {ι : Sort
*} [Countable ι] {s : ι -> Set α} : μ (⋃ i, s i) = 0 ↔ forall i, μ (s i) = 0
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem sum_left {ι : Type*} [Countable ι] {μ : ι → Measure α} : sum μ ⟂ₘ ν ↔ ∀ i, μ i ⟂ₘ ν := by
  refine ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => ?_⟩
  choose s hsm hsμ hsν using H
  refine ⟨⋂ i, s i, MeasurableSet.iInter hsm, ?_, ?_⟩
  · rw [sum_apply _ (MeasurableSet.iInter hsm), ENNReal.tsum_eq_zero]
    exact fun i => measure_mono_null (iInter_subset _ _) (hsμ i)
  · rwa [compl_iInter, measure_iUnion_null_iff]

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.sum_right** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.MutuallySingular`。
形式化陈述：sum_right {ι : Type*} [Countable ι] {ν : ι -> Measure α} : μ ⟂ₘ sum ν ↔ fo
rall i, μ ⟂ₘ ν i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.MutuallySingular.comm`：comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.sum_left`：sum_left {ι : Type*} [C
ountable ι] {μ : ι -> Measure α} : sum μ ⟂ₘ ν ↔ forall i, μ i ⟂ₘ ν
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
-/
theorem sum_right {ι : Type*} [Countable ι] {ν : ι → Measure α} : μ ⟂ₘ sum ν ↔ ∀ i, μ ⟂ₘ ν i :=
  comm.trans <| sum_left.trans <| forall_congr' fun _ => comm

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.add_left_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.MutuallySingular`。
形式化陈述：add_left_iff : μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.sum_cond`：sum_cond (μ ν : Measure α) : (sum fun b 
=> cond b μ ν) = μ + ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.sum_left`：sum_left {ι : Type*} [C
ountable ι] {μ : ι -> Measure α} : sum μ ⟂ₘ ν ↔ forall i, μ i ⟂ₘ ν
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `cond.eq_2`：∀ {α : Sort u} (x y : α), (bif false then x else y) = y
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_left_iff : μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν := by
  rw [← sum_cond, sum_left, Bool.forall_bool, cond, cond, and_comm]

@[simp]
/-
**MeasureTheory.Measure.MutuallySingular.add_right_iff** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：add_right_iff : μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.MutuallySingular.comm`：comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left_iff`：add_left_iff : μ₁ +
 μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
theorem add_right_iff : μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂ :=
  comm.trans <| add_left_iff.trans <| and_congr comm comm
/-
**MeasureTheory.Measure.MutuallySingular.add_left** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.MutuallySingular`。
形式化陈述：add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ
参数：h₁ : ν₁ ⟂ₘ μ；h₂ : ν₂ ⟂ₘ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left_iff`：add_left_iff : μ₁ +
 μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
-/
theorem add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ :=
  add_left_iff.2 ⟨h₁, h₂⟩
/-
**MeasureTheory.Measure.MutuallySingular.add_right** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.MutuallySingular`。
形式化陈述：add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂
参数：h₁ : μ ⟂ₘ ν₁；h₂ : μ ⟂ₘ ν₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_right_iff`：add_right_iff : μ 
⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂
-/
theorem add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂ :=
  add_right_iff.2 ⟨h₁, h₂⟩
/-
**MeasureTheory.Measure.MutuallySingular.smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.MutuallySingular`。
形式化陈述：smul (r : Real>=0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ
参数：r : Real>=0∞；h : ν ⟂ₘ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
theorem smul (r : ℝ≥0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.mono_ac (AbsolutelyContinuous.rfl.smul_left r) AbsolutelyContinuous.rfl
/-
**MeasureTheory.Measure.MutuallySingular.smul_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.MutuallySingular`。
形式化陈述：smul_nnreal (r : Real>=0) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ
参数：r : Real>=0；h : ν ⟂ₘ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.smul`：smul (r : Real>=0∞) (h : ν 
⟂ₘ μ) : r • ν ⟂ₘ μ
-/
theorem smul_nnreal (r : ℝ≥0) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.smul r
/-
**MeasureTheory.Measure.MutuallySingular.restrict** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure.MutuallySingular`。
形式化陈述：restrict (h : μ ⟂ₘ ν) (s : Set α) : μ.restrict s ⟂ₘ ν
参数：h : μ ⟂ₘ ν；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_nullSet`：measure_nullSet 
(h : μ ⟂ₘ ν) : μ h.nullSet = 0
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet`：measure_co
mpl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
-/
lemma restrict (h : μ ⟂ₘ ν) (s : Set α) : μ.restrict s ⟂ₘ ν := by
  refine ⟨h.nullSet, h.measurableSet_nullSet, ?_, h.measure_compl_nullSet⟩
  rw [Measure.restrict_apply h.measurableSet_nullSet]
  exact measure_mono_null Set.inter_subset_left h.measure_nullSet

end MutuallySingular

/-
**MeasureTheory.Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular** 是 
Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：eq_zero_of_absolutelyContinuous_of_mutuallySingular {μ ν : Measure α} (h_a
c : μ ≪ ν) (h_ms : μ ⟂ₘ ν) : μ = 0
参数：h_ac : μ ≪ ν；h_ms : μ ⟂ₘ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.MutuallySingular.self_iff`：self_iff (μ : Measure α
) : μ ⟂ₘ μ ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
lemma eq_zero_of_absolutelyContinuous_of_mutuallySingular {μ ν : Measure α}
    (h_ac : μ ≪ ν) (h_ms : μ ⟂ₘ ν) :
    μ = 0 := by
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac
/-
**MeasureTheory.Measure.absolutelyContinuous_of_add_of_mutuallySingular** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α} (h : μ
 ≪ ν₁ + ν₂) (h_ms : μ ⟂ₘ ν₂) : μ ≪ ν₁
参数：h : μ ≪ ν₁ + ν₂；h_ms : μ ⟂ₘ ν₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_nullSet`：measure_nullSet 
(h : μ ⟂ₘ ν) : μ h.nullSet = 0
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet`：measure_co
mpl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `Disjoint.inter_left'`：inter_left' (u : Set α) (h : Disjoint s t) : Disjo
int (u inter s) t
· 使用定理 `Disjoint.inter_right'`：inter_right' (u : Set α) (h : Disjoint s t) : Dis
joint s (u inter t)
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.measure_inter_null_of_null_right`：measure_inter_null_of_nu
ll_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S inter T) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MeasureTheory.measure_inter_null_of_null_left`：measure_inter_null_of_nul
l_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S inter T) = 0
-/
lemma absolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α}
    (h : μ ≪ ν₁ + ν₂) (h_ms : μ ⟂ₘ ν₂) : μ ≪ ν₁ := by
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  let t := h_ms.nullSet
  have ht : MeasurableSet t := h_ms.measurableSet_nullSet
  have htμ : μ t = 0 := h_ms.measure_nullSet
  have htν₂ : ν₂ tᶜ = 0 := h_ms.measure_compl_nullSet
  have : μ s = μ (s ∩ tᶜ) := by
    conv_lhs => rw [← inter_union_compl s t]
    rw [measure_union, measure_inter_null_of_null_right _ htμ, zero_add]
    · exact (disjoint_compl_right.inter_right' _).inter_left' _
    · exact hs.inter ht.compl
  rw [this]
  refine h ?_
  simp only [Measure.coe_add, Pi.add_apply, add_eq_zero]
  exact ⟨measure_inter_null_of_null_left _ hs_zero, measure_inter_null_of_null_right _ htν₂⟩
/-
**MeasureTheory.Measure._root_.MeasurableEmbedding.mutuallySingular_map** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.mutuallySingular_map {β : Type*} {_ : MeasurableSpace β}
    {f : α → β} (hf : MeasurableEmbedding f) (hμν : μ ⟂ₘ ν) :
    μ.map f ⟂ₘ ν.map f := by
  refine ⟨f '' hμν.nullSet, hf.measurableSet_image' hμν.measurableSet_nullSet, ?_, ?_⟩
  · rw [hf.map_apply, hf.injective.preimage_image, hμν.measure_nullSet]
  · rw [hf.map_apply, Set.preimage_compl, hf.injective.preimage_image, hμν.measure_compl_nullSet]
/-
**MeasureTheory.Measure.exists_null_set_measure_lt_of_disjoint** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_null_set_measure_lt_of_disjoint (h : Disjoint μ ν) {ε : Real>=0} (h
ε : 0 < ε) : exists s, μ s = 0 ∧ ν sᶜ <= 2 * ε
参数：h : Disjoint μ ν；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.mul_pos`：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
（共 60 条，此处仅展示前 30 条）
-/
lemma exists_null_set_measure_lt_of_disjoint (h : Disjoint μ ν) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ s, μ s = 0 ∧ ν sᶜ ≤ 2 * ε := by
  have h₁ : (μ ⊓ ν) univ = 0 := le_bot_iff.1 (h (inf_le_left (b := ν)) inf_le_right) ▸ rfl
  simp_rw [Measure.inf_apply MeasurableSet.univ, inter_univ] at h₁
  have h₂ : ∀ n : ℕ, ∃ t, μ t + ν tᶜ < ε * (1 / 2) ^ n := by
    intro n
    obtain ⟨m, ⟨t, ht₁, rfl⟩, hm₂⟩ :
        ∃ x ∈ {m | ∃ t, m = μ t + ν tᶜ}, x < ε * (1 / 2 : ℝ≥0∞) ^ n := by
      refine exists_lt_of_csInf_lt ⟨ν univ, ∅, by simp⟩ <| h₁ ▸ ENNReal.mul_pos ?_ (by simp)
      norm_cast
      exact hε.ne.symm
    exact ⟨t, hm₂⟩
  choose t ht₂ using h₂
  refine ⟨⋂ n, t n, ?_, ?_⟩
  · refine eq_zero_of_le_mul_pow (by simp)
      fun n ↦ ((measure_mono <| iInter_subset_of_subset n fun _ ht ↦ ht).trans
      (le_add_right le_rfl)).trans (ht₂ n).le
  · rw [compl_iInter, (by simp [ENNReal.tsum_mul_left, mul_comm] :
      2 * (ε : ℝ≥0∞) = ∑' (n : ℕ), ε * (1 / 2 : ℝ≥0∞) ^ n)]
    refine (measure_iUnion_le _).trans ?_
    exact ENNReal.summable.tsum_le_tsum (fun n ↦ (le_add_left le_rfl).trans (ht₂ n).le)
      ENNReal.summable
/-
**MeasureTheory.Measure.mutuallySingular_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：mutuallySingular_of_disjoint (h : Disjoint μ ν) : μ ⟂ₘ ν
参数：h : Disjoint μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 76 条，此处仅展示前 30 条）
-/
lemma mutuallySingular_of_disjoint (h : Disjoint μ ν) : μ ⟂ₘ ν := by
  have h' (n : ℕ) : ∃ s, μ s = 0 ∧ ν sᶜ ≤ (1 / 2) ^ n := by
    convert!
      exists_null_set_measure_lt_of_disjoint h (ε := (1 / 2) ^ (n + 1)) <| pow_pos (by simp) (n + 1)
    conv =>
      -- this tweak is needed due to the known issue of `norm_cast` with numeric fractions
      enter [1, 1]
      equals ((1 : ℝ≥0) / (2 : ℝ≥0)) => rfl
    norm_cast
    ring
  choose s hs₂ hs₃ using h'
  refine Measure.MutuallySingular.mk (t := (⋃ n, s n)ᶜ) (measure_iUnion_null hs₂) ?_ ?_
  · rw [compl_iUnion]
    refine eq_zero_of_le_mul_pow (ε := 1) (by simp : (1 / 2 : ℝ≥0∞) < 1) <| fun n ↦ ?_
    rw [ENNReal.coe_one, one_mul]
    exact (measure_mono <| iInter_subset_of_subset n fun _ ht ↦ ht).trans (hs₃ n)
  · rw [union_compl_self]
/-
**MeasureTheory.Measure.MutuallySingular.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},
 μ.MutuallySingular ν → Disjoint μ ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MeasureTheory.measure_inter_null_of_null_right`：measure_inter_null_of_nu
ll_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S inter T) = 0
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_nullSet`：measure_nullSet 
(h : μ ⟂ₘ ν) : μ h.nullSet = 0
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet`：measure_co
mpl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
-/
lemma MutuallySingular.disjoint (h : μ ⟂ₘ ν) : Disjoint μ ν := by
  have h_bot_iff (ξ : Measure α) : ξ ≤ ⊥ ↔ ξ = 0 := by
    rw [le_bot_iff]
    rfl
  intro ξ hξμ hξν
  rw [h_bot_iff]
  ext s hs
  simp only [Measure.coe_zero, Pi.zero_apply]
  rw [← inter_union_compl s h.nullSet, measure_union, add_eq_zero]
  · exact ⟨measure_inter_null_of_null_right _ <| absolutelyContinuous_of_le hξμ h.measure_nullSet,
      measure_inter_null_of_null_right _ <| absolutelyContinuous_of_le hξν h.measure_compl_nullSet⟩
  · exact Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right
  · exact hs.inter h.measurableSet_nullSet.compl
/-
**MeasureTheory.Measure.MutuallySingular.disjoint_ae** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},
   μ.MutuallySingular ν → Disjoint (MeasureTheory.ae μ) (MeasureTheory.ae ν)
参数：MeasureTheory.ae μ；MeasureTheory.ae ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.measure_inter_null_of_null_right`：measure_inter_null_of_nu
ll_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S inter T) = 0
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_nullSet`：measure_nullSet 
(h : μ ⟂ₘ ν) : μ h.nullSet = 0
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet`：measure_co
mpl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
· 使用定理 `Set.union_eq_compl_compl_inter_compl`：union_eq_compl_compl_inter_compl (
s t : Set α) : s union t = (sᶜ inter tᶜ)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
-/
lemma MutuallySingular.disjoint_ae (h : μ ⟂ₘ ν) : Disjoint (ae μ) (ae ν) := by
  rw [disjoint_iff_inf_le]
  intro s _
  refine ⟨s ∪ h.nullSetᶜ, ?_, s ∪ h.nullSet, ?_, ?_⟩
  · rw [mem_ae_iff, compl_union, compl_compl]
    exact measure_inter_null_of_null_right _ h.measure_nullSet
  · rw [mem_ae_iff, compl_union]
    exact measure_inter_null_of_null_right _ h.measure_compl_nullSet
  · rw [union_eq_compl_compl_inter_compl, union_eq_compl_compl_inter_compl,
      ← compl_union, compl_compl, inter_union_compl, compl_compl]
/-
**MeasureTheory.Measure.disjoint_of_disjoint_ae** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：disjoint_of_disjoint_ae (h : Disjoint (ae μ) (ae ν)) : Disjoint μ ν
参数：h : Disjoint (ae μ) (ae ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `MeasureTheory.Measure.le_intro`：le_intro (h : forall s, MeasurableSet s 
-> s.Nonempty -> μ₁ s <= μ₂ s) : μ₁ <= μ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Measure.inf_apply`：inf_apply {s : Set α} (hs : MeasurableS
et s) : (μ ⊓ ν) s = sInf {m | exists t, m = μ (t inter s) + ν (tᶜ inter s)}
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `csInf_eq_bot_of_bot_mem`：∀ {α : Type u_1} [inst : ConditionallyCompleteL
inearOrder α] [inst_1 : OrderBot α] {s : Set α}, ⊥ ∈ s → sInf s = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma disjoint_of_disjoint_ae (h : Disjoint (ae μ) (ae ν)) : Disjoint μ ν := by
  simp_rw [Filter.disjoint_iff, mem_ae_iff] at h
  obtain ⟨s, hs, t, ht, hst⟩ := h
  rw [disjoint_iff_inf_le]
  have : (⊥ : Measure α) = 0 := rfl
  refine Measure.le_intro fun u hu _ ↦ ?_
  simp only [Measure.inf_apply hu, this, coe_zero, Pi.zero_apply, nonpos_iff_eq_zero]
  refine csInf_eq_bot_of_bot_mem ⟨t, ?_⟩
  simp [measure_mono_null (inter_subset_left.trans hst.subset_compl_left) hs,
    measure_mono_null inter_subset_left ht]
/-
**MeasureTheory.Measure.mutuallySingular_tfae** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：mutuallySingular_tfae : List.TFAE [ μ ⟂ₘ ν, Disjoint μ ν, Disjoint (ae μ) 
(ae ν) ]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.disjoint`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α}, μ.MutuallySingular ν → Disjo
int μ ν
· 使用引理 `MeasureTheory.Measure.mutuallySingular_of_disjoint`：mutuallySingular_of_
disjoint (h : Disjoint μ ν) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.MutuallySingular.disjoint_ae`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.MutuallySingular ν → 
Disjoint (MeasureTheory.ae μ) (MeasureTh…
· 使用引理 `MeasureTheory.Measure.disjoint_of_disjoint_ae`：disjoint_of_disjoint_ae (
h : Disjoint (ae μ) (ae ν)) : Disjoint μ ν
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
lemma mutuallySingular_tfae : List.TFAE
    [ μ ⟂ₘ ν,
      Disjoint μ ν,
      Disjoint (ae μ) (ae ν) ] := by
  tfae_have 1 → 2
  | h => h.disjoint
  tfae_have 2 → 1
  | h => mutuallySingular_of_disjoint h
  tfae_have 1 → 3
  | h => h.disjoint_ae
  tfae_have 3 → 2
  | h => disjoint_of_disjoint_ae h
  tfae_finish
/-
**MeasureTheory.Measure.mutuallySingular_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：mutuallySingular_iff_disjoint : μ ⟂ₘ ν ↔ Disjoint μ ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.mutuallySingular_tfae`：mutuallySingular_tfae : Lis
t.TFAE [ μ ⟂ₘ ν, Disjoint μ ν, Disjoint (ae μ) (ae ν) ]
-/
lemma mutuallySingular_iff_disjoint : μ ⟂ₘ ν ↔ Disjoint μ ν :=
  mutuallySingular_tfae.out 0 1
/-
**MeasureTheory.Measure.mutuallySingular_iff_disjoint_ae** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：mutuallySingular_iff_disjoint_ae : μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.mutuallySingular_tfae`：mutuallySingular_tfae : Lis
t.TFAE [ μ ⟂ₘ ν, Disjoint μ ν, Disjoint (ae μ) (ae ν) ]
-/
lemma mutuallySingular_iff_disjoint_ae : μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν) :=
  mutuallySingular_tfae.out 0 2

end Measure

end MeasureTheory

