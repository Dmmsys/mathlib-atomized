/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
public import Mathlib.MeasureTheory.Measure.AEDisjoint

/-!
# Null measurable sets and complete measures

## Main definitions

### Null measurable sets and functions

A set `s : Set α` is called *null measurable* (`MeasureTheory.NullMeasurableSet`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `MeasureTheory.toMeasurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `MeasurableSpace` instance on
`MeasureTheory.NullMeasurableSpace α μ`. We also say that `f : α → β` is
`MeasureTheory.NullMeasurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`MeasureTheory.NullMeasurableSpace α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `MeasurableSpace α` σ-algebra (or the σ-algebra is
complete w.r.t. measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `MeasureTheory.Measure.completion μ` to be the same measure
interpreted as a measure on `MeasureTheory.NullMeasurableSpace α μ` and prove that this is a
complete measure.

## Implementation notes

We define `MeasureTheory.NullMeasurableSet` as `@MeasurableSet (NullMeasurableSpace α μ) _` so
that theorems about `MeasurableSet`s like `MeasurableSet.union` can be applied to
`NullMeasurableSet`s. However, these lemmas output terms of the same form
`@MeasurableSet (NullMeasurableSpace α μ) _ _`. While this is definitionally equal to the
expected output `NullMeasurableSet s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `MeasureTheory.NullMeasurableSet` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/

@[expose] public section

open Filter Set Encodable
open scoped ENNReal

variable {ι α β γ : Type*}

namespace MeasureTheory

/-- A type tag for `α` with `MeasurableSet` given by `NullMeasurableSet`. -/
@[nolint unusedArguments]
/-
**MeasureTheory.NullMeasurableSpace** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：NullMeasurableSpace (α : Type*) [MeasurableSpace α] (_μ : Measure α
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type tag for `α` with `MeasurableSet` given by `NullMeasurableSet`.
-/
def NullMeasurableSpace (α : Type*) [MeasurableSpace α]
    (_μ : Measure α := by volume_tac) : Type _ :=
  α

section

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

/-
**MeasureTheory.NullMeasurableSpace.instInhabited** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.NullMeasurableSpace`。
形式化陈述：{α : Type u_2} →   {m0 : MeasurableSpace α} →     {μ : MeasureTheory.Measu
re α} → [h : Inhabited α] → Inhabited (MeasureTheory.NullMeasurableSpace α μ)
参数：MeasureTheory.NullMeasurableSpace α μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NullMeasurableSpace.instInhabited [h : Inhabited α] :
    Inhabited (NullMeasurableSpace α μ) :=
  h
/-
**MeasureTheory.NullMeasurableSpace.instSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.NullMeasurableSpace`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [h
 : Subsingleton α],   Subsingleton (MeasureTheory.NullMeasurableSpace α μ)
参数：MeasureTheory.NullMeasurableSpace α μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NullMeasurableSpace.instSubsingleton [h : Subsingleton α] :
    Subsingleton (NullMeasurableSpace α μ) :=
  h
/-
**MeasureTheory.NullMeasurableSpace.instMeasurableSpace** 是 Mathlib 中的一个定义，位于命名空
间 `MeasureTheory.NullMeasurableSpace`。
形式化陈述：{α : Type u_2} →   {m0 : MeasurableSpace α} → {μ : MeasureTheory.Measure α
} → MeasurableSpace (MeasureTheory.NullMeasurableSpace α μ)
参数：MeasureTheory.NullMeasurableSpace α μ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
instance NullMeasurableSpace.instMeasurableSpace : MeasurableSpace (NullMeasurableSpace α μ) :=
  fast_instance% @eventuallyMeasurableSpace α inferInstance (ae μ) _

/-- A set is called `NullMeasurableSet` if it can be approximated by a measurable set up to
a set of null measure. -/
/-
**MeasureTheory.NullMeasurableSet** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：NullMeasurableSet [MeasurableSpace α] (s : Set α) (μ : Measure α
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is called `NullMeasurableSet` if it can be approximated by a measurable se
t up to
a set of null measure.
-/
def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by volume_tac) : Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s

@[simp, aesop unsafe (rule_sets := [Measurable])]
/-
**MeasureTheory._root_.MeasurableSet.nullMeasurableSet** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableSet.nullMeasurableSet (h : MeasurableSet s) : NullMeasurableSet s μ :=
  h.eventuallyMeasurableSet
/-
**MeasureTheory._root_.MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableS
et** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableSet (s : Set α) :
    NullMeasurableSet s μ ↔ EventuallyMeasurableSet m0 (ae μ) s :=
  Iff.rfl
/-
**MeasureTheory.nullMeasurableSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：nullMeasurableSet_empty : NullMeasurableSet ∅ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
-/
theorem nullMeasurableSet_empty : NullMeasurableSet ∅ μ :=
  MeasurableSet.empty
/-
**MeasureTheory.nullMeasurableSet_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：nullMeasurableSet_univ : NullMeasurableSet univ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem nullMeasurableSet_univ : NullMeasurableSet univ μ :=
  MeasurableSet.univ

namespace NullMeasurableSet

/-
**MeasureTheory.NullMeasurableSet.of_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.NullMeasurableSet`。
形式化陈述：of_null (h : μ s = 0) : NullMeasurableSet s μ
参数：h : μ s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
-/
theorem of_null (h : μ s = 0) : NullMeasurableSet s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩
/-
**MeasureTheory.NullMeasurableSet.compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.NullMeasurableSet`。
形式化陈述：compl (h : NullMeasurableSet s μ) : NullMeasurableSet sᶜ μ
参数：h : NullMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem compl (h : NullMeasurableSet s μ) : NullMeasurableSet sᶜ μ :=
  MeasurableSet.compl h
/-
**MeasureTheory.NullMeasurableSet.of_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.NullMeasurableSet`。
形式化陈述：of_compl (h : NullMeasurableSet sᶜ μ) : NullMeasurableSet s μ
参数：h : NullMeasurableSet sᶜ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
-/
theorem of_compl (h : NullMeasurableSet sᶜ μ) : NullMeasurableSet s μ :=
  MeasurableSet.of_compl h

@[simp]
/-
**MeasureTheory.NullMeasurableSet.compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.NullMeasurableSet`。
形式化陈述：compl_iff : NullMeasurableSet sᶜ μ ↔ NullMeasurableSet s μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl_iff`：MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ Me
asurableSet s
-/
theorem compl_iff : NullMeasurableSet sᶜ μ ↔ NullMeasurableSet s μ :=
  MeasurableSet.compl_iff

@[nontriviality]
/-
**MeasureTheory.NullMeasurableSet.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.NullMeasurableSet`。
形式化陈述：of_subsingleton [Subsingleton α] : NullMeasurableSet s μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.measurableSet`：Subsingleton.measurableSet [Subsingleton α] 
{s : Set α} : MeasurableSet s
· 使用定理 `MeasureTheory.NullMeasurableSpace.instSubsingleton`：∀ {α : Type u_2} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [h : Subsingleton α],   Subs
ingleton (MeasureTheory.NullMeasurableSp…
-/
theorem of_subsingleton [Subsingleton α] : NullMeasurableSet s μ :=
  Subsingleton.measurableSet
/-
**MeasureTheory.NullMeasurableSet.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.NullMeasurableSet s μ → s =ᵐ[μ] t → MeasureTheory.N
ullMeasurableSet t μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableSet`：∀ {α : Type
 u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} (s : Set α),   Meas
ureTheory.NullMeasurableSet s μ ↔ EventuallyMeasu…
· 使用定理 `EventuallyMeasurableSet.congr`：EventuallyMeasurableSet.congr (ht : Event
uallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
protected theorem congr (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t) : NullMeasurableSet t μ := by
  rw [nullMeasurableSet_iff_eventuallyMeasurableSet]
  exact EventuallyMeasurableSet.congr hs h.symm

@[measurability]
/-
**MeasureTheory.NullMeasurableSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ι
 : Sort u_5} [Countable ι] {s : ι → Set α},   (∀ (i : ι), MeasureTheory.NullMeas
urableSet (s i) μ) → MeasureTheory.NullMeasurableSet (⋃ i, s i) μ
参数：∀ (i : ι), MeasureTheory.NullMeasurableSet (s i) μ；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
-/
protected theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) : NullMeasurableSet (⋃ i, s i) μ :=
  MeasurableSet.iUnion h
/-
**MeasureTheory.NullMeasurableSet.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.NullMeasurableSet`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : ι → Set α} {s : Set ι},   s.Countable → (∀ b ∈ s, MeasureTheor
y.NullMeasurableSet (f b) μ) → MeasureTheory.NullMeasurableSet (⋃ b ∈ s, f b) μ
参数：∀ b ∈ s, MeasureTheory.NullMeasurableSet (f b) μ；⋃ b ∈ s, f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
-/
protected theorem biUnion {f : ι → Set α} {s : Set ι} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  MeasurableSet.biUnion hs h
/-
**MeasureTheory.NullMeasurableSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set (Set α)},   s.Countable → (∀ t ∈ s, MeasureTheory.NullMeasurableSet t μ) 
→ MeasureTheory.NullMeasurableSet (⋃₀ s) μ
参数：Set α；∀ t ∈ s, MeasureTheory.NullMeasurableSet t μ；⋃₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
-/
protected theorem sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋃₀ s) μ := by
  rw [sUnion_eq_biUnion]
  exact MeasurableSet.biUnion hs h

@[measurability]
/-
**MeasureTheory.NullMeasurableSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ι
 : Sort u_5} [Countable ι] {f : ι → Set α},   (∀ (i : ι), MeasureTheory.NullMeas
urableSet (f i) μ) → MeasureTheory.NullMeasurableSet (⋂ i, f i) μ
参数：∀ (i : ι), MeasureTheory.NullMeasurableSet (f i) μ；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
-/
protected theorem iInter {ι : Sort*} [Countable ι] {f : ι → Set α}
    (h : ∀ i, NullMeasurableSet (f i) μ) : NullMeasurableSet (⋂ i, f i) μ :=
  MeasurableSet.iInter h
/-
**MeasureTheory.NullMeasurableSet.biInter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasureTheor
y.NullMeasurableSet (f b) μ) → MeasureTheory.NullMeasurableSet (⋂ b ∈ s, f b) μ
参数：∀ b ∈ s, MeasureTheory.NullMeasurableSet (f b) μ；⋂ b ∈ s, f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
-/
protected theorem biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  MeasurableSet.biInter hs h
/-
**MeasureTheory.NullMeasurableSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set (Set α)},   s.Countable → (∀ t ∈ s, MeasureTheory.NullMeasurableSet t μ) 
→ MeasureTheory.NullMeasurableSet (⋂₀ s) μ
参数：Set α；∀ t ∈ s, MeasureTheory.NullMeasurableSet t μ；⋂₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.sInter`：MeasurableSet.sInter {s : Set (Set α)} (hs : s.Cou
ntable) (h : forall t in s, MeasurableSet t) : MeasurableSet (⋂₀ s)
-/
protected theorem sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋂₀ s) μ :=
  MeasurableSet.sInter hs h

@[simp]
/-
**MeasureTheory.NullMeasurableSet.union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.NullMeasurableSet s μ → MeasureTheory.NullMeasurabl
eSet t μ → MeasureTheory.NullMeasurableSet (s ∪ t) μ
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
-/
protected theorem union (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∪ t) μ :=
  MeasurableSet.union hs ht
/-
**MeasureTheory.NullMeasurableSet.union_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.NullMeasurableSet s μ → μ t = 0 → MeasureTheory.Nul
lMeasurableSet (s ∪ t) μ
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.union`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
-/
protected theorem union_null (hs : NullMeasurableSet s μ) (ht : μ t = 0) :
    NullMeasurableSet (s ∪ t) μ :=
  hs.union (of_null ht)

@[simp]
/-
**MeasureTheory.NullMeasurableSet.inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.NullMeasurableSet s μ → MeasureTheory.NullMeasurabl
eSet t μ → MeasureTheory.NullMeasurableSet (s ∩ t) μ
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
protected theorem inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∩ t) μ :=
  MeasurableSet.inter hs ht

@[simp]
/-
**MeasureTheory.NullMeasurableSet.diff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 t : Set α},   MeasureTheory.NullMeasurableSet s μ → MeasureTheory.NullMeasurabl
eSet t μ → MeasureTheory.NullMeasurableSet (s \ t) μ
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
-/
protected theorem diff (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s \ t) μ :=
  MeasurableSet.diff hs ht

@[simp]
/-
**MeasureTheory.NullMeasurableSet.symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
₁ s₂ : Set α},   MeasureTheory.NullMeasurableSet s₁ μ →     MeasureTheory.NullMe
asurableSet s₂ μ → MeasureTheory.NullMeasurableSet (symmDiff s₁ s₂) μ
参数：symmDiff s₁ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.union`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.diff`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasura
bleSet s μ → MeasureTheory…
-/
protected theorem symmDiff {s₁ s₂ : Set α} (h₁ : NullMeasurableSet s₁ μ)
    (h₂ : NullMeasurableSet s₂ μ) : NullMeasurableSet (symmDiff s₁ s₂) μ :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp]
/-
**MeasureTheory.NullMeasurableSet.disjointed** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 : ℕ → Set α},   (∀ (i : ℕ), MeasureTheory.NullMeasurableSet (f i) μ) → ∀ (n : ℕ
), MeasureTheory.NullMeasurableSet (disjointed f n) μ
参数：∀ (i : ℕ), MeasureTheory.NullMeasurableSet (f i) μ；n : ℕ；disjointed f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
-/
protected theorem disjointed {f : ℕ → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (n) :
    NullMeasurableSet (disjointed f n) μ :=
  MeasurableSet.disjointed h n
/-
**MeasureTheory.NullMeasurableSet.const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} (p
 : Prop),   MeasureTheory.NullMeasurableSet {_a | p} μ
参数：p : Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
-/
protected theorem const (p : Prop) : NullMeasurableSet { _a : α | p } μ :=
  MeasurableSet.const p
/-
**MeasureTheory.NullMeasurableSet.instMeasurableSingletonClass** 是 Mathlib 中的一个实
例，位于命名空间 `MeasureTheory.NullMeasurableSet`。
形式化陈述：instMeasurableSingletonClass [MeasurableSingletonClass α] : MeasurableSing
letonClass (NullMeasurableSpace α μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
-/
instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (NullMeasurableSpace α μ) :=
  eventuallyMeasurableSingleton (m := m0)
/-
**MeasureTheory.NullMeasurableSet.insert** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set α}   [MeasurableSingletonClass (MeasureTheory.NullMeasurableSpace α μ)], 
  MeasureTheory.NullMeasurableSet s μ → ∀ (a : α), MeasureTheory.NullMeasurableS
et (insert a s) μ
参数：MeasureTheory.NullMeasurableSpace α μ；a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.insert`：∀ {α : Type u_1} [inst : MeasurableSpace α] [Measu
rableSingletonClass α] {s : Set α},   MeasurableSet s → ∀ (a : α), MeasurableSet
 (insert a…
-/
protected theorem insert [MeasurableSingletonClass (NullMeasurableSpace α μ)]
    (hs : NullMeasurableSet s μ) (a : α) : NullMeasurableSet (insert a s) μ :=
  MeasurableSet.insert hs a
/-
**MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.NullMeasurableSet`。
形式化陈述：exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) : exists t ⊇ 
s, MeasurableSet t ∧ t =ᵐ[μ] s
参数：h : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Filter.EventuallyEq.union`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∪ s' =ᶠ[l] t ∪ t'
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ t ⊇ s, MeasurableSet t ∧ t =ᵐ[μ] s := by
  rcases h with ⟨t, htm, hst⟩
  refine ⟨t ∪ toMeasurable μ (s \ t), ?_, htm.union (measurableSet_toMeasurable _ _), ?_⟩
  · exact sdiff_subset_iff.1 (subset_toMeasurable _ _)
  · have : toMeasurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using hst.symm.union this
/-
**MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.NullMeasurableSet`。
形式化陈述：toMeasurable_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s
参数：h : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.toMeasurable_def`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (μ : MeasureTheory.Measure α) (s : Set α),   MeasureTheory.toMeasurable μ s 
=     if h : ∃ t ⊇ s…
· 使用定理 `MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq`：exists
_measurable_superset_ae_eq (h : NullMeasurableSet s μ) : exists t ⊇ s, Measurabl
eSet t ∧ t =ᵐ[μ] s
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem toMeasurable_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s := by
  rw [toMeasurable_def, dif_pos]
  exact (exists_measurable_superset_ae_eq h).choose_spec.2.2
/-
**MeasureTheory.NullMeasurableSet.compl_toMeasurable_compl_ae_eq** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.NullMeasurableSet`。
形式化陈述：compl_toMeasurable_compl_ae_eq (h : NullMeasurableSet s μ) : (toMeasurable
 μ sᶜ)ᶜ =ᵐ[μ] s
参数：h : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_set_compl`：ae_eq_set_compl {s t : Set α} : sᶜ =ᵐ[μ] 
t ↔ s =ᵐ[μ] tᶜ
· 使用定理 `MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq`：toMeasurable_ae_eq (
h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
-/
theorem compl_toMeasurable_compl_ae_eq (h : NullMeasurableSet s μ) : (toMeasurable μ sᶜ)ᶜ =ᵐ[μ] s :=
  Iff.mpr ae_eq_set_compl <| toMeasurable_ae_eq h.compl
/-
**MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.NullMeasurableSet`。
形式化陈述：exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) : exists t subs
eteq s, MeasurableSet t ∧ t =ᵐ[μ] s
参数：h : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.NullMeasurableSet.compl_toMeasurable_compl_ae_eq`：compl_to
Measurable_compl_ae_eq (h : NullMeasurableSet s μ) : (toMeasurable μ sᶜ)ᶜ =ᵐ[μ] 
s
-/
theorem exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ t ⊆ s, MeasurableSet t ∧ t =ᵐ[μ] s :=
  ⟨(toMeasurable μ sᶜ)ᶜ, compl_subset_comm.2 <| subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, compl_toMeasurable_compl_ae_eq h⟩

end NullMeasurableSet

open NullMeasurableSet

open scoped Function -- required for scoped `on` notation

/-- If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint sets, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such that
`tᵢ =ᵐ[μ] sᵢ`. -/
/-
**MeasureTheory.exists_subordinate_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：exists_subordinate_pairwise_disjoint [Countable ι] {s : ι -> Set α} (h : f
orall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) : exists
 t : ι -> Set α, (forall i, t i subseteq s i) ∧ (forall i, s i =ᵐ[μ] t i) ∧ (for
all i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t)
参数：h : forall i, NullMeasurableSet (s i) μ；hd : Pairwise (AEDisjoint μ on s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_null_pairwise_disjoint_sdiff`：exists_null_pairwise_
disjoint_sdiff [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s)
) : exists t : ι -> Set α, (forall i, M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.sdiff_null_ae_eq_self`：sdiff_null_ae_eq_self (ht : μ t = 0
) : (s \ t : Set α) =ᵐ[μ] s
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq`：exists_m
easurable_subset_ae_eq (h : NullMeasurableSet s μ) : exists t subseteq s, Measur
ableSet t ∧ t =ᵐ[μ] s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint se
ts, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such 
that
`tᵢ =ᵐ[μ] sᵢ`.
-/
theorem exists_subordinate_pairwise_disjoint [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) :
    ∃ t : ι → Set α,
      (∀ i, t i ⊆ s i) ∧
        (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) := by
  choose t ht_sub htm ht_eq using fun i => exists_measurable_subset_ae_eq (h i)
  rcases exists_null_pairwise_disjoint_sdiff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => sdiff_subset.trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (sdiff_null_ae_eq_self (hu₀ i)).symm, fun i => (htm i).diff (hum i),
      hud.mono fun i j h =>
        h.mono (sdiff_subset_sdiff_left (ht_sub i)) (sdiff_subset_sdiff_left (ht_sub j))⟩
/-
**MeasureTheory.measure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_iUnion {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f :
 ι -> Set α} (hn : Pairwise (Disjoint on f)) (h : forall i, MeasurableSet (f i))
 : μ (⋃ i, f i) = ∑' i, μ (f i)
参数：hn : Pairwise (Disjoint on f)；h : forall i, MeasurableSet (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_extend`：measure_eq_extend (hs : MeasurableSet s
) : μ s = extend (fun t (_ht : MeasurableSet t) => μ t) s
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasureTheory.extend_iUnion`：extend_iUnion {β} [Countable β] {f : β -> S
et α} (hd : Pairwise (Disjoint on f)) (hm : forall i, P (f i)) : extend m (⋃ i, 
f i) = ∑' i, exte…
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.m_iUnion`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (self : MeasureTheory.Measure α) ⦃f : ℕ → Set α⦄,   (∀ (i : ℕ), MeasurableSe
t (f i)) →     Pairw…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measure_iUnion {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f : ι → Set α}
    (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rw [measure_eq_extend (MeasurableSet.iUnion h),
    extend_iUnion MeasurableSet.empty _ MeasurableSet.iUnion _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_iUnion
/-
**MeasureTheory.measure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_iUnion {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f :
 ι -> Set α} (hn : Pairwise (Disjoint on f)) (h : forall i, MeasurableSet (f i))
 : μ (⋃ i, f i) = ∑' i, μ (f i)
参数：hn : Pairwise (Disjoint on f)；h : forall i, MeasurableSet (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_extend`：measure_eq_extend (hs : MeasurableSet s
) : μ s = extend (fun t (_ht : MeasurableSet t) => μ t) s
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasureTheory.extend_iUnion`：extend_iUnion {β} [Countable β] {f : β -> S
et α} (hd : Pairwise (Disjoint on f)) (hm : forall i, P (f i)) : extend m (⋃ i, 
f i) = ∑' i, exte…
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.m_iUnion`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (self : MeasureTheory.Measure α) ⦃f : ℕ → Set α⦄,   (∀ (i : ℕ), MeasurableSe
t (f i)) →     Pairw…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measure_iUnion₀ [Countable ι] {f : ι → Set α} (hd : Pairwise (AEDisjoint μ on f))
    (h : ∀ i, NullMeasurableSet (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, _ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (.countable_iUnion ht_eq)
    _ = ∑' i, μ (t i) := measure_iUnion htd htm
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm
/-
**MeasureTheory.measure_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ union s
₂) = μ s₁ + μ s₂
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union₀`：measure_union₀ (ht : NullMeasurableSet t μ
) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measure_union₀_aux (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (hd : AEDisjoint μ s t) : μ (s ∪ t) = μ s + μ t := by
  rw [union_eq_iUnion, measure_iUnion₀, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts [pairwise_on_bool.mpr hd, fun b ↦ Bool.casesOn b ht hs]

/-- A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
/-
**MeasureTheory.measure_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ (s inter t)
 + μ (s \ t) = μ s
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_inter_add_sdiff₀`：measure_inter_add_sdiff₀ (s : Se
t α) (ht : NullMeasurableSet t μ) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`.
-/
theorem measure_inter_add_sdiff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∩ t) + μ (s \ t) = μ s := by
  refine le_antisymm ?_ (measure_le_inter_add_sdiff _ _ _)
  rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
  replace hs'm : NullMeasurableSet s' μ := hs'm.nullMeasurableSet
  calc
    μ (s ∩ t) + μ (s \ t) ≤ μ (s' ∩ t) + μ (s' \ t) := by gcongr
    _ = μ (s' ∩ t ∪ s' \ t) :=
      (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) <|
          (@disjoint_inf_sdiff _ s' t _).aedisjoint).symm
    _ = μ s' := congr_arg μ (inter_union_sdiff _ _)
    _ = μ s := hs'

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff₀ := measure_inter_add_sdiff₀

/-- If `s` and `t` are null measurable sets of equal measure
and their intersection has finite measure,
then `s \ t` and `t \ s` have equal measures too. -/
/-
**MeasureTheory.measure_sdiff_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sdiff_symm (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t 
μ) (h : μ s = μ t) (hfin : μ (s inter t) != ∞) : μ (s \ t) = μ (t \ s)
参数：hs : NullMeasurableSet s μ；ht : NullMeasurableSet t μ；h : μ s = μ t；hfin : μ 
(s inter t) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_right_inj`：add_right_inj (h : a != ∞) : a + b = a + c ↔ b = 
c
· 使用定理 `MeasureTheory.measure_inter_add_sdiff₀`：measure_inter_add_sdiff₀ (s : Se
t α) (ht : NullMeasurableSet t μ) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
If `s` and `t` are null measurable sets of equal measure
and their intersection has finite measure,
then `s \ t` and `t \ s` have equal measures too.
-/
theorem measure_sdiff_symm (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (h : μ s = μ t) (hfin : μ (s ∩ t) ≠ ∞) : μ (s \ t) = μ (t \ s) := by
  rw [← ENNReal.add_right_inj hfin, measure_inter_add_sdiff₀ _ ht, inter_comm,
    measure_inter_add_sdiff₀ _ hs, h]

@[deprecated (since := "2026-06-03")] alias measure_diff_symm := measure_sdiff_symm
/-
**MeasureTheory.measure_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_union_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s union t)
 + μ (s inter t) = μ s + μ t
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `IsAddCommutative.is_comm`：∀ {M : Type u_2} {inst : Add M} [self : IsAddC
ommutative M], Std.Commutative fun x1 x2 => x1 + x2
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem measure_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_sdiff₀ (s ∪ t) ht, union_inter_cancel_right, union_sdiff_right, ←
    measure_inter_add_sdiff₀ s ht, add_comm, ← add_assoc, add_right_comm]
/-
**MeasureTheory.measure_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_union_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s union t)
 + μ (s inter t) = μ s + μ t
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `IsAddCommutative.is_comm`：∀ {M : Type u_2} {inst : Add M} [self : IsAddC
ommutative M], Std.Commutative fun x1 x2 => x1 + x2
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem measure_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter₀ t hs, add_comm]
/-
**MeasureTheory.measure_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ union s
₂) = μ s₁ + μ s₂
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union₀`：measure_union₀ (ht : NullMeasurableSet t μ
) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measure_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [← measure_union_add_inter₀ s ht, hd, add_zero]
/-
**MeasureTheory.measure_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ union s
₂) = μ s₁ + μ s₂
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union₀`：measure_union₀ (ht : NullMeasurableSet t μ
) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measure_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [union_comm, measure_union₀ hs (AEDisjoint.symm hd), add_comm]
/-
**MeasureTheory.measure_add_measure_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_add_measure_compl₀`：measure_add_measure_compl₀ {s 
: Set α} (hs : NullMeasurableSet s μ) : μ s + μ sᶜ = μ univ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_add_measure_compl₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    μ s + μ sᶜ = μ univ := by rw [← measure_union₀' hs aedisjoint_compl_right, union_compl_self]
/-
**MeasureTheory.measure_of_measure_compl_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measure_of_measure_compl_eq_zero (hs : μ sᶜ = 0) : μ s = μ Set.univ
参数：hs : μ sᶜ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.measure_add_measure_compl₀`：measure_add_measure_compl₀ {s 
: Set α} (hs : NullMeasurableSet s μ) : μ s + μ sᶜ = μ univ
· 使用定理 `MeasureTheory.NullMeasurableSet.of_compl`：of_compl (h : NullMeasurableSe
t sᶜ μ) : NullMeasurableSet s μ
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
-/
lemma measure_of_measure_compl_eq_zero (hs : μ sᶜ = 0) : μ s = μ Set.univ := by
  simpa [hs] using measure_add_measure_compl₀ <| .of_compl <| .of_null hs

section MeasurableSingletonClass

variable [MeasurableSingletonClass (NullMeasurableSpace α μ)]

/-
**MeasureTheory.nullMeasurableSet_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：nullMeasurableSet_singleton (x : α) : NullMeasurableSet {x} μ
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
theorem nullMeasurableSet_singleton (x : α) : NullMeasurableSet {x} μ :=
  @measurableSet_singleton _ _ _ _

@[simp]
/-
**MeasureTheory.nullMeasurableSet_insert** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：nullMeasurableSet_insert {a : α} {s : Set α} : NullMeasurableSet (insert a
 s) μ ↔ NullMeasurableSet s μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_insert`：measurableSet_insert {a : α} {s : Set α} : Measura
bleSet (insert a s) ↔ MeasurableSet s
-/
theorem nullMeasurableSet_insert {a : α} {s : Set α} :
    NullMeasurableSet (insert a s) μ ↔ NullMeasurableSet s μ :=
  measurableSet_insert
/-
**MeasureTheory.nullMeasurableSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：nullMeasurableSet_eq {a : α} : NullMeasurableSet { x | x = a } μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nullMeasurableSet_singleton`：nullMeasurableSet_singleton (
x : α) : NullMeasurableSet {x} μ
-/
theorem nullMeasurableSet_eq {a : α} : NullMeasurableSet { x | x = a } μ :=
  nullMeasurableSet_singleton a
/-
**MeasureTheory._root_.Set.Finite.nullMeasurableSet** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Set.Finite.nullMeasurableSet (hs : s.Finite) : NullMeasurableSet s μ :=
  Finite.measurableSet hs
/-
**MeasureTheory._root_.Finset.nullMeasurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Finset.nullMeasurableSet (s : Finset α) : NullMeasurableSet (↑s) μ := by
  apply Finset.measurableSet

end MeasurableSingletonClass

/-
**MeasureTheory._root_.Set.Finite.nullMeasurableSet_biUnion** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.nullMeasurableSet_biUnion {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finite.measurableSet_biUnion hs h
/-
**MeasureTheory._root_.Finset.nullMeasurableSet_biUnion** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.nullMeasurableSet_biUnion {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finset.measurableSet_biUnion s h
/-
**MeasureTheory._root_.Set.Finite.nullMeasurableSet_sUnion** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.nullMeasurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋃₀ s) μ :=
  Finite.measurableSet_sUnion hs h
/-
**MeasureTheory._root_.Set.Finite.nullMeasurableSet_biInter** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.nullMeasurableSet_biInter {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  Finite.measurableSet_biInter hs h
/-
**MeasureTheory._root_.Finset.nullMeasurableSet_biInter** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.nullMeasurableSet_biInter {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  s.finite_toSet.nullMeasurableSet_biInter h
/-
**MeasureTheory._root_.Set.Finite.nullMeasurableSet_sInter** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.nullMeasurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋂₀ s) μ :=
  NullMeasurableSet.sInter (Finite.countable hs) h
/-
**MeasureTheory.nullMeasurableSet_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：nullMeasurableSet_toMeasurable : NullMeasurableSet (toMeasurable μ s) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
-/
theorem nullMeasurableSet_toMeasurable : NullMeasurableSet (toMeasurable μ s) μ :=
  (measurableSet_toMeasurable _ _).nullMeasurableSet

variable [MeasurableSingletonClass α] {mβ : MeasurableSpace β} [MeasurableSingletonClass β]
/-
**MeasureTheory.measure_preimage_fst_singleton_eq_tsum** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：measure_preimage_fst_singleton_eq_tsum [Countable β] (μ : Measure (α × β))
 (x : α) : μ (Prod.fst ⁻¹' {x}) = ∑' y, μ {(x, y)}
参数：μ : Measure (α × β)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用引理 `Set.preimage_fst_singleton_eq_range`：preimage_fst_singleton_eq_range : (
Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·)
-/
lemma measure_preimage_fst_singleton_eq_tsum [Countable β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑' y, μ {(x, y)} := by
  rw [← measure_iUnion (by simp [Pairwise]) fun _ ↦ .singleton _, iUnion_singleton_eq_range,
    preimage_fst_singleton_eq_range]
/-
**MeasureTheory.measure_preimage_snd_singleton_eq_tsum** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：measure_preimage_snd_singleton_eq_tsum [Countable α] (μ : Measure (α × β))
 (y : β) : μ (Prod.snd ⁻¹' {y}) = ∑' x, μ {(x, y)}
参数：μ : Measure (α × β)；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma measure_preimage_snd_singleton_eq_tsum [Countable α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑' x, μ {(x, y)} := by
  have : Prod.snd ⁻¹' {y} = ⋃ x : α, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this, measure_iUnion] <;> simp [Pairwise]
/-
**MeasureTheory.measure_preimage_fst_singleton_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：measure_preimage_fst_singleton_eq_sum [Fintype β] (μ : Measure (α × β)) (x
 : α) : μ (Prod.fst ⁻¹' {x}) = ∑ y, μ {(x, y)}
参数：μ : Measure (α × β)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.measure_preimage_fst_singleton_eq_tsum`：measure_preimage_f
st_singleton_eq_tsum [Countable β] (μ : Measure (α × β)) (x : α) : μ (Prod.fst ⁻
¹' {x}) = ∑' y, μ {(x, y)}
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
lemma measure_preimage_fst_singleton_eq_sum [Fintype β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑ y, μ {(x, y)} := by
  rw [measure_preimage_fst_singleton_eq_tsum μ x, tsum_fintype]
/-
**MeasureTheory.measure_preimage_snd_singleton_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：measure_preimage_snd_singleton_eq_sum [Fintype α] (μ : Measure (α × β)) (y
 : β) : μ (Prod.snd ⁻¹' {y}) = ∑ x, μ {(x, y)}
参数：μ : Measure (α × β)；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.measure_preimage_snd_singleton_eq_tsum`：measure_preimage_s
nd_singleton_eq_tsum [Countable α] (μ : Measure (α × β)) (y : β) : μ (Prod.snd ⁻
¹' {y}) = ∑' x, μ {(x, y)}
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
lemma measure_preimage_snd_singleton_eq_sum [Fintype α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑ x, μ {(x, y)} := by
  rw [measure_preimage_snd_singleton_eq_tsum μ y, tsum_fintype]

end

section NullMeasurable

variable [m : MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {μ : Measure α}

/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set.

A similar notion is `AEMeasurable`. That notion is equivalent to `NullMeasurable` if
the σ-algebra on the codomain is countably generated, but stronger in general. -/
/-
**MeasureTheory.NullMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：NullMeasurable (f : α -> β) (μ : Measure α
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` is null measurable if the preimage of a measurable set is
 a null
measurable set.

A similar notion is `AEMeasurable`. That notion is equivalent to `NullMeasurable
` if
the σ-algebra on the codomain is countably generated, but stronger in general.
-/
def NullMeasurable (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ
/-
**MeasureTheory._root_.MeasureTheory.nullMeasurable_iff_eventuallyMeasurable** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.nullMeasurable_iff_eventuallyMeasurable (f : α → β) :
    NullMeasurable f μ ↔ EventuallyMeasurable m (ae μ) f := by rfl
/-
**MeasureTheory._root_.Measurable.nullMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Measurable.nullMeasurable (h : Measurable f) : NullMeasurable f μ :=
  h.eventuallyMeasurable
/-
**MeasureTheory.NullMeasurable.measurable'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.NullMeasurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [m : MeasurableSpace α] [inst : Measurable
Space β] {f : α → β}   {μ : MeasureTheory.Measure α}, MeasureTheory.NullMeasurab
le f μ → Measurable f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem NullMeasurable.measurable' (h : NullMeasurable f μ) :
    @Measurable (NullMeasurableSpace α μ) β _ _ f :=
  h
/-
**MeasureTheory.Measurable.comp_nullMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [m : MeasurableSpace α] [in
st : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {f : α → β} {μ : MeasureT
heory.Measure α} {g : β → γ},   Measurable g → MeasureTheory.NullMeasurable f μ 
→ MeasureTheory.NullMeasurable (g ∘ f) μ
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.nullMeasurable_iff_eventuallyMeasurable`：∀ {α : Type u_2} 
{β : Type u_3} [m : MeasurableSpace α] [inst : MeasurableSpace β] {μ : MeasureTh
eory.Measure α}   (f : α → β), MeasureTheor…
· 使用定理 `Measurable.comp_eventuallyMeasurable`：Measurable.comp_eventuallyMeasurab
le (hh : Measurable h) (hf : EventuallyMeasurable m l f) : EventuallyMeasurable 
m l (h ∘ f)
-/
theorem Measurable.comp_nullMeasurable {g : β → γ} (hg : Measurable g) (hf : NullMeasurable f μ) :
    NullMeasurable (g ∘ f) μ := by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact hg.comp_eventuallyMeasurable hf
/-
**MeasureTheory.NullMeasurable.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Nu
llMeasurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [m : MeasurableSpace α] [inst : Measurable
Space β] {f : α → β}   {μ : MeasureTheory.Measure α} {g : α → β},   MeasureTheor
y.NullMeasurable f μ → f =ᵐ[μ] g → MeasureTheory.NullMeasurable g μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.nullMeasurable_iff_eventuallyMeasurable`：∀ {α : Type u_2} 
{β : Type u_3} [m : MeasurableSpace α] [inst : MeasurableSpace β] {μ : MeasureTh
eory.Measure α}   (f : α → β), MeasureTheor…
· 使用定理 `EventuallyMeasurable.congr`：EventuallyMeasurable.congr (hf : EventuallyM
easurable m l f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem NullMeasurable.congr {g : α → β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g) :
    NullMeasurable g μ := by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact EventuallyMeasurable.congr hf hg.symm

end NullMeasurable

section IsComplete

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
/-
**MeasureTheory.Measure.IsComplete** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：{α : Type u_2} → {x : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can m
ore simply state
  that a set `s` is null if `μ s = 0`.
-/
class Measure.IsComplete {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : ∀ s, μ s = 0 → MeasurableSet s

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}
/-
**MeasureTheory.Measure.isComplete_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α},  
 μ.IsComplete ↔ ∀ (s : Set α), μ s = 0 → MeasurableSet s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsComplete.out'`：∀ {α : Type u_2} {x : MeasurableS
pace α} {μ : MeasureTheory.Measure α} [self : μ.IsComplete] (s : Set α),   μ s =
 0 → MeasurableSet s
-/
theorem Measure.isComplete_iff : μ.IsComplete ↔ ∀ s, μ s = 0 → MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**MeasureTheory.Measure.IsComplete.out** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure.IsComplete`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α},  
 μ.IsComplete → ∀ (s : Set α), μ s = 0 → MeasurableSet s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsComplete.out'`：∀ {α : Type u_2} {x : MeasurableS
pace α} {μ : MeasureTheory.Measure α} [self : μ.IsComplete] (s : Set α),   μ s =
 0 → MeasurableSet s
-/
theorem Measure.IsComplete.out (h : μ.IsComplete) : ∀ s, μ s = 0 → MeasurableSet s :=
  h.1
/-
**MeasureTheory.measurableSet_of_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurableSet_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s
参数：hs : μ s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsComplete.out'`：∀ {α : Type u_2} {x : MeasurableS
pace α} {μ : MeasureTheory.Measure α} [self : μ.IsComplete] (s : Set α),   μ s =
 0 → MeasurableSet s
-/
theorem measurableSet_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs
/-
**MeasureTheory.NullMeasurableSet.measurable_of_complete** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set α},   MeasureTheory.NullMeasurableSet s μ → ∀ [μ.IsComplete], MeasurableS
et s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measurableSet_of_null`：measurableSet_of_null [μ.IsComplete
] (hs : μ s = 0) : MeasurableSet s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq`：toMeasurable_ae_eq (
h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
-/
theorem NullMeasurableSet.measurable_of_complete (hs : NullMeasurableSet s μ) [μ.IsComplete] :
    MeasurableSet s :=
  sdiff_sdiff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diff
      (measurableSet_of_null (ae_le_set.1 <|
        EventuallyEq.le (NullMeasurableSet.toMeasurable_ae_eq hs)))
/-
**MeasureTheory.NullMeasurable.measurable_of_complete** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.NullMeasurable`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [μ.IsComplete]   {_m1 : MeasurableSpace β} {f : α → β}, MeasureTheo
ry.NullMeasurable f μ → Measurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.measurable_of_complete`：∀ {α : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasureTh
eory.NullMeasurableSet s μ → ∀ [μ.IsComplete…
-/
theorem NullMeasurable.measurable_of_complete [μ.IsComplete] {_m1 : MeasurableSpace β} {f : α → β}
    (hf : NullMeasurable f μ) : Measurable f := fun _s hs => (hf hs).measurable_of_complete
/-
**MeasureTheory._root_.Measurable.congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [_hμ : μ.IsComplete] {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  NullMeasurable.measurable_of_complete (NullMeasurable.congr hf.nullMeasurable hfg)

namespace Measure

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
/-
**MeasureTheory.Measure.completion** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：completion {_ : MeasurableSpace α} (μ : Measure α) : MeasureTheory.Measure
 (NullMeasurableSpace α μ) where toOuterMeasure
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a measure we can complete it to a (complete) measure on all null measurabl
e sets.
-/
def completion {_ : MeasurableSpace α} (μ : Measure α) :
    MeasureTheory.Measure (NullMeasurableSpace α μ) where
  toOuterMeasure := μ.toOuterMeasure
  m_iUnion _ hs hd := measure_iUnion₀ (hd.mono fun _ _ h => h.aedisjoint) hs
  trim_le := by
    nth_rewrite 2 [← μ.trimmed]
    exact OuterMeasure.trim_anti_measurableSpace _ fun _ ↦ MeasurableSet.nullMeasurableSet
/-
**MeasureTheory.Measure.completion.isComplete** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.completion`。
形式化陈述：∀ {α : Type u_2} {_m : MeasurableSpace α} (μ : MeasureTheory.Measure α), μ
.completion.IsComplete
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
-/
instance completion.isComplete {_m : MeasurableSpace α} (μ : Measure α) : μ.completion.IsComplete :=
  ⟨fun _z hz => NullMeasurableSet.of_null hz⟩

@[simp]
/-
**MeasureTheory.Measure.coe_completion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.completion = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.completion = μ :=
  rfl
/-
**MeasureTheory.Measure.completion_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : μ.c
ompletion s = μ s
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.completion s = μ s :=
  rfl

@[simp]
/-
**MeasureTheory.Measure.ae_completion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：ae_completion {_ : MeasurableSpace α} (μ : Measure α) : ae μ.completion = 
ae μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem ae_completion {_ : MeasurableSpace α} (μ : Measure α) : ae μ.completion = ae μ := rfl

end Measure

end IsComplete

end MeasureTheory

