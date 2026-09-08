/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Simple functions

A function `f` from a measurable space to any type is called *simple*, if every preimage `f ⁻¹' {x}`
is measurable, and the range is finite. In this file, we define simple functions and establish their
basic properties; and we construct a sequence of simple functions approximating an arbitrary Borel
measurable function `f : α → ℝ≥0∞`.

The theorem `Measurable.ennreal_induction` shows that in order to prove something for an arbitrary
measurable function into `ℝ≥0∞`, it is sufficient to show that the property holds for (multiples of)
characteristic functions and is closed under addition and supremum of increasing sequences of
functions.
-/

@[expose] public section


noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This struc
ture bundles
a function with these properties.
-/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  /-- The underlying function -/
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

/-
**MeasureTheory.SimpleFunc.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：instFunLike : FunLike (α ->ₛ β) α β where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (α →ₛ β) α β where
  coe := toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
/-
**MeasureTheory.SimpleFunc.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：coe_injective ⦃f g : α ->ₛ β⦄ (H : (f : α -> β) = g) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g := DFunLike.ext' H

@[ext]
/-
**MeasureTheory.SimpleFunc.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SimpleFu
nc`。
形式化陈述：ext {f g : α ->ₛ β} (H : forall a, f a = g a) : f = g
参数：H : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ H
/-
**MeasureTheory.SimpleFunc.finite_range** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：finite_range (f : α ->ₛ β) : (Set.range f).Finite
参数：f : α ->ₛ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.finite_range'`：∀ {α : Type u} [inst : Measurabl
eSpace α] {β : Type v} (self : MeasureTheory.SimpleFunc α β),   (Set.range self.
toFun).Finite
-/
theorem finite_range (f : α →ₛ β) : (Set.range f).Finite :=
  f.finite_range'
/-
**MeasureTheory.SimpleFunc.measurableSet_fiber** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：measurableSet_fiber (f : α ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
参数：f : α ->ₛ β；x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber'`：∀ {α : Type u} [inst : Me
asurableSpace α] {β : Type v} (self : MeasureTheory.SimpleFunc α β) (x : β),   M
easurableSet (self.toFun ⁻¹' {x})
-/
theorem measurableSet_fiber (f : α →ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x
/-
**MeasureTheory.SimpleFunc.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simpl
eFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] (f : α → β) (h 
: ∀ (x : β), MeasurableSet (f ⁻¹' {x}))   (h' : (Set.range f).Finite), ⇑{ toFun 
:= f, measurableSet_fiber' := h, finite_range' := h' } = f
参数：f : α → β；h : ∀ (x : β), MeasurableSet (f ⁻¹' {x})；h' : (Set.range f).Finite。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (f : α → β) (h h') : ⇑(mk f h h') = f := rfl
/-
**MeasureTheory.SimpleFunc.apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：apply_mk (f : α -> β) (h h') (x : α) : SimpleFunc.mk f h h' x = f x
参数：f : α -> β；h h'；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_mk (f : α → β) (h h') (x : α) : SimpleFunc.mk f h h' x = f x :=
  rfl

/-- Simple function defined on a finite type. -/
/-
**MeasureTheory.SimpleFunc.ofFinite** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：ofFinite [Finite α] [MeasurableSingletonClass α] (f : α -> β) : α ->ₛ β wh
ere toFun
参数：f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e

--- 原说明 ---
Simple function defined on a finite type.
-/
def ofFinite [Finite α] [MeasurableSingletonClass α] (f : α → β) : α →ₛ β where
  toFun := f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f


/-- Simple function defined on the empty type. -/
/-
**MeasureTheory.SimpleFunc.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：ofIsEmpty [IsEmpty α] : α ->ₛ β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simple function defined on the empty type.
-/
def ofIsEmpty [IsEmpty α] : α →ₛ β := ofFinite isEmptyElim

/-- Range of a simple function `α →ₛ β` as a `Finset β`. -/
/-
**MeasureTheory.SimpleFunc.range** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simple
Func`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : MeasurableSpace α] → MeasureTheo
ry.SimpleFunc α β → Finset β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite

--- 原说明 ---
Range of a simple function `α →ₛ β` as a `Finset β`.
-/
protected def range (f : α →ₛ β) : Finset β :=
  f.finite_range.toFinset

@[simp]
/-
**MeasureTheory.SimpleFunc.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：mem_range {f : α ->ₛ β} {b} : b in f.range ↔ b in range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite
-/
theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
  Finite.mem_toFinset _
/-
**MeasureTheory.SimpleFunc.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：mem_range_self (f : α ->ₛ β) (x : α) : f x in f.range
参数：f : α ->ₛ β；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
-/
theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：coe_range (f : α ->ₛ β) : (↑f.range : Set β) = Set.range f
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite
-/
theorem coe_range (f : α →ₛ β) : (↑f.range : Set β) = Set.range f :=
  f.finite_range.coe_toFinset
/-
**MeasureTheory.SimpleFunc.mem_range_of_measure_ne_zero** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.SimpleFunc`。
形式化陈述：mem_range_of_measure_ne_zero {f : α ->ₛ β} {x : β} {μ : Measure α} (H : μ 
(f ⁻¹' {x}) != 0) : x in f.range
参数：H : μ (f ⁻¹' {x}) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
-/
theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
    x ∈ f.range :=
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩
/-
**MeasureTheory.SimpleFunc.forall_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：forall_mem_range {f : α ->ₛ β} {p : β -> Prop} : (forall y in f.range, p y
) ↔ forall x, p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_range {f : α →ₛ β} {p : β → Prop} : (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) := by
  simp only [mem_range, Set.forall_mem_range]
/-
**MeasureTheory.SimpleFunc.exists_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：exists_range_iff {f : α ->ₛ β} {p : β -> Prop} : (exists y in f.range, p y
) ↔ exists x, p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
-/
theorem exists_range_iff {f : α →ₛ β} {p : β → Prop} : (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) := by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff
/-
**MeasureTheory.SimpleFunc.preimage_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：preimage_eq_empty_iff (f : α ->ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range
参数：f : α ->ₛ β；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.preimage_singleton_eq_empty`：preimage_singleton_eq_empty {f : α -> β
} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
-/
theorem preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
  preimage_singleton_eq_empty.trans <| not_congr mem_range.symm
/-
**MeasureTheory.SimpleFunc.exists_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：exists_forall_le [Nonempty β] [Preorder β] [IsDirectedOrder β] (f : α ->ₛ 
β) : exists C, forall x, f x <= C
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.forall_mem_range`：forall_mem_range {f : α ->ₛ β
} {p : β -> Prop} : (forall y in f.range, p y) ↔ forall x, p (f x)
· 使用定理 `Finset.exists_le`：Finset.exists_le [Nonempty α] [Preorder α] [IsDirected
Order α] (s : Finset α) : exists M, forall i in s, i <= M
-/
theorem exists_forall_le [Nonempty β] [Preorder β] [IsDirectedOrder β] (f : α →ₛ β) :
    ∃ C, ∀ x, f x ≤ C :=
  f.range.exists_le.imp fun _ => forall_mem_range.1

/-- Constant function as a `SimpleFunc`. -/
/-
**MeasureTheory.SimpleFunc.const** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simple
Func`。
形式化陈述：const (α) {β} [MeasurableSpace α] (b : β) : α ->ₛ β
参数：α；b : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_range_const`：finite_range_const {c : β} : (range fun _ : α =>
 c).Finite

--- 原说明 ---
Constant function as a `SimpleFunc`.
-/
def const (α) {β} [MeasurableSpace α] (b : β) : α →ₛ β :=
  ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩
/-
**MeasureTheory.SimpleFunc.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：instInhabited [Inhabited β] : Inhabited (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Inhabited β] : Inhabited (α →ₛ β) :=
  ⟨const _ default⟩
/-
**MeasureTheory.SimpleFunc.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：const_apply (a : α) (b : β) : (const α b) a = b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (a : α) (b : β) : (const α b) a = b :=
  rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：coe_const (b : β) : ⇑(const α b) = Function.const α b
参数：b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.range_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：range_const (α) [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).ran
ge = {b}
参数：α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_const (α) [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).range = {b} :=
  Finset.coe_injective <| by simp +unfoldPartialApp [Function.const]
/-
**MeasureTheory.SimpleFunc.range_const_subset** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：range_const_subset (α) [MeasurableSpace α] (b : β) : (const α b).range sub
seteq {b}
参数：α；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem range_const_subset (α) [MeasurableSpace α] (b : β) : (const α b).range ⊆ {b} :=
  Finset.coe_subset.1 <| by simp
/-
**MeasureTheory.SimpleFunc.simpleFunc_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：simpleFunc_bot {α} (f : @SimpleFunc α ⊥ β) [Nonempty β] : exists c, forall
 x, f x = c
参数：f : @SimpleFunc α ⊥ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `Set.exists_eq_const_of_preimage_singleton`：exists_eq_const_of_preimage_s
ingleton [Nonempty β] {f : α -> β} (hf : forall b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b}
 = univ) : exists b, f = const …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem simpleFunc_bot {α} (f : @SimpleFunc α ⊥ β) [Nonempty β] : ∃ c, ∀ x, f x = c := by
  have hf_meas := @SimpleFunc.measurableSet_fiber α _ ⊥ f
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  exact (exists_eq_const_of_preimage_singleton hf_meas).imp fun c hc ↦ congr_fun hc
/-
**MeasureTheory.SimpleFunc.simpleFunc_bot'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：simpleFunc_bot' {α} [Nonempty β] (f : @SimpleFunc α ⊥ β) : exists c, f = @
SimpleFunc.const α _ ⊥ c
参数：f : @SimpleFunc α ⊥ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `MeasureTheory.SimpleFunc.simpleFunc_bot`：simpleFunc_bot {α} (f : @Simple
Func α ⊥ β) [Nonempty β] : exists c, forall x, f x = c
-/
theorem simpleFunc_bot' {α} [Nonempty β] (f : @SimpleFunc α ⊥ β) :
    ∃ c, f = @SimpleFunc.const α _ ⊥ c :=
  letI : MeasurableSpace α := ⊥; (simpleFunc_bot f).imp fun _ ↦ ext
/-
**MeasureTheory.SimpleFunc.measurableSet_cut** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：measurableSet_cut (r : α -> β -> Prop) (f : α ->ₛ β) (h : forall b, Measur
ableSet { a | r a b }) : MeasurableSet { a | r a (f a) }
参数：r : α -> β -> Prop；f : α ->ₛ β；h : forall b, MeasurableSet { a | r a b }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `MeasureTheory.SimpleFunc.finite_range`：finite_range (f : α ->ₛ β) : (Set
.range f).Finite
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
-/
theorem measurableSet_cut (r : α → β → Prop) (f : α →ₛ β) (h : ∀ b, MeasurableSet { a | r a b }) :
    MeasurableSet { a | r a (f a) } := by
  have : { a | r a (f a) } = ⋃ b ∈ range f, { a | r a b } ∩ f ⁻¹' {b} := by
    ext a
    suffices r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  exact
    MeasurableSet.biUnion f.finite_range.countable fun b _ =>
      MeasurableSet.inter (h b) (f.measurableSet_fiber _)

@[measurability]
/-
**MeasureTheory.SimpleFunc.measurableSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：measurableSet_preimage (f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
参数：f : α ->ₛ β；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_cut`：measurableSet_cut (r : α -> 
β -> Prop) (f : α ->ₛ β) (h : forall b, MeasurableSet { a | r a b }) : Measurabl
eSet { a | r a (f a) }
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
-/
theorem measurableSet_preimage (f : α →ₛ β) (s) : MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ b => b ∈ s) f fun b => MeasurableSet.const (b ∈ s)

/-- A simple function is measurable -/
@[fun_prop]
/-
**MeasureTheory.SimpleFunc.measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   (f : MeasureTheory.SimpleFunc α β), Measurable ⇑f
参数：f : MeasureTheory.SimpleFunc α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)

--- 原说明 ---
A simple function is measurable
-/
protected theorem measurable [MeasurableSpace β] (f : α →ₛ β) : Measurable f := fun s _ =>
  measurableSet_preimage f s

@[fun_prop]
/-
**MeasureTheory.SimpleFunc.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   (f : MeasureTheory.SimpleFunc α β)
, AEMeasurable (⇑f) μ
参数：f : MeasureTheory.SimpleFunc α β；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
-/
protected theorem aemeasurable [MeasurableSpace β] {μ : Measure α} (f : α →ₛ β) :
    AEMeasurable f μ :=
  f.measurable.aemeasurable
/-
**MeasureTheory.SimpleFunc.sum_measure_preimage_singleton** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] (f : MeasureThe
ory.SimpleFunc α β)   {μ : MeasureTheory.Measure α} (s : Finset β), ∑ y ∈ s, μ (
⇑f ⁻¹' {y}) = μ (⇑f ⁻¹' ↑s)
参数：f : MeasureTheory.SimpleFunc α β；s : Finset β；⇑f ⁻¹' {y}；⇑f ⁻¹' ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.sum_measure_preimage_singleton`：sum_measure_preimage_singl
eton (s : Finset β) {f : α -> β} (hf : forall y in s, MeasurableSet (f ⁻¹' {y}))
 : (∑ b in s, μ (f ⁻¹' {b})) = μ (…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
-/
protected theorem sum_measure_preimage_singleton (f : α →ₛ β) {μ : Measure α} (s : Finset β) :
    (∑ y ∈ s, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _
/-
**MeasureTheory.SimpleFunc.sum_range_measure_preimage_singleton** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：sum_range_measure_preimage_singleton (f : α ->ₛ β) (μ : Measure α) : (∑ y 
in f.range, μ (f ⁻¹' {y})) = μ univ
参数：f : α ->ₛ β；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.sum_measure_preimage_singleton`：∀ {α : Type u_1
} {β : Type u_2} [inst : MeasurableSpace α] (f : MeasureTheory.SimpleFunc α β)  
 {μ : MeasureTheory.Measure α} (s : Finset β)…
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
-/
theorem sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : Measure α) :
    (∑ y ∈ f.range, μ (f ⁻¹' {y})) = μ univ := by
  rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

open scoped Classical in
/-- If-then-else as a `SimpleFunc`. -/
/-
**MeasureTheory.SimpleFunc.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：piecewise (s : Set α) (hs : MeasurableSet s) (f g : α ->ₛ β) : α ->ₛ β
参数：s : Set α；hs : MeasurableSet s；f g : α ->ₛ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If-then-else as a `SimpleFunc`.
-/
def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α →ₛ β) : α →ₛ β :=
  ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩

open scoped Classical in
@[simp]
/-
**MeasureTheory.SimpleFunc.coe_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β) : ⇑(piece
wise s hs f g) = s.piecewise f g
参数：hs : MeasurableSet s；f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) :
    ⇑(piecewise s hs f g) = s.piecewise f g :=
  rfl

open scoped Classical in
/-
**MeasureTheory.SimpleFunc.piecewise_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β) (a) : p
iecewise s hs f g a = if a in s then f a else g a
参数：hs : MeasurableSet s；f g : α ->ₛ β；a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) (a) :
    piecewise s hs f g a = if a ∈ s then f a else g a :=
  rfl

open scoped Classical in
@[simp]
/-
**MeasureTheory.SimpleFunc.piecewise_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：piecewise_compl {s : Set α} (hs : MeasurableSet sᶜ) (f g : α ->ₛ β) : piec
ewise sᶜ hs f g = piecewise s hs.of_compl g f
参数：hs : MeasurableSet sᶜ；f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.coe_injective`：coe_injective ⦃f g : α ->ₛ β⦄ (H
 : (f : α -> β) = g) : f = g
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_compl`：piecewise_compl [forall i, Decidable (i in sᶜ)] : s
ᶜ.piecewise f g = s.piecewise g f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_compl {s : Set α} (hs : MeasurableSet sᶜ) (f g : α →ₛ β) :
    piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
  coe_injective <| by simp

@[simp]
/-
**MeasureTheory.SimpleFunc.piecewise_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：piecewise_univ (f g : α ->ₛ β) : piecewise univ MeasurableSet.univ f g = f
参数：f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.coe_injective`：coe_injective ⦃f g : α ->ₛ β⦄ (H
 : (f : α -> β) = g) : f = g
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_univ`：piecewise_univ [forall i : α, Decidable (i in (Set.u
niv : Set α))] : piecewise Set.univ f g = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_univ (f g : α →ₛ β) : piecewise univ MeasurableSet.univ f g = f :=
  coe_injective <| by simp

@[simp]
/-
**MeasureTheory.SimpleFunc.piecewise_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：piecewise_empty (f g : α ->ₛ β) : piecewise ∅ MeasurableSet.empty f g = g
参数：f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.coe_injective`：coe_injective ⦃f g : α ->ₛ β⦄ (H
 : (f : α -> β) = g) : f = g
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_empty`：piecewise_empty [forall i : α, Decidable (i in (∅ :
 Set α))] : piecewise ∅ f g = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_empty (f g : α →ₛ β) : piecewise ∅ MeasurableSet.empty f g = g :=
  coe_injective <| by simp

@[simp]
/-
**MeasureTheory.SimpleFunc.piecewise_same** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：piecewise_same (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) : piecewis
e s hs f f = f
参数：f : α ->ₛ β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.coe_injective`：coe_injective ⦃f g : α ->ₛ β⦄ (H
 : (f : α -> β) = g) : f = g
· 使用定理 `Set.piecewise_same`：piecewise_same : s.piecewise f f = f
-/
theorem piecewise_same (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) :
    piecewise s hs f f = f := by
  classical
  exact coe_injective <| Set.piecewise_same _ _

/-- Dependent If-then-else as a `SimpleFunc`. -/
@[simps]
/-
**MeasureTheory.SimpleFunc.dite** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.SimpleF
unc`。
形式化陈述：dite (s : Set α) (hs : MeasurableSet s) (f : s ->ₛ β) (g : (sᶜ : Set α) ->
ₛ β) : α ->ₛ β where toFun x
参数：s : Set α；hs : MeasurableSet s；f : s ->ₛ β；g : (sᶜ : Set α) ->ₛ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent If-then-else as a `SimpleFunc`.
-/
def dite (s : Set α) (hs : MeasurableSet s) (f : s →ₛ β) (g : (sᶜ : Set α) →ₛ β) : α →ₛ β where
  toFun x := open scoped Classical in if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩
  measurableSet_fiber' x := by
    classical
    let : MeasurableSpace β := ⊤
    exact Measurable.dite f.measurable g.measurable hs trivial
  finite_range' := (f.finite_range.union g.finite_range).subset (by grind)
/-
**MeasureTheory.SimpleFunc.support_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：support_indicator [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α ->ₛ β
) : Function.support (f.piecewise s hs (SimpleFunc.const α 0)) = s inter Functio
n.support f
参数：hs : MeasurableSet s；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.support_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M},   Function.support (s.indicator f) = s ∩ Function.suppor
t f
-/
theorem support_indicator [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α →ₛ β) :
    Function.support (f.piecewise s hs (SimpleFunc.const α 0)) = s ∩ Function.support f :=
  Set.support_indicator

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-
**MeasureTheory.SimpleFunc.range_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：range_indicator {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonemp
ty) (hs_ne_univ : s != univ) (x y : β) : (piecewise s hs (const α x) (const α y)
).range = {x, y}
参数：hs : MeasurableSet s；hs_nonempty : s.Nonempty；hs_ne_univ : s != univ；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `Set.range_piecewise`：range_piecewise (f g : α -> β) : range (s.piecewise
 f g) = f '' s union g '' sᶜ
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_indicator {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
    (hs_ne_univ : s ≠ univ) (x y : β) :
    (piecewise s hs (const α x) (const α y)).range = {x, y} := by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union, Function.const]
/-
**MeasureTheory.SimpleFunc.measurable_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：measurable_bind [MeasurableSpace γ] (f : α ->ₛ β) (g : β -> α -> γ) (hg : 
forall b, Measurable (g b)) : Measurable fun a => g (f a) a
参数：f : α ->ₛ β；g : β -> α -> γ；hg : forall b, Measurable (g b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_cut`：measurableSet_cut (r : α -> 
β -> Prop) (f : α ->ₛ β) (h : forall b, MeasurableSet { a | r a b }) : Measurabl
eSet { a | r a (f a) }
-/
theorem measurable_bind [MeasurableSpace γ] (f : α →ₛ β) (g : β → α → γ)
    (hg : ∀ b, Measurable (g b)) : Measurable fun a => g (f a) a := fun s hs =>
  f.measurableSet_cut (fun a b => g b a ∈ s) fun b => hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
/-
**MeasureTheory.SimpleFunc.bind** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.SimpleF
unc`。
形式化陈述：bind (f : α ->ₛ β) (g : β -> α ->ₛ γ) : α ->ₛ γ
参数：f : α ->ₛ β；g : β -> α ->ₛ γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple 
functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind 
g a = g (f a) a`.
-/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
  ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
    (f.finite_range.biUnion fun b _ => (g b).finite_range).subset <| by
      rintro _ ⟨a, rfl⟩; simp⟩

@[simp]
/-
**MeasureTheory.SimpleFunc.bind_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：bind_apply (f : α ->ₛ β) (g : β -> α ->ₛ γ) (a) : f.bind g a = g (f a) a
参数：f : α ->ₛ β；g : β -> α ->ₛ γ；a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) : f.bind g a = g (f a) a :=
  rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
function `g ∘ f : α →ₛ γ` -/
/-
**MeasureTheory.SimpleFunc.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.SimpleFu
nc`。
形式化陈述：map (g : β -> γ) (f : α ->ₛ β) : α ->ₛ γ
参数：g : β -> γ；f : α ->ₛ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` retur
n the simple
function `g ∘ f : α →ₛ γ`
-/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ :=
  bind f (const α ∘ g)
/-
**MeasureTheory.SimpleFunc.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：map_apply (g : β -> γ) (f : α ->ₛ β) (a) : f.map g a = g (f a)
参数：g : β -> γ；f : α ->ₛ β；a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) :=
  rfl
/-
**MeasureTheory.SimpleFunc.map_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：map_map (g : β -> γ) (h : γ -> δ) (f : α ->ₛ β) : (f.map g).map h = f.map 
(h ∘ g)
参数：g : β -> γ；h : γ -> δ；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_map (g : β → γ) (h : γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) :=
  rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_map (g : β -> γ) (f : α ->ₛ β) : (f.map g : α -> γ) = g ∘ f
参数：g : β -> γ；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f :=
  rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.range_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：range_map [DecidableEq γ] (g : β -> γ) (f : α ->ₛ β) : (f.map g).range = f
.range.image g
参数：g : β -> γ；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_map [DecidableEq γ] (g : β → γ) (f : α →ₛ β) : (f.map g).range = f.range.image g :=
  Finset.coe_injective <| by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

@[simp]
/-
**MeasureTheory.SimpleFunc.map_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：map_const (g : β -> γ) (b : β) : (const α b).map g = const α (g b)
参数：g : β -> γ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) :=
  rfl

open scoped Classical in
/-
**MeasureTheory.SimpleFunc.map_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：map_preimage (f : α ->ₛ β) (g : β -> γ) (s : Set γ) : f.map g ⁻¹' s = f ⁻¹
' ↑{b in f.range | g b in s}
参数：f : α ->ₛ β；g : β -> γ；s : Set γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.preimage_inter_range`：preimage_inter_range {f : α -> β} {s : Set β} 
: f ⁻¹' (s inter range f) = f ⁻¹' s
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
theorem map_preimage (f : α →ₛ β) (g : β → γ) (s : Set γ) :
    f.map g ⁻¹' s = f ⁻¹' ↑{b ∈ f.range | g b ∈ s} := by
  simp only [coe_range, sep_mem_eq, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range, ← Finset.mem_coe]
  exact preimage_comp

open scoped Classical in
/-
**MeasureTheory.SimpleFunc.map_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：map_preimage_singleton (f : α ->ₛ β) (g : β -> γ) (c : γ) : f.map g ⁻¹' {c
} = f ⁻¹' ↑{b in f.range | g b = c}
参数：f : α ->ₛ β；g : β -> γ；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.map_preimage`：map_preimage (f : α ->ₛ β) (g : β
 -> γ) (s : Set γ) : f.map g ⁻¹' s = f ⁻¹' ↑{b in f.range | g b in s}
-/
theorem map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑{b ∈ f.range | g b = c} :=
  map_preimage _ _ _

/-- Composition of a `SimpleFun` and a measurable function is a `SimpleFunc`. -/
/-
**MeasureTheory.SimpleFunc.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.SimpleF
unc`。
形式化陈述：comp [MeasurableSpace β] (f : β ->ₛ γ) (g : α -> β) (hgm : Measurable g) :
 α ->ₛ γ where toFun
参数：f : β ->ₛ γ；g : α -> β；hgm : Measurable g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a `SimpleFun` and a measurable function is a `SimpleFunc`.
-/
def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ where
  toFun := f ∘ g
  finite_range' := f.finite_range.subset <| Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：coe_comp [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable 
g) : ⇑(f.comp g hgm) = f ∘ g
参数：f : β ->ₛ γ；hgm : Measurable g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    ⇑(f.comp g hgm) = f ∘ g :=
  rfl
/-
**MeasureTheory.SimpleFunc.range_comp_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：range_comp_subset_range [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hg
m : Measurable g) : (f.comp g hgm).range subseteq f.range
参数：f : β ->ₛ γ；hgm : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
-/
theorem range_comp_subset_range [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    (f.comp g hgm).range ⊆ f.range :=
  Finset.coe_subset.1 <| by simp only [coe_range, coe_comp, Set.range_comp_subset_range]

/-- Extend a `SimpleFunc` along a measurable embedding: `f₁.extend g hg f₂` is the function
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`. -/
/-
**MeasureTheory.SimpleFunc.extend** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simpl
eFunc`。
形式化陈述：extend [MeasurableSpace β] (f₁ : α ->ₛ γ) (g : α -> β) (hg : MeasurableEmb
edding g) (f₂ : β ->ₛ γ) : β ->ₛ γ where toFun
参数：f₁ : α ->ₛ γ；g : α -> β；hg : MeasurableEmbedding g；f₂ : β ->ₛ γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a `SimpleFunc` along a measurable embedding: `f₁.extend g hg f₂` is the f
unction
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`.
-/
def extend [MeasurableSpace β] (f₁ : α →ₛ γ) (g : α → β) (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : β →ₛ γ where
  toFun := Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.subset (image_subset_range _ _)).subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    let : MeasurableSpace γ := ⊤; have : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurableSet_singleton _)

@[simp]
/-
**MeasureTheory.SimpleFunc.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：extend_apply [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : Measura
bleEmbedding g) (f₂ : β ->ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x
参数：f₁ : α ->ₛ γ；hg : MeasurableEmbedding g；f₂ : β ->ₛ γ；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
-/
theorem extend_apply [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
  hg.injective.extend_apply _ _ _

@[simp]
/-
**MeasureTheory.SimpleFunc.extend_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：extend_apply' [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : Measur
ableEmbedding g) (f₂ : β ->ₛ γ) {y : β} (h : ¬exists x, g x = y) : (f₁.extend g 
hg f₂) y = f₂ y
参数：f₁ : α ->ₛ γ；hg : MeasurableEmbedding g；f₂ : β ->ₛ γ；h : ¬exists x, g x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
-/
theorem extend_apply' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) {y : β} (h : ¬∃ x, g x = y) : (f₁.extend g hg f₂) y = f₂ y :=
  Function.extend_apply' _ _ _ h

@[simp]
/-
**MeasureTheory.SimpleFunc.extend_comp_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：extend_comp_eq' [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : Meas
urableEmbedding g) (f₂ : β ->ₛ γ) : f₁.extend g hg f₂ ∘ g = f₁
参数：f₁ : α ->ₛ γ；hg : MeasurableEmbedding g；f₂ : β ->ₛ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.extend_apply`：extend_apply [MeasurableSpace β] 
(f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g) (f₂ : β ->ₛ γ) (x : α) 
: (f₁.extend g hg f₂) (g x)…
-/
theorem extend_comp_eq' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : f₁.extend g hg f₂ ∘ g = f₁ :=
  funext fun _ => extend_apply _ _ _ _

@[simp]
/-
**MeasureTheory.SimpleFunc.extend_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：extend_comp_eq [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : Measu
rableEmbedding g) (f₂ : β ->ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁
参数：f₁ : α ->ₛ γ；hg : MeasurableEmbedding g；f₂ : β ->ₛ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.coe_injective`：coe_injective ⦃f g : α ->ₛ β⦄ (H
 : (f : α -> β) = g) : f = g
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `MeasureTheory.SimpleFunc.extend_comp_eq'`：extend_comp_eq' [MeasurableSpa
ce β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g) (f₂ : β ->ₛ γ) : 
f₁.extend g hg f₂ ∘ g = f₁
-/
theorem extend_comp_eq [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
  coe_injective <| extend_comp_eq' _ hg _

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
/-
**MeasureTheory.SimpleFunc.seq** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.SimpleFu
nc`。
形式化陈述：seq (f : α ->ₛ β -> γ) (g : α ->ₛ β) : α ->ₛ γ
参数：f : α ->ₛ β -> γ；g : α ->ₛ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a simple function taking values in `β → γ` and `g` is another simple f
unction
with the same domain and codomain `β`, then `f.seq g = f a (g a)`.
-/
def seq (f : α →ₛ β → γ) (g : α →ₛ β) : α →ₛ γ :=
  f.bind fun f => g.map f

@[simp]
/-
**MeasureTheory.SimpleFunc.seq_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：seq_apply (f : α ->ₛ β -> γ) (g : α ->ₛ β) (a : α) : f.seq g a = f a (g a)
参数：f : α ->ₛ β -> γ；g : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_apply (f : α →ₛ β → γ) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) :=
  rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `fun a => (f a, g a)`. -/
/-
**MeasureTheory.SimpleFunc.pair** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.SimpleF
unc`。
形式化陈述：pair (f : α ->ₛ β) (g : α ->ₛ γ) : α ->ₛ β × γ
参数：f : α ->ₛ β；g : α ->ₛ γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `fun a => (f a, g a)`.
-/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ β × γ :=
  (f.map Prod.mk).seq g

@[simp]
/-
**MeasureTheory.SimpleFunc.pair_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：pair_apply (f : α ->ₛ β) (g : α ->ₛ γ) (a) : pair f g a = (f a, g a)
参数：f : α ->ₛ β；g : α ->ₛ γ；a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) :=
  rfl
/-
**MeasureTheory.SimpleFunc.pair_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：pair_preimage (f : α ->ₛ β) (g : α ->ₛ γ) (s : Set β) (t : Set γ) : pair f
 g ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t
参数：f : α ->ₛ β；g : α ->ₛ γ；s : Set β；t : Set γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : Set β) (t : Set γ) :
    pair f g ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

-- A special form of `pair_preimage`
/-
**MeasureTheory.SimpleFunc.pair_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：pair_preimage_singleton (f : α ->ₛ β) (g : α ->ₛ γ) (b : β) (c : γ) : pair
 f g ⁻¹' {(b, c)} = f ⁻¹' {b} inter g ⁻¹' {c}
参数：f : α ->ₛ β；g : α ->ₛ γ；b : β；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
· 使用定理 `MeasureTheory.SimpleFunc.pair_preimage`：pair_preimage (f : α ->ₛ β) (g :
 α ->ₛ γ) (s : Set β) (t : Set γ) : pair f g ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t
-/
theorem pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
    pair f g ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} := by
  rw [← singleton_prod_singleton]
  exact pair_preimage _ _ _ _
/-
**MeasureTheory.SimpleFunc.map_fst_pair** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
(f : MeasureTheory.SimpleFunc α β)   (g : MeasureTheory.SimpleFunc α γ), Measure
Theory.SimpleFunc.map Prod.fst (f.pair g) = f
参数：f : MeasureTheory.SimpleFunc α β；g : MeasureTheory.SimpleFunc α γ；f.pair g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_fst_pair (f : α →ₛ β) (g : α →ₛ γ) : (f.pair g).map Prod.fst = f := rfl
/-
**MeasureTheory.SimpleFunc.map_snd_pair** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
(f : MeasureTheory.SimpleFunc α β)   (g : MeasureTheory.SimpleFunc α γ), Measure
Theory.SimpleFunc.map Prod.snd (f.pair g) = g
参数：f : MeasureTheory.SimpleFunc α β；g : MeasureTheory.SimpleFunc α γ；f.pair g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_snd_pair (f : α →ₛ β) (g : α →ₛ γ) : (f.pair g).map Prod.snd = g := rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.bind_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：bind_const (f : α ->ₛ β) : f.bind (const α) = f
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

@[to_additive]
/-
**MeasureTheory.SimpleFunc.instOne** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：instOne [One β] : One (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne [One β] : One (α →ₛ β) :=
  ⟨const α 1⟩

@[to_additive]
/-
**MeasureTheory.SimpleFunc.instMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：instMul [Mul β] : Mul (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [Mul β] : Mul (α →ₛ β) :=
  ⟨fun f g => (f.map (· * ·)).seq g⟩

@[to_additive]
/-
**MeasureTheory.SimpleFunc.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：instDiv [Div β] : Div (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv [Div β] : Div (α →ₛ β) :=
  ⟨fun f g => (f.map (· / ·)).seq g⟩

@[to_additive]
/-
**MeasureTheory.SimpleFunc.instInv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：instInv [Inv β] : Inv (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv [Inv β] : Inv (α →ₛ β) :=
  ⟨fun f => f.map Inv.inv⟩
/-
**MeasureTheory.SimpleFunc.instSup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：instSup [Max β] : Max (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup [Max β] : Max (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩
/-
**MeasureTheory.SimpleFunc.instInf** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：instInf [Min β] : Min (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf [Min β] : Min (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩
/-
**MeasureTheory.SimpleFunc.instLE** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Simpl
eFunc`。
形式化陈述：instLE [LE β] : LE (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE [LE β] : LE (α →ₛ β) :=
  ⟨fun f g => ∀ a, f a ≤ g a⟩

@[to_additive (attr := simp)]
/-
**MeasureTheory.SimpleFunc.const_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：const_one [One β] : const α (1 : β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MeasureTheory.SimpleFunc.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_one [One β] : ⇑(1 : α ->ₛ β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one [One β] : ⇑(1 : α →ₛ β) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MeasureTheory.SimpleFunc.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_mul [Mul β] (f g : α ->ₛ β) : ⇑(f * g) = ⇑f * ⇑g
参数：f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [Mul β] (f g : α →ₛ β) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MeasureTheory.SimpleFunc.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_inv [Inv β] (f : α ->ₛ β) : ⇑(f⁻¹) = (⇑f)⁻¹
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv [Inv β] (f : α →ₛ β) : ⇑(f⁻¹) = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MeasureTheory.SimpleFunc.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_div [Div β] (f g : α ->ₛ β) : ⇑(f / g) = ⇑f / ⇑g
参数：f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div [Div β] (f g : α →ₛ β) : ⇑(f / g) = ⇑f / ⇑g :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.SimpleFunc.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_sup [Max β] (f g : α ->ₛ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup [Max β] (f g : α →ₛ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.SimpleFunc.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_inf [Min β] (f g : α ->ₛ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
参数：f g : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf [Min β] (f g : α →ₛ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[to_additive]
/-
**MeasureTheory.SimpleFunc.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：mul_apply [Mul β] (f g : α ->ₛ β) (a : α) : (f * g) a = f a * g a
参数：f g : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a :=
  rfl

@[to_additive]
/-
**MeasureTheory.SimpleFunc.div_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：div_apply [Div β] (f g : α ->ₛ β) (x : α) : (f / g) x = f x / g x
参数：f g : α ->ₛ β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_apply [Div β] (f g : α →ₛ β) (x : α) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
/-
**MeasureTheory.SimpleFunc.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：inv_apply [Inv β] (f : α ->ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹
参数：f : α ->ₛ β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply [Inv β] (f : α →ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
/-
**MeasureTheory.SimpleFunc.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：sup_apply [Max β] (f g : α ->ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a
参数：f g : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply [Max β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
/-
**MeasureTheory.SimpleFunc.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：inf_apply [Min β] (f g : α ->ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a
参数：f g : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_apply [Min β] (f g : α →ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.SimpleFunc.range_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：range_one [Nonempty α] [One β] : (1 : α ->ₛ β).range = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_one`：Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.ra
nge (1 : α -> β) = {1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_one [Nonempty α] [One β] : (1 : α →ₛ β).range = {1} :=
  Finset.ext fun x => by simp

@[simp]
/-
**MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：range_eq_empty_of_isEmpty {β} [hα : IsEmpty α] (f : α ->ₛ β) : f.range = ∅
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_eq_empty_of_isEmpty {β} [hα : IsEmpty α] (f : α →ₛ β) : f.range = ∅ := by
  ext
  simp
/-
**MeasureTheory.SimpleFunc.eq_zero_of_mem_range_zero** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：eq_zero_of_mem_range_zero [Zero β] : forall {y : β}, y in (0 : α ->ₛ β).ra
nge -> y = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.forall_mem_range`：forall_mem_range {f : α ->ₛ β
} {p : β -> Prop} : (forall y in f.range, p y) ↔ forall x, p (f x)
-/
theorem eq_zero_of_mem_range_zero [Zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
  @(forall_mem_range.2 fun _ => rfl)

@[to_additive]
/-
**MeasureTheory.SimpleFunc.mul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq_map₂ [Mul β] (f g : α →ₛ β) : f * g = (pair f g).map fun p : β × β => p.1 * p.2 :=
  rfl
/-
**MeasureTheory.SimpleFunc.sup_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_eq_map₂ [Max β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2 :=
  rfl

@[to_additive]
/-
**MeasureTheory.SimpleFunc.const_mul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：const_mul_eq_map [Mul β] (f : α ->ₛ β) (b : β) : const α b * f = f.map fun
 a => b * a
参数：f : α ->ₛ β；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_mul_eq_map [Mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map fun a => b * a :=
  rfl

@[to_additive]
/-
**MeasureTheory.SimpleFunc.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：map_mul [Mul β] [Mul γ] {g : β -> γ} (hg : forall x y, g (x * y) = g x * g
 y) (f₁ f₂ : α ->ₛ β) : (f₁ * f₂).map g = f₁.map g * f₂.map g
参数：hg : forall x y, g (x * y) = g x * g y；f₁ f₂ : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
-/
theorem map_mul [Mul β] [Mul γ] {g : β → γ} (hg : ∀ x y, g (x * y) = g x * g y) (f₁ f₂ : α →ₛ β) :
    (f₁ * f₂).map g = f₁.map g * f₂.map g :=
  ext fun _ => hg _ _

variable {K : Type*}

@[to_additive]
/-
**MeasureTheory.SimpleFunc.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：instSMul [SMul K β] : SMul K (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [SMul K β] : SMul K (α →ₛ β) :=
  ⟨fun k f => f.map (k • ·)⟩

@[to_additive (attr := simp)]
/-
**MeasureTheory.SimpleFunc.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：coe_smul [SMul K β] (c : K) (f : α ->ₛ β) : ⇑(c • f) = c • ⇑f
参数：c : K；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [SMul K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.SimpleFunc.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：smul_apply [SMul K β] (k : K) (f : α ->ₛ β) (a : α) : (k • f) a = k • f a
参数：k : K；f : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
  rfl
/-
**MeasureTheory.SimpleFunc.hasNatSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：hasNatSMul [AddMonoid β] : SMul Nat (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatSMul [AddMonoid β] : SMul ℕ (α →ₛ β) := inferInstance

@[to_additive existing hasNatSMul]
/-
**MeasureTheory.SimpleFunc.hasNatPow** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：hasNatPow [Monoid β] : Pow (α ->ₛ β) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatPow [Monoid β] : Pow (α →ₛ β) ℕ :=
  ⟨fun f n => f.map (· ^ n)⟩

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：coe_pow [Monoid β] (f : α ->ₛ β) (n : Nat) : ⇑(f ^ n) = (⇑f) ^ n
参数：f : α ->ₛ β；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow [Monoid β] (f : α →ₛ β) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl
/-
**MeasureTheory.SimpleFunc.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：pow_apply [Monoid β] (n : Nat) (f : α ->ₛ β) (a : α) : (f ^ n) a = f a ^ n
参数：n : Nat；f : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply [Monoid β] (n : ℕ) (f : α →ₛ β) (a : α) : (f ^ n) a = f a ^ n :=
  rfl
/-
**MeasureTheory.SimpleFunc.hasIntPow** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：hasIntPow [DivInvMonoid β] : Pow (α ->ₛ β) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasIntPow [DivInvMonoid β] : Pow (α →ₛ β) ℤ :=
  ⟨fun f n => f.map (· ^ n)⟩

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：coe_zpow [DivInvMonoid β] (f : α ->ₛ β) (z : Int) : ⇑(f ^ z) = (⇑f) ^ z
参数：f : α ->ₛ β；z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow [DivInvMonoid β] (f : α →ₛ β) (z : ℤ) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl
/-
**MeasureTheory.SimpleFunc.zpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：zpow_apply [DivInvMonoid β] (z : Int) (f : α ->ₛ β) (a : α) : (f ^ z) a = 
f a ^ z
参数：z : Int；f : α ->ₛ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zpow_apply [DivInvMonoid β] (z : ℤ) (f : α →ₛ β) (a : α) : (f ^ z) a = f a ^ z :=
  rfl

-- TODO: work out how to generate these instances with `to_additive`, which gets confused by the
-- argument order swap between `coe_smul` and `coe_pow`.
section Additive

/-
**MeasureTheory.SimpleFunc.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：instAddMonoid [AddMonoid β] : AddMonoid (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid [AddMonoid β] : AddMonoid (α →ₛ β) :=
  fast_instance% Function.Injective.addMonoid (fun f => show α → β from f) coe_injective coe_zero
    coe_add fun _ _ => coe_smul _ _
/-
**MeasureTheory.SimpleFunc.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：instAddCommMonoid [AddCommMonoid β] : AddCommMonoid (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid β] : AddCommMonoid (α →ₛ β) :=
  fast_instance% Function.Injective.addCommMonoid (fun f => show α → β from f)
    coe_injective coe_zero coe_add fun _ _ => coe_smul _ _
/-
**MeasureTheory.SimpleFunc.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：instAddGroup [AddGroup β] : AddGroup (α ->ₛ β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.coe_injective`：coe_injective ⦃f g : α ->ₛ β⦄ (H
 : (f : α -> β) = g) : f = g
-/
instance instAddGroup [AddGroup β] : AddGroup (α →ₛ β) :=
  Function.Injective.addGroup (fun f => show α → β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _
/-
**MeasureTheory.SimpleFunc.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：instAddCommGroup [AddCommGroup β] : AddCommGroup (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup β] : AddCommGroup (α →ₛ β) :=
  fast_instance% Function.Injective.addCommGroup (fun f => show α → β from f) coe_injective
    coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

end Additive

@[to_additive existing]
/-
**MeasureTheory.SimpleFunc.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：instMonoid [Monoid β] : Monoid (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Monoid β] : Monoid (α →ₛ β) :=
  fast_instance% Function.Injective.monoid (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]
/-
**MeasureTheory.SimpleFunc.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：instCommMonoid [CommMonoid β] : CommMonoid (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid β] : CommMonoid (α →ₛ β) :=
  fast_instance% Function.Injective.commMonoid (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]
/-
**MeasureTheory.SimpleFunc.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：instGroup [Group β] : Group (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroup [Group β] : Group (α →ₛ β) :=
  fast_instance% Function.Injective.group (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive existing]
/-
**MeasureTheory.SimpleFunc.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：instCommGroup [CommGroup β] : CommGroup (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup [CommGroup β] : CommGroup (α →ₛ β) :=
  fast_instance% Function.Injective.commGroup (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid K] [MulAction K β] : MulAction K (α →ₛ β) :=
  fast_instance% Function.Injective.mulAction (fun f => show α → β from f) coe_injective coe_smul
/-
**MeasureTheory.SimpleFunc.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：instModule [Semiring K] [AddCommMonoid β] [Module K β] : Module K (α ->ₛ β
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring K] [AddCommMonoid β] [Module K β] : Module K (α →ₛ β) :=
  fast_instance% Function.Injective.module K ⟨⟨fun f => show α → β from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul
/-
**MeasureTheory.SimpleFunc.smul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：smul_eq_map [SMul K β] (k : K) (f : α ->ₛ β) : k • f = f.map (k • ·)
参数：k : K；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eq_map [SMul K β] (k : K) (f : α →ₛ β) : k • f = f.map (k • ·) :=
  rfl
/-
**MeasureTheory.SimpleFunc.smul_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：smul_const [SMul K β] (k : K) (b : β) : (k • const α b : α ->ₛ β) = const 
α (k • b)
参数：k : K；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
-/
lemma smul_const [SMul K β] (k : K) (b : β) :
    (k • const α b : α →ₛ β) = const α (k • b) := ext fun _ ↦ rfl
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalNonAssocSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring β] : NonUnitalSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalSemiring (fun f => show α → β from f)
    SimpleFunc.coe_injective coe_zero coe_add coe_mul coe_smul
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NatCast β] : NatCast (α →ₛ β) where
  natCast n := const _ (NatCast.natCast n)

@[simp, norm_cast]
/-
**MeasureTheory.SimpleFunc.coe_natCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：coe_natCast [NatCast β] (n : Nat) : ⇑(↑n : α ->ₛ β) = fun _ => ↑n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_natCast [NatCast β] (n : ℕ) :
    ⇑(↑n : α →ₛ β) = fun _ ↦ ↑n := rfl
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring β] : NonAssocSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonAssocSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_natCast
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IntCast β] : IntCast (α →ₛ β) where
  intCast n := const _ (IntCast.intCast n)

@[simp, norm_cast]
/-
**MeasureTheory.SimpleFunc.coe_intCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：coe_intCast [IntCast β] (n : Int) : ⇑(↑n : α ->ₛ β) = fun _ => ↑n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_intCast [IntCast β] (n : ℤ) :
    ⇑(↑n : α →ₛ β) = fun _ ↦ ↑n := rfl
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing β] : NonAssocRing (α →ₛ β) :=
  fast_instance% Function.Injective.nonAssocRing (fun f => show α → β from f) coe_injective
    coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalCommSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring β] : CommSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.commSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_pow coe_natCast
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing β] : NonUnitalCommRing (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalCommRing (fun f => show α → β from f)
    coe_injective coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing β] : CommRing (α →ₛ β) :=
  fast_instance% Function.Injective.commRing (fun f => show α → β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring β] : Semiring (α →ₛ β) :=
  fast_instance% Function.Injective.semiring (fun f => show α → β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_smul coe_pow coe_natCast
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing β] : NonUnitalRing (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalRing (fun f => show α → β from f) coe_injective
    coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring β] : Ring (α →ₛ β) :=
  fast_instance% Function.Injective.ring (fun f => show α → β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul K γ] [SMul γ β] [SMul K β] [IsScalarTower K γ β] : IsScalarTower K γ (α →ₛ β) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul γ β] [SMul K β] [SMulCommClass K γ β] : SMulCommClass K γ (α →ₛ β) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring K] [Semiring β] [Algebra K β] : Algebra K (α →ₛ β) where
  algebraMap := {
    toFun r := const α <| algebraMap K β r
    map_one' := ext fun _ ↦ algebraMap K β |>.map_one ▸ rfl
    map_mul' _ _ := ext fun _ ↦ algebraMap K β |>.map_mul ..
    map_zero' := ext fun _ ↦ algebraMap K β |>.map_zero ▸ rfl
    map_add' _ _ := ext fun _ ↦ algebraMap K β |>.map_add .. }
  commutes' _ _ := ext fun _ ↦ Algebra.commutes ..
  smul_def' _ _ := ext fun _ ↦ Algebra.smul_def ..

@[simp]
/-
**MeasureTheory.SimpleFunc.const_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：const_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) : con
st α (algebraMap K β k) = algebraMap K (α ->ₛ β) k
参数：k : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) :
    const α (algebraMap K β k) = algebraMap K (α →ₛ β) k := rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：coe_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) (x : α)
 : ⇑(algebraMap K (α ->ₛ β)) k x = algebraMap K (α -> β) k x
参数：k : K；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) (x : α) :
    ⇑(algebraMap K (α →ₛ β)) k x = algebraMap K (α → β) k x := rfl

section Star

/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star β] : Star (α →ₛ β) where
  star f := f.map Star.star

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_star** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：coe_star [Star β] {f : α ->ₛ β} : ⇑(star f) = star ⇑f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_star [Star β] {f : α →ₛ β} : ⇑(star f) = star ⇑f := rfl
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar β] : InvolutiveStar (α →ₛ β) where
  star_involutive _ := ext fun _ ↦ star_star _
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid β] [StarAddMonoid β] : StarAddMonoid (α →ₛ β) where
  star_add _ _ := ext fun _ ↦ star_add ..
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul β] [StarMul β] : StarMul (α →ₛ β) where
  star_mul _ _ := ext fun _ ↦ star_mul ..
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring β] [StarRing β] : StarRing (α →ₛ β) where
  star_add _ _ := ext fun _ ↦ star_add ..

end Star

section Preorder
variable [Preorder β] {s : Set α} {f f₁ f₂ g g₁ g₂ : α →ₛ β} {hs : MeasurableSet s}

/-
**MeasureTheory.SimpleFunc.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：instPreorder : Preorder (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder : Preorder (α →ₛ β) := Preorder.lift (⇑)
/-
**MeasureTheory.SimpleFunc.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Preor
der β] {f g : MeasureTheory.SimpleFunc α β},   ⇑f ≤ ⇑g ↔ f ≤ g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast, gcongr] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := .rfl
/-
**MeasureTheory.SimpleFunc.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Preor
der β] {f g : MeasureTheory.SimpleFunc α β},   ⇑f < ⇑g ↔ f < g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast, gcongr] lemma coe_lt_coe : ⇑f < g ↔ f < g := .rfl

@[simp, gcongr]
/-
**MeasureTheory.SimpleFunc.mk_le_mk** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：mk_le_mk {f g : α -> β} {hf hg hf' hg'} : mk f hf hf' <= mk g hg hg' ↔ f <
= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_le_mk {f g : α → β} {hf hg hf' hg'} : mk f hf hf' ≤ mk g hg hg' ↔ f ≤ g := Iff.rfl

@[simp, gcongr]
/-
**MeasureTheory.SimpleFunc.mk_lt_mk** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：mk_lt_mk {f g : α -> β} {hf hg hf' hg'} : mk f hf hf' < mk g hg hg' ↔ f < 
g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_lt_mk {f g : α → β} {hf hg hf' hg'} : mk f hf hf' < mk g hg hg' ↔ f < g := Iff.rfl

@[gcongr only]
/-
**MeasureTheory.SimpleFunc.piecewise_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：piecewise_mono (hf : forall a in s, f₁ a <= f₂ a) (hg : forall a ∉ s, g₁ a
 <= g₂ a) : piecewise s hs f₁ g₁ <= piecewise s hs f₂ g₂
参数：hf : forall a in s, f₁ a <= f₂ a；hg : forall a ∉ s, g₁ a <= g₂ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_mono`：piecewise_mono {δ : α -> Type*} [forall i, Preorder 
(δ i)] {s : Set α} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, δ i} 
(h₁ : fo…
-/
lemma piecewise_mono (hf : ∀ a ∈ s, f₁ a ≤ f₂ a) (hg : ∀ a ∉ s, g₁ a ≤ g₂ a) :
    piecewise s hs f₁ g₁ ≤ piecewise s hs f₂ g₂ := by
  classical
  exact Set.piecewise_mono hf hg

end Preorder

/-
**MeasureTheory.SimpleFunc.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：instPartialOrder [PartialOrder β] : PartialOrder (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder [PartialOrder β] : PartialOrder (α →ₛ β) :=
  { SimpleFunc.instPreorder with
    le_antisymm := fun _f _g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }
/-
**MeasureTheory.SimpleFunc.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：instOrderBot [LE β] [OrderBot β] : OrderBot (α ->ₛ β) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot [LE β] [OrderBot β] : OrderBot (α →ₛ β) where
  bot := const α ⊥
  bot_le _ _ := bot_le
/-
**MeasureTheory.SimpleFunc.instOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：instOrderTop [LE β] [OrderTop β] : OrderTop (α ->ₛ β) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderTop [LE β] [OrderTop β] : OrderTop (α →ₛ β) where
  top := const α ⊤
  le_top _ _ := le_top

@[to_additive]
/-
**MeasureTheory.SimpleFunc.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.SimpleFunc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (α →ₛ β) where
  mul_le_mul_left _ _ h _ _ := mul_le_mul_left (h _) _
/-
**MeasureTheory.SimpleFunc.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _f _g _h hfh hgh a => le_inf (hfh a) (hgh a) }
/-
**MeasureTheory.SimpleFunc.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _f _g _h hfh hgh a => sup_le (hfh a) (hgh a) }
/-
**MeasureTheory.SimpleFunc.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：instLattice [Lattice β] : Lattice (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice [Lattice β] : Lattice (α →ₛ β) :=
  { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }
/-
**MeasureTheory.SimpleFunc.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (α ->ₛ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (α →ₛ β) :=
  { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }
/-
**MeasureTheory.SimpleFunc.finset_sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：finset_sup_apply [SemilatticeSup β] [OrderBot β] {f : γ -> α ->ₛ β} (s : F
inset γ) (a : α) : s.sup f a = s.sup fun c => f c a
参数：s : Finset γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `MeasureTheory.SimpleFunc.sup_apply`：sup_apply [Max β] (f g : α ->ₛ β) (a
 : α) : (f ⊔ g) a = f a ⊔ g a
-/
theorem finset_sup_apply [SemilatticeSup β] [OrderBot β] {f : γ → α →ₛ β} (s : Finset γ) (a : α) :
    s.sup f a = s.sup fun c => f c a := by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s _ ih
  rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]

section Restrict

variable [Zero β]

open scoped Classical in
/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
/-
**MeasureTheory.SimpleFunc.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：restrict (f : α ->ₛ β) (s : Set α) : α ->ₛ β
参数：f : α ->ₛ β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = cons
t α 0`.
-/
def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0
/-
**MeasureTheory.SimpleFunc.restrict_of_not_measurable** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SimpleFunc`。
形式化陈述：restrict_of_not_measurable {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet 
s) : restrict f s = 0
参数：hs : ¬MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem restrict_of_not_measurable {f : α →ₛ β} {s : Set α} (hs : ¬MeasurableSet s) :
    restrict f s = 0 :=
  dif_neg hs

@[simp]
/-
**MeasureTheory.SimpleFunc.coe_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：coe_restrict (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) : ⇑(restrict
 f s) = indicator s f
参数：f : α ->ₛ β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.restrict.eq_1`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : Zero β] (f : MeasureTheory.SimpleFunc α β) 
  (s : Set α), f.restrict s …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.SimpleFunc.coe_piecewise`：coe_piecewise {s : Set α} (hs : 
MeasurableSet s) (f g : α ->ₛ β) : ⇑(piecewise s hs f g) = s.piecewise f g
· 使用定理 `MeasureTheory.SimpleFunc.coe_zero`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : Zero β], ⇑0 = 0
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
-/
theorem coe_restrict (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) :
    ⇑(restrict f s) = indicator s f := by
  classical
  rw [restrict, dif_pos hs, coe_piecewise, coe_zero, piecewise_eq_indicator]

@[simp]
/-
**MeasureTheory.SimpleFunc.restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：restrict_univ (f : α ->ₛ β) : restrict f univ = f
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_univ`：piecewise_univ (f g : α ->ₛ β) 
: piecewise univ MeasurableSet.univ f g = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_univ (f : α →ₛ β) : restrict f univ = f := by simp [restrict]

@[simp]
/-
**MeasureTheory.SimpleFunc.restrict_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：restrict_empty (f : α ->ₛ β) : restrict f ∅ = 0
参数：f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_empty`：piecewise_empty (f g : α ->ₛ β
) : piecewise ∅ MeasurableSet.empty f g = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 := by simp [restrict]
/-
**MeasureTheory.SimpleFunc.map_restrict_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：map_restrict_of_zero [Zero γ] {g : β -> γ} (hg : g 0 = 0) (f : α ->ₛ β) (s
 : Set α) : (f.restrict s).map g = (f.map g).restrict s
参数：hg : g 0 = 0；f : α ->ₛ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.indicator_comp_of_zero`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_
4} [inst : Zero M] [inst_1 : Zero N] {s : Set α} {f : α → M} {g : M → N},   g 0 
= 0 → s.indicato…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.restrict_of_not_measurable`：restrict_of_not_mea
surable {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet s) : restrict f s = 0
-/
theorem map_restrict_of_zero [Zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : Set α) :
    (f.restrict s).map g = (f.map g).restrict s := by
  classical
  exact ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
    else by simp [restrict_of_not_measurable hs, hg]
/-
**MeasureTheory.SimpleFunc.map_coe_ennreal_restrict** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SimpleFunc`。
形式化陈述：map_coe_ennreal_restrict (f : α ->ₛ Real>=0) (s : Set α) : (f.restrict s).
map ((↑) : Real>=0 -> Real>=0∞) = (f.map (↑)).restrict s
参数：f : α ->ₛ Real>=0；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.map_restrict_of_zero`：map_restrict_of_zero [Zer
o γ] {g : β -> γ} (hg : g 0 = 0) (f : α ->ₛ β) (s : Set α) : (f.restrict s).map 
g = (f.map g).restrict s
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
-/
theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map ((↑) : ℝ≥0 → ℝ≥0∞) = (f.map (↑)).restrict s :=
  map_restrict_of_zero ENNReal.coe_zero _ _
/-
**MeasureTheory.SimpleFunc.map_coe_nnreal_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：map_coe_nnreal_restrict (f : α ->ₛ Real>=0) (s : Set α) : (f.restrict s).m
ap ((↑) : Real>=0 -> Real) = (f.map (↑)).restrict s
参数：f : α ->ₛ Real>=0；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.map_restrict_of_zero`：map_restrict_of_zero [Zer
o γ] {g : β -> γ} (hg : g 0 = 0) (f : α ->ₛ β) (s : Set α) : (f.restrict s).map 
g = (f.map g).restrict s
· 使用定理 `NNReal.coe_zero`：↑0 = 0
-/
theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map ((↑) : ℝ≥0 → ℝ) = (f.map (↑)).restrict s :=
  map_restrict_of_zero NNReal.coe_zero _ _
/-
**MeasureTheory.SimpleFunc.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：restrict_apply (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) (a) : rest
rict f s a = indicator s f a
参数：f : α ->ₛ β；hs : MeasurableSet s；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_apply (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) (a) :
    restrict f s a = indicator s f a := by simp only [f.coe_restrict hs]
/-
**MeasureTheory.SimpleFunc.restrict_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：restrict_preimage (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Se
t β} (ht : (0 : β) ∉ t) : restrict f s ⁻¹' t = s inter f ⁻¹' t
参数：f : α ->ₛ β；hs : MeasurableSet s；ht : (0 : β) ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `Set.indicator_preimage_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst 
: Zero M] (s : Set α) (f : α → M) {t : Set M},   0 ∉ t → s.indicator f ⁻¹' t = f
 ⁻¹' t ∩ s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_preimage (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
    (ht : (0 : β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t := by
  simp [hs, indicator_preimage_of_notMem _ _ ht, inter_comm]
/-
**MeasureTheory.SimpleFunc.restrict_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SimpleFunc`。
形式化陈述：restrict_preimage_singleton (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet 
s) {r : β} (hr : r != 0) : restrict f s ⁻¹' {r} = s inter f ⁻¹' {r}
参数：f : α ->ₛ β；hs : MeasurableSet s；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.restrict_preimage`：restrict_preimage (f : α ->ₛ
 β) {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : (0 : β) ∉ t) : restrict
 f s ⁻¹' t = s inter f ⁻¹' t
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem restrict_preimage_singleton (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
    (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
  f.restrict_preimage hs hr.symm
/-
**MeasureTheory.SimpleFunc.mem_restrict_range** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：mem_restrict_range {r : β} {s : Set α} {f : α ->ₛ β} (hs : MeasurableSet s
) : r in (restrict f s).range ↔ r = 0 ∧ s != univ ∨ r in f '' s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `MeasureTheory.SimpleFunc.coe_range`：coe_range (f : α ->ₛ β) : (↑f.range 
: Set β) = Set.range f
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `Set.mem_range_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {r : M} {s : Set α} {f : α → M},   r ∈ Set.range (s.indicator f) ↔ r = 0 ∧ s ≠ 
Set.univ ∨ r …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_restrict_range {r : β} {s : Set α} {f : α →ₛ β} (hs : MeasurableSet s) :
    r ∈ (restrict f s).range ↔ r = 0 ∧ s ≠ univ ∨ r ∈ f '' s := by
  rw [← Finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]
/-
**MeasureTheory.SimpleFunc.mem_image_of_mem_range_restrict** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α ->ₛ β} (hr : r 
in (restrict f s).range) (h0 : r != 0) : r in f '' s
参数：hr : r in (restrict f s).range；h0 : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.mem_restrict_range`：mem_restrict_range {r : β} 
{s : Set α} {f : α ->ₛ β} (hs : MeasurableSet s) : r in (restrict f s).range ↔ r
 = 0 ∧ s != univ ∨ r in f '' s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `MeasureTheory.SimpleFunc.eq_zero_of_mem_range_zero`：eq_zero_of_mem_range
_zero [Zero β] : forall {y : β}, y in (0 : α ->ₛ β).range -> y = 0
· 使用定理 `MeasureTheory.SimpleFunc.restrict_of_not_measurable`：restrict_of_not_mea
surable {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet s) : restrict f s = 0
-/
theorem mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α →ₛ β}
    (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) : r ∈ f '' s := by
  classical
  exact if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0, -mem_range] using hr
  else by
    rw [restrict_of_not_measurable hs] at hr
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim

@[gcongr, mono]
/-
**MeasureTheory.SimpleFunc.restrict_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：restrict_mono [Preorder β] (s : Set α) {f g : α ->ₛ β} (H : f <= g) : f.re
strict s <= g.restrict s
参数：s : Set α；H : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.indicator_le_indicator`：∀ {α : Type u_2} {M : Type u_3} [inst : Preo
rder M] [inst_1 : Zero M] {s : Set α} {f g : α → M} {a : α},   f a ≤ g a → s.ind
icator f a ≤ s.i…
· 使用定理 `MeasureTheory.SimpleFunc.restrict_of_not_measurable`：restrict_of_not_mea
surable {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet s) : restrict f s = 0
-/
theorem restrict_mono [Preorder β] (s : Set α) {f g : α →ₛ β} (H : f ≤ g) :
    f.restrict s ≤ g.restrict s := by
  classical
  exact if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else by simp only [restrict_of_not_measurable hs, le_refl]

end Restrict

section Approx

section

variable [SemilatticeSup β] [OrderBot β] [Zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `iSup_approx_apply` for details. -/
/-
**MeasureTheory.SimpleFunc.approx** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simpl
eFunc`。
形式化陈述：approx (i : Nat -> β) (f : α -> β) (n : Nat) : α ->ₛ β
参数：i : Nat -> β；f : α -> β；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to t
he supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `iSup_approx_appl
y` for details.
-/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k ≤ f a }

open scoped Classical in
/-
**MeasureTheory.SimpleFunc.approx_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace
 β] [OpensMeasurableSpace β] {i : Nat -> β} {f : α -> β} {n : Nat} (a : α) (hf :
 Measurable f) : (approx i f n : α ->ₛ β) a = (Finset.range n).sup fun k => if i
 k <= f a then i k else 0
参数：a : α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.finset_sup_apply`：finset_sup_apply [Semilattice
Sup β] [OrderBot β] {f : γ -> α ->ₛ β} (s : Finset γ) (a : α) : s.sup f a = s.su
p fun c => f c a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.restrict_apply`：restrict_apply (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) (a) : restrict f s a = indicator s f a
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : Measurable f) :
    (approx i f n : α →ₛ β) a = (Finset.range n).sup fun k => if i k ≤ f a then i k else 0 := by
  dsimp only [approx]
  rw [finset_sup_apply]
  congr
  funext k
  rw [restrict_apply]
  · simp only [coe_const, mem_ofPred_eq, indicator_apply, Function.const_apply]
  · exact hf measurableSet_Ici
/-
**MeasureTheory.SimpleFunc.monotone_approx** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：monotone_approx (i : Nat -> β) (f : α -> β) : Monotone (approx i f)
参数：i : Nat -> β；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.range_subset_range`：range_subset_range {n m} : range n subseteq r
ange m ↔ n <= m
-/
theorem monotone_approx (i : ℕ → β) (f : α → β) : Monotone (approx i f) := fun _ _ h =>
  Finset.sup_mono <| Finset.range_subset_range.2 h
/-
**MeasureTheory.SimpleFunc.approx_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace 
β] [OpensMeasurableSpace β] [MeasurableSpace γ] {i : Nat -> β} {f : γ -> β} {g :
 α -> γ} {n : Nat} (a : α) (hf : Measurable f) (hg : Measurable g) : (approx i (
f ∘ g) n : α ->ₛ β) a = (approx i f n : γ ->ₛ β) (g a)
参数：a : α；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.approx_apply`：approx_apply [TopologicalSpace β]
 [OrderClosedTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] {i : Nat -
> β} {f : α -> β} {n : Nat}…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] [MeasurableSpace γ] {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
    (hf : Measurable f) (hg : Measurable g) :
    (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) := by
  rw [approx_apply _ hf, approx_apply _ (hf.comp hg), Function.comp_apply]

end

/-
**MeasureTheory.SimpleFunc.iSup_approx_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：iSup_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTop
ology β] [Zero β] [MeasurableSpace β] [OpensMeasurableSpace β] (i : Nat -> β) (f
 : α -> β) (a : α) (hf : Measurable f) (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f
 n : α ->ₛ β) a = ⨆ (k) (_ : i k <= f a), i k
参数：i : Nat -> β；f : α -> β；a : α；hf : Measurable f；h_zero : (0 : β) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.approx_apply`：approx_apply [TopologicalSpace β]
 [OrderClosedTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] {i : Nat -
> β} {f : α -> β} {n : Nat}…
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem iSup_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f n : α →ₛ β) a = ⨆ (k) (_ : i k ≤ f a), i k := by
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
  · rw [approx_apply a hf, h_zero]
    refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · exact le_iSup_of_le k (le_iSup (fun _ : i k ≤ f a => i k) h)
    · exact bot_le
  · refine le_iSup_of_le (k + 1) ?_
    rw [approx_apply a hf]
    have : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
    refine le_trans (le_of_eq ?_) (Finset.le_sup this)
    rw [if_pos hk]

end Approx

section EApprox
variable {f : α → ℝ≥0∞}

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
/-
**MeasureTheory.SimpleFunc.ennrealRatEmbed** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：ennrealRatEmbed (n : Nat) : Real>=0∞
参数：n : Nat。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational nu
mbers.
-/
def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))
/-
**MeasureTheory.SimpleFunc.ennrealRatEmbed_encode** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：ennrealRatEmbed_encode (q : Rat) : ennrealRatEmbed (Encodable.encode q) = 
Real.toNNReal q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.ennrealRatEmbed.eq_1`：∀ (n : ℕ), MeasureTheory.
SimpleFunc.ennrealRatEmbed n = ENNReal.ofReal ↑((Encodable.decode n).getD 0)
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
-/
theorem ennrealRatEmbed_encode (q : ℚ) :
    ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [ennrealRatEmbed, Encodable.encodek]; rfl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
/-
**MeasureTheory.SimpleFunc.eapprox** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Simp
leFunc`。
形式化陈述：eapprox : (α -> Real>=0∞) -> Nat -> α ->ₛ Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Approximate a function `α → ℝ≥0∞` by a sequence of simple functions.
-/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
  approx ennrealRatEmbed
/-
**MeasureTheory.SimpleFunc.eapprox_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：eapprox_lt_top (f : α -> Real>=0∞) (n : Nat) (a : α) : eapprox f n a < ∞
参数：f : α -> Real>=0∞；n : Nat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.finset_sup_apply`：finset_sup_apply [Semilattice
Sup β] [OrderBot β] {f : γ -> α ->ₛ β} (s : Finset γ) (a : α) : s.sup f a = s.su
p fun c => f c a
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `bot_lt_top`：bot_lt_top : (⊥ : α) < ⊤
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Set.indicator_le_self`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoid
 M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] (s : Set α)   (f : α → M
), s.indica…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `WithTop.top_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α], 0 < ⊤
-/
theorem eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ := by
  simp only [eapprox, approx, finset_sup_apply, restrict]
  rw [Finset.sup_lt_iff (α := ℝ≥0∞) bot_lt_top]
  intro b _
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { a : α | ennrealRatEmbed b ≤ f a }.indicator (fun _ => ennrealRatEmbed b) a ≤
          ennrealRatEmbed b :=
        indicator_le_self _ _ a
      _ < ⊤ := ENNReal.coe_lt_top
  · exact WithTop.top_pos

@[gcongr, mono]
/-
**MeasureTheory.SimpleFunc.monotone_eapprox** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：monotone_eapprox (f : α -> Real>=0∞) : Monotone (eapprox f)
参数：f : α -> Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.monotone_approx`：monotone_approx (i : Nat -> β)
 (f : α -> β) : Monotone (approx i f)
-/
theorem monotone_eapprox (f : α → ℝ≥0∞) : Monotone (eapprox f) :=
  monotone_approx _ f
/-
**MeasureTheory.SimpleFunc.iSup_eapprox_apply** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：iSup_eapprox_apply (hf : Measurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ
 Real>=0∞) a = f a
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.eapprox.eq_1`：∀ {α : Type u_1} [inst : Measurab
leSpace α],   MeasureTheory.SimpleFunc.eapprox = MeasureTheory.SimpleFunc.approx
 MeasureTheory.SimpleFunc.e…
· 使用定理 `MeasureTheory.SimpleFunc.iSup_approx_apply`：iSup_approx_apply [Topologic
alSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β] [MeasurableSpace
 β] [OpensMeasurableSpace β] (i …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_rat_btwn`：lt_iff_exists_rat_btwn : a < b ↔ exists 
q : Rat, 0 <= q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : Real>=0∞) < b
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `MeasureTheory.SimpleFunc.ennrealRatEmbed_encode`：ennrealRatEmbed_encode 
(q : Rat) : ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
lemma iSup_eapprox_apply (hf : Measurable f) (a : α) : ⨆ n, (eapprox f n : α →ₛ ℝ≥0∞) a = f a := by
  rw [eapprox, iSup_approx_apply ennrealRatEmbed f a hf rfl]
  refine le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt ?_)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : ℝ≥0∞) ≤ ⨆ (k : ℕ) (_ : ennrealRatEmbed k ≤ f a), ennrealRatEmbed k := by
    refine le_iSup_of_le (Encodable.encode q) ?_
    rw [ennrealRatEmbed_encode q]
    exact le_iSup_of_le (le_of_lt q_lt) le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
/-
**MeasureTheory.SimpleFunc.iSup_coe_eapprox** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：iSup_coe_eapprox (hf : Measurable f) : ⨆ n, ⇑(eapprox f n) = f
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
-/
lemma iSup_coe_eapprox (hf : Measurable f) : ⨆ n, ⇑(eapprox f n) = f := by
  simpa [funext_iff] using iSup_eapprox_apply hf
/-
**MeasureTheory.SimpleFunc.eapprox_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：eapprox_comp [MeasurableSpace γ] {f : γ -> Real>=0∞} {g : α -> γ} {n : Nat
} (hf : Measurable f) (hg : Measurable g) : (eapprox (f ∘ g) n : α -> Real>=0∞) 
= (eapprox f n : γ ->ₛ Real>=0∞) ∘ g
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.approx_comp`：approx_comp [TopologicalSpace β] [
OrderClosedTopology β] [MeasurableSpace β] [OpensMeasurableSpace β] [MeasurableS
pace γ] {i : Nat -> β} {f …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem eapprox_comp [MeasurableSpace γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ} (hf : Measurable f)
    (hg : Measurable g) : (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
  funext fun a => approx_comp a hf hg
/-
**MeasureTheory.SimpleFunc.tendsto_eapprox** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：tendsto_eapprox {f : α -> Real>=0∞} (hf_meas : Measurable f) (a : α) : Ten
dsto (fun n => eapprox f n a) atTop (𝓝 (f a))
参数：hf_meas : Measurable f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.SimpleFunc.iSup_coe_eapprox`：iSup_coe_eapprox (hf : Measur
able f) : ⨆ n, ⇑(eapprox f n) = f
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
-/
lemma tendsto_eapprox {f : α → ℝ≥0∞} (hf_meas : Measurable f) (a : α) :
    Tendsto (fun n ↦ eapprox f n a) atTop (𝓝 (f a)) := by
  nth_rw 2 [← iSup_coe_eapprox hf_meas]
  rw [iSup_apply]
  exact tendsto_atTop_iSup fun _ _ hnm ↦ monotone_eapprox f hnm a

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
/-
**MeasureTheory.SimpleFunc.eapproxDiff** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → (α → ENNReal) → ℕ → MeasureT
heory.SimpleFunc α NNReal
参数：α → ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their v
alues
in `ℝ≥0`.
-/
def eapproxDiff (f : α → ℝ≥0∞) : ℕ → α →ₛ ℝ≥0
  | 0 => (eapprox f 0).map ENNReal.toNNReal
  | n + 1 => (eapprox f (n + 1) - eapprox f n).map ENNReal.toNNReal
/-
**MeasureTheory.SimpleFunc.sum_eapproxDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：sum_eapproxDiff (f : α -> Real>=0∞) (n : Nat) (a : α) : (∑ k in Finset.ran
ge (n + 1), (eapproxDiff f k a : Real>=0∞)) = eapprox f n a
参数：f : α -> Real>=0∞；n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.SimpleFunc.eapprox_lt_top`：eapprox_lt_top (f : α -> Real>=
0∞) (n : Nat) (a : α) : eapprox f n a < ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `MeasureTheory.SimpleFunc.eapproxDiff.eq_2`：∀ {α : Type u_1} [inst : Meas
urableSpace α] (f : α → ENNReal) (n : ℕ),   MeasureTheory.SimpleFunc.eapproxDiff
 f n.succ =     MeasureTheory.S…
· 使用定理 `MeasureTheory.SimpleFunc.coe_map`：coe_map (g : β -> γ) (f : α ->ₛ β) : (
f.map g : α -> γ) = g ∘ f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasureTheory.SimpleFunc.coe_sub`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : Sub β] (f g : MeasureTheory.SimpleFunc α β),   ⇑(
f - g) = ⇑f - ⇑g
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem sum_eapproxDiff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
    (∑ k ∈ Finset.range (n + 1), (eapproxDiff f k a : ℝ≥0∞)) = eapprox f n a := by
  induction n with
  | zero =>
    simp [eapproxDiff, (eapprox_lt_top f 0 a).ne]
  | succ n IH =>
    rw [Finset.sum_range_succ, IH, eapproxDiff, coe_map, Function.comp_apply,
      coe_sub, Pi.sub_apply, ENNReal.coe_toNNReal,
      add_tsub_cancel_of_le (monotone_eapprox f (Nat.le_succ _) _)]
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n + 1) a)).ne
    rw [tsub_le_iff_right]
    exact le_self_add
/-
**MeasureTheory.SimpleFunc.tsum_eapproxDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：tsum_eapproxDiff (f : α -> Real>=0∞) (hf : Measurable f) (a : α) : (∑' n, 
(eapproxDiff f n a : Real>=0∞)) = f a
参数：f : α -> Real>=0∞；hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_eq_iSup_nat'`：∀ {f : ℕ → ENNReal} {N : ℕ → ℕ},   Filter.Ten
dsto N Filter.atTop Filter.atTop → ∑' (i : ℕ), f i = ⨆ i, ∑ a ∈ Finset.range (N 
i), f a
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.sum_eapproxDiff`：sum_eapproxDiff (f : α -> Real
>=0∞) (n : Nat) (a : α) : (∑ k in Finset.range (n + 1), (eapproxDiff f k a : Rea
l>=0∞)) = eapprox f n a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tsum_eapproxDiff (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) :
    (∑' n, (eapproxDiff f n a : ℝ≥0∞)) = f a := by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1), sum_eapproxDiff,
    iSup_eapprox_apply hf a]

end EApprox

end Measurable

section Measure

variable {m : MeasurableSpace α} {μ ν : Measure α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
/-
**MeasureTheory.SimpleFunc.lintegral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：lintegral {_m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (μ : Measure α) : 
Real>=0∞
参数：f : α ->ₛ Real>=0∞；μ : Measure α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Integral of a simple function whose codomain is `ℝ≥0∞`.
-/
def lintegral {_m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  ∑ x ∈ f.range, x * μ (f ⁻¹' {x})
/-
**MeasureTheory.SimpleFunc.lintegral_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：lintegral_eq_of_subset (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : fo
rall x, f x != 0 -> μ (f ⁻¹' {f x}) != 0 -> f x in s) : f.lintegral μ = ∑ x in s
, x * μ (f ⁻¹' {x})
参数：f : α ->ₛ Real>=0∞；hs : forall x, f x != 0 -> μ (f ⁻¹' {f x}) != 0 -> f x in 
s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_bij_ne_zero`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [
inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} 
(i : (a : ι)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_singleton_nonempty`：preimage_singleton_nonempty {f : α -> β
} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y in range f
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
-/
theorem lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞}
    (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
    f.lintegral μ = ∑ x ∈ s, x * μ (f ⁻¹' {x}) := by
  refine Finset.sum_bij_ne_zero (fun r _ _ => r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intros
    assumption
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range, ← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
  · intros
    rfl
/-
**MeasureTheory.SimpleFunc.lintegral_eq_of_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：lintegral_eq_of_subset' (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : f
.range \ {0} subseteq s) : f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x})
参数：f : α ->ₛ Real>=0∞；hs : f.range \ {0} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_of_subset`：lintegral_eq_of_subset 
(f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : forall x, f x != 0 -> μ (f ⁻¹' 
{f x}) != 0 -> f x in s) : f.lintegra…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `MeasureTheory.SimpleFunc.mem_range_self`：mem_range_self (f : α ->ₛ β) (x
 : α) : f x in f.range
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞} (hs : f.range \ {0} ⊆ s) :
    f.lintegral μ = ∑ x ∈ s, x * μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hfx _ =>
    hs <| Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`. -/
/-
**MeasureTheory.SimpleFunc.map_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：map_lintegral (g : β -> Real>=0∞) (f : α ->ₛ β) : (f.map g).lintegral μ = 
∑ x in f.range, g x * μ (f ⁻¹' {x})
参数：g : β -> Real>=0∞；f : α ->ₛ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.SimpleFunc.range_map`：range_map [DecidableEq γ] (g : β -> 
γ) (f : α ->ₛ β) : (f.map g).range = f.range.image g
· 使用定理 `Finset.sum_image'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst 
: AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ 
→ ι} (h…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.mem_range`：mem_range {f : α ->ₛ β} {b} : b in f
.range ↔ b in range f
· 使用定理 `MeasureTheory.SimpleFunc.map_preimage_singleton`：map_preimage_singleton 
(f : α ->ₛ β) (g : β -> γ) (c : γ) : f.map g ⁻¹' {c} = f ⁻¹' ↑{b in f.range | g 
b = c}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.sum_measure_preimage_singleton`：∀ {α : Type u_1
} {β : Type u_2} [inst : MeasurableSpace α] (f : MeasureTheory.SimpleFunc α β)  
 {μ : MeasureTheory.Measure α} (s : Finset β)…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)

--- 原说明 ---
Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.
-/
theorem map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
    (f.map g).lintegral μ = ∑ x ∈ f.range, g x * μ (f ⁻¹' {x}) := by
  simp only [lintegral, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · grind
/-
**MeasureTheory.SimpleFunc.add_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：add_lintegral (f g : α ->ₛ Real>=0∞) : (f + g).lintegral μ = f.lintegral μ
 + g.lintegral μ
参数：f g : α ->ₛ Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.add_eq_map₂`：∀ {α : Type u_1} {β : Type u_2} [i
nst : MeasurableSpace α] [inst_1 : Add β] (f g : MeasureTheory.SimpleFunc α β), 
  f + g = MeasureTheory.Si…
· 使用定理 `MeasureTheory.SimpleFunc.map_lintegral`：map_lintegral (g : β -> Real>=0∞
) (f : α ->ₛ β) : (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x})
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
-/
theorem add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
  calc
    (f + g).lintegral μ =
        ∑ x ∈ (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) := by
      rw [add_eq_map₂, map_lintegral]; exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
    _ = (∑ x ∈ (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ x ∈ (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).lintegral μ + ((pair f g).map Prod.snd).lintegral μ := by
      rw [map_lintegral, map_lintegral]
    _ = lintegral f μ + lintegral g μ := rfl
/-
**MeasureTheory.SimpleFunc.const_mul_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：const_mul_lintegral (f : α ->ₛ Real>=0∞) (x : Real>=0∞) : (const α x * f).
lintegral μ = x * f.lintegral μ
参数：f : α ->ₛ Real>=0∞；x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.map_lintegral`：map_lintegral (g : β -> Real>=0∞
) (f : α ->ₛ β) : (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x})
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
    (const α x * f).lintegral μ = x * f.lintegral μ :=
  calc
    (f.map fun a => x * a).lintegral μ = ∑ r ∈ f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = x * ∑ r ∈ f.range, r * μ (f ⁻¹' {r}) := by simp_rw [Finset.mul_sum, mul_assoc]

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
/-
**MeasureTheory.SimpleFunc.lintegral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：lintegral {_m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (μ : Measure α) : 
Real>=0∞
参数：f : α ->ₛ Real>=0∞；μ : Measure α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map.
-/
def lintegralₗ {m : MeasurableSpace α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] Measure α →ₗ[ℝ≥0∞] ℝ≥0∞ where
  toFun f :=
    { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
  map_add' f g := LinearMap.ext fun _ => add_lintegral f g
  map_smul' c f := LinearMap.ext fun _ => const_mul_lintegral f c

@[simp]
/-
**MeasureTheory.SimpleFunc.zero_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：zero_lintegral : (0 : α ->ₛ Real>=0∞).lintegral μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
  LinearMap.ext_iff.1 lintegralₗ.map_zero μ
/-
**MeasureTheory.SimpleFunc.lintegral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：lintegral_add {ν} (f : α ->ₛ Real>=0∞) : f.lintegral (μ + ν) = f.lintegral
 μ + f.lintegral ν
参数：f : α ->ₛ Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
  (lintegralₗ f).map_add μ ν
/-
**MeasureTheory.SimpleFunc.lintegral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：lintegral_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Rea
l>=0∞] (f : α ->ₛ Real>=0∞) (c : R) : f.lintegral (c • μ) = c • f.lintegral μ
参数：f : α ->ₛ Real>=0∞；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem lintegral_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (f : α →ₛ ℝ≥0∞) (c : R) : f.lintegral (c • μ) = c • f.lintegral μ := by
  simpa only [smul_one_smul] using! (lintegralₗ f).map_smul (c • 1) μ

@[simp]
/-
**MeasureTheory.SimpleFunc.lintegral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：lintegral_zero [MeasurableSpace α] (f : α ->ₛ Real>=0∞) : f.lintegral 0 = 
0
参数：f : α ->ₛ Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem lintegral_zero [MeasurableSpace α] (f : α →ₛ ℝ≥0∞) : f.lintegral 0 = 0 :=
  (lintegralₗ f).map_zero
/-
**MeasureTheory.SimpleFunc.lintegral_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：lintegral_finsetSum {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> Measure α) (s : Fin
set ι) : f.lintegral (∑ i in s, μ i) = ∑ i in s, f.lintegral (μ i)
参数：f : α ->ₛ Real>=0∞；μ : ι -> Measure α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem lintegral_finsetSum {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measure α) (s : Finset ι) :
    f.lintegral (∑ i ∈ s, μ i) = ∑ i ∈ s, f.lintegral (μ i) :=
  map_sum (lintegralₗ f) ..

@[deprecated (since := "2026-04-08")] alias lintegral_finset_sum := lintegral_finsetSum
/-
**MeasureTheory.SimpleFunc.lintegral_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：lintegral_sum {m : MeasurableSpace α} {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> M
easure α) : f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i)
参数：f : α ->ₛ Real>=0∞；μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
-/
theorem lintegral_sum {m : MeasurableSpace α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measure α) :
    f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i) := by
  simp only [lintegral, Measure.sum_apply, f.measurableSet_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm
/-
**MeasureTheory.SimpleFunc.restrict_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：restrict_lintegral (f : α ->ₛ Real>=0∞) {s : Set α} (hs : MeasurableSet s)
 : (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} inter s)
参数：f : α ->ₛ Real>=0∞；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_of_subset`：lintegral_eq_of_subset 
(f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : forall x, f x != 0 -> μ (f ⁻¹' 
{f x}) != 0 -> f x in s) : f.lintegra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.restrict_apply`：restrict_apply (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) (a) : restrict f s a = indicator s f a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.coe_restrict`：coe_restrict (f : α ->ₛ β) {s : S
et α} (hs : MeasurableSet s) : ⇑(restrict f s) = indicator s f
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.forall_mem_range`：forall_mem_range {f : α ->ₛ β
} {p : β -> Prop} : (forall y in f.range, p y) ↔ forall x, p (f x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.SimpleFunc.restrict_preimage_singleton`：restrict_preimage_
singleton (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β} (hr : r != 0)
 : restrict f s ⁻¹' {r} = s inter f ⁻¹' {r…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (restrict f s).lintegral μ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ s) := by
  classical
  exact calc
    (restrict f s).lintegral μ = ∑ r ∈ f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x ∈ s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
        else False.elim <| hx <| by simp [*]
    _ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ s) :=
      Finset.sum_congr rfl <|
        forall_mem_range.2 fun b =>
          if hb : f b = 0 then by simp only [hb, zero_mul]
          else by rw [restrict_preimage_singleton _ hs hb, inter_comm]
/-
**MeasureTheory.SimpleFunc.lintegral_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：lintegral_restrict {m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (s : Set α
) (μ : Measure α) : f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y
} inter s)
参数：f : α ->ₛ Real>=0∞；s : Set α；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_restrict {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (s : Set α) (μ : Measure α) :
    f.lintegral (μ.restrict s) = ∑ y ∈ f.range, y * μ (f ⁻¹' {y} ∩ s) := by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]
/-
**MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：restrict_lintegral_eq_lintegral_restrict (f : α ->ₛ Real>=0∞) {s : Set α} 
(hs : MeasurableSet s) : (restrict f s).lintegral μ = f.lintegral (μ.restrict s)
参数：f : α ->ₛ Real>=0∞；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.restrict_lintegral`：restrict_lintegral (f : α -
>ₛ Real>=0∞) {s : Set α} (hs : MeasurableSet s) : (restrict f s).lintegral μ = ∑
 r in f.range, r * μ (f ⁻¹' {r} i…
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_restrict`：lintegral_restrict {m : Mea
surableSpace α} (f : α ->ₛ Real>=0∞) (s : Set α) (μ : Measure α) : f.lintegral (
μ.restrict s) = ∑ y in f.range, y…
-/
theorem restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : Set α}
    (hs : MeasurableSet s) : (restrict f s).lintegral μ = f.lintegral (μ.restrict s) := by
  rw [f.restrict_lintegral hs, lintegral_restrict]
/-
**MeasureTheory.SimpleFunc.lintegral_restrict_iUnion_of_directed** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：lintegral_restrict_iUnion_of_directed {ι : Type*} [Countable ι] (f : α ->ₛ
 Real>=0∞) {s : ι -> Set α} (hd : Directed (· subseteq ·) s) (μ : Measure α) : f
.lintegral (μ.restrict (⋃ i, s i)) = ⨆ i, f.lintegral (μ.restrict (s i))
参数：f : α ->ₛ Real>=0∞；hd : Directed (· subseteq ·) s；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup`：restrict_iUnion_app
ly_eq_iSup [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s) {t : 
Set α} (ht : MeasurableSet t) : μ.restric…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用引理 `ENNReal.finsetSum_iSup`：finsetSum_iSup {α : Type*} {s : Finset α} {f : α
 -> ι -> Real>=0∞} (hf : forall i j, exists k, forall a, f a i <= f a k ∧ f a j 
<= f a k) : …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.measure_mono_left`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α}, μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
-/
theorem lintegral_restrict_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α →ₛ ℝ≥0∞) {s : ι → Set α} (hd : Directed (· ⊆ ·) s) (μ : Measure α) :
    f.lintegral (μ.restrict (⋃ i, s i)) = ⨆ i, f.lintegral (μ.restrict (s i)) := by
  simp only [lintegral, Measure.restrict_iUnion_apply_eq_iSup hd (measurableSet_preimage ..),
    ENNReal.mul_iSup]
  refine finsetSum_iSup fun i j ↦ (hd i j).imp fun k ⟨hik, hjk⟩ ↦ fun a ↦ ?_
  constructor <;> gcongr
/-
**MeasureTheory.SimpleFunc.const_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：const_lintegral (c : Real>=0∞) : (const α c).lintegral μ = c * μ univ
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.lintegral.eq_1`：∀ {α : Type u_1} {_m : Measurab
leSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Measure α
),   f.lintegral μ = ∑ x ∈ f.…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty`：range_eq_empty_of_is
Empty {β} [hα : IsEmpty α] (f : α ->ₛ β) : f.range = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.range_const`：range_const (α) [MeasurableSpace α
] [Nonempty α] (b : β) : (const α b).range = {b}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ := by
  rw [lintegral]
  cases isEmpty_or_nonempty α
  · simp [μ.eq_zero_of_isEmpty]
  · simp only [range_const, coe_const, Finset.sum_singleton]
    unfold Function.const; rw [preimage_const_of_mem (mem_singleton c)]
/-
**MeasureTheory.SimpleFunc.const_lintegral_restrict** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SimpleFunc`。
形式化陈述：const_lintegral_restrict (c : Real>=0∞) (s : Set α) : (const α c).lintegra
l (μ.restrict s) = c * μ s
参数：c : Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.const_lintegral`：const_lintegral (c : Real>=0∞)
 : (const α c).lintegral μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem const_lintegral_restrict (c : ℝ≥0∞) (s : Set α) :
    (const α c).lintegral (μ.restrict s) = c * μ s := by
  rw [const_lintegral, Measure.restrict_apply MeasurableSet.univ, univ_inter]
/-
**MeasureTheory.SimpleFunc.restrict_const_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SimpleFunc`。
形式化陈述：restrict_const_lintegral (c : Real>=0∞) {s : Set α} (hs : MeasurableSet s)
 : ((const α c).restrict s).lintegral μ = c * μ s
参数：c : Real>=0∞；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict`：restr
ict_lintegral_eq_lintegral_restrict (f : α ->ₛ Real>=0∞) {s : Set α} (hs : Measu
rableSet s) : (restrict f s).lintegral μ = f.lintegral …
· 使用定理 `MeasureTheory.SimpleFunc.const_lintegral_restrict`：const_lintegral_restr
ict (c : Real>=0∞) (s : Set α) : (const α c).lintegral (μ.restrict s) = c * μ s
-/
theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ((const α c).restrict s).lintegral μ = c * μ s := by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]
/-
**MeasureTheory.SimpleFunc.lintegral_mono_fun** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：lintegral_mono_fun {f g : α ->ₛ Real>=0∞} (h : f <= g) : f.lintegral μ <= 
g.lintegral μ
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.of_left_le_map_sup`：of_left_le_map_sup [SemilatticeSup α] [Preo
rder β] {f : α -> β} (h : forall x y, f x <= f (x ⊔ y)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_fst_pair`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] (f : MeasureTheory.SimpleFunc α β)   (g
 : MeasureTheory.SimpleFunc…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.SimpleFunc.map_lintegral`：map_lintegral (g : β -> Real>=0∞
) (f : α ->ₛ β) : (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x})
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_mono_fun {f g : α →ₛ ℝ≥0∞} (h : f ≤ g) : f.lintegral μ ≤ g.lintegral μ := by
  refine Monotone.of_left_le_map_sup (f := (lintegral · μ)) (fun f g ↦ ?_) h
  calc
    f.lintegral μ = ((pair f g).map Prod.fst).lintegral μ := by rw [map_fst_pair]
    _ ≤ ((pair f g).map fun p ↦ p.1 ⊔ p.2).lintegral μ := by
      simp only [map_lintegral]
      gcongr
      exact le_sup_left
/-
**MeasureTheory.SimpleFunc.le_sup_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：le_sup_lintegral (f g : α ->ₛ Real>=0∞) : f.lintegral μ ⊔ g.lintegral μ <=
 (f ⊔ g).lintegral μ
参数：f g : α ->ₛ Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono_fun`：lintegral_mono_fun {f g : α
 ->ₛ Real>=0∞} (h : f <= g) : f.lintegral μ <= g.lintegral μ
-/
theorem le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
  Monotone.le_map_sup (fun _ _ ↦ lintegral_mono_fun) f g
/-
**MeasureTheory.SimpleFunc.lintegral_mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：lintegral_mono_measure {f : α ->ₛ Real>=0∞} (h : μ <= ν) : f.lintegral μ <
= f.lintegral ν
参数：h : μ <= ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.measure_mono_left`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α}, μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
-/
theorem lintegral_mono_measure {f : α →ₛ ℝ≥0∞} (h : μ ≤ ν) : f.lintegral μ ≤ f.lintegral ν := by
  simp only [lintegral]
  gcongr

/-- `SimpleFunc.lintegral` is monotone both in function and in measure. -/
@[mono, gcongr]
/-
**MeasureTheory.SimpleFunc.lintegral_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：lintegral_mono {f g : α ->ₛ Real>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.li
ntegral μ <= g.lintegral ν
参数：hfg : f <= g；hμν : μ <= ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono_fun`：lintegral_mono_fun {f g : α
 ->ₛ Real>=0∞} (h : f <= g) : f.lintegral μ <= g.lintegral μ
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono_measure`：lintegral_mono_measure 
{f : α ->ₛ Real>=0∞} (h : μ <= ν) : f.lintegral μ <= f.lintegral ν

--- 原说明 ---
`SimpleFunc.lintegral` is monotone both in function and in measure.
-/
theorem lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) :
    f.lintegral μ ≤ g.lintegral ν :=
  (lintegral_mono_fun hfg).trans (lintegral_mono_measure hμν)

/-- `SimpleFunc.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
/-
**MeasureTheory.SimpleFunc.lintegral_eq_of_measure_preimage** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α ->ₛ Real>=0∞} 
{g : β ->ₛ Real>=0∞} {ν : Measure β} (H : forall y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y}
)) : f.lintegral μ = g.lintegral ν
参数：H : forall y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_of_subset`：lintegral_eq_of_subset 
(f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : forall x, f x != 0 -> μ (f ⁻¹' 
{f x}) != 0 -> f x in s) : f.lintegra…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.mem_range_of_measure_ne_zero`：mem_range_of_meas
ure_ne_zero {f : α ->ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) != 0) : x i
n f.range

--- 原说明 ---
`SimpleFunc.lintegral` depends only on the measures of `f ⁻¹' {y}`.
-/
theorem lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
    {ν : Measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν := by
  simp only [lintegral, ← H]
  apply lintegral_eq_of_subset
  simp only [H]
  intros
  exact mem_range_of_measure_ne_zero ‹_›

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
/-
**MeasureTheory.SimpleFunc.lintegral_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：lintegral_congr {f g : α ->ₛ Real>=0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g
.lintegral μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_of_measure_preimage`：lintegral_eq_
of_measure_preimage [MeasurableSpace β] {f : α ->ₛ Real>=0∞} {g : β ->ₛ Real>=0∞
} {ν : Measure β} (H : forall y, μ (f ⁻¹' {y}) …
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.Eventually.set_eq`：∀ {α : Type u} {s t : Set α} {l : Filter α}, (
∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t) → s =ᶠ[l] t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If two simple functions are equal a.e., then their `lintegral`s are equal.
-/
theorem lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage fun y =>
    measure_congr <| Eventually.set_eq <| h.mono fun x hx => by simp [hx]
/-
**MeasureTheory.SimpleFunc.lintegral_map'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：lintegral_map' {β} [MeasurableSpace β] {μ' : Measure β} (f : α ->ₛ Real>=0
∞) (g : β ->ₛ Real>=0∞) (m' : α -> β) (eq : forall a, f a = g (m' a)) (h : foral
l s, MeasurableSet s -> μ' s = μ (m' ⁻¹' s)) : f.lintegral μ = g.lintegral μ'
参数：f : α ->ₛ Real>=0∞；g : β ->ₛ Real>=0∞；m' : α -> β；eq : forall a, f a = g (m' 
a)；h : forall s, MeasurableSet s -> μ' s = μ (m' ⁻¹' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_of_measure_preimage`：lintegral_eq_
of_measure_preimage [MeasurableSpace β] {f : α ->ₛ Real>=0∞} {g : β ->ₛ Real>=0∞
} {ν : Measure β} (H : forall y, μ (f ⁻¹' {y}) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
-/
theorem lintegral_map' {β} [MeasurableSpace β] {μ' : Measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
    (m' : α → β) (eq : ∀ a, f a = g (m' a)) (h : ∀ s, MeasurableSet s → μ' s = μ (m' ⁻¹' s)) :
    f.lintegral μ = g.lintegral μ' :=
  lintegral_eq_of_measure_preimage fun y => by
    simp only [preimage, eq]
    exact (h (g ⁻¹' {y}) (g.measurableSet_preimage _)).symm
/-
**MeasureTheory.SimpleFunc.lintegral_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：lintegral_map {β} [MeasurableSpace β] (g : β ->ₛ Real>=0∞) {f : α -> β} (h
f : Measurable f) : g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ
参数：g : β ->ₛ Real>=0∞；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_map'`：lintegral_map' {β} [MeasurableS
pace β] {μ' : Measure β} (f : α ->ₛ Real>=0∞) (g : β ->ₛ Real>=0∞) (m' : α -> β)
 (eq : forall a, f a = g (m' …
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
theorem lintegral_map {β} [MeasurableSpace β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : Measurable f) :
    g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ :=
  Eq.symm <| lintegral_map' _ _ f (fun _ => rfl) fun _s hs => Measure.map_apply hf hs

end Measure

section FinMeasSupp

open Finset Function

open scoped Classical in
/-
**MeasureTheory.SimpleFunc.support_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：support_eq [MeasurableSpace α] [Zero β] (f : α ->ₛ β) : support f = ⋃ y in
 {y in f.range | y != 0}, f ⁻¹' {y}
参数：f : α ->ₛ β。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_eq [MeasurableSpace α] [Zero β] (f : α →ₛ β) :
    support f = ⋃ y ∈ {y ∈ f.range | y ≠ 0}, f ⁻¹' {y} :=
  Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and, exists_prop,
      mem_iUnion, mem_singleton_iff, exists_eq_right']

variable {m : MeasurableSpace α} [Zero β] [Zero γ] {μ : Measure α} {f : α →ₛ β}
/-
**MeasureTheory.SimpleFunc.measurableSet_support** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：measurableSet_support [MeasurableSpace α] (f : α ->ₛ β) : MeasurableSet (s
upport f)
参数：f : α ->ₛ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.support_eq`：support_eq [MeasurableSpace α] [Zer
o β] (f : α ->ₛ β) : support f = ⋃ y in {y in f.range | y != 0}, f ⁻¹' {y}
· 使用定理 `Finset.measurableSet_biUnion`：Finset.measurableSet_biUnion {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b
 in s, f b)
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
-/
theorem measurableSet_support [MeasurableSpace α] (f : α →ₛ β) : MeasurableSet (support f) := by
  rw [f.support_eq]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiber _ _
/-
**MeasureTheory.SimpleFunc.measure_support_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.SimpleFunc`。
形式化陈述：measure_support_lt_top (f : α ->ₛ β) (hf : forall y, y != 0 -> μ (f ⁻¹' {y
}) < ∞) : μ (support f) < ∞
参数：f : α ->ₛ β；hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.support_eq`：support_eq [MeasurableSpace α] [Zer
o β] (f : α ->ₛ β) : support f = ⋃ y in {y in f.range | y != 0}, f ⁻¹' {y}
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_biUnion_finset_le`：measure_biUnion_finset_le (I : 
Finset ι) (s : ι -> Set α) : μ (⋃ i in I, s i) <= ∑ i in I, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
lemma measure_support_lt_top (f : α →ₛ β) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    μ (support f) < ∞ := by
  classical
  rw [support_eq]
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun y hy => ?_)
  rw [Finset.mem_filter] at hy
  exact hf y hy.2

/-- A `SimpleFunc` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
/-
**MeasureTheory.SimpleFunc.FinMeasSupp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [Zero β] → {_m : MeasurableSpace α} → 
MeasureTheory.SimpleFunc α β → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SimpleFunc` has finite measure support if it is equal to `0` outside of a set
 of finite
measure.
-/
protected def FinMeasSupp {_m : MeasurableSpace α} (f : α →ₛ β) (μ : Measure α) : Prop :=
  f =ᶠ[μ.cofinite] 0
/-
**MeasureTheory.SimpleFunc.finMeasSupp_iff_support** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SimpleFunc`。
形式化陈述：finMeasSupp_iff_support : f.FinMeasSupp μ ↔ μ (support f) < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem finMeasSupp_iff_support : f.FinMeasSupp μ ↔ μ (support f) < ∞ :=
  Iff.rfl
/-
**MeasureTheory.SimpleFunc.finMeasSupp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：finMeasSupp_iff : f.FinMeasSupp μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff_support`：finMeasSupp_iff_suppor
t : f.FinMeasSupp μ ↔ μ (support f) < ∞
· 使用定理 `MeasureTheory.SimpleFunc.support_eq`：support_eq [MeasurableSpace α] [Zer
o β] (f : α ->ₛ β) : support f = ⋃ y in {y in f.range | y != 0}, f ⁻¹' {y}
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem finMeasSupp_iff : f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ := by
  classical
  constructor
  · refine fun h y hy => lt_of_le_of_lt (measure_mono ?_) h
    exact fun x hx (H : f x = 0) => hy <| H ▸ Eq.symm hx
  · intro H
    rw [finMeasSupp_iff_support, support_eq]
    exact measure_biUnion_lt_top (finite_toSet _) fun y hy ↦ H y (mem_filter.1 hy).2

namespace FinMeasSupp

/-
**MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc.FinMeasSupp`。
形式化陈述：meas_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y != 0
) : μ (f ⁻¹' {y}) < ∞
参数：h : f.FinMeasSupp μ；hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff`：finMeasSupp_iff : f.FinMeasSup
p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem meas_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y ≠ 0) :
    μ (f ⁻¹' {y}) < ∞ :=
  finMeasSupp_iff.1 h y hy
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc.FinMeasSupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} [in
st : Zero β] [inst_1 : Zero γ]   {μ : MeasureTheory.Measure α} {f : MeasureTheor
y.SimpleFunc α β} {g : β → γ},   f.FinMeasSupp μ → g 0 = 0 → (MeasureTheory.Simp
leFunc.map g f).FinMeasSupp μ
参数：MeasureTheory.SimpleFunc.map g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_comp_subset`：∀ {ι : Type u_1} {M : Type u_3} {N : Type 
u_4} [inst : Zero M] [inst_1 : Zero N] {g : M → N},   g 0 = 0 → ∀ (f : ι → M), F
unction.support (g…
-/
protected theorem map {g : β → γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0) : (f.map g).FinMeasSupp μ :=
  flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.of_map** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc.FinMeasSupp`。
形式化陈述：of_map {g : β -> γ} (h : (f.map g).FinMeasSupp μ) (hg : forall b, g b = 0 
-> b = 0) : f.FinMeasSupp μ
参数：h : (f.map g).FinMeasSupp μ；hg : forall b, g b = 0 -> b = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_subset_comp`：∀ {ι : Type u_1} {M : Type u_3} {N : Type 
u_4} [inst : Zero M] [inst_1 : Zero N] {g : M → N},   (∀ {x : M}, g x = 0 → x = 
0) → ∀ (f : ι → M)…
-/
theorem of_map {g : β → γ} (h : (f.map g).FinMeasSupp μ) (hg : ∀ b, g b = 0 → b = 0) :
    f.FinMeasSupp μ :=
  flip lt_of_le_of_lt h <| measure_mono <| support_subset_comp @hg _
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc.FinMeasSupp`。
形式化陈述：map_iff {g : β -> γ} (hg : forall {b}, g b = 0 ↔ b = 0) : (f.map g).FinMea
sSupp μ ↔ f.FinMeasSupp μ
参数：hg : forall {b}, g b = 0 ↔ b = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.of_map`：of_map {g : β -> γ} (h : (f
.map g).FinMeasSupp μ) (hg : forall b, g b = 0 -> b = 0) : f.FinMeasSupp μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.map`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} {m : MeasurableSpace α} [inst : Zero β] [inst_1 : Zero γ]   {μ 
: MeasureTheory.Measure α} {f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
    (f.map g).FinMeasSupp μ ↔ f.FinMeasSupp μ :=
  ⟨fun h => h.of_map fun _ => hg.1, fun h => h.map <| hg.2 rfl⟩
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.pair** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc.FinMeasSupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} [in
st : Zero β] [inst_1 : Zero γ]   {μ : MeasureTheory.Measure α} {f : MeasureTheor
y.SimpleFunc α β} {g : MeasureTheory.SimpleFunc α γ},   f.FinMeasSupp μ → g.FinM
easSupp μ → (f.pair g).FinMeasSupp μ
参数：f.pair g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.support_prodMk`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} 
[inst : Zero M] [inst_1 : Zero N] (f : ι → M) (g : ι → N),   (Function.support f
un x => (f x,…
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
-/
protected theorem pair {g : α →ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    (pair f g).FinMeasSupp μ :=
  calc
    μ (support <| pair f g) = μ (support f ∪ support g) := congr_arg μ <| support_prodMk f g
    _ ≤ μ (support f) + μ (support g) := measure_union_le _ _
    _ < _ := add_lt_top.2 ⟨hf, hg⟩
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc.FinMeasSupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} [in
st : Zero β] [inst_1 : Zero γ]   {μ : MeasureTheory.Measure α} {f : MeasureTheor
y.SimpleFunc α β} {g : β → γ},   f.FinMeasSupp μ → g 0 = 0 → (MeasureTheory.Simp
leFunc.map g f).FinMeasSupp μ
参数：MeasureTheory.SimpleFunc.map g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Function.support_comp_subset`：∀ {ι : Type u_1} {M : Type u_3} {N : Type 
u_4} [inst : Zero M] [inst_1 : Zero N] {g : M → N},   g 0 = 0 → ∀ (f : ι → M), F
unction.support (g…
-/
protected theorem map₂ [Zero δ] (hf : f.FinMeasSupp μ) {g : α →ₛ γ} (hg : g.FinMeasSupp μ)
    {op : β → γ → δ} (H : op 0 0 = 0) : ((pair f g).map (Function.uncurry op)).FinMeasSupp μ :=
  (hf.pair hg).map H
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc.FinMeasSupp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_5} [inst : AddZeroClass β]   {f g : MeasureTheory.SimpleFunc α β}, f.Fi
nMeasSupp μ → g.FinMeasSupp μ → (f + g).FinMeasSupp μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.add_eq_map₂`：∀ {α : Type u_1} {β : Type u_2} [i
nst : MeasurableSpace α] [inst_1 : Add β] (f g : MeasureTheory.SimpleFunc α β), 
  f + g = MeasureTheory.Si…
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.map₂`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} {δ : Type u_4} {m : MeasurableSpace α} [inst : Zero β] [inst_1
 : Zero γ]   {μ : MeasureTheory…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
protected theorem add {β} [AddZeroClass β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f + g).FinMeasSupp μ := by
  rw [add_eq_map₂]
  exact hf.map₂ hg (zero_add 0)
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc.FinMeasSupp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_5} [inst : MulZeroClass β]   {f g : MeasureTheory.SimpleFunc α β}, f.Fi
nMeasSupp μ → g.FinMeasSupp μ → (f * g).FinMeasSupp μ
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.mul_eq_map₂`：mul_eq_map₂ [Mul β] (f g : α ->ₛ β
) : f * g = (pair f g).map fun p : β × β => p.1 * p.2
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.map₂`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} {δ : Type u_4} {m : MeasurableSpace α} [inst : Zero β] [inst_1
 : Zero γ]   {μ : MeasureTheory…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected theorem mul {β} [MulZeroClass β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f * g).FinMeasSupp μ := by
  rw [mul_eq_map₂]
  exact hf.map₂ hg (zero_mul 0)
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.lintegral_lt_top** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.SimpleFunc.FinMeasSupp`。
形式化陈述：lintegral_lt_top {f : α ->ₛ Real>=0∞} (hm : f.FinMeasSupp μ) (hf : forallᵐ
 a ∂μ, f a != ∞) : f.lintegral μ < ∞
参数：hm : f.FinMeasSupp μ；hf : forallᵐ a ∂μ, f a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff`：finMeasSupp_iff : f.FinMeasSup
p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.FinMeasSupp μ) (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.lintegral μ < ∞ := by
  refine sum_lt_top.2 fun a ha => ?_
  rcases eq_or_ne a ∞ with (rfl | ha)
  · simp only [ae_iff, Ne, Classical.not_not] at hf
    simp [Set.preimage, hf]
  · by_cases ha0 : a = 0
    · subst a
      simp
    · exact mul_lt_top ha.lt_top (finMeasSupp_iff.1 hm _ ha0)
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SimpleFunc.FinMeasSupp`。
形式化陈述：of_lintegral_ne_top {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞) : f.FinM
easSupp μ
参数：h : f.lintegral μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff`：finMeasSupp_iff : f.FinMeasSup
p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `ENNReal.lt_top_of_mul_ne_top_right`：lt_top_of_mul_ne_top_right (h : a * 
b != ∞) (ha : a != 0) : b < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.lt_top_of_sum_ne_top`：lt_top_of_sum_ne_top {s : Finset α} {f : α
 -> Real>=0∞} (h : ∑ x in s, f x != ∞) {a : α} (ha : a in s) : f a < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_of_subset'`：lintegral_eq_of_subset
' (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : f.range \ {0} subseteq s) : f
.lintegral μ = ∑ x in s, x * μ (f ⁻¹' …
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.FinMeasSupp μ := by
  refine finMeasSupp_iff.2 fun b hb => ?_
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hb
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).ne
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.iff_lintegral_lt_top** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc.FinMeasSupp`。
形式化陈述：iff_lintegral_lt_top {f : α ->ₛ Real>=0∞} (hf : forallᵐ a ∂μ, f a != ∞) : 
f.FinMeasSupp μ ↔ f.lintegral μ < ∞
参数：hf : forallᵐ a ∂μ, f a != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.lintegral_lt_top`：lintegral_lt_top 
{f : α ->ₛ Real>=0∞} (hm : f.FinMeasSupp μ) (hf : forallᵐ a ∂μ, f a != ∞) : f.li
ntegral μ < ∞
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top`：of_lintegral_n
e_top {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞) : f.FinMeasSupp μ
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.FinMeasSupp μ ↔ f.lintegral μ < ∞ :=
  ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩

end FinMeasSupp

/-
**MeasureTheory.SimpleFunc.measure_support_lt_top_of_lintegral_ne_top** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：measure_support_lt_top_of_lintegral_ne_top {f : α ->ₛ Real>=0∞} (hf : f.li
ntegral μ != ∞) : μ (support f) < ∞
参数：hf : f.lintegral μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.SimpleFunc.measure_support_lt_top`：measure_support_lt_top 
(f : α ->ₛ β) (hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞) : μ (support f) < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff`：finMeasSupp_iff : f.FinMeasSup
p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top`：of_lintegral_n
e_top {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞) : f.FinMeasSupp μ
-/
lemma measure_support_lt_top_of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (hf : f.lintegral μ ≠ ∞) :
    μ (support f) < ∞ := by
  refine measure_support_lt_top f ?_
  rw [← finMeasSupp_iff]
  exact FinMeasSupp.of_lintegral_ne_top hf

end FinMeasSupp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`).

To use in an induction proof, the syntax is `induction f using SimpleFunc.induction with`. -/
@[elab_as_elim]
/-
**MeasureTheory.SimpleFunc.induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：∀ {α : Type u_5} {γ : Type u_6} [inst : MeasurableSpace α] [inst_1 : AddZe
roClass γ]   {motive : MeasureTheory.SimpleFunc α γ → Prop},   (∀ (c : γ) {s : S
et α} (hs : MeasurableSet s),       motive         (MeasureTheory.SimpleFunc.pie
cewise s hs (MeasureTheory.SimpleFunc.const α c)           (MeasureTheory.Simple
Func.const α 0))) →     (∀ ⦃f g : MeasureTheory.SimpleFunc α γ⦄,         Disjoin
t (Function.support ⇑f) (Function.support ⇑g) → motive f → motive g → motive (f 
+ g)) →       ∀ (f : MeasureTheory.SimpleFunc α γ), motive f
参数：∀ (c : γ) {s : Set α} (hs : MeasurableSet s),       motive         (MeasureTh
eory.SimpleFunc.piecewise s hs (MeasureTheory.SimpleFunc.const α c)           (M
easureTheory.SimpleFunc.const α 0))；∀ ⦃f g : MeasureTheory.SimpleFunc α γ⦄,     
    Disjoint (Function.support ⇑f) (Function.support ⇑g) → motive f → motive g →
 motive (f + g)；f : MeasureTheory.SimpleFunc α γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.range_subset_singleton`：range_subset_singleton {f : ι -> α} {x : α} 
: range f subseteq {x} ↔ f = const ι x
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_same`：piecewise_same (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) : piecewise s hs f f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `Set.range_piecewise`：range_piecewise (f g : α -> β) : range (s.piecewise
 f g) = f '' s union g '' sᶜ
· 使用定理 `Set.image_compl_preimage`：image_compl_preimage {f : α -> β} {s : Set β} 
: f '' (f ⁻¹' s)ᶜ = range f \ s
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `Set.sdiff_sdiff_comm`：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (
s \ u) \ t
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is close
d under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such condit
ions can be added
once we need them (for example it is only necessary to consider the case where `
g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image
 of `f`).

To use in an induction proof, the syntax is `induction f using SimpleFunc.induct
ion with`.
-/
protected theorem induction {α γ} [MeasurableSpace α] [AddZeroClass γ]
    {motive : SimpleFunc α γ → Prop}
    (const : ∀ (c) {s} (hs : MeasurableSet s),
      motive (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)))
    (add : ∀ ⦃f g : SimpleFunc α γ⦄,
      Disjoint (support f) (support g) → motive f → motive g → motive (f + g))
    (f : SimpleFunc α γ) : motive f := by
  classical
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty, sdiff_eq_empty, range_subset_singleton] at h
    convert! const 0 MeasurableSet.univ
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx 0 f
    have Pg : motive g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage, union_sdiff_distrib, sdiff_sdiff_comm, h, Finset.coe_insert,
        insert_sdiff_self_of_notMem, sdiff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]
        convert! Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert! add _ Pg (const x mx)
    · ext1 y
      by_cases hy : y ∈ f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]
    rw [disjoint_iff_inf_le]
    rintro y
    by_cases hy : y ∈ f ⁻¹' {x} <;> simp [g, hy]

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for constant functions and that it is closed under piecewise combinations
of functions.

To use in an induction proof, the syntax is `induction f with`. -/
@[induction_eliminator]
/-
**MeasureTheory.SimpleFunc.induction'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：∀ {α : Type u_5} {γ : Type u_6} [inst : MeasurableSpace α] [Nonempty γ] {P
 : MeasureTheory.SimpleFunc α γ → Prop},   (∀ (c : γ), P (MeasureTheory.SimpleFu
nc.const α c)) →     (∀ ⦃f g : MeasureTheory.SimpleFunc α γ⦄ {s : Set α} (hs : M
easurableSet s),         P f → P g → P (MeasureTheory.SimpleFunc.piecewise s hs 
f g)) →       ∀ (f : MeasureTheory.SimpleFunc α γ), P f
参数：∀ (c : γ), P (MeasureTheory.SimpleFunc.const α c)；∀ ⦃f g : MeasureTheory.Simp
leFunc α γ⦄ {s : Set α} (hs : MeasurableSet s),         P f → P g → P (MeasureTh
eory.SimpleFunc.piecewise s hs f g)；f : MeasureTheory.SimpleFunc α γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.range_subset_singleton`：range_subset_singleton {f : ι -> α} {x : α} 
: range f subseteq {x} ↔ f = const ι x
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `Set.range_piecewise`：range_piecewise (f g : α -> β) : range (s.piecewise
 f g) = f '' s union g '' sᶜ
· 使用定理 `Set.image_compl_preimage`：image_compl_preimage {f : α -> β} {s : Set β} 
: f '' (f ⁻¹' s)ᶜ = range f \ s
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `Set.sdiff_sdiff_comm`：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (
s \ u) \ t
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_compl`：piecewise_compl {s : Set α} (h
s : MeasurableSet sᶜ) (f g : α ->ₛ β) : piecewise sᶜ hs f g = piecewise s hs.of_
compl g f
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
To prove something for an arbitrary simple function, it suffices to show
that the property holds for constant functions and that it is closed under piece
wise combinations
of functions.

To use in an induction proof, the syntax is `induction f with`.
-/
protected theorem induction' {α γ} [MeasurableSpace α] [Nonempty γ] {P : SimpleFunc α γ → Prop}
    (const : ∀ (c), P (SimpleFunc.const _ c))
    (pcw : ∀ ⦃f g : SimpleFunc α γ⦄ {s} (hs : MeasurableSet s), P f → P g →
      P (f.piecewise s hs g))
    (f : SimpleFunc α γ) : P f := by
  let c : γ := Classical.ofNonempty
  classical
  generalize h : f.range \ {c} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty, sdiff_eq_empty, range_subset_singleton] at h
    convert! const c
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx (SimpleFunc.const α c) f
    have Pg : P g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage, union_sdiff_distrib, sdiff_sdiff_comm, h, Finset.coe_insert,
        insert_sdiff_self_of_notMem, sdiff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]
        convert! Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert! pcw mx.compl Pg (const x)
    · ext1 y
      by_cases hy : y ∈ f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]

/-- In a topological vector space, the addition of a measurable function and a simple function is
measurable. -/
/-
**MeasureTheory.SimpleFunc._root_.Measurable.add_simpleFunc** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a topological vector space, the addition of a measurable function and a simpl
e function is
measurable.
-/
theorem _root_.Measurable.add_simpleFunc
    {E : Type*} {_ : MeasurableSpace α} [MeasurableSpace E] [AddCancelMonoid E] [MeasurableAdd E]
    {g : α → E} (hg : Measurable g) (f : SimpleFunc α E) : Measurable (g + (f : α → E)) :=
  f.measurable_bind (fun b a ↦ g a + b) fun b ↦ hg.add_const b

/-- In a topological vector space, the addition of a simple function and a measurable function is
measurable. -/
/-
**MeasureTheory.SimpleFunc._root_.Measurable.simpleFunc_add** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a topological vector space, the addition of a simple function and a measurabl
e function is
measurable.
-/
theorem _root_.Measurable.simpleFunc_add
    {E : Type*} {_ : MeasurableSpace α} [MeasurableSpace E] [AddCancelMonoid E] [MeasurableAdd E]
    {g : α → E} (hg : Measurable g) (f : SimpleFunc α E) : Measurable ((f : α → E) + g) :=
  f.measurable_bind (fun b a ↦ b + g a) fun b ↦ hg.const_add b

end SimpleFunc

end MeasureTheory

open MeasureTheory MeasureTheory.SimpleFunc

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`). -/
@[elab_as_elim]
/-
**Measurable.ennreal_induction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.ennreal_induction {motive : (α -> Real>=0∞) -> Prop} (indicator
 : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s -> motive (Set.indicator s fun _ =
> c)) (add : forall ⦃f g : α -> Real>=0∞⦄, Disjoint (support f) (support g) -> M
easurable f -> Measurable g -> motive f -> motive g -> motive (f + g)) (iSup : f
orall ⦃f : Nat -> α -> Real>=0∞⦄, (forall n, Measurable (f n)) -> Monotone f -> 
(forall n, motive (f n)) -> motive fun x => ⨆ n, f n x) ⦃f : α -> Real>=0∞⦄ (hf 
: Measurable f) : motive f
参数：α -> Real>=0∞；indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s -> motiv
e (Set.indicator s fun _ => c)；add : forall ⦃f g : α -> Real>=0∞⦄, Disjoint (sup
port f) (support g) -> Measurable f -> Measurable g -> motive f -> motive g -> m
otive (f + g)；iSup : forall ⦃f : Nat -> α -> Real>=0∞⦄, (forall n, Measurable (f
 n)) -> Monotone f -> (forall n, motive (f n)) -> motive fun x => ⨆ n, f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …

--- 原说明 ---
To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices
 to show
that the property holds for (multiples of) characteristic functions and is close
d under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and
 such conditions
can be added once we need them (for example in `h_add` it is only necessary to c
onsider the sum of
a simple function with a multiple of a characteristic function and that the inte
rsection
of their images is a subset of `{0}`).
-/
theorem Measurable.ennreal_induction {motive : (α → ℝ≥0∞) → Prop}
    (indicator : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → motive (Set.indicator s fun _ => c))
    (add : ∀ ⦃f g : α → ℝ≥0∞⦄, Disjoint (support f) (support g) →
      Measurable f → Measurable g → motive f → motive g → motive (f + g))
    (iSup : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f →
      (∀ n, motive (f n)) → motive fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : motive f := by
  convert! iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 2
  · rw [iSup_eapprox_apply hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => indicator c hs)
        (fun f g hfg hf hg => add hfg f.measurable g.measurable hf hg) (eapprox f n)

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions with finite mass according to
some sigma-finite measure and is closed under addition and supremum of increasing sequences of
functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`). -/
@[elab_as_elim]
/-
**Measurable.ennreal_sigmaFinite_induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.ennreal_sigmaFinite_induction [SigmaFinite μ] {motive : (α -> R
eal>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s -> μ s
 < ∞ -> motive (Set.indicator s fun _ => c)) (add : forall ⦃f g : α -> Real>=0∞⦄
, Disjoint (support f) (support g) -> Measurable f -> Measurable g -> motive f -
> motive g -> motive (f + g)) (iSup : forall ⦃f : Nat -> α -> Real>=0∞⦄, (forall
 n, Measurable (f n)) -> Monotone f -> (forall n, motive (f n)) -> motive fun x 
=> ⨆ n, f n x) ⦃f : α -> R
参数：α -> Real>=0∞；indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s -> μ s <
 ∞ -> motive (Set.indicator s fun _ => c)；add : forall ⦃f g : α -> Real>=0∞⦄, Di
sjoint (support f) (support g) -> Measurable f -> Measurable g -> motive f -> mo
tive g -> motive (f + g)；iSup : forall ⦃f : Nat -> α -> Real>=0∞⦄, (forall n, Me
asurable (f n)) -> Monotone f -> (forall n, motive (f n)) -> motive fun x => ⨆ n
, f n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_induction`：Measurable.ennreal_induction {motive : (α 
-> Real>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s ->
 motive (Set.indic…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_iUnion_apply`：∀ {ι : Sort u_1} {α : Type u_2} {M : Type u_
3} [inst : CompleteLattice M] [inst_1 : Zero M],   ⊥ = 0 → ∀ (s : ι → Set α) (f 
: α → M) (x : α)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.spanningSets_mono`：spanningSets_mono [SigmaFinite μ] {m n 
: Nat} (hmn : m <= n) : spanningSets μ m subseteq spanningSets μ n
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_inter_lt_top_of_right_ne_top`：measure_inter_lt_top
_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t) < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞

--- 原说明 ---
To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices
 to show
that the property holds for (multiples of) characteristic functions with finite 
mass according to
some sigma-finite measure and is closed under addition and supremum of increasin
g sequences of
functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and
 such conditions
can be added once we need them (for example in `h_add` it is only necessary to c
onsider the sum of
a simple function with a multiple of a characteristic function and that the inte
rsection
of their images is a subset of `{0}`).
-/
lemma Measurable.ennreal_sigmaFinite_induction [SigmaFinite μ] {motive : (α → ℝ≥0∞) → Prop}
    (indicator : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → μ s < ∞ → motive (Set.indicator s fun _ ↦ c))
    (add : ∀ ⦃f g : α → ℝ≥0∞⦄, Disjoint (support f) (support g) →
      Measurable f → Measurable g → motive f → motive g → motive (f + g))
    (iSup : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f →
      (∀ n, motive (f n)) → motive fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : motive f := by
  refine Measurable.ennreal_induction (fun c s hs ↦ ?_) add iSup hf
  convert!
    iSup (f := fun n ↦ (s ∩ spanningSets μ n).indicator fun _ ↦ c)
      (fun n ↦ measurable_const.indicator (hs.inter (measurableSet_spanningSets ..)))
      (fun m n hmn a ↦ by dsimp; grw [hmn])
      (fun n ↦
        indicator _ (hs.inter (measurableSet_spanningSets ..))
          (measure_inter_lt_top_of_right_ne_top (measure_spanningSets_lt_top ..).ne)) with
    a
  simp [← Set.indicator_iUnion_apply (M := ℝ≥0∞) rfl, ← Set.inter_iUnion]
