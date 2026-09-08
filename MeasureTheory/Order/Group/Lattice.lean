/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability results on groups with a lattice structure.

## Tags

measurable function, group, lattice operation
-/

public section

variable {α β : Type*} [Lattice α] [Group α] [MeasurableSpace α]
  [MeasurableSpace β] {f : β → α}

@[to_additive]
/-
**measurable_oneLePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_oneLePart [MeasurableSup α] : Measurable (oneLePart : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSup.measurable_sup_const`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Max M} [self : MeasurableSup M] (c : M), Measurable fun x => x
 ⊔ c
-/
theorem measurable_oneLePart [MeasurableSup α] : Measurable (oneLePart : α → α) :=
  measurable_sup_const _

@[to_additive (attr := fun_prop)]
/-
**Measurable.oneLePart** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Lattice α] [inst_1 : Group α] [ins
t_2 : MeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β → α} [MeasurableS
up α], Measurable f → Measurable fun x => (f x)⁺ᵐ
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_oneLePart`：measurable_oneLePart [MeasurableSup α] : Measurabl
e (oneLePart : α -> α)
-/
protected theorem Measurable.oneLePart [MeasurableSup α] (hf : Measurable f) :
    Measurable fun x ↦ oneLePart (f x) :=
  measurable_oneLePart.comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.oneLePart** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Lattice α] [inst_1 : Group α] [ins
t_2 : MeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β → α} {μ : Measure
Theory.Measure β} [MeasurableSup α],   AEMeasurable f μ → AEMeasurable (fun x =>
 (f x)⁺ᵐ) μ
参数：fun x => (f x)⁺ᵐ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.sup_const`：AEMeasurable.sup_const (hf : AEMeasurable f μ) (
c : M) : AEMeasurable (fun x => f x ⊔ c) μ
-/
protected theorem AEMeasurable.oneLePart {μ : MeasureTheory.Measure β} [MeasurableSup α]
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ oneLePart (f x)) μ :=
  hf.sup_const 1

variable [MeasurableInv α]

@[to_additive]
/-
**measurable_leOnePart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_leOnePart [MeasurableSup α] : Measurable (leOnePart : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableSup.measurable_sup_const`：∀ {M : Type u_1} {inst : MeasurableS
pace M} {inst_1 : Max M} [self : MeasurableSup M] (c : M), Measurable fun x => x
 ⊔ c
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
theorem measurable_leOnePart [MeasurableSup α] : Measurable (leOnePart : α → α) :=
  (measurable_sup_const _).comp measurable_inv

@[to_additive (attr := fun_prop)]
/-
**Measurable.leOnePart** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Lattice α] [inst_1 : Group α] [ins
t_2 : MeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β → α} [MeasurableI
nv α] [MeasurableSup α],   Measurable f → Measurable fun x => (f x)⁻ᵐ
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_leOnePart`：measurable_leOnePart [MeasurableSup α] : Measurabl
e (leOnePart : α -> α)
-/
protected theorem Measurable.leOnePart [MeasurableSup α] (hf : Measurable f) :
    Measurable fun x ↦ leOnePart (f x) :=
  measurable_leOnePart.comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.leOnePart** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Lattice α] [inst_1 : Group α] [ins
t_2 : MeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β → α} [MeasurableI
nv α] {μ : MeasureTheory.Measure β} [MeasurableSup α],   AEMeasurable f μ → AEMe
asurable (fun x => (f x)⁻ᵐ) μ
参数：fun x => (f x)⁻ᵐ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.sup_const`：AEMeasurable.sup_const (hf : AEMeasurable f μ) (
c : M) : AEMeasurable (fun x => f x ⊔ c) μ
· 使用定理 `AEMeasurable.inv`：AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurabl
e f⁻¹ μ
-/
protected theorem AEMeasurable.leOnePart {μ : MeasureTheory.Measure β} [MeasurableSup α]
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ leOnePart (f x)) μ :=
  hf.inv.sup_const 1

variable [MeasurableSup₂ α]

@[to_additive]
/-
**measurable_mabs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_mabs : Measurable (mabs : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.sup`：Measurable.sup (hf : Measurable f) (hg : Measurable g) :
 Measurable (f ⊔ g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
theorem measurable_mabs : Measurable (mabs : α → α) :=
  measurable_id'.sup measurable_inv

@[to_additive (attr := fun_prop)]
/-
**Measurable.mabs** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Lattice α] [inst_1 : Group α] [ins
t_2 : MeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β → α} [MeasurableI
nv α] [MeasurableSup₂ α],   Measurable f → Measurable fun x => |f x|ₘ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_mabs`：measurable_mabs : Measurable (mabs : α -> α)
-/
protected theorem Measurable.mabs (hf : Measurable f) : Measurable fun x ↦ mabs (f x) :=
  measurable_mabs.comp hf

@[to_additive (attr := fun_prop)]
/-
**AEMeasurable.mabs** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Lattice α] [inst_1 : Group α] [ins
t_2 : MeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β → α} [MeasurableI
nv α] [MeasurableSup₂ α] {μ : MeasureTheory.Measure β},   AEMeasurable f μ → AEM
easurable (fun x => |f x|ₘ) μ
参数：fun x => |f x|ₘ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_mabs`：measurable_mabs : Measurable (mabs : α -> α)
-/
protected theorem AEMeasurable.mabs {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ mabs (f x)) μ :=
  measurable_mabs.comp_aemeasurable hf
