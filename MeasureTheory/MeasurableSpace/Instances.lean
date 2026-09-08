/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.ZMod.Defs

/-!
# Measurable-space typeclass instances

This file provides measurable-space instances for a selection of standard countable types,
in each case defining the Σ-algebra to be `⊤` (the discrete measurable-space structure).
-/

public section

/-
**Empty.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Empty.instMeasurableSpace : MeasurableSpace Empty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Empty.instMeasurableSpace : MeasurableSpace Empty := ⊤
/-
**PUnit.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PUnit.instMeasurableSpace : MeasurableSpace PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PUnit.instMeasurableSpace : MeasurableSpace PUnit := ⊤
/-
**Bool.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instMeasurableSpace : MeasurableSpace Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bool.instMeasurableSpace : MeasurableSpace Bool := ⊤
/-
**Prop.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instMeasurableSpace : MeasurableSpace Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.instMeasurableSpace : MeasurableSpace Prop := ⊤
/-
**Nat.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instMeasurableSpace : MeasurableSpace Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Nat.instMeasurableSpace : MeasurableSpace ℕ := ⊤
/-
**ENat.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ENat.instMeasurableSpace : MeasurableSpace Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ENat.instMeasurableSpace : MeasurableSpace ℕ∞ := ⊤
/-
**Fin.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.instMeasurableSpace (n : Nat) : MeasurableSpace (Fin n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Fin.instMeasurableSpace (n : ℕ) : MeasurableSpace (Fin n) := ⊤
/-
**ZMod.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZMod.instMeasurableSpace (n : Nat) : MeasurableSpace (ZMod n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ZMod.instMeasurableSpace (n : ℕ) : MeasurableSpace (ZMod n) := ⊤
/-
**Int.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instMeasurableSpace : MeasurableSpace Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Int.instMeasurableSpace : MeasurableSpace ℤ := ⊤
/-
**Rat.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instMeasurableSpace : MeasurableSpace Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Rat.instMeasurableSpace : MeasurableSpace ℚ := ⊤

@[to_additive]
/-
**IterateMulAct.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IterateMulAct.instMeasurableSpace {α : Type*} {f : α -> α} : MeasurableSpa
ce (IterateMulAct f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IterateMulAct.instMeasurableSpace {α : Type*} {f : α → α} :
    MeasurableSpace (IterateMulAct f) := ⊤

@[to_additive]
/-
**IterateMulAct.instDiscreteMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IterateMulAct.instDiscreteMeasurableSpace {α : Type*} {f : α -> α} : Discr
eteMeasurableSpace (IterateMulAct f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
-/
instance IterateMulAct.instDiscreteMeasurableSpace {α : Type*} {f : α → α} :
    DiscreteMeasurableSpace (IterateMulAct f) := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Subsingleton.measurableSingletonClass
    {α} [MeasurableSpace α] [Subsingleton α] : MeasurableSingletonClass α := by
  refine ⟨fun i => ?_⟩
  convert! MeasurableSet.univ
  simp [Set.eq_univ_iff_forall, eq_iff_true_of_subsingleton]
/-
**Bool.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
/-
**Prop.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ => trivial⟩
/-
**Nat.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instMeasurableSingletonClass : MeasurableSingletonClass Nat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance Nat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ := ⟨fun _ => trivial⟩
/-
**ENat.instDiscreteMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ENat.instDiscreteMeasurableSpace : DiscreteMeasurableSpace Nat∞
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance ENat.instDiscreteMeasurableSpace : DiscreteMeasurableSpace ℕ∞ := ⟨fun _ ↦ trivial⟩
/-
**ENat.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ENat.instMeasurableSingletonClass : MeasurableSingletonClass Nat∞
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [in
st : MeasurableSpace α] [DiscreteMeasurableSpace α], MeasurableSingletonClass α
-/
instance ENat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ∞ := inferInstance
/-
**Fin.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.instMeasurableSingletonClass (n : Nat) : MeasurableSingletonClass (Fin
 n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance Fin.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩
/-
**ZMod.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZMod.instMeasurableSingletonClass (n : Nat) : MeasurableSingletonClass (ZM
od n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance ZMod.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (ZMod n) :=
  ⟨fun _ => trivial⟩
/-
**Int.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instMeasurableSingletonClass : MeasurableSingletonClass Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance Int.instMeasurableSingletonClass : MeasurableSingletonClass ℤ := ⟨fun _ => trivial⟩
/-
**Rat.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.instMeasurableSingletonClass : MeasurableSingletonClass Rat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance Rat.instMeasurableSingletonClass : MeasurableSingletonClass ℚ := ⟨fun _ => trivial⟩
