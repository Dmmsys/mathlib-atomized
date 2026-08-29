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

/--
Instance `Empty.instMeasurableSpace` / 实例 `Empty.instMeasurableSpace`

English:
instance Empty.instMeasurableSpace
  signature: : MeasurableSpace Empty
  body: ⊤

中文:
实例 Empty.instMeasurableSpace
  签名: : MeasurableSpace Empty
  定义体: ⊤
-/
instance Empty.instMeasurableSpace : MeasurableSpace Empty := ⊤

/--
Instance `PUnit.instMeasurableSpace` / 实例 `PUnit.instMeasurableSpace`

English:
instance PUnit.instMeasurableSpace
  signature: : MeasurableSpace PUnit
  body: ⊤

中文:
实例 PUnit.instMeasurableSpace
  签名: : MeasurableSpace PUnit
  定义体: ⊤
-/
instance PUnit.instMeasurableSpace : MeasurableSpace PUnit := ⊤

/--
Instance `Bool.instMeasurableSpace` / 实例 `Bool.instMeasurableSpace`

English:
instance Bool.instMeasurableSpace
  signature: : MeasurableSpace Bool
  body: ⊤

中文:
实例 Bool.instMeasurableSpace
  签名: : MeasurableSpace 布尔
  定义体: ⊤
-/
instance Bool.instMeasurableSpace : MeasurableSpace Bool := ⊤

/--
Instance `Prop.instMeasurableSpace` / 实例 `Prop.instMeasurableSpace`

English:
instance Prop.instMeasurableSpace
  signature: : MeasurableSpace Prop
  body: ⊤

中文:
实例 Prop.instMeasurableSpace
  签名: : MeasurableSpace 命题
  定义体: ⊤
-/
instance Prop.instMeasurableSpace : MeasurableSpace Prop := ⊤

/--
Instance `Nat.instMeasurableSpace` / 实例 `Nat.instMeasurableSpace`

English:
instance Nat.instMeasurableSpace
  signature: : MeasurableSpace Nat
  body: ⊤

中文:
实例 Nat.instMeasurableSpace
  签名: : MeasurableSpace 自然数
  定义体: ⊤
-/
instance Nat.instMeasurableSpace : MeasurableSpace Nat := ⊤

/--
Instance `ENat.instMeasurableSpace` / 实例 `ENat.instMeasurableSpace`

English:
instance ENat.instMeasurableSpace
  signature: : MeasurableSpace Nat∞
  body: ⊤

中文:
实例 ENat.instMeasurableSpace
  签名: : MeasurableSpace 自然数∞
  定义体: ⊤
-/
instance ENat.instMeasurableSpace : MeasurableSpace Nat∞ := ⊤

/--
Instance `Fin.instMeasurableSpace` / 实例 `Fin.instMeasurableSpace`

English:
instance Fin.instMeasurableSpace
  signature: (n : Nat)
  body: ⊤

中文:
实例 Fin.instMeasurableSpace
  签名: (n : 自然数)
  定义体: ⊤
-/
instance Fin.instMeasurableSpace (n : Nat) : MeasurableSpace (Fin n) := ⊤

/--
Instance `ZMod.instMeasurableSpace` / 实例 `ZMod.instMeasurableSpace`

English:
instance ZMod.instMeasurableSpace
  signature: (n : Nat)
  body: ⊤

中文:
实例 ZMod.instMeasurableSpace
  签名: (n : 自然数)
  定义体: ⊤
-/
instance ZMod.instMeasurableSpace (n : Nat) : MeasurableSpace (ZMod n) := ⊤

/--
Instance `Int.instMeasurableSpace` / 实例 `Int.instMeasurableSpace`

English:
instance Int.instMeasurableSpace
  signature: : MeasurableSpace Int
  body: ⊤

中文:
实例 Int.instMeasurableSpace
  签名: : MeasurableSpace 整数
  定义体: ⊤
-/
instance Int.instMeasurableSpace : MeasurableSpace Int := ⊤

/--
Instance `Rat.instMeasurableSpace` / 实例 `Rat.instMeasurableSpace`

English:
instance Rat.instMeasurableSpace
  signature: : MeasurableSpace Rat
  body: ⊤

@[to_additive]

中文:
实例 Rat.instMeasurableSpace
  签名: : MeasurableSpace Rat
  定义体: ⊤

@[to_additive]
-/
instance Rat.instMeasurableSpace : MeasurableSpace Rat := ⊤

@[to_additive]
/--
Instance `IterateMulAct.instMeasurableSpace` / 实例 `IterateMulAct.instMeasurableSpace`

English:
instance IterateMulAct.instMeasurableSpace
  signature: {α : Type*} {f : α -> α}
  body: ⊤

@[to_additive]

中文:
实例 IterateMulAct.instMeasurableSpace
  签名: {α : 类型} {f : α -> α}
  定义体: ⊤

@[to_additive]
-/
instance IterateMulAct.instMeasurableSpace {α : Type*} {f : α -> α} :
    MeasurableSpace (IterateMulAct f) := ⊤

@[to_additive]
/--
Instance `IterateMulAct.instDiscreteMeasurableSpace` / 实例 `IterateMulAct.instDiscreteMeasurableSpace`

English:
instance IterateMulAct.instDiscreteMeasurableSpace
  signature: {α : Type*} {f : α -> α}
  body: inferInstance

中文:
实例 IterateMulAct.instDiscreteMeasurableSpace
  签名: {α : 类型} {f : α -> α}
  定义体: inferInstance
-/
instance IterateMulAct.instDiscreteMeasurableSpace {α : Type*} {f : α -> α} :
    DiscreteMeasurableSpace (IterateMulAct f) := inferInstance

instance (priority := 100) Subsingleton.measurableSingletonClass
    {α} [MeasurableSpace α] [Subsingleton α] : MeasurableSingletonClass α := by
  refine ⟨fun i => ?_⟩
  convert! MeasurableSet.univ
  simp [Set.eq_univ_iff_forall, eq_iff_true_of_subsingleton]

/--
Instance `Bool.instMeasurableSingletonClass` / 实例 `Bool.instMeasurableSingletonClass`

English:
instance Bool.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass Bool
  body: ⟨fun _ => trivial⟩

中文:
实例 Bool.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass 布尔
  定义体: ⟨fun _ => trivial⟩
-/
instance Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

/--
Instance `Prop.instMeasurableSingletonClass` / 实例 `Prop.instMeasurableSingletonClass`

English:
instance Prop.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass Prop
  body: ⟨fun _ => trivial⟩

中文:
实例 Prop.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass 命题
  定义体: ⟨fun _ => trivial⟩
-/
instance Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ => trivial⟩

/--
Instance `Nat.instMeasurableSingletonClass` / 实例 `Nat.instMeasurableSingletonClass`

English:
instance Nat.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass Nat
  body: ⟨fun _ => trivial⟩

中文:
实例 Nat.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass 自然数
  定义体: ⟨fun _ => trivial⟩
-/
instance Nat.instMeasurableSingletonClass : MeasurableSingletonClass Nat := ⟨fun _ => trivial⟩

/--
Instance `ENat.instDiscreteMeasurableSpace` / 实例 `ENat.instDiscreteMeasurableSpace`

English:
instance ENat.instDiscreteMeasurableSpace
  signature: : DiscreteMeasurableSpace Nat∞
  body: ⟨fun _ => trivial⟩

中文:
实例 ENat.instDiscreteMeasurableSpace
  签名: : DiscreteMeasurableSpace 自然数∞
  定义体: ⟨fun _ => trivial⟩
-/
instance ENat.instDiscreteMeasurableSpace : DiscreteMeasurableSpace Nat∞ := ⟨fun _ => trivial⟩

/--
Instance `ENat.instMeasurableSingletonClass` / 实例 `ENat.instMeasurableSingletonClass`

English:
instance ENat.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass Nat∞
  body: inferInstance

中文:
实例 ENat.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass 自然数∞
  定义体: inferInstance
-/
instance ENat.instMeasurableSingletonClass : MeasurableSingletonClass Nat∞ := inferInstance

/--
Instance `Fin.instMeasurableSingletonClass` / 实例 `Fin.instMeasurableSingletonClass`

English:
instance Fin.instMeasurableSingletonClass
  signature: (n : Nat)
  body: ⟨fun _ => trivial⟩

中文:
实例 Fin.instMeasurableSingletonClass
  签名: (n : 自然数)
  定义体: ⟨fun _ => trivial⟩
-/
instance Fin.instMeasurableSingletonClass (n : Nat) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩

/--
Instance `ZMod.instMeasurableSingletonClass` / 实例 `ZMod.instMeasurableSingletonClass`

English:
instance ZMod.instMeasurableSingletonClass
  signature: (n : Nat)
  body: ⟨fun _ => trivial⟩

中文:
实例 ZMod.instMeasurableSingletonClass
  签名: (n : 自然数)
  定义体: ⟨fun _ => trivial⟩
-/
instance ZMod.instMeasurableSingletonClass (n : Nat) : MeasurableSingletonClass (ZMod n) :=
  ⟨fun _ => trivial⟩

/--
Instance `Int.instMeasurableSingletonClass` / 实例 `Int.instMeasurableSingletonClass`

English:
instance Int.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass Int
  body: ⟨fun _ => trivial⟩

中文:
实例 Int.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass 整数
  定义体: ⟨fun _ => trivial⟩
-/
instance Int.instMeasurableSingletonClass : MeasurableSingletonClass Int := ⟨fun _ => trivial⟩

/--
Instance `Rat.instMeasurableSingletonClass` / 实例 `Rat.instMeasurableSingletonClass`

English:
instance Rat.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass Rat
  body: ⟨fun _ => trivial⟩

中文:
实例 Rat.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass Rat
  定义体: ⟨fun _ => trivial⟩
-/
instance Rat.instMeasurableSingletonClass : MeasurableSingletonClass Rat := ⟨fun _ => trivial⟩
