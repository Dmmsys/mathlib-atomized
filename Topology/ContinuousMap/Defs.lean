/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
module

public import Mathlib.Data.FunLike.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Lift
public import Mathlib.Topology.Defs.Basic

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass
which is meant to be satisfied by itself and all stricter types.
-/

@[expose] public section

open Function
open scoped Topology

/--
Definition of `ContinuousMap` / `ContinuousMap` 的定义

English:
structure ContinuousMap
  parameters: (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  axioms and operations (2):
    - toFun : X -> Y
    - continuous_toFun : Continuous toFun  [default: by fun_prop]

中文:
结构 ContinuousMap
  参数: (X Y : 类型) [TopologicalSpace X] [TopologicalSpace Y]
  公理与运算 (2 个):
    - toFun : X -> Y
    - continuous_toFun : Continuous toFun  [默认: by fun_prop]

Depends on / 依赖: fun_prop
-/
structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The function `X → Y` -/
  protected toFun : X -> Y
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by fun_prop

/-- `C(X, Y)` is the type of continuous maps from `X` to `Y`. -/
notation "C(" X ", " Y ")" => ContinuousMap X Y

section

/--
Definition of `ContinuousMapClass` / `ContinuousMapClass` 的定义

English:
class ContinuousMapClass
  parameters: (F : Type*) (X Y : outParam Type*)
  axioms and operations (1):
    - map_continuous((f : F)) : Continuous f

中文:
类 ContinuousMapClass
  参数: (F : 类型) (X Y : outParam 类型)
  公理与运算 (1 个):
    - map_continuous((f : F)) : Continuous f
-/
class ContinuousMapClass (F : Type*) (X Y : outParam Type*)
    [TopologicalSpace X] [TopologicalSpace Y] [FunLike F X Y] : Prop where
  /-- Continuity -/
  map_continuous (f : F) : Continuous f

end

export ContinuousMapClass (map_continuous)

attribute [continuity, fun_prop] map_continuous

section ContinuousMapClass

variable {F X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [FunLike F X Y]
variable [ContinuousMapClass F X Y]

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: (f : F)
  body: ⟨f, map_continuous f⟩

中文:
定义 toContinuousMap
  签名: (f : F)
  定义体: ⟨f, map_continuous f⟩
-/
@[coe, reducible] def toContinuousMap (f : F) : C(X, Y) := ⟨f, map_continuous f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F C(X, Y)
  body: ⟨toContinuousMap⟩

中文:
实例 :
  签名: CoeTC F C(X, Y)
  定义体: ⟨toContinuousMap⟩
-/
instance : CoeTC F C(X, Y) := ⟨toContinuousMap⟩

end ContinuousMapClass

/-! ### Continuous maps -/


namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike C(X, Y) X Y where
  body: ContinuousMap.toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 instFunLike
  签名: : FunLike C(X, Y) X Y where
  定义体: ContinuousMap.toFun
  coe_injective f g h := by cases f; cases g; congr

Depends on / 依赖: ContinuousMap, ContinuousMap.toFun
-/
instance instFunLike : FunLike C(X, Y) X Y where
  coe := ContinuousMap.toFun
  coe_injective f g h := by cases f; cases g; congr

/--
Instance `instContinuousMapClass` / 实例 `instContinuousMapClass`

English:
instance instContinuousMapClass
  signature: : ContinuousMapClass C(X, Y) X Y where
  body: ContinuousMap.continuous_toFun

@[simp]

中文:
实例 instContinuousMapClass
  签名: : ContinuousMapClass C(X, Y) X Y where
  定义体: ContinuousMap.continuous_toFun

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_toFun, continuous_toFun
-/
instance instContinuousMapClass : ContinuousMapClass C(X, Y) X Y where
  map_continuous := ContinuousMap.continuous_toFun

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : C(X, Y)}
  statement: f.toFun = (f : X -> Y)
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: {f : C(X, Y)}
  结论: f.toFun = (f : X -> Y)
  证明: rfl
-/
theorem toFun_eq_coe {f : C(X, Y)} : f.toFun = (f : X -> Y) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (X -> Y) C(X, Y) DFunLike.coe Continuous
  body: ⟨fun f hf => ⟨⟨f, hf⟩, rfl⟩⟩

中文:
实例 :
  签名: CanLift (X -> Y) C(X, Y) DFunLike.coe Continuous
  定义体: ⟨fun f hf => ⟨⟨f, hf⟩, rfl⟩⟩
-/
instance : CanLift (X -> Y) C(X, Y) DFunLike.coe Continuous := ⟨fun f hf => ⟨⟨f, hf⟩, rfl⟩⟩

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : C(X, Y))
  body: f

中文:
定义 Simps.apply
  签名: (f : C(X, Y))
  定义体: f
-/
def Simps.apply (f : C(X, Y)) : X -> Y := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun -> apply)

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F)
  proof: rfl

中文:
定理 coe_coe
  条件: {F : 类型} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F)
  证明: rfl
-/
protected theorem coe_coe {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) :
    ⇑(f : C(X, Y)) = f :=
  rfl

/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) (x : X)
  proof: rfl

中文:
定理 coe_apply
  条件: {F : 类型} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) (x : X)
  证明: rfl
-/
protected theorem coe_apply {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) (x : X) :
    (f : C(X, Y)) x = f x :=
  rfl

/--
theorem `coe_injective'` / 定理 `coe_injective'`

English:
theorem coe_injective'
  given: {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y]
  proof: .of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective'
  条件: {F : 类型} [FunLike F X Y] [ContinuousMapClass F X Y]
  证明: .of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[ext]
-/
protected theorem coe_injective' {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] :
    Injective (toContinuousMap : F -> C(X, Y)) :=
  .of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : C(X, Y)} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : C(X, Y)} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : C(X, Y)) (f' : X -> Y) (h : f' = f)
  body: f'
  continuous_toFun := h.symm ▸ f.continuous_toFun

@[simp]

中文:
定义 copy
  签名: (f : C(X, Y)) (f' : X -> Y) (h : f' = f)
  定义体: f'
  continuous_toFun := h.symm ▸ f.continuous_toFun

@[simp]
-/
protected def copy (f : C(X, Y)) (f' : X -> Y) (h : f' = f) : C(X, Y) where
  toFun := f'
  continuous_toFun := h.symm ▸ f.continuous_toFun

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : C(X, Y)) (f' : X -> Y) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : C(X, Y)) (f' : X -> Y) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : C(X, Y)) (f' : X -> Y) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : C(X, Y)) (f' : X -> Y) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : C(X, Y)) (f' : X -> Y) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : C(X, Y)) (f' : X -> Y) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : C(X, Y))
  statement: Continuous f
  proof: f.continuous_toFun

中文:
定理 continuous
  条件: (f : C(X, Y))
  结论: Continuous f
  证明: f.continuous_toFun
-/
protected theorem continuous (f : C(X, Y)) : Continuous f :=
  f.continuous_toFun

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : C(X, Y)} (H : f = g) (x : X)
  statement: f x = g x
  proof: H ▸ rfl

中文:
定理 congr_fun
  条件: {f g : C(X, Y)} (H : f = g) (x : X)
  结论: f x = g x
  证明: H ▸ rfl
-/
protected theorem congr_fun {f g : C(X, Y)} (H : f = g) (x : X) : f x = g x :=
  H ▸ rfl

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : C(X, Y)) {x y : X} (h : x = y)
  statement: f x = f y
  proof: h ▸ rfl

中文:
定理 congr_arg
  条件: (f : C(X, Y)) {x y : X} (h : x = y)
  结论: f x = f y
  证明: h ▸ rfl
-/
protected theorem congr_arg (f : C(X, Y)) {x y : X} (h : x = y) : f x = f y :=
  h ▸ rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective (DFunLike.coe : C(X, Y) -> (X -> Y))
  proof: DFunLike.coe_injective

@[simp]

中文:
定理 coe_injective
  结论: Function.Injective (DFunLike.coe : C(X, Y) -> (X -> Y))
  证明: DFunLike.coe_injective

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective (DFunLike.coe : C(X, Y) -> (X -> Y)) :=
  DFunLike.coe_injective

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : X -> Y) (h : Continuous f)
  statement: ⇑(⟨f, h⟩ : C(X, Y)) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : X -> Y) (h : Continuous f)
  结论: ⇑(⟨f, h⟩ : C(X, Y)) = f
  证明: rfl
-/
theorem coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ : C(X, Y)) = f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: Y] : Subsingleton C(X, Y)
  body: DFunLike.subsingleton_cod

中文:
实例 [Subsingleton
  签名: Y] : Subsingleton C(X, Y)
  定义体: DFunLike.subsingleton_cod

Depends on / 依赖: DFunLike, DFunLike.subsingleton_cod, subsingleton_cod
-/
instance [Subsingleton Y] : Subsingleton C(X, Y) := DFunLike.subsingleton_cod
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: X] : Subsingleton C(X, Y)
  body: DFunLike.subsingleton_dom

中文:
实例 [IsEmpty
  签名: X] : Subsingleton C(X, Y)
  定义体: DFunLike.subsingleton_dom

Depends on / 依赖: DFunLike, DFunLike.subsingleton_dom, subsingleton_dom
-/
instance [IsEmpty X] : Subsingleton C(X, Y) := DFunLike.subsingleton_dom

end ContinuousMap
