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

/-- The type of continuous maps from `X` to `Y`.

When possible, instead of parametrizing results over `(f : C(X, Y))`,
you should parametrize over `{F : Type*} [ContinuousMapClass F X Y] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMapClass`. -/
/-
**ContinuousMap** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] wher
e /-- The function `X → Y` -/ protected toFun : X -> Y /-- Proposition that `toF
un` is continuous -/ protected continuous_toFun : Continuous toFun
参数：X Y : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous maps from `X` to `Y`.

When possible, instead of parametrizing results over `(f : C(X, Y))`,
you should parametrize over `{F : Type*} [ContinuousMapClass F X Y] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMapClass`.
-/
structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The function `X → Y` -/
  protected toFun : X → Y
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by fun_prop

/-- `C(X, Y)` is the type of continuous maps from `X` to `Y`. -/
notation "C(" X ", " Y ")" => ContinuousMap X Y

section

/-- `ContinuousMapClass F X Y` states that `F` is a type of continuous maps.

You should extend this class when you extend `ContinuousMap`. -/
/-
**ContinuousMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (X : outParam (Type u_2)) →     (Y : outParam (Type u_3
)) → [TopologicalSpace X] → [TopologicalSpace Y] → [FunLike F X Y] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMapClass F X Y` states that `F` is a type of continuous maps.

You should extend this class when you extend `ContinuousMap`.
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

/-- Coerce a bundled morphism with a `ContinuousMapClass` instance to a `ContinuousMap`. -/
/-
**toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{F : Type u_1} →   {X : Type u_2} →     {Y : Type u_3} →       [inst : Top
ologicalSpace X] →         [inst_1 : TopologicalSpace Y] → [inst_2 : FunLike F X
 Y] → [ContinuousMapClass F X Y] → F → C(X, Y)
参数：X, Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…

--- 原说明 ---
Coerce a bundled morphism with a `ContinuousMapClass` instance to a `ContinuousM
ap`.
-/
@[coe, reducible] def toContinuousMap (f : F) : C(X, Y) := ⟨f, map_continuous f⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce a bundled morphism with a `ContinuousMapClass` instance to a `ContinuousM
ap`.
-/
instance : CoeTC F C(X, Y) := ⟨toContinuousMap⟩

end ContinuousMapClass

/-! ### Continuous maps -/


namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-
**ContinuousMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instFunLike : FunLike C(X, Y) X Y where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike C(X, Y) X Y where
  coe := ContinuousMap.toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**ContinuousMap.instContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`
。
形式化陈述：instContinuousMapClass : ContinuousMapClass C(X, Y) X Y where map_continuo
us
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
instance instContinuousMapClass : ContinuousMapClass C(X, Y) X Y where
  map_continuous := ContinuousMap.continuous_toFun

@[simp]
/-
**ContinuousMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：toFun_eq_coe {f : C(X, Y)} : f.toFun = (f : X -> Y)
参数：X, Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : C(X, Y)} : f.toFun = (f : X → Y) :=
  rfl
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (X → Y) C(X, Y) DFunLike.coe Continuous := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- See note [custom simps projection]. -/
/-
**ContinuousMap.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Simps`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : 
TopologicalSpace Y] → C(X, Y) → X → Y
参数：X, Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [custom simps projection].
-/
def Simps.apply (f : C(X, Y)) : X → Y := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

@[simp]
/-
**ContinuousMap.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {F : Type u_3}   [inst_2 : FunLike F X Y] [inst_3 : ContinuousMa
pClass F X Y] (f : F), ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) :
    ⇑(f : C(X, Y)) = f :=
  rfl
/-
**ContinuousMap.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {F : Type u_3}   [inst_2 : FunLike F X Y] [inst_3 : ContinuousMa
pClass F X Y] (f : F) (x : X), ↑f x = f x
参数：f : F；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_apply {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) (x : X) :
    (f : C(X, Y)) x = f x :=
  rfl

/-- Coercion to a `ContinuousMap` is injective.

The unprimed version `ContinuousMap.coe_injective`
is used for the coercion from `C(X, Y)` to `X → Y`. -/
/-
**ContinuousMap.coe_injective'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {F : Type u_3}   [inst_2 : FunLike F X Y] [inst_3 : ContinuousMa
pClass F X Y], Function.Injective toContinuousMap
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
Coercion to a `ContinuousMap` is injective.

The unprimed version `ContinuousMap.coe_injective`
is used for the coercion from `C(X, Y)` to `X → Y`.
-/
protected theorem coe_injective' {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] :
    Injective (toContinuousMap : F → C(X, Y)) :=
  .of_comp (f := DFunLike.coe) DFunLike.coe_injective

@[ext]
/-
**ContinuousMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
参数：X, Y；h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : C(X, Y)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `ContinuousMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**ContinuousMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     [inst : TopologicalSpace X] → [ins
t_1 : TopologicalSpace Y] → (f : C(X, Y)) → (f' : X → Y) → f' = ⇑f → C(X, Y)
参数：f : C(X, Y)；f' : X → Y；X, Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ContinuousMap` with a new `toFun` equal to the old one. Useful to fix
 definitional
equalities.
-/
protected def copy (f : C(X, Y)) (f' : X → Y) (h : f' = f) : C(X, Y) where
  toFun := f'
  continuous_toFun := h.symm ▸ f.continuous_toFun

@[simp]
/-
**ContinuousMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_copy (f : C(X, Y)) (f' : X -> Y) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : C(X, Y)；f' : X -> Y；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : C(X, Y)) (f' : X → Y) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**ContinuousMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：copy_eq (f : C(X, Y)) (f' : X -> Y) (h : f' = f) : f.copy f' h = f
参数：f : C(X, Y)；f' : X -> Y；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : C(X, Y)) (f' : X → Y) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/-- Deprecated. Use `map_continuous` instead. -/
/-
**ContinuousMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : C(X, Y)), Continuous ⇑f
参数：f : C(X, Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun

--- 原说明 ---
Deprecated. Use `map_continuous` instead.
-/
protected theorem continuous (f : C(X, Y)) : Continuous f :=
  f.continuous_toFun

/-- Deprecated. Use `DFunLike.congr_fun` instead. -/
/-
**ContinuousMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X), f x = g x
参数：X, Y；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Deprecated. Use `DFunLike.congr_fun` instead.
-/
protected theorem congr_fun {f g : C(X, Y)} (H : f = g) (x : X) : f x = g x :=
  H ▸ rfl

/-- Deprecated. Use `DFunLike.congr_arg` instead. -/
/-
**ContinuousMap.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : C(X, Y)) {x y : X},   x = y → f x = f y
参数：f : C(X, Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Deprecated. Use `DFunLike.congr_arg` instead.
-/
protected theorem congr_arg (f : C(X, Y)) {x y : X} (h : x = y) : f x = f y :=
  h ▸ rfl
/-
**ContinuousMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_injective : Function.Injective (DFunLike.coe : C(X, Y) -> (X -> Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : Function.Injective (DFunLike.coe : C(X, Y) → (X → Y)) :=
  DFunLike.coe_injective

@[simp]
/-
**ContinuousMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ : C(X, Y)) = f
参数：f : X -> Y；h : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : X → Y) (h : Continuous f) : ⇑(⟨f, h⟩ : C(X, Y)) = f :=
  rfl
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton Y] : Subsingleton C(X, Y) := DFunLike.subsingleton_cod
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty X] : Subsingleton C(X, Y) := DFunLike.subsingleton_dom

end ContinuousMap

