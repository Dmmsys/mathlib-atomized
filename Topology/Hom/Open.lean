/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous open maps

This file defines bundled continuous open maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `ContinuousOpenMap`: Continuous open maps.

## Typeclasses

* `ContinuousOpenMapClass`
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/--
Definition of `ContinuousOpenMap` / `ContinuousOpenMap` 的定义

English:
structure ContinuousOpenMap
  parameters: (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
  axioms and operations (1):
    - map_open' : IsOpenMap toFun

中文:
结构 余ntinuousOpen映射
  参数: (α β : 类型) [拓扑空间 α] [拓扑空间 β]
  公理与运算 (1 个):
    - map_open' : 是开映射 toFun
-/
structure ContinuousOpenMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β where
  map_open' : IsOpenMap toFun

@[inherit_doc] infixr:25 " ->CO " => ContinuousOpenMap

section

/--
Definition of `ContinuousOpenMapClass` / `ContinuousOpenMapClass` 的定义

English:
class ContinuousOpenMapClass
  parameters: (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  extends: ContinuousMapClass F α β
  axioms and operations (1):
    - map_open((f : F)) : IsOpenMap f

中文:
类 余ntinuousOpen映射类
  参数: (F : 类型) (α β : outParam 类型) [拓扑空间 α]
  继承: 连续映射类 F α β
  公理与运算 (1 个):
    - map_open((f : F)) : 是开映射 f
-/
class ContinuousOpenMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  [TopologicalSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  map_open (f : F) : IsOpenMap f

end

export ContinuousOpenMapClass (map_open)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [TopologicalSpace β] [FunLike F α β]
  body: ⟨fun f => ⟨f, map_open f⟩⟩

中文:
实例 [拓扑空间
  签名: α] [拓扑空间 β] [函数状 F α β]
  定义体: ⟨fun f => ⟨f, map_open f⟩⟩

Depends on / 依赖: map_open
-/
instance [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
    [ContinuousOpenMapClass F α β] :
    CoeTC F (α ->CO β) :=
  ⟨fun f => ⟨f, map_open f⟩⟩

/-! ### Continuous open maps -/


namespace ContinuousOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (α ->CO β) α β where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : 函数状 (α ->CO β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (α ->CO β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousOpenMapClass (α ->CO β) α β
  body: f.continuous_toFun
  map_open f := f.map_open'

中文:
实例 :
  签名: 余ntinuousOpen映射类 (α ->CO β) α β
  定义体: f.continuous_toFun
  map_open f := f.map_open'

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance : ContinuousOpenMapClass (α ->CO β) α β where
  map_continuous f := f.continuous_toFun
  map_open f := f.map_open'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : α ->CO β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: {f : α ->CO β}
  结论: f.toFun = (f : α -> β)
  证明: rfl
-/
theorem toFun_eq_coe {f : α ->CO β} : f.toFun = (f : α -> β) :=
  rfl

/-- `simp`-normal form of `toFun_eq_coe`. -/
@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  given: (f : α ->CO β)
  statement: (f.toContinuousMap : α -> β) = f
  proof: rfl

@[ext]

中文:
定理 coe_toContinuousMap
  条件: (f : α ->CO β)
  结论: (f.toContinuousMap : α -> β) = f
  证明: rfl

@[ext]
-/
theorem coe_toContinuousMap (f : α ->CO β) : (f.toContinuousMap : α -> β) = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->CO β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : α ->CO β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ->CO β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->CO β) (f' : α -> β) (h : f' = f)
  body: ⟨f.toContinuousMap.copy f' h, h.symm.subst f.map_open'⟩

@[simp]

中文:
定义 copy
  签名: (f : α ->CO β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f.toContinuousMap.copy f' h, h.symm.subst f.map_open'⟩

@[simp]
-/
protected def copy (f : α ->CO β) (f' : α -> β) (h : f' = f) : α ->CO β :=
⟨f.toContinuousMap.copy f' h, h.symm.subst f.map_open'⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->CO β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->CO β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : α ->CO β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->CO β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->CO β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->CO β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->CO α
  body: ⟨ContinuousMap.id _, IsOpenMap.id⟩

中文:
定义 id
  签名: : α ->CO α
  定义体: ⟨ContinuousMap.id _, IsOpenMap.id⟩
-/
protected def id : α ->CO α :=
  ⟨ContinuousMap.id _, IsOpenMap.id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->CO α)
  body: ⟨ContinuousOpenMap.id _⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (α ->CO α)
  定义体: ⟨ContinuousOpenMap.id _⟩

@[simp, norm_cast]

Depends on / 依赖: ContinuousOpenMap, ContinuousOpenMap.id
-/
instance : Inhabited (α ->CO α) :=
  ⟨ContinuousOpenMap.id _⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(ContinuousOpenMap.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(余ntinuousOpen映射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(ContinuousOpenMap.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: ContinuousOpenMap.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 余ntinuousOpen映射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : ContinuousOpenMap.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->CO γ) (g : α ->CO β)
  body: ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩

@[simp]

中文:
定义 comp
  签名: (f : β ->CO γ) (g : α ->CO β)
  定义体: ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩

@[simp]

Depends on / 依赖: f.map_open, f.toContinuousMap.comp, g.map_open, g.toContinuousMap, map_open, toContinuousMap
-/
def comp (f : β ->CO γ) (g : α ->CO β) : ContinuousOpenMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : β ->CO γ) (g : α ->CO β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : β ->CO γ) (g : α ->CO β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : β ->CO γ) (g : α ->CO β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : β ->CO γ) (g : α ->CO β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : β ->CO γ) (g : α ->CO β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : β ->CO γ) (g : α ->CO β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->CO δ) (g : β ->CO γ) (h : α ->CO β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : γ ->CO δ) (g : β ->CO γ) (h : α ->CO β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : γ ->CO δ) (g : β ->CO γ) (h : α ->CO β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->CO β)
  statement: f.comp (ContinuousOpenMap.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->CO β)
  结论: f.comp (余ntinuousOpen映射.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : α ->CO β) : f.comp (ContinuousOpenMap.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->CO β)
  statement: (ContinuousOpenMap.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : α ->CO β)
  结论: (余ntinuousOpen映射.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : α ->CO β) : (ContinuousOpenMap.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->CO γ} {f : α ->CO β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->CO γ} {f : α ->CO β} (hf : 满射 f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->CO γ} {f : α ->CO β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->CO γ} {f₁ f₂ : α ->CO β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : β ->CO γ} {f₁ f₂ : α ->CO β} (hg : 单射 g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : β ->CO γ} {f₁ f₂ : α ->CO β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end ContinuousOpenMap
