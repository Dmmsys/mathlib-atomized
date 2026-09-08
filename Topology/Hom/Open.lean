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

/-- The type of continuous open maps from `α` to `β`, aka Priestley homomorphisms. -/
/-
**ContinuousOpenMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [TopologicalSpace α] → [TopologicalSpace
 β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous open maps from `α` to `β`, aka Priestley homomorphisms.
-/
structure ContinuousOpenMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β where
  map_open' : IsOpenMap toFun

@[inherit_doc] infixr:25 " →CO " => ContinuousOpenMap

section

/-- `ContinuousOpenMapClass F α β` states that `F` is a type of continuous open maps.

You should extend this class when you extend `ContinuousOpenMap`. -/
/-
**ContinuousOpenMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) →   (α : outParam (Type u_7)) →     (β : outParam (Type u_8
)) → [TopologicalSpace α] → [TopologicalSpace β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousOpenMapClass F α β` states that `F` is a type of continuous open maps
.

You should extend this class when you extend `ContinuousOpenMap`.
-/
class ContinuousOpenMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  [TopologicalSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  map_open (f : F) : IsOpenMap f

end

export ContinuousOpenMapClass (map_open)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
    [ContinuousOpenMapClass F α β] :
    CoeTC F (α →CO β) :=
  ⟨fun f => ⟨f, map_open f⟩⟩

/-! ### Continuous open maps -/


namespace ContinuousOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-
**ContinuousOpenMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOpenMap`。
形式化陈述：instFunLike : FunLike (α ->CO β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (α →CO β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**ContinuousOpenMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOpenMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousOpenMapClass (α →CO β) α β where
  map_continuous f := f.continuous_toFun
  map_open f := f.map_open'
/-
**ContinuousOpenMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：toFun_eq_coe {f : α ->CO β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : α →CO β} : f.toFun = (f : α → β) :=
  rfl

/-- `simp`-normal form of `toFun_eq_coe`. -/
@[simp]
/-
**ContinuousOpenMap.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpe
nMap`。
形式化陈述：coe_toContinuousMap (f : α ->CO β) : (f.toContinuousMap : α -> β) = f
参数：f : α ->CO β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`simp`-normal form of `toFun_eq_coe`.
-/
theorem coe_toContinuousMap (f : α →CO β) : (f.toContinuousMap : α → β) = f := rfl

@[ext]
/-
**ContinuousOpenMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：ext {f g : α ->CO β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `ContinuousOpenMap` with a new `ContinuousMap` equal to the old one. Useful to fix
definitional equalities. -/
/-
**ContinuousOpenMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOpenMap`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : TopologicalSpace α] → [ins
t_1 : TopologicalSpace β] → (f : α →CO β) → (f' : α → β) → f' = ⇑f → α →CO β
参数：f : α →CO β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ContinuousOpenMap` with a new `ContinuousMap` equal to the old one. U
seful to fix
definitional equalities.
-/
protected def copy (f : α →CO β) (f' : α → β) (h : f' = f) : α →CO β :=
  ⟨f.toContinuousMap.copy f' <| h, h.symm.subst f.map_open'⟩

@[simp]
/-
**ContinuousOpenMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：coe_copy (f : α ->CO β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->CO β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →CO β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**ContinuousOpenMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：copy_eq (f : α ->CO β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->CO β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →CO β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `ContinuousOpenMap`. -/
/-
**ContinuousOpenMap.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOpenMap`。
形式化陈述：(α : Type u_2) → [inst : TopologicalSpace α] → α →CO α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id

--- 原说明 ---
`id` as a `ContinuousOpenMap`.
-/
protected def id : α →CO α :=
  ⟨ContinuousMap.id _, IsOpenMap.id⟩
/-
**ContinuousOpenMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOpenMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →CO α) :=
  ⟨ContinuousOpenMap.id _⟩

@[simp, norm_cast]
/-
**ContinuousOpenMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：coe_id : ⇑(ContinuousOpenMap.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(ContinuousOpenMap.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**ContinuousOpenMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：id_apply (a : α) : ContinuousOpenMap.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : ContinuousOpenMap.id α a = a :=
  rfl

/-- Composition of `ContinuousOpenMap`s as a `ContinuousOpenMap`. -/
/-
**ContinuousOpenMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOpenMap`。
形式化陈述：comp (f : β ->CO γ) (g : α ->CO β) : ContinuousOpenMap α γ
参数：f : β ->CO γ；g : α ->CO β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `ContinuousOpenMap`s as a `ContinuousOpenMap`.
-/
def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩

@[simp]
/-
**ContinuousOpenMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：coe_comp (f : β ->CO γ) (g : α ->CO β) : (f.comp g : α -> γ) = f ∘ g
参数：f : β ->CO γ；g : α ->CO β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : β →CO γ) (g : α →CO β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**ContinuousOpenMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：comp_apply (f : β ->CO γ) (g : α ->CO β) (a : α) : (f.comp g) a = f (g a)
参数：f : β ->CO γ；g : α ->CO β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
/-
**ContinuousOpenMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：comp_assoc (f : γ ->CO δ) (g : β ->CO γ) (h : α ->CO β) : (f.comp g).comp 
h = f.comp (g.comp h)
参数：f : γ ->CO δ；g : β ->CO γ；h : α ->CO β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →CO δ) (g : β →CO γ) (h : α →CO β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**ContinuousOpenMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：comp_id (f : α ->CO β) : f.comp (ContinuousOpenMap.id α) = f
参数：f : α ->CO β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOpenMap.ext`：ext {f g : α ->CO β} (h : forall a, f a = g a) : 
f = g
-/
theorem comp_id (f : α →CO β) : f.comp (ContinuousOpenMap.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousOpenMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：id_comp (f : α ->CO β) : (ContinuousOpenMap.id β).comp f = f
参数：f : α ->CO β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOpenMap.ext`：ext {f g : α ->CO β} (h : forall a, f a = g a) : 
f = g
-/
theorem id_comp (f : α →CO β) : (ContinuousOpenMap.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousOpenMap.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：cancel_right {g₁ g₂ : β ->CO γ} {f : α ->CO β} (hf : Surjective f) : g₁.co
mp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOpenMap.ext`：ext {f g : α ->CO β} (h : forall a, f a = g a) : 
f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem cancel_right {g₁ g₂ : β →CO γ} {f : α →CO β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
/-
**ContinuousOpenMap.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOpenMap`。
形式化陈述：cancel_left {g : β ->CO γ} {f₁ f₂ : α ->CO β} (hg : Injective g) : g.comp 
f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOpenMap.ext`：ext {f g : α ->CO β} (h : forall a, f a = g a) : 
f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOpenMap.comp_apply`：comp_apply (f : β ->CO γ) (g : α ->CO β) (
a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : β →CO γ} {f₁ f₂ : α →CO β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end ContinuousOpenMap

