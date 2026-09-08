/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Continuous order homomorphisms

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `ContinuousOrderHom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `ContinuousOrderHomClass`
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/-- The type of continuous monotone maps from `α` to `β`, aka Priestley homomorphisms. -/
/-
**ContinuousOrderHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) →   (β : Type u_7) → [Preorder α] → [Preorder β] → [Topolog
icalSpace α] → [TopologicalSpace β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous monotone maps from `α` to `β`, aka Priestley homomorphism
s.
-/
structure ContinuousOrderHom (α β : Type*) [Preorder α] [Preorder β] [TopologicalSpace α]
  [TopologicalSpace β] extends OrderHom α β where
  continuous_toFun : Continuous toFun

@[inherit_doc] infixr:25 " →Co " => ContinuousOrderHom

section

/-- `ContinuousOrderHomClass F α β` states that `F` is a type of continuous monotone maps.

You should extend this class when you extend `ContinuousOrderHom`. -/
/-
**ContinuousOrderHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) →   (α : outParam (Type u_7)) →     (β : outParam (Type u_8
)) →       [Preorder α] → [Preorder β] → [TopologicalSpace α] → [TopologicalSpac
e β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousOrderHomClass F α β` states that `F` is a type of continuous monotone
 maps.

You should extend this class when you extend `ContinuousOrderHom`.
-/
class ContinuousOrderHomClass (F : Type*) (α β : outParam Type*) [Preorder α] [Preorder β]
    [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β] : Prop
    extends ContinuousMapClass F α β where
  map_monotone (f : F) : Monotone f

namespace ContinuousOrderHomClass

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [FunLike F α β] [ContinuousOrderHomClass F α β]

-- See note [lower instance priority]
/-
**ContinuousOrderHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toOrderHomClass :
    OrderHomClass F α β :=
  { ‹ContinuousOrderHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }

/-- Turn an element of a type `F` satisfying `ContinuousOrderHomClass F α β` into an actual
`ContinuousOrderHom`. This is declared as the default coercion from `F` to `α →Co β`. -/
@[coe]
/-
**ContinuousOrderHomClass.toContinuousOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousOrderHomClass`。
形式化陈述：toContinuousOrderHom (f : F) : α ->Co β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOrderHomClass.map_monotone`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preorder β}   {
inst_2 : TopologicalSpace …

--- 原说明 ---
Turn an element of a type `F` satisfying `ContinuousOrderHomClass F α β` into an
 actual
`ContinuousOrderHom`. This is declared as the default coercion from `F` to `α →C
o β`.
-/
def toContinuousOrderHom (f : F) : α →Co β :=
    { toFun := f
      monotone' := ContinuousOrderHomClass.map_monotone f
      continuous_toFun := map_continuous f }
/-
**ContinuousOrderHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC F (α →Co β) :=
  ⟨toContinuousOrderHom⟩

end ContinuousOrderHomClass
/-! ### Top homomorphisms -/


namespace ContinuousOrderHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β]

section Preorder

variable [Preorder β] [TopologicalSpace γ] [Preorder γ] [TopologicalSpace δ] [Preorder δ]

/-- Reinterpret a `ContinuousOrderHom` as a `ContinuousMap`. -/
/-
**ContinuousOrderHom.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOrderH
om`。
形式化陈述：toContinuousMap (f : α ->Co β) : C(α, β)
参数：f : α ->Co β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOrderHom.continuous_toFun`：∀ {α : Type u_6} {β : Type u_7} [in
st : Preorder α] [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 :
 TopologicalSpace β] (sel…

--- 原说明 ---
Reinterpret a `ContinuousOrderHom` as a `ContinuousMap`.
-/
def toContinuousMap (f : α →Co β) : C(α, β) :=
  { f with }
/-
**ContinuousOrderHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHom`。
形式化陈述：instFunLike : FunLike (α ->Co β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (α →Co β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**ContinuousOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousOrderHomClass (α →Co β) α β where
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun
/-
**ContinuousOrderHom.coe_toOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHo
m`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Preo
rder α] [inst_2 : TopologicalSpace β]   [inst_3 : Preorder β] (f : α →Co β), ⇑f.
toOrderHom = ⇑f
参数：f : α →Co β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toOrderHom (f : α →Co β) : ⇑f.toOrderHom = f := rfl
/-
**ContinuousOrderHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`
。
形式化陈述：toFun_eq_coe {f : α ->Co β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : α →Co β} : f.toFun = (f : α → β) := rfl

@[ext]
/-
**ContinuousOrderHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：ext {f g : α ->Co β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `ContinuousOrderHom` with a new `ContinuousMap` equal to the old one. Useful to fix
definitional equalities. -/
/-
**ContinuousOrderHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOrderHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : TopologicalSpace α] →     
  [inst_1 : Preorder α] →         [inst_2 : TopologicalSpace β] → [inst_3 : Preo
rder β] → (f : α →Co β) → (f' : α → β) → f' = ⇑f → α →Co β
参数：f : α →Co β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ContinuousOrderHom` with a new `ContinuousMap` equal to the old one. 
Useful to fix
definitional equalities.
-/
protected def copy (f : α →Co β) (f' : α → β) (h : f' = f) : α →Co β :=
  ⟨f.toOrderHom.copy f' h, h.symm.subst f.continuous_toFun⟩

@[simp]
/-
**ContinuousOrderHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：coe_copy (f : α ->Co β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->Co β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →Co β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**ContinuousOrderHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：copy_eq (f : α ->Co β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->Co β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →Co β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `ContinuousOrderHom`. -/
/-
**ContinuousOrderHom.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOrderHom`。
形式化陈述：(α : Type u_2) → [inst : TopologicalSpace α] → [inst_1 : Preorder α] → α →
Co α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
`id` as a `ContinuousOrderHom`.
-/
protected def id : α →Co α :=
  ⟨OrderHom.id, continuous_id⟩
/-
**ContinuousOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →Co α) :=
  ⟨ContinuousOrderHom.id _⟩

@[simp, norm_cast]
/-
**ContinuousOrderHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：coe_id : ⇑(ContinuousOrderHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(ContinuousOrderHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**ContinuousOrderHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：id_apply (a : α) : ContinuousOrderHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : ContinuousOrderHom.id α a = a :=
  rfl

/-- Composition of `ContinuousOrderHom`s as a `ContinuousOrderHom`. -/
/-
**ContinuousOrderHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousOrderHom`。
形式化陈述：comp (f : β ->Co γ) (g : α ->Co β) : ContinuousOrderHom α γ
参数：f : β ->Co γ；g : α ->Co β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `ContinuousOrderHom`s as a `ContinuousOrderHom`.
-/
def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
  ⟨f.toOrderHom.comp g.toOrderHom, f.continuous_toFun.comp g.continuous_toFun⟩

@[simp]
/-
**ContinuousOrderHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：coe_comp (f : β ->Co γ) (g : α ->Co β) : (f.comp g : α -> γ) = f ∘ g
参数：f : β ->Co γ；g : α ->Co β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : β →Co γ) (g : α →Co β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**ContinuousOrderHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：comp_apply (f : β ->Co γ) (g : α ->Co β) (a : α) : (f.comp g) a = f (g a)
参数：f : β ->Co γ；g : α ->Co β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
/-
**ContinuousOrderHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：comp_assoc (f : γ ->Co δ) (g : β ->Co γ) (h : α ->Co β) : (f.comp g).comp 
h = f.comp (g.comp h)
参数：f : γ ->Co δ；g : β ->Co γ；h : α ->Co β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →Co δ) (g : β →Co γ) (h : α →Co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**ContinuousOrderHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：comp_id (f : α ->Co β) : f.comp (ContinuousOrderHom.id α) = f
参数：f : α ->Co β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOrderHom.ext`：ext {f g : α ->Co β} (h : forall a, f a = g a) :
 f = g
-/
theorem comp_id (f : α →Co β) : f.comp (ContinuousOrderHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousOrderHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：id_comp (f : α ->Co β) : (ContinuousOrderHom.id β).comp f = f
参数：f : α ->Co β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOrderHom.ext`：ext {f g : α ->Co β} (h : forall a, f a = g a) :
 f = g
-/
theorem id_comp (f : α →Co β) : (ContinuousOrderHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousOrderHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`
。
形式化陈述：cancel_right {g₁ g₂ : β ->Co γ} {f : α ->Co β} (hf : Surjective f) : g₁.co
mp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOrderHom.ext`：ext {f g : α ->Co β} (h : forall a, f a = g a) :
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
theorem cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
/-
**ContinuousOrderHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOrderHom`。
形式化陈述：cancel_left {g : β ->Co γ} {f₁ f₂ : α ->Co β} (hg : Injective g) : g.comp 
f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOrderHom.ext`：ext {f g : α ->Co β} (h : forall a, f a = g a) :
 f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOrderHom.comp_apply`：comp_apply (f : β ->Co γ) (g : α ->Co β) 
(a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
/-
**ContinuousOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (α →Co β) :=
  Preorder.lift ((↑) : (α →Co β) → α → β)

end Preorder

/-
**ContinuousOrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousOrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder β] : PartialOrder (α →Co β) :=
  PartialOrder.lift ((↑) : (α →Co β) → α → β) DFunLike.coe_injective

end ContinuousOrderHom

end

