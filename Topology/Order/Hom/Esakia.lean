/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.Bounded
public import Mathlib.Topology.Order.Hom.Basic

/-!
# Esakia morphisms

This file defines pseudo-epimorphisms and Esakia morphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `PseudoEpimorphism`: Pseudo-epimorphisms. Maps `f` such that `f a ≤ b` implies the existence of
  `a'` such that `a ≤ a'` and `f a' = b`.
* `EsakiaHom`: Esakia morphisms. Continuous pseudo-epimorphisms.

## Typeclasses

* `PseudoEpimorphismClass`
* `EsakiaHomClass`

## References

* [Wikipedia, *Esakia space*](https://en.wikipedia.org/wiki/Esakia_space)
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/-- The type of pseudo-epimorphisms, aka p-morphisms, aka bounded maps, from `α` to `β`. -/
/-
**PseudoEpimorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Preorder α] → [Preorder β] → Type (max 
u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of pseudo-epimorphisms, aka p-morphisms, aka bounded maps, from `α` to 
`β`.
-/
structure PseudoEpimorphism (α β : Type*) [Preorder α] [Preorder β] extends α →o β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b

/-- The type of Esakia morphisms, aka continuous pseudo-epimorphisms, from `α` to `β`. -/
/-
**EsakiaHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) →   (β : Type u_7) → [TopologicalSpace α] → [Preorder α] → 
[TopologicalSpace β] → [Preorder β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Esakia morphisms, aka continuous pseudo-epimorphisms, from `α` to `β
`.
-/
structure EsakiaHom (α β : Type*) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  [Preorder β] extends α →Co β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a ≤ b → ∃ c, a ≤ c ∧ toFun c = b

section

/-- `PseudoEpimorphismClass F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `PseudoEpimorphism`. -/
/-
**PseudoEpimorphismClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) →   (α : outParam (Type u_7)) → (β : outParam (Type u_8)) →
 [Preorder α] → [Preorder β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PseudoEpimorphismClass F α β` states that `F` is a type of `⊔`-preserving morph
isms.

You should extend this class when you extend `PseudoEpimorphism`.
-/
class PseudoEpimorphismClass (F : Type*) (α β : outParam Type*)
    [Preorder α] [Preorder β] [FunLike F α β] : Prop
    extends OrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b

/-- `EsakiaHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `EsakiaHom`. -/
/-
**EsakiaHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) →   (α : outParam (Type u_7)) →     (β : outParam (Type u_8
)) →       [TopologicalSpace α] → [Preorder α] → [TopologicalSpace β] → [Preorde
r β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EsakiaHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `EsakiaHom`.
-/
class EsakiaHomClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [FunLike F α β] : Prop
    extends ContinuousOrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b

end

export PseudoEpimorphismClass (exists_map_eq_of_map_le)

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PseudoEpimorphismClass.toTopHomClass [PartialOrder α] [OrderTop α]
    [Preorder β] [OrderTop β] [PseudoEpimorphismClass F α β] : TopHomClass F α β where
  map_top f := by
    let ⟨b, h⟩ := exists_map_eq_of_map_le f (@le_top _ _ _ <| f ⊤)
    rw [← top_le_iff.1 h.1, h.2]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) EsakiaHomClass.toPseudoEpimorphismClass [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [EsakiaHomClass F α β] : PseudoEpimorphismClass F α β :=
  { ‹EsakiaHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [Preorder β] [PseudoEpimorphismClass F α β] :
    CoeTC F (PseudoEpimorphism α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β]
    [EsakiaHomClass F α β] : CoeTC F (EsakiaHom α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

end Hom

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toPseudoEpimorphismClass [Preorder α] [Preorder β]
    [EquivLike F α β] [OrderIsoClass F α β] : PseudoEpimorphismClass F α β where
  exists_map_eq_of_map_le f _a b h :=
    ⟨EquivLike.inv f b, (le_map_inv_iff f).2 h, EquivLike.right_inv _ _⟩

/-! ### Pseudo-epimorphisms -/


namespace PseudoEpimorphism

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/-
**PseudoEpimorphism.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `PseudoEpimorphism`。
形式化陈述：instFunLike : FunLike (PseudoEpimorphism α β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (PseudoEpimorphism α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**PseudoEpimorphism.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoEpimorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoEpimorphismClass (PseudoEpimorphism α β) α β where
  map_rel f _ _ h := f.monotone' h
  exists_map_eq_of_map_le := PseudoEpimorphism.exists_map_eq_of_map_le'

@[simp]
/-
**PseudoEpimorphism.toOrderHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphi
sm`。
形式化陈述：toOrderHom_eq_coe (f : PseudoEpimorphism α β) : ⇑f.toOrderHom = f
参数：f : PseudoEpimorphism α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderHom_eq_coe (f : PseudoEpimorphism α β) : ⇑f.toOrderHom = f := rfl
/-
**PseudoEpimorphism.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：toFun_eq_coe {f : PseudoEpimorphism α β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : PseudoEpimorphism α β} : f.toFun = (f : α → β) := rfl

@[ext]
/-
**PseudoEpimorphism.ext** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：ext {f g : PseudoEpimorphism α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : PseudoEpimorphism α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `PseudoEpimorphism` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**PseudoEpimorphism.copy** 是 Mathlib 中的一个定义，位于命名空间 `PseudoEpimorphism`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Preorder α] →       [inst_
1 : Preorder β] → (f : PseudoEpimorphism α β) → (f' : α → β) → f' = ⇑f → PseudoE
pimorphism α β
参数：f : PseudoEpimorphism α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `PseudoEpimorphism` with a new `toFun` equal to the old one. Useful to
 fix
definitional equalities.
-/
protected def copy (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : PseudoEpimorphism α β :=
  ⟨f.toOrderHom.copy f' h, by simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]
/-
**PseudoEpimorphism.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：coe_copy (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy
 f' h) = f'
参数：f : PseudoEpimorphism α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
/-
**PseudoEpimorphism.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：copy_eq (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f) : f.copy f'
 h = f
参数：f : PseudoEpimorphism α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : PseudoEpimorphism α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `PseudoEpimorphism`. -/
/-
**PseudoEpimorphism.id** 是 Mathlib 中的一个定义，位于命名空间 `PseudoEpimorphism`。
形式化陈述：(α : Type u_2) → [inst : Preorder α] → PseudoEpimorphism α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `PseudoEpimorphism`.
-/
protected def id : PseudoEpimorphism α α :=
  ⟨OrderHom.id, fun _ b h => ⟨b, h, rfl⟩⟩
/-
**PseudoEpimorphism.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoEpimorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (PseudoEpimorphism α α) :=
  ⟨PseudoEpimorphism.id α⟩

@[simp, norm_cast]
/-
**PseudoEpimorphism.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：coe_id : ⇑(PseudoEpimorphism.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(PseudoEpimorphism.id α) = id := rfl

@[simp, norm_cast]
/-
**PseudoEpimorphism.coe_id_orderHom** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism
`。
形式化陈述：coe_id_orderHom : (PseudoEpimorphism.id α : α ->o α) = OrderHom.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphismClass.toRelHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preorder β}   {
inst_2 : FunLike F α β} [s…
· 使用定理 `PseudoEpimorphism.instPseudoEpimorphismClass`：∀ {α : Type u_2} {β : Type
 u_3} [inst : Preorder α] [inst_1 : Preorder β],   PseudoEpimorphismClass (Pseud
oEpimorphism α β) α β
-/
theorem coe_id_orderHom : (PseudoEpimorphism.id α : α →o α) = OrderHom.id := rfl

variable {α}

@[simp]
/-
**PseudoEpimorphism.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：id_apply (a : α) : PseudoEpimorphism.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : PseudoEpimorphism.id α a = a := rfl

/-- Composition of `PseudoEpimorphism`s as a `PseudoEpimorphism`. -/
/-
**PseudoEpimorphism.comp** 是 Mathlib 中的一个定义，位于命名空间 `PseudoEpimorphism`。
形式化陈述：comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimo
rphism α γ
参数：g : PseudoEpimorphism β γ；f : PseudoEpimorphism α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `PseudoEpimorphism`s as a `PseudoEpimorphism`.
-/
def comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimorphism α γ :=
  ⟨g.toOrderHom.comp f.toOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]
/-
**PseudoEpimorphism.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：coe_comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : (g.comp
 f : α -> γ) = g ∘ f
参数：g : PseudoEpimorphism β γ；f : PseudoEpimorphism α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α → γ) = g ∘ f := rfl

@[simp]
/-
**PseudoEpimorphism.coe_comp_orderHom** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphi
sm`。
形式化陈述：coe_comp_orderHom (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) 
: (g.comp f : α ->o γ) = (g : β ->o γ).comp f
参数：g : PseudoEpimorphism β γ；f : PseudoEpimorphism α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphismClass.toRelHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preorder β}   {
inst_2 : FunLike F α β} [s…
· 使用定理 `PseudoEpimorphism.instPseudoEpimorphismClass`：∀ {α : Type u_2} {β : Type
 u_3} [inst : Preorder α] [inst_1 : Preorder β],   PseudoEpimorphismClass (Pseud
oEpimorphism α β) α β
-/
theorem coe_comp_orderHom (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α →o γ) = (g : β →o γ).comp f := rfl

@[simp]
/-
**PseudoEpimorphism.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：comp_apply (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α)
 : (g.comp f) a = g (f a)
参数：g : PseudoEpimorphism β γ；f : PseudoEpimorphism α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α) :
    (g.comp f) a = g (f a) := rfl

@[simp]
/-
**PseudoEpimorphism.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：comp_assoc (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ) (f : Ps
eudoEpimorphism α β) : (h.comp g).comp f = h.comp (g.comp f)
参数：h : PseudoEpimorphism γ δ；g : PseudoEpimorphism β γ；f : PseudoEpimorphism α β
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ)
    (f : PseudoEpimorphism α β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp]
/-
**PseudoEpimorphism.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：comp_id (f : PseudoEpimorphism α β) : f.comp (PseudoEpimorphism.id α) = f
参数：f : PseudoEpimorphism α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphism.ext`：ext {f g : PseudoEpimorphism α β} (h : forall a, 
f a = g a) : f = g
-/
theorem comp_id (f : PseudoEpimorphism α β) : f.comp (PseudoEpimorphism.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**PseudoEpimorphism.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：id_comp (f : PseudoEpimorphism α β) : (PseudoEpimorphism.id β).comp f = f
参数：f : PseudoEpimorphism α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphism.ext`：ext {f g : PseudoEpimorphism α β} (h : forall a, 
f a = g a) : f = g
-/
theorem id_comp (f : PseudoEpimorphism α β) : (PseudoEpimorphism.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**PseudoEpimorphism.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：cancel_right {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β} (
hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphism.ext`：ext {f g : PseudoEpimorphism α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]
/-
**PseudoEpimorphism.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEpimorphism`。
形式化陈述：cancel_left {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (h
g : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphism.ext`：ext {f g : PseudoEpimorphism α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PseudoEpimorphism.comp_apply`：comp_apply (g : PseudoEpimorphism β γ) (f 
: PseudoEpimorphism α β) (a : α) : (g.comp f) a = g (f a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end PseudoEpimorphism

/-! ### Esakia morphisms -/


namespace EsakiaHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β] [TopologicalSpace γ]
  [Preorder γ] [TopologicalSpace δ] [Preorder δ]

/-
**EsakiaHom.toPseudoEpimorphism** 是 Mathlib 中的一个定义，位于命名空间 `EsakiaHom`。
形式化陈述：toPseudoEpimorphism (f : EsakiaHom α β) : PseudoEpimorphism α β
参数：f : EsakiaHom α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHom.exists_map_eq_of_map_le'`：∀ {α : Type u_6} {β : Type u_7} [ins
t : TopologicalSpace α] [inst_1 : Preorder α] [inst_2 : TopologicalSpace β]   [i
nst_3 : Preorder β] (sel…
-/
def toPseudoEpimorphism (f : EsakiaHom α β) : PseudoEpimorphism α β :=
  { f with }
/-
**EsakiaHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `EsakiaHom`。
形式化陈述：instFunLike : FunLike (EsakiaHom α β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (EsakiaHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
/-
**EsakiaHom.** 是 Mathlib 中的一个实例，位于命名空间 `EsakiaHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EsakiaHomClass (EsakiaHom α β) α β where
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun
  exists_map_eq_of_map_le f := f.exists_map_eq_of_map_le'

@[simp]
/-
**EsakiaHom.toContinuousOrderHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：toContinuousOrderHom_coe {f : EsakiaHom α β} : f.toContinuousOrderHom = (f
 : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousOrderHom_coe {f : EsakiaHom α β} :
    f.toContinuousOrderHom = (f : α → β) := rfl
/-
**EsakiaHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：toFun_eq_coe {f : EsakiaHom α β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : EsakiaHom α β} : f.toFun = (f : α → β) := rfl

@[ext]
/-
**EsakiaHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：ext {f g : EsakiaHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : EsakiaHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of an `EsakiaHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**EsakiaHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `EsakiaHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : TopologicalSpace α] →     
  [inst_1 : Preorder α] →         [inst_2 : TopologicalSpace β] →           [ins
t_3 : Preorder β] → (f : EsakiaHom α β) → (f' : α → β) → f' = ⇑f → EsakiaHom α β
参数：f : EsakiaHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an `EsakiaHom` with a new `toFun` equal to the old one. Useful to fix de
finitional
equalities.
-/
protected def copy (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : EsakiaHom α β :=
  ⟨f.toContinuousOrderHom.copy f' h, by
    simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]
/-
**EsakiaHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_copy (f : EsakiaHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) =
 f'
参数：f : EsakiaHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
/-
**EsakiaHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：copy_eq (f : EsakiaHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : EsakiaHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : EsakiaHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as an `EsakiaHom`. -/
/-
**EsakiaHom.id** 是 Mathlib 中的一个定义，位于命名空间 `EsakiaHom`。
形式化陈述：(α : Type u_2) → [inst : TopologicalSpace α] → [inst_1 : Preorder α] → Esa
kiaHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as an `EsakiaHom`.
-/
protected def id : EsakiaHom α α :=
  ⟨ContinuousOrderHom.id α, fun _ b h => ⟨b, h, rfl⟩⟩
/-
**EsakiaHom.** 是 Mathlib 中的一个实例，位于命名空间 `EsakiaHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (EsakiaHom α α) :=
  ⟨EsakiaHom.id α⟩

@[simp, norm_cast]
/-
**EsakiaHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_id : ⇑(EsakiaHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(EsakiaHom.id α) = id := rfl

@[simp, norm_cast]
/-
**EsakiaHom.coe_id_pseudoEpimorphism** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_id_pseudoEpimorphism : (EsakiaHom.id α : PseudoEpimorphism α α) = Pseu
doEpimorphism.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphismClass.toRelHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preorder β}   {
inst_2 : FunLike F α β} [s…
· 使用定理 `EsakiaHomClass.toPseudoEpimorphismClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : TopologicalSpace α]   [inst_2 :
 Preorder α] [inst_3 : Topolo…
· 使用定理 `EsakiaHom.instEsakiaHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : To
pologicalSpace α] [inst_1 : Preorder α] [inst_2 : TopologicalSpace β]   [inst_3 
: Preorder β], Esa…
· 使用定理 `PseudoEpimorphismClass.exists_map_eq_of_map_le`：∀ {F : Type u_6} {α : ou
tParam (Type u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preor
der β}   {inst_2 : FunLike F α β} [s…
-/
theorem coe_id_pseudoEpimorphism :
    (EsakiaHom.id α : PseudoEpimorphism α α) = PseudoEpimorphism.id α := rfl

variable {α}

@[simp]
/-
**EsakiaHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：id_apply (a : α) : EsakiaHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : EsakiaHom.id α a = a := rfl

@[simp, norm_cast]
/-
**EsakiaHom.coe_id_continuousOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_id_continuousOrderHom : (EsakiaHom.id α : α ->Co α) = ContinuousOrderH
om.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHomClass.toContinuousOrderHomClass`：∀ {F : Type u_6} {α : outParam
 (Type u_7)} {β : outParam (Type u_8)} {inst : TopologicalSpace α} {inst_1 : Pre
order α}   {inst_2 : Topologic…
· 使用定理 `EsakiaHom.instEsakiaHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : To
pologicalSpace α] [inst_1 : Preorder α] [inst_2 : TopologicalSpace β]   [inst_3 
: Preorder β], Esa…
-/
theorem coe_id_continuousOrderHom : (EsakiaHom.id α : α →Co α) = ContinuousOrderHom.id α := rfl

/-- Composition of `EsakiaHom`s as an `EsakiaHom`. -/
/-
**EsakiaHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `EsakiaHom`。
形式化陈述：comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ
参数：g : EsakiaHom β γ；f : EsakiaHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `EsakiaHom`s as an `EsakiaHom`.
-/
def comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ :=
  ⟨g.toContinuousOrderHom.comp f.toContinuousOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]
/-
**EsakiaHom.coe_comp_continuousOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_comp_continuousOrderHom (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.c
omp f : α ->Co γ) = (g : β ->Co γ).comp f
参数：g : EsakiaHom β γ；f : EsakiaHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHomClass.toContinuousOrderHomClass`：∀ {F : Type u_6} {α : outParam
 (Type u_7)} {β : outParam (Type u_8)} {inst : TopologicalSpace α} {inst_1 : Pre
order α}   {inst_2 : Topologic…
· 使用定理 `EsakiaHom.instEsakiaHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : To
pologicalSpace α] [inst_1 : Preorder α] [inst_2 : TopologicalSpace β]   [inst_3 
: Preorder β], Esa…
-/
theorem coe_comp_continuousOrderHom (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : α →Co γ) = (g : β →Co γ).comp f := rfl

@[simp]
/-
**EsakiaHom.coe_comp_pseudoEpimorphism** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_comp_pseudoEpimorphism (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.co
mp f : PseudoEpimorphism α γ) = (g : PseudoEpimorphism β γ).comp f
参数：g : EsakiaHom β γ；f : EsakiaHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEpimorphismClass.toRelHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preorder β}   {
inst_2 : FunLike F α β} [s…
· 使用定理 `EsakiaHomClass.toPseudoEpimorphismClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : TopologicalSpace α]   [inst_2 :
 Preorder α] [inst_3 : Topolo…
· 使用定理 `EsakiaHom.instEsakiaHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : To
pologicalSpace α] [inst_1 : Preorder α] [inst_2 : TopologicalSpace β]   [inst_3 
: Preorder β], Esa…
· 使用定理 `PseudoEpimorphismClass.exists_map_eq_of_map_le`：∀ {F : Type u_6} {α : ou
tParam (Type u_7)} {β : outParam (Type u_8)} {inst : Preorder α} {inst_1 : Preor
der β}   {inst_2 : FunLike F α β} [s…
-/
theorem coe_comp_pseudoEpimorphism (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : PseudoEpimorphism α γ) = (g : PseudoEpimorphism β γ).comp f := rfl

@[simp]
/-
**EsakiaHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：coe_comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.comp f : α -> γ) = g
 ∘ f
参数：g : EsakiaHom β γ；f : EsakiaHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.comp f : α → γ) = g ∘ f := rfl

@[simp]
/-
**EsakiaHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α) : (g.comp f) a 
= g (f a)
参数：g : EsakiaHom β γ；f : EsakiaHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α) : (g.comp f) a = g (f a) := rfl

@[simp]
/-
**EsakiaHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：comp_assoc (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β) : (
h.comp g).comp f = h.comp (g.comp f)
参数：h : EsakiaHom γ δ；g : EsakiaHom β γ；f : EsakiaHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp]
/-
**EsakiaHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：comp_id (f : EsakiaHom α β) : f.comp (EsakiaHom.id α) = f
参数：f : EsakiaHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHom.ext`：ext {f g : EsakiaHom α β} (h : forall a, f a = g a) : f =
 g
-/
theorem comp_id (f : EsakiaHom α β) : f.comp (EsakiaHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**EsakiaHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：id_comp (f : EsakiaHom α β) : (EsakiaHom.id β).comp f = f
参数：f : EsakiaHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHom.ext`：ext {f g : EsakiaHom α β} (h : forall a, f a = g a) : f =
 g
-/
theorem id_comp (f : EsakiaHom α β) : (EsakiaHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**EsakiaHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：cancel_right {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective 
f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHom.ext`：ext {f g : EsakiaHom α β} (h : forall a, f a = g a) : f =
 g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]
/-
**EsakiaHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `EsakiaHom`。
形式化陈述：cancel_left {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g)
 : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EsakiaHom.ext`：ext {f g : EsakiaHom α β} (h : forall a, f a = g a) : f =
 g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EsakiaHom.comp_apply`：comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β)
 (a : α) : (g.comp f) a = g (f a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end EsakiaHom

