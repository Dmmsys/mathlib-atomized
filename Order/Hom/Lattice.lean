/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Unbounded lattice homomorphisms

This file defines unbounded lattice homomorphisms. _Bounded_ lattice homomorphisms are defined in
`Mathlib/Order/Hom/BoundedLattice.lean`.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupHom`: Maps which preserve `⊔`.
* `InfHom`: Maps which preserve `⊓`.
* `LatticeHom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.

## Typeclasses

* `SupHomClass`
* `InfHomClass`
* `LatticeHomClass`
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
/-
**SupHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Max α] → [Max β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `⊔`-preserving functions from `α` to `β`.
-/
structure SupHom (α β : Type*) [Max α] [Max β] where
  /-- The underlying function of a `SupHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → β
  /-- A `SupHom` preserves suprema.

  Do not use this directly. Use `map_sup` instead. -/
  map_sup' (a b : α) : toFun (a ⊔ b) = toFun a ⊔ toFun b

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
@[to_dual existing]
/-
**InfHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Min α] → [Min β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `⊓`-preserving functions from `α` to `β`.
-/
structure InfHom (α β : Type*) [Min α] [Min β] where
  /-- The underlying function of an `InfHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → β
  /-- An `InfHom` preserves infima.

  Do not use this directly. Use `map_inf` instead. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

/-- The type of lattice homomorphisms from `α` to `β`. -/
/-
**LatticeHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Lattice α] → [Lattice β] → Type (max u_
6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of lattice homomorphisms from `α` to `β`.
-/
structure LatticeHom (α β : Type*) [Lattice α] [Lattice β] extends SupHom α β, InfHom α β where

attribute [nolint docBlame] LatticeHom.toInfHom

attribute [to_dual existing] LatticeHom.toInfHom

section

/-- `SupHomClass F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `SupHom`. -/
/-
**SupHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [Max α] → [Max β] → [Fu
nLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SupHomClass F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `SupHom`.
-/
class SupHomClass (F α β : Type*) [Max α] [Max β] [FunLike F α β] : Prop where
  /-- A `SupHomClass` morphism preserves suprema. -/
  map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b

/-- `InfHomClass F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `InfHom`. -/
@[to_dual existing]
/-
**InfHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [Min α] → [Min β] → [Fu
nLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InfHomClass F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `InfHom`.
-/
class InfHomClass (F α β : Type*) [Min α] [Min β] [FunLike F α β] : Prop where
  /-- An `InfHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b

/-- `LatticeHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `LatticeHom`. -/
/-
**LatticeHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [Lattice α] → [Lattice 
β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LatticeHomClass F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `LatticeHom`.
-/
class LatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [FunLike F α β] : Prop
  extends SupHomClass F α β, InfHomClass F α β where

attribute [to_dual existing] LatticeHomClass.toInfHomClass

end

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_sup map_inf

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β where
  map_rel := fun f a b h => by rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h]

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β]
    [OrderIsoClass F α β] : SupHomClass F α β where
  map_sup := fun f a b =>
    eq_of_forall_ge_iff fun c => by simp only [← le_map_inv_iff, sup_le_iff]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β]
    [OrderIsoClass F α β] : LatticeHomClass F α β where

end Equiv

section OrderEmbedding

variable [FunLike F α β]

/-- We can regard an injective map preserving binary infima as an order embedding. -/
@[simps! apply]
/-
**orderEmbeddingOfInjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderEmbeddingOfInjective [SemilatticeInf α] [SemilatticeInf β] (f : F) [I
nfHomClass F α β] (hf : Injective f) : α ↪o β
参数：f : F；hf : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can regard an injective map preserving binary infima as an order embedding.
-/
def orderEmbeddingOfInjective [SemilatticeInf α] [SemilatticeInf β] (f : F) [InfHomClass F α β]
    (hf : Injective f) : α ↪o β :=
  OrderEmbedding.ofMapLEIff f (fun x y ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ OrderHomClass.mono f h⟩
    rwa [← inf_eq_left, ← hf.eq_iff, map_inf, inf_eq_left])

end OrderEmbedding

variable [FunLike F α β]

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Max α] [Max β] [SupHomClass F α β] : CoeTC F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

/-! ### Supremum homomorphisms -/

namespace SupHom

variable [Max α]

section Sup

variable [Max β] [Max γ] [Max δ]

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupHomClass (SupHom α β) α β where
  map_sup := SupHom.map_sup'
/-
**SupHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Max β] (f : SupHo
m α β), f.toFun = ⇑f
参数：f : SupHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma toFun_eq_coe (f : SupHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp, norm_cast)]
/-
**SupHom.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `SupHom`。
形式化陈述：coe_mk (f : α -> β) (hf) : ⇑(mk f hf) = f
参数：f : α -> β；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
/-
**SupHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：ext {f g : SupHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of an `InfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/-
**SupHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : Max α] → [inst_1 : Max β] → (f
 : SupHom α β) → (f' : α → β) → f' = ⇑f → SupHom α β
参数：f : SupHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'

@[to_dual (attr := simp)]
/-
**SupHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_copy (f : SupHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : SupHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : SupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/-
**SupHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：copy_eq (f : SupHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : SupHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : SupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SupHom`. -/
@[to_dual /-- `id` as an `InfHom`. -/]
/-
**SupHom.id** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：(α : Type u_2) → [inst : Max α] → SupHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `SupHom`.
-/
protected def id : SupHom α α :=
  ⟨id, fun _ _ => rfl⟩

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
/-
**SupHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_id : ⇑(SupHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(SupHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
/-
**SupHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：id_apply (a : α) : SupHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl

/-- Composition of `SupHom`s as a `SupHom`. -/
@[to_dual /-- Composition of `InfHom`s as an `InfHom`. -/]
/-
**SupHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where toFun
参数：f : SupHom β γ；g : SupHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `SupHom`s as a `SupHom`.
-/
def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
  toFun := f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl

@[to_dual (attr := simp)]
/-
**SupHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α -> γ) = f ∘ g
参数：f : SupHom β γ；g : SupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g
 a)
参数：f : SupHom β γ；g : SupHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) : (f.comp g)
.comp h = f.comp (g.comp h)
参数：f : SupHom γ δ；g : SupHom β γ；h : SupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
/-
**SupHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Max β] (f : SupHo
m α β), f.comp (SupHom.id α) = f
参数：f : SupHom α β；SupHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem comp_id (f : SupHom α β) : f.comp (SupHom.id α) = f := rfl
/-
**SupHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Max β] (f : SupHo
m α β), (SupHom.id β).comp f = f
参数：f : SupHom α β；SupHom.id β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem id_comp (f : SupHom α β) : (SupHom.id β).comp f = f := rfl

@[to_dual (attr := simp)]
/-
**SupHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) : g
₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHom.ext`：ext {f g : SupHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => SupHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]
/-
**SupHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) : g.c
omp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHom.ext`：ext {f g : SupHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SupHom.comp_apply`：comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) 
: (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupHom.ext fun a => hg <| by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

end Sup

variable (α) [SemilatticeSup β]

/-- The constant function as a `SupHom`. -/
@[to_dual /-- The constant function as an `InfHom`. -/]
/-
**SupHom.const** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：const (b : β) : SupHom α β
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function as a `SupHom`.
-/
def const (b : β) : SupHom α β := ⟨fun _ ↦ b, fun _ _ ↦ (sup_idem _).symm⟩

@[to_dual (attr := simp)]
/-
**SupHom.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_const (b : β) : ⇑(const α b) = Function.const α b
参数：b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：const_apply (b : β) (a : α) : const α b a = b
参数：b : β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

variable {α}

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (SupHom α β) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply, map_sup, map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (SupHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (SupHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Bot β] : Bot (SupHom α β) :=
  ⟨SupHom.const α ⊥⟩

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Top β] : Top (SupHom α β) :=
  ⟨SupHom.const α ⊤⟩

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderBot β] : OrderBot (SupHom α β) :=
  OrderBot.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderTop β] : OrderTop (SupHom α β) :=
  OrderTop.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

@[to_dual]
/-
**SupHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedOrder β] : BoundedOrder (SupHom α β) :=
  BoundedOrder.lift ((↑) : _ → α → β) (fun _ _ => id) rfl rfl

@[to_dual (attr := simp)]
/-
**SupHom.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_sup (f g : SupHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : SupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (f g : SupHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a
参数：f g : SupHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：bot_apply [Bot β] (a : α) : (⊥ : SupHom α β) a = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_apply [Bot β] (a : α) : (⊥ : SupHom α β) a = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.top_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：top_apply [Top β] (a : α) : (⊤ : SupHom α β) a = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_apply [Top β] (a : α) : (⊤ : SupHom α β) a = ⊤ :=
  rfl

@[to_dual (attr := simp, gcongr) (reorder := toFun₁ toFun₂, map_sup₁ map_sup₂)
  (rename := toFun₁ ↔ toFun₂, map_sup₁ → map_inf₂, map_sup₂ → map_inf₁)]
/-
**SupHom.mk_le_mk** 是 Mathlib 中的一个引理，位于命名空间 `SupHom`。
形式化陈述：mk_le_mk (toFun₁ toFun₂ : α -> β) (map_sup₁ map_sup₂) : mk toFun₁ map_sup₁
 <= mk toFun₂ map_sup₂ ↔ toFun₁ <= toFun₂
参数：toFun₁ toFun₂ : α -> β；map_sup₁ map_sup₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_le_mk (toFun₁ toFun₂ : α → β) (map_sup₁ map_sup₂) :
    mk toFun₁ map_sup₁ ≤ mk toFun₂ map_sup₂ ↔ toFun₁ ≤ toFun₂ := .rfl

/-- `Subtype.val` as a `SupHom`. -/
@[to_dual (rename := Psup → Pinf) /-- `Subtype.val` as an `InfHom`. -/]
/-
**SupHom.subtypeVal** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：subtypeVal {P : β -> Prop} (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ 
y)) : letI
参数：Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subtype.val` as a `SupHom`.
-/
def subtypeVal {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    letI := Subtype.semilatticeSup Psup
    SupHom {x : β // P x} β :=
  letI := Subtype.semilatticeSup Psup
  .mk Subtype.val (by simp)

@[to_dual (attr := simp) (rename := Psup → Pinf)]
/-
**SupHom.subtypeVal_apply** 是 Mathlib 中的一个引理，位于命名空间 `SupHom`。
形式化陈述：subtypeVal_apply {P : β -> Prop} (Psup : forall ⦃x y : β⦄, P x -> P y -> P
 (x ⊔ y)) (x : {x : β // P x}) : subtypeVal Psup x = x
参数：Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)；x : {x : β // P x}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_apply {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) (x : {x : β // P x}) :
    subtypeVal Psup x = x := rfl

@[to_dual (attr := simp) (rename := Psup → Pinf)]
/-
**SupHom.subtypeVal_coe** 是 Mathlib 中的一个引理，位于命名空间 `SupHom`。
形式化陈述：subtypeVal_coe {P : β -> Prop} (Psup : forall ⦃x y : β⦄, P x -> P y -> P (
x ⊔ y)) : ⇑(subtypeVal Psup) = Subtype.val
参数：Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_coe {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    ⇑(subtypeVal Psup) = Subtype.val := rfl

end SupHom

/-! ### Lattice homomorphisms -/


namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

/-
**LatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `LatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (LatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
/-
**LatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `LatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LatticeHomClass (LatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
/-
**LatticeHom.toFun_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：toFun_eq_coe (f : LatticeHom α β) : f.toFun = f
参数：f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_eq_coe (f : LatticeHom α β) : f.toFun = f := rfl
/-
**LatticeHom.coe_toSupHom** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (f
 : LatticeHom α β), ⇑f.toSupHom = ⇑f
参数：f : LatticeHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma coe_toSupHom (f : LatticeHom α β) : ⇑f.toSupHom = f := rfl
/-
**LatticeHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] (f
 : SupHom α β)   (hf : ∀ (a b : α), f.toFun (a ⊓ b) = f.toFun a ⊓ f.toFun b), ⇑{
 toSupHom := f, map_inf' := hf } = ⇑f
参数：f : SupHom α β；hf : ∀ (a b : α), f.toFun (a ⊓ b) = f.toFun a ⊓ f.toFun b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : SupHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
/-
**LatticeHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：ext {f g : LatticeHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `LatticeHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**LatticeHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Lattice α] → [inst_1 : Lat
tice β] → (f : LatticeHom α β) → (f' : α → β) → f' = ⇑f → LatticeHom α β
参数：f : LatticeHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `LatticeHom` with a new `toFun` equal to the old one. Useful to fix de
finitional
equalities.
-/
protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

@[simp]
/-
**LatticeHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：coe_copy (f : LatticeHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) 
= f'
参数：f : LatticeHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**LatticeHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：copy_eq (f : LatticeHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : LatticeHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : LatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `LatticeHom`. -/
/-
**LatticeHom.id** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：(α : Type u_2) → [inst : Lattice α] → LatticeHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `LatticeHom`.
-/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
/-
**LatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `LatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

@[simp, norm_cast]
/-
**LatticeHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：coe_id : ⇑(LatticeHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(LatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**LatticeHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：id_apply (a : α) : LatticeHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl

/-- Composition of `LatticeHom`s as a `LatticeHom`. -/
/-
**LatticeHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ
参数：f : LatticeHom β γ；g : LatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `LatticeHom`s as a `LatticeHom`.
-/
def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]
/-
**LatticeHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α -> γ) =
 f ∘ g
参数：f : LatticeHom β γ；g : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**LatticeHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) 
a = f (g a)
参数：f : LatticeHom β γ；g : LatticeHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
-- `simp`-normal form of `coe_comp_sup_hom`
/-
**LatticeHom.coe_comp_sup_hom'** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：coe_comp_sup_hom' (f : LatticeHom β γ) (g : LatticeHom α β) : ⟨f ∘ g, map_
sup (f.comp g)⟩ = (f : SupHom β γ).comp g
参数：f : LatticeHom β γ；g : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `LatticeHom.instLatticeHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Lattice α] [inst_1 : Lattice β], LatticeHomClass (LatticeHom α β) α β
-/
theorem coe_comp_sup_hom' (f : LatticeHom β γ) (g : LatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

@[to_dual]
/-
**LatticeHom.coe_comp_sup_hom** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : S
upHom α γ) = (f : SupHom β γ).comp g
参数：f : LatticeHom β γ；g : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `LatticeHom.instLatticeHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Lattice α] [inst_1 : Lattice β], LatticeHomClass (LatticeHom α β) α β
-/
theorem coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
/-
**LatticeHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) 
: (f.comp g).comp h = f.comp (g.comp h)
参数：f : LatticeHom γ δ；g : LatticeHom β γ；h : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**LatticeHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f
参数：f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LatticeHom.ext`：ext {f g : LatticeHom α β} (h : forall a, f a = g a) : f
 = g
-/
theorem comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f :=
  LatticeHom.ext fun _ => rfl

@[simp]
/-
**LatticeHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f
参数：f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LatticeHom.ext`：ext {f g : LatticeHom α β} (h : forall a, f a = g a) : f
 = g
-/
theorem id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f :=
  LatticeHom.ext fun _ => rfl

@[simp]
/-
**LatticeHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjectiv
e f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LatticeHom.ext`：ext {f g : LatticeHom α β} (h : forall a, f a = g a) : f
 = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => LatticeHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
/-
**LatticeHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective 
g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LatticeHom.ext`：ext {f g : LatticeHom α β} (h : forall a, f a = g a) : f
 = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LatticeHom.comp_apply`：comp_apply (f : LatticeHom β γ) (g : LatticeHom α
 β) (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => LatticeHom.ext fun a => hg <| by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

/-- `Subtype.val` as a `LatticeHom`. -/
@[to_dual self (reorder := 4 5)]
/-
**LatticeHom.subtypeVal** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：subtypeVal {P : β -> Prop} (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) 
(Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) : letI
参数：Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；Pinf : forall ⦃x y⦄, P x -> P y 
-> P (x ⊓ y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subtype.val` as a `LatticeHom`.
-/
def subtypeVal {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    LatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_inf Pinf])

@[simp, to_dual self (reorder := 4 5)]
/-
**LatticeHom.subtypeVal_apply** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：subtypeVal_apply {P : β -> Prop} (Psup : forall ⦃x y⦄, P x -> P y -> P (x 
⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) (x : {x : β // P x}) : subt
ypeVal Psup Pinf x = x
参数：Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；Pinf : forall ⦃x y⦄, P x -> P y 
-> P (x ⊓ y)；x : {x : β // P x}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_apply {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y))
    (x : {x : β // P x}) :
    subtypeVal Psup Pinf x = x := rfl

@[simp, to_dual self (reorder := 4 5)]
/-
**LatticeHom.subtypeVal_coe** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：subtypeVal_coe {P : β -> Prop} (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ 
y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) : ⇑(subtypeVal Psup Pinf) = S
ubtype.val
参数：Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；Pinf : forall ⦃x y⦄, P x -> P y 
-> P (x ⊓ y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_coe {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    ⇑(subtypeVal Psup Pinf) = Subtype.val := rfl

end LatticeHom

namespace OrderHomClass

variable (α β)
variable [LinearOrder α] [Lattice β] [OrderHomClass F α β]

/-- An order homomorphism from a linear order is a lattice homomorphism. -/
/-
**OrderHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order homomorphism from a linear order is a lattice homomorphism.
-/
instance (priority := 100) toLatticeHomClass : LatticeHomClass F α β :=
  { ‹OrderHomClass F α β› with
    map_sup := fun f a b => by
      obtain h | h := le_total a b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b ≤ f a)]
    map_inf := fun f a b => by
      obtain h | h := le_total a b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b ≤ f a)] }

/-- Reinterpret an order homomorphism to a linear order as a `LatticeHom`. -/
/-
**OrderHomClass.toLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderHomClass`。
形式化陈述：toLatticeHom (f : F) : LatticeHom α β
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an order homomorphism to a linear order as a `LatticeHom`.
-/
def toLatticeHom (f : F) : LatticeHom α β := f

@[simp]
/-
**OrderHomClass.coe_to_lattice_hom** 是 Mathlib 中的一个定理，位于命名空间 `OrderHomClass`。
形式化陈述：coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f :=
  rfl

@[simp]
/-
**OrderHomClass.to_lattice_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHomClass`。
形式化陈述：to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a
参数：f : F；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a :=
  rfl

end OrderHomClass

/-! ### Dual homs -/

namespace SupHom

variable [Max α] [Max β] [Max γ]

/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[to_dual (attr := simps) /--
Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/]
/-
**SupHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `SupHom`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Max α] → [inst_1 : Max β] → SupH
om α β ≃ InfHom αᵒᵈ βᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SupHom.map_sup'`：∀ {α : Type u_6} {β : Type u_7} [inst : Max α] [inst_1 
: Max β] (self : SupHom α β) (a b : α),   self.toFun (a ⊔ b) = self.toFun a ⊔ se
lf.to…
-/
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩

@[to_dual (attr := simp)]
/-
**SupHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：dual_id : SupHom.dual (SupHom.id α) = InfHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : SupHom.dual (SupHom.id α) = InfHom.id _ :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：dual_comp (g : SupHom β γ) (f : SupHom α β) : SupHom.dual (g.comp f) = (Su
pHom.dual g).comp (SupHom.dual f)
参数：g : SupHom β γ；f : SupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) :
    SupHom.dual (g.comp f) = (SupHom.dual g).comp (SupHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl

@[to_dual (attr := simp)]
/-
**SupHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupHom`。
形式化陈述：symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) : SupHom.dual.sym
m (g.comp f) = (SupHom.dual.symm g).comp (SupHom.dual.symm f)
参数：g : InfHom βᵒᵈ γᵒᵈ；f : InfHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) =
      (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl

end SupHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps!]
/-
**LatticeHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Lattice α] → [inst_1 : Lattice β
] → LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret a lattice homomorphism as a lattice homomorphism between the dual la
ttices.
-/
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩
/-
**LatticeHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：∀ {α : Type u_2} [inst : Lattice α], LatticeHom.dual (LatticeHom.id α) = L
atticeHom.id αᵒᵈ
参数：LatticeHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dual_id : LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _ := rfl

@[simp]
/-
**LatticeHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) : LatticeHom.dual (g.c
omp f) = (LatticeHom.dual g).comp (LatticeHom.dual f)
参数：g : LatticeHom β γ；f : LatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) :
    LatticeHom.dual (g.comp f) = (LatticeHom.dual g).comp (LatticeHom.dual f) :=
  rfl

@[simp]
/-
**LatticeHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl

@[simp]
/-
**LatticeHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) : Lattice
Hom.dual.symm (g.comp f) = (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f
)
参数：g : LatticeHom βᵒᵈ γᵒᵈ；f : LatticeHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) =
      (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl

end LatticeHom

/-! ### Prod -/

namespace LatticeHom
variable [Lattice α] [Lattice β]

/-- Natural projection homomorphism from `α × β` to `α`. -/
/-
**LatticeHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：fst : LatticeHom (α × β) α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural projection homomorphism from `α × β` to `α`.
-/
def fst : LatticeHom (α × β) α where
  toFun := Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- Natural projection homomorphism from `α × β` to `β`. -/
/-
**LatticeHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：snd : LatticeHom (α × β) β where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural projection homomorphism from `α × β` to `β`.
-/
def snd : LatticeHom (α × β) β where
  toFun := Prod.snd
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
/-
**LatticeHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β], ⇑
LatticeHom.fst = Prod.fst
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst (α := α) (β := β)) = Prod.fst := rfl
/-
**LatticeHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `LatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β], ⇑
LatticeHom.snd = Prod.snd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd (α := α) (β := β)) = Prod.snd := rfl
/-
**LatticeHom.fst_apply** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：fst_apply (x : α × β) : fst x = x.fst
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_apply (x : α × β) : fst x = x.fst := rfl
/-
**LatticeHom.snd_apply** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：snd_apply (x : α × β) : snd x = x.snd
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_apply (x : α × β) : snd x = x.snd := rfl

end LatticeHom

/-! ### Pi -/

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)]

/-- Evaluation as a lattice homomorphism. -/
/-
**Pi.evalLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：evalLatticeHom (i : ι) : LatticeHom (forall i, α i) (α i) where toFun
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation as a lattice homomorphism.
-/
def evalLatticeHom (i : ι) : LatticeHom (∀ i, α i) (α i) where
  toFun := Function.eval i
  map_sup' _a _b := rfl
  map_inf' _a _b := rfl

@[simp, norm_cast]
/-
**Pi.coe_evalLatticeHom** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：coe_evalLatticeHom (i : ι) : ⇑(evalLatticeHom (α
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_evalLatticeHom (i : ι) : ⇑(evalLatticeHom (α := α) i) = Function.eval i := rfl
/-
**Pi.evalLatticeHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：evalLatticeHom_apply (i : ι) (f : forall i, α i) : evalLatticeHom i f = f 
i
参数：i : ι；f : forall i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalLatticeHom_apply (i : ι) (f : ∀ i, α i) : evalLatticeHom i f = f i := rfl

end Pi

