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

/--
Definition of `PseudoEpimorphism` / `PseudoEpimorphism` 的定义

English:
structure PseudoEpimorphism
  parameters: (α β : Type*) [Preorder α] [Preorder β]
  extends: α ->o β
  axioms and operations (1):
    - exists_map_eq_of_map_le'(⦃a) : α⦄ ⦃b : β⦄ : toFun a <= b -> exists c, a <= c ∧ toFun c = b

中文:
结构 PseudoEpimorphism
  参数: (α β : 类型) [Preorder α] [Preorder β]
  继承: α ->o β
  公理与运算 (1 个):
    - exists_map_eq_of_map_le'(⦃a) : α⦄ ⦃b : β⦄ : toFun a <= b -> 存在 c, a <= c ∧ toFun c = b
-/
structure PseudoEpimorphism (α β : Type*) [Preorder α] [Preorder β] extends α ->o β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a <= b -> exists c, a <= c ∧ toFun c = b

/--
Definition of `EsakiaHom` / `EsakiaHom` 的定义

English:
structure EsakiaHom
  parameters: (α β : Type*) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  extends: α ->Co β
  axioms and operations (1):
    - exists_map_eq_of_map_le'(⦃a) : α⦄ ⦃b : β⦄ : toFun a <= b -> exists c, a <= c ∧ toFun c = b

中文:
结构 EsakiaHom
  参数: (α β : 类型) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  继承: α ->Co β
  公理与运算 (1 个):
    - exists_map_eq_of_map_le'(⦃a) : α⦄ ⦃b : β⦄ : toFun a <= b -> 存在 c, a <= c ∧ toFun c = b
-/
structure EsakiaHom (α β : Type*) [TopologicalSpace α] [Preorder α] [TopologicalSpace β]
  [Preorder β] extends α ->Co β where
  exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : toFun a <= b -> exists c, a <= c ∧ toFun c = b

section

/--
Definition of `PseudoEpimorphismClass` / `PseudoEpimorphismClass` 的定义

English:
class PseudoEpimorphismClass
  parameters: (F : Type*) (α β : outParam Type*)
  extends: OrderHomClass F α β
  axioms and operations (1):
    - exists_map_eq_of_map_le((f : F) ⦃a) : α⦄ ⦃b : β⦄ : f a <= b -> exists c, a <= c ∧ f c = b

中文:
类 PseudoEpimorphismClass
  参数: (F : 类型) (α β : outParam 类型)
  继承: OrderHomClass F α β
  公理与运算 (1 个):
    - exists_map_eq_of_map_le((f : F) ⦃a) : α⦄ ⦃b : β⦄ : f a <= b -> 存在 c, a <= c ∧ f c = b
-/
class PseudoEpimorphismClass (F : Type*) (α β : outParam Type*)
    [Preorder α] [Preorder β] [FunLike F α β] : Prop
    extends OrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a <= b -> exists c, a <= c ∧ f c = b

/--
Definition of `EsakiaHomClass` / `EsakiaHomClass` 的定义

English:
class EsakiaHomClass
  parameters: (F : Type*) (α β : outParam Type*) [TopologicalSpace α] [Preorder α]
  extends: ContinuousOrderHomClass F α β
  axioms and operations (1):
    - exists_map_eq_of_map_le((f : F) ⦃a) : α⦄ ⦃b : β⦄ : f a <= b -> exists c, a <= c ∧ f c = b

中文:
类 EsakiaHomClass
  参数: (F : 类型) (α β : outParam 类型) [TopologicalSpace α] [Preorder α]
  继承: ContinuousOrderHomClass F α β
  公理与运算 (1 个):
    - exists_map_eq_of_map_le((f : F) ⦃a) : α⦄ ⦃b : β⦄ : f a <= b -> 存在 c, a <= c ∧ f c = b
-/
class EsakiaHomClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [FunLike F α β] : Prop
    extends ContinuousOrderHomClass F α β where
  exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a <= b -> exists c, a <= c ∧ f c = b

end

export PseudoEpimorphismClass (exists_map_eq_of_map_le)

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
instance (priority := 100) PseudoEpimorphismClass.toTopHomClass [PartialOrder α] [OrderTop α]
    [Preorder β] [OrderTop β] [PseudoEpimorphismClass F α β] : TopHomClass F α β where
  map_top f := by
    let ⟨b, h⟩ := exists_map_eq_of_map_le f (@le_top _ _ _ <| f ⊤)
    rw [← top_le_iff.1 h.1]; rw [h.2]

-- See note [lower instance priority]
instance (priority := 100) EsakiaHomClass.toPseudoEpimorphismClass [TopologicalSpace α] [Preorder α]
    [TopologicalSpace β] [Preorder β] [EsakiaHomClass F α β] : PseudoEpimorphismClass F α β :=
  { ‹EsakiaHomClass F α β› with
    map_rel := ContinuousOrderHomClass.map_monotone }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [PseudoEpimorphismClass F α β] :
  body: ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

中文:
实例 [Preorder
  签名: α] [Preorder β] [PseudoEpimorphismClass F α β] :
  定义体: ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

Depends on / 依赖: exists_map_eq_of_map_le
-/
instance [Preorder α] [Preorder β] [PseudoEpimorphismClass F α β] :
    CoeTC F (PseudoEpimorphism α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [Preorder α] [TopologicalSpace β] [Preorder β]
  body: ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

中文:
实例 [TopologicalSpace
  签名: α] [Preorder α] [TopologicalSpace β] [Preorder β]
  定义体: ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

Depends on / 依赖: exists_map_eq_of_map_le
-/
instance [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β]
    [EsakiaHomClass F α β] : CoeTC F (EsakiaHom α β) :=
  ⟨fun f => ⟨f, exists_map_eq_of_map_le f⟩⟩

end Hom

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toPseudoEpimorphismClass [Preorder α] [Preorder β]
    [EquivLike F α β] [OrderIsoClass F α β] : PseudoEpimorphismClass F α β where
  exists_map_eq_of_map_le f _a b h :=
    ⟨EquivLike.inv f b, (le_map_inv_iff f).2 h, EquivLike.right_inv _ _⟩

/-! ### Pseudo-epimorphisms -/


namespace PseudoEpimorphism

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (PseudoEpimorphism α β) α β where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : FunLike (PseudoEpimorphism α β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (PseudoEpimorphism α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEpimorphismClass (PseudoEpimorphism α β) α β
  body: f.monotone' h
  exists_map_eq_of_map_le := PseudoEpimorphism.exists_map_eq_of_map_le'

@[simp]

中文:
实例 :
  签名: PseudoEpimorphismClass (PseudoEpimorphism α β) α β
  定义体: f.monotone' h
  exists_map_eq_of_map_le := PseudoEpimorphism.exists_map_eq_of_map_le'

@[simp]

Depends on / 依赖: f.monotone, monotone
-/
instance : PseudoEpimorphismClass (PseudoEpimorphism α β) α β where
  map_rel f _ _ h := f.monotone' h
  exists_map_eq_of_map_le := PseudoEpimorphism.exists_map_eq_of_map_le'

@[simp]
/--
theorem `toOrderHom_eq_coe` / 定理 `toOrderHom_eq_coe`

English:
theorem toOrderHom_eq_coe
  given: (f : PseudoEpimorphism α β)
  statement: ⇑f.toOrderHom = f
  proof: rfl

中文:
定理 toOrderHom_eq_coe
  条件: (f : PseudoEpimorphism α β)
  结论: ⇑f.toOrderHom = f
  证明: rfl
-/
theorem toOrderHom_eq_coe (f : PseudoEpimorphism α β) : ⇑f.toOrderHom = f := rfl

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : PseudoEpimorphism α β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : PseudoEpimorphism α β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : PseudoEpimorphism α β} : f.toFun = (f : α -> β) := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : PseudoEpimorphism α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : PseudoEpimorphism α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : PseudoEpimorphism α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f)
  body: ⟨f.toOrderHom.copy f' h, by simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]

中文:
定义 copy
  签名: (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f.toOrderHom.copy f' h, by simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]
-/
protected def copy (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f) : PseudoEpimorphism α β :=
  ⟨f.toOrderHom.copy f' h, by simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : PseudoEpimorphism α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : PseudoEpimorphism α α
  body: ⟨OrderHom.id, fun _ b h => ⟨b, h, rfl⟩⟩

中文:
定义 id
  签名: : PseudoEpimorphism α α
  定义体: ⟨OrderHom.id, fun _ b h => ⟨b, h, rfl⟩⟩
-/
protected def id : PseudoEpimorphism α α :=
  ⟨OrderHom.id, fun _ b h => ⟨b, h, rfl⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (PseudoEpimorphism α α)
  body: ⟨PseudoEpimorphism.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited (PseudoEpimorphism α α)
  定义体: ⟨PseudoEpimorphism.id α⟩

@[simp, norm_cast]

Depends on / 依赖: PseudoEpimorphism, PseudoEpimorphism.id
-/
instance : Inhabited (PseudoEpimorphism α α) :=
  ⟨PseudoEpimorphism.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(PseudoEpimorphism.id α) = id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id
  结论: ⇑(PseudoEpimorphism.id α) = id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id : ⇑(PseudoEpimorphism.id α) = id := rfl

@[simp, norm_cast]
/--
theorem `coe_id_orderHom` / 定理 `coe_id_orderHom`

English:
theorem coe_id_orderHom
  statement: (PseudoEpimorphism.id α : α ->o α) = OrderHom.id
  proof: rfl

中文:
定理 coe_id_orderHom
  结论: (PseudoEpimorphism.id α : α ->o α) = OrderHom.id
  证明: rfl
-/
theorem coe_id_orderHom : (PseudoEpimorphism.id α : α ->o α) = OrderHom.id := rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: PseudoEpimorphism.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: PseudoEpimorphism.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : PseudoEpimorphism.id α a = a := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β)
  body: ⟨g.toOrderHom.comp f.toOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]

中文:
定义 comp
  签名: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β)
  定义体: ⟨g.toOrderHom.comp f.toOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]

Depends on / 依赖: exists_map_eq_of_map_le, f.exists_map_eq_of_map_le, f.toOrderHom, g.exists_map_eq_of_map_le, g.toOrderHom.comp, toOrderHom
-/
def comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimorphism α γ :=
  ⟨g.toOrderHom.comp f.toOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β)
  证明: rfl

@[simp]
-/
theorem coe_comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α -> γ) = g ∘ f := rfl

@[simp]
/--
theorem `coe_comp_orderHom` / 定理 `coe_comp_orderHom`

English:
theorem coe_comp_orderHom
  given: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_orderHom
  条件: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_orderHom (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) :
    (g.comp f : α ->o γ) = (g : β ->o γ).comp f := rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α) :
    (g.comp f) a = g (f a) := rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  结论: (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ)
  证明: rfl

@[simp]
-/
theorem comp_assoc (h : PseudoEpimorphism γ δ) (g : PseudoEpimorphism β γ)
    (f : PseudoEpimorphism α β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : PseudoEpimorphism α β)
  statement: f.comp (PseudoEpimorphism.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : PseudoEpimorphism α β)
  结论: f.comp (PseudoEpimorphism.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : PseudoEpimorphism α β) : f.comp (PseudoEpimorphism.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : PseudoEpimorphism α β)
  statement: (PseudoEpimorphism.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : PseudoEpimorphism α β)
  结论: (PseudoEpimorphism.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : PseudoEpimorphism α β) : (PseudoEpimorphism.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  statement: {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β}
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]

中文:
定理 cancel_right
  结论: {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β}
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : PseudoEpimorphism β γ} {f : PseudoEpimorphism α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (hg : Injective g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : PseudoEpimorphism β γ} {f₁ f₂ : PseudoEpimorphism α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end PseudoEpimorphism

/-! ### Esakia morphisms -/


namespace EsakiaHom

variable [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β] [TopologicalSpace γ]
  [Preorder γ] [TopologicalSpace δ] [Preorder δ]

/--
Definition of `toPseudoEpimorphism` / `toPseudoEpimorphism` 的定义

English:
definition toPseudoEpimorphism
  signature: (f : EsakiaHom α β)
  body: { f with }

中文:
定义 toPseudoEpimorphism
  签名: (f : EsakiaHom α β)
  定义体: { f with }
-/
def toPseudoEpimorphism (f : EsakiaHom α β) : PseudoEpimorphism α β :=
  { f with }

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (EsakiaHom α β) α β where
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

中文:
实例 instFunLike
  签名: : FunLike (EsakiaHom α β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (EsakiaHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EsakiaHomClass (EsakiaHom α β) α β
  body: f.monotone'
  map_continuous f := f.continuous_toFun
  exists_map_eq_of_map_le f := f.exists_map_eq_of_map_le'

@[simp]

中文:
实例 :
  签名: EsakiaHomClass (EsakiaHom α β) α β
  定义体: f.monotone'
  map_continuous f := f.continuous_toFun
  exists_map_eq_of_map_le f := f.exists_map_eq_of_map_le'

@[simp]

Depends on / 依赖: f.monotone, monotone
-/
instance : EsakiaHomClass (EsakiaHom α β) α β where
  map_monotone f := f.monotone'
  map_continuous f := f.continuous_toFun
  exists_map_eq_of_map_le f := f.exists_map_eq_of_map_le'

@[simp]
/--
theorem `toContinuousOrderHom_coe` / 定理 `toContinuousOrderHom_coe`

English:
theorem toContinuousOrderHom_coe
  given: {f : EsakiaHom α β}
  proof: rfl

中文:
定理 toContinuousOrderHom_coe
  条件: {f : EsakiaHom α β}
  证明: rfl
-/
theorem toContinuousOrderHom_coe {f : EsakiaHom α β} :
    f.toContinuousOrderHom = (f : α -> β) := rfl

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : EsakiaHom α β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : EsakiaHom α β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : EsakiaHom α β} : f.toFun = (f : α -> β) := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : EsakiaHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : EsakiaHom α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : EsakiaHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : EsakiaHom α β) (f' : α -> β) (h : f' = f)
  body: ⟨f.toContinuousOrderHom.copy f' h, by
    simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]

中文:
定义 copy
  签名: (f : EsakiaHom α β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f.toContinuousOrderHom.copy f' h, by
    simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]
-/
protected def copy (f : EsakiaHom α β) (f' : α -> β) (h : f' = f) : EsakiaHom α β :=
  ⟨f.toContinuousOrderHom.copy f' h, by
    simpa only [h.symm, toFun_eq_coe] using! f.exists_map_eq_of_map_le'⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : EsakiaHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : EsakiaHom α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : EsakiaHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : EsakiaHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : EsakiaHom α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : EsakiaHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : EsakiaHom α α
  body: ⟨ContinuousOrderHom.id α, fun _ b h => ⟨b, h, rfl⟩⟩

中文:
定义 id
  签名: : EsakiaHom α α
  定义体: ⟨ContinuousOrderHom.id α, fun _ b h => ⟨b, h, rfl⟩⟩
-/
protected def id : EsakiaHom α α :=
  ⟨ContinuousOrderHom.id α, fun _ b h => ⟨b, h, rfl⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (EsakiaHom α α)
  body: ⟨EsakiaHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited (EsakiaHom α α)
  定义体: ⟨EsakiaHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: EsakiaHom, EsakiaHom.id
-/
instance : Inhabited (EsakiaHom α α) :=
  ⟨EsakiaHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(EsakiaHom.id α) = id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id
  结论: ⇑(EsakiaHom.id α) = id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id : ⇑(EsakiaHom.id α) = id := rfl

@[simp, norm_cast]
/--
theorem `coe_id_pseudoEpimorphism` / 定理 `coe_id_pseudoEpimorphism`

English:
theorem coe_id_pseudoEpimorphism
  proof: rfl

中文:
定理 coe_id_pseudoEpimorphism
  证明: rfl
-/
theorem coe_id_pseudoEpimorphism :
    (EsakiaHom.id α : PseudoEpimorphism α α) = PseudoEpimorphism.id α := rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: EsakiaHom.id α a = a
  proof: rfl

@[simp, norm_cast]

中文:
定理 id_apply
  条件: (a : α)
  结论: EsakiaHom.id α a = a
  证明: rfl

@[simp, norm_cast]
-/
theorem id_apply (a : α) : EsakiaHom.id α a = a := rfl

@[simp, norm_cast]
/--
theorem `coe_id_continuousOrderHom` / 定理 `coe_id_continuousOrderHom`

English:
theorem coe_id_continuousOrderHom
  statement: (EsakiaHom.id α : α ->Co α) = ContinuousOrderHom.id α
  proof: rfl

中文:
定理 coe_id_continuousOrderHom
  结论: (EsakiaHom.id α : α ->Co α) = ContinuousOrderHom.id α
  证明: rfl
-/
theorem coe_id_continuousOrderHom : (EsakiaHom.id α : α ->Co α) = ContinuousOrderHom.id α := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  body: ⟨g.toContinuousOrderHom.comp f.toContinuousOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]

中文:
定义 comp
  签名: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  定义体: ⟨g.toContinuousOrderHom.comp f.toContinuousOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]

Depends on / 依赖: exists_map_eq_of_map_le, f.exists_map_eq_of_map_le, f.toContinuousOrderHom, g.exists_map_eq_of_map_le, g.toContinuousOrderHom.comp, toContinuousOrderHom
-/
def comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ :=
  ⟨g.toContinuousOrderHom.comp f.toContinuousOrderHom, fun a b h₀ => by
    obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀
    obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁
    exact ⟨b, h₂, rfl⟩⟩

@[simp]
/--
theorem `coe_comp_continuousOrderHom` / 定理 `coe_comp_continuousOrderHom`

English:
theorem coe_comp_continuousOrderHom
  given: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_continuousOrderHom
  条件: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_continuousOrderHom (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : α ->Co γ) = (g : β ->Co γ).comp f := rfl

@[simp]
/--
theorem `coe_comp_pseudoEpimorphism` / 定理 `coe_comp_pseudoEpimorphism`

English:
theorem coe_comp_pseudoEpimorphism
  given: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_pseudoEpimorphism
  条件: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_pseudoEpimorphism (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (g.comp f : PseudoEpimorphism α γ) = (g : PseudoEpimorphism β γ).comp f := rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  statement: (g.comp f : α -> γ) = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (g : EsakiaHom β γ) (f : EsakiaHom α β)
  结论: (g.comp f : α -> γ) = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : (g.comp f : α -> γ) = g ∘ f := rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α)
  statement: (g.comp f) a = g (f a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α)
  结论: (g.comp f) a = g (f a)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α) : (g.comp f) a = g (f a) := rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (h : EsakiaHom γ δ) (g : EsakiaHom β γ) (f : EsakiaHom α β) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : EsakiaHom α β)
  statement: f.comp (EsakiaHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : EsakiaHom α β)
  结论: f.comp (EsakiaHom.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : EsakiaHom α β) : f.comp (EsakiaHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : EsakiaHom α β)
  statement: (EsakiaHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : EsakiaHom α β)
  结论: (EsakiaHom.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : EsakiaHom α β) : (EsakiaHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : EsakiaHom β γ} {f : EsakiaHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (comp · f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : EsakiaHom β γ} {f₁ f₂ : EsakiaHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end EsakiaHom
