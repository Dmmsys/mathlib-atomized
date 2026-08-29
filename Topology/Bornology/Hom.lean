/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Bornology.Basic

/-!
# Locally bounded maps

This file defines locally bounded maps between bornologies.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `LocallyBoundedMap`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `LocallyBoundedMapClass`
-/

@[expose] public section


open Bornology Filter Function Set

variable {F α β γ δ : Type*}

/--
Definition of `LocallyBoundedMap` / `LocallyBoundedMap` 的定义

English:
structure LocallyBoundedMap
  parameters: (α β : Type*) [Bornology α] [Bornology β]
  axioms and operations (2):
    - toFun : α -> β
    - comap_cobounded_le' : (cobounded β).comap toFun <= cobounded α

中文:
结构 LocallyBoundedMap
  参数: (α β : 类型) [Bornology α] [Bornology β]
  公理与运算 (2 个):
    - toFun : α -> β
    - comap_cobounded_le' : (cobounded β).comap toFun <= cobounded α
-/
structure LocallyBoundedMap (α β : Type*) [Bornology α] [Bornology β] where
  /-- The function underlying a locally bounded map -/
  toFun : α -> β
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le' : (cobounded β).comap toFun <= cobounded α

section

/--
Definition of `LocallyBoundedMapClass` / `LocallyBoundedMapClass` 的定义

English:
class LocallyBoundedMapClass
  parameters: (F : Type*) (α β : outParam Type*) [Bornology α]
  axioms and operations (1):
    - comap_cobounded_le((f : F)) : (cobounded β).comap f <= cobounded α

中文:
类 LocallyBoundedMapClass
  参数: (F : 类型) (α β : outParam 类型) [Bornology α]
  公理与运算 (1 个):
    - comap_cobounded_le((f : F)) : (cobounded β).comap f <= cobounded α
-/
class LocallyBoundedMapClass (F : Type*) (α β : outParam Type*) [Bornology α]
    [Bornology β] [FunLike F α β] : Prop where
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le (f : F) : (cobounded β).comap f <= cobounded α

end

export LocallyBoundedMapClass (comap_cobounded_le)

variable [FunLike F α β]

/--
theorem `Bornology.IsBounded.image` / 定理 `Bornology.IsBounded.image`

English:
theorem Bornology.IsBounded.image
  statement: [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] (f : F)
  proof: comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

中文:
定理 Bornology.IsBounded.image
  结论: [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] (f : F)
  证明: comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

Depends on / 依赖: comap_cobounded_le, comap_cobounded_le_iff
-/
theorem Bornology.IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] (f : F)
    {s : Set α} (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

/-- Turn an element of a type `F` satisfying `LocallyBoundedMapClass F α β` into an actual
`LocallyBoundedMap`. This is declared as the default coercion from `F` to
`LocallyBoundedMap α β`. -/
@[coe]
/--
Definition of `LocallyBoundedMapClass.toLocallyBoundedMap` / `LocallyBoundedMapClass.toLocallyBoundedMap` 的定义

English:
definition LocallyBoundedMapClass.toLocallyBoundedMap
  signature: [Bornology α] [Bornology β]
  body: f
  comap_cobounded_le' := comap_cobounded_le f

中文:
定义 LocallyBoundedMapClass.toLocallyBoundedMap
  签名: [Bornology α] [Bornology β]
  定义体: f
  comap_cobounded_le' := comap_cobounded_le f
-/
def LocallyBoundedMapClass.toLocallyBoundedMap [Bornology α] [Bornology β]
    [LocallyBoundedMapClass F α β] (f : F) : LocallyBoundedMap α β where
  toFun := f
  comap_cobounded_le' := comap_cobounded_le f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Bornology
  signature: α] [Bornology β] [LocallyBoundedMapClass F α β] :
  body: ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

中文:
实例 [Bornology
  签名: α] [Bornology β] [LocallyBoundedMapClass F α β] :
  定义体: ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

Depends on / 依赖: comap_cobounded_le
-/
instance [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] :
    CoeTC F (LocallyBoundedMap α β) :=
  ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

namespace LocallyBoundedMap

variable [Bornology α] [Bornology β] [Bornology γ] [Bornology δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (LocallyBoundedMap α β) α β
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

中文:
实例 :
  签名: FunLike (LocallyBoundedMap α β) α β
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (LocallyBoundedMap α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyBoundedMapClass (LocallyBoundedMap α β) α β
  body: f.comap_cobounded_le'

@[ext]

中文:
实例 :
  签名: LocallyBoundedMapClass (LocallyBoundedMap α β) α β
  定义体: f.comap_cobounded_le'

@[ext]

Depends on / 依赖: comap_cobounded_le, f.comap_cobounded_le
-/
instance : LocallyBoundedMapClass (LocallyBoundedMap α β) α β where
  comap_cobounded_le f := f.comap_cobounded_le'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : LocallyBoundedMap α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : LocallyBoundedMap α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : LocallyBoundedMap α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f)
  body: ⟨f', h.symm ▸ f.comap_cobounded_le'⟩

@[simp]

中文:
定义 copy
  签名: (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f)
  定义体: ⟨f', h.symm ▸ f.comap_cobounded_le'⟩

@[simp]
-/
protected def copy (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f) : LocallyBoundedMap α β :=
  ⟨f', h.symm ▸ f.comap_cobounded_le'⟩

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/--
Definition of `ofMapBounded` / `ofMapBounded` 的定义

English:
definition ofMapBounded
  signature: (f : α -> β) (h : forall ⦃s : Set α⦄, IsBounded s -> IsBounded (f '' s))
  body: ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp]

中文:
定义 ofMapBounded
  签名: (f : α -> β) (h : 对任意 ⦃s : Set α⦄, IsBounded s -> IsBounded (f '' s))
  定义体: ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp]

Depends on / 依赖: comap_cobounded_le_iff
-/
def ofMapBounded (f : α -> β) (h : forall ⦃s : Set α⦄, IsBounded s -> IsBounded (f '' s)) :
    LocallyBoundedMap α β :=
  ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp]
/--
theorem `coe_ofMapBounded` / 定理 `coe_ofMapBounded`

English:
theorem coe_ofMapBounded
  given: (f : α -> β) {h}
  statement: ⇑(ofMapBounded f h) = f
  proof: rfl

@[simp]

中文:
定理 coe_ofMapBounded
  条件: (f : α -> β) {h}
  结论: ⇑(ofMapBounded f h) = f
  证明: rfl

@[simp]
-/
theorem coe_ofMapBounded (f : α -> β) {h} : ⇑(ofMapBounded f h) = f :=
  rfl

@[simp]
/--
theorem `ofMapBounded_apply` / 定理 `ofMapBounded_apply`

English:
theorem ofMapBounded_apply
  given: (f : α -> β) {h} (a : α)
  statement: ofMapBounded f h a = f a
  proof: rfl

中文:
定理 ofMapBounded_apply
  条件: (f : α -> β) {h} (a : α)
  结论: ofMapBounded f h a = f a
  证明: rfl
-/
theorem ofMapBounded_apply (f : α -> β) {h} (a : α) : ofMapBounded f h a = f a :=
  rfl

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : LocallyBoundedMap α α
  body: ⟨id, comap_id.le⟩

中文:
定义 id
  签名: : LocallyBoundedMap α α
  定义体: ⟨id, comap_id.le⟩
-/
protected def id : LocallyBoundedMap α α :=
  ⟨id, comap_id.le⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LocallyBoundedMap α α)
  body: ⟨LocallyBoundedMap.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited (LocallyBoundedMap α α)
  定义体: ⟨LocallyBoundedMap.id α⟩

@[simp, norm_cast]

Depends on / 依赖: LocallyBoundedMap, LocallyBoundedMap.id
-/
instance : Inhabited (LocallyBoundedMap α α) :=
  ⟨LocallyBoundedMap.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(LocallyBoundedMap.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(LocallyBoundedMap.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(LocallyBoundedMap.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: LocallyBoundedMap.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: LocallyBoundedMap.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : LocallyBoundedMap.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β)
  body: f ∘ g
  comap_cobounded_le' :=
comap_comap.ge.trans (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'

@[simp]

中文:
定义 comp
  签名: (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β)
  定义体: f ∘ g
  comap_cobounded_le' :=
comap_comap.ge.trans (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'

@[simp]
-/
def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ where
  toFun := f ∘ g
  comap_cobounded_le' :=
comap_comap.ge.trans (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) :
    f.comp g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  结论: (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
    (h : LocallyBoundedMap α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : LocallyBoundedMap α β)
  statement: f.comp (LocallyBoundedMap.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : LocallyBoundedMap α β)
  结论: f.comp (LocallyBoundedMap.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : LocallyBoundedMap α β)
  statement: (LocallyBoundedMap.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : LocallyBoundedMap α β)
  结论: (LocallyBoundedMap.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  statement: {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congrArg (comp · _)⟩

@[simp]

中文:
定理 cancel_right
  结论: {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congrArg (comp · _)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congrArg (comp · _)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end LocallyBoundedMap
