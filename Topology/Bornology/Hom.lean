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

/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
/-
**LocallyBoundedMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Bornology α] → [Bornology β] → Type (ma
x u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bounded maps from `α` to `β`, the maps which send a bounded set to a
 bounded set.
-/
structure LocallyBoundedMap (α β : Type*) [Bornology α] [Bornology β] where
  /-- The function underlying a locally bounded map -/
  toFun : α → β
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le' : (cobounded β).comap toFun ≤ cobounded α

section

/-- `LocallyBoundedMapClass F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `LocallyBoundedMap`. -/
/-
**LocallyBoundedMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) →   (α : outParam (Type u_7)) → (β : outParam (Type u_8)) →
 [Bornology α] → [Bornology β] → [FunLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyBoundedMapClass F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `LocallyBoundedMap`.
-/
class LocallyBoundedMapClass (F : Type*) (α β : outParam Type*) [Bornology α]
    [Bornology β] [FunLike F α β] : Prop where
  /-- The pullback of the `Bornology.cobounded` filter under the function is contained in the
  cobounded filter. Equivalently, the function maps bounded sets to bounded sets. -/
  comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α

end

export LocallyBoundedMapClass (comap_cobounded_le)

variable [FunLike F α β]

/-
**Bornology.IsBounded.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapCl
ass F α β] (f : F) {s : Set α} (hs : IsBounded s) : IsBounded (f '' s)
参数：f : F；hs : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bornology.comap_cobounded_le_iff`：comap_cobounded_le_iff [Bornology β] {
f : α -> β} : (cobounded β).comap f <= cobounded α ↔ forall ⦃s⦄, IsBounded s -> 
IsBounded (f '' s)
· 使用定理 `LocallyBoundedMapClass.comap_cobounded_le`：∀ {F : Type u_6} {α : outPara
m (Type u_7)} {β : outParam (Type u_8)} {inst : Bornology α} {inst_1 : Bornology
 β}   {inst_2 : FunLike F α β} …
-/
theorem Bornology.IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] (f : F)
    {s : Set α} (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

/-- Turn an element of a type `F` satisfying `LocallyBoundedMapClass F α β` into an actual
`LocallyBoundedMap`. This is declared as the default coercion from `F` to
`LocallyBoundedMap α β`. -/
@[coe]
/-
**LocallyBoundedMapClass.toLocallyBoundedMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyBoundedMapClass.toLocallyBoundedMap [Bornology α] [Bornology β] [Lo
callyBoundedMapClass F α β] (f : F) : LocallyBoundedMap α β where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedMapClass.comap_cobounded_le`：∀ {F : Type u_6} {α : outPara
m (Type u_7)} {β : outParam (Type u_8)} {inst : Bornology α} {inst_1 : Bornology
 β}   {inst_2 : FunLike F α β} …

--- 原说明 ---
Turn an element of a type `F` satisfying `LocallyBoundedMapClass F α β` into an 
actual
`LocallyBoundedMap`. This is declared as the default coercion from `F` to
`LocallyBoundedMap α β`.
-/
def LocallyBoundedMapClass.toLocallyBoundedMap [Bornology α] [Bornology β]
    [LocallyBoundedMapClass F α β] (f : F) : LocallyBoundedMap α β where
  toFun := f
  comap_cobounded_le' := comap_cobounded_le f
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] :
    CoeTC F (LocallyBoundedMap α β) :=
  ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

namespace LocallyBoundedMap

variable [Bornology α] [Bornology β] [Bornology γ] [Bornology δ]

/-
**LocallyBoundedMap.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyBoundedMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (LocallyBoundedMap α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
/-
**LocallyBoundedMap.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyBoundedMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyBoundedMapClass (LocallyBoundedMap α β) α β where
  comap_cobounded_le f := f.comap_cobounded_le'

@[ext]
/-
**LocallyBoundedMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：ext {f g : LocallyBoundedMap α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : LocallyBoundedMap α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `LocallyBoundedMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**LocallyBoundedMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `LocallyBoundedMap`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Bornology α] →       [inst
_1 : Bornology β] → (f : LocallyBoundedMap α β) → (f' : α → β) → f' = ⇑f → Local
lyBoundedMap α β
参数：f : LocallyBoundedMap α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `LocallyBoundedMap` with a new `toFun` equal to the old one. Useful to
 fix
definitional equalities.
-/
protected def copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : LocallyBoundedMap α β :=
  ⟨f', h.symm ▸ f.comap_cobounded_le'⟩

@[simp]
/-
**LocallyBoundedMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：coe_copy (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy
 f' h) = f'
参数：f : LocallyBoundedMap α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**LocallyBoundedMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：copy_eq (f : LocallyBoundedMap α β) (f' : α -> β) (h : f' = f) : f.copy f'
 h = f
参数：f : LocallyBoundedMap α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/-- Construct a `LocallyBoundedMap` from the fact that the function maps bounded sets to bounded
sets. -/
/-
**LocallyBoundedMap.ofMapBounded** 是 Mathlib 中的一个定义，位于命名空间 `LocallyBoundedMap`。
形式化陈述：ofMapBounded (f : α -> β) (h : forall ⦃s : Set α⦄, IsBounded s -> IsBounde
d (f '' s)) : LocallyBoundedMap α β
参数：f : α -> β；h : forall ⦃s : Set α⦄, IsBounded s -> IsBounded (f '' s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `LocallyBoundedMap` from the fact that the function maps bounded set
s to bounded
sets.
-/
def ofMapBounded (f : α → β) (h : ∀ ⦃s : Set α⦄, IsBounded s → IsBounded (f '' s)) :
    LocallyBoundedMap α β :=
  ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp]
/-
**LocallyBoundedMap.coe_ofMapBounded** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMa
p`。
形式化陈述：coe_ofMapBounded (f : α -> β) {h} : ⇑(ofMapBounded f h) = f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofMapBounded (f : α → β) {h} : ⇑(ofMapBounded f h) = f :=
  rfl

@[simp]
/-
**LocallyBoundedMap.ofMapBounded_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBounded
Map`。
形式化陈述：ofMapBounded_apply (f : α -> β) {h} (a : α) : ofMapBounded f h a = f a
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMapBounded_apply (f : α → β) {h} (a : α) : ofMapBounded f h a = f a :=
  rfl

variable (α)

/-- `id` as a `LocallyBoundedMap`. -/
/-
**LocallyBoundedMap.id** 是 Mathlib 中的一个定义，位于命名空间 `LocallyBoundedMap`。
形式化陈述：(α : Type u_2) → [inst : Bornology α] → LocallyBoundedMap α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `LocallyBoundedMap`.
-/
protected def id : LocallyBoundedMap α α :=
  ⟨id, comap_id.le⟩
/-
**LocallyBoundedMap.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyBoundedMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LocallyBoundedMap α α) :=
  ⟨LocallyBoundedMap.id α⟩

@[simp, norm_cast]
/-
**LocallyBoundedMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：coe_id : ⇑(LocallyBoundedMap.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(LocallyBoundedMap.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**LocallyBoundedMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：id_apply (a : α) : LocallyBoundedMap.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : LocallyBoundedMap.id α a = a :=
  rfl

/-- Composition of `LocallyBoundedMap`s as a `LocallyBoundedMap`. -/
/-
**LocallyBoundedMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `LocallyBoundedMap`。
形式化陈述：comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoun
dedMap α γ where toFun
参数：f : LocallyBoundedMap β γ；g : LocallyBoundedMap α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `LocallyBoundedMap`s as a `LocallyBoundedMap`.
-/
def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ where
  toFun := f ∘ g
  comap_cobounded_le' :=
    comap_comap.ge.trans <| (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'

@[simp]
/-
**LocallyBoundedMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.com
p g) = f ∘ g
参数：f : LocallyBoundedMap β γ；g : LocallyBoundedMap α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**LocallyBoundedMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α)
 : f.comp g a = f (g a)
参数：f : LocallyBoundedMap β γ；g : LocallyBoundedMap α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) :
    f.comp g a = f (g a) :=
  rfl

@[simp]
/-
**LocallyBoundedMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ) (h : Lo
callyBoundedMap α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : LocallyBoundedMap γ δ；g : LocallyBoundedMap β γ；h : LocallyBoundedMap α β
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
    (h : LocallyBoundedMap α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**LocallyBoundedMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f
参数：f : LocallyBoundedMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedMap.ext`：ext {f g : LocallyBoundedMap α β} (h : forall a, 
f a = g a) : f = g
-/
theorem comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**LocallyBoundedMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f
参数：f : LocallyBoundedMap α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedMap.ext`：ext {f g : LocallyBoundedMap α β} (h : forall a, 
f a = g a) : f = g
-/
theorem id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**LocallyBoundedMap.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β} (
hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedMap.ext`：ext {f g : LocallyBoundedMap α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congrArg (comp · _)⟩

@[simp]
/-
**LocallyBoundedMap.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedMap`。
形式化陈述：cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (h
g : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedMap.ext`：ext {f g : LocallyBoundedMap α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LocallyBoundedMap.comp_apply`：comp_apply (f : LocallyBoundedMap β γ) (g 
: LocallyBoundedMap α β) (a : α) : f.comp g a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end LocallyBoundedMap

