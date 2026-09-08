/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Functor
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Attr.Register

/-!
# Functors with two arguments

This file defines bifunctors.

A bifunctor is a function `F : Type* → Type* → Type*` along with a bimap which turns `F α β` into
`F α' β'` given two functions `α → α'` and `β → β'`. It further
* respects the identity: `bimap id id = id`
* composes in the obvious way: `(bimap f' g') ∘ (bimap f g) = bimap (f' ∘ f) (g' ∘ g)`

## Main declarations

* `Bifunctor`: A typeclass for the bare bimap of a bifunctor.
* `LawfulBifunctor`: A typeclass asserting this bimap respects the bifunctor laws.
-/

public section


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/-- Lawless bifunctor. This typeclass only holds the data for the bimap. -/
/-
**Bifunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Type u₀ → Type u₁ → Type u₂) → Type (max (max (u₀ + 1) (u₁ + 1)) u₂)
参数：max (u₀ + 1) (u₁ + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lawless bifunctor. This typeclass only holds the data for the bimap.
-/
class Bifunctor (F : Type u₀ → Type u₁ → Type u₂) where
  bimap : ∀ {α α' β β'}, (α → α') → (β → β') → F α β → F α' β'

export Bifunctor (bimap)

/-- Bifunctor. This typeclass asserts that a lawless `Bifunctor` is lawful. -/
/-
**LawfulBifunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u₀ → Type u₁ → Type u₂) → [Bifunctor F] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bifunctor. This typeclass asserts that a lawless `Bifunctor` is lawful.
-/
class LawfulBifunctor (F : Type u₀ → Type u₁ → Type u₂) [Bifunctor F] : Prop where
  id_bimap : ∀ {α β} (x : F α β), bimap id id x = x
  bimap_bimap :
    ∀ {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ → α₁) (f' : α₁ → α₂) (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α₀ β₀),
      bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x

export LawfulBifunctor (id_bimap bimap_bimap)

attribute [higher_order bimap_id_id] id_bimap

attribute [higher_order bimap_comp_bimap] bimap_bimap

export LawfulBifunctor (bimap_id_id bimap_comp_bimap)

variable {F : Type u₀ → Type u₁ → Type u₂} [Bifunctor F]

namespace Bifunctor

/-- Left map of a bifunctor. -/
/-
**Bifunctor.fst** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bifunctor`。
形式化陈述：fst {α α' β} (f : α -> α') : F α β -> F α' β
参数：f : α -> α'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left map of a bifunctor.
-/
abbrev fst {α α' β} (f : α → α') : F α β → F α' β :=
  bimap f id

/-- Right map of a bifunctor. -/
/-
**Bifunctor.snd** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bifunctor`。
形式化陈述：snd {α β β'} (f : β -> β') : F α β -> F α β'
参数：f : β -> β'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right map of a bifunctor.
-/
abbrev snd {α β β'} (f : β → β') : F α β → F α β' :=
  bimap id f

variable [LawfulBifunctor F]

@[higher_order fst_id]
/-
**Bifunctor.id_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：id_fst : forall {α β} (x : F α β), fst id x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBifunctor.id_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst : Bi
functor F} [self : LawfulBifunctor F] {α : Type u₀} {β : Type u₁}   (x : F α β),
 bimap id id x…
-/
theorem id_fst : ∀ {α β} (x : F α β), fst id x = x :=
  @id_bimap _ _ _

@[higher_order snd_id]
/-
**Bifunctor.id_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：id_snd : forall {α β} (x : F α β), snd id x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBifunctor.id_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst : Bi
functor F} [self : LawfulBifunctor F] {α : Type u₀} {β : Type u₁}   (x : F α β),
 bimap id id x…
-/
theorem id_snd : ∀ {α β} (x : F α β), snd id x = x :=
  @id_bimap _ _ _

@[higher_order fst_comp_fst]
/-
**Bifunctor.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：comp_fst {α₀ α₁ α₂ β} (f : α₀ -> α₁) (f' : α₁ -> α₂) (x : F α₀ β) : fst f'
 (fst f x) = fst (f' ∘ f) x
参数：f : α₀ -> α₁；f' : α₁ -> α₂；x : F α₀ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_fst {α₀ α₁ α₂ β} (f : α₀ → α₁) (f' : α₁ → α₂) (x : F α₀ β) :
    fst f' (fst f x) = fst (f' ∘ f) x := by simp [fst, bimap_bimap]

@[higher_order fst_comp_snd]
/-
**Bifunctor.fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：fst_snd {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀) : fst f
 (snd f' x) = bimap f f' x
参数：f : α₀ -> α₁；f' : β₀ -> β₁；x : F α₀ β₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_snd {α₀ α₁ β₀ β₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
    fst f (snd f' x) = bimap f f' x := by simp [fst, bimap_bimap]

@[higher_order snd_comp_fst]
/-
**Bifunctor.snd_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：snd_fst {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀) : snd f
' (fst f x) = bimap f f' x
参数：f : α₀ -> α₁；f' : β₀ -> β₁；x : F α₀ β₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_fst {α₀ α₁ β₀ β₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
    snd f' (fst f x) = bimap f f' x := by simp [snd, bimap_bimap]

@[higher_order snd_comp_snd]
/-
**Bifunctor.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：comp_snd {α β₀ β₁ β₂} (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α β₀) : snd g'
 (snd g x) = snd (g' ∘ g) x
参数：g : β₀ -> β₁；g' : β₁ -> β₂；x : F α β₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_snd {α β₀ β₁ β₂} (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α β₀) :
    snd g' (snd g x) = snd (g' ∘ g) x := by simp [snd, bimap_bimap]

attribute [functor_norm]
  bimap_bimap comp_snd comp_fst snd_comp_snd snd_comp_fst fst_comp_snd fst_comp_fst
  bimap_comp_bimap bimap_id_id fst_id snd_id

end Bifunctor

open Functor

/-
**Prod.bifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.bifunctor : Bifunctor Prod where bimap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.bifunctor : Bifunctor Prod where bimap := @Prod.map
/-
**Prod.lawfulBifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.lawfulBifunctor : LawfulBifunctor Prod where id_bimap _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.lawfulBifunctor : LawfulBifunctor Prod where
  id_bimap _ := rfl
  bimap_bimap _ _ _ _ _ := rfl
/-
**Bifunctor.const** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bifunctor.const : Bifunctor Const where bimap f _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bifunctor.const : Bifunctor Const where bimap f _ := f
/-
**LawfulBifunctor.const** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LawfulBifunctor.const : LawfulBifunctor Const where id_bimap _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LawfulBifunctor.const : LawfulBifunctor Const where
  id_bimap _ := rfl
  bimap_bimap _ _ _ _ _ := rfl
/-
**Bifunctor.flip** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bifunctor.flip : Bifunctor (flip F) where bimap {_α α' _β β'} f f' x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bifunctor.flip : Bifunctor (flip F) where
  bimap {_α α' _β β'} f f' x := (bimap f' f x : F β' α')

set_option backward.isDefEq.respectTransparency false in
/-
**LawfulBifunctor.flip** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LawfulBifunctor.flip [LawfulBifunctor F] : LawfulBifunctor (flip F) where 
id_bimap
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LawfulBifunctor.bimap_id_id`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α : Type u₀} {β : Type u₁},   bimap id
 id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
-/
instance LawfulBifunctor.flip [LawfulBifunctor F] : LawfulBifunctor (flip F) where
  id_bimap := by simp [bimap, functor_norm]
  bimap_bimap := by simp [bimap, functor_norm]
/-
**Sum.bifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.bifunctor : Bifunctor Sum where bimap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sum.bifunctor : Bifunctor Sum where bimap := @Sum.map
/-
**Sum.lawfulBifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.lawfulBifunctor : LawfulBifunctor Sum where id_bimap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sum.lawfulBifunctor : LawfulBifunctor Sum where
  id_bimap := by aesop
  bimap_bimap := by aesop

open Bifunctor
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) Bifunctor.functor {α} : Functor (F α) where map f x := snd f x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) Bifunctor.lawfulFunctor [LawfulBifunctor F] {α} :
    LawfulFunctor (F α) where
  id_map := by simp [Functor.map, functor_norm]
  comp_map := by simp [Functor.map, functor_norm]
  map_const := by simp [mapConst, Functor.map]

section Bicompl

variable (G : Type* → Type u₀) (H : Type* → Type u₁) [Functor G] [Functor H]

/-
**Function.bicompl.bifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.bicompl.bifunctor : Bifunctor (bicompl F G H) where bimap {_α α' 
_β β'} f f' x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.bicompl.bifunctor : Bifunctor (bicompl F G H) where
  bimap {_α α' _β β'} f f' x := (bimap (map f) (map f') x : F (G α') (H β'))

set_option backward.isDefEq.respectTransparency false in
/-
**Function.bicompl.lawfulBifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.bicompl.lawfulBifunctor [LawfulFunctor G] [LawfulFunctor H] [Lawf
ulBifunctor F] : LawfulBifunctor (bicompl F G H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Functor.map_id`：Functor.map_id : (id <$> ·) = (id : F α -> F α)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LawfulBifunctor.bimap_id_id`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α : Type u₀} {β : Type u₁},   bimap id
 id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
· 使用定理 `Functor.map_comp_map`：Functor.map_comp_map (f : α -> β) (g : β -> γ) : (
(g <$> ·) ∘ (f <$> ·) : F α -> F γ) = ((g ∘ f) <$> ·)
-/
instance Function.bicompl.lawfulBifunctor [LawfulFunctor G] [LawfulFunctor H] [LawfulBifunctor F] :
    LawfulBifunctor (bicompl F G H) := by
  constructor <;> intros <;> simp [bimap, map_id, map_comp_map, functor_norm]

end Bicompl

section Bicompr

variable (G : Type u₂ → Type*) [Functor G]

/-
**Function.bicompr.bifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.bicompr.bifunctor : Bifunctor (bicompr G F) where bimap {_α α' _β
 β'} f f' x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Function.bicompr.bifunctor : Bifunctor (bicompr G F) where
  bimap {_α α' _β β'} f f' x := (map (bimap f f') x : G (F α' β'))

set_option backward.isDefEq.respectTransparency false in
/-
**Function.bicompr.lawfulBifunctor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.bicompr.lawfulBifunctor [LawfulFunctor G] [LawfulBifunctor F] : L
awfulBifunctor (bicompr G F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulBifunctor.bimap_id_id`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α : Type u₀} {β : Type u₁},   bimap id
 id = id
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulBifunctor.bimap_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst :
 Bifunctor F} [self : LawfulBifunctor F] {α₀ α₁ α₂ : Type u₀}   {β₀ β₁ β₂ : Type
 u₁} (f : α₀ → α₁…
-/
instance Function.bicompr.lawfulBifunctor [LawfulFunctor G] [LawfulBifunctor F] :
    LawfulBifunctor (bicompr G F) := by
  constructor <;> intros <;> simp [bimap, functor_norm]

end Bicompr

