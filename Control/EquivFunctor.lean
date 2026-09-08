/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Convert

/-!
# Functions functorial with respect to equivalences

An `EquivFunctor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/

@[expose] public section


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/-- An `EquivFunctor` is only functorial with respect to equivalences.

To construct an `EquivFunctor`, it suffices to supply just the function `f α → f β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence that
this function is part of an equivalence, provided by `EquivFunctor.mapEquiv`.
-/
/-
**EquivFunctor** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：EquivFunctor (f : Type u₀ -> Type u₁) where /-- The action of `f` on isomo
rphisms. -/ map : forall {α β}, α ≃ β -> f α -> f β /-- `map` of `f` preserves t
he identity morphism. -/ map_refl' : forall α, map (Equiv.refl α) = @id (f α)
参数：f : Type u₀ -> Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `EquivFunctor` is only functorial with respect to equivalences.

To construct an `EquivFunctor`, it suffices to supply just the function `f α → f
 β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence
 that
this function is part of an equivalence, provided by `EquivFunctor.mapEquiv`.
-/
class EquivFunctor (f : Type u₀ → Type u₁) where
  /-- The action of `f` on isomorphisms. -/
  map : ∀ {α β}, α ≃ β → f α → f β
  /-- `map` of `f` preserves the identity morphism. -/
  map_refl' : ∀ α, map (Equiv.refl α) = @id (f α) := by rfl
  /-- `map` is functorial on equivalences. -/
  map_trans' : ∀ {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k := by rfl

attribute [simp] EquivFunctor.map_refl'

namespace EquivFunctor

section

variable (f : Type u₀ → Type u₁) [EquivFunctor f] {α β : Type u₀} (e : α ≃ β)

/-- An `EquivFunctor` in fact takes every equiv to an equiv. -/
/-
**EquivFunctor.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `EquivFunctor`。
形式化陈述：mapEquiv : f α ≃ f β where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An `EquivFunctor` in fact takes every equiv to an equiv.
-/
def mapEquiv : f α ≃ f β where
  toFun := EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert! (congr_fun (EquivFunctor.map_trans' e e.symm) x).symm
    simp
  right_inv y := by
    convert! (congr_fun (EquivFunctor.map_trans' e.symm e) y).symm
    simp

@[simp]
/-
**EquivFunctor.mapEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `EquivFunctor`。
形式化陈述：mapEquiv_apply (x : f α) : mapEquiv f e x = EquivFunctor.map e x
参数：x : f α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_apply (x : f α) : mapEquiv f e x = EquivFunctor.map e x :=
  rfl
/-
**EquivFunctor.mapEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `EquivFunctor`。
形式化陈述：mapEquiv_symm_apply (y : f β) : (mapEquiv f e).symm y = EquivFunctor.map e
.symm y
参数：y : f β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mapEquiv_symm_apply (y : f β) : (mapEquiv f e).symm y = EquivFunctor.map e.symm y :=
  rfl

@[simp]
/-
**EquivFunctor.mapEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `EquivFunctor`。
形式化陈述：mapEquiv_refl (α) : mapEquiv f (Equiv.refl α) = Equiv.refl (f α)
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `EquivFunctor.map_refl'`：∀ {f : Type u₀ → Type u₁} [self : EquivFunctor f
] (α : Type u₀), EquivFunctor.map (Equiv.refl α) = id
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapEquiv_refl (α) : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
  ext; simp [mapEquiv]

@[simp]
/-
**EquivFunctor.mapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `EquivFunctor`。
形式化陈述：mapEquiv_symm : (mapEquiv f e).symm = mapEquiv f e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `EquivFunctor.mapEquiv_symm_apply`：mapEquiv_symm_apply (y : f β) : (mapEq
uiv f e).symm y = EquivFunctor.map e.symm y
-/
theorem mapEquiv_symm : (mapEquiv f e).symm = mapEquiv f e.symm :=
  Equiv.ext <| mapEquiv_symm_apply f e

set_option backward.isDefEq.respectTransparency false in
/-- The composition of `mapEquiv`s is carried over the `EquivFunctor`.
For plain `Functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp]
/-
**EquivFunctor.mapEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `EquivFunctor`。
形式化陈述：mapEquiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) : (mapEquiv f ab).t
rans (mapEquiv f bc) = mapEquiv f (ab.trans bc)
参数：ab : α ≃ β；bc : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `EquivFunctor.map_trans'`：∀ {f : Type u₀ → Type u₁} [self : EquivFunctor 
f] {α β γ : Type u₀} (k : α ≃ β) (h : β ≃ γ),   EquivFunctor.map (k.trans h) = E
quivFunctor.m…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of `mapEquiv`s is carried over the `EquivFunctor`.
For plain `Functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
theorem mapEquiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) :
    (mapEquiv f ab).trans (mapEquiv f bc) = mapEquiv f (ab.trans bc) :=
  Equiv.ext fun x => by simp [mapEquiv, map_trans']

end

/-
**EquivFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `EquivFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ofLawfulFunctor (f : Type u₀ → Type u₁) [Functor f] [LawfulFunctor f] :
    EquivFunctor f where
  map {_ _} e := Functor.map e
  map_refl' α := by
    ext
    apply LawfulFunctor.id_map
  map_trans' {α β γ} k h := by
    ext x
    apply LawfulFunctor.comp_map k h x
/-
**EquivFunctor.mapEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `EquivFunctor.mapEqu
iv`。
形式化陈述：∀ (f : Type u₀ → Type u₁) [inst : Applicative f] [inst_1 : LawfulApplicati
ve f] {α β : Type u₀},   (∀ (γ : Type u₀), Function.Injective pure) → Function.I
njective (EquivFunctor.mapEquiv f)
参数：f : Type u₀ → Type u₁；∀ (γ : Type u₀), Function.Injective pure；EquivFunctor.m
apEquiv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
-/
theorem mapEquiv.injective (f : Type u₀ → Type u₁)
    [Applicative f] [LawfulApplicative f] {α β : Type u₀}
    (h : ∀ γ, Function.Injective (pure : γ → f γ)) :
      Function.Injective (@EquivFunctor.mapEquiv f _ α β) :=
  fun e₁ e₂ H =>
    Equiv.ext fun x => h β (by simpa [EquivFunctor.map] using Equiv.congr_fun H (pure x))

end EquivFunctor

