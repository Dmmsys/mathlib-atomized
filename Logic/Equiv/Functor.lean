/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Kim Morrison
-/
module

public import Mathlib.Control.Bifunctor
public import Mathlib.Logic.Equiv.Defs

/-!
# Functor and bifunctors can be applied to `Equiv`s.

We define
```lean
def Functor.mapEquiv (f : Type u → Type v) [Functor f] [LawfulFunctor f] :
    α ≃ β → f α ≃ f β
```
and
```lean
def Bifunctor.mapEquiv (F : Type u → Type v → Type w) [Bifunctor F] [LawfulBifunctor F] :
    α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/

@[expose] public section


universe u v w

variable {α β : Type u}

open Equiv

namespace Functor

variable (f : Type u → Type v) [Functor f] [LawfulFunctor f]

/-- Apply a functor to an `Equiv`. -/
/-
**Functor.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：mapEquiv (h : α ≃ β) : f α ≃ f β where toFun
参数：h : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Apply a functor to an `Equiv`.
-/
def mapEquiv (h : α ≃ β) : f α ≃ f β where
  toFun := map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]

@[simp]
/-
**Functor.mapEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Functor`。
形式化陈述：mapEquiv_apply (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map 
h x
参数：h : α ≃ β；x : f α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_apply (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map h x :=
  rfl

@[simp]
/-
**Functor.mapEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Functor`。
形式化陈述：mapEquiv_symm_apply (h : α ≃ β) (y : f β) : (mapEquiv f h : f α ≃ f β).sym
m y = map h.symm y
参数：h : α ≃ β；y : f β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mapEquiv_symm_apply (h : α ≃ β) (y : f β) :
    (mapEquiv f h : f α ≃ f β).symm y = map h.symm y :=
  rfl

@[simp]
/-
**Functor.mapEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Functor`。
形式化陈述：mapEquiv_refl : mapEquiv f (Equiv.refl α) = Equiv.refl (f α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
-/
theorem mapEquiv_refl : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
  ext x
  simp only [mapEquiv_apply, refl_apply]
  exact LawfulFunctor.id_map x

end Functor

namespace Bifunctor

variable {α' β' : Type v} (F : Type u → Type v → Type w) [Bifunctor F] [LawfulBifunctor F]

/-- Apply a bifunctor to a pair of `Equiv`s. -/
/-
**Bifunctor.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Bifunctor`。
形式化陈述：mapEquiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' where toFun
参数：h : α ≃ β；h' : α' ≃ β'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Apply a bifunctor to a pair of `Equiv`s.
-/
def mapEquiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' where
  toFun := bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv x := by simp [bimap_bimap, id_bimap]
  right_inv x := by simp [bimap_bimap, id_bimap]

@[simp]
/-
**Bifunctor.mapEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：mapEquiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') : (mapEquiv F h h' 
: F α α' ≃ F β β') x = bimap h h' x
参数：h : α ≃ β；h' : α' ≃ β'；x : F α α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
    (mapEquiv F h h' : F α α' ≃ F β β') x = bimap h h' x :=
  rfl

@[simp]
/-
**Bifunctor.mapEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：mapEquiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') : (mapEquiv F 
h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y
参数：h : α ≃ β；h' : α' ≃ β'；y : F β β'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mapEquiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
    (mapEquiv F h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y :=
  rfl

@[simp]
/-
**Bifunctor.mapEquiv_refl_refl** 是 Mathlib 中的一个定理，位于命名空间 `Bifunctor`。
形式化陈述：mapEquiv_refl_refl : mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.ref
l (F α α')
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
· 使用定理 `LawfulBifunctor.id_bimap`：∀ {F : Type u₀ → Type u₁ → Type u₂} {inst : Bi
functor F} [self : LawfulBifunctor F] {α : Type u₀} {β : Type u₁}   (x : F α β),
 bimap id id x…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapEquiv_refl_refl : mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.refl (F α α') := by
  ext x
  simp [id_bimap]

end Bifunctor

