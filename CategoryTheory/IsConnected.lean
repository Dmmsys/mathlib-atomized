/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Connected category

Define a connected category as a _nonempty_ category for which every functor
to a discrete category is isomorphic to the constant functor.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

We give some equivalent definitions:
- A nonempty category for which every functor to a discrete category is
  constant on objects.
  See `any_functor_const_on_obj` and `Connected.of_any_functor_const_on_obj`.
- A nonempty category for which every function `F` for which the presence of a
  morphism `f : j₁ ⟶ j₂` implies `F j₁ = F j₂` must be constant everywhere.
  See `constant_of_preserves_morphisms` and `Connected.of_constant_of_preserves_morphisms`.
- A nonempty category for which any subset of its elements containing the
  default and closed under morphisms is everything.
  See `induct_on_objects` and `Connected.of_induct`.
- A nonempty category for which every object is related under the reflexive
  transitive closure of the relation "there is a morphism in some direction
  from `j₁` to `j₂`".
  See `connected_zigzag` and `zigzag_connected`.
- A nonempty category for which for any two objects there is a sequence of
  morphisms (some reversed) from one to the other.
  See `exists_zigzag'` and `connected_of_zigzag`.

We also prove the result that the functor given by `(X × -)` preserves any
connected limit. That is, any limit of shape `J` where `J` is a connected
category is preserved by the functor `(X × -)`. This appears in `CategoryTheory.Limits.Connected`.
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory.Category CategoryTheory.Functor

open Opposite

namespace CategoryTheory

/-- A possibly empty category for which every functor to a discrete category is constant.
-/
/-
**CategoryTheory.IsPreconnected** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(J : Type u₁) → [CategoryTheory.Category.{v₁, u₁} J] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A possibly empty category for which every functor to a discrete category is cons
tant.
-/
class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant :
    ∀ {α : Type u₁} (F : J ⥤ Discrete α) (j : J), Nonempty (F ≅ (Functor.const J).obj (F.obj j))

attribute [inherit_doc IsPreconnected] IsPreconnected.iso_constant

/-- We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits. -/
@[stacks 002S]
/-
**CategoryTheory.IsConnected** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(J : Type u₁) → [CategoryTheory.Category.{v₁, u₁} J] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits.
-/
class IsConnected (J : Type u₁) [Category.{v₁} J] : Prop extends IsPreconnected J where
  [is_nonempty : Nonempty J]

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]

namespace IsPreconnected.IsoConstantAux

set_option backward.privateInPublic true in
/-- Implementation detail of `isoConstant`. -/
/-
**CategoryTheory.IsPreconnected.IsoConstantAux.liftToDiscrete** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.IsPreconnected.IsoConstantAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail of `isoConstant`.
-/
private def liftToDiscrete {α : Type u₂} (F : J ⥤ Discrete α) : J ⥤ Discrete J where
  obj j := have := Nonempty.intro j
    Discrete.mk (Function.invFun F.obj (F.obj j))
  map {j _} f := have := Nonempty.intro j
    ⟨⟨congr_arg (Function.invFun F.obj) (Discrete.ext (Discrete.eq_of_hom (F.map f)))⟩⟩

set_option backward.privateInPublic true in
/-- Implementation detail of `isoConstant`. -/
/-
**CategoryTheory.IsPreconnected.IsoConstantAux.factorThroughDiscrete** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.IsPreconnected.IsoConstantAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail of `isoConstant`.
-/
private def factorThroughDiscrete {α : Type u₂} (F : J ⥤ Discrete α) :
    liftToDiscrete F ⋙ Discrete.functor F.obj ≅ F :=
  NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by cat_disch)

end IsPreconnected.IsoConstantAux

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `J` is connected, any functor `F : J ⥤ Discrete α` is isomorphic to
the constant functor with value `F.obj j` (for any choice of `j`).
-/
/-
**CategoryTheory.isoConstant** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isoConstant [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j : J) 
: F ≅ (Functor.const J).obj (F.obj j)
参数：F : J ⥤ Discrete α；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is connected, any functor `F : J ⥤ Discrete α` is isomorphic to
the constant functor with value `F.obj j` (for any choice of `j`).
-/
def isoConstant [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j : J) :
    F ≅ (Functor.const J).obj (F.obj j) :=
  (IsPreconnected.IsoConstantAux.factorThroughDiscrete F).symm
    ≪≫ isoWhiskerRight (IsPreconnected.iso_constant _ j).some _
    ≪≫ NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by simp)

/-- If `J` is connected, any functor to a discrete category is constant on objects.
The converse is given in `IsConnected.of_any_functor_const_on_obj`.
-/
/-
**CategoryTheory.any_functor_const_on_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：any_functor_const_on_obj [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discret
e α) (j j' : J) : F.obj j = F.obj j'
参数：F : J ⥤ Discrete α；j j' : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y

--- 原说明 ---
If `J` is connected, any functor to a discrete category is constant on objects.
The converse is given in `IsConnected.of_any_functor_const_on_obj`.
-/
theorem any_functor_const_on_obj [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j j' : J) :
    F.obj j = F.obj j' := by
  ext; exact ((isoConstant F j').hom.app j).down.1

/-- If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
/-
**CategoryTheory.IsPreconnected.of_any_functor_const_on_obj** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.IsPreconnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Typ
e u₁} (F : CategoryTheory.Functor J (CategoryTheory.Discrete α)) (j j' : J), F.o
bj j = F.obj j') →     CategoryTheory.IsPreconnected J
参数：∀ {α : Type u₁} (F : CategoryTheory.Functor J (CategoryTheory.Discrete α)) (j
 j' : J), F.obj j = F.obj j'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
theorem IsPreconnected.of_any_functor_const_on_obj
    (h : ∀ {α : Type u₁} (F : J ⥤ Discrete α), ∀ j j' : J, F.obj j = F.obj j') :
    IsPreconnected J where
  iso_constant := fun F j' => ⟨NatIso.ofComponents fun j => eqToIso (h F j j')⟩
/-
**CategoryTheory.IsPreconnected.prod** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPreconnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   [CategoryTheory.IsPreconnected J
] [CategoryTheory.IsPreconnected K], CategoryTheory.IsPreconnected (J × K)
参数：J × K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreconnected.of_any_functor_const_on_obj`：∀ {J : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Type u₁} (F : Category
Theory.Functor J (CategoryTheory.Discrete α)) (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.any_functor_const_on_obj`：any_functor_const_on_obj [IsPre
connected J] {α : Type u₂} (F : J ⥤ Discrete α) (j j' : J) : F.obj j = F.obj j'
-/
instance IsPreconnected.prod [IsPreconnected J] [IsPreconnected K] : IsPreconnected (J × K) := by
  refine .of_any_functor_const_on_obj (fun {a} F ⟨j, k⟩ ⟨j', k'⟩ => ?_)
  exact (any_functor_const_on_obj (Prod.sectL J k ⋙ F) j j').trans
    (any_functor_const_on_obj (Prod.sectR j' K ⋙ F) k k')
/-
**CategoryTheory.IsConnected.prod** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsCo
nnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {K : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   [CategoryTheory.IsConnected J] [
CategoryTheory.IsConnected K], CategoryTheory.IsConnected (J × K)
参数：J × K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreconnected.prod`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 K]   [CategoryTheory.Is…
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
-/
instance IsConnected.prod [IsConnected J] [IsConnected K] : IsConnected (J × K) where

/-- If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
/-
**CategoryTheory.IsConnected.of_any_functor_const_on_obj** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.IsConnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J], 
  (∀ {α : Type u₁} (F : CategoryTheory.Functor J (CategoryTheory.Discrete α)) (j
 j' : J), F.obj j = F.obj j') →     CategoryTheory.IsConnected J
参数：∀ {α : Type u₁} (F : CategoryTheory.Functor J (CategoryTheory.Discrete α)) (j
 j' : J), F.obj j = F.obj j'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreconnected.of_any_functor_const_on_obj`：∀ {J : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Type u₁} (F : Category
Theory.Functor J (CategoryTheory.Discrete α)) (…

--- 原说明 ---
If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
theorem IsConnected.of_any_functor_const_on_obj [Nonempty J]
    (h : ∀ {α : Type u₁} (F : J ⥤ Discrete α), ∀ j j' : J, F.obj j = F.obj j') : IsConnected J :=
  { IsPreconnected.of_any_functor_const_on_obj h with }

/-- If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, we have that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `IsConnected.of_constant_of_preserves_morphisms`
-/
/-
**CategoryTheory.constant_of_preserves_morphisms** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：constant_of_preserves_morphisms [IsPreconnected J] {α : Type u₂} (F : J ->
 α) (h : forall (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J) : F j = F j'
参数：F : J -> α；h : forall (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂；j j' : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Discrete.mk.injEq`：∀ {α : Type u₁} (as as_1 : α), ({ as :
= as } = { as := as_1 }) = (as = as_1)
· 使用定理 `CategoryTheory.any_functor_const_on_obj`：any_functor_const_on_obj [IsPre
connected J] {α : Type u₂} (F : J ⥤ Discrete α) (j j' : J) : F.obj j = F.obj j'

--- 原说明 ---
If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, we have that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `IsConnected.of_constant_of_preserves_morphisms`
-/
theorem constant_of_preserves_morphisms [IsPreconnected J] {α : Type u₂} (F : J → α)
    (h : ∀ (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J) : F j = F j' := by
  simpa using
    any_functor_const_on_obj
      { obj := Discrete.mk ∘ F
        map := fun f => eqToHom (by ext; exact h _ _ f) }
      j j'

/-- If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, there exists `a` such that `F j = a`
holds for any `j`. See `constant_of_preserves_morphisms` for a different
formulation of the fact that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `IsConnected.of_constant_of_preserves_morphisms`
-/
/-
**CategoryTheory.constant_of_preserves_morphisms'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：constant_of_preserves_morphisms' [IsConnected J] {α : Type u₂} (F : J -> α
) (h : forall (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) : exists (a : α), forall (
j : J), F j = a
参数：F : J -> α；h : forall (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用定理 `CategoryTheory.constant_of_preserves_morphisms`：constant_of_preserves_mo
rphisms [IsPreconnected J] {α : Type u₂} (F : J -> α) (h : forall (j₁ j₂ : J) (_
 : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J)…
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J

--- 原说明 ---
If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, there exists `a` such that `F j = a`
holds for any `j`. See `constant_of_preserves_morphisms` for a different
formulation of the fact that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `IsConnected.of_constant_of_preserves_morphisms`
-/
theorem constant_of_preserves_morphisms' [IsConnected J] {α : Type u₂} (F : J → α)
    (h : ∀ (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) :
    ∃ (a : α), ∀ (j : J), F j = a :=
  ⟨F (Classical.arbitrary _), fun _ ↦ constant_of_preserves_morphisms _ h _ _⟩

/-- `J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
/-
**CategoryTheory.IsPreconnected.of_constant_of_preserves_morphisms** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.IsPreconnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Typ
e u₁} (F : J → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ (j j' : J), F 
j = F j') →     CategoryTheory.IsPreconnected J
参数：∀ {α : Type u₁} (F : J → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ (
j j' : J), F j = F j'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreconnected.of_any_functor_const_on_obj`：∀ {J : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Type u₁} (F : Category
Theory.Functor J (CategoryTheory.Discrete α)) (…
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `CategoryTheory.Discrete.eq_of_hom`：eq_of_hom {X Y : Discrete α} (i : X ⟶
 Y) : X.as = Y.as

--- 原说明 ---
`J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
theorem IsPreconnected.of_constant_of_preserves_morphisms
    (h : ∀ {α : Type u₁} (F : J → α),
      (∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ j j' : J, F j = F j') :
    IsPreconnected J :=
  IsPreconnected.of_any_functor_const_on_obj fun F =>
    h F.obj fun f => by ext; exact Discrete.eq_of_hom (F.map f)

/-- `J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
/-
**CategoryTheory.IsConnected.of_constant_of_preserves_morphisms** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.IsConnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J], 
  (∀ {α : Type u₁} (F : J → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ (
j j' : J), F j = F j') →     CategoryTheory.IsConnected J
参数：∀ {α : Type u₁} (F : J → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ (
j j' : J), F j = F j'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreconnected.of_constant_of_preserves_morphisms`：∀ {J :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Type u₁} (F : J
 → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ …

--- 原说明 ---
`J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
theorem IsConnected.of_constant_of_preserves_morphisms [Nonempty J]
    (h : ∀ {α : Type u₁} (F : J → α),
      (∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ j j' : J, F j = F j') :
    IsConnected J :=
  { IsPreconnected.of_constant_of_preserves_morphisms h with }

/-- An inductive-like property for the objects of a connected category.
If the set `p` is nonempty, and `p` is closed under morphisms of `J`,
then `p` contains all of `J`.

The converse is given in `IsConnected.of_induct`.
-/
/-
**CategoryTheory.induct_on_objects** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：induct_on_objects [IsPreconnected J] (p : Set J) {j₀ : J} (h0 : j₀ in p) (
h1 : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ in p ↔ j₂ in p) (j : J) : j in p
参数：p : Set J；h0 : j₀ in p；h1 : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ in p ↔ j₂ in
 p；j : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.constant_of_preserves_morphisms`：constant_of_preserves_mo
rphisms [IsPreconnected J] {α : Type u₂} (F : J -> α) (h : forall (j₁ j₂ : J) (_
 : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J)…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
An inductive-like property for the objects of a connected category.
If the set `p` is nonempty, and `p` is closed under morphisms of `J`,
then `p` contains all of `J`.

The converse is given in `IsConnected.of_induct`.
-/
theorem induct_on_objects [IsPreconnected J] (p : Set J) {j₀ : J} (h0 : j₀ ∈ p)
    (h1 : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) (j : J) : j ∈ p := by
  let aux (j₁ j₂ : J) (f : j₁ ⟶ j₂) := congrArg ULift.up <| (h1 f).eq
  injection constant_of_preserves_morphisms (fun k => ULift.up.{u₁} (k ∈ p)) aux j j₀ with i
  rwa [i]

/--
If any maximal connected component containing some element j₀ of J is all of J, then J is connected.

The converse of `induct_on_objects`.
-/
/-
**CategoryTheory.IsConnected.of_induct** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsConnected`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₀ : J},   (∀
 (p : Set J), j₀ ∈ p → (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ (j : J
), j ∈ p) →     CategoryTheory.IsConnected J
参数：∀ (p : Set J), j₀ ∈ p → (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ (j
 : J), j ∈ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.of_constant_of_preserves_morphisms`：∀ {J : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J],   (∀ {α : Type 
u₁} (F : J → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If any maximal connected component containing some element j₀ of J is all of J, 
then J is connected.

The converse of `induct_on_objects`.
-/
theorem IsConnected.of_induct {j₀ : J}
    (h : ∀ p : Set J, j₀ ∈ p → (∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ j : J, j ∈ p) :
    IsConnected J :=
  have := Nonempty.intro j₀
  IsConnected.of_constant_of_preserves_morphisms fun {α} F a => by
    have w := h { j | F j = F j₀ } rfl (fun {j₁} {j₂} f => by
      change F j₁ = F j₀ ↔ F j₂ = F j₀
      simp [a f])
    intro j j'
    rw [w j, w j']

attribute [local instance] uliftCategory in
/-- Lifting the universe level of morphisms and objects preserves connectedness. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifting the universe level of morphisms and objects preserves connectedness.
-/
instance [hc : IsConnected J] : IsConnected (ULiftHom.{v₂} (ULift.{u₂} J)) := by
  apply IsConnected.of_induct
  · rintro p hj₀ h ⟨j⟩
    let p' : Set J := {j : J | ⟨j⟩ ∈ p}
    have hj₀' : Classical.choice hc.is_nonempty ∈ p' := by
      simp only [p']
      exact hj₀
    apply induct_on_objects p' hj₀' fun f => h ((ULiftHomULiftCategory.equiv J).functor.map f)

/-- Another induction principle for `IsPreconnected J`:
given a type family `Z : J → Sort*` and
a rule for transporting in *both* directions along a morphism in `J`,
we can transport an `x : Z j₀` to a point in `Z j` for any `j`.
-/
/-
**CategoryTheory.isPreconnected_induction** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isPreconnected_induction [IsPreconnected J] (Z : J -> Sort*) (h₁ : forall 
{j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₁ -> Z j₂) (h₂ : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂),
 Z j₂ -> Z j₁) {j₀ : J} (x : Z j₀) (j : J) : Nonempty (Z j)
参数：Z : J -> Sort*；h₁ : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₁ -> Z j₂；h₂ : foral
l {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₂ -> Z j₁；x : Z j₀；j : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.induct_on_objects`：induct_on_objects [IsPreconnected J] (
p : Set J) {j₀ : J} (h0 : j₀ in p) (h1 : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ in
 p ↔ j₂ in p) (j : J) …

--- 原说明 ---
Another induction principle for `IsPreconnected J`:
given a type family `Z : J → Sort*` and
a rule for transporting in *both* directions along a morphism in `J`,
we can transport an `x : Z j₀` to a point in `Z j` for any `j`.
-/
theorem isPreconnected_induction [IsPreconnected J] (Z : J → Sort*)
    (h₁ : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₁ → Z j₂) (h₂ : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₂ → Z j₁)
    {j₀ : J} (x : Z j₀) (j : J) : Nonempty (Z j) :=
  (induct_on_objects { j | Nonempty (Z j) } ⟨x⟩
      (fun f => ⟨by rintro ⟨y⟩; exact ⟨h₁ f y⟩, by rintro ⟨y⟩; exact ⟨h₂ f y⟩⟩)
      j :)

/-- If `J` and `K` are equivalent, then if `J` is preconnected then `K` is as well. -/
/-
**CategoryTheory.isPreconnected_of_equivalent** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：isPreconnected_of_equivalent {K : Type u₂} [Category.{v₂} K] [IsPreconnect
ed J] (e : J ≌ K) : IsPreconnected K where iso_constant F k
参数：e : J ≌ K。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` and `K` are equivalent, then if `J` is preconnected then `K` is as well.
-/
theorem isPreconnected_of_equivalent {K : Type u₂} [Category.{v₂} K] [IsPreconnected J]
    (e : J ≌ K) : IsPreconnected K where
  iso_constant F k :=
    ⟨calc
        F ≅ e.inverse ⋙ e.functor ⋙ F := (e.invFunIdAssoc F).symm
        _ ≅ e.inverse ⋙ (Functor.const J).obj ((e.functor ⋙ F).obj (e.inverse.obj k)) :=
          isoWhiskerLeft e.inverse (isoConstant (e.functor ⋙ F) (e.inverse.obj k))
        _ ≅ e.inverse ⋙ (Functor.const J).obj (F.obj k) :=
          isoWhiskerLeft _ ((F ⋙ Functor.const J).mapIso (e.counitIso.app k))
        _ ≅ (Functor.const K).obj (F.obj k) := NatIso.ofComponents fun _ => Iso.refl _⟩
/-
**CategoryTheory.isPreconnected_iff_of_equivalence** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isPreconnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌
 K) : IsPreconnected J ↔ IsPreconnected K
参数：e : J ≌ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isPreconnected_of_equivalent`：isPreconnected_of_equivalen
t {K : Type u₂} [Category.{v₂} K] [IsPreconnected J] (e : J ≌ K) : IsPreconnecte
d K where iso_constant F k
-/
lemma isPreconnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) :
    IsPreconnected J ↔ IsPreconnected K :=
  ⟨fun _ => isPreconnected_of_equivalent e, fun _ => isPreconnected_of_equivalent e.symm⟩

/-- If `J` and `K` are equivalent, then if `J` is connected then `K` is as well. -/
/-
**CategoryTheory.isConnected_of_equivalent** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isConnected_of_equivalent {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsC
onnected J] : IsConnected K
参数：e : J ≌ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isPreconnected_of_equivalent`：isPreconnected_of_equivalen
t {K : Type u₂} [Category.{v₂} K] [IsPreconnected J] (e : J ≌ K) : IsPreconnecte
d K where iso_constant F k
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J

--- 原说明 ---
If `J` and `K` are equivalent, then if `J` is connected then `K` is as well.
-/
theorem isConnected_of_equivalent {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] :
    IsConnected K :=
  { is_nonempty := Nonempty.map e.functor.obj (by infer_instance)
    toIsPreconnected := isPreconnected_of_equivalent e }
/-
**CategoryTheory.isConnected_iff_of_equivalence** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isConnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K)
 : IsConnected J ↔ IsConnected K
参数：e : J ≌ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
-/
lemma isConnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) :
    IsConnected J ↔ IsConnected K :=
  ⟨fun _ => isConnected_of_equivalent e, fun _ => isConnected_of_equivalent e.symm⟩

/-- If `J` is preconnected, then `Jᵒᵖ` is preconnected as well. -/
/-
**CategoryTheory.isPreconnected_op** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isPreconnected_op [IsPreconnected J] : IsPreconnected Jᵒᵖ where iso_consta
nt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `CategoryTheory.Discrete.eq_of_hom`：eq_of_hom {X Y : Discrete α} (i : X ⟶
 Y) : X.as = Y.as
· 使用定理 `CategoryTheory.IsPreconnected.iso_constant`：∀ {J : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsPreconnected J] {α : Ty
pe u₁}   (F : CategoryTheory.Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If `J` is preconnected, then `Jᵒᵖ` is preconnected as well.
-/
instance isPreconnected_op [IsPreconnected J] : IsPreconnected Jᵒᵖ where
  iso_constant := fun {α} F X =>
    ⟨NatIso.ofComponents fun Y =>
      eqToIso (Discrete.ext (Discrete.eq_of_hom ((Nonempty.some
        (IsPreconnected.iso_constant (F.rightOp ⋙ (Discrete.opposite α).functor) (unop X))).app
          (unop Y)).hom))⟩

/-- If `J` is connected, then `Jᵒᵖ` is connected as well. -/
/-
**CategoryTheory.isConnected_op** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isConnected_op [IsConnected J] : IsConnected Jᵒᵖ where is_nonempty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J

--- 原说明 ---
If `J` is connected, then `Jᵒᵖ` is connected as well.
-/
instance isConnected_op [IsConnected J] : IsConnected Jᵒᵖ where
  is_nonempty := Nonempty.intro (op (Classical.arbitrary J))
/-
**CategoryTheory.isPreconnected_of_isPreconnected_op** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：isPreconnected_of_isPreconnected_op [IsPreconnected Jᵒᵖ] : IsPreconnected 
J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isPreconnected_of_equivalent`：isPreconnected_of_equivalen
t {K : Type u₂} [Category.{v₂} K] [IsPreconnected J] (e : J ≌ K) : IsPreconnecte
d K where iso_constant F k
-/
theorem isPreconnected_of_isPreconnected_op [IsPreconnected Jᵒᵖ] : IsPreconnected J :=
  isPreconnected_of_equivalent (opOpEquivalence J)
/-
**CategoryTheory.isConnected_of_isConnected_op** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：isConnected_of_isConnected_op [IsConnected Jᵒᵖ] : IsConnected J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
-/
theorem isConnected_of_isConnected_op [IsConnected Jᵒᵖ] : IsConnected J :=
  isConnected_of_equivalent (opOpEquivalence J)

variable (J) in
@[simp]
/-
**CategoryTheory.isConnected_op_iff_isConnected** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isConnected_op_iff_isConnected : IsConnected Jᵒᵖ ↔ IsConnected J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_isConnected_op`：isConnected_of_isConnected
_op [IsConnected Jᵒᵖ] : IsConnected J
-/
theorem isConnected_op_iff_isConnected : IsConnected Jᵒᵖ ↔ IsConnected J :=
  ⟨fun _ => isConnected_of_isConnected_op, fun _ => isConnected_op⟩

/-- j₁ and j₂ are related by `Zag` if there is a morphism between them. -/
/-
**CategoryTheory.Zag** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Zag (j₁ j₂ : J) : Prop
参数：j₁ j₂ : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
j₁ and j₂ are related by `Zag` if there is a morphism between them.
-/
def Zag (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)
/-
**CategoryTheory.Zag.refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] (X : J), Categ
oryTheory.Zag X X
参数：X : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[refl] theorem Zag.refl (X : J) : Zag X X := Or.inl ⟨𝟙 _⟩
/-
**CategoryTheory.zag_symm** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：zag_symm : Std.Symm (@Zag J _) where symm _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
instance zag_symm : Std.Symm (@Zag J _) where
  symm _ _ h := h.symm

@[deprecated (since := "2026-06-10")] alias zag_symmetric := zag_symm
/-
**CategoryTheory.Zag.symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J},  
 CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zag j₂ j₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
@[symm] theorem Zag.symm {j₁ j₂ : J} (h : Zag j₁ j₂) : Zag j₂ j₁ := symm_of _ h
/-
**CategoryTheory.Zag.of_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J} (f
 : j₁ ⟶ j₂), CategoryTheory.Zag j₁ j₂
参数：f : j₁ ⟶ j₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Zag.of_hom {j₁ j₂ : J} (f : j₁ ⟶ j₂) : Zag j₁ j₂ := Or.inl ⟨f⟩
/-
**CategoryTheory.Zag.of_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J} (f
 : j₂ ⟶ j₁), CategoryTheory.Zag j₁ j₂
参数：f : j₂ ⟶ j₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Zag.of_inv {j₁ j₂ : J} (f : j₂ ⟶ j₁) : Zag j₁ j₂ := Or.inr ⟨f⟩

/-- `j₁` and `j₂` are related by `Zigzag` if there is a chain of
morphisms from `j₁` to `j₂`, with backward morphisms allowed.
-/
/-
**CategoryTheory.Zigzag** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Zigzag : J -> J -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`j₁` and `j₂` are related by `Zigzag` if there is a chain of
morphisms from `j₁` to `j₂`, with backward morphisms allowed.
-/
def Zigzag : J → J → Prop :=
  Relation.ReflTransGen Zag
/-
**CategoryTheory.zigzag_symm** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：zigzag_symm : Std.Symm (@Zigzag J _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zigzag_symm : Std.Symm (@Zigzag J _) :=
  inferInstanceAs <| Std.Symm <| Relation.ReflTransGen Zag

@[deprecated (since := "2026-06-10")] alias zigzag_symmetric := zigzag_symm
/-
**CategoryTheory.zigzag_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：zigzag_equivalence : _root_.Equivalence (@Zigzag J _) where refl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
theorem zigzag_equivalence : _root_.Equivalence (@Zigzag J _) where
  refl := refl_of <| Relation.ReflTransGen _
  symm := symm_of <| Relation.ReflTransGen _
  trans := trans_of <| Relation.ReflTransGen _
/-
**CategoryTheory.Zigzag.refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zigzag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] (X : J), Categ
oryTheory.Zigzag X X
参数：X : J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `CategoryTheory.zigzag_equivalence`：zigzag_equivalence : _root_.Equivalen
ce (@Zigzag J _) where refl
-/
@[refl] theorem Zigzag.refl (X : J) : Zigzag X X := zigzag_equivalence.refl _
/-
**CategoryTheory.Zigzag.symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zigzag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J},  
 CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.Zigzag j₂ j₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
@[symm] theorem Zigzag.symm {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag j₂ j₁ := symm_of _ h
/-
**CategoryTheory.Zigzag.trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zigzag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J}
,   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.Zigzag j₂ j₃ → CategoryTheory.Z
igzag j₁ j₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `CategoryTheory.zigzag_equivalence`：zigzag_equivalence : _root_.Equivalen
ce (@Zigzag J _) where refl
-/
@[trans] theorem Zigzag.trans {j₁ j₂ j₃ : J} (h₁ : Zigzag j₁ j₂) (h₂ : Zigzag j₂ j₃) :
    Zigzag j₁ j₃ :=
  zigzag_equivalence.trans h₁ h₂
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := J) (Zigzag · ·) (Zigzag · ·) (Zigzag · ·) where
  trans := Zigzag.trans
/-
**CategoryTheory.Zigzag.of_zag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zigzag`
。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J},  
 CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zigzag j₁ j₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem Zigzag.of_zag {j₁ j₂ : J} (h : Zag j₁ j₂) : Zigzag j₁ j₂ :=
  Relation.ReflTransGen.single h
/-
**CategoryTheory.Zigzag.of_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zigzag`
。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J} (f
 : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
参数：f : j₁ ⟶ j₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.of_zag`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zigza
g j₁ j₂
· 使用定理 `CategoryTheory.Zag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zag j₁ j₂
-/
theorem Zigzag.of_hom {j₁ j₂ : J} (f : j₁ ⟶ j₂) : Zigzag j₁ j₂ :=
  of_zag (Zag.of_hom f)
/-
**CategoryTheory.Zigzag.of_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zigzag`
。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ : J} (f
 : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
参数：f : j₂ ⟶ j₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.of_zag`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zigza
g j₁ j₂
· 使用定理 `CategoryTheory.Zag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zag j₁ j₂
-/
theorem Zigzag.of_inv {j₁ j₂ : J} (f : j₂ ⟶ j₁) : Zigzag j₁ j₂ :=
  of_zag (Zag.of_inv f)
/-
**CategoryTheory.Zigzag.of_zag_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Z
igzag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J}
,   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zag j₂ j₃ → CategoryTheory.Zigzag 
j₁ j₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_zag`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zigza
g j₁ j₂
-/
theorem Zigzag.of_zag_trans {j₁ j₂ j₃ : J} (h₁ : Zag j₁ j₂) (h₂ : Zag j₂ j₃) : Zigzag j₁ j₃ :=
  trans (of_zag h₁) (of_zag h₂)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := J) (Zag · ·) (Zigzag · ·) (Zigzag · ·) where
  trans h h' := Zigzag.trans (.of_zag h) h'
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := J) (Zigzag · ·) (Zag · ·) (Zigzag · ·) where
  trans h h' := Zigzag.trans h (.of_zag h')
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (α := J) (Zag · ·) (Zag · ·) (Zigzag · ·) where
  trans := Zigzag.of_zag_trans
/-
**CategoryTheory.Zigzag.of_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zig
zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J}
 (f₁₂ : j₁ ⟶ j₂) (f₂₃ : j₂ ⟶ j₃),   CategoryTheory.Zigzag j₁ j₃
参数：f₁₂ : j₁ ⟶ j₂；f₂₃ : j₂ ⟶ j₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
-/
theorem Zigzag.of_hom_hom {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₂₃ : j₂ ⟶ j₃) : Zigzag j₁ j₃ :=
  (of_hom f₁₂).trans (of_hom f₂₃)
/-
**CategoryTheory.Zigzag.of_hom_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zig
zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J}
 (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂),   CategoryTheory.Zigzag j₁ j₃
参数：f₁₂ : j₁ ⟶ j₂；f₃₂ : j₃ ⟶ j₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
-/
theorem Zigzag.of_hom_inv {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂) : Zigzag j₁ j₃ :=
  (of_hom f₁₂).trans (of_inv f₃₂)
/-
**CategoryTheory.Zigzag.of_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zig
zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J}
 (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃),   CategoryTheory.Zigzag j₁ j₃
参数：f₂₁ : j₂ ⟶ j₁；f₂₃ : j₂ ⟶ j₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
-/
theorem Zigzag.of_inv_hom {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃) : Zigzag j₁ j₃ :=
  (of_inv f₂₁).trans (of_hom f₂₃)
/-
**CategoryTheory.Zigzag.of_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Zig
zag`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J}
 (f₂₁ : j₂ ⟶ j₁) (f₃₂ : j₃ ⟶ j₂),   CategoryTheory.Zigzag j₁ j₃
参数：f₂₁ : j₂ ⟶ j₁；f₃₂ : j₃ ⟶ j₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
-/
theorem Zigzag.of_inv_inv {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₃₂ : j₃ ⟶ j₂) : Zigzag j₁ j₃ :=
  (of_inv f₂₁).trans (of_inv f₃₂)

/-- The setoid given by the equivalence relation `Zigzag`. A quotient for this
setoid is a connected component of the category.
-/
@[instance_reducible]
/-
**CategoryTheory.Zigzag.setoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Zigzag`
。
形式化陈述：(J : Type u₂) → [CategoryTheory.Category.{v₁, u₂} J] → Setoid J
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_equivalence`：zigzag_equivalence : _root_.Equivalen
ce (@Zigzag J _) where refl

--- 原说明 ---
The setoid given by the equivalence relation `Zigzag`. A quotient for this
setoid is a connected component of the category.
-/
def Zigzag.setoid (J : Type u₂) [Category.{v₁} J] : Setoid J where
  r := Zigzag
  iseqv := zigzag_equivalence

/-- If there is a zigzag from `j₁` to `j₂`, then there is a zigzag from `F j₁` to
`F j₂` as long as `F` is a prefunctor.
-/
/-
**CategoryTheory.zigzag_prefunctor_obj_of_zigzag** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：zigzag_prefunctor_obj_of_zigzag (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂
) : Zigzag (F.obj j₁) (F.obj j₂)
参数：F : J ⥤q K；h : Zigzag j₁ j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
If there is a zigzag from `j₁` to `j₂`, then there is a zigzag from `F j₁` to
`F j₂` as long as `F` is a prefunctor.
-/
theorem zigzag_prefunctor_obj_of_zigzag (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) :
    Zigzag (F.obj j₁) (F.obj j₂) :=
  h.lift F.obj fun _ _ => Or.imp (Nonempty.map fun f => F.map f) (Nonempty.map fun f => F.map f)

/-- If there is a zigzag from `j₁` to `j₂`, then there is a zigzag from `F j₁` to
`F j₂` as long as `F` is a functor.
-/
/-
**CategoryTheory.zigzag_obj_of_zigzag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：zigzag_obj_of_zigzag (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag (
F.obj j₁) (F.obj j₂)
参数：F : J ⥤ K；h : Zigzag j₁ j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_prefunctor_obj_of_zigzag`：zigzag_prefunctor_obj_of
_zigzag (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag (F.obj j₁) (F.obj j
₂)

--- 原说明 ---
If there is a zigzag from `j₁` to `j₂`, then there is a zigzag from `F j₁` to
`F j₂` as long as `F` is a functor.
-/
theorem zigzag_obj_of_zigzag (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) :
    Zigzag (F.obj j₁) (F.obj j₂) :=
  zigzag_prefunctor_obj_of_zigzag F.toPrefunctor h

/-- A Zag in a discrete category entails an equality of its extremities -/
/-
**CategoryTheory.eq_of_zag** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eq_of_zag (X) {a b : Discrete X} (h : Zag a b) : a.as = b.as
参数：X；h : Zag a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `CategoryTheory.Discrete.eq_of_hom`：eq_of_hom {X Y : Discrete α} (i : X ⟶
 Y) : X.as = Y.as
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A Zag in a discrete category entails an equality of its extremities
-/
lemma eq_of_zag (X) {a b : Discrete X} (h : Zag a b) : a.as = b.as :=
  h.elim (fun ⟨f⟩ ↦ Discrete.eq_of_hom f) (fun ⟨f⟩ ↦ (Discrete.eq_of_hom f).symm)

/-- A zigzag in a discrete category entails an equality of its extremities -/
/-
**CategoryTheory.eq_of_zigzag** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eq_of_zigzag (X) {a b : Discrete X} (h : Zigzag a b) : a.as = b.as
参数：X；h : Zigzag a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.eq_of_zag`：eq_of_zag (X) {a b : Discrete X} (h : Zag a b)
 : a.as = b.as

--- 原说明 ---
A zigzag in a discrete category entails an equality of its extremities
-/
lemma eq_of_zigzag (X) {a b : Discrete X} (h : Zigzag a b) : a.as = b.as := by
  induction h with
  | refl => rfl
  | tail _ h eq => exact eq.trans (eq_of_zag _ h)

-- TODO: figure out the right way to generalise this to `Zigzag`.
/-
**CategoryTheory.zag_of_zag_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：zag_of_zag_obj (F : J ⥤ K) [F.Full] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj
 j₂)) : Zag j₁ j₂
参数：F : J ⥤ K；h : Zag (F.obj j₁) (F.obj j₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem zag_of_zag_obj (F : J ⥤ K) [F.Full] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj j₂)) :
    Zag j₁ j₂ :=
  Or.imp (Nonempty.map F.preimage) (Nonempty.map F.preimage) h

/-- Any equivalence relation containing (⟶) holds for all pairs of a connected category. -/
/-
**CategoryTheory.equiv_relation** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：equiv_relation [IsPreconnected J] (r : J -> J -> Prop) (hr : _root_.Equiva
lence r) (h : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), r j₁ j₂) : forall j₁ j₂ : J, r j
₁ j₂
参数：r : J -> J -> Prop；hr : _root_.Equivalence r；h : forall {j₁ j₂ : J} (_ : j₁ ⟶
 j₂), r j₁ j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.induct_on_objects`：induct_on_objects [IsPreconnected J] (
p : Set J) {j₀ : J} (h0 : j₀ in p) (h1 : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ in
 p ↔ j₂ in p) (j : J) …
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x

--- 原说明 ---
Any equivalence relation containing (⟶) holds for all pairs of a connected categ
ory.
-/
theorem equiv_relation [IsPreconnected J] (r : J → J → Prop) (hr : _root_.Equivalence r)
    (h : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), r j₁ j₂) : ∀ j₁ j₂ : J, r j₁ j₂ := by
  intro j₁ j₂
  have z : ∀ j : J, r j₁ j :=
    induct_on_objects {k | r j₁ k} (hr.1 j₁)
      fun f => ⟨fun t => hr.3 t (h f), fun t => hr.3 t (hr.2 (h f))⟩
  exact z j₂

/-- In a connected category, any two objects are related by `Zigzag`. -/
/-
**CategoryTheory.isPreconnected_zigzag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：isPreconnected_zigzag [IsPreconnected J] (j₁ j₂ : J) : Zigzag j₁ j₂
参数：j₁ j₂ : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.equiv_relation`：equiv_relation [IsPreconnected J] (r : J 
-> J -> Prop) (hr : _root_.Equivalence r) (h : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂),
 r j₁ j₂) : forall …
· 使用定理 `CategoryTheory.zigzag_equivalence`：zigzag_equivalence : _root_.Equivalen
ce (@Zigzag J _) where refl
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b

--- 原说明 ---
In a connected category, any two objects are related by `Zigzag`.
-/
theorem isPreconnected_zigzag [IsPreconnected J] (j₁ j₂ : J) : Zigzag j₁ j₂ :=
  equiv_relation _ zigzag_equivalence
    (fun f => Relation.ReflTransGen.single (Or.inl (Nonempty.intro f))) _ _
/-
**CategoryTheory.zigzag_isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：zigzag_isPreconnected (h : forall j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnecte
d J
参数：h : forall j₁ j₂ : J, Zigzag j₁ j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreconnected.of_constant_of_preserves_morphisms`：∀ {J :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J],   (∀ {α : Type u₁} (F : J
 → α), (∀ {j₁ j₂ : J} (x : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem zigzag_isPreconnected (h : ∀ j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J := by
  apply IsPreconnected.of_constant_of_preserves_morphisms
  intro α F hF j j'
  specialize h j j'
  induction h with
  | refl => rfl
  | tail _ hj ih =>
    rw [ih]
    rcases hj with (⟨⟨hj⟩⟩ | ⟨⟨hj⟩⟩)
    exacts [hF hj, (hF hj).symm]

/-- If any two objects in a nonempty category are related by `Zigzag`, the category is connected.
-/
/-
**CategoryTheory.zigzag_isConnected** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：zigzag_isConnected [Nonempty J] (h : forall j₁ j₂ : J, Zigzag j₁ j₂) : IsC
onnected J
参数：h : forall j₁ j₂ : J, Zigzag j₁ j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_isPreconnected`：zigzag_isPreconnected (h : forall 
j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J

--- 原说明 ---
If any two objects in a nonempty category are related by `Zigzag`, the category 
is connected.
-/
theorem zigzag_isConnected [Nonempty J] (h : ∀ j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J :=
  { zigzag_isPreconnected h with }
/-
**CategoryTheory.exists_zigzag'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：exists_zigzag' [IsConnected J] (j₁ j₂ : J) : exists l, List.IsChain Zag (j
₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂
参数：j₁ j₂ : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.exists_isChain_cons_of_relationReflTransGen`：exists_isChain_cons_of
_relationReflTransGen (h : Relation.ReflTransGen r a b) : exists l, IsChain r (a
 :: l) ∧ getLast (a :: l) (cons_ne_nil…
· 使用定理 `CategoryTheory.isPreconnected_zigzag`：isPreconnected_zigzag [IsPreconnec
ted J] (j₁ j₂ : J) : Zigzag j₁ j₂
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
-/
theorem exists_zigzag' [IsConnected J] (j₁ j₂ : J) :
    ∃ l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂ :=
  List.exists_isChain_cons_of_relationReflTransGen (isPreconnected_zigzag _ _)

/-- If any two objects in a nonempty category are linked by a sequence of (potentially reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
/-
**CategoryTheory.isPreconnected_of_zigzag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isPreconnected_of_zigzag (h : forall j₁ j₂ : J, exists l, List.IsChain Zag
 (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) : IsPreconnecte
d J
参数：h : forall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁
 :: l) (List.cons_ne_nil _ _) = j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `CategoryTheory.zigzag_isPreconnected`：zigzag_isPreconnected (h : forall 
j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J
· 使用定理 `List.relationReflTransGen_of_exists_isChain_cons`：relationReflTransGen_o
f_exists_isChain_cons (l : List α) (hl₁ : IsChain r (a :: l)) (hl₂ : getLast (a 
:: l) (cons_ne_nil _ _) = b) : Relatio…

--- 原说明 ---
If any two objects in a nonempty category are linked by a sequence of (potential
ly reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
theorem isPreconnected_of_zigzag (h : ∀ j₁ j₂ : J, ∃ l,
    List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) :
    IsPreconnected J := by
  apply zigzag_isPreconnected
  intro j₁ j₂
  rcases h j₁ j₂ with ⟨l, hl₁, hl₂⟩
  apply List.relationReflTransGen_of_exists_isChain_cons l hl₁ hl₂

/-- If any two objects in a nonempty category are linked by a sequence of (potentially reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
/-
**CategoryTheory.isConnected_of_zigzag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：isConnected_of_zigzag [Nonempty J] (h : forall j₁ j₂ : J, exists l, List.I
sChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) : IsC
onnected J
参数：h : forall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁
 :: l) (List.cons_ne_nil _ _) = j₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `CategoryTheory.isPreconnected_of_zigzag`：isPreconnected_of_zigzag (h : f
orall j₁ j₂ : J, exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (
List.cons_ne_nil _ _) = j₂) :…

--- 原说明 ---
If any two objects in a nonempty category are linked by a sequence of (potential
ly reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
theorem isConnected_of_zigzag [Nonempty J] (h : ∀ j₁ j₂ : J, ∃ l,
    List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) :
    IsConnected J :=
  { isPreconnected_of_zigzag h with }

/-- If `Discrete α` is connected, then `α` is (type-)equivalent to `PUnit`. -/
/-
**CategoryTheory.discreteIsConnectedEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：discreteIsConnectedEquivPUnit {α : Type u₁} [IsConnected (Discrete α)] : α
 ≃ PUnit
参数：Discrete α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Discrete α` is connected, then `α` is (type-)equivalent to `PUnit`.
-/
def discreteIsConnectedEquivPUnit {α : Type u₁} [IsConnected (Discrete α)] : α ≃ PUnit :=
  Discrete.equivOfEquivalence.{u₁, u₁}
    { functor := Functor.star (Discrete α)
      inverse := Discrete.functor fun _ => Classical.arbitrary _
      unitIso := isoConstant _ (Classical.arbitrary _)
      counitIso := Functor.punitExt _ _ }

variable {C : Type w₂} [Category.{w₁} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For objects `X Y : C`, any natural transformation `α : const X ⟶ const Y` from a connected
category must be constant.
This is the key property of connected categories which we use to establish properties about limits.
-/
/-
**CategoryTheory.nat_trans_from_is_connected** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：nat_trans_from_is_connected [IsPreconnected J] {X Y : C} (α : (Functor.con
st J).obj X ⟶ (Functor.const J).obj Y) : forall j j' : J, α.app j = (α.app j' : 
X ⟶ Y)
参数：α : (Functor.const J).obj X ⟶ (Functor.const J).obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.constant_of_preserves_morphisms`：constant_of_preserves_mo
rphisms [IsPreconnected J] {α : Type u₂} (F : J -> α) (h : forall (j₁ j₂ : J) (_
 : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
For objects `X Y : C`, any natural transformation `α : const X ⟶ const Y` from a
 connected
category must be constant.
This is the key property of connected categories which we use to establish prope
rties about limits.
-/
theorem nat_trans_from_is_connected [IsPreconnected J] {X Y : C}
    (α : (Functor.const J).obj X ⟶ (Functor.const J).obj Y) :
    ∀ j j' : J, α.app j = (α.app j' : X ⟶ Y) :=
  @constant_of_preserves_morphisms _ _ _ (X ⟶ Y) (fun j => α.app j) fun _ _ f => by
    simpa using (α.naturality f).symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsConnected J] : (Functor.const J : C ⥤ J ⥤ C).Full where
  map_surjective f := ⟨f.app (Classical.arbitrary J), by
    ext j
    apply nat_trans_from_is_connected f (Classical.arbitrary J) j⟩
/-
**CategoryTheory.nonempty_hom_of_preconnected_groupoid** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：nonempty_hom_of_preconnected_groupoid {G} [Groupoid G] [IsPreconnected G] 
: forall x y : G, Nonempty (x ⟶ y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.equiv_relation`：equiv_relation [IsPreconnected J] (r : J 
-> J -> Prop) (hr : _root_.Equivalence r) (h : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂),
 r j₁ j₂) : forall …
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
· 使用定理 `CategoryTheory.instIsGroupoid`：∀ {C : Type u} [inst : CategoryTheory.Gro
upoid C], CategoryTheory.IsGroupoid C
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
-/
theorem nonempty_hom_of_preconnected_groupoid {G} [Groupoid G] [IsPreconnected G] :
    ∀ x y : G, Nonempty (x ⟶ y) := by
  refine equiv_relation _ ?_ fun {j₁ j₂} => Nonempty.intro
  exact
    ⟨fun j => ⟨𝟙 _⟩,
     fun {j₁ j₂} => Nonempty.map fun f => inv f,
     fun {_ _ _} => Nonempty.map2 (· ≫ ·)⟩

attribute [instance] nonempty_hom_of_preconnected_groupoid
/-
**CategoryTheory.isPreconnected_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory`。
形式化陈述：isPreconnected_of_subsingleton [Subsingleton J] : IsPreconnected J where i
so_constant {α} F j
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance isPreconnected_of_subsingleton [Subsingleton J] : IsPreconnected J where
  iso_constant {α} F j := ⟨NatIso.ofComponents (fun x ↦ eqToIso (by simp [Subsingleton.allEq x j]))⟩
/-
**CategoryTheory.isConnected_of_nonempty_and_subsingleton** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J] [
Subsingleton J], CategoryTheory.IsConnected J
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isConnected_of_nonempty_and_subsingleton [Nonempty J] [Subsingleton J] :
    IsConnected J where

end CategoryTheory

