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

/--
Definition of `IsPreconnected` / `IsPreconnected` 的定义

English:
class IsPreconnected
  parameters: (J : Type u₁) [Category.{v₁} J]
  axioms and operations (1):
    - iso_constant : forall {α : Type u₁} (F : J ⥤ Discrete α) (j : J), Nonempty (F ≅ (Functor.const J).obj (F.obj j))

中文:
类 是预连通
  参数: (J : 类型u₁) [范畴.{v₁} J]
  公理与运算 (1 个):
    - iso_constant : 对任意 {α : 类型u₁} (F : J ⥤ 离散 α) (j : J), 非空 (F ≅ (函子.const J).obj (F.obj j))
-/
class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant :
    forall {α : Type u₁} (F : J ⥤ Discrete α) (j : J), Nonempty (F ≅ (Functor.const J).obj (F.obj j))

attribute [inherit_doc IsPreconnected] IsPreconnected.iso_constant

/-- We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits. -/
@[stacks 002S]
/--
Definition of `IsConnected` / `IsConnected` 的定义

English:
class IsConnected
  parameters: (J : Type u₁) [Category.{v₁} J]
  extends: IsPreconnected J
  axioms and operations (1):
    - [is_nonempty : Nonempty J]

中文:
类 是连通
  参数: (J : 类型u₁) [范畴.{v₁} J]
  继承: 是预连通 J
  公理与运算 (1 个):
    - [is_nonempty : 非空 J]
-/
class IsConnected (J : Type u₁) [Category.{v₁} J] : Prop extends IsPreconnected J where
  [is_nonempty : Nonempty J]

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]

namespace IsPreconnected.IsoConstantAux

set_option backward.privateInPublic true in
/--
Definition of `liftToDiscrete` / `liftToDiscrete` 的定义

English:
definition liftToDiscrete
  signature: {α : Type u₂} (F : J ⥤ Discrete α)
  body: have := Nonempty.intro j
    Discrete.mk (Function.invFun F.obj (F.obj j))
  map {j _} f := have := Nonempty.intro j
    ⟨⟨congr_arg (Function.invFun F.obj) (Discrete.ext (Discrete.eq_of_hom (F.map f)))⟩⟩

中文:
定义 liftToDiscrete
  签名: {α : 类型u₂} (F : J ⥤ 离散 α)
  定义体: have := Nonempty.intro j
    Discrete.mk (Function.invFun F.obj (F.obj j))
  map {j _} f := have := Nonempty.intro j
    ⟨⟨congr_arg (Function.invFun F.obj) (Discrete.ext (Discrete.eq_of_hom (F.map f)))⟩⟩
-/
private def liftToDiscrete {α : Type u₂} (F : J ⥤ Discrete α) : J ⥤ Discrete J where
  obj j := have := Nonempty.intro j
    Discrete.mk (Function.invFun F.obj (F.obj j))
  map {j _} f := have := Nonempty.intro j
    ⟨⟨congr_arg (Function.invFun F.obj) (Discrete.ext (Discrete.eq_of_hom (F.map f)))⟩⟩

set_option backward.privateInPublic true in
/--
Definition of `factorThroughDiscrete` / `factorThroughDiscrete` 的定义

English:
definition factorThroughDiscrete
  signature: {α : Type u₂} (F : J ⥤ Discrete α)
  body: NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by cat_disch)

中文:
定义 factorThroughDiscrete
  签名: {α : 类型u₂} (F : J ⥤ 离散 α)
  定义体: NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by cat_disch)
-/
private def factorThroughDiscrete {α : Type u₂} (F : J ⥤ Discrete α) :
    liftToDiscrete F ⋙ Discrete.functor F.obj ≅ F :=
  NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by cat_disch)

end IsPreconnected.IsoConstantAux

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `isoConstant` / `isoConstant` 的定义

English:
definition isoConstant
  signature: [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j : J)
  body: (IsPreconnected.IsoConstantAux.factorThroughDiscrete F).symm
    ≪≫ isoWhiskerRight (IsPreconnected.iso_constant _ j).some _
    ≪≫ NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by simp)

中文:
定义 isoConstant
  签名: [是预连通 J] {α : 类型u₂} (F : J ⥤ 离散 α) (j : J)
  定义体: (IsPreconnected.IsoConstantAux.factorThroughDiscrete F).symm
    ≪≫ isoWhiskerRight (IsPreconnected.iso_constant _ j).some _
    ≪≫ NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by simp)

Depends on / 依赖: Function, Function.apply_invFun_apply, IsPreconnected, IsPreconnected.IsoConstantAux.factorThroughDiscrete, IsPreconnected.iso_constant, IsoConstantAux, NatIso, NatIso.ofComponents, apply_invFun_apply, eqToIso, factorThroughDiscrete, isoWhiskerRight, iso_constant, ofComponents
-/
def isoConstant [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j : J) :
    F ≅ (Functor.const J).obj (F.obj j) :=
  (IsPreconnected.IsoConstantAux.factorThroughDiscrete F).symm
    ≪≫ isoWhiskerRight (IsPreconnected.iso_constant _ j).some _
    ≪≫ NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by simp)

/--
theorem `any_functor_const_on_obj` / 定理 `any_functor_const_on_obj`

English:
theorem any_functor_const_on_obj
  given: [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j j' : J)
  proof: by
  ext; exact ((isoConstant F j').hom.app j).down.1

中文:
定理 any_functor_const_on_obj
  条件: [是预连通 J] {α : 类型u₂} (F : J ⥤ 离散 α) (j j' : J)
  证明: by
  ext; exact ((isoConstant F j').hom.app j).down.1

Depends on / 依赖: hom.app, isoConstant
-/
theorem any_functor_const_on_obj [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j j' : J) :
    F.obj j = F.obj j' := by
  ext; exact ((isoConstant F j').hom.app j).down.1

/--
theorem `IsPreconnected.of_any_functor_const_on_obj` / 定理 `IsPreconnected.of_any_functor_const_on_obj`

English:
theorem IsPreconnected.of_any_functor_const_on_obj
  proof: fun F j' => ⟨NatIso.ofComponents fun j => eqToIso (h F j j')⟩

中文:
定理 是预连通.of_any_functor_const_on_obj
  证明: fun F j' => ⟨NatIso.ofComponents fun j => eqToIso (h F j j')⟩

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents
-/
theorem IsPreconnected.of_any_functor_const_on_obj
    (h : forall {α : Type u₁} (F : J ⥤ Discrete α), forall j j' : J, F.obj j = F.obj j') :
    IsPreconnected J where
  iso_constant := fun F j' => ⟨NatIso.ofComponents fun j => eqToIso (h F j j')⟩

/--
Instance `IsPreconnected.prod` / 实例 `IsPreconnected.prod`

English:
instance IsPreconnected.prod
  signature: [IsPreconnected J] [IsPreconnected K]
  body: by
  refine .of_any_functor_const_on_obj (fun {a} F ⟨j, k⟩ ⟨j', k'⟩ => ?_)
  exact (any_functor_const_on_obj (Prod.sectL J k ⋙ F) j j').trans
    (any_functor_const_on_obj (Prod.sectR j' K ⋙ F) k k')

中文:
实例 是预连通.乘积
  签名: [是预连通 J] [是预连通 K]
  定义体: by
  refine .of_any_functor_const_on_obj (fun {a} F ⟨j, k⟩ ⟨j', k'⟩ => ?_)
  exact (any_functor_const_on_obj (Prod.sectL J k ⋙ F) j j').trans
    (any_functor_const_on_obj (Prod.sectR j' K ⋙ F) k k')

Depends on / 依赖: Prod.sectL, Prod.sectR, any_functor_const_on_obj, of_any_functor_const_on_obj
-/
instance IsPreconnected.prod [IsPreconnected J] [IsPreconnected K] : IsPreconnected (J × K) := by
  refine .of_any_functor_const_on_obj (fun {a} F ⟨j, k⟩ ⟨j', k'⟩ => ?_)
  exact (any_functor_const_on_obj (Prod.sectL J k ⋙ F) j j').trans
    (any_functor_const_on_obj (Prod.sectR j' K ⋙ F) k k')

/--
Instance `IsConnected.prod` / 实例 `IsConnected.prod`

English:
instance IsConnected.prod
  signature: [IsConnected J] [IsConnected K]

中文:
实例 是连通.乘积
  签名: [是连通 J] [是连通 K]
-/
instance IsConnected.prod [IsConnected J] [IsConnected K] : IsConnected (J × K) where

/--
theorem `IsConnected.of_any_functor_const_on_obj` / 定理 `IsConnected.of_any_functor_const_on_obj`

English:
theorem IsConnected.of_any_functor_const_on_obj
  statement: [Nonempty J]
  proof: { IsPreconnected.of_any_functor_const_on_obj h with }

中文:
定理 是连通.of_any_functor_const_on_obj
  结论: [非空 J]
  证明: { IsPreconnected.of_any_functor_const_on_obj h with }

Depends on / 依赖: IsPreconnected, IsPreconnected.of_any_functor_const_on_obj, of_any_functor_const_on_obj
-/
theorem IsConnected.of_any_functor_const_on_obj [Nonempty J]
    (h : forall {α : Type u₁} (F : J ⥤ Discrete α), forall j j' : J, F.obj j = F.obj j') : IsConnected J :=
  { IsPreconnected.of_any_functor_const_on_obj h with }

/--
theorem `constant_of_preserves_morphisms` / 定理 `constant_of_preserves_morphisms`

English:
theorem constant_of_preserves_morphisms
  statement: [IsPreconnected J] {α : Type u₂} (F : J -> α)
  proof: by
  simpa using
    any_functor_const_on_obj
      { obj := Discrete.mk ∘ F
        map := fun f => eqToHom (by ext; exact h _ _ f) }
      j j'

中文:
定理 constant_of_preserves_morphisms
  结论: [是预连通 J] {α : 类型u₂} (F : J -> α)
  证明: by
  simpa using
    any_functor_const_on_obj
      { obj := Discrete.mk ∘ F
        map := fun f => eqToHom (by ext; exact h _ _ f) }
      j j'

Depends on / 依赖: Discrete, Discrete.mk, any_functor_const_on_obj, eqToHom
-/
theorem constant_of_preserves_morphisms [IsPreconnected J] {α : Type u₂} (F : J -> α)
    (h : forall (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J) : F j = F j' := by
  simpa using
    any_functor_const_on_obj
      { obj := Discrete.mk ∘ F
        map := fun f => eqToHom (by ext; exact h _ _ f) }
      j j'

/--
theorem `constant_of_preserves_morphisms'` / 定理 `constant_of_preserves_morphisms'`

English:
theorem constant_of_preserves_morphisms'
  statement: [IsConnected J] {α : Type u₂} (F : J -> α)
  proof: ⟨F (Classical.arbitrary _), fun _ => constant_of_preserves_morphisms _ h _ _⟩

中文:
定理 constant_of_preserves_morphisms'
  结论: [是连通 J] {α : 类型u₂} (F : J -> α)
  证明: ⟨F (Classical.arbitrary _), fun _ => constant_of_preserves_morphisms _ h _ _⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, constant_of_preserves_morphisms
-/
theorem constant_of_preserves_morphisms' [IsConnected J] {α : Type u₂} (F : J -> α)
    (h : forall (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) :
    exists (a : α), forall (j : J), F j = a :=
  ⟨F (Classical.arbitrary _), fun _ => constant_of_preserves_morphisms _ h _ _⟩

/--
theorem `IsPreconnected.of_constant_of_preserves_morphisms` / 定理 `IsPreconnected.of_constant_of_preserves_morphisms`

English:
theorem IsPreconnected.of_constant_of_preserves_morphisms
  proof: IsPreconnected.of_any_functor_const_on_obj fun F =>
    h F.obj fun f => by ext; exact Discrete.eq_of_hom (F.map f)

中文:
定理 是预连通.of_constant_of_preserves_morphisms
  证明: IsPreconnected.of_any_functor_const_on_obj fun F =>
    h F.obj fun f => by ext; exact Discrete.eq_of_hom (F.map f)

Depends on / 依赖: Discrete, Discrete.eq_of_hom, F.map, F.obj, IsPreconnected, IsPreconnected.of_any_functor_const_on_obj, eq_of_hom, of_any_functor_const_on_obj
-/
theorem IsPreconnected.of_constant_of_preserves_morphisms
    (h : forall {α : Type u₁} (F : J -> α),
      (forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), F j₁ = F j₂) -> forall j j' : J, F j = F j') :
    IsPreconnected J :=
  IsPreconnected.of_any_functor_const_on_obj fun F =>
    h F.obj fun f => by ext; exact Discrete.eq_of_hom (F.map f)

/--
theorem `IsConnected.of_constant_of_preserves_morphisms` / 定理 `IsConnected.of_constant_of_preserves_morphisms`

English:
theorem IsConnected.of_constant_of_preserves_morphisms
  statement: [Nonempty J]
  proof: { IsPreconnected.of_constant_of_preserves_morphisms h with }

中文:
定理 是连通.of_constant_of_preserves_morphisms
  结论: [非空 J]
  证明: { IsPreconnected.of_constant_of_preserves_morphisms h with }

Depends on / 依赖: IsPreconnected, IsPreconnected.of_constant_of_preserves_morphisms, of_constant_of_preserves_morphisms
-/
theorem IsConnected.of_constant_of_preserves_morphisms [Nonempty J]
    (h : forall {α : Type u₁} (F : J -> α),
      (forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), F j₁ = F j₂) -> forall j j' : J, F j = F j') :
    IsConnected J :=
  { IsPreconnected.of_constant_of_preserves_morphisms h with }

/--
theorem `induct_on_objects` / 定理 `induct_on_objects`

English:
theorem induct_on_objects
  statement: [IsPreconnected J] (p : Set J) {j₀ : J} (h0 : j₀ in p)
  proof: by
let aux (j₁ j₂ : J) (f : j₁ ⟶ j₂) := congrArg ULift.up (h1 f).eq
  injection constant_of_preserves_morphisms (fun k => ULift.up.{u₁} (k in p)) aux j j₀ with i
  rwa [i]

中文:
定理 induct_on_objects
  结论: [是预连通 J] (p : 集合 J) {j₀ : J} (h0 : j₀ in p)
  证明: by
let aux (j₁ j₂ : J) (f : j₁ ⟶ j₂) := congrArg ULift.up (h1 f).eq
  injection constant_of_preserves_morphisms (fun k => ULift.up.{u₁} (k in p)) aux j j₀ with i
  rwa [i]

Depends on / 依赖: ULift.up, constant_of_preserves_morphisms, injection
-/
theorem induct_on_objects [IsPreconnected J] (p : Set J) {j₀ : J} (h0 : j₀ in p)
    (h1 : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ in p ↔ j₂ in p) (j : J) : j in p := by
let aux (j₁ j₂ : J) (f : j₁ ⟶ j₂) := congrArg ULift.up (h1 f).eq
  injection constant_of_preserves_morphisms (fun k => ULift.up.{u₁} (k in p)) aux j j₀ with i
  rwa [i]

/--
theorem `IsConnected.of_induct` / 定理 `IsConnected.of_induct`

English:
theorem IsConnected.of_induct
  statement: {j₀ : J}
  proof: have := Nonempty.intro j₀
  IsConnected.of_constant_of_preserves_morphisms fun {α} F a => by
    have w := h { j | F j = F j₀ } rfl (fun {j₁} {j₂} f => by
      change F j₁ = F j₀ ↔ F j₂ = F j₀
      simp [a f])
    intro j j'
    rw [w j]; rw [w j']

中文:
定理 是连通.of_induct
  结论: {j₀ : J}
  证明: have := Nonempty.intro j₀
  IsConnected.of_constant_of_preserves_morphisms fun {α} F a => by
    have w := h { j | F j = F j₀ } rfl (fun {j₁} {j₂} f => by
      change F j₁ = F j₀ ↔ F j₂ = F j₀
      simp [a f])
    intro j j'
    rw [w j]; rw [w j']

Depends on / 依赖: IsConnected, IsConnected.of_constant_of_preserves_morphisms, Nonempty, Nonempty.intro, of_constant_of_preserves_morphisms
-/
theorem IsConnected.of_induct {j₀ : J}
    (h : forall p : Set J, j₀ in p -> (forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ in p ↔ j₂ in p) -> forall j : J, j in p) :
    IsConnected J :=
  have := Nonempty.intro j₀
  IsConnected.of_constant_of_preserves_morphisms fun {α} F a => by
    have w := h { j | F j = F j₀ } rfl (fun {j₁} {j₂} f => by
      change F j₁ = F j₀ ↔ F j₂ = F j₀
      simp [a f])
    intro j j'
    rw [w j]; rw [w j']

attribute [local instance] uliftCategory in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hc
  signature: : IsConnected J] : IsConnected (ULiftHom.{v₂} (ULift.{u₂} J))
  body: by
  apply IsConnected.of_induct
  · rintro p hj₀ h ⟨j⟩
    let p' : Set J := {j : J | ⟨j⟩ in p}
    have hj₀' : Classical.choice hc.is_nonempty in p' := by
      simp only [p']
      exact hj₀
    apply induct_on_objects p' hj₀' fun f => h ((ULiftHomULiftCategory.equiv J).functor.map f)

中文:
实例 [hc
  签名: : 是连通 J] : 是连通 (ULiftHom.{v₂} (类型层提升.{u₂} J))
  定义体: by
  apply IsConnected.of_induct
  · rintro p hj₀ h ⟨j⟩
    let p' : Set J := {j : J | ⟨j⟩ in p}
    have hj₀' : Classical.choice hc.is_nonempty in p' := by
      simp only [p']
      exact hj₀
    apply induct_on_objects p' hj₀' fun f => h ((ULiftHomULiftCategory.equiv J).functor.map f)

Depends on / 依赖: Classical, Classical.choice, IsConnected, IsConnected.of_induct, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, choice, functor, functor.map, hc.is_nonempty, induct_on_objects, is_nonempty, of_induct
-/
instance [hc : IsConnected J] : IsConnected (ULiftHom.{v₂} (ULift.{u₂} J)) := by
  apply IsConnected.of_induct
  · rintro p hj₀ h ⟨j⟩
    let p' : Set J := {j : J | ⟨j⟩ in p}
    have hj₀' : Classical.choice hc.is_nonempty in p' := by
      simp only [p']
      exact hj₀
    apply induct_on_objects p' hj₀' fun f => h ((ULiftHomULiftCategory.equiv J).functor.map f)

/--
theorem `isPreconnected_induction` / 定理 `isPreconnected_induction`

English:
theorem isPreconnected_induction
  statement: [IsPreconnected J] (Z : J -> Sort*)
  proof: (induct_on_objects { j | Nonempty (Z j) } ⟨x⟩
      (fun f => ⟨by rintro ⟨y⟩; exact ⟨h₁ f y⟩, by rintro ⟨y⟩; exact ⟨h₂ f y⟩⟩)
      j :)

中文:
定理 isPreconnected_induction
  结论: [是预连通 J] (Z : J -> 类型层*)
  证明: (induct_on_objects { j | Nonempty (Z j) } ⟨x⟩
      (fun f => ⟨by rintro ⟨y⟩; exact ⟨h₁ f y⟩, by rintro ⟨y⟩; exact ⟨h₂ f y⟩⟩)
      j :)

Depends on / 依赖: Nonempty, induct_on_objects
-/
theorem isPreconnected_induction [IsPreconnected J] (Z : J -> Sort*)
    (h₁ : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₁ -> Z j₂) (h₂ : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₂ -> Z j₁)
    {j₀ : J} (x : Z j₀) (j : J) : Nonempty (Z j) :=
  (induct_on_objects { j | Nonempty (Z j) } ⟨x⟩
      (fun f => ⟨by rintro ⟨y⟩; exact ⟨h₁ f y⟩, by rintro ⟨y⟩; exact ⟨h₂ f y⟩⟩)
      j :)

/--
theorem `isPreconnected_of_equivalent` / 定理 `isPreconnected_of_equivalent`

English:
theorem isPreconnected_of_equivalent
  statement: {K : Type u₂} [Category.{v₂} K] [IsPreconnected J]
  proof: ⟨calc
        F ≅ e.inverse ⋙ e.functor ⋙ F := (e.invFunIdAssoc F).symm
        _ ≅ e.inverse ⋙ (Functor.const J).obj ((e.functor ⋙ F).obj (e.inverse.obj k)) :=
          isoWhiskerLeft e.inverse (isoConstant (e.functor ⋙ F) (e.inverse.obj k))
        _ ≅ e.inverse ⋙ (Functor.const J).obj (F.obj k) 

中文:
定理 isPreconnected_of_equivalent
  结论: {K : 类型u₂} [范畴.{v₂} K] [是预连通 J]
  证明: ⟨calc
        F ≅ e.inverse ⋙ e.functor ⋙ F := (e.invFunIdAssoc F).symm
        _ ≅ e.inverse ⋙ (Functor.const J).obj ((e.functor ⋙ F).obj (e.inverse.obj k)) :=
          isoWhiskerLeft e.inverse (isoConstant (e.functor ⋙ F) (e.inverse.obj k))
        _ ≅ e.inverse ⋙ (Functor.const J).obj (F.obj k) 

Depends on / 依赖: F.obj, Functor, Functor.const, Iso.refl, NatIso, NatIso.ofComponents, counitIso, e.counitIso.app, e.functor, e.invFunIdAssoc, e.inverse, e.inverse.obj, functor, invFunIdAssoc, inverse, isoConstant, isoWhiskerLeft, mapIso, ofComponents
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

/--
lemma `isPreconnected_iff_of_equivalence` / 引理 `isPreconnected_iff_of_equivalence`

English:
lemma isPreconnected_iff_of_equivalence
  given: {K : Type u₂} [Category.{v₂} K] (e : J ≌ K)
  proof: ⟨fun _ => isPreconnected_of_equivalent e, fun _ => isPreconnected_of_equivalent e.symm⟩

中文:
引理 isPreconnected_iff_of_equivalence
  条件: {K : 类型u₂} [范畴.{v₂} K] (e : J ≌ K)
  证明: ⟨fun _ => isPreconnected_of_equivalent e, fun _ => isPreconnected_of_equivalent e.symm⟩

Depends on / 依赖: e.symm, isPreconnected_of_equivalent
-/
lemma isPreconnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) :
    IsPreconnected J ↔ IsPreconnected K :=
  ⟨fun _ => isPreconnected_of_equivalent e, fun _ => isPreconnected_of_equivalent e.symm⟩

/--
theorem `isConnected_of_equivalent` / 定理 `isConnected_of_equivalent`

English:
theorem isConnected_of_equivalent
  given: {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J]
  proof: { is_nonempty := Nonempty.map e.functor.obj (by infer_instance)
    toIsPreconnected := isPreconnected_of_equivalent e }

中文:
定理 isConnected_of_equivalent
  条件: {K : 类型u₂} [范畴.{v₂} K] (e : J ≌ K) [是连通 J]
  证明: { is_nonempty := Nonempty.map e.functor.obj (by infer_instance)
    toIsPreconnected := isPreconnected_of_equivalent e }

Depends on / 依赖: Nonempty, Nonempty.map, e.functor.obj, functor, infer_instance, isPreconnected_of_equivalent, is_nonempty, toIsPreconnected
-/
theorem isConnected_of_equivalent {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] :
    IsConnected K :=
  { is_nonempty := Nonempty.map e.functor.obj (by infer_instance)
    toIsPreconnected := isPreconnected_of_equivalent e }

/--
lemma `isConnected_iff_of_equivalence` / 引理 `isConnected_iff_of_equivalence`

English:
lemma isConnected_iff_of_equivalence
  given: {K : Type u₂} [Category.{v₂} K] (e : J ≌ K)
  proof: ⟨fun _ => isConnected_of_equivalent e, fun _ => isConnected_of_equivalent e.symm⟩

中文:
引理 isConnected_iff_of_equivalence
  条件: {K : 类型u₂} [范畴.{v₂} K] (e : J ≌ K)
  证明: ⟨fun _ => isConnected_of_equivalent e, fun _ => isConnected_of_equivalent e.symm⟩

Depends on / 依赖: e.symm, isConnected_of_equivalent
-/
lemma isConnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) :
    IsConnected J ↔ IsConnected K :=
  ⟨fun _ => isConnected_of_equivalent e, fun _ => isConnected_of_equivalent e.symm⟩

/--
Instance `isPreconnected_op` / 实例 `isPreconnected_op`

English:
instance isPreconnected_op
  signature: [IsPreconnected J]
  body: fun {α} F X =>
    ⟨NatIso.ofComponents fun Y =>
      eqToIso (Discrete.ext (Discrete.eq_of_hom ((Nonempty.some
        (IsPreconnected.iso_constant (F.rightOp ⋙ (Discrete.opposite α).functor) (unop X))).app
          (unop Y)).hom))⟩

中文:
实例 isPreconnected_op
  签名: [是预连通 J]
  定义体: fun {α} F X =>
    ⟨NatIso.ofComponents fun Y =>
      eqToIso (Discrete.ext (Discrete.eq_of_hom ((Nonempty.some
        (IsPreconnected.iso_constant (F.rightOp ⋙ (Discrete.opposite α).functor) (unop X))).app
          (unop Y)).hom))⟩
-/
instance isPreconnected_op [IsPreconnected J] : IsPreconnected Jᵒᵖ where
  iso_constant := fun {α} F X =>
    ⟨NatIso.ofComponents fun Y =>
      eqToIso (Discrete.ext (Discrete.eq_of_hom ((Nonempty.some
        (IsPreconnected.iso_constant (F.rightOp ⋙ (Discrete.opposite α).functor) (unop X))).app
          (unop Y)).hom))⟩

/--
Instance `isConnected_op` / 实例 `isConnected_op`

English:
instance isConnected_op
  signature: [IsConnected J]
  body: Nonempty.intro (op (Classical.arbitrary J))

中文:
实例 isConnected_op
  签名: [是连通 J]
  定义体: Nonempty.intro (op (Classical.arbitrary J))

Depends on / 依赖: Classical, Classical.arbitrary, Nonempty, Nonempty.intro, arbitrary
-/
instance isConnected_op [IsConnected J] : IsConnected Jᵒᵖ where
  is_nonempty := Nonempty.intro (op (Classical.arbitrary J))

/--
theorem `isPreconnected_of_isPreconnected_op` / 定理 `isPreconnected_of_isPreconnected_op`

English:
theorem isPreconnected_of_isPreconnected_op
  given: [IsPreconnected Jᵒᵖ]
  statement: IsPreconnected J
  proof: isPreconnected_of_equivalent (opOpEquivalence J)

中文:
定理 isPreconnected_of_isPreconnected_op
  条件: [是预连通 Jᵒᵖ]
  结论: 是预连通 J
  证明: isPreconnected_of_equivalent (opOpEquivalence J)

Depends on / 依赖: isPreconnected_of_equivalent, opOpEquivalence
-/
theorem isPreconnected_of_isPreconnected_op [IsPreconnected Jᵒᵖ] : IsPreconnected J :=
  isPreconnected_of_equivalent (opOpEquivalence J)

/--
theorem `isConnected_of_isConnected_op` / 定理 `isConnected_of_isConnected_op`

English:
theorem isConnected_of_isConnected_op
  given: [IsConnected Jᵒᵖ]
  statement: IsConnected J
  proof: isConnected_of_equivalent (opOpEquivalence J)

中文:
定理 isConnected_of_isConnected_op
  条件: [是连通 Jᵒᵖ]
  结论: 是连通 J
  证明: isConnected_of_equivalent (opOpEquivalence J)

Depends on / 依赖: isConnected_of_equivalent, opOpEquivalence
-/
theorem isConnected_of_isConnected_op [IsConnected Jᵒᵖ] : IsConnected J :=
  isConnected_of_equivalent (opOpEquivalence J)

variable (J) in
@[simp]
/--
theorem `isConnected_op_iff_isConnected` / 定理 `isConnected_op_iff_isConnected`

English:
theorem isConnected_op_iff_isConnected
  statement: IsConnected Jᵒᵖ ↔ IsConnected J
  proof: ⟨fun _ => isConnected_of_isConnected_op, fun _ => isConnected_op⟩

中文:
定理 isConnected_op_iff_isConnected
  结论: 是连通 Jᵒᵖ ↔ 是连通 J
  证明: ⟨fun _ => isConnected_of_isConnected_op, fun _ => isConnected_op⟩

Depends on / 依赖: isConnected_of_isConnected_op, isConnected_op
-/
theorem isConnected_op_iff_isConnected : IsConnected Jᵒᵖ ↔ IsConnected J :=
  ⟨fun _ => isConnected_of_isConnected_op, fun _ => isConnected_op⟩

/--
Definition of `Zag` / `Zag` 的定义

English:
definition Zag
  signature: (j₁ j₂ : J)
  body: Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

中文:
定义 Zag
  签名: (j₁ j₂ : J)
  定义体: Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

Depends on / 依赖: Nonempty
-/
def Zag (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

/--
theorem `Zag.refl` / 定理 `Zag.refl`

English:
theorem Zag.refl
  given: (X : J)
  statement: Zag X X
  proof: Or.inl ⟨𝟙 _⟩

中文:
定理 Zag.refl
  条件: (X : J)
  结论: Zag X X
  证明: Or.inl ⟨𝟙 _⟩
-/
@[refl] theorem Zag.refl (X : J) : Zag X X := Or.inl ⟨𝟙 _⟩

/--
Instance `zag_symm` / 实例 `zag_symm`

English:
instance zag_symm
  signature: : Std.Symm (@Zag J _) where
  body: h.symm

@[deprecated (since := "2026-06-10")] alias zag_symmetric := zag_symm

中文:
实例 zag_symm
  签名: : Std.Symm (@Zag J _) where
  定义体: h.symm

@[deprecated (since := "2026-06-10")] alias zag_symmetric := zag_symm

Depends on / 依赖: h.symm
-/
instance zag_symm : Std.Symm (@Zag J _) where
  symm _ _ h := h.symm

@[deprecated (since := "2026-06-10")] alias zag_symmetric := zag_symm

/--
theorem `Zag.symm` / 定理 `Zag.symm`

English:
theorem Zag.symm
  given: {j₁ j₂ : J} (h : Zag j₁ j₂)
  statement: Zag j₂ j₁
  proof: symm_of _ h

中文:
定理 Zag.symm
  条件: {j₁ j₂ : J} (h : Zag j₁ j₂)
  结论: Zag j₂ j₁
  证明: symm_of _ h
-/
@[symm] theorem Zag.symm {j₁ j₂ : J} (h : Zag j₁ j₂) : Zag j₂ j₁ := symm_of _ h

/--
theorem `Zag.of_hom` / 定理 `Zag.of_hom`

English:
theorem Zag.of_hom
  given: {j₁ j₂ : J} (f : j₁ ⟶ j₂)
  statement: Zag j₁ j₂
  proof: Or.inl ⟨f⟩

中文:
定理 Zag.of_hom
  条件: {j₁ j₂ : J} (f : j₁ ⟶ j₂)
  结论: Zag j₁ j₂
  证明: Or.inl ⟨f⟩

Depends on / 依赖: Or.inl
-/
theorem Zag.of_hom {j₁ j₂ : J} (f : j₁ ⟶ j₂) : Zag j₁ j₂ := Or.inl ⟨f⟩

/--
theorem `Zag.of_inv` / 定理 `Zag.of_inv`

English:
theorem Zag.of_inv
  given: {j₁ j₂ : J} (f : j₂ ⟶ j₁)
  statement: Zag j₁ j₂
  proof: Or.inr ⟨f⟩

中文:
定理 Zag.of_inv
  条件: {j₁ j₂ : J} (f : j₂ ⟶ j₁)
  结论: Zag j₁ j₂
  证明: Or.inr ⟨f⟩

Depends on / 依赖: Or.inr
-/
theorem Zag.of_inv {j₁ j₂ : J} (f : j₂ ⟶ j₁) : Zag j₁ j₂ := Or.inr ⟨f⟩

/--
Definition of `Zigzag` / `Zigzag` 的定义

English:
definition Zigzag
  signature: : J -> J -> Prop
  body: Relation.ReflTransGen Zag

中文:
定义 Zigzag
  签名: : J -> J -> 命题
  定义体: Relation.ReflTransGen Zag

Depends on / 依赖: ReflTransGen, Relation, Relation.ReflTransGen
-/
def Zigzag : J -> J -> Prop :=
  Relation.ReflTransGen Zag

/--
Instance `zigzag_symm` / 实例 `zigzag_symm`

English:
instance zigzag_symm
  signature: : Std.Symm (@Zigzag J _)
  body: inferInstanceAs Std.Symm Relation.ReflTransGen Zag

@[deprecated (since := "2026-06-10")] alias zigzag_symmetric := zigzag_symm

中文:
实例 zigzag_symm
  签名: : Std.Symm (@Zigzag J _)
  定义体: inferInstanceAs Std.Symm Relation.ReflTransGen Zag

@[deprecated (since := "2026-06-10")] alias zigzag_symmetric := zigzag_symm

Depends on / 依赖: ReflTransGen, Relation, Relation.ReflTransGen, Std.Symm
-/
instance zigzag_symm : Std.Symm (@Zigzag J _) :=
inferInstanceAs Std.Symm Relation.ReflTransGen Zag

@[deprecated (since := "2026-06-10")] alias zigzag_symmetric := zigzag_symm

/--
theorem `zigzag_equivalence` / 定理 `zigzag_equivalence`

English:
theorem zigzag_equivalence
  statement: _root_.Equivalence (@Zigzag J _) where
  proof: refl_of Relation.ReflTransGen _
symm := symm_of Relation.ReflTransGen _
trans := trans_of Relation.ReflTransGen _

中文:
定理 zigzag_equivalence
  结论: _root_.等价 (@Zigzag J _) where
  证明: refl_of Relation.ReflTransGen _
symm := symm_of Relation.ReflTransGen _
trans := trans_of Relation.ReflTransGen _

Depends on / 依赖: ReflTransGen, Relation, Relation.ReflTransGen, refl_of
-/
theorem zigzag_equivalence : _root_.Equivalence (@Zigzag J _) where
refl := refl_of Relation.ReflTransGen _
symm := symm_of Relation.ReflTransGen _
trans := trans_of Relation.ReflTransGen _

/--
theorem `Zigzag.refl` / 定理 `Zigzag.refl`

English:
theorem Zigzag.refl
  given: (X : J)
  statement: Zigzag X X
  proof: zigzag_equivalence.refl _

中文:
定理 Zigzag.refl
  条件: (X : J)
  结论: Zigzag X X
  证明: zigzag_equivalence.refl _
-/
@[refl] theorem Zigzag.refl (X : J) : Zigzag X X := zigzag_equivalence.refl _

/--
theorem `Zigzag.symm` / 定理 `Zigzag.symm`

English:
theorem Zigzag.symm
  given: {j₁ j₂ : J} (h : Zigzag j₁ j₂)
  statement: Zigzag j₂ j₁
  proof: symm_of _ h

中文:
定理 Zigzag.symm
  条件: {j₁ j₂ : J} (h : Zigzag j₁ j₂)
  结论: Zigzag j₂ j₁
  证明: symm_of _ h
-/
@[symm] theorem Zigzag.symm {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag j₂ j₁ := symm_of _ h

/--
theorem `Zigzag.trans` / 定理 `Zigzag.trans`

English:
theorem Zigzag.trans
  given: {j₁ j₂ j₃ : J} (h₁ : Zigzag j₁ j₂) (h₂ : Zigzag j₂ j₃)
  proof: zigzag_equivalence.trans h₁ h₂

中文:
定理 Zigzag.trans
  条件: {j₁ j₂ j₃ : J} (h₁ : Zigzag j₁ j₂) (h₂ : Zigzag j₂ j₃)
  证明: zigzag_equivalence.trans h₁ h₂
-/
@[trans] theorem Zigzag.trans {j₁ j₂ j₃ : J} (h₁ : Zigzag j₁ j₂) (h₂ : Zigzag j₂ j₃) :
    Zigzag j₁ j₃ :=
  zigzag_equivalence.trans h₁ h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := J) (Zigzag · ·) (Zigzag · ·) (Zigzag · ·)
  body: Zigzag.trans

中文:
实例 :
  签名: Trans (α := J) (Zigzag · ·) (Zigzag · ·) (Zigzag · ·)
  定义体: Zigzag.trans

Depends on / 依赖: Zigzag
-/
instance : Trans (α := J) (Zigzag · ·) (Zigzag · ·) (Zigzag · ·) where
  trans := Zigzag.trans

/--
theorem `Zigzag.of_zag` / 定理 `Zigzag.of_zag`

English:
theorem Zigzag.of_zag
  given: {j₁ j₂ : J} (h : Zag j₁ j₂)
  statement: Zigzag j₁ j₂
  proof: Relation.ReflTransGen.single h

中文:
定理 Zigzag.of_zag
  条件: {j₁ j₂ : J} (h : Zag j₁ j₂)
  结论: Zigzag j₁ j₂
  证明: Relation.ReflTransGen.single h

Depends on / 依赖: ReflTransGen, Relation, Relation.ReflTransGen.single, single
-/
theorem Zigzag.of_zag {j₁ j₂ : J} (h : Zag j₁ j₂) : Zigzag j₁ j₂ :=
  Relation.ReflTransGen.single h

/--
theorem `Zigzag.of_hom` / 定理 `Zigzag.of_hom`

English:
theorem Zigzag.of_hom
  given: {j₁ j₂ : J} (f : j₁ ⟶ j₂)
  statement: Zigzag j₁ j₂
  proof: of_zag (Zag.of_hom f)

中文:
定理 Zigzag.of_hom
  条件: {j₁ j₂ : J} (f : j₁ ⟶ j₂)
  结论: Zigzag j₁ j₂
  证明: of_zag (Zag.of_hom f)

Depends on / 依赖: Zag.of_hom, of_hom, of_zag
-/
theorem Zigzag.of_hom {j₁ j₂ : J} (f : j₁ ⟶ j₂) : Zigzag j₁ j₂ :=
  of_zag (Zag.of_hom f)

/--
theorem `Zigzag.of_inv` / 定理 `Zigzag.of_inv`

English:
theorem Zigzag.of_inv
  given: {j₁ j₂ : J} (f : j₂ ⟶ j₁)
  statement: Zigzag j₁ j₂
  proof: of_zag (Zag.of_inv f)

中文:
定理 Zigzag.of_inv
  条件: {j₁ j₂ : J} (f : j₂ ⟶ j₁)
  结论: Zigzag j₁ j₂
  证明: of_zag (Zag.of_inv f)

Depends on / 依赖: Zag.of_inv, of_inv, of_zag
-/
theorem Zigzag.of_inv {j₁ j₂ : J} (f : j₂ ⟶ j₁) : Zigzag j₁ j₂ :=
  of_zag (Zag.of_inv f)

/--
theorem `Zigzag.of_zag_trans` / 定理 `Zigzag.of_zag_trans`

English:
theorem Zigzag.of_zag_trans
  given: {j₁ j₂ j₃ : J} (h₁ : Zag j₁ j₂) (h₂ : Zag j₂ j₃)
  statement: Zigzag j₁ j₃
  proof: trans (of_zag h₁) (of_zag h₂)

中文:
定理 Zigzag.of_zag_trans
  条件: {j₁ j₂ j₃ : J} (h₁ : Zag j₁ j₂) (h₂ : Zag j₂ j₃)
  结论: Zigzag j₁ j₃
  证明: trans (of_zag h₁) (of_zag h₂)

Depends on / 依赖: of_zag
-/
theorem Zigzag.of_zag_trans {j₁ j₂ j₃ : J} (h₁ : Zag j₁ j₂) (h₂ : Zag j₂ j₃) : Zigzag j₁ j₃ :=
  trans (of_zag h₁) (of_zag h₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := J) (Zag · ·) (Zigzag · ·) (Zigzag · ·)
  body: Zigzag.trans (.of_zag h) h'

中文:
实例 :
  签名: Trans (α := J) (Zag · ·) (Zigzag · ·) (Zigzag · ·)
  定义体: Zigzag.trans (.of_zag h) h'

Depends on / 依赖: Zigzag
-/
instance : Trans (α := J) (Zag · ·) (Zigzag · ·) (Zigzag · ·) where
  trans h h' := Zigzag.trans (.of_zag h) h'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := J) (Zigzag · ·) (Zag · ·) (Zigzag · ·)
  body: Zigzag.trans h (.of_zag h')

中文:
实例 :
  签名: Trans (α := J) (Zigzag · ·) (Zag · ·) (Zigzag · ·)
  定义体: Zigzag.trans h (.of_zag h')

Depends on / 依赖: Zigzag
-/
instance : Trans (α := J) (Zigzag · ·) (Zag · ·) (Zigzag · ·) where
  trans h h' := Zigzag.trans h (.of_zag h')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (α := J) (Zag · ·) (Zag · ·) (Zigzag · ·)
  body: Zigzag.of_zag_trans

中文:
实例 :
  签名: Trans (α := J) (Zag · ·) (Zag · ·) (Zigzag · ·)
  定义体: Zigzag.of_zag_trans

Depends on / 依赖: Zigzag
-/
instance : Trans (α := J) (Zag · ·) (Zag · ·) (Zigzag · ·) where
  trans := Zigzag.of_zag_trans

/--
theorem `Zigzag.of_hom_hom` / 定理 `Zigzag.of_hom_hom`

English:
theorem Zigzag.of_hom_hom
  given: {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₂₃ : j₂ ⟶ j₃)
  statement: Zigzag j₁ j₃
  proof: (of_hom f₁₂).trans (of_hom f₂₃)

中文:
定理 Zigzag.of_hom_hom
  条件: {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₂₃ : j₂ ⟶ j₃)
  结论: Zigzag j₁ j₃
  证明: (of_hom f₁₂).trans (of_hom f₂₃)

Depends on / 依赖: of_hom
-/
theorem Zigzag.of_hom_hom {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₂₃ : j₂ ⟶ j₃) : Zigzag j₁ j₃ :=
  (of_hom f₁₂).trans (of_hom f₂₃)

/--
theorem `Zigzag.of_hom_inv` / 定理 `Zigzag.of_hom_inv`

English:
theorem Zigzag.of_hom_inv
  given: {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂)
  statement: Zigzag j₁ j₃
  proof: (of_hom f₁₂).trans (of_inv f₃₂)

中文:
定理 Zigzag.of_hom_inv
  条件: {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂)
  结论: Zigzag j₁ j₃
  证明: (of_hom f₁₂).trans (of_inv f₃₂)

Depends on / 依赖: of_hom, of_inv
-/
theorem Zigzag.of_hom_inv {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂) : Zigzag j₁ j₃ :=
  (of_hom f₁₂).trans (of_inv f₃₂)

/--
theorem `Zigzag.of_inv_hom` / 定理 `Zigzag.of_inv_hom`

English:
theorem Zigzag.of_inv_hom
  given: {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃)
  statement: Zigzag j₁ j₃
  proof: (of_inv f₂₁).trans (of_hom f₂₃)

中文:
定理 Zigzag.of_inv_hom
  条件: {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃)
  结论: Zigzag j₁ j₃
  证明: (of_inv f₂₁).trans (of_hom f₂₃)

Depends on / 依赖: of_hom, of_inv
-/
theorem Zigzag.of_inv_hom {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃) : Zigzag j₁ j₃ :=
  (of_inv f₂₁).trans (of_hom f₂₃)

/--
theorem `Zigzag.of_inv_inv` / 定理 `Zigzag.of_inv_inv`

English:
theorem Zigzag.of_inv_inv
  given: {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₃₂ : j₃ ⟶ j₂)
  statement: Zigzag j₁ j₃
  proof: (of_inv f₂₁).trans (of_inv f₃₂)

中文:
定理 Zigzag.of_inv_inv
  条件: {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₃₂ : j₃ ⟶ j₂)
  结论: Zigzag j₁ j₃
  证明: (of_inv f₂₁).trans (of_inv f₃₂)

Depends on / 依赖: of_inv
-/
theorem Zigzag.of_inv_inv {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₃₂ : j₃ ⟶ j₂) : Zigzag j₁ j₃ :=
  (of_inv f₂₁).trans (of_inv f₃₂)

/-- The setoid given by the equivalence relation `Zigzag`. A quotient for this
setoid is a connected component of the category.
-/
@[instance_reducible]
/--
Definition of `Zigzag.setoid` / `Zigzag.setoid` 的定义

English:
definition Zigzag.setoid
  signature: (J : Type u₂) [Category.{v₁} J]
  body: Zigzag
  iseqv := zigzag_equivalence

中文:
定义 Zigzag.setoid
  签名: (J : 类型u₂) [范畴.{v₁} J]
  定义体: Zigzag
  iseqv := zigzag_equivalence

Depends on / 依赖: Zigzag
-/
def Zigzag.setoid (J : Type u₂) [Category.{v₁} J] : Setoid J where
  r := Zigzag
  iseqv := zigzag_equivalence

/--
theorem `zigzag_prefunctor_obj_of_zigzag` / 定理 `zigzag_prefunctor_obj_of_zigzag`

English:
theorem zigzag_prefunctor_obj_of_zigzag
  given: (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂)
  proof: h.lift F.obj fun _ _ => Or.imp (Nonempty.map fun f => F.map f) (Nonempty.map fun f => F.map f)

中文:
定理 zigzag_prefunctor_obj_of_zigzag
  条件: (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂)
  证明: h.lift F.obj fun _ _ => Or.imp (Nonempty.map fun f => F.map f) (Nonempty.map fun f => F.map f)

Depends on / 依赖: F.map, F.obj, Nonempty, Nonempty.map, Or.imp, h.lift
-/
theorem zigzag_prefunctor_obj_of_zigzag (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) :
    Zigzag (F.obj j₁) (F.obj j₂) :=
  h.lift F.obj fun _ _ => Or.imp (Nonempty.map fun f => F.map f) (Nonempty.map fun f => F.map f)

/--
theorem `zigzag_obj_of_zigzag` / 定理 `zigzag_obj_of_zigzag`

English:
theorem zigzag_obj_of_zigzag
  given: (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂)
  proof: zigzag_prefunctor_obj_of_zigzag F.toPrefunctor h

中文:
定理 zigzag_obj_of_zigzag
  条件: (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂)
  证明: zigzag_prefunctor_obj_of_zigzag F.toPrefunctor h

Depends on / 依赖: F.toPrefunctor, toPrefunctor, zigzag_prefunctor_obj_of_zigzag
-/
theorem zigzag_obj_of_zigzag (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) :
    Zigzag (F.obj j₁) (F.obj j₂) :=
  zigzag_prefunctor_obj_of_zigzag F.toPrefunctor h

/--
lemma `eq_of_zag` / 引理 `eq_of_zag`

English:
lemma eq_of_zag
  given: (X) {a b : Discrete X} (h : Zag a b)
  statement: a.as = b.as
  proof: h.elim (fun ⟨f⟩ => Discrete.eq_of_hom f) (fun ⟨f⟩ => (Discrete.eq_of_hom f).symm)

中文:
引理 eq_of_zag
  条件: (X) {a b : 离散 X} (h : Zag a b)
  结论: a.as = b.as
  证明: h.elim (fun ⟨f⟩ => Discrete.eq_of_hom f) (fun ⟨f⟩ => (Discrete.eq_of_hom f).symm)

Depends on / 依赖: Discrete, Discrete.eq_of_hom, eq_of_hom, h.elim
-/
lemma eq_of_zag (X) {a b : Discrete X} (h : Zag a b) : a.as = b.as :=
  h.elim (fun ⟨f⟩ => Discrete.eq_of_hom f) (fun ⟨f⟩ => (Discrete.eq_of_hom f).symm)

/--
lemma `eq_of_zigzag` / 引理 `eq_of_zigzag`

English:
lemma eq_of_zigzag
  given: (X) {a b : Discrete X} (h : Zigzag a b)
  statement: a.as = b.as
  proof: by
  induction h with
  | refl => rfl
  | tail _ h eq => exact eq.trans (eq_of_zag _ h)

中文:
引理 eq_of_zigzag
  条件: (X) {a b : 离散 X} (h : Zigzag a b)
  结论: a.as = b.as
  证明: by
  induction h with
  | refl => rfl
  | tail _ h eq => exact eq.trans (eq_of_zag _ h)

Depends on / 依赖: eq.trans, eq_of_zag
-/
lemma eq_of_zigzag (X) {a b : Discrete X} (h : Zigzag a b) : a.as = b.as := by
  induction h with
  | refl => rfl
  | tail _ h eq => exact eq.trans (eq_of_zag _ h)

-- TODO: figure out the right way to generalise this to `Zigzag`.
/--
theorem `zag_of_zag_obj` / 定理 `zag_of_zag_obj`

English:
theorem zag_of_zag_obj
  given: (F : J ⥤ K) [F.Full] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj j₂))
  proof: Or.imp (Nonempty.map F.preimage) (Nonempty.map F.preimage) h

中文:
定理 zag_of_zag_obj
  条件: (F : J ⥤ K) [F.满] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj j₂))
  证明: Or.imp (Nonempty.map F.preimage) (Nonempty.map F.preimage) h

Depends on / 依赖: F.preimage, Nonempty, Nonempty.map, Or.imp, preimage
-/
theorem zag_of_zag_obj (F : J ⥤ K) [F.Full] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj j₂)) :
    Zag j₁ j₂ :=
  Or.imp (Nonempty.map F.preimage) (Nonempty.map F.preimage) h

/--
theorem `equiv_relation` / 定理 `equiv_relation`

English:
theorem equiv_relation
  statement: [IsPreconnected J] (r : J -> J -> Prop) (hr : _root_.Equivalence r)
  proof: by
  intro j₁ j₂
  have z : forall j : J, r j₁ j :=
    induct_on_objects {k | r j₁ k} (hr.1 j₁)
      fun f => ⟨fun t => hr.3 t (h f), fun t => hr.3 t (hr.2 (h f))⟩
  exact z j₂

中文:
定理 equiv_relation
  结论: [是预连通 J] (r : J -> J -> 命题) (hr : _root_.等价 r)
  证明: by
  intro j₁ j₂
  have z : forall j : J, r j₁ j :=
    induct_on_objects {k | r j₁ k} (hr.1 j₁)
      fun f => ⟨fun t => hr.3 t (h f), fun t => hr.3 t (hr.2 (h f))⟩
  exact z j₂

Depends on / 依赖: induct_on_objects
-/
theorem equiv_relation [IsPreconnected J] (r : J -> J -> Prop) (hr : _root_.Equivalence r)
    (h : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), r j₁ j₂) : forall j₁ j₂ : J, r j₁ j₂ := by
  intro j₁ j₂
  have z : forall j : J, r j₁ j :=
    induct_on_objects {k | r j₁ k} (hr.1 j₁)
      fun f => ⟨fun t => hr.3 t (h f), fun t => hr.3 t (hr.2 (h f))⟩
  exact z j₂

/--
theorem `isPreconnected_zigzag` / 定理 `isPreconnected_zigzag`

English:
theorem isPreconnected_zigzag
  given: [IsPreconnected J] (j₁ j₂ : J)
  statement: Zigzag j₁ j₂
  proof: equiv_relation _ zigzag_equivalence
    (fun f => Relation.ReflTransGen.single (Or.inl (Nonempty.intro f))) _ _

中文:
定理 isPreconnected_zigzag
  条件: [是预连通 J] (j₁ j₂ : J)
  结论: Zigzag j₁ j₂
  证明: equiv_relation _ zigzag_equivalence
    (fun f => Relation.ReflTransGen.single (Or.inl (Nonempty.intro f))) _ _

Depends on / 依赖: Nonempty, Nonempty.intro, Or.inl, ReflTransGen, Relation, Relation.ReflTransGen.single, equiv_relation, single, zigzag_equivalence
-/
theorem isPreconnected_zigzag [IsPreconnected J] (j₁ j₂ : J) : Zigzag j₁ j₂ :=
  equiv_relation _ zigzag_equivalence
    (fun f => Relation.ReflTransGen.single (Or.inl (Nonempty.intro f))) _ _


/--
theorem `zigzag_isPreconnected` / 定理 `zigzag_isPreconnected`

English:
theorem zigzag_isPreconnected
  given: (h : forall j₁ j₂ : J, Zigzag j₁ j₂)
  statement: IsPreconnected J
  proof: by
  apply IsPreconnected.of_constant_of_preserves_morphisms
  intro α F hF j j'
  specialize h j j'
  induction h with
  | refl => rfl
  | tail _ hj ih =>
    rw [ih]
    rcases hj with (⟨⟨hj⟩⟩ | ⟨⟨hj⟩⟩)
    exacts [hF hj, (hF hj).symm]

中文:
定理 zigzag_isPreconnected
  条件: (h : 对任意 j₁ j₂ : J, Zigzag j₁ j₂)
  结论: 是预连通 J
  证明: by
  apply IsPreconnected.of_constant_of_preserves_morphisms
  intro α F hF j j'
  specialize h j j'
  induction h with
  | refl => rfl
  | tail _ hj ih =>
    rw [ih]
    rcases hj with (⟨⟨hj⟩⟩ | ⟨⟨hj⟩⟩)
    exacts [hF hj, (hF hj).symm]

Depends on / 依赖: IsPreconnected, IsPreconnected.of_constant_of_preserves_morphisms, exacts, of_constant_of_preserves_morphisms, specialize
-/
theorem zigzag_isPreconnected (h : forall j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J := by
  apply IsPreconnected.of_constant_of_preserves_morphisms
  intro α F hF j j'
  specialize h j j'
  induction h with
  | refl => rfl
  | tail _ hj ih =>
    rw [ih]
    rcases hj with (⟨⟨hj⟩⟩ | ⟨⟨hj⟩⟩)
    exacts [hF hj, (hF hj).symm]

/--
theorem `zigzag_isConnected` / 定理 `zigzag_isConnected`

English:
theorem zigzag_isConnected
  given: [Nonempty J] (h : forall j₁ j₂ : J, Zigzag j₁ j₂)
  statement: IsConnected J
  proof: { zigzag_isPreconnected h with }

中文:
定理 zigzag_isConnected
  条件: [非空 J] (h : 对任意 j₁ j₂ : J, Zigzag j₁ j₂)
  结论: 是连通 J
  证明: { zigzag_isPreconnected h with }

Depends on / 依赖: IsConnected, IsLimi, NatTrans, NatTrans.naturality, Over.forget, Over.mkIdTerminal, Over.mkIdTerminal.from, WithTerminal, WithTerminal.isLimitEquiv.symm, WithTerminal.liftToTerminal, c.map, casesOn, forget, generalizing, i.casesOn, isConnected_of_hasTerminal, isLimitEquiv, isLimitOfReflects, liftToTerminal, mkIdTerminal
-/
theorem zigzag_isConnected [Nonempty J] (h : forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J :=
  { zigzag_isPreconnected h with }

/--
theorem `exists_zigzag'` / 定理 `exists_zigzag'`

English:
theorem exists_zigzag'
  given: [IsConnected J] (j₁ j₂ : J)
  proof: List.exists_isChain_cons_of_relationReflTransGen (isPreconnected_zigzag _ _)

中文:
定理 存在_zigzag'
  条件: [是连通 J] (j₁ j₂ : J)
  证明: List.exists_isChain_cons_of_relationReflTransGen (isPreconnected_zigzag _ _)

Depends on / 依赖: Coequifibered, Coequifibered.cancel_right_of_respectsIso, Discrete, Discrete.equivalence, F.op, HasCoproductsOfShape, IsClosedUnderIsomorphisms, List.exists_isChain_cons_of_relationReflTransGen, Quiver, Quiver.Hom.opEquiv, Under.w, cancel_right_of_respectsIso, e.hom, equivalence, exists_isChain_cons_of_relationReflTransGen, f.hom.Coequifibered, hasColimitsOfShape_of_equivalence, isClosedUnderColimitsOfShape_iff_op, isClosedUnderLimitsOfShape_inverseImage_iff, isPreconnected_zigzag
-/
theorem exists_zigzag' [IsConnected J] (j₁ j₂ : J) :
    exists l, List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂ :=
  List.exists_isChain_cons_of_relationReflTransGen (isPreconnected_zigzag _ _)

/--
theorem `isPreconnected_of_zigzag` / 定理 `isPreconnected_of_zigzag`

English:
theorem isPreconnected_of_zigzag
  statement: (h : forall j₁ j₂ : J, exists l,
  proof: by
  apply zigzag_isPreconnected
  intro j₁ j₂
  rcases h j₁ j₂ with ⟨l, hl₁, hl₂⟩
  apply List.relationReflTransGen_of_exists_isChain_cons l hl₁ hl₂

中文:
定理 isPreconnected_of_zigzag
  结论: (h : 对任意 j₁ j₂ : J, 存在 l,
  证明: by
  apply zigzag_isPreconnected
  intro j₁ j₂
  rcases h j₁ j₂ with ⟨l, hl₁, hl₂⟩
  apply List.relationReflTransGen_of_exists_isChain_cons l hl₁ hl₂

Depends on / 依赖: List.relationReflTransGen_of_exists_isChain_cons, relationReflTransGen_of_exists_isChain_cons, zigzag_isPreconnected
-/
theorem isPreconnected_of_zigzag (h : forall j₁ j₂ : J, exists l,
    List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) :
    IsPreconnected J := by
  apply zigzag_isPreconnected
  intro j₁ j₂
  rcases h j₁ j₂ with ⟨l, hl₁, hl₂⟩
  apply List.relationReflTransGen_of_exists_isChain_cons l hl₁ hl₂

/--
theorem `isConnected_of_zigzag` / 定理 `isConnected_of_zigzag`

English:
theorem isConnected_of_zigzag
  statement: [Nonempty J] (h : forall j₁ j₂ : J, exists l,
  proof: { isPreconnected_of_zigzag h with }

中文:
定理 isConnected_of_zigzag
  结论: [非空 J] (h : 对任意 j₁ j₂ : J, 存在 l,
  证明: { isPreconnected_of_zigzag h with }

Depends on / 依赖: isPreconnected_of_zigzag
-/
theorem isConnected_of_zigzag [Nonempty J] (h : forall j₁ j₂ : J, exists l,
    List.IsChain Zag (j₁ :: l) ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) :
    IsConnected J :=
  { isPreconnected_of_zigzag h with }

/--
Definition of `discreteIsConnectedEquivPUnit` / `discreteIsConnectedEquivPUnit` 的定义

English:
definition discreteIsConnectedEquivPUnit
  signature: {α : Type u₁} [IsConnected (Discrete α)]
  body: Discrete.equivOfEquivalence.{u₁, u₁}
    { functor := Functor.star (Discrete α)
      inverse := Discrete.functor fun _ => Classical.arbitrary _
      unitIso := isoConstant _ (Classical.arbitrary _)
      counitIso := Functor.punitExt _ _ }

中文:
定义 discreteIsConnectedEquivPUnit
  签名: {α : 类型u₁} [是连通 (离散 α)]
  定义体: Discrete.equivOfEquivalence.{u₁, u₁}
    { functor := Functor.star (Discrete α)
      inverse := Discrete.functor fun _ => Classical.arbitrary _
      unitIso := isoConstant _ (Classical.arbitrary _)
      counitIso := Functor.punitExt _ _ }

Depends on / 依赖: Classical, Classical.arbitrary, Discrete, Discrete.equivOfEquivalence, Discrete.functor, Functor, Functor.punitExt, Functor.star, arbitrary, counitIso, equivOfEquivalence, functor, inverse, isoConstant, punitExt, unitIso
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
/--
theorem `nat_trans_from_is_connected` / 定理 `nat_trans_from_is_connected`

English:
theorem nat_trans_from_is_connected
  statement: [IsPreconnected J] {X Y : C}
  proof: @constant_of_preserves_morphisms _ _ _ (X ⟶ Y) (fun j => α.app j) fun _ _ f => by
    simpa using (α.naturality f).symm

中文:
定理 nat_trans_from_is_connected
  结论: [是预连通 J] {X Y : C}
  证明: @constant_of_preserves_morphisms _ _ _ (X ⟶ Y) (fun j => α.app j) fun _ _ f => by
    simpa using (α.naturality f).symm

Depends on / 依赖: constant_of_preserves_morphisms, naturality
-/
theorem nat_trans_from_is_connected [IsPreconnected J] {X Y : C}
    (α : (Functor.const J).obj X ⟶ (Functor.const J).obj Y) :
    forall j j' : J, α.app j = (α.app j' : X ⟶ Y) :=
  @constant_of_preserves_morphisms _ _ _ (X ⟶ Y) (fun j => α.app j) fun _ _ f => by
    simpa using (α.naturality f).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: J] : (Functor.const J
  body: ⟨f.app (Classical.arbitrary J), by
    ext j
    apply nat_trans_from_is_connected f (Classical.arbitrary J) j⟩

中文:
实例 [是连通
  签名: J] : (函子.const J
  定义体: ⟨f.app (Classical.arbitrary J), by
    ext j
    apply nat_trans_from_is_connected f (Classical.arbitrary J) j⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, f.app, nat_trans_from_is_connected
-/
instance [IsConnected J] : (Functor.const J : C ⥤ J ⥤ C).Full where
  map_surjective f := ⟨f.app (Classical.arbitrary J), by
    ext j
    apply nat_trans_from_is_connected f (Classical.arbitrary J) j⟩

/--
theorem `nonempty_hom_of_preconnected_groupoid` / 定理 `nonempty_hom_of_preconnected_groupoid`

English:
theorem nonempty_hom_of_preconnected_groupoid
  given: {G} [Groupoid G] [IsPreconnected G]
  proof: by
  refine equiv_relation _ ?_ fun {j₁ j₂} => Nonempty.intro
  exact
    ⟨fun j => ⟨𝟙 _⟩,
     fun {j₁ j₂} => Nonempty.map fun f => inv f,
     fun {_ _ _} => Nonempty.map2 (· ≫ ·)⟩

中文:
定理 nonempty_hom_of_preconnected_groupoid
  条件: {G} [群胚 G] [是预连通 G]
  证明: by
  refine equiv_relation _ ?_ fun {j₁ j₂} => Nonempty.intro
  exact
    ⟨fun j => ⟨𝟙 _⟩,
     fun {j₁ j₂} => Nonempty.map fun f => inv f,
     fun {_ _ _} => Nonempty.map2 (· ≫ ·)⟩

Depends on / 依赖: Nonempty, Nonempty.intro, Nonempty.map, Nonempty.map2, equiv_relation
-/
theorem nonempty_hom_of_preconnected_groupoid {G} [Groupoid G] [IsPreconnected G] :
    forall x y : G, Nonempty (x ⟶ y) := by
  refine equiv_relation _ ?_ fun {j₁ j₂} => Nonempty.intro
  exact
    ⟨fun j => ⟨𝟙 _⟩,
     fun {j₁ j₂} => Nonempty.map fun f => inv f,
     fun {_ _ _} => Nonempty.map2 (· ≫ ·)⟩

attribute [instance] nonempty_hom_of_preconnected_groupoid

/--
Instance `isPreconnected_of_subsingleton` / 实例 `isPreconnected_of_subsingleton`

English:
instance isPreconnected_of_subsingleton
  signature: [Subsingleton J]
  body: ⟨NatIso.ofComponents (fun x => eqToIso (by simp [Subsingleton.allEq x j]))⟩

中文:
实例 isPreconnected_of_subsingleton
  签名: [子单例 J]
  定义体: ⟨NatIso.ofComponents (fun x => eqToIso (by simp [Subsingleton.allEq x j]))⟩

Depends on / 依赖: NatIso, NatIso.ofComponents, Subsingleton, Subsingleton.allEq, eqToIso, ofComponents
-/
instance isPreconnected_of_subsingleton [Subsingleton J] : IsPreconnected J where
  iso_constant {α} F j := ⟨NatIso.ofComponents (fun x => eqToIso (by simp [Subsingleton.allEq x j]))⟩

/--
Instance `isConnected_of_nonempty_and_subsingleton` / 实例 `isConnected_of_nonempty_and_subsingleton`

English:
instance isConnected_of_nonempty_and_subsingleton
  signature: [Nonempty J] [Subsingleton J]

中文:
实例 isConnected_of_nonempty_and_subsingleton
  签名: [非空 J] [子单例 J]
-/
instance isConnected_of_nonempty_and_subsingleton [Nonempty J] [Subsingleton J] :
    IsConnected J where

end CategoryTheory
