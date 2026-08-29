/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!

# Topological subcategories of `Action V G`

For a concrete category `V`, where the forgetful functor factors via `TopCat`,
and a monoid `G`, equipped with a topological space instance,
we define the full subcategory `ContAction V G` of all objects of `Action V G`
where the induced action is continuous.

We also define a category `DiscreteContAction V G` as the full subcategory of `ContAction V G`,
where the underlying topological space is discrete.

Finally we define inclusion functors into `Action V G` and `TopCat` in terms
of `HasForget₂` instances.

-/

@[expose] public section

open CategoryTheory Limits

variable (V : Type*) [Category* V] {FV : V -> V -> Type*} {CV : V -> Type*}
    [forall X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] [HasForget₂ V TopCat]
variable (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Action

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (Action V G) TopCat
  body: HasForget₂.trans (Action V G) V TopCat

中文:
实例 :
  签名: HasForget₂ (Action V G) TopCat
  定义体: HasForget₂.trans (Action V G) V TopCat

Depends on / 依赖: Action, TopCat
-/
instance : HasForget₂ (Action V G) TopCat :=
  HasForget₂.trans (Action V G) V TopCat

set_option backward.isDefEq.respectTransparency.types false in
instance (X : Action V G) : MulAction G ((CategoryTheory.forget₂ _ TopCat).obj X) where
  smul g x := ((CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
  one_smul x := by
    change ((CategoryTheory.forget₂ _ TopCat).map (X.ρ 1)) x = x
    simp
  mul_smul g h x := by
    change (CategoryTheory.forget₂ _ TopCat).map (X.ρ (g * h)) x =
      ((CategoryTheory.forget₂ _ TopCat).map (X.ρ h) ≫
        (CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
    rw [← Functor.map_comp]; rw [map_mul]
    rfl

variable {V G}

/--
Definition of `IsContinuous` / `IsContinuous` 的定义

English:
abbreviation IsContinuous
  signature: (X : Action V G)
  body: ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)

中文:
缩写 IsContinuous
  签名: (X : Action V G)
  定义体: ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, ContinuousSMul, TopCat
-/
abbrev IsContinuous (X : Action V G) : Prop :=
  ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)

/--
lemma `isContinuous_def` / 引理 `isContinuous_def`

English:
lemma isContinuous_def
  given: (X : Action V G)
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
引理 isContinuous_def
  条件: (X : Action V G)
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
lemma isContinuous_def (X : Action V G) :
    X.IsContinuous ↔ Continuous (fun p : G × (forget₂ _ TopCat).obj X =>
      (forget₂ _ TopCat).map (X.ρ p.1) p.2) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

end Action

open Action

/--
Definition of `ContAction` / `ContAction` 的定义

English:
abbreviation ContAction
  signature: : Type _
  body: ObjectProperty.FullSubcategory (IsContinuous (V := V) (G := G))

中文:
缩写 ContAction
  签名: : Type _
  定义体: ObjectProperty.FullSubcategory (IsContinuous (V := V) (G := G))

Depends on / 依赖: FullSubcategory, IsContinuous, ObjectProperty, ObjectProperty.FullSubcategory
-/
abbrev ContAction : Type _ := ObjectProperty.FullSubcategory (IsContinuous (V := V) (G := G))

namespace ContAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (ContAction V G) V
  body: HasForget₂.trans (ContAction V G) (Action V G) V

中文:
实例 :
  签名: HasForget₂ (ContAction V G) V
  定义体: HasForget₂.trans (ContAction V G) (Action V G) V

Depends on / 依赖: Action, ContAction
-/
instance : HasForget₂ (ContAction V G) V :=
  HasForget₂.trans (ContAction V G) (Action V G) V

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (ContAction V G) TopCat
  body: HasForget₂.trans (ContAction V G) (Action V G) TopCat

中文:
实例 :
  签名: HasForget₂ (ContAction V G) TopCat
  定义体: HasForget₂.trans (ContAction V G) (Action V G) TopCat

Depends on / 依赖: Action, ContAction, TopCat
-/
instance : HasForget₂ (ContAction V G) TopCat :=
  HasForget₂.trans (ContAction V G) (Action V G) TopCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ContAction V G) (Action V G)
  body: X.obj

中文:
实例 :
  签名: Coe (ContAction V G) (Action V G)
  定义体: X.obj

Depends on / 依赖: X.obj
-/
instance : Coe (ContAction V G) (Action V G) where
  coe X := X.obj

variable {V G}

/--
Definition of `IsDiscrete` / `IsDiscrete` 的定义

English:
abbreviation IsDiscrete
  signature: (X : ContAction V G)
  body: DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

中文:
缩写 IsDiscrete
  签名: (X : ContAction V G)
  定义体: DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, DiscreteTopology, TopCat
-/
abbrev IsDiscrete (X : ContAction V G) : Prop :=
  DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

variable (V) {H : Type*} [Monoid H] [TopologicalSpace H]

/-- The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`. This is the analogue of
`Action.res` in the continuous setting. -/
@[simps! obj_obj map]
/--
Definition of `res` / `res` 的定义

English:
definition res
  signature: (f : G ->ₜ* H)
  body: ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Action.res _ f) fun X => by
    constructor
    let v : G × (forget₂ _ TopCat).obj X -> H × (forget₂ _ TopCat).obj X := fun p => (f p.1, p.2)
    have : Continuous v := by fun_prop
    let u : H × (forget₂ _ TopCat).obj X -> (forget₂ _ TopCat).obj X :=
   

中文:
定义 res
  签名: (f : G ->ₜ* H)
  定义体: ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Action.res _ f) fun X => by
    constructor
    let v : G × (forget₂ _ TopCat).obj X -> H × (forget₂ _ TopCat).obj X := fun p => (f p.1, p.2)
    have : Continuous v := by fun_prop
    let u : H × (forget₂ _ TopCat).obj X -> (forget₂ _ TopCat).obj X :=
   

Depends on / 依赖: Action, Action.res, Continuous, ObjectProperty, ObjectProperty.lift, TopCat, X.obj, fun_prop
-/
def res (f : G ->ₜ* H) : ContAction V H ⥤ ContAction V G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Action.res _ f) fun X => by
    constructor
    let v : G × (forget₂ _ TopCat).obj X -> H × (forget₂ _ TopCat).obj X := fun p => (f p.1, p.2)
    have : Continuous v := by fun_prop
    let u : H × (forget₂ _ TopCat).obj X -> (forget₂ _ TopCat).obj X :=
      fun p => (forget₂ _ TopCat).map (X.obj.ρ p.1) p.2
    have : Continuous u := X.2.1
    change Continuous (u ∘ v)
    fun_prop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting scalars along a composition is naturally isomorphic to restricting scalars twice. -/
@[simps! hom inv]
/--
Definition of `resComp` / `resComp` 的定义

English:
definition resComp
  signature: {K : Type*} [Monoid K] [TopologicalSpace K]
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 resComp
  签名: {K : 类型} [Monoid K] [TopologicalSpace K]
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def resComp {K : Type*} [Monoid K] [TopologicalSpace K]
    (f : G ->ₜ* H) (h : H ->ₜ* K) :
    ContAction.res V (h.comp f) ≅ ContAction.res V h ⋙ ContAction.res V f :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `f = f'`, restriction of scalars along `f` and `f'` is the same. -/
@[simps! hom inv]
/--
Definition of `resCongr` / `resCongr` 的定义

English:
definition resCongr
  signature: (f f' : G ->ₜ* H) (h : f = f')
  body: NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _)
    (by subst h; simp))) fun f => ObjectProperty.hom_ext _ (Action.Hom.ext (by simp))

中文:
定义 resCongr
  签名: (f f' : G ->ₜ* H) (h : f = f')
  定义体: NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _)
    (by subst h; simp))) fun f => ObjectProperty.hom_ext _ (Action.Hom.ext (by simp))

Depends on / 依赖: Action, Action.Hom.ext, Action.mkIso, Classical, Classical.choice, Finite, Finite.exists_type_univ_nonempty_mulEquiv, Iso.refl, Limits, Limits.preservesColimitsOfShape_of_equiv, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.hom_ext, ObjectProperty.isoMk, choice, exists_type_univ_nonempty_mulEquiv, hom_ext, ofComponents, preservesColimitsOfShape_of_equiv
-/
def resCongr (f f' : G ->ₜ* H) (h : f = f') : ContAction.res V f ≅ ContAction.res V f' :=
  NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _)
    (by subst h; simp))) fun f => ObjectProperty.hom_ext _ (Action.Hom.ext (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of scalars along a topological monoid isomorphism induces an equivalence of
categories. -/
@[simps! functor inverse]
/--
Definition of `resEquiv` / `resEquiv` 的定义

English:
definition resEquiv
  signature: (f : G ≃ₜ* H)
  body: res _ f
  inverse := res _ f.symm
  unitIso := resCongr V (ContinuousMonoidHom.id H) _ (by ext; simp) ≪≫
    ContAction.resComp _ _ _
  counitIso := (ContAction.resComp _ _ _).symm ≪≫
    ContAction.resCongr V _ (ContinuousMonoidHom.id G) (by ext; simp)

中文:
定义 resEquiv
  签名: (f : G ≃ₜ* H)
  定义体: res _ f
  inverse := res _ f.symm
  unitIso := resCongr V (ContinuousMonoidHom.id H) _ (by ext; simp) ≪≫
    ContAction.resComp _ _ _
  counitIso := (ContAction.resComp _ _ _).symm ≪≫
    ContAction.resCongr V _ (ContinuousMonoidHom.id G) (by ext; simp)
-/
def resEquiv (f : G ≃ₜ* H) : ContAction V H ≌ ContAction V G where
  functor := res _ f
  inverse := res _ f.symm
  unitIso := resCongr V (ContinuousMonoidHom.id H) _ (by ext; simp) ≪≫
    ContAction.resComp _ _ _
  counitIso := (ContAction.resComp _ _ _).symm ≪≫
    ContAction.resCongr V _ (ContinuousMonoidHom.id G) (by ext; simp)

end ContAction

open ContAction

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `DiscreteContAction` / `DiscreteContAction` 的定义

English:
definition DiscreteContAction
  signature: : Type _
  body: ObjectProperty.FullSubcategory (IsDiscrete (V := V) (G := G))
deriving Category, ConcreteCategory

中文:
定义 DiscreteContAction
  签名: : Type _
  定义体: ObjectProperty.FullSubcategory (IsDiscrete (V := V) (G := G))
deriving Category, ConcreteCategory

Depends on / 依赖: FullSubcategory, IsDiscrete, ObjectProperty, ObjectProperty.FullSubcategory
-/
def DiscreteContAction : Type _ := ObjectProperty.FullSubcategory (IsDiscrete (V := V) (G := G))
deriving Category, ConcreteCategory

namespace DiscreteContAction


set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (DiscreteContAction V G) (ContAction V G)
  body: inferInstanceAs HasForget₂ (ObjectProperty.FullSubcategory _) _

中文:
实例 :
  签名: HasForget₂ (DiscreteContAction V G) (ContAction V G)
  定义体: inferInstanceAs HasForget₂ (ObjectProperty.FullSubcategory _) _

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory
-/
instance : HasForget₂ (DiscreteContAction V G) (ContAction V G) :=
inferInstanceAs HasForget₂ (ObjectProperty.FullSubcategory _) _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (DiscreteContAction V G) TopCat
  body: HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat

中文:
实例 :
  签名: HasForget₂ (DiscreteContAction V G) TopCat
  定义体: HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat

Depends on / 依赖: ContAction, DiscreteContAction, TopCat
-/
instance : HasForget₂ (DiscreteContAction V G) TopCat :=
  HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat

variable {V G}

set_option backward.isDefEq.respectTransparency.types false in
instance (X : DiscreteContAction V G) :
    DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X) :=
  X.property

end DiscreteContAction

namespace CategoryTheory

variable {V W : Type*} [Category* V] {FV : V -> V -> Type*} {CV : V -> Type*}
    [forall X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] [HasForget₂ V TopCat]
    [Category* W] {FW : W -> W -> Type*} {CW : W -> Type*} [forall X Y, FunLike (FW X Y) (CW X) (CW Y)]
    [ConcreteCategory W FW] [HasForget₂ W TopCat]
    (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Functor

/-- Continuous version of `Functor.mapAction`. -/
@[simps! obj_obj map]
/--
Definition of `mapContAction` / `mapContAction` 的定义

English:
definition mapContAction
  signature: (F : V ⥤ W) (H : forall X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
  body: ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F.mapAction G) H

中文:
定义 mapContAction
  签名: (F : V ⥤ W) (H : 对任意 X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
  定义体: ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F.mapAction G) H

Depends on / 依赖: F.mapAction, ObjectProperty, ObjectProperty.lift, mapAction
-/
def mapContAction (F : V ⥤ W) (H : forall X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous) :
    ContAction V G ⥤ ContAction W G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F.mapAction G) H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Continuous version of `Functor.mapActionComp`. -/
@[simps! hom inv]
/--
Definition of `mapContActionComp` / `mapContActionComp` 的定义

English:
definition mapContActionComp
  signature: {T : Type*} [Category* T]
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 mapContActionComp
  签名: {T : 类型} [Category* T]
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapContActionComp {T : Type*} [Category* T]
    {FT : T -> T -> Type*} {CT : T -> Type*} [forall X Y, FunLike (FT X Y) (CT X) (CT Y)]
    [ConcreteCategory T FT] [HasForget₂ T TopCat]
    (F : V ⥤ W) (H : forall X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
    (F' : W ⥤ T) (H' : forall X : ContAction W G, ((F'.mapAction G).obj X.obj).IsContinuous) :
    Functor.mapContAction G (F ⋙ F') (fun X => H' ((F.mapContAction G H).obj X)) ≅
      Functor.mapContAction G F H ⋙ Functor.mapContAction G F' H' :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Continuous version of `Functor.mapActionCongr`. -/
@[simps! hom inv]
/--
Definition of `mapContActionCongr` / `mapContActionCongr` 的定义

English:
definition mapContActionCongr
  body: NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Action.mkIso (e.app X.obj.V) (by simp)))

中文:
定义 mapContActionCongr
  定义体: NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Action.mkIso (e.app X.obj.V) (by simp)))

Depends on / 依赖: Action, Action.mkIso, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.isoMk, X.obj.V, e.app, ofComponents
-/
def mapContActionCongr
    {F : V ⥤ W} {F' : V ⥤ W} (e : F ≅ F')
    (H : forall X : ContAction V G, ((F.mapAction G).obj X.obj).IsContinuous)
    (H' : forall X : ContAction V G, ((F'.mapAction G).obj X.obj).IsContinuous) :
    Functor.mapContAction G F H ≅ Functor.mapContAction G F' H' :=
  NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Action.mkIso (e.app X.obj.V) (by simp)))

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Continuous version of `Equivalence.mapAction`. -/
@[simps functor inverse]
/--
Definition of `Equivalence.mapContAction` / `Equivalence.mapContAction` 的定义

English:
definition Equivalence.mapContAction
  signature: (E : V ≌ W)
  body: E.functor.mapContAction G H₁
  inverse := E.inverse.mapContAction G H₂
  unitIso := Functor.mapContActionCongr G E.unitIso
      (fun X => X.2) (fun X => H₂ ((E.functor.mapContAction G H₁).obj X)) ≪≫
    Functor.mapContActionComp G _ _ _ _
  counitIso := (Functor.mapContActionComp G _ _ _ _).symm ≪≫

中文:
定义 Equivalence.mapContAction
  签名: (E : V ≌ W)
  定义体: E.functor.mapContAction G H₁
  inverse := E.inverse.mapContAction G H₂
  unitIso := Functor.mapContActionCongr G E.unitIso
      (fun X => X.2) (fun X => H₂ ((E.functor.mapContAction G H₁).obj X)) ≪≫
    Functor.mapContActionComp G _ _ _ _
  counitIso := (Functor.mapContActionComp G _ _ _ _).symm ≪≫

Depends on / 依赖: E.functor.mapContAction, functor, mapContAction
-/
def Equivalence.mapContAction (E : V ≌ W)
    (H₁ : forall X : ContAction V G, ((E.functor.mapAction G).obj X.obj).IsContinuous)
    (H₂ : forall X : ContAction W G, ((E.inverse.mapAction G).obj X.obj).IsContinuous) :
    ContAction V G ≌ ContAction W G where
  functor := E.functor.mapContAction G H₁
  inverse := E.inverse.mapContAction G H₂
  unitIso := Functor.mapContActionCongr G E.unitIso
      (fun X => X.2) (fun X => H₂ ((E.functor.mapContAction G H₁).obj X)) ≪≫
    Functor.mapContActionComp G _ _ _ _
  counitIso := (Functor.mapContActionComp G _ _ _ _).symm ≪≫
    Functor.mapContActionCongr G E.counitIso _ (fun X => X.2)

end CategoryTheory
