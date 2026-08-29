/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Wide pullbacks

We define the category `WidePullbackShape`, (resp. `WidePushoutShape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wideCospan` (`wideSpan`) constructs a functor from this category, hitting
the given morphisms.

We use `WidePullbackShape` to define ordinary pullbacks (pushouts) by using `J := WalkingPair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `HasWidePullbacks` and `HasFiniteWidePullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

@[expose] public section

universe w w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

variable (J : Type w)

/-- A wide pullback shape for any type `J` can be written simply as `Option J`. -/
@[implicit_reducible]
/--
Definition of `WidePullbackShape` / `WidePullbackShape` 的定义

English:
definition WidePullbackShape
  body: Option J

中文:
定义 WidePullbackShape
  定义体: Option J
-/
def WidePullbackShape := Option J

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (WidePullbackShape J)
  body: none

中文:
实例 :
  签名: 可居 (WidePullbackShape J)
  定义体: none
-/
instance : Inhabited (WidePullbackShape J) where
  default := none

/-- A wide pushout shape for any type `J` can be written simply as `Option J`. -/
@[implicit_reducible]
/--
Definition of `WidePushoutShape` / `WidePushoutShape` 的定义

English:
definition WidePushoutShape
  body: Option J

中文:
定义 WidePushoutShape
  定义体: Option J
-/
def WidePushoutShape := Option J

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (WidePushoutShape J)
  body: none

中文:
实例 :
  签名: 可居 (WidePushoutShape J)
  定义体: none
-/
instance : Inhabited (WidePushoutShape J) where
  default := none

namespace WidePullbackShape

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : WidePullbackShape J -> WidePullbackShape J -> Type w
  constructors (2):
    - id: forall X, Hom X X
    - term: forall j : J, Hom (some j) none

中文:
归纳类型 态射
  参数: : WidePullbackShape J -> WidePullbackShape J -> 类型 w
  构造子 (2 个):
    - id: 对任意 X, 态射 X X
    - term: 对任意 j : J, 态射 (some j) none
-/
inductive Hom : WidePullbackShape J -> WidePullbackShape J -> Type w
  | id : forall X, Hom X X
  | term : forall j : J, Hom (some j) none
  deriving DecidableEq

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instDecidableEqHom.decEq

/--
Instance `struct` / 实例 `struct`

English:
instance struct
  signature: : CategoryStruct (WidePullbackShape J) where
  body: Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _

中文:
实例 struct
  签名: : CategoryStruct (WidePullbackShape J) where
  定义体: Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _
-/
instance struct : CategoryStruct (WidePullbackShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _

/--
Instance `Hom.inhabited` / 实例 `Hom.inhabited`

English:
instance Hom.inhabited
  signature: : Inhabited (Hom (none : WidePullbackShape J) none)
  body: ⟨Hom.id (none : WidePullbackShape J)⟩

中文:
实例 态射.inhabited
  签名: : 可居 (态射 (none : WidePullbackShape J) none)
  定义体: ⟨Hom.id (none : WidePullbackShape J)⟩

Depends on / 依赖: Hom.id, WidePullbackShape
-/
instance Hom.inhabited : Inhabited (Hom (none : WidePullbackShape J) none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩

open Lean Elab Tactic
/- Pointing note: experimenting with manual scoping of aesop tactics. Attempted to define
aesop rule directing on `WidePushoutOut` and it didn't take for some reason -/
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
meta def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `subsingleton_hom` / 实例 `subsingleton_hom`

English:
instance subsingleton_hom
  signature: : Quiver.IsThin (WidePullbackShape J)
  body: fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl

中文:
实例 subsingleton_hom
  签名: : 箭图.IsThin (WidePullbackShape J)
  定义体: fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl

Depends on / 依赖: WidePullbackShape, casesm
-/
instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : SmallCategory (WidePullbackShape J)
  body: thin_category

@[simp]

中文:
实例 category
  签名: : 小范畴 (WidePullbackShape J)
  定义体: thin_category

@[simp]

Depends on / 依赖: thin_category
-/
instance category : SmallCategory (WidePullbackShape J) :=
  thin_category

@[simp]
/--
theorem `hom_id` / 定理 `hom_id`

English:
theorem hom_id
  given: (X : WidePullbackShape J)
  statement: Hom.id X = 𝟙 X
  proof: rfl

中文:
定理 hom_id
  条件: (X : WidePullbackShape J)
  结论: 态射.id X = 𝟙 X
  证明: rfl
-/
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
/--
Definition of `wideCospan` / `wideCospan` 的定义

English:
definition wideCospan
  signature: (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B)
  body: Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j

中文:
定义 wideCospan
  签名: (B : C) (objs : J -> C) (arrows : 对任意 j : J, objs j ⟶ B)
  定义体: Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j

Depends on / 依赖: Option.casesOn, casesOn
-/
def wideCospan (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `diagramIsoWideCospan` / `diagramIsoWideCospan` 的定义

English:
definition diagramIsoWideCospan
  signature: (F : WidePullbackShape J ⥤ C)
  body: NatIso.ofComponents fun j => eqToIso by cat_disch

中文:
定义 diagramIsoWideCospan
  签名: (F : WidePullbackShape J ⥤ C)
  定义体: NatIso.ofComponents fun j => eqToIso by cat_disch

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, eqToIso, ofComponents
-/
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
NatIso.ofComponents fun j => eqToIso by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct a cone over a wide cospan. -/
@[simps]
/--
Definition of `mkCone` / `mkCone` 的定义

English:
definition mkCone
  signature: {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : forall j, X ⟶ F.obj (some j))
  body: { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

中文:
定义 mkCone
  签名: {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : 对任意 j, X ⟶ F.obj (some j))
  定义体: { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

Depends on / 依赖: naturality
-/
def mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : forall j, X ⟶ F.obj (some j))
    (w : forall j, π j ≫ F.map (Hom.term j) = f) : Cone F :=
  { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivalenceOfEquiv` / `equivalenceOfEquiv` 的定义

English:
definition equivalenceOfEquiv
  signature: (J' : Type w') (h : J ≃ J')
  body: wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact 

中文:
定义 equivalenceOfEquiv
  签名: (J' : 类型 w') (h : J ≃ J')
  定义体: wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact 

Depends on / 依赖: Hom.term, wideCospan
-/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') :
    WidePullbackShape J ≌ WidePullbackShape J' where
  functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

@[simp]
/--
lemma `equivalenceOfEquiv_functor_obj_none` / 引理 `equivalenceOfEquiv_functor_obj_none`

English:
lemma equivalenceOfEquiv_functor_obj_none
  given: {ι ι' : Type*} (e : ι ≃ ι')
  proof: rfl

@[simp]

中文:
引理 equivalenceOfEquiv_functor_obj_none
  条件: {ι ι' : 类型} (e : ι ≃ ι')
  证明: rfl

@[simp]
-/
lemma equivalenceOfEquiv_functor_obj_none {ι ι' : Type*} (e : ι ≃ ι') :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj none = none := rfl

@[simp]
/--
lemma `equivalenceOfEquiv_functor_obj_some` / 引理 `equivalenceOfEquiv_functor_obj_some`

English:
lemma equivalenceOfEquiv_functor_obj_some
  given: {ι ι' : Type*} (e : ι ≃ ι') (i)
  proof: rfl

@[simp]

中文:
引理 equivalenceOfEquiv_functor_obj_some
  条件: {ι ι' : 类型} (e : ι ≃ ι') (i)
  证明: rfl

@[simp]
-/
lemma equivalenceOfEquiv_functor_obj_some {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj (some i) = some (e i) := rfl

@[simp]
/--
lemma `equivalenceOfEquiv_functor_map_term` / 引理 `equivalenceOfEquiv_functor_map_term`

English:
lemma equivalenceOfEquiv_functor_map_term
  given: {ι ι' : Type*} (e : ι ≃ ι') (i)
  proof: rfl

中文:
引理 equivalenceOfEquiv_functor_map_term
  条件: {ι ι' : 类型} (e : ι ≃ ι') (i)
  证明: rfl
-/
lemma equivalenceOfEquiv_functor_map_term {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.map (.term i) = .term (e i) := rfl

attribute [local instance] uliftCategory in
/--
Definition of `uliftEquivalence` / `uliftEquivalence` 的定义

English:
definition uliftEquivalence
  signature: :
  body: (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

中文:
定义 uliftEquivalence
  签名: :
  定义体: (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

Depends on / 依赖: Equiv.ulift, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, WidePullbackShape, equivalenceOfEquiv, symm.trans
-/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ WidePullbackShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

/-- Show two functors out of a wide pullback shape are isomorphic by showing their components are
isomorphic. -/
@[simps!]
/--
Definition of `functorExt` / `functorExt` 的定义

English:
definition functorExt
  signature: {ι : Type*} {F G : WidePullbackShape ι ⥤ C}
  body: NatIso.ofComponents
    (fun i => match i with
      | none => base
      | some i => comp i)
    (fun f => by rcases f <;> simp [w])

中文:
定义 functorExt
  签名: {ι : 类型} {F G : WidePullbackShape ι ⥤ C}
  定义体: NatIso.ofComponents
    (fun i => match i with
      | none => base
      | some i => comp i)
    (fun f => by rcases f <;> simp [w])

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def functorExt {ι : Type*} {F G : WidePullbackShape ι ⥤ C}
    (base : F.obj none ≅ G.obj none) (comp : forall i, F.obj (some i) ≅ G.obj (some i))
    (w : forall i, F.map (.term i) ≫ base.hom = (comp i).hom ≫ G.map (.term i) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents
    (fun i => match i with
      | none => base
      | some i => comp i)
    (fun f => by rcases f <;> simp [w])

end WidePullbackShape

namespace WidePushoutShape

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : WidePushoutShape J -> WidePushoutShape J -> Type w
  constructors (2):
    - id: forall X, Hom X X
    - init: forall j : J, Hom none (some j)

中文:
归纳类型 态射
  参数: : WidePushoutShape J -> WidePushoutShape J -> 类型 w
  构造子 (2 个):
    - id: 对任意 X, 态射 X X
    - init: 对任意 j : J, 态射 none (some j)
-/
inductive Hom : WidePushoutShape J -> WidePushoutShape J -> Type w
  | id : forall X, Hom X X
  | init : forall j : J, Hom none (some j)
  deriving DecidableEq

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instDecidableEqHom.decEq

/--
Instance `struct` / 实例 `struct`

English:
instance struct
  signature: : CategoryStruct (WidePushoutShape J) where
  body: Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.init _

中文:
实例 struct
  签名: : CategoryStruct (WidePushoutShape J) where
  定义体: Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.init _
-/
instance struct : CategoryStruct (WidePushoutShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.init _

/--
Instance `Hom.inhabited` / 实例 `Hom.inhabited`

English:
instance Hom.inhabited
  signature: : Inhabited (Hom (none : WidePushoutShape J) none)
  body: ⟨Hom.id (none : WidePushoutShape J)⟩

中文:
实例 态射.inhabited
  签名: : 可居 (态射 (none : WidePushoutShape J) none)
  定义体: ⟨Hom.id (none : WidePushoutShape J)⟩
-/
instance Hom.inhabited : Inhabited (Hom (none : WidePushoutShape J) none) :=
  ⟨Hom.id (none : WidePushoutShape J)⟩

open Lean Elab Tactic
-- Pointing note: experimenting with manual scoping of aesop tactics; only this worked
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
meta def evalCasesBash' : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePushoutShape _,
      (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash'

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `subsingleton_hom` / 实例 `subsingleton_hom`

English:
instance subsingleton_hom
  signature: : Quiver.IsThin (WidePushoutShape J)
  body: fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl

中文:
实例 subsingleton_hom
  签名: : 箭图.IsThin (WidePushoutShape J)
  定义体: fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl

Depends on / 依赖: WidePushoutShape, casesm, repeat
-/
instance subsingleton_hom : Quiver.IsThin (WidePushoutShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : SmallCategory (WidePushoutShape J)
  body: thin_category

@[simp]

中文:
实例 category
  签名: : 小范畴 (WidePushoutShape J)
  定义体: thin_category

@[simp]

Depends on / 依赖: thin_category
-/
instance category : SmallCategory (WidePushoutShape J) :=
  thin_category

@[simp]
/--
theorem `hom_id` / 定理 `hom_id`

English:
theorem hom_id
  given: (X : WidePushoutShape J)
  statement: Hom.id X = 𝟙 X
  proof: rfl

中文:
定理 hom_id
  条件: (X : WidePushoutShape J)
  结论: 态射.id X = 𝟙 X
  证明: rfl
-/
theorem hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
/--
Definition of `wideSpan` / `wideSpan` 的定义

English:
definition wideSpan
  signature: (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j)
  body: Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [hom_id, Category.id_comp]; congr
    · cases g
      simp only [hom_id, Category.comp_id]; congr

中文:
定义 wideSpan
  签名: (B : C) (objs : J -> C) (arrows : 对任意 j : J, B ⟶ objs j)
  定义体: Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [hom_id, Category.id_comp]; congr
    · cases g
      simp only [hom_id, Category.comp_id]; congr

Depends on / 依赖: Option.casesOn, casesOn
-/
def wideSpan (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j) : WidePushoutShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [hom_id, Category.id_comp]; congr
    · cases g
      simp only [hom_id, Category.comp_id]; congr

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `diagramIsoWideSpan` / `diagramIsoWideSpan` 的定义

English:
definition diagramIsoWideSpan
  signature: (F : WidePushoutShape J ⥤ C)
  body: NatIso.ofComponents fun j => eqToIso by cases j; repeat rfl

中文:
定义 diagramIsoWideSpan
  签名: (F : WidePushoutShape J ⥤ C)
  定义体: NatIso.ofComponents fun j => eqToIso by cases j; repeat rfl

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents, repeat
-/
def diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) :
    F ≅ wideSpan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.init j) :=
NatIso.ofComponents fun j => eqToIso by cases j; repeat rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct a cocone over a wide span. -/
@[simps]
/--
Definition of `mkCocone` / `mkCocone` 的定义

English:
definition mkCocone
  signature: {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : forall j, F.obj (some j) ⟶ X)
  body: { pt := X
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

中文:
定义 mkCocone
  签名: {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : 对任意 j, F.obj (some j) ⟶ X)
  定义体: { pt := X
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

Depends on / 依赖: naturality
-/
def mkCocone {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : forall j, F.obj (some j) ⟶ X)
    (w : forall j, F.map (Hom.init j) ≫ ι j = f) : Cocone F :=
  { pt := X
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivalenceOfEquiv` / `equivalenceOfEquiv` 的定义

English:
definition equivalenceOfEquiv
  signature: (J' : Type w') (h : J ≃ J')
  body: wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqTo

中文:
定义 equivalenceOfEquiv
  签名: (J' : 类型 w') (h : J ≃ J')
  定义体: wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqTo

Depends on / 依赖: Hom.init, wideSpan
-/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePushoutShape J ≌ WidePushoutShape J' where
  functor := wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

attribute [local instance] uliftCategory in
/--
Definition of `uliftEquivalence` / `uliftEquivalence` 的定义

English:
definition uliftEquivalence
  signature: :
  body: (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePushoutShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

中文:
定义 uliftEquivalence
  签名: :
  定义体: (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePushoutShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

Depends on / 依赖: Equiv.ulift, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, WidePushoutShape, equivalenceOfEquiv, symm.trans
-/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePushoutShape J)) ≌ WidePushoutShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePushoutShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

end WidePushoutShape

variable (C : Type u) [Category.{v} C]

/--
Definition of `HasWidePullbacks` / `HasWidePullbacks` 的定义

English:
abbreviation HasWidePullbacks
  signature: : Prop
  body: forall J : Type w, HasLimitsOfShape (WidePullbackShape J) C

中文:
缩写 HasWidePullbacks
  签名: : 命题
  定义体: forall J : Type w, HasLimitsOfShape (WidePullbackShape J) C

Depends on / 依赖: HasLimitsOfShape, WidePullbackShape, nil_mem_paths
-/
abbrev HasWidePullbacks : Prop :=
  forall J : Type w, HasLimitsOfShape (WidePullbackShape J) C

/--
Definition of `HasWidePushouts` / `HasWidePushouts` 的定义

English:
abbreviation HasWidePushouts
  signature: : Prop
  body: forall J : Type w, HasColimitsOfShape (WidePushoutShape J) C

中文:
缩写 HasWidePushouts
  签名: : 命题
  定义体: forall J : Type w, HasColimitsOfShape (WidePushoutShape J) C

Depends on / 依赖: HasColimitsOfShape, WidePushoutShape
-/
abbrev HasWidePushouts : Prop :=
  forall J : Type w, HasColimitsOfShape (WidePushoutShape J) C

variable {C J}

/--
Definition of `HasWidePullback` / `HasWidePullback` 的定义

English:
abbreviation HasWidePullback
  signature: (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B)
  body: HasLimit (WidePullbackShape.wideCospan B objs arrows)

中文:
缩写 HasWidePullback
  签名: (B : C) (objs : J -> C) (arrows : 对任意 j : J, objs j ⟶ B)
  定义体: HasLimit (WidePullbackShape.wideCospan B objs arrows)

Depends on / 依赖: HasLimit, WidePullbackShape, WidePullbackShape.wideCospan, arrows, wideCospan
-/
abbrev HasWidePullback (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)

/--
Definition of `HasWidePushout` / `HasWidePushout` 的定义

English:
abbreviation HasWidePushout
  signature: (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j)
  body: HasColimit (WidePushoutShape.wideSpan B objs arrows)

中文:
缩写 HasWidePushout
  签名: (B : C) (objs : J -> C) (arrows : 对任意 j : J, B ⟶ objs j)
  定义体: HasColimit (WidePushoutShape.wideSpan B objs arrows)

Depends on / 依赖: HasColimit, WidePushoutShape, WidePushoutShape.wideSpan, arrows, wideSpan
-/
abbrev HasWidePushout (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j) : Prop :=
  HasColimit (WidePushoutShape.wideSpan B objs arrows)

/--
Definition of `widePullback` / `widePullback` 的定义

English:
abbreviation widePullback
  signature: (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B)
  body: limit (WidePullbackShape.wideCospan B objs arrows)

中文:
缩写 widePullback
  签名: (B : C) (objs : J -> C) (arrows : 对任意 j : J, objs j ⟶ B)
  定义体: limit (WidePullbackShape.wideCospan B objs arrows)

Depends on / 依赖: WidePullbackShape, WidePullbackShape.wideCospan, arrows, wideCospan
-/
noncomputable abbrev widePullback (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B)
    [HasWidePullback B objs arrows] : C :=
  limit (WidePullbackShape.wideCospan B objs arrows)

/--
Definition of `widePushout` / `widePushout` 的定义

English:
abbreviation widePushout
  signature: (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j)
  body: colimit (WidePushoutShape.wideSpan B objs arrows)

中文:
缩写 widePushout
  签名: (B : C) (objs : J -> C) (arrows : 对任意 j : J, B ⟶ objs j)
  定义体: colimit (WidePushoutShape.wideSpan B objs arrows)

Depends on / 依赖: WidePushoutShape, WidePushoutShape.wideSpan, arrows, colimit, wideSpan
-/
noncomputable abbrev widePushout (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j)
    [HasWidePushout B objs arrows] : C :=
  colimit (WidePushoutShape.wideSpan B objs arrows)

namespace WidePullback

variable {C : Type u} [Category.{v} C] {B : C} {objs : J -> C} (arrows : forall j : J, objs j ⟶ B)
variable [HasWidePullback B objs arrows]

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: (j : J)
  body: limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)

中文:
缩写 π
  签名: (j : J)
  定义体: limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)

Depends on / 依赖: Option.some, W.paths.id_mem, W.paths.map_mem_strictMap, WidePullbackShape, WidePullbackShape.wideCospan, id_mem, map_mem_strictMap, pathComposition, wideCospan
-/
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)


/--
Definition of `base` / `base` 的定义

English:
abbreviation base
  signature: : widePullback _ _ arrows ⟶ B
  body: limit.π (WidePullbackShape.wideCospan _ _ _) Option.none

@[reassoc (attr := simp)]

中文:
缩写 base
  签名: : widePullback _ _ arrows ⟶ B
  定义体: limit.π (WidePullbackShape.wideCospan _ _ _) Option.none

@[reassoc (attr := simp)]

Depends on / 依赖: Option.none, WidePullbackShape, WidePullbackShape.wideCospan, wideCospan
-/
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none

@[reassoc (attr := simp)]
/--
theorem `π_arrow` / 定理 `π_arrow`

English:
theorem π_arrow
  given: (j : J)
  statement: π arrows j ≫ arrows _ = base arrows
  proof: by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)

中文:
定理 π_arrow
  条件: (j : J)
  结论: π arrows j ≫ arrows _ = base arrows
  证明: by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)

Depends on / 依赖: WidePullbackShape, WidePullbackShape.Hom.term, WidePullbackShape.wideCospan, limit.w, wideCospan
-/
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)

variable {arrows} in
/--
Definition of `lift` / `lift` 的定义

English:
abbreviation lift
  signature: {X : C} (f : X ⟶ B) (fs : forall j : J, X ⟶ objs j)
  body: limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)

中文:
缩写 lift
  签名: {X : C} (f : X ⟶ B) (fs : 对任意 j : J, X ⟶ objs j)
  定义体: limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)

Depends on / 依赖: WidePullbackShape, WidePullbackShape.mkCone, WidePullbackShape.wideCospan, limit.lift, mkCone, wideCospan
-/
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : forall j : J, X ⟶ objs j)
    (w : forall j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)

variable {X : C} (f : X ⟶ B) (fs : forall j : J, X ⟶ objs j) (w : forall j, fs j ≫ arrows j = f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `lift_π` / 定理 `lift_π`

English:
theorem lift_π
  given: (j : J)
  statement: lift f fs w ≫ π arrows j = fs _
  proof: by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

中文:
定理 lift_π
  条件: (j : J)
  结论: lift f fs w ≫ π arrows j = fs _
  证明: by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

Depends on / 依赖: WidePullbackShape, WidePullbackShape.mkCone_, limit.lift_
-/
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `lift_base` / 定理 `lift_base`

English:
theorem lift_base
  statement: lift f fs w ≫ base arrows = f
  proof: by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

中文:
定理 lift_base
  结论: lift f fs w ≫ base arrows = f
  证明: by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

Depends on / 依赖: WidePullbackShape, WidePullbackShape.mkCone_, limit.lift_
-/
theorem lift_base : lift f fs w ≫ base arrows = f := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

/--
theorem `eq_lift_of_comp_eq` / 定理 `eq_lift_of_comp_eq`

English:
theorem eq_lift_of_comp_eq
  given: (g : X ⟶ widePullback _ _ arrows)
  proof: by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

中文:
定理 eq_lift_of_comp_eq
  条件: (g : X ⟶ widePullback _ _ arrows)
  证明: by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

Depends on / 依赖: WidePullbackShape, WidePullbackShape.mkCone, WidePullbackShape.wideCospan, arrows, isLimit, limit.isLimit, mkCone, wideCospan
-/
theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (forall j : J, g ≫ π arrows j = fs j) -> g ≫ base arrows = f -> g = lift f fs w := by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_eq_lift` / 定理 `hom_eq_lift`

English:
theorem hom_eq_lift
  given: (g : X ⟶ widePullback _ _ arrows)
  proof: by
  aesop

@[ext 1100]

中文:
定理 hom_eq_lift
  条件: (g : X ⟶ widePullback _ _ arrows)
  证明: by
  aesop

@[ext 1100]

Depends on / 依赖: Category
-/
theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by simp) := by
  aesop

@[ext 1100]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: (g1 g2 : X ⟶ widePullback _ _ arrows)
  statement: (forall j : J,
  proof: by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

中文:
定理 hom_ext
  条件: (g1 g2 : X ⟶ widePullback _ _ arrows)
  结论: (对任意 j : J,
  证明: by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

Depends on / 依赖: hom_ext, limit.hom_ext
-/
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (forall j : J,
    g1 ≫ π arrows j = g2 ≫ π arrows j) -> g1 ≫ base arrows = g2 ≫ base arrows -> g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end WidePullback

/--
Definition of `WidePullbackCone` / `WidePullbackCone` 的定义

English:
abbreviation WidePullbackCone
  signature: {ι : Type*} {X : C} {Y : ι -> C} (f : forall i, Y i ⟶ X)
  body: Cone (WidePullbackShape.wideCospan X Y f)

中文:
缩写 WidePullbackCone
  签名: {ι : 类型} {X : C} {Y : ι -> C} (f : 对任意 i, Y i ⟶ X)
  定义体: Cone (WidePullbackShape.wideCospan X Y f)

Depends on / 依赖: WidePullbackShape, WidePullbackShape.wideCospan, wideCospan
-/
abbrev WidePullbackCone {ι : Type*} {X : C} {Y : ι -> C} (f : forall i, Y i ⟶ X) :=
  Cone (WidePullbackShape.wideCospan X Y f)

namespace WidePullbackCone

variable {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X}

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: (s : WidePullbackCone f) (i : ι)
  body: (Cone.π s).app (some i)

中文:
定义 π
  签名: (s : WidePullbackCone f) (i : ι)
  定义体: (Cone.π s).app (some i)
-/
def π (s : WidePullbackCone f) (i : ι) : s.pt ⟶ Y i :=
  (Cone.π s).app (some i)

/--
Definition of `base` / `base` 的定义

English:
definition base
  signature: (s : WidePullbackCone f)
  body: (Cone.π s).app none

中文:
定义 base
  签名: (s : WidePullbackCone f)
  定义体: (Cone.π s).app none
-/
def base (s : WidePullbackCone f) : s.pt ⟶ X :=
  (Cone.π s).app none

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `condition` / 引理 `condition`

English:
lemma condition
  given: (s : WidePullbackCone f) (i : ι)
  statement: s.π i ≫ f i = s.base
  proof: by
  simpa using! ((Cone.π s).naturality (.term i)).symm

中文:
引理 condition
  条件: (s : WidePullbackCone f) (i : ι)
  结论: s.π i ≫ f i = s.base
  证明: by
  simpa using! ((Cone.π s).naturality (.term i)).symm

Depends on / 依赖: naturality
-/
lemma condition (s : WidePullbackCone f) (i : ι) : s.π i ≫ f i = s.base := by
  simpa using! ((Cone.π s).naturality (.term i)).symm

/-- Construct a wide pullback cone from the projections. -/
@[simps! pt]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = b)
  body: WidePullbackShape.mkCone b π h

@[simp]

中文:
定义 mk
  签名: {W : C} (b : W ⟶ X) (π : 对任意 i, W ⟶ Y i) (h : 对任意 i, π i ≫ f i = b)
  定义体: WidePullbackShape.mkCone b π h

@[simp]

Depends on / 依赖: WidePullbackShape, WidePullbackShape.mkCone, mkCone
-/
def mk {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = b) :
    WidePullbackCone f :=
  WidePullbackShape.mkCone b π h

@[simp]
/--
lemma `mk_base` / 引理 `mk_base`

English:
lemma mk_base
  given: {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = b)
  proof: rfl

@[simp]

中文:
引理 mk_base
  条件: {W : C} (b : W ⟶ X) (π : 对任意 i, W ⟶ Y i) (h : 对任意 i, π i ≫ f i = b)
  证明: rfl

@[simp]
-/
lemma mk_base {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = b) :
    (WidePullbackCone.mk b π h).base = b := rfl

@[simp]
/--
lemma `mk_π` / 引理 `mk_π`

English:
lemma mk_π
  given: {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = b) (i : ι)
  proof: rfl

中文:
引理 mk_π
  条件: {W : C} (b : W ⟶ X) (π : 对任意 i, W ⟶ Y i) (h : 对任意 i, π i ≫ f i = b) (i : ι)
  证明: rfl
-/
lemma mk_π {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = b) (i : ι) :
    (WidePullbackCone.mk b π h).π i = π i := rfl

/--
Definition of `IsLimit.mk` / `IsLimit.mk` 的定义

English:
definition IsLimit.mk
  signature: (s : WidePullbackCone f) (lift : forall t : WidePullbackCone f, t.pt ⟶ s.pt)
  body: lift
  fac t j := by
    cases j
    · exact facbase t
    · exact facπ t _
  uniq t m hm := uniq _ _ (hm none) fun _ => hm (some _)

中文:
定义 是极限.mk
  签名: (s : WidePullbackCone f) (lift : 对任意 t : WidePullbackCone f, t.pt ⟶ s.pt)
  定义体: lift
  fac t j := by
    cases j
    · exact facbase t
    · exact facπ t _
  uniq t m hm := uniq _ _ (hm none) fun _ => hm (some _)
-/
def IsLimit.mk (s : WidePullbackCone f) (lift : forall t : WidePullbackCone f, t.pt ⟶ s.pt)
    (facbase : forall t, lift t ≫ s.base = t.base) (facπ : forall t i, lift t ≫ s.π i = t.π i)
    (uniq : forall (t) (m : t.pt ⟶ s.pt), m ≫ s.base = t.base -> (forall i, m ≫ s.π i = t.π i) -> m = lift t) :
    IsLimit s where
  lift := lift
  fac t j := by
    cases j
    · exact facbase t
    · exact facπ t _
  uniq t m hm := uniq _ _ (hm none) fun _ => hm (some _)

/--
lemma `IsLimit.hom_ext` / 引理 `IsLimit.hom_ext`

English:
lemma IsLimit.hom_ext
  statement: {s : WidePullbackCone f} (hs : IsLimit s)
  proof: by
  apply hs.hom_ext
  rintro (_ | j)
  · exact hbase
  · exact hπ j

中文:
引理 是极限.hom_ext
  结论: {s : WidePullbackCone f} (hs : 是极限 s)
  证明: by
  apply hs.hom_ext
  rintro (_ | j)
  · exact hbase
  · exact hπ j
-/
lemma IsLimit.hom_ext {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} {k l : W ⟶ s.pt} (hbase : k ≫ s.base = l ≫ s.base)
    (hπ : forall i, k ≫ s.π i = l ≫ s.π i) :
    k = l := by
  apply hs.hom_ext
  rintro (_ | j)
  · exact hbase
  · exact hπ j

/--
Definition of `IsLimit.lift` / `IsLimit.lift` 的定义

English:
definition IsLimit.lift
  signature: {s : WidePullbackCone f} (hs : IsLimit s)
  body: hs.lift (WidePullbackCone.mk b a w)

@[reassoc (attr := simp)]

中文:
定义 是极限.lift
  签名: {s : WidePullbackCone f} (hs : 是极限 s)
  定义体: hs.lift (WidePullbackCone.mk b a w)

@[reassoc (attr := simp)]
-/
def IsLimit.lift {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : forall i, W ⟶ Y i) (w : forall i, a i ≫ f i = b) :
    W ⟶ s.pt :=
  hs.lift (WidePullbackCone.mk b a w)

@[reassoc (attr := simp)]
/--
lemma `IsLimit.lift_base` / 引理 `IsLimit.lift_base`

English:
lemma IsLimit.lift_base
  statement: {s : WidePullbackCone f} (hs : IsLimit s)
  proof: hs.fac _ _

@[reassoc (attr := simp)]

中文:
引理 是极限.lift_base
  结论: {s : WidePullbackCone f} (hs : 是极限 s)
  证明: hs.fac _ _

@[reassoc (attr := simp)]

Depends on / 依赖: hs.fac
-/
lemma IsLimit.lift_base {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : forall i, W ⟶ Y i) (w : forall i, a i ≫ f i = b) :
    IsLimit.lift hs b a w ≫ s.base = b :=
  hs.fac _ _

@[reassoc (attr := simp)]
/--
lemma `IsLimit.lift_π` / 引理 `IsLimit.lift_π`

English:
lemma IsLimit.lift_π
  statement: {s : WidePullbackCone f} (hs : IsLimit s)
  proof: hs.fac _ _

中文:
引理 是极限.lift_π
  结论: {s : WidePullbackCone f} (hs : 是极限 s)
  证明: hs.fac _ _

Depends on / 依赖: Iso.refl, hs.fac
-/
lemma IsLimit.lift_π {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : forall i, W ⟶ Y i) (w : forall i, a i ≫ f i = b) (i : ι) :
    IsLimit.lift hs b a w ≫ s.π i = a i :=
  hs.fac _ _

/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {ι : Type*}
  body: Cone.ext e by
    rintro (_ | _)
    · exact base.symm
    · exact (π _).symm

中文:
定义 ext
  签名: {ι : 类型}
  定义体: Cone.ext e by
    rintro (_ | _)
    · exact base.symm
    · exact (π _).symm

Depends on / 依赖: Cone.ext, base.symm, cat_disch, e.hom
-/
def ext {ι : Type*}
    {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} {s t : WidePullbackCone f}
    (e : s.pt ≅ t.pt)
    (base : e.hom ≫ t.base = s.base := by cat_disch)
    (π : forall i, e.hom ≫ t.π i = s.π i := by cat_disch) :
    s ≅ t :=
Cone.ext e by
    rintro (_ | _)
    · exact base.symm
    · exact (π _).symm

/-- Reindex a wide pullback cone. -/
@[simps! pt]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : WidePullbackCone f)
  body: .mk s.base (fun i => s.π _) (by simp)

@[simp]

中文:
定义 reindex
  签名: {ι : 类型} {X : C} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X} (s : WidePullbackCone f)
  定义体: .mk s.base (fun i => s.π _) (by simp)

@[simp]

Depends on / 依赖: s.base
-/
def reindex {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    WidePullbackCone (fun i => f (e i)) :=
  .mk s.base (fun i => s.π _) (by simp)

@[simp]
/--
lemma `reindex_base` / 引理 `reindex_base`

English:
lemma reindex_base
  statement: {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : WidePullbackCone f)
  proof: rfl

@[simp]

中文:
引理 reindex_base
  结论: {ι : 类型} {X : C} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X} (s : WidePullbackCone f)
  证明: rfl

@[simp]
-/
lemma reindex_base {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    (s.reindex e).base = s.base := rfl

@[simp]
/--
lemma `reindex_π` / 引理 `reindex_π`

English:
lemma reindex_π
  statement: {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : WidePullbackCone f)
  proof: rfl

中文:
引理 reindex_π
  结论: {ι : 类型} {X : C} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X} (s : WidePullbackCone f)
  证明: rfl
-/
lemma reindex_π {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) (i : ι') :
    (s.reindex e).π i = s.π (e i) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `reindexIsLimitEquiv` / `reindexIsLimitEquiv` 的定义

English:
definition reindexIsLimitEquiv
  signature: {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X}
  body: (IsLimit.whiskerEquivalenceEquiv <| WidePullbackShape.equivalenceOfEquiv _ e.symm).trans
    IsLimit.equivOfNatIsoOfIso
      (WidePullbackShape.functorExt (Iso.refl X) (fun i => eqToIso (by simp))
        fun i => by simp [← eqToHom_naturality]) _ _
      (WidePullbackCone.ext (Iso.refl _) (by simp

中文:
定义 reindexIsLimitEquiv
  签名: {ι : 类型} {X : C} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X}
  定义体: (IsLimit.whiskerEquivalenceEquiv <| WidePullbackShape.equivalenceOfEquiv _ e.symm).trans
    IsLimit.equivOfNatIsoOfIso
      (WidePullbackShape.functorExt (Iso.refl X) (fun i => eqToIso (by simp))
        fun i => by simp [← eqToHom_naturality]) _ _
      (WidePullbackCone.ext (Iso.refl _) (by simp

Depends on / 依赖: IsLimit, IsLimit.equivOfNatIsoOfIso, IsLimit.whiskerEquivalenceEquiv, Iso.refl, WidePullbackCone, WidePullbackCone.ext, WidePullbackShape, WidePullbackShape.equivalenceOfEquiv, WidePullbackShape.functorExt, apply_symm_apply, e.apply_symm_apply, e.symm, eqToHom_naturality, eqToIso, equivOfNatIsoOfIso, equivalenceOfEquiv, functorExt, reindex, whiskerEquivalenceEquiv
-/
def reindexIsLimitEquiv {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X}
    (s : WidePullbackCone f) {ι' : Type*} (e : ι' ≃ ι) :
    IsLimit (s.reindex e) ≃ IsLimit s :=
(IsLimit.whiskerEquivalenceEquiv <| WidePullbackShape.equivalenceOfEquiv _ e.symm).trans
    IsLimit.equivOfNatIsoOfIso
      (WidePullbackShape.functorExt (Iso.refl X) (fun i => eqToIso (by simp))
        fun i => by simp [← eqToHom_naturality]) _ _
      (WidePullbackCone.ext (Iso.refl _) (by simp [base, reindex, mk])
        (fun i => by
          simp [π, reindex, mk,
            eqToHom_naturality (fun i => (Cone.π s).app (some i)) (e.apply_symm_apply i)]))

end WidePullbackCone

namespace WidePushout

variable {C : Type u} [Category.{v} C] {B : C} {objs : J -> C} (arrows : forall j : J, B ⟶ objs j)
variable [HasWidePushout B objs arrows]

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: (j : J)
  body: colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)

中文:
缩写 ι
  签名: (j : J)
  定义体: colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)

Depends on / 依赖: Option.some, WidePushoutShape, WidePushoutShape.wideSpan, colimit, wideSpan
-/
noncomputable abbrev ι (j : J) : objs j ⟶ widePushout _ _ arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)

/--
Definition of `head` / `head` 的定义

English:
abbreviation head
  signature: : B ⟶ widePushout B objs arrows
  body: colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none

@[reassoc, simp]

中文:
缩写 head
  签名: : B ⟶ widePushout B objs arrows
  定义体: colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none

@[reassoc, simp]

Depends on / 依赖: Option.none, WidePushoutShape, WidePushoutShape.wideSpan, colimit, wideSpan
-/
noncomputable abbrev head : B ⟶ widePushout B objs arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none

@[reassoc, simp]
/--
theorem `arrow_ι` / 定理 `arrow_ι`

English:
theorem arrow_ι
  given: (j : J)
  statement: arrows j ≫ ι arrows j = head arrows
  proof: by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)

中文:
定理 arrow_ι
  条件: (j : J)
  结论: arrows j ≫ ι arrows j = head arrows
  证明: by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)

Depends on / 依赖: WidePushoutShape, WidePushoutShape.Hom.init, WidePushoutShape.wideSpan, colimit, colimit.w, wideSpan
-/
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)

variable {arrows} in
/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: {X : C} (f : B ⟶ X) (fs : forall j : J, objs j ⟶ X)
  body: colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)

中文:
缩写 desc
  签名: {X : C} (f : B ⟶ X) (fs : 对任意 j : J, objs j ⟶ X)
  定义体: colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)

Depends on / 依赖: WidePushoutShape, WidePushoutShape.mkCocone, WidePushoutShape.wideSpan, arrows, colimit, colimit.desc, mkCocone, wideSpan
-/
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : forall j : J, objs j ⟶ X)
    (w : forall j, arrows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X :=
  colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)

variable {X : C} (f : B ⟶ X) (fs : forall j : J, objs j ⟶ X) (w : forall j, arrows j ≫ fs j = f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `ι_desc` / 定理 `ι_desc`

English:
theorem ι_desc
  given: (j : J)
  statement: ι arrows j ≫ desc f fs w = fs _
  proof: by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

中文:
定理 ι_desc
  条件: (j : J)
  结论: ι arrows j ≫ desc f fs w = fs _
  证明: by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

Depends on / 依赖: WidePushoutShape, WidePushoutShape.mkCocone_, colimit
-/
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `head_desc` / 定理 `head_desc`

English:
theorem head_desc
  statement: head arrows ≫ desc f fs w = f
  proof: by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

中文:
定理 head_desc
  结论: head arrows ≫ desc f fs w = f
  证明: by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

Depends on / 依赖: WidePushoutShape, WidePushoutShape.mkCocone_, colimit
-/
theorem head_desc : head arrows ≫ desc f fs w = f := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

/--
theorem `eq_desc_of_comp_eq` / 定理 `eq_desc_of_comp_eq`

English:
theorem eq_desc_of_comp_eq
  given: (g : widePushout _ _ arrows ⟶ X)
  proof: by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

中文:
定理 eq_desc_of_comp_eq
  条件: (g : widePushout _ _ arrows ⟶ X)
  证明: by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

Depends on / 依赖: WidePushoutShape, WidePushoutShape.mkCocone, WidePushoutShape.wideSpan, arrows, colimit, colimit.isColimit, isColimit, mkCocone, wideSpan
-/
theorem eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) :
    (forall j : J, ι arrows j ≫ g = fs j) -> head arrows ≫ g = f -> g = desc f fs w := by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_eq_desc` / 定理 `hom_eq_desc`

English:
theorem hom_eq_desc
  given: (g : widePushout _ _ arrows ⟶ X)
  proof: by
  cat_disch

@[ext 1100]

中文:
定理 hom_eq_desc
  条件: (g : widePushout _ _ arrows ⟶ X)
  证明: by
  cat_disch

@[ext 1100]

Depends on / 依赖: cat_disch
-/
theorem hom_eq_desc (g : widePushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j => by
        rw [← Category.assoc]
        simp := by
  cat_disch

@[ext 1100]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: (g1 g2 : widePushout _ _ arrows ⟶ X)
  statement: (forall j : J,
  proof: by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

中文:
定理 hom_ext
  条件: (g1 g2 : widePushout _ _ arrows ⟶ X)
  结论: (对任意 j : J,
  证明: by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext
-/
theorem hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) : (forall j : J,
    ι arrows j ≫ g1 = ι arrows j ≫ g2) -> head arrows ≫ g1 = head arrows ≫ g2 -> g1 = g2 := by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end WidePushout

variable (J)

/--
Definition of `widePullbackShapeOpMap` / `widePullbackShapeOpMap` 的定义

English:
definition widePullbackShapeOpMap
  signature: :

中文:
定义 widePullbackShapeOpMap
  签名: :

Depends on / 依赖: asEquivalence, isEquivalence_functor
-/
def widePullbackShapeOpMap :
    forall X Y : WidePullbackShape J,
      (X ⟶ Y) -> ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, WidePullbackShape.Hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, WidePullbackShape.Hom.term _ => Quiver.Hom.op (WidePushoutShape.Hom.init _)

/-- The obvious functor `WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
@[simps]
/--
Definition of `widePullbackShapeOp` / `widePullbackShapeOp` 的定义

English:
definition widePullbackShapeOp
  signature: : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  body: op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂

中文:
定义 widePullbackShapeOp
  签名: : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  定义体: op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂
-/
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  obj X := op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂

/--
Definition of `widePushoutShapeOpMap` / `widePushoutShapeOpMap` 的定义

English:
definition widePushoutShapeOpMap
  signature: :

中文:
定义 widePushoutShapeOpMap
  签名: :
-/
def widePushoutShapeOpMap :
    forall X Y : WidePushoutShape J,
      (X ⟶ Y) -> ((op X : (WidePullbackShape J)ᵒᵖ) ⟶ (op Y : (WidePullbackShape J)ᵒᵖ))
  | _, _, WidePushoutShape.Hom.id X => Quiver.Hom.op (WidePullbackShape.Hom.id _)
  | _, _, WidePushoutShape.Hom.init _ => Quiver.Hom.op (WidePullbackShape.Hom.term _)

/-- The obvious functor `WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
@[simps]
/--
Definition of `widePushoutShapeOp` / `widePushoutShapeOp` 的定义

English:
definition widePushoutShapeOp
  signature: : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  body: op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y

中文:
定义 widePushoutShapeOp
  签名: : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  定义体: op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y
-/
def widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  obj X := op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y

/-- The obvious functor `(WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J` -/
@[simps!]
/--
Definition of `widePullbackShapeUnop` / `widePullbackShapeUnop` 的定义

English:
definition widePullbackShapeUnop
  signature: : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J
  body: (widePullbackShapeOp J).leftOp

中文:
定义 widePullbackShapeUnop
  签名: : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J
  定义体: (widePullbackShapeOp J).leftOp

Depends on / 依赖: leftOp, widePullbackShapeOp
-/
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp

/-- The obvious functor `(WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J` -/
@[simps!]
/--
Definition of `widePushoutShapeUnop` / `widePushoutShapeUnop` 的定义

English:
definition widePushoutShapeUnop
  signature: : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J
  body: (widePushoutShapeOp J).leftOp

中文:
定义 widePushoutShapeUnop
  签名: : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J
  定义体: (widePushoutShapeOp J).leftOp

Depends on / 依赖: leftOp, widePushoutShapeOp
-/
def widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J :=
  (widePushoutShapeOp J).leftOp

/--
Definition of `widePushoutShapeOpUnop` / `widePushoutShapeOpUnop` 的定义

English:
definition widePushoutShapeOpUnop
  signature: : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 widePushoutShapeOpUnop
  签名: : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/--
Definition of `widePushoutShapeUnopOp` / `widePushoutShapeUnopOp` 的定义

English:
definition widePushoutShapeUnopOp
  signature: : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 widePushoutShapeUnopOp
  签名: : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/--
Definition of `widePullbackShapeOpUnop` / `widePullbackShapeOpUnop` 的定义

English:
definition widePullbackShapeOpUnop
  signature: : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 widePullbackShapeOpUnop
  签名: : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/--
Definition of `widePullbackShapeUnopOp` / `widePullbackShapeUnopOp` 的定义

English:
definition widePullbackShapeUnopOp
  signature: : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 widePullbackShapeUnopOp
  签名: : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The duality equivalence `(WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
@[simps]
/--
Definition of `widePushoutShapeOpEquiv` / `widePushoutShapeOpEquiv` 的定义

English:
definition widePushoutShapeOpEquiv
  signature: : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  body: widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J

中文:
定义 widePushoutShapeOpEquiv
  签名: : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  定义体: widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J

Depends on / 依赖: widePushoutShapeUnop
-/
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J

/-- The duality equivalence `(WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
@[simps]
/--
Definition of `widePullbackShapeOpEquiv` / `widePullbackShapeOpEquiv` 的定义

English:
definition widePullbackShapeOpEquiv
  signature: : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  body: widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J

中文:
定义 widePullbackShapeOpEquiv
  签名: : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  定义体: widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J

Depends on / 依赖: widePullbackShapeUnop
-/
def widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  functor := widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J

/--
theorem `hasWidePushouts_shrink` / 定理 `hasWidePushouts_shrink`

English:
theorem hasWidePushouts_shrink
  given: [HasWidePushouts.{max w w'} C]
  statement: HasWidePushouts.{w} C
  proof: fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

中文:
定理 hasWidePushouts_shrink
  条件: [HasWidePushouts.{最大值 w w'} C]
  结论: HasWidePushouts.{w} C
  证明: fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})
-/
theorem hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w} C := fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

/--
theorem `hasWidePullbacks_shrink` / 定理 `hasWidePullbacks_shrink`

English:
theorem hasWidePullbacks_shrink
  given: [HasWidePullbacks.{max w w'} C]
  statement: HasWidePullbacks.{w} C
  proof: fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

中文:
定理 hasWidePullbacks_shrink
  条件: [HasWidePullbacks.{最大值 w w'} C]
  结论: HasWidePullbacks.{w} C
  证明: fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})
-/
theorem hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks.{w} C := fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

end CategoryTheory.Limits
