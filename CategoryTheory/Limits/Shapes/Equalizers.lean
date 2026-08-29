/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject ${a ∈ A | f(a) = g(a)}$ known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `WalkingParallelPair` is the indexing category used for (co)equalizer diagrams
* `parallelPair` is a functor from `WalkingParallelPair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallelPair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `isIso_limit_cone_parallelPair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

@[expose] public section

section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v v₂ u u₂

/--
Inductive type `WalkingParallelPair` / 归纳类型 `WalkingParallelPair`

English:
inductive WalkingParallelPair
  parameters: : Type
  constructors (2):
    - zero: 
    - one: 

中文:
归纳类型 WalkingParallelPair
  参数: : Type
  构造子 (2 个):
    - zero: 
    - one: 
-/
inductive WalkingParallelPair : Type
  | zero
  | one
  deriving DecidableEq, Inhabited

open WalkingParallelPair

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `WalkingParallelPairHom` / 归纳类型 `WalkingParallelPairHom`

English:
inductive WalkingParallelPairHom
  parameters: : WalkingParallelPair -> WalkingParallelPair -> Type
  constructors (3):
    - left: WalkingParallelPairHom zero one
    - right: WalkingParallelPairHom zero one
    - id: (X : WalkingParallelPair) : WalkingParallelPairHom X X

中文:
归纳类型 WalkingParallelPairHom
  参数: : WalkingParallelPair -> WalkingParallelPair -> Type
  构造子 (3 个):
    - left: WalkingParallelPairHom zero one
    - right: WalkingParallelPairHom zero one
    - id: (X : WalkingParallelPair) : WalkingParallelPairHom X X
-/
inductive WalkingParallelPairHom : WalkingParallelPair -> WalkingParallelPair -> Type
  | left : WalkingParallelPairHom zero one
  | right : WalkingParallelPairHom zero one
  | id (X : WalkingParallelPair) : WalkingParallelPairHom X X
  deriving DecidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (WalkingParallelPairHom zero one)
  body: WalkingParallelPairHom.left

中文:
实例 :
  签名: Inhabited (WalkingParallelPairHom zero one)
  定义体: WalkingParallelPairHom.left

Depends on / 依赖: WalkingParallelPairHom, WalkingParallelPairHom.left
-/
instance : Inhabited (WalkingParallelPairHom zero one) where default := WalkingParallelPairHom.left

open WalkingParallelPairHom

/--
Definition of `WalkingParallelPairHom.comp` / `WalkingParallelPairHom.comp` 的定义

English:
definition WalkingParallelPairHom.comp
  signature: :

中文:
定义 WalkingParallelPairHom.comp
  签名: :
-/
def WalkingParallelPairHom.comp :
    forall {X Y Z : WalkingParallelPair} (_ : WalkingParallelPairHom X Y)
      (_ : WalkingParallelPairHom Y Z), WalkingParallelPairHom X Z
  | _, _, _, id _, h => h
  | _, _, _, left, id one => left
  | _, _, _, right, id one => right

/--
theorem `WalkingParallelPairHom.id_comp` / 定理 `WalkingParallelPairHom.id_comp`

English:
theorem WalkingParallelPairHom.id_comp
  proof: rfl

中文:
定理 WalkingParallelPairHom.id_comp
  证明: rfl
-/
theorem WalkingParallelPairHom.id_comp
    {X Y : WalkingParallelPair} (g : WalkingParallelPairHom X Y) : comp (id X) g = g :=
  rfl

/--
theorem `WalkingParallelPairHom.comp_id` / 定理 `WalkingParallelPairHom.comp_id`

English:
theorem WalkingParallelPairHom.comp_id
  proof: by
  cases f <;> rfl

中文:
定理 WalkingParallelPairHom.comp_id
  证明: by
  cases f <;> rfl
-/
theorem WalkingParallelPairHom.comp_id
    {X Y : WalkingParallelPair} (f : WalkingParallelPairHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl

/--
theorem `WalkingParallelPairHom.assoc` / 定理 `WalkingParallelPairHom.assoc`

English:
theorem WalkingParallelPairHom.assoc
  statement: {X Y Z W : WalkingParallelPair}
  proof: by
  cases f <;> cases g <;> cases h <;> rfl

中文:
定理 WalkingParallelPairHom.assoc
  结论: {X Y Z W : WalkingParallelPair}
  证明: by
  cases f <;> cases g <;> cases h <;> rfl
-/
theorem WalkingParallelPairHom.assoc {X Y Z W : WalkingParallelPair}
    (f : WalkingParallelPairHom X Y) (g : WalkingParallelPairHom Y Z)
    (h : WalkingParallelPairHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

/--
Instance `walkingParallelPairHomCategory` / 实例 `walkingParallelPairHomCategory`

English:
instance walkingParallelPairHomCategory
  signature: : SmallCategory WalkingParallelPair where
  body: WalkingParallelPairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]

中文:
实例 walkingParallelPairHomCategory
  签名: : SmallCategory WalkingParallelPair where
  定义体: WalkingParallelPairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]

Depends on / 依赖: WalkingParallelPairHom
-/
instance walkingParallelPairHomCategory : SmallCategory WalkingParallelPair where
  Hom := WalkingParallelPairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]
/--
theorem `walkingParallelPairHom_id` / 定理 `walkingParallelPairHom_id`

English:
theorem walkingParallelPairHom_id
  given: (X : WalkingParallelPair)
  statement: WalkingParallelPairHom.id X = 𝟙 X
  proof: rfl

中文:
定理 walkingParallelPairHom_id
  条件: (X : WalkingParallelPair)
  结论: WalkingParallelPairHom.id X = 𝟙 X
  证明: rfl
-/
theorem walkingParallelPairHom_id (X : WalkingParallelPair) : WalkingParallelPairHom.id X = 𝟙 X :=
  rfl

/-- The functor `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[implicit_reducible]
/--
Definition of `walkingParallelPairOp` / `walkingParallelPairOp` 的定义

English:
definition walkingParallelPairOp
  signature: : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where
  body: op match x with | zero => one | one => zero
  map f := by
    cases f <;> apply Quiver.Hom.op
    exacts [left, right, WalkingParallelPairHom.id _]
  map_comp := by rintro _ _ _ (_ | _ | _) g <;> cases g <;> rfl

@[simp]

中文:
定义 walkingParallelPairOp
  签名: : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where
  定义体: op match x with | zero => one | one => zero
  map f := by
    cases f <;> apply Quiver.Hom.op
    exacts [left, right, WalkingParallelPairHom.id _]
  map_comp := by rintro _ _ _ (_ | _ | _) g <;> cases g <;> rfl

@[simp]
-/
def walkingParallelPairOp : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where
obj x := op match x with | zero => one | one => zero
  map f := by
    cases f <;> apply Quiver.Hom.op
    exacts [left, right, WalkingParallelPairHom.id _]
  map_comp := by rintro _ _ _ (_ | _ | _) g <;> cases g <;> rfl

@[simp]
/--
theorem `walkingParallelPairOp_zero` / 定理 `walkingParallelPairOp_zero`

English:
theorem walkingParallelPairOp_zero
  statement: walkingParallelPairOp.obj zero = op one
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOp_zero
  结论: walkingParallelPairOp.obj zero = op one
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOp_zero : walkingParallelPairOp.obj zero = op one := rfl

@[simp]
/--
theorem `walkingParallelPairOp_one` / 定理 `walkingParallelPairOp_one`

English:
theorem walkingParallelPairOp_one
  statement: walkingParallelPairOp.obj one = op zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOp_one
  结论: walkingParallelPairOp.obj one = op zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOp_one : walkingParallelPairOp.obj one = op zero := rfl

@[simp]
/--
theorem `walkingParallelPairOp_left` / 定理 `walkingParallelPairOp_left`

English:
theorem walkingParallelPairOp_left
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOp_left
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOp_left :
    walkingParallelPairOp.map left = @Quiver.Hom.op _ _ zero one left := rfl

@[simp]
/--
theorem `walkingParallelPairOp_right` / 定理 `walkingParallelPairOp_right`

English:
theorem walkingParallelPairOp_right
  proof: rfl

中文:
定理 walkingParallelPairOp_right
  证明: rfl
-/
theorem walkingParallelPairOp_right :
    walkingParallelPairOp.map right = @Quiver.Hom.op _ _ zero one right := rfl

/--
The equivalence `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[simps functor inverse]
/--
Definition of `walkingParallelPairOpEquiv` / `walkingParallelPairOpEquiv` 的定义

English:
definition walkingParallelPairOpEquiv
  signature: : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ where
  body: walkingParallelPairOp
  inverse := walkingParallelPairOp.leftOp
  unitIso :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl))
      (by rintro _ _ (_ | _ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun j => eqToIso (by
            induction j with | _ X
            cases X 

中文:
定义 walkingParallelPairOpEquiv
  签名: : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ where
  定义体: walkingParallelPairOp
  inverse := walkingParallelPairOp.leftOp
  unitIso :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl))
      (by rintro _ _ (_ | _ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun j => eqToIso (by
            induction j with | _ X
            cases X 

Depends on / 依赖: walkingParallelPairOp
-/
def walkingParallelPairOpEquiv : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ where
  functor := walkingParallelPairOp
  inverse := walkingParallelPairOp.leftOp
  unitIso :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl))
      (by rintro _ _ (_ | _ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun j => eqToIso (by
            induction j with | _ X
            cases X <;> rfl))
      (fun {i} {j} f => by
      induction i with | _ i
      induction j with | _ j
      let g := f.unop
      have : f = g.op := rfl
      rw [this]
      cases i <;> cases j <;> cases g <;> rfl)
  functor_unitIso_comp := fun j => by cases j <;> rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_unitIso_zero` / 定理 `walkingParallelPairOpEquiv_unitIso_zero`

English:
theorem walkingParallelPairOpEquiv_unitIso_zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_unitIso_zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_unitIso_zero :
    walkingParallelPairOpEquiv.unitIso.app zero = Iso.refl zero := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_unitIso_one` / 定理 `walkingParallelPairOpEquiv_unitIso_one`

English:
theorem walkingParallelPairOpEquiv_unitIso_one
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_unitIso_one
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_unitIso_one :
    walkingParallelPairOpEquiv.unitIso.app one = Iso.refl one := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_counitIso_zero` / 定理 `walkingParallelPairOpEquiv_counitIso_zero`

English:
theorem walkingParallelPairOpEquiv_counitIso_zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_counitIso_zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_counitIso_zero :
    walkingParallelPairOpEquiv.counitIso.app (op zero) = Iso.refl (op zero) := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_counitIso_one` / 定理 `walkingParallelPairOpEquiv_counitIso_one`

English:
theorem walkingParallelPairOpEquiv_counitIso_one
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_counitIso_one
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_counitIso_one :
    walkingParallelPairOpEquiv.counitIso.app (op one) = Iso.refl (op one) :=
  rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_unitIso_hom_app_zero` / 定理 `walkingParallelPairOpEquiv_unitIso_hom_app_zero`

English:
theorem walkingParallelPairOpEquiv_unitIso_hom_app_zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_unitIso_hom_app_zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_unitIso_hom_app_zero :
    walkingParallelPairOpEquiv.unitIso.hom.app zero = 𝟙 zero := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_unitIso_hom_app_one` / 定理 `walkingParallelPairOpEquiv_unitIso_hom_app_one`

English:
theorem walkingParallelPairOpEquiv_unitIso_hom_app_one
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_unitIso_hom_app_one
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_unitIso_hom_app_one :
    walkingParallelPairOpEquiv.unitIso.hom.app one = 𝟙 one := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_unitIso_inv_app_zero` / 定理 `walkingParallelPairOpEquiv_unitIso_inv_app_zero`

English:
theorem walkingParallelPairOpEquiv_unitIso_inv_app_zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_unitIso_inv_app_zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_unitIso_inv_app_zero :
    walkingParallelPairOpEquiv.unitIso.inv.app zero = 𝟙 zero := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_unitIso_inv_app_one` / 定理 `walkingParallelPairOpEquiv_unitIso_inv_app_one`

English:
theorem walkingParallelPairOpEquiv_unitIso_inv_app_one
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_unitIso_inv_app_one
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_unitIso_inv_app_one :
    walkingParallelPairOpEquiv.unitIso.inv.app one = 𝟙 one := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_counitIso_hom_app_op_zero` / 定理 `walkingParallelPairOpEquiv_counitIso_hom_app_op_zero`

English:
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_counitIso_hom_app_op_zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_zero :
    walkingParallelPairOpEquiv.counitIso.hom.app (op zero) = 𝟙 (op zero) := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_counitIso_hom_app_op_one` / 定理 `walkingParallelPairOpEquiv_counitIso_hom_app_op_one`

English:
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_one
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_counitIso_hom_app_op_one
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_one :
    walkingParallelPairOpEquiv.counitIso.hom.app (op one) = 𝟙 (op one) :=
  rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_counitIso_inv_app_op_zero` / 定理 `walkingParallelPairOpEquiv_counitIso_inv_app_op_zero`

English:
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_zero
  proof: rfl

@[simp]

中文:
定理 walkingParallelPairOpEquiv_counitIso_inv_app_op_zero
  证明: rfl

@[simp]
-/
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_zero :
    walkingParallelPairOpEquiv.counitIso.inv.app (op zero) = 𝟙 (op zero) := rfl

@[simp]
/--
theorem `walkingParallelPairOpEquiv_counitIso_inv_app_op_one` / 定理 `walkingParallelPairOpEquiv_counitIso_inv_app_op_one`

English:
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_one
  proof: rfl

中文:
定理 walkingParallelPairOpEquiv_counitIso_inv_app_op_one
  证明: rfl
-/
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_one :
    walkingParallelPairOpEquiv.counitIso.inv.app (op one) = 𝟙 (op one) :=
  rfl

variable {C : Type u}
variable {X Y : C}

namespace parallelPair

/-- Implementation of `parallelPair`, do not use directly. -/
@[instance_reducible]
/--
Definition of `parallelPairObj` / `parallelPairObj` 的定义

English:
definition parallelPairObj
  signature: (X Y : C) (x : WalkingParallelPair)
  body: match x with
  | zero => X
  | one => Y

中文:
定义 parallelPairObj
  签名: (X Y : C) (x : WalkingParallelPair)
  定义体: match x with
  | zero => X
  | one => Y
-/
def parallelPairObj (X Y : C) (x : WalkingParallelPair) : C :=
  match x with
  | zero => X
  | one => Y

/--
theorem `parallelPairObj_zero` / 定理 `parallelPairObj_zero`

English:
theorem parallelPairObj_zero
  statement: parallelPairObj X Y zero = X
  proof: rfl

中文:
定理 parallelPairObj_zero
  结论: parallelPairObj X Y zero = X
  证明: rfl
-/
@[simp] theorem parallelPairObj_zero : parallelPairObj X Y zero = X := rfl
/--
theorem `parallelPairObj_one` / 定理 `parallelPairObj_one`

English:
theorem parallelPairObj_one
  statement: parallelPairObj X Y one = Y
  proof: rfl

中文:
定理 parallelPairObj_one
  结论: parallelPairObj X Y one = Y
  证明: rfl
-/
@[simp] theorem parallelPairObj_one : parallelPairObj X Y one = Y := rfl

variable [Category.{v} C]

/--
Definition of `parallelPairHom` / `parallelPairHom` 的定义

English:
definition parallelPairHom
  signature: (f g : X ⟶ Y) {x y : WalkingParallelPair} (h : x ⟶ y)
  body: match h with
  | .id _ => 𝟙 _
  | .left => f
  | .right => g

中文:
定义 parallelPairHom
  签名: (f g : X ⟶ Y) {x y : WalkingParallelPair} (h : x ⟶ y)
  定义体: match h with
  | .id _ => 𝟙 _
  | .left => f
  | .right => g
-/
def parallelPairHom (f g : X ⟶ Y) {x y : WalkingParallelPair} (h : x ⟶ y) :
    parallelPairObj X Y x ⟶ parallelPairObj X Y y :=
  match h with
  | .id _ => 𝟙 _
  | .left => f
  | .right => g

/--
theorem `parallelPairHom_id` / 定理 `parallelPairHom_id`

English:
theorem parallelPairHom_id
  given: {f g : X ⟶ Y} {x : WalkingParallelPair}
  proof: (rfl)

中文:
定理 parallelPairHom_id
  条件: {f g : X ⟶ Y} {x : WalkingParallelPair}
  证明: (rfl)
-/
@[simp] theorem parallelPairHom_id {f g : X ⟶ Y} {x : WalkingParallelPair} :
  parallelPairHom f g (𝟙 x) = 𝟙 (parallelPairObj X Y x) := (rfl)

/--
theorem `parallelPairHom_left` / 定理 `parallelPairHom_left`

English:
theorem parallelPairHom_left
  given: {f g : X ⟶ Y}
  proof: (rfl)

中文:
定理 parallelPairHom_left
  条件: {f g : X ⟶ Y}
  证明: (rfl)
-/
@[simp] theorem parallelPairHom_left {f g : X ⟶ Y} :
  parallelPairHom f g .left = f := (rfl)

/--
theorem `parallelPairHom_right` / 定理 `parallelPairHom_right`

English:
theorem parallelPairHom_right
  given: {f g : X ⟶ Y}
  proof: (rfl)

中文:
定理 parallelPairHom_right
  条件: {f g : X ⟶ Y}
  证明: (rfl)
-/
@[simp] theorem parallelPairHom_right {f g : X ⟶ Y} :
  parallelPairHom f g .right = g := (rfl)

end parallelPair

variable [Category.{v} C]

open parallelPair in
/-- `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
common domain and codomain. -/
@[implicit_reducible]
/--
Definition of `parallelPair` / `parallelPair` 的定义

English:
definition parallelPair
  signature: (f g : X ⟶ Y)
  body: parallelPairObj X Y x
  map h := parallelPairHom f g h
  map_comp := by rintro _ _ _ ⟨⟩ ⟨⟩ <;> simp

@[simp]

中文:
定义 parallelPair
  签名: (f g : X ⟶ Y)
  定义体: parallelPairObj X Y x
  map h := parallelPairHom f g h
  map_comp := by rintro _ _ _ ⟨⟩ ⟨⟩ <;> simp

@[simp]

Depends on / 依赖: parallelPairObj
-/
def parallelPair (f g : X ⟶ Y) : WalkingParallelPair ⥤ C where
  obj x := parallelPairObj X Y x
  map h := parallelPairHom f g h
  map_comp := by rintro _ _ _ ⟨⟩ ⟨⟩ <;> simp

@[simp]
/--
theorem `parallelPair_obj_zero` / 定理 `parallelPair_obj_zero`

English:
theorem parallelPair_obj_zero
  given: (f g : X ⟶ Y)
  statement: (parallelPair f g).obj zero = X
  proof: rfl

@[simp]

中文:
定理 parallelPair_obj_zero
  条件: (f g : X ⟶ Y)
  结论: (parallelPair f g).obj zero = X
  证明: rfl

@[simp]
-/
theorem parallelPair_obj_zero (f g : X ⟶ Y) : (parallelPair f g).obj zero = X := rfl

@[simp]
/--
theorem `parallelPair_obj_one` / 定理 `parallelPair_obj_one`

English:
theorem parallelPair_obj_one
  given: (f g : X ⟶ Y)
  statement: (parallelPair f g).obj one = Y
  proof: rfl

@[simp]

中文:
定理 parallelPair_obj_one
  条件: (f g : X ⟶ Y)
  结论: (parallelPair f g).obj one = Y
  证明: rfl

@[simp]
-/
theorem parallelPair_obj_one (f g : X ⟶ Y) : (parallelPair f g).obj one = Y := rfl

@[simp]
/--
theorem `parallelPair_map_left` / 定理 `parallelPair_map_left`

English:
theorem parallelPair_map_left
  given: (f g : X ⟶ Y)
  statement: (parallelPair f g).map left = f
  proof: rfl

@[simp]

中文:
定理 parallelPair_map_left
  条件: (f g : X ⟶ Y)
  结论: (parallelPair f g).map left = f
  证明: rfl

@[simp]
-/
theorem parallelPair_map_left (f g : X ⟶ Y) : (parallelPair f g).map left = f := rfl

@[simp]
/--
theorem `parallelPair_map_right` / 定理 `parallelPair_map_right`

English:
theorem parallelPair_map_right
  given: (f g : X ⟶ Y)
  statement: (parallelPair f g).map right = g
  proof: rfl

@[simp]

中文:
定理 parallelPair_map_right
  条件: (f g : X ⟶ Y)
  结论: (parallelPair f g).map right = g
  证明: rfl

@[simp]
-/
theorem parallelPair_map_right (f g : X ⟶ Y) : (parallelPair f g).map right = g := rfl

@[simp]
/--
theorem `parallelPair_functor_obj` / 定理 `parallelPair_functor_obj`

English:
theorem parallelPair_functor_obj
  given: {F : WalkingParallelPair ⥤ C} (j : WalkingParallelPair)
  proof: by cases j <;> rfl

中文:
定理 parallelPair_functor_obj
  条件: {F : WalkingParallelPair ⥤ C} (j : WalkingParallelPair)
  证明: by cases j <;> rfl
-/
theorem parallelPair_functor_obj {F : WalkingParallelPair ⥤ C} (j : WalkingParallelPair) :
    (parallelPair (F.map left) (F.map right)).obj j = F.obj j := by cases j <;> rfl

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
`parallelPair` -/
@[simps!]
/--
Definition of `diagramIsoParallelPair` / `diagramIsoParallelPair` 的定义

English:
definition diagramIsoParallelPair
  signature: (F : WalkingParallelPair ⥤ C)
  body: NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_ | _ | _) <;> simp)

中文:
定义 diagramIsoParallelPair
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_ | _ | _) <;> simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents
-/
def diagramIsoParallelPair (F : WalkingParallelPair ⥤ C) :
    F ≅ parallelPair (F.map left) (F.map right) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_ | _ | _) <;> simp)

/-- Constructor for natural transformations between parallel pairs. -/
@[simps]
/--
Definition of `parallelPairHomMk` / `parallelPairHomMk` 的定义

English:
definition parallelPairHomMk
  signature: {F G : WalkingParallelPair ⥤ C}
  body: by rintro (_ | _); exacts [p, q]
  naturality := by rintro _ _ (_ | _); all_goals cat_disch

中文:
定义 parallelPairHomMk
  签名: {F G : WalkingParallelPair ⥤ C}
  定义体: by rintro (_ | _); exacts [p, q]
  naturality := by rintro _ _ (_ | _); all_goals cat_disch

Depends on / 依赖: F.map, G.map, all_goals, cat_disch, exacts, naturality
-/
def parallelPairHomMk {F G : WalkingParallelPair ⥤ C}
    (p : F.obj zero ⟶ G.obj zero)
    (q : F.obj one ⟶ G.obj one)
    (hl : F.map left ≫ q = p ≫ G.map left := by cat_disch)
    (hr : F.map right ≫ q = p ≫ G.map right := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _); exacts [p, q]
  naturality := by rintro _ _ (_ | _); all_goals cat_disch

/-- Constructor for natural isomorphisms between parallel pairs. -/
@[simps!]
/--
Definition of `parallelPairIsoMk` / `parallelPairIsoMk` 的定义

English:
definition parallelPairIsoMk
  signature: {F G : WalkingParallelPair ⥤ C}
  body: NatIso.ofComponents (by rintro (_ | _); exacts [p, q])
    (by rintro _ _ (_ | _); all_goals cat_disch)

中文:
定义 parallelPairIsoMk
  签名: {F G : WalkingParallelPair ⥤ C}
  定义体: NatIso.ofComponents (by rintro (_ | _); exacts [p, q])
    (by rintro _ _ (_ | _); all_goals cat_disch)

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, all_goals, cat_disch, exacts, ofComponents, p.hom, q.hom
-/
def parallelPairIsoMk {F G : WalkingParallelPair ⥤ C}
    (p : F.obj zero ≅ G.obj zero)
    (q : F.obj one ≅ G.obj one)
    (hl : F.map left ≫ q.hom = p.hom ≫ G.map left := by cat_disch)
    (hr : F.map right ≫ q.hom = p.hom ≫ G.map right := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _); exacts [p, q])
    (by rintro _ _ (_ | _); all_goals cat_disch)

/--
Definition of `parallelPairHom` / `parallelPairHom` 的定义

English:
definition parallelPairHom
  signature: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  body: parallelPairHomMk p q

中文:
定义 parallelPairHom
  签名: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  定义体: parallelPairHomMk p q

Depends on / 依赖: parallelPairHomMk
-/
def parallelPairHom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : parallelPair f g ⟶ parallelPair f' g' :=
  parallelPairHomMk p q

/--
Definition of `parallelPairIso` / `parallelPairIso` 的定义

English:
definition parallelPairIso
  signature: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ≅ X') (q : Y ≅ Y')
  body: parallelPairIsoMk p q

@[simp]

中文:
定义 parallelPairIso
  签名: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ≅ X') (q : Y ≅ Y')
  定义体: parallelPairIsoMk p q

@[simp]

Depends on / 依赖: parallelPairIsoMk
-/
def parallelPairIso {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ≅ X') (q : Y ≅ Y')
    (wf : f ≫ q.hom = p.hom ≫ f') (wg : g ≫ q.hom = p.hom ≫ g') :
    parallelPair f g ≅ parallelPair f' g' := parallelPairIsoMk p q

@[simp]
/--
theorem `parallelPairHom_app_zero` / 定理 `parallelPairHom_app_zero`

English:
theorem parallelPairHom_app_zero
  statement: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
  proof: rfl

@[simp]

中文:
定理 parallelPairHom_app_zero
  结论: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
  证明: rfl

@[simp]
-/
theorem parallelPairHom_app_zero {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app zero = p :=
  rfl

@[simp]
/--
theorem `parallelPairHom_app_one` / 定理 `parallelPairHom_app_one`

English:
theorem parallelPairHom_app_one
  statement: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
  proof: rfl

中文:
定理 parallelPairHom_app_one
  结论: {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
  证明: rfl
-/
theorem parallelPairHom_app_one {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app one = q :=
  rfl

/-- Construct a natural isomorphism between functors out of the walking parallel pair from
its components. -/
@[simps!]
/--
Definition of `parallelPair.ext` / `parallelPair.ext` 的定义

English:
definition parallelPair.ext
  signature: {F G : WalkingParallelPair ⥤ C} (zero : F.obj zero ≅ G.obj zero)
  body: NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one])
    (by rintro _ _ ⟨_⟩ <;> simp [left, right])

中文:
定义 parallelPair.ext
  签名: {F G : WalkingParallelPair ⥤ C} (zero : F.obj zero ≅ G.obj zero)
  定义体: NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one])
    (by rintro _ _ ⟨_⟩ <;> simp [left, right])

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, cat_disch, exacts, ofComponents, one.hom, zero.hom
-/
def parallelPair.ext {F G : WalkingParallelPair ⥤ C} (zero : F.obj zero ≅ G.obj zero)
    (one : F.obj one ≅ G.obj one)
    (left : F.map left ≫ one.hom = zero.hom ≫ G.map left := by cat_disch)
    (right : F.map right ≫ one.hom = zero.hom ≫ G.map right := by cat_disch) : F ≅ G :=
  NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one])
    (by rintro _ _ ⟨_⟩ <;> simp [left, right])

/-- Construct a natural isomorphism between `parallelPair f g` and `parallelPair f' g'` given
equalities `f = f'` and `g = g'`. -/
@[simps!]
/--
Definition of `parallelPair.eqOfHomEq` / `parallelPair.eqOfHomEq` 的定义

English:
definition parallelPair.eqOfHomEq
  signature: {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g')
  body: parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

中文:
定义 parallelPair.eqOfHomEq
  签名: {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g')
  定义体: parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

Depends on / 依赖: Iso.refl, parallelPair, parallelPair.ext
-/
def parallelPair.eqOfHomEq {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    parallelPair f g ≅ parallelPair f' g' :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

/--
Definition of `Fork` / `Fork` 的定义

English:
abbreviation Fork
  signature: (f g : X ⟶ Y)
  body: Cone (parallelPair f g)

中文:
缩写 Fork
  签名: (f g : X ⟶ Y)
  定义体: Cone (parallelPair f g)

Depends on / 依赖: parallelPair
-/
abbrev Fork (f g : X ⟶ Y) :=
  Cone (parallelPair f g)

/--
Definition of `Cofork` / `Cofork` 的定义

English:
abbreviation Cofork
  signature: (f g : X ⟶ Y)
  body: Cocone (parallelPair f g)

中文:
缩写 Cofork
  签名: (f g : X ⟶ Y)
  定义体: Cocone (parallelPair f g)

Depends on / 依赖: Cocone, parallelPair
-/
abbrev Cofork (f g : X ⟶ Y) :=
  Cocone (parallelPair f g)

variable {f g : X ⟶ Y}

/--
Definition of `Fork.ι` / `Fork.ι` 的定义

English:
definition Fork.ι
  signature: (t : Fork f g)
  body: t.π.app zero

@[simp]

中文:
定义 Fork.ι
  签名: (t : Fork f g)
  定义体: t.π.app zero

@[simp]
-/
def Fork.ι (t : Fork f g) : t.pt ⟶ X :=
  t.π.app zero

@[simp]
/--
theorem `Fork.app_zero_eq_ι` / 定理 `Fork.app_zero_eq_ι`

English:
theorem Fork.app_zero_eq_ι
  given: (t : Fork f g)
  statement: t.π.app zero = t.ι
  proof: rfl

中文:
定理 Fork.app_zero_eq_ι
  条件: (t : Fork f g)
  结论: t.π.app zero = t.ι
  证明: rfl
-/
theorem Fork.app_zero_eq_ι (t : Fork f g) : t.π.app zero = t.ι :=
  rfl

/--
Definition of `Cofork.π` / `Cofork.π` 的定义

English:
definition Cofork.π
  signature: (t : Cofork f g)
  body: t.ι.app one

@[simp]

中文:
定义 Cofork.π
  签名: (t : Cofork f g)
  定义体: t.ι.app one

@[simp]
-/
def Cofork.π (t : Cofork f g) : Y ⟶ t.pt :=
  t.ι.app one

@[simp]
/--
theorem `Cofork.app_one_eq_π` / 定理 `Cofork.app_one_eq_π`

English:
theorem Cofork.app_one_eq_π
  given: (t : Cofork f g)
  statement: t.ι.app one = t.π
  proof: rfl

@[simp]

中文:
定理 Cofork.app_one_eq_π
  条件: (t : Cofork f g)
  结论: t.ι.app one = t.π
  证明: rfl

@[simp]
-/
theorem Cofork.app_one_eq_π (t : Cofork f g) : t.ι.app one = t.π :=
  rfl

@[simp]
/--
theorem `Fork.app_one_eq_ι_comp_left` / 定理 `Fork.app_one_eq_ι_comp_left`

English:
theorem Fork.app_one_eq_ι_comp_left
  given: (s : Fork f g)
  statement: s.π.app one = s.ι ≫ f
  proof: by
  rw [← s.app_zero_eq_ι]; rw [← s.w left]; rw [parallelPair_map_left]

@[reassoc]

中文:
定理 Fork.app_one_eq_ι_comp_left
  条件: (s : Fork f g)
  结论: s.π.app one = s.ι ≫ f
  证明: by
  rw [← s.app_zero_eq_ι]; rw [← s.w left]; rw [parallelPair_map_left]

@[reassoc]

Depends on / 依赖: parallelPair_map_left, s.app_zero_eq_
-/
theorem Fork.app_one_eq_ι_comp_left (s : Fork f g) : s.π.app one = s.ι ≫ f := by
  rw [← s.app_zero_eq_ι]; rw [← s.w left]; rw [parallelPair_map_left]

@[reassoc]
/--
theorem `Fork.app_one_eq_ι_comp_right` / 定理 `Fork.app_one_eq_ι_comp_right`

English:
theorem Fork.app_one_eq_ι_comp_right
  given: (s : Fork f g)
  statement: s.π.app one = s.ι ≫ g
  proof: by
  rw [← s.app_zero_eq_ι]; rw [← s.w right]; rw [parallelPair_map_right]

@[simp]

中文:
定理 Fork.app_one_eq_ι_comp_right
  条件: (s : Fork f g)
  结论: s.π.app one = s.ι ≫ g
  证明: by
  rw [← s.app_zero_eq_ι]; rw [← s.w right]; rw [parallelPair_map_right]

@[simp]

Depends on / 依赖: parallelPair_map_right, s.app_zero_eq_
-/
theorem Fork.app_one_eq_ι_comp_right (s : Fork f g) : s.π.app one = s.ι ≫ g := by
  rw [← s.app_zero_eq_ι]; rw [← s.w right]; rw [parallelPair_map_right]

@[simp]
/--
theorem `Cofork.app_zero_eq_comp_π_left` / 定理 `Cofork.app_zero_eq_comp_π_left`

English:
theorem Cofork.app_zero_eq_comp_π_left
  given: (s : Cofork f g)
  statement: s.ι.app zero = f ≫ s.π
  proof: by
  rw [← s.app_one_eq_π]; rw [← s.w left]; rw [parallelPair_map_left]

@[reassoc]

中文:
定理 Cofork.app_zero_eq_comp_π_left
  条件: (s : Cofork f g)
  结论: s.ι.app zero = f ≫ s.π
  证明: by
  rw [← s.app_one_eq_π]; rw [← s.w left]; rw [parallelPair_map_left]

@[reassoc]

Depends on / 依赖: parallelPair_map_left, s.app_one_eq_
-/
theorem Cofork.app_zero_eq_comp_π_left (s : Cofork f g) : s.ι.app zero = f ≫ s.π := by
  rw [← s.app_one_eq_π]; rw [← s.w left]; rw [parallelPair_map_left]

@[reassoc]
/--
theorem `Cofork.app_zero_eq_comp_π_right` / 定理 `Cofork.app_zero_eq_comp_π_right`

English:
theorem Cofork.app_zero_eq_comp_π_right
  given: (s : Cofork f g)
  statement: s.ι.app zero = g ≫ s.π
  proof: by
  rw [← s.app_one_eq_π]; rw [← s.w right]; rw [parallelPair_map_right]

中文:
定理 Cofork.app_zero_eq_comp_π_right
  条件: (s : Cofork f g)
  结论: s.ι.app zero = g ≫ s.π
  证明: by
  rw [← s.app_one_eq_π]; rw [← s.w right]; rw [parallelPair_map_right]

Depends on / 依赖: parallelPair_map_right, s.app_one_eq_
-/
theorem Cofork.app_zero_eq_comp_π_right (s : Cofork f g) : s.ι.app zero = g ≫ s.π := by
  rw [← s.app_one_eq_π]; rw [← s.w right]; rw [parallelPair_map_right]

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[simps, implicit_reducible]
/--
Definition of `Fork.ofι` / `Fork.ofι` 的定义

English:
definition Fork.ofι
  signature: {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  body: P
  π :=
    { app := fun X => by
        cases X
        · exact ι
        · exact ι ≫ f
      naturality := fun {X} {Y} f =>
        by cases X <;> cases Y <;> cases f <;> simp [w] }

中文:
定义 Fork.ofι
  签名: {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  定义体: P
  π :=
    { app := fun X => by
        cases X
        · exact ι
        · exact ι ≫ f
      naturality := fun {X} {Y} f =>
        by cases X <;> cases Y <;> cases f <;> simp [w] }
-/
def Fork.ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : Fork f g where
  pt := P
  π :=
    { app := fun X => by
        cases X
        · exact ι
        · exact ι ≫ f
      naturality := fun {X} {Y} f =>
        by cases X <;> cases Y <;> cases f <;> simp [w] }

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
`f ≫ π = g ≫ π`. -/
@[simps, implicit_reducible]
/--
Definition of `Cofork.ofπ` / `Cofork.ofπ` 的定义

English:
definition Cofork.ofπ
  signature: {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)
  body: P
  ι :=
    { app := fun X => WalkingParallelPair.casesOn X (f ≫ π) π
      naturality := fun i j f => by cases f <;> simp [w] }

@[simp]

中文:
定义 Cofork.ofπ
  签名: {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)
  定义体: P
  ι :=
    { app := fun X => WalkingParallelPair.casesOn X (f ≫ π) π
      naturality := fun i j f => by cases f <;> simp [w] }

@[simp]
-/
def Cofork.ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : Cofork f g where
  pt := P
  ι :=
    { app := fun X => WalkingParallelPair.casesOn X (f ≫ π) π
      naturality := fun i j f => by cases f <;> simp [w] }

@[simp]
/--
theorem `Fork.ι_ofι` / 定理 `Fork.ι_ofι`

English:
theorem Fork.ι_ofι
  given: {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  statement: (Fork.ofι ι w).ι = ι
  proof: rfl

@[simp]

中文:
定理 Fork.ι_ofι
  条件: {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  结论: (Fork.ofι ι w).ι = ι
  证明: rfl

@[simp]
-/
theorem Fork.ι_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : (Fork.ofι ι w).ι = ι :=
  rfl

@[simp]
/--
theorem `Cofork.π_ofπ` / 定理 `Cofork.π_ofπ`

English:
theorem Cofork.π_ofπ
  given: {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)
  statement: (Cofork.ofπ π w).π = π
  proof: rfl

@[reassoc]

中文:
定理 Cofork.π_ofπ
  条件: {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)
  结论: (Cofork.ofπ π w).π = π
  证明: rfl

@[reassoc]
-/
theorem Cofork.π_ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : (Cofork.ofπ π w).π = π :=
  rfl

@[reassoc]
/--
theorem `Fork.condition` / 定理 `Fork.condition`

English:
theorem Fork.condition
  given: (t : Fork f g)
  statement: t.ι ≫ f = t.ι ≫ g
  proof: by
  rw [← t.app_one_eq_ι_comp_left]; rw [← t.app_one_eq_ι_comp_right]

@[reassoc]

中文:
定理 Fork.condition
  条件: (t : Fork f g)
  结论: t.ι ≫ f = t.ι ≫ g
  证明: by
  rw [← t.app_one_eq_ι_comp_left]; rw [← t.app_one_eq_ι_comp_right]

@[reassoc]

Depends on / 依赖: t.app_one_eq_
-/
theorem Fork.condition (t : Fork f g) : t.ι ≫ f = t.ι ≫ g := by
  rw [← t.app_one_eq_ι_comp_left]; rw [← t.app_one_eq_ι_comp_right]

@[reassoc]
/--
theorem `Cofork.condition` / 定理 `Cofork.condition`

English:
theorem Cofork.condition
  given: (t : Cofork f g)
  statement: f ≫ t.π = g ≫ t.π
  proof: by
  rw [← t.app_zero_eq_comp_π_left]; rw [← t.app_zero_eq_comp_π_right]

中文:
定理 Cofork.condition
  条件: (t : Cofork f g)
  结论: f ≫ t.π = g ≫ t.π
  证明: by
  rw [← t.app_zero_eq_comp_π_left]; rw [← t.app_zero_eq_comp_π_right]

Depends on / 依赖: t.app_zero_eq_comp_
-/
theorem Cofork.condition (t : Cofork f g) : f ≫ t.π = g ≫ t.π := by
  rw [← t.app_zero_eq_comp_π_left]; rw [← t.app_zero_eq_comp_π_right]

/--
theorem `Fork.equalizer_ext` / 定理 `Fork.equalizer_ext`

English:
theorem Fork.equalizer_ext
  given: (s : Fork f g) {W : C} {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι)
  proof: by
      simp only [← Category.assoc]; exact congrArg (· ≫ f) h
    rw [s.app_one_eq_ι_comp_left]; rw [this]

中文:
定理 Fork.equalizer_ext
  条件: (s : Fork f g) {W : C} {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι)
  证明: by
      simp only [← Category.assoc]; exact congrArg (· ≫ f) h
    rw [s.app_one_eq_ι_comp_left]; rw [this]

Depends on / 依赖: Category, Category.assoc, s.app_one_eq_
-/
theorem Fork.equalizer_ext (s : Fork f g) {W : C} {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) :
    forall j : WalkingParallelPair, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by
    have : k ≫ ι s ≫ f = l ≫ ι s ≫ f := by
      simp only [← Category.assoc]; exact congrArg (· ≫ f) h
    rw [s.app_one_eq_ι_comp_left]; rw [this]

/--
theorem `Cofork.coequalizer_ext` / 定理 `Cofork.coequalizer_ext`

English:
theorem Cofork.coequalizer_ext
  statement: (s : Cofork f g) {W : C} {k l : s.pt ⟶ W}

中文:
定理 Cofork.coequalizer_ext
  结论: (s : Cofork f g) {W : C} {k l : s.pt ⟶ W}
-/
theorem Cofork.coequalizer_ext (s : Cofork f g) {W : C} {k l : s.pt ⟶ W}
    (h : Cofork.π s ≫ k = Cofork.π s ≫ l) : forall j : WalkingParallelPair, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by simp only [s.app_zero_eq_comp_π_left, Category.assoc, h]
  | one => h

/--
theorem `Fork.IsLimit.hom_ext` / 定理 `Fork.IsLimit.hom_ext`

English:
theorem Fork.IsLimit.hom_ext
  statement: {s : Fork f g} (hs : IsLimit s) {W : C} {k l : W ⟶ s.pt}
  proof: hs.hom_ext Fork.equalizer_ext _ h

中文:
定理 Fork.IsLimit.hom_ext
  结论: {s : Fork f g} (hs : IsLimit s) {W : C} {k l : W ⟶ s.pt}
  证明: hs.hom_ext Fork.equalizer_ext _ h

Depends on / 依赖: Fork.equalizer_ext, equalizer_ext, hom_ext, hs.hom_ext
-/
theorem Fork.IsLimit.hom_ext {s : Fork f g} (hs : IsLimit s) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ Fork.ι s = l ≫ Fork.ι s) : k = l :=
hs.hom_ext Fork.equalizer_ext _ h

/--
theorem `Cofork.IsColimit.hom_ext` / 定理 `Cofork.IsColimit.hom_ext`

English:
theorem Cofork.IsColimit.hom_ext
  statement: {s : Cofork f g} (hs : IsColimit s) {W : C} {k l : s.pt ⟶ W}
  proof: hs.hom_ext Cofork.coequalizer_ext _ h

@[reassoc (attr := simp)]

中文:
定理 Cofork.IsColimit.hom_ext
  结论: {s : Cofork f g} (hs : IsColimit s) {W : C} {k l : s.pt ⟶ W}
  证明: hs.hom_ext Cofork.coequalizer_ext _ h

@[reassoc (attr := simp)]

Depends on / 依赖: Cofork, Cofork.coequalizer_ext, coequalizer_ext, hom_ext, hs.hom_ext
-/
theorem Cofork.IsColimit.hom_ext {s : Cofork f g} (hs : IsColimit s) {W : C} {k l : s.pt ⟶ W}
    (h : Cofork.π s ≫ k = Cofork.π s ≫ l) : k = l :=
hs.hom_ext Cofork.coequalizer_ext _ h

@[reassoc (attr := simp)]
/--
theorem `Fork.IsLimit.lift_ι` / 定理 `Fork.IsLimit.lift_ι`

English:
theorem Fork.IsLimit.lift_ι
  given: {s t : Fork f g} (hs : IsLimit s)
  statement: hs.lift t ≫ s.ι = t.ι
  proof: hs.fac _ _

@[reassoc (attr := simp)]

中文:
定理 Fork.IsLimit.lift_ι
  条件: {s t : Fork f g} (hs : IsLimit s)
  结论: hs.lift t ≫ s.ι = t.ι
  证明: hs.fac _ _

@[reassoc (attr := simp)]

Depends on / 依赖: hs.fac
-/
theorem Fork.IsLimit.lift_ι {s t : Fork f g} (hs : IsLimit s) : hs.lift t ≫ s.ι = t.ι :=
  hs.fac _ _

@[reassoc (attr := simp)]
/--
theorem `Cofork.IsColimit.π_desc` / 定理 `Cofork.IsColimit.π_desc`

English:
theorem Cofork.IsColimit.π_desc
  given: {s t : Cofork f g} (hs : IsColimit s)
  statement: s.π ≫ hs.desc t = t.π
  proof: hs.fac _ _

中文:
定理 Cofork.IsColimit.π_desc
  条件: {s t : Cofork f g} (hs : IsColimit s)
  结论: s.π ≫ hs.desc t = t.π
  证明: hs.fac _ _

Depends on / 依赖: hs.fac
-/
theorem Cofork.IsColimit.π_desc {s t : Cofork f g} (hs : IsColimit s) : s.π ≫ hs.desc t = t.π :=
  hs.fac _ _

/--
Definition of `Fork.IsLimit.lift` / `Fork.IsLimit.lift` 的定义

English:
definition Fork.IsLimit.lift
  signature: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  body: hs.lift (Fork.ofι _ h)

@[reassoc (attr := simp)]

中文:
定义 Fork.IsLimit.lift
  签名: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  定义体: hs.lift (Fork.ofι _ h)

@[reassoc (attr := simp)]

Depends on / 依赖: Fork.of, hs.lift
-/
def Fork.IsLimit.lift {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ s.pt :=
  hs.lift (Fork.ofι _ h)

@[reassoc (attr := simp)]
/--
lemma `Fork.IsLimit.lift_ι'` / 引理 `Fork.IsLimit.lift_ι'`

English:
lemma Fork.IsLimit.lift_ι'
  given: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  proof: hs.fac _ _

中文:
引理 Fork.IsLimit.lift_ι'
  条件: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  证明: hs.fac _ _

Depends on / 依赖: hs.fac
-/
lemma Fork.IsLimit.lift_ι' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    Fork.IsLimit.lift hs k h ≫ Fork.ι s = k :=
    hs.fac _ _

/--
Definition of `Fork.IsLimit.lift'` / `Fork.IsLimit.lift'` 的定义

English:
definition Fork.IsLimit.lift'
  signature: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  body: ⟨Fork.IsLimit.lift hs k h, by simp⟩

中文:
定义 Fork.IsLimit.lift'
  签名: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  定义体: ⟨Fork.IsLimit.lift hs k h, by simp⟩

Depends on / 依赖: Fork.IsLimit.lift, IsLimit
-/
def Fork.IsLimit.lift' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨Fork.IsLimit.lift hs k h, by simp⟩

/--
lemma `Fork.IsLimit.mono` / 引理 `Fork.IsLimit.mono`

English:
lemma Fork.IsLimit.mono
  given: {s : Fork f g} (hs : IsLimit s)
  statement: Mono s.ι where
  proof: hom_ext hs h

中文:
引理 Fork.IsLimit.mono
  条件: {s : Fork f g} (hs : IsLimit s)
  结论: Mono s.ι where
  证明: hom_ext hs h

Depends on / 依赖: hom_ext
-/
lemma Fork.IsLimit.mono {s : Fork f g} (hs : IsLimit s) : Mono s.ι where
  right_cancellation _ _ h := hom_ext hs h

/--
Definition of `Cofork.IsColimit.desc` / `Cofork.IsColimit.desc` 的定义

English:
definition Cofork.IsColimit.desc
  signature: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  body: hs.desc (Cofork.ofπ _ h)

@[reassoc (attr := simp)]

中文:
定义 Cofork.IsColimit.desc
  签名: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  定义体: hs.desc (Cofork.ofπ _ h)

@[reassoc (attr := simp)]

Depends on / 依赖: Cofork, Cofork.of, hs.desc
-/
def Cofork.IsColimit.desc {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : s.pt ⟶ W :=
  hs.desc (Cofork.ofπ _ h)

@[reassoc (attr := simp)]
/--
lemma `Cofork.IsColimit.π_desc'` / 引理 `Cofork.IsColimit.π_desc'`

English:
lemma Cofork.IsColimit.π_desc'
  statement: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  proof: hs.fac _ _

中文:
引理 Cofork.IsColimit.π_desc'
  结论: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  证明: hs.fac _ _

Depends on / 依赖: hs.fac
-/
lemma Cofork.IsColimit.π_desc' {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : Cofork.π s ≫ Cofork.IsColimit.desc hs k h = k :=
  hs.fac _ _

/--
Definition of `Cofork.IsColimit.desc'` / `Cofork.IsColimit.desc'` 的定义

English:
definition Cofork.IsColimit.desc'
  signature: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  body: ⟨Cofork.IsColimit.desc hs k h, by simp⟩

中文:
定义 Cofork.IsColimit.desc'
  签名: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  定义体: ⟨Cofork.IsColimit.desc hs k h, by simp⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.desc, IsColimit
-/
def Cofork.IsColimit.desc' {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨Cofork.IsColimit.desc hs k h, by simp⟩

/--
lemma `Cofork.IsColimit.epi` / 引理 `Cofork.IsColimit.epi`

English:
lemma Cofork.IsColimit.epi
  given: {s : Cofork f g} (hs : IsColimit s)
  statement: Epi s.π where
  proof: hom_ext hs h

中文:
引理 Cofork.IsColimit.epi
  条件: {s : Cofork f g} (hs : IsColimit s)
  结论: Epi s.π where
  证明: hom_ext hs h

Depends on / 依赖: hom_ext
-/
lemma Cofork.IsColimit.epi {s : Cofork f g} (hs : IsColimit s) : Epi s.π where
  left_cancellation _ _ h := hom_ext hs h

/--
theorem `Fork.IsLimit.existsUnique` / 定理 `Fork.IsLimit.existsUnique`

English:
theorem Fork.IsLimit.existsUnique
  statement: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X)
  proof: ⟨hs.lift Fork.ofι _ h, hs.fac _ _, fun _ hm =>
Fork.IsLimit.hom_ext hs hm.symm ▸ (hs.fac (Fork.ofι _ h) WalkingParallelPair.zero).symm⟩

中文:
定理 Fork.IsLimit.existsUnique
  结论: {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X)
  证明: ⟨hs.lift Fork.ofι _ h, hs.fac _ _, fun _ hm =>
Fork.IsLimit.hom_ext hs hm.symm ▸ (hs.fac (Fork.ofι _ h) WalkingParallelPair.zero).symm⟩

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.of, IsLimit, WalkingParallelPair, WalkingParallelPair.zero, hm.symm, hom_ext, hs.fac, hs.lift
-/
theorem Fork.IsLimit.existsUnique {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = k ≫ g) : exists! l : W ⟶ s.pt, l ≫ Fork.ι s = k :=
⟨hs.lift Fork.ofι _ h, hs.fac _ _, fun _ hm =>
Fork.IsLimit.hom_ext hs hm.symm ▸ (hs.fac (Fork.ofι _ h) WalkingParallelPair.zero).symm⟩

/--
theorem `Cofork.IsColimit.existsUnique` / 定理 `Cofork.IsColimit.existsUnique`

English:
theorem Cofork.IsColimit.existsUnique
  statement: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  proof: ⟨hs.desc Cofork.ofπ _ h, hs.fac _ _, fun _ hm =>
Cofork.IsColimit.hom_ext hs hm.symm ▸ (hs.fac (Cofork.ofπ _ h) WalkingParallelPair.one).symm⟩

中文:
定理 Cofork.IsColimit.existsUnique
  结论: {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  证明: ⟨hs.desc Cofork.ofπ _ h, hs.fac _ _, fun _ hm =>
Cofork.IsColimit.hom_ext hs hm.symm ▸ (hs.fac (Cofork.ofπ _ h) WalkingParallelPair.one).symm⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, Cofork.of, IsColimit, WalkingParallelPair, WalkingParallelPair.one, hm.symm, hom_ext, hs.desc, hs.fac
-/
theorem Cofork.IsColimit.existsUnique {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : exists! d : s.pt ⟶ W, Cofork.π s ≫ d = k :=
⟨hs.desc Cofork.ofπ _ h, hs.fac _ _, fun _ hm =>
Cofork.IsColimit.hom_ext hs hm.symm ▸ (hs.fac (Cofork.ofπ _ h) WalkingParallelPair.one).symm⟩

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[simps]
/--
Definition of `Fork.IsLimit.mk` / `Fork.IsLimit.mk` 的定义

English:
definition Fork.IsLimit.mk
  signature: (t : Fork f g) (lift : forall s : Fork f g, s.pt ⟶ t.pt)
  body: { lift
    fac := fun s j =>
WalkingParallelPair.casesOn j (fac s) by
        simp [← Category.assoc, fac]
    uniq := fun s m j => by aesop }

中文:
定义 Fork.IsLimit.mk
  签名: (t : Fork f g) (lift : 对任意 s : Fork f g, s.pt ⟶ t.pt)
  定义体: { lift
    fac := fun s j =>
WalkingParallelPair.casesOn j (fac s) by
        simp [← Category.assoc, fac]
    uniq := fun s m j => by aesop }

Depends on / 依赖: Category, Category.assoc, WalkingParallelPair, WalkingParallelPair.casesOn, casesOn
-/
def Fork.IsLimit.mk (t : Fork f g) (lift : forall s : Fork f g, s.pt ⟶ t.pt)
    (fac : forall s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s)
    (uniq : forall (s : Fork f g) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j =>
WalkingParallelPair.casesOn j (fac s) by
        simp [← Category.assoc, fac]
    uniq := fun s m j => by aesop }

/--
Definition of `Fork.IsLimit.mk'` / `Fork.IsLimit.mk'` 的定义

English:
definition Fork.IsLimit.mk'
  signature: {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
  body: Fork.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w => (create s).2.2 w

中文:
定义 Fork.IsLimit.mk'
  签名: {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
  定义体: Fork.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w => (create s).2.2 w

Depends on / 依赖: Fork.IsLimit.mk, IsLimit, create
-/
def Fork.IsLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : forall s : Fork f g, { l // l ≫ t.ι = s.ι ∧ forall {m}, m ≫ t.ι = s.ι -> m = l }) : IsLimit t :=
  Fork.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w => (create s).2.2 w

/--
Definition of `Cofork.IsColimit.mk` / `Cofork.IsColimit.mk` 的定义

English:
definition Cofork.IsColimit.mk
  signature: (t : Cofork f g) (desc : forall s : Cofork f g, t.pt ⟶ s.pt)
  body: { desc
    fac := fun s j =>
      WalkingParallelPair.casesOn j (by simp_all) (fac s)
    uniq := by aesop }

中文:
定义 Cofork.IsColimit.mk
  签名: (t : Cofork f g) (desc : 对任意 s : Cofork f g, t.pt ⟶ s.pt)
  定义体: { desc
    fac := fun s j =>
      WalkingParallelPair.casesOn j (by simp_all) (fac s)
    uniq := by aesop }

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.casesOn, casesOn
-/
def Cofork.IsColimit.mk (t : Cofork f g) (desc : forall s : Cofork f g, t.pt ⟶ s.pt)
    (fac : forall s : Cofork f g, Cofork.π t ≫ desc s = Cofork.π s)
    (uniq : forall (s : Cofork f g) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      WalkingParallelPair.casesOn j (by simp_all) (fac s)
    uniq := by aesop }

/--
Definition of `Cofork.IsColimit.mk'` / `Cofork.IsColimit.mk'` 的定义

English:
definition Cofork.IsColimit.mk'
  signature: {X Y : C} {f g : X ⟶ Y} (t : Cofork f g)
  body: Cofork.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 w

中文:
定义 Cofork.IsColimit.mk'
  签名: {X Y : C} {f g : X ⟶ Y} (t : Cofork f g)
  定义体: Cofork.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 w

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit, create
-/
def Cofork.IsColimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Cofork f g)
    (create : forall s : Cofork f g, { l : t.pt ⟶ s.pt // t.π ≫ l = s.π
                                    ∧ forall {m}, t.π ≫ m = s.π -> m = l }) : IsColimit t :=
  Cofork.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 w

/--
Definition of `Fork.IsLimit.ofExistsUnique` / `Fork.IsLimit.ofExistsUnique` 的定义

English:
definition Fork.IsLimit.ofExistsUnique
  signature: {t : Fork f g}
  body: by
  choose d hd hd' using hs
  exact Fork.IsLimit.mk _ d hd fun s m hm => hd' _ _ hm

中文:
定义 Fork.IsLimit.ofExistsUnique
  签名: {t : Fork f g}
  定义体: by
  choose d hd hd' using hs
  exact Fork.IsLimit.mk _ d hd fun s m hm => hd' _ _ hm

Depends on / 依赖: Fork.IsLimit.mk, IsLimit
-/
noncomputable def Fork.IsLimit.ofExistsUnique {t : Fork f g}
    (hs : forall s : Fork f g, exists! l : s.pt ⟶ t.pt, l ≫ Fork.ι t = Fork.ι s) : IsLimit t := by
  choose d hd hd' using hs
  exact Fork.IsLimit.mk _ d hd fun s m hm => hd' _ _ hm

/--
Definition of `Cofork.IsColimit.ofExistsUnique` / `Cofork.IsColimit.ofExistsUnique` 的定义

English:
definition Cofork.IsColimit.ofExistsUnique
  signature: {t : Cofork f g}
  body: by
  choose d hd hd' using hs
  exact Cofork.IsColimit.mk _ d hd fun s m hm => hd' _ _ hm

中文:
定义 Cofork.IsColimit.ofExistsUnique
  签名: {t : Cofork f g}
  定义体: by
  choose d hd hd' using hs
  exact Cofork.IsColimit.mk _ d hd fun s m hm => hd' _ _ hm

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit
-/
noncomputable def Cofork.IsColimit.ofExistsUnique {t : Cofork f g}
    (hs : forall s : Cofork f g, exists! d : t.pt ⟶ s.pt, Cofork.π t ≫ d = Cofork.π s) : IsColimit t := by
  choose d hd hd' using hs
  exact Cofork.IsColimit.mk _ d hd fun s m hm => hd' _ _ hm

/--
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `Fork.IsLimit.homIso_natural`.
This is a special case of `IsLimit.homIso'`, often useful to construct adjunctions.
-/
@[simps]
/--
Definition of `Fork.IsLimit.homIso` / `Fork.IsLimit.homIso` 的定义

English:
definition Fork.IsLimit.homIso
  signature: {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) (Z : C)
  body: ⟨k ≫ t.ι, by simp only [Category.assoc, t.condition]⟩
  invFun h := (Fork.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Fork.IsLimit.hom_ext ht (Fork.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Fork.IsLimit.lift' ht _ _).prop

中文:
定义 Fork.IsLimit.homIso
  签名: {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) (Z : C)
  定义体: ⟨k ≫ t.ι, by simp only [Category.assoc, t.condition]⟩
  invFun h := (Fork.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Fork.IsLimit.hom_ext ht (Fork.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Fork.IsLimit.lift' ht _ _).prop

Depends on / 依赖: Category, Category.assoc, condition, t.condition
-/
def Fork.IsLimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // h ≫ f = h ≫ g } where
  toFun k := ⟨k ≫ t.ι, by simp only [Category.assoc, t.condition]⟩
  invFun h := (Fork.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Fork.IsLimit.hom_ext ht (Fork.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Fork.IsLimit.lift' ht _ _).prop

/--
theorem `Fork.IsLimit.homIso_natural` / 定理 `Fork.IsLimit.homIso_natural`

English:
theorem Fork.IsLimit.homIso_natural
  statement: {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t)
  proof: Category.assoc _ _ _

中文:
定理 Fork.IsLimit.homIso_natural
  结论: {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t)
  证明: Category.assoc _ _ _

Depends on / 依赖: Category, Category.assoc
-/
theorem Fork.IsLimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t)
    {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Fork.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (Fork.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _

/-- Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `Cofork.IsColimit.homIso_natural`.
This is a special case of `IsColimit.homIso'`, often useful to construct adjunctions.
-/
@[simps]
/--
Definition of `Cofork.IsColimit.homIso` / `Cofork.IsColimit.homIso` 的定义

English:
definition Cofork.IsColimit.homIso
  signature: {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} (ht : IsColimit t) (Z : C)
  body: ⟨t.π ≫ k, by simp only [← Category.assoc, t.condition]⟩
  invFun h := (Cofork.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cofork.IsColimit.hom_ext ht (Cofork.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cofork.IsColimit.desc' ht _ _).prop

中文:
定义 Cofork.IsColimit.homIso
  签名: {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} (ht : IsColimit t) (Z : C)
  定义体: ⟨t.π ≫ k, by simp only [← Category.assoc, t.condition]⟩
  invFun h := (Cofork.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cofork.IsColimit.hom_ext ht (Cofork.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cofork.IsColimit.desc' ht _ _).prop

Depends on / 依赖: Category, Category.assoc, condition, t.condition
-/
def Cofork.IsColimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} (ht : IsColimit t) (Z : C) :
    (t.pt ⟶ Z) ≃ { h : Y ⟶ Z // f ≫ h = g ≫ h } where
  toFun k := ⟨t.π ≫ k, by simp only [← Category.assoc, t.condition]⟩
  invFun h := (Cofork.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cofork.IsColimit.hom_ext ht (Cofork.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cofork.IsColimit.desc' ht _ _).prop

/--
theorem `Cofork.IsColimit.homIso_natural` / 定理 `Cofork.IsColimit.homIso_natural`

English:
theorem Cofork.IsColimit.homIso_natural
  statement: {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} {Z Z' : C}
  proof: (Category.assoc _ _ _).symm

中文:
定理 Cofork.IsColimit.homIso_natural
  结论: {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} {Z Z' : C}
  证明: (Category.assoc _ _ _).symm

Depends on / 依赖: Category, Category.assoc
-/
theorem Cofork.IsColimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} {Z Z' : C}
    (q : Z ⟶ Z') (ht : IsColimit t) (k : t.pt ⟶ Z) :
    (Cofork.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') =
      (Cofork.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm

/--
Definition of `Cone.ofFork` / `Cone.ofFork` 的定义

English:
definition Cone.ofFork
  signature: {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right))
  body: t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by simp)
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

中文:
定义 Cone.ofFork
  签名: {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right))
  定义体: t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by simp)
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

Depends on / 依赖: t.pt
-/
def Cone.ofFork {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) : Cone F where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by simp)
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

/--
Definition of `Cocone.ofCofork` / `Cocone.ofCofork` 的定义

English:
definition Cocone.ofCofork
  signature: {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
  body: t.pt
  ι :=
    { app := fun X => eqToHom (by simp) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

@[simp]

中文:
定义 Cocone.ofCofork
  签名: {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
  定义体: t.pt
  ι :=
    { app := fun X => eqToHom (by simp) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

@[simp]

Depends on / 依赖: t.pt
-/
def Cocone.ofCofork {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right)) :
    Cocone F where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by simp) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

@[simp]
/--
theorem `Cone.ofFork_π` / 定理 `Cone.ofFork_π`

English:
theorem Cone.ofFork_π
  given: {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) (j)
  proof: rfl

@[simp]

中文:
定理 Cone.ofFork_π
  条件: {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) (j)
  证明: rfl

@[simp]
-/
theorem Cone.ofFork_π {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) (j) :
    (Cone.ofFork t).π.app j = t.π.app j ≫ eqToHom (by simp) := rfl

@[simp]
/--
theorem `Cocone.ofCofork_ι` / 定理 `Cocone.ofCofork_ι`

English:
theorem Cocone.ofCofork_ι
  statement: {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
  proof: rfl

中文:
定理 Cocone.ofCofork_ι
  结论: {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
  证明: rfl
-/
theorem Cocone.ofCofork_ι {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
    (j) : (Cocone.ofCofork t).ι.app j = eqToHom (by simp) ≫ t.ι.app j := rfl

/--
Definition of `Fork.ofCone` / `Fork.ofCone` 的定义

English:
definition Fork.ofCone
  signature: {F : WalkingParallelPair ⥤ C} (t : Cone F)
  body: t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by simp)
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

中文:
定义 Fork.ofCone
  签名: {F : WalkingParallelPair ⥤ C} (t : Cone F)
  定义体: t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by simp)
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

Depends on / 依赖: t.pt
-/
def Fork.ofCone {F : WalkingParallelPair ⥤ C} (t : Cone F) : Fork (F.map left) (F.map right) where
  pt := t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by simp)
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

/--
Definition of `Cofork.ofCocone` / `Cofork.ofCocone` 的定义

English:
definition Cofork.ofCocone
  signature: {F : WalkingParallelPair ⥤ C} (t : Cocone F)
  body: t.pt
  ι := { app := fun X => eqToHom (by simp) ≫ t.ι.app X
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

@[simp]

中文:
定义 Cofork.ofCocone
  签名: {F : WalkingParallelPair ⥤ C} (t : Cocone F)
  定义体: t.pt
  ι := { app := fun X => eqToHom (by simp) ≫ t.ι.app X
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

@[simp]

Depends on / 依赖: t.pt
-/
def Cofork.ofCocone {F : WalkingParallelPair ⥤ C} (t : Cocone F) :
    Cofork (F.map left) (F.map right) where
  pt := t.pt
  ι := { app := fun X => eqToHom (by simp) ≫ t.ι.app X
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

@[simp]
/--
theorem `Fork.ofCone_π` / 定理 `Fork.ofCone_π`

English:
theorem Fork.ofCone_π
  given: {F : WalkingParallelPair ⥤ C} (t : Cone F) (j)
  proof: rfl

@[simp]

中文:
定理 Fork.ofCone_π
  条件: {F : WalkingParallelPair ⥤ C} (t : Cone F) (j)
  证明: rfl

@[simp]
-/
theorem Fork.ofCone_π {F : WalkingParallelPair ⥤ C} (t : Cone F) (j) :
    (Fork.ofCone t).π.app j = t.π.app j ≫ eqToHom (by simp) := rfl

@[simp]
/--
theorem `Cofork.ofCocone_ι` / 定理 `Cofork.ofCocone_ι`

English:
theorem Cofork.ofCocone_ι
  given: {F : WalkingParallelPair ⥤ C} (t : Cocone F) (j)
  proof: rfl

@[simp]

中文:
定理 Cofork.ofCocone_ι
  条件: {F : WalkingParallelPair ⥤ C} (t : Cocone F) (j)
  证明: rfl

@[simp]
-/
theorem Cofork.ofCocone_ι {F : WalkingParallelPair ⥤ C} (t : Cocone F) (j) :
    (Cofork.ofCocone t).ι.app j = eqToHom (by simp) ≫ t.ι.app j := rfl

@[simp]
/--
theorem `Fork.ι_postcompose` / 定理 `Fork.ι_postcompose`

English:
theorem Fork.ι_postcompose
  statement: {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
  proof: rfl

@[simp]

中文:
定理 Fork.ι_postcompose
  结论: {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
  证明: rfl

@[simp]
-/
theorem Fork.ι_postcompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Fork f g} : Fork.ι ((Cone.postcompose α).obj c) = c.ι ≫ α.app .zero :=
  rfl

@[simp]
/--
theorem `Cofork.π_precompose` / 定理 `Cofork.π_precompose`

English:
theorem Cofork.π_precompose
  statement: {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
  proof: rfl

中文:
定理 Cofork.π_precompose
  结论: {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
  证明: rfl
-/
theorem Cofork.π_precompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Cofork f' g'} :
    Cofork.π ((Cocone.precompose α).obj c) = α.app .one ≫ c.π := rfl

/-- Helper function for constructing morphisms between equalizer forks.
-/
@[simps]
/--
Definition of `Fork.mkHom` / `Fork.mkHom` 的定义

English:
definition Fork.mkHom
  signature: {s t : Fork f g} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι)
  body: k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simp only [Fork.app_one_eq_ι_comp_left, ← Category.assoc]
      congr

中文:
定义 Fork.mkHom
  签名: {s t : Fork f g} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι)
  定义体: k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simp only [Fork.app_one_eq_ι_comp_left, ← Category.assoc]
      congr
-/
def Fork.mkHom {s t : Fork f g} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simp only [Fork.app_one_eq_ι_comp_left, ← Category.assoc]
      congr

/-- To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
/--
Definition of `Fork.ext` / `Fork.ext` 的定义

English:
definition Fork.ext
  signature: {s t : Fork f g} (i : s.pt ≅ t.pt) (w : i.hom ≫ t.ι = s.ι := by cat_disch)
  body: Fork.mkHom i.hom w
  inv := Fork.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

中文:
定义 Fork.ext
  签名: {s t : Fork f g} (i : s.pt ≅ t.pt) (w : i.hom ≫ t.ι = s.ι := by cat_disch)
  定义体: Fork.mkHom i.hom w
  inv := Fork.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

Depends on / 依赖: Fork.mkHom, Iso.inv_hom_id_assoc, cat_disch, i.hom, i.inv, inv_hom_id_assoc
-/
def Fork.ext {s t : Fork f g} (i : s.pt ≅ t.pt) (w : i.hom ≫ t.ι = s.ι := by cat_disch) :
    s ≅ t where
  hom := Fork.mkHom i.hom w
  inv := Fork.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

/--
Definition of `ForkOfι.ext` / `ForkOfι.ext` 的定义

English:
definition ForkOfι.ext
  signature: {P : C} {ι ι' : P ⟶ X} (w : ι ≫ f = ι ≫ g) (w' : ι' ≫ f = ι' ≫ g) (h : ι = ι')
  body: Fork.ext (Iso.refl _) (by simp [h])

中文:
定义 ForkOfι.ext
  签名: {P : C} {ι ι' : P ⟶ X} (w : ι ≫ f = ι ≫ g) (w' : ι' ≫ f = ι' ≫ g) (h : ι = ι')
  定义体: Fork.ext (Iso.refl _) (by simp [h])

Depends on / 依赖: Fork.ext, Iso.refl
-/
def ForkOfι.ext {P : C} {ι ι' : P ⟶ X} (w : ι ≫ f = ι ≫ g) (w' : ι' ≫ f = ι' ≫ g) (h : ι = ι') :
    Fork.ofι ι w ≅ Fork.ofι ι' w' :=
  Fork.ext (Iso.refl _) (by simp [h])

/-- Every fork is isomorphic to one of the form `Fork.of_ι _ _`. -/
@[simps!]
/--
Definition of `Fork.isoForkOfι` / `Fork.isoForkOfι` 的定义

English:
definition Fork.isoForkOfι
  signature: (c : Fork f g)
  body: Fork.ext (Iso.refl _)

中文:
定义 Fork.isoForkOfι
  签名: (c : Fork f g)
  定义体: Fork.ext (Iso.refl _)

Depends on / 依赖: Fork.ext, Iso.refl
-/
def Fork.isoForkOfι (c : Fork f g) : c ≅ Fork.ofι c.ι c.condition :=
  Fork.ext (Iso.refl _)

/--
Definition of `Fork.equivOfIsos` / `Fork.equivOfIsos` 的定义

English:
definition Fork.equivOfIsos
  signature: {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
  body: Cone.postcomposeEquivalence
    parallelPair.ext e₀ e₁ (by simp [comm₁]) (by simp [comm₂])

@[simp]

中文:
定义 Fork.equivOfIsos
  签名: {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
  定义体: Cone.postcomposeEquivalence
    parallelPair.ext e₀ e₁ (by simp [comm₁]) (by simp [comm₂])

@[simp]

Depends on / 依赖: Cone.postcomposeEquivalence, cat_disch, parallelPair, parallelPair.ext, postcomposeEquivalence
-/
def Fork.equivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) :
    Fork f g ≌ Fork f' g' :=
Cone.postcomposeEquivalence
    parallelPair.ext e₀ e₁ (by simp [comm₁]) (by simp [comm₂])

@[simp]
/--
lemma `Fork.equivOfIsos_functor_obj_ι` / 引理 `Fork.equivOfIsos_functor_obj_ι`

English:
lemma Fork.equivOfIsos_functor_obj_ι
  statement: {X Y : C} {f g : X ⟶ Y}
  proof: rfl

@[simp]

中文:
引理 Fork.equivOfIsos_functor_obj_ι
  结论: {X Y : C} {f g : X ⟶ Y}
  证明: rfl

@[simp]

Depends on / 依赖: Fork.equivOfIsos, cat_disch, equivOfIsos, functor, functor.obj
-/
lemma Fork.equivOfIsos_functor_obj_ι {X Y : C} {f g : X ⟶ Y}
    {X' Y' : C} {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) (c : Fork f g) :
    ((Fork.equivOfIsos e₀ e₁ comm₁ comm₂).functor.obj c).ι = c.ι ≫ e₀.hom :=
  rfl

@[simp]
/--
lemma `Fork.equivOfIsos_inverse_obj_ι` / 引理 `Fork.equivOfIsos_inverse_obj_ι`

English:
lemma Fork.equivOfIsos_inverse_obj_ι
  statement: {X Y : C} {f g : X ⟶ Y}
  proof: rfl

中文:
引理 Fork.equivOfIsos_inverse_obj_ι
  结论: {X Y : C} {f g : X ⟶ Y}
  证明: rfl

Depends on / 依赖: Fork.equivOfIsos, cat_disch, equivOfIsos, inverse, inverse.obj
-/
lemma Fork.equivOfIsos_inverse_obj_ι {X Y : C} {f g : X ⟶ Y}
    {X' Y' : C} {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) (c : Fork f' g') :
    ((Fork.equivOfIsos e₀ e₁ comm₁ comm₂).inverse.obj c).ι = c.ι ≫ e₀.inv :=
  rfl

/--
Definition of `Fork.isLimitEquivOfIsos` / `Fork.isLimitEquivOfIsos` 的定义

English:
definition Fork.isLimitEquivOfIsos
  signature: {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
  body: let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsLimit.equivOfNatIsoOfIso i c c' (Fork.ext e comm₃)

中文:
定义 Fork.isLimitEquivOfIsos
  签名: {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
  定义体: let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsLimit.equivOfNatIsoOfIso i c c' (Fork.ext e comm₃)

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.equivOfNatIsoOfIso, cat_disch, e.hom, equivOfNatIsoOfIso, parallelPair, parallelPair.ext
-/
def Fork.isLimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Fork f g)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by cat_disch) :
    IsLimit c ≃ IsLimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsLimit.equivOfNatIsoOfIso i c c' (Fork.ext e comm₃)

/--
Definition of `Fork.isLimitOfIsos` / `Fork.isLimitOfIsos` 的定义

English:
definition Fork.isLimitOfIsos
  signature: {X' Y' : C} (c : Fork f g) (hc : IsLimit c)
  body: (Fork.isLimitEquivOfIsos c c' e₀ e₁ e) hc

中文:
定义 Fork.isLimitOfIsos
  签名: {X' Y' : C} (c : Fork f g) (hc : IsLimit c)
  定义体: (Fork.isLimitEquivOfIsos c c' e₀ e₁ e) hc

Depends on / 依赖: Fork.isLimitEquivOfIsos, IsLimit, cat_disch, e.hom, isLimitEquivOfIsos
-/
def Fork.isLimitOfIsos {X' Y' : C} (c : Fork f g) (hc : IsLimit c)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by cat_disch) : IsLimit c' :=
  (Fork.isLimitEquivOfIsos c c' e₀ e₁ e) hc

/-- Helper function for constructing morphisms between coequalizer coforks.
-/
@[simps]
/--
Definition of `Cofork.mkHom` / `Cofork.mkHom` 的定义

English:
definition Cofork.mkHom
  signature: {s t : Cofork f g} (k : s.pt ⟶ t.pt) (w : s.π ≫ k = t.π)
  body: k
  w := by
    rintro ⟨_ | _⟩
    · simp [Cofork.app_zero_eq_comp_π_left, w]
    · exact w

@[reassoc (attr := simp)]

中文:
定义 Cofork.mkHom
  签名: {s t : Cofork f g} (k : s.pt ⟶ t.pt) (w : s.π ≫ k = t.π)
  定义体: k
  w := by
    rintro ⟨_ | _⟩
    · simp [Cofork.app_zero_eq_comp_π_left, w]
    · exact w

@[reassoc (attr := simp)]
-/
def Cofork.mkHom {s t : Cofork f g} (k : s.pt ⟶ t.pt) (w : s.π ≫ k = t.π) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · simp [Cofork.app_zero_eq_comp_π_left, w]
    · exact w

@[reassoc (attr := simp)]
/--
theorem `Fork.hom_comp_ι` / 定理 `Fork.hom_comp_ι`

English:
theorem Fork.hom_comp_ι
  given: {s t : Fork f g} (f : s ⟶ t)
  statement: f.hom ≫ t.ι = s.ι
  proof: by
  cases s; cases t; cases f; aesop

@[reassoc (attr := simp)]

中文:
定理 Fork.hom_comp_ι
  条件: {s t : Fork f g} (f : s ⟶ t)
  结论: f.hom ≫ t.ι = s.ι
  证明: by
  cases s; cases t; cases f; aesop

@[reassoc (attr := simp)]
-/
theorem Fork.hom_comp_ι {s t : Fork f g} (f : s ⟶ t) : f.hom ≫ t.ι = s.ι := by
  cases s; cases t; cases f; aesop

@[reassoc (attr := simp)]
/--
theorem `Fork.π_comp_hom` / 定理 `Fork.π_comp_hom`

English:
theorem Fork.π_comp_hom
  given: {s t : Cofork f g} (f : s ⟶ t)
  statement: s.π ≫ f.hom = t.π
  proof: by
  cases s; cases t; cases f; aesop

中文:
定理 Fork.π_comp_hom
  条件: {s t : Cofork f g} (f : s ⟶ t)
  结论: s.π ≫ f.hom = t.π
  证明: by
  cases s; cases t; cases f; aesop
-/
theorem Fork.π_comp_hom {s t : Cofork f g} (f : s ⟶ t) : s.π ≫ f.hom = t.π := by
  cases s; cases t; cases f; aesop

/-- To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
@[simps]
/--
Definition of `Cofork.ext` / `Cofork.ext` 的定义

English:
definition Cofork.ext
  signature: {s t : Cofork f g} (i : s.pt ≅ t.pt) (w : s.π ≫ i.hom = t.π := by cat_disch)
  body: Cofork.mkHom i.hom w
  inv := Cofork.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

中文:
定义 Cofork.ext
  签名: {s t : Cofork f g} (i : s.pt ≅ t.pt) (w : s.π ≫ i.hom = t.π := by cat_disch)
  定义体: Cofork.mkHom i.hom w
  inv := Cofork.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

Depends on / 依赖: Cofork, Cofork.mkHom, Iso.comp_inv_eq, cat_disch, comp_inv_eq, i.hom, i.inv
-/
def Cofork.ext {s t : Cofork f g} (i : s.pt ≅ t.pt) (w : s.π ≫ i.hom = t.π := by cat_disch) :
    s ≅ t where
  hom := Cofork.mkHom i.hom w
  inv := Cofork.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

/--
Definition of `CoforkOfπ.ext` / `CoforkOfπ.ext` 的定义

English:
definition CoforkOfπ.ext
  signature: {P : C} {π π' : Y ⟶ P} (w : f ≫ π = g ≫ π) (w' : f ≫ π' = g ≫ π') (h : π = π')
  body: Cofork.ext (Iso.refl _) (by simp [h])

中文:
定义 CoforkOfπ.ext
  签名: {P : C} {π π' : Y ⟶ P} (w : f ≫ π = g ≫ π) (w' : f ≫ π' = g ≫ π') (h : π = π')
  定义体: Cofork.ext (Iso.refl _) (by simp [h])

Depends on / 依赖: Cofork, Cofork.ext, Iso.refl
-/
def CoforkOfπ.ext {P : C} {π π' : Y ⟶ P} (w : f ≫ π = g ≫ π) (w' : f ≫ π' = g ≫ π') (h : π = π') :
    Cofork.ofπ π w ≅ Cofork.ofπ π' w' :=
  Cofork.ext (Iso.refl _) (by simp [h])

/--
Definition of `Cofork.isoCoforkOfπ` / `Cofork.isoCoforkOfπ` 的定义

English:
definition Cofork.isoCoforkOfπ
  signature: (c : Cofork f g)
  body: Cofork.ext (Iso.refl _)

中文:
定义 Cofork.isoCoforkOfπ
  签名: (c : Cofork f g)
  定义体: Cofork.ext (Iso.refl _)

Depends on / 依赖: Cofork, Cofork.ext, Iso.refl
-/
def Cofork.isoCoforkOfπ (c : Cofork f g) : c ≅ Cofork.ofπ c.π c.condition :=
  Cofork.ext (Iso.refl _)

/--
Definition of `Cofork.isColimitEquivOfIsos` / `Cofork.isColimitEquivOfIsos` 的定义

English:
definition Cofork.isColimitEquivOfIsos
  signature: {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
  body: let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsColimit.equivOfNatIsoOfIso i c c' (Cofork.ext e (by rw [← comm₃, ← Category.assoc]; rfl))

中文:
定义 Cofork.isColimitEquivOfIsos
  签名: {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
  定义体: let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsColimit.equivOfNatIsoOfIso i c c' (Cofork.ext e (by rw [← comm₃, ← Category.assoc]; rfl))

Depends on / 依赖: Category, Category.assoc, Cofork, Cofork.ext, IsColimit, IsColimit.equivOfNatIsoOfIso, cat_disch, e.hom, equivOfNatIsoOfIso, parallelPair, parallelPair.ext
-/
def Cofork.isColimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Cofork f g)
    {f' g' : X' ⟶ Y'} (c' : Cofork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e₁.inv ≫ c.π ≫ e.hom = c'.π := by cat_disch) :
    IsColimit c ≃ IsColimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsColimit.equivOfNatIsoOfIso i c c' (Cofork.ext e (by rw [← comm₃, ← Category.assoc]; rfl))

/--
Definition of `Cofork.isColimitOfIsos` / `Cofork.isColimitOfIsos` 的定义

English:
definition Cofork.isColimitOfIsos
  signature: {X' Y' : C} (c : Cofork f g) (hc : IsColimit c)
  body: (Cofork.isColimitEquivOfIsos c c' e₀ e₁ e) hc

中文:
定义 Cofork.isColimitOfIsos
  签名: {X' Y' : C} (c : Cofork f g) (hc : IsColimit c)
  定义体: (Cofork.isColimitEquivOfIsos c c' e₀ e₁ e) hc

Depends on / 依赖: Cofork, Cofork.isColimitEquivOfIsos, IsColimit, cat_disch, e.hom, isColimitEquivOfIsos
-/
def Cofork.isColimitOfIsos {X' Y' : C} (c : Cofork f g) (hc : IsColimit c)
    {f' g' : X' ⟶ Y'} (c' : Cofork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e₁.inv ≫ c.π ≫ e.hom = c'.π := by cat_disch) : IsColimit c' :=
  (Cofork.isColimitEquivOfIsos c c' e₀ e₁ e) hc

variable (f g)

section

/--
Definition of `HasEqualizer` / `HasEqualizer` 的定义

English:
abbreviation HasEqualizer
  body: HasLimit (parallelPair f g)

中文:
缩写 HasEqualizer
  定义体: HasLimit (parallelPair f g)

Depends on / 依赖: HasLimit, parallelPair
-/
abbrev HasEqualizer :=
  HasLimit (parallelPair f g)

variable [HasEqualizer f g]

/--
Definition of `equalizer` / `equalizer` 的定义

English:
abbreviation equalizer
  signature: : C
  body: limit (parallelPair f g)

中文:
缩写 equalizer
  签名: : C
  定义体: limit (parallelPair f g)

Depends on / 依赖: parallelPair
-/
noncomputable abbrev equalizer : C :=
  limit (parallelPair f g)

/--
Definition of `equalizer.ι` / `equalizer.ι` 的定义

English:
abbreviation equalizer.ι
  signature: : equalizer f g ⟶ X
  body: limit.π (parallelPair f g) zero

中文:
缩写 equalizer.ι
  签名: : equalizer f g ⟶ X
  定义体: limit.π (parallelPair f g) zero

Depends on / 依赖: parallelPair
-/
noncomputable abbrev equalizer.ι : equalizer f g ⟶ X :=
  limit.π (parallelPair f g) zero

/--
Definition of `equalizer.fork` / `equalizer.fork` 的定义

English:
abbreviation equalizer.fork
  signature: : Fork f g
  body: limit.cone (parallelPair f g)

@[simp]

中文:
缩写 equalizer.fork
  签名: : Fork f g
  定义体: limit.cone (parallelPair f g)

@[simp]

Depends on / 依赖: Category, Category.assoc, CategoryTheory, CategoryTheory.Functor.map_comp, Functor, braided, limit.cone, map_comp, parallelPair, slice_lhs
-/
noncomputable abbrev equalizer.fork : Fork f g :=
  limit.cone (parallelPair f g)

@[simp]
/--
theorem `equalizer.fork_ι` / 定理 `equalizer.fork_ι`

English:
theorem equalizer.fork_ι
  statement: (equalizer.fork f g).ι = equalizer.ι f g
  proof: rfl

@[simp]

中文:
定理 equalizer.fork_ι
  结论: (equalizer.fork f g).ι = equalizer.ι f g
  证明: rfl

@[simp]
-/
theorem equalizer.fork_ι : (equalizer.fork f g).ι = equalizer.ι f g :=
  rfl

@[simp]
/--
theorem `equalizer.fork_π_app_zero` / 定理 `equalizer.fork_π_app_zero`

English:
theorem equalizer.fork_π_app_zero
  statement: (equalizer.fork f g).π.app zero = equalizer.ι f g
  proof: rfl

@[reassoc]

中文:
定理 equalizer.fork_π_app_zero
  结论: (equalizer.fork f g).π.app zero = equalizer.ι f g
  证明: rfl

@[reassoc]
-/
theorem equalizer.fork_π_app_zero : (equalizer.fork f g).π.app zero = equalizer.ι f g :=
  rfl

@[reassoc]
/--
theorem `equalizer.condition` / 定理 `equalizer.condition`

English:
theorem equalizer.condition
  statement: equalizer.ι f g ≫ f = equalizer.ι f g ≫ g
  proof: Fork.condition limit.cone parallelPair f g

中文:
定理 equalizer.condition
  结论: equalizer.ι f g ≫ f = equalizer.ι f g ≫ g
  证明: Fork.condition limit.cone parallelPair f g

Depends on / 依赖: Fork.condition, condition, limit.cone, parallelPair
-/
theorem equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
Fork.condition limit.cone parallelPair f g

/--
Definition of `equalizerIsEqualizer` / `equalizerIsEqualizer` 的定义

English:
definition equalizerIsEqualizer
  signature: : IsLimit (Fork.ofι (equalizer.ι f g)
  body: IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

中文:
定义 equalizerIsEqualizer
  签名: : IsLimit (Fork.ofι (equalizer.ι f g)
  定义体: IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, isLimit, limit.isLimit, ofIsoLimit
-/
noncomputable def equalizerIsEqualizer : IsLimit (Fork.ofι (equalizer.ι f g)
    (equalizer.condition f g)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/--
Definition of `equalizer.lift` / `equalizer.lift` 的定义

English:
abbreviation equalizer.lift
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  body: limit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]

中文:
缩写 equalizer.lift
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  定义体: limit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]

Depends on / 依赖: Fork.of, limit.lift, parallelPair
-/
noncomputable abbrev equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
  limit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]
/--
theorem `equalizer.lift_ι` / 定理 `equalizer.lift_ι`

English:
theorem equalizer.lift_ι
  given: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  proof: limit.lift_π _ _

中文:
定理 equalizer.lift_ι
  条件: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  证明: limit.lift_π _ _

Depends on / 依赖: limit.lift_
-/
theorem equalizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    equalizer.lift k h ≫ equalizer.ι f g = k :=
  limit.lift_π _ _

/--
Definition of `equalizer.lift'` / `equalizer.lift'` 的定义

English:
definition equalizer.lift'
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  body: ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

中文:
定义 equalizer.lift'
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  定义体: ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

Depends on / 依赖: equalizer, equalizer.lift, equalizer.lift_
-/
noncomputable def equalizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ equalizer f g // l ≫ equalizer.ι f g = k } :=
  ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

/-- Two maps into an equalizer are equal if they are equal when composed with the equalizer map. -/
@[ext]
/--
theorem `equalizer.hom_ext` / 定理 `equalizer.hom_ext`

English:
theorem equalizer.hom_ext
  statement: {W : C} {k l : W ⟶ equalizer f g}
  proof: Fork.IsLimit.hom_ext (limit.isLimit _) h

中文:
定理 equalizer.hom_ext
  结论: {W : C} {k l : W ⟶ equalizer f g}
  证明: Fork.IsLimit.hom_ext (limit.isLimit _) h

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, hom_ext, isLimit, limit.isLimit
-/
theorem equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g}
    (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
  Fork.IsLimit.hom_ext (limit.isLimit _) h

/--
theorem `equalizer.existsUnique` / 定理 `equalizer.existsUnique`

English:
theorem equalizer.existsUnique
  given: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  proof: Fork.IsLimit.existsUnique (limit.isLimit _) _ h

中文:
定理 equalizer.existsUnique
  条件: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  证明: Fork.IsLimit.existsUnique (limit.isLimit _) _ h

Depends on / 依赖: Fork.IsLimit.existsUnique, IsLimit, existsUnique, isLimit, limit.isLimit
-/
theorem equalizer.existsUnique {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    exists! l : W ⟶ equalizer f g, l ≫ equalizer.ι f g = k :=
  Fork.IsLimit.existsUnique (limit.isLimit _) _ h

/--
Instance `equalizer.ι_mono` / 实例 `equalizer.ι_mono`

English:
instance equalizer.ι_mono
  signature: : Mono (equalizer.ι f g) where
  body: equalizer.hom_ext w

中文:
实例 equalizer.ι_mono
  签名: : Mono (equalizer.ι f g) where
  定义体: equalizer.hom_ext w

Depends on / 依赖: equalizer, equalizer.hom_ext, hom_ext
-/
instance equalizer.ι_mono : Mono (equalizer.ι f g) where
  right_cancellation _ _ w := equalizer.hom_ext w

end

section

variable {f g}

/--
theorem `mono_of_isLimit_fork` / 定理 `mono_of_isLimit_fork`

English:
theorem mono_of_isLimit_fork
  given: {c : Fork f g} (i : IsLimit c)
  statement: Mono (Fork.ι c)
  proof: { right_cancellation := fun _ _ w => Fork.IsLimit.hom_ext i w }

中文:
定理 mono_of_isLimit_fork
  条件: {c : Fork f g} (i : IsLimit c)
  结论: Mono (Fork.ι c)
  证明: { right_cancellation := fun _ _ w => Fork.IsLimit.hom_ext i w }

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, hom_ext, right_cancellation
-/
theorem mono_of_isLimit_fork {c : Fork f g} (i : IsLimit c) : Mono (Fork.ι c) :=
  { right_cancellation := fun _ _ w => Fork.IsLimit.hom_ext i w }

end

section

variable {f g}

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
@[implicit_reducible]
/--
Definition of `idFork` / `idFork` 的定义

English:
definition idFork
  signature: (h : f = g)
  body: Fork.ofι (𝟙 X) h ▸ rfl

中文:
定义 idFork
  签名: (h : f = g)
  定义体: Fork.ofι (𝟙 X) h ▸ rfl

Depends on / 依赖: Fork.of
-/
def idFork (h : f = g) : Fork f g :=
Fork.ofι (𝟙 X) h ▸ rfl

/--
Definition of `isLimitIdFork` / `isLimitIdFork` 的定义

English:
definition isLimitIdFork
  signature: (h : f = g)
  body: Fork.IsLimit.mk _ (fun s => Fork.ι s) (fun _ => Category.comp_id _) fun s m h => by
    convert! h
    exact (Category.comp_id _).symm

中文:
定义 isLimitIdFork
  签名: (h : f = g)
  定义体: Fork.IsLimit.mk _ (fun s => Fork.ι s) (fun _ => Category.comp_id _) fun s m h => by
    convert! h
    exact (Category.comp_id _).symm

Depends on / 依赖: Category, Category.comp_id, Fork.IsLimit.mk, IsLimit, comp_id, convert
-/
def isLimitIdFork (h : f = g) : IsLimit (idFork h) :=
  Fork.IsLimit.mk _ (fun s => Fork.ι s) (fun _ => Category.comp_id _) fun s m h => by
    convert! h
    exact (Category.comp_id _).symm

/--
theorem `isIso_limit_cone_parallelPair_of_eq` / 定理 `isIso_limit_cone_parallelPair_of_eq`

English:
theorem isIso_limit_cone_parallelPair_of_eq
  given: (h₀ : f = g) {c : Fork f g} (h : IsLimit c)
  proof: Iso.isIso_hom IsLimit.conePointUniqueUpToIso h isLimitIdFork h₀

中文:
定理 isIso_limit_cone_parallelPair_of_eq
  条件: (h₀ : f = g) {c : Fork f g} (h : IsLimit c)
  证明: Iso.isIso_hom IsLimit.conePointUniqueUpToIso h isLimitIdFork h₀

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, Iso.isIso_hom, conePointUniqueUpToIso, isIso_hom, isLimitIdFork
-/
theorem isIso_limit_cone_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) :
    IsIso c.ι :=
Iso.isIso_hom IsLimit.conePointUniqueUpToIso h isLimitIdFork h₀

/--
theorem `equalizer.ι_of_eq` / 定理 `equalizer.ι_of_eq`

English:
theorem equalizer.ι_of_eq
  given: [HasEqualizer f g] (h : f = g)
  statement: IsIso (equalizer.ι f g)
  proof: isIso_limit_cone_parallelPair_of_eq h limit.isLimit _

中文:
定理 equalizer.ι_of_eq
  条件: [HasEqualizer f g] (h : f = g)
  结论: IsIso (equalizer.ι f g)
  证明: isIso_limit_cone_parallelPair_of_eq h limit.isLimit _

Depends on / 依赖: isIso_limit_cone_parallelPair_of_eq, isLimit, limit.isLimit
-/
theorem equalizer.ι_of_eq [HasEqualizer f g] (h : f = g) : IsIso (equalizer.ι f g) :=
isIso_limit_cone_parallelPair_of_eq h limit.isLimit _

/--
theorem `isIso_limit_cone_parallelPair_of_self` / 定理 `isIso_limit_cone_parallelPair_of_self`

English:
theorem isIso_limit_cone_parallelPair_of_self
  given: {c : Fork f f} (h : IsLimit c)
  statement: IsIso c.ι
  proof: isIso_limit_cone_parallelPair_of_eq rfl h

中文:
定理 isIso_limit_cone_parallelPair_of_self
  条件: {c : Fork f f} (h : IsLimit c)
  结论: IsIso c.ι
  证明: isIso_limit_cone_parallelPair_of_eq rfl h

Depends on / 依赖: isIso_limit_cone_parallelPair_of_eq
-/
theorem isIso_limit_cone_parallelPair_of_self {c : Fork f f} (h : IsLimit c) : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq rfl h

/--
theorem `isIso_limit_cone_parallelPair_of_epi` / 定理 `isIso_limit_cone_parallelPair_of_epi`

English:
theorem isIso_limit_cone_parallelPair_of_epi
  given: {c : Fork f g} (h : IsLimit c) [Epi c.ι]
  statement: IsIso c.ι
  proof: isIso_limit_cone_parallelPair_of_eq ((cancel_epi _).1 (Fork.condition c)) h

中文:
定理 isIso_limit_cone_parallelPair_of_epi
  条件: {c : Fork f g} (h : IsLimit c) [Epi c.ι]
  结论: IsIso c.ι
  证明: isIso_limit_cone_parallelPair_of_eq ((cancel_epi _).1 (Fork.condition c)) h

Depends on / 依赖: Fork.condition, cancel_epi, condition, isIso_limit_cone_parallelPair_of_eq
-/
theorem isIso_limit_cone_parallelPair_of_epi {c : Fork f g} (h : IsLimit c) [Epi c.ι] : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq ((cancel_epi _).1 (Fork.condition c)) h

/--
theorem `eq_of_epi_fork_ι` / 定理 `eq_of_epi_fork_ι`

English:
theorem eq_of_epi_fork_ι
  given: (t : Fork f g) [Epi (Fork.ι t)]
  statement: f = g
  proof: (cancel_epi (Fork.ι t)).1 Fork.condition t

中文:
定理 eq_of_epi_fork_ι
  条件: (t : Fork f g) [Epi (Fork.ι t)]
  结论: f = g
  证明: (cancel_epi (Fork.ι t)).1 Fork.condition t

Depends on / 依赖: Fork.condition, cancel_epi, condition
-/
theorem eq_of_epi_fork_ι (t : Fork f g) [Epi (Fork.ι t)] : f = g :=
(cancel_epi (Fork.ι t)).1 Fork.condition t

/--
theorem `eq_of_epi_equalizer` / 定理 `eq_of_epi_equalizer`

English:
theorem eq_of_epi_equalizer
  given: [HasEqualizer f g] [Epi (equalizer.ι f g)]
  statement: f = g
  proof: (cancel_epi (equalizer.ι f g)).1 equalizer.condition _ _

中文:
定理 eq_of_epi_equalizer
  条件: [HasEqualizer f g] [Epi (equalizer.ι f g)]
  结论: f = g
  证明: (cancel_epi (equalizer.ι f g)).1 equalizer.condition _ _

Depends on / 依赖: cancel_epi, condition, equalizer, equalizer.condition
-/
theorem eq_of_epi_equalizer [HasEqualizer f g] [Epi (equalizer.ι f g)] : f = g :=
(cancel_epi (equalizer.ι f g)).1 equalizer.condition _ _

end

/--
Instance `hasEqualizer_of_self` / 实例 `hasEqualizer_of_self`

English:
instance hasEqualizer_of_self
  signature: : HasEqualizer f f
  body: HasLimit.mk
    { cone := idFork rfl
      isLimit := isLimitIdFork rfl }

中文:
实例 hasEqualizer_of_self
  签名: : HasEqualizer f f
  定义体: HasLimit.mk
    { cone := idFork rfl
      isLimit := isLimitIdFork rfl }

Depends on / 依赖: HasLimit, HasLimit.mk, idFork, isLimit, isLimitIdFork
-/
instance hasEqualizer_of_self : HasEqualizer f f :=
  HasLimit.mk
    { cone := idFork rfl
      isLimit := isLimitIdFork rfl }

/--
Instance `equalizer.ι_of_self` / 实例 `equalizer.ι_of_self`

English:
instance equalizer.ι_of_self
  signature: : IsIso (equalizer.ι f f)
  body: equalizer.ι_of_eq rfl

中文:
实例 equalizer.ι_of_self
  签名: : IsIso (equalizer.ι f f)
  定义体: equalizer.ι_of_eq rfl

Depends on / 依赖: equalizer
-/
instance equalizer.ι_of_self : IsIso (equalizer.ι f f) :=
  equalizer.ι_of_eq rfl

/--
Definition of `equalizer.isoSourceOfSelf` / `equalizer.isoSourceOfSelf` 的定义

English:
definition equalizer.isoSourceOfSelf
  signature: : equalizer f f ≅ X
  body: asIso (equalizer.ι f f)

@[simp]

中文:
定义 equalizer.isoSourceOfSelf
  签名: : equalizer f f ≅ X
  定义体: asIso (equalizer.ι f f)

@[simp]

Depends on / 依赖: equalizer
-/
noncomputable def equalizer.isoSourceOfSelf : equalizer f f ≅ X :=
  asIso (equalizer.ι f f)

@[simp]
/--
theorem `equalizer.isoSourceOfSelf_hom` / 定理 `equalizer.isoSourceOfSelf_hom`

English:
theorem equalizer.isoSourceOfSelf_hom
  statement: (equalizer.isoSourceOfSelf f).hom = equalizer.ι f f
  proof: rfl

@[simp]

中文:
定理 equalizer.isoSourceOfSelf_hom
  结论: (equalizer.isoSourceOfSelf f).hom = equalizer.ι f f
  证明: rfl

@[simp]
-/
theorem equalizer.isoSourceOfSelf_hom : (equalizer.isoSourceOfSelf f).hom = equalizer.ι f f :=
  rfl

@[simp]
/--
theorem `equalizer.isoSourceOfSelf_inv` / 定理 `equalizer.isoSourceOfSelf_inv`

English:
theorem equalizer.isoSourceOfSelf_inv
  proof: by
  ext
  simp [equalizer.isoSourceOfSelf]

中文:
定理 equalizer.isoSourceOfSelf_inv
  证明: by
  ext
  simp [equalizer.isoSourceOfSelf]

Depends on / 依赖: equalizer, equalizer.isoSourceOfSelf, isoSourceOfSelf
-/
theorem equalizer.isoSourceOfSelf_inv :
    (equalizer.isoSourceOfSelf f).inv = equalizer.lift (𝟙 X) (by simp) := by
  ext
  simp [equalizer.isoSourceOfSelf]


section

variable {f g : X ⟶ Y} {Z : C} (h : Z ⟶ X)

/--
Definition of `precompFork` / `precompFork` 的定义

English:
definition precompFork
  signature: (s : Fork f g) (c : PullbackCone s.ι h)
  body: Fork.ofι c.snd by
    rw [← c.condition_assoc]; rw [← c.condition_assoc]; rw [s.condition]

中文:
定义 precompFork
  签名: (s : Fork f g) (c : PullbackCone s.ι h)
  定义体: Fork.ofι c.snd by
    rw [← c.condition_assoc]; rw [← c.condition_assoc]; rw [s.condition]

Depends on / 依赖: Fork.of, c.condition_assoc, c.snd, condition, condition_assoc, s.condition
-/
def precompFork (s : Fork f g) (c : PullbackCone s.ι h) : Fork (h ≫ f) (h ≫ g) :=
Fork.ofι c.snd by
    rw [← c.condition_assoc]; rw [← c.condition_assoc]; rw [s.condition]

/--
Definition of `liftPrecomp` / `liftPrecomp` 的定义

English:
definition liftPrecomp
  signature: {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
  body: hc.lift PullbackCone.mk
    (hs.lift <| Fork.ofι (s'.ι ≫ h) (by simp [s'.condition])) s'.ι

中文:
定义 liftPrecomp
  签名: {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
  定义体: hc.lift PullbackCone.mk
    (hs.lift <| Fork.ofι (s'.ι ≫ h) (by simp [s'.condition])) s'.ι

Depends on / 依赖: Fork.of, PullbackCone, PullbackCone.mk, condition, hc.lift, hs.lift
-/
def liftPrecomp {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
    (s' : Fork (h ≫ f) (h ≫ g)) :
    s'.pt ⟶ (precompFork h s c).pt :=
hc.lift PullbackCone.mk
    (hs.lift <| Fork.ofι (s'.ι ≫ h) (by simp [s'.condition])) s'.ι

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitPrecompFork` / `isLimitPrecompFork` 的定义

English:
definition isLimitPrecompFork
  signature: {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
  body: Fork.IsLimit.mk _
    (fun s' => liftPrecomp h hs hc s')
    (by simp [liftPrecomp, precompFork])
    (fun s' m h => hc.hom_ext <| by
      apply PullbackCone.equalizer_ext
      · simp only [liftPrecomp, IsLimit.fac, PullbackCone.mk_π_app]
        apply hs.hom_ext
        apply Fork.equalizer_ext
 

中文:
定义 isLimitPrecompFork
  签名: {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
  定义体: Fork.IsLimit.mk _
    (fun s' => liftPrecomp h hs hc s')
    (by simp [liftPrecomp, precompFork])
    (fun s' m h => hc.hom_ext <| by
      apply PullbackCone.equalizer_ext
      · simp only [liftPrecomp, IsLimit.fac, PullbackCone.mk_π_app]
        apply hs.hom_ext
        apply Fork.equalizer_ext
 

Depends on / 依赖: Fork.IsLimit.mk, Fork.equalizer_ext, IsLimit, IsLimit.fac, PullbackCone, PullbackCone.equalizer_ext, PullbackCone.mk_, c.condition, condition, equalizer_ext, hc.hom_ext, hom_ext, hs.hom_ext, liftPrecomp, precompFork, reassoc_of
-/
def isLimitPrecompFork {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c) :
    IsLimit (precompFork h s c) :=
  Fork.IsLimit.mk _
    (fun s' => liftPrecomp h hs hc s')
    (by simp [liftPrecomp, precompFork])
    (fun s' m h => hc.hom_ext <| by
      apply PullbackCone.equalizer_ext
      · simp only [liftPrecomp, IsLimit.fac, PullbackCone.mk_π_app]
        apply hs.hom_ext
        apply Fork.equalizer_ext
        simp only [Fork.ι_ofι, precompFork] at h
        simp [c.condition, reassoc_of% h]
      · simpa [liftPrecomp] using! h)

/--
lemma `hasEqualizer_precomp_of_equalizer` / 引理 `hasEqualizer_precomp_of_equalizer`

English:
lemma hasEqualizer_precomp_of_equalizer
  statement: {s : Fork f g} (hs : IsLimit s)
  proof: HasLimit.mk
    { cone := precompFork h s c
      isLimit := isLimitPrecompFork h hs hc }

中文:
引理 hasEqualizer_precomp_of_equalizer
  结论: {s : Fork f g} (hs : IsLimit s)
  证明: HasLimit.mk
    { cone := precompFork h s c
      isLimit := isLimitPrecompFork h hs hc }

Depends on / 依赖: HasLimit, HasLimit.mk, isLimit, isLimitPrecompFork, precompFork
-/
lemma hasEqualizer_precomp_of_equalizer {s : Fork f g} (hs : IsLimit s)
    {c : PullbackCone s.ι h} (hc : IsLimit c) :
    HasEqualizer (h ≫ f) (h ≫ g) :=
  HasLimit.mk
    { cone := precompFork h s c
      isLimit := isLimitPrecompFork h hs hc }

/--
Instance `hasEqualizer_precomp_of_hasEqualizer` / 实例 `hasEqualizer_precomp_of_hasEqualizer`

English:
instance hasEqualizer_precomp_of_hasEqualizer
  signature: [HasEqualizer f g] [HasPullback (equalizer.ι f g) h]
  body: hasEqualizer_precomp_of_equalizer h
    (equalizerIsEqualizer f g) (pullback.isLimit (equalizer.ι f g) h)

中文:
实例 hasEqualizer_precomp_of_hasEqualizer
  签名: [HasEqualizer f g] [HasPullback (equalizer.ι f g) h]
  定义体: hasEqualizer_precomp_of_equalizer h
    (equalizerIsEqualizer f g) (pullback.isLimit (equalizer.ι f g) h)

Depends on / 依赖: equalizer, equalizerIsEqualizer, hasEqualizer_precomp_of_equalizer, isLimit, pullback, pullback.isLimit
-/
instance hasEqualizer_precomp_of_hasEqualizer [HasEqualizer f g] [HasPullback (equalizer.ι f g) h] :
    HasEqualizer (h ≫ f) (h ≫ g) :=
  hasEqualizer_precomp_of_equalizer h
    (equalizerIsEqualizer f g) (pullback.isLimit (equalizer.ι f g) h)

end

section

/--
Definition of `HasCoequalizer` / `HasCoequalizer` 的定义

English:
abbreviation HasCoequalizer
  body: HasColimit (parallelPair f g)

中文:
缩写 HasCoequalizer
  定义体: HasColimit (parallelPair f g)

Depends on / 依赖: HasColimit, parallelPair
-/
abbrev HasCoequalizer :=
  HasColimit (parallelPair f g)

variable [HasCoequalizer f g]

/--
Definition of `coequalizer` / `coequalizer` 的定义

English:
abbreviation coequalizer
  signature: : C
  body: colimit (parallelPair f g)

中文:
缩写 coequalizer
  签名: : C
  定义体: colimit (parallelPair f g)

Depends on / 依赖: colimit, parallelPair
-/
noncomputable abbrev coequalizer : C :=
  colimit (parallelPair f g)

/--
Definition of `coequalizer.π` / `coequalizer.π` 的定义

English:
abbreviation coequalizer.π
  signature: : Y ⟶ coequalizer f g
  body: colimit.ι (parallelPair f g) one

中文:
缩写 coequalizer.π
  签名: : Y ⟶ coequalizer f g
  定义体: colimit.ι (parallelPair f g) one

Depends on / 依赖: colimit, parallelPair
-/
noncomputable abbrev coequalizer.π : Y ⟶ coequalizer f g :=
  colimit.ι (parallelPair f g) one

/--
Definition of `coequalizer.cofork` / `coequalizer.cofork` 的定义

English:
abbreviation coequalizer.cofork
  signature: : Cofork f g
  body: colimit.cocone (parallelPair f g)

@[simp]

中文:
缩写 coequalizer.cofork
  签名: : Cofork f g
  定义体: colimit.cocone (parallelPair f g)

@[simp]

Depends on / 依赖: cocone, colimit, colimit.cocone, parallelPair
-/
noncomputable abbrev coequalizer.cofork : Cofork f g :=
  colimit.cocone (parallelPair f g)

@[simp]
/--
theorem `coequalizer.cofork_π` / 定理 `coequalizer.cofork_π`

English:
theorem coequalizer.cofork_π
  statement: (coequalizer.cofork f g).π = coequalizer.π f g
  proof: rfl

中文:
定理 coequalizer.cofork_π
  结论: (coequalizer.cofork f g).π = coequalizer.π f g
  证明: rfl
-/
theorem coequalizer.cofork_π : (coequalizer.cofork f g).π = coequalizer.π f g :=
  rfl

/--
theorem `coequalizer.cofork_ι_app_one` / 定理 `coequalizer.cofork_ι_app_one`

English:
theorem coequalizer.cofork_ι_app_one
  statement: (coequalizer.cofork f g).ι.app one = coequalizer.π f g
  proof: rfl

@[reassoc]

中文:
定理 coequalizer.cofork_ι_app_one
  结论: (coequalizer.cofork f g).ι.app one = coequalizer.π f g
  证明: rfl

@[reassoc]
-/
theorem coequalizer.cofork_ι_app_one : (coequalizer.cofork f g).ι.app one = coequalizer.π f g :=
  rfl

@[reassoc]
/--
theorem `coequalizer.condition` / 定理 `coequalizer.condition`

English:
theorem coequalizer.condition
  statement: f ≫ coequalizer.π f g = g ≫ coequalizer.π f g
  proof: Cofork.condition colimit.cocone parallelPair f g

中文:
定理 coequalizer.condition
  结论: f ≫ coequalizer.π f g = g ≫ coequalizer.π f g
  证明: Cofork.condition colimit.cocone parallelPair f g

Depends on / 依赖: Cofork, Cofork.condition, cocone, colimit, colimit.cocone, condition, parallelPair
-/
theorem coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
Cofork.condition colimit.cocone parallelPair f g

/--
Definition of `coequalizerIsCoequalizer` / `coequalizerIsCoequalizer` 的定义

English:
definition coequalizerIsCoequalizer
  signature: :
  body: IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _) (by simp))

中文:
定义 coequalizerIsCoequalizer
  签名: :
  定义体: IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _) (by simp))

Depends on / 依赖: Cofork, Cofork.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, colimit, colimit.isColimit, isColimit, ofIsoColimit
-/
noncomputable def coequalizerIsCoequalizer :
    IsColimit (Cofork.ofπ (coequalizer.π f g) (coequalizer.condition f g)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _) (by simp))

variable {f g}

/--
Definition of `coequalizer.desc` / `coequalizer.desc` 的定义

English:
abbreviation coequalizer.desc
  signature: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  body: colimit.desc (parallelPair f g) (Cofork.ofπ k h)

@[reassoc]

中文:
缩写 coequalizer.desc
  签名: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  定义体: colimit.desc (parallelPair f g) (Cofork.ofπ k h)

@[reassoc]

Depends on / 依赖: Cofork, Cofork.of, colimit, colimit.desc, parallelPair
-/
noncomputable abbrev coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    coequalizer f g ⟶ W :=
  colimit.desc (parallelPair f g) (Cofork.ofπ k h)

@[reassoc]
/--
theorem `coequalizer.π_desc` / 定理 `coequalizer.π_desc`

English:
theorem coequalizer.π_desc
  given: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  proof: colimit.ι_desc _ _

中文:
定理 coequalizer.π_desc
  条件: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  证明: colimit.ι_desc _ _

Depends on / 依赖: colimit
-/
theorem coequalizer.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    coequalizer.π f g ≫ coequalizer.desc k h = k :=
  colimit.ι_desc _ _

/--
theorem `coequalizer.π_colimMap_desc` / 定理 `coequalizer.π_colimMap_desc`

English:
theorem coequalizer.π_colimMap_desc
  statement: {X' Y' Z : C} (f' g' : X' ⟶ Y') [HasCoequalizer f' g']
  proof: by
  rw [ι_colimMap_assoc]; rw [parallelPairHom_app_one]; rw [coequalizer.π_desc]

中文:
定理 coequalizer.π_colimMap_desc
  结论: {X' Y' Z : C} (f' g' : X' ⟶ Y') [HasCoequalizer f' g']
  证明: by
  rw [ι_colimMap_assoc]; rw [parallelPairHom_app_one]; rw [coequalizer.π_desc]

Depends on / 依赖: coequalizer, parallelPairHom_app_one
-/
theorem coequalizer.π_colimMap_desc {X' Y' Z : C} (f' g' : X' ⟶ Y') [HasCoequalizer f' g']
    (p : X ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') (h : Y' ⟶ Z)
    (wh : f' ≫ h = g' ≫ h) :
    coequalizer.π f g ≫ colimMap (parallelPairHom f g f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h := by
  rw [ι_colimMap_assoc]; rw [parallelPairHom_app_one]; rw [coequalizer.π_desc]

/--
Definition of `coequalizer.desc'` / `coequalizer.desc'` 的定义

English:
definition coequalizer.desc'
  signature: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  body: ⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩

中文:
定义 coequalizer.desc'
  签名: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  定义体: ⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩

Depends on / 依赖: coequalizer, coequalizer.desc
-/
noncomputable def coequalizer.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    { l : coequalizer f g ⟶ W // coequalizer.π f g ≫ l = k } :=
  ⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
map -/
@[ext]
/--
theorem `coequalizer.hom_ext` / 定理 `coequalizer.hom_ext`

English:
theorem coequalizer.hom_ext
  statement: {W : C} {k l : coequalizer f g ⟶ W}
  proof: Cofork.IsColimit.hom_ext (colimit.isColimit _) h

中文:
定理 coequalizer.hom_ext
  结论: {W : C} {k l : coequalizer f g ⟶ W}
  证明: Cofork.IsColimit.hom_ext (colimit.isColimit _) h

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, colimit, colimit.isColimit, hom_ext, isColimit
-/
theorem coequalizer.hom_ext {W : C} {k l : coequalizer f g ⟶ W}
    (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) : k = l :=
  Cofork.IsColimit.hom_ext (colimit.isColimit _) h

/--
theorem `coequalizer.existsUnique` / 定理 `coequalizer.existsUnique`

English:
theorem coequalizer.existsUnique
  given: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  proof: Cofork.IsColimit.existsUnique (colimit.isColimit _) _ h

中文:
定理 coequalizer.existsUnique
  条件: {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k)
  证明: Cofork.IsColimit.existsUnique (colimit.isColimit _) _ h

Depends on / 依赖: Cofork, Cofork.IsColimit.existsUnique, IsColimit, colimit, colimit.isColimit, existsUnique, isColimit
-/
theorem coequalizer.existsUnique {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    exists! d : coequalizer f g ⟶ W, coequalizer.π f g ≫ d = k :=
  Cofork.IsColimit.existsUnique (colimit.isColimit _) _ h

/--
Instance `coequalizer.π_epi` / 实例 `coequalizer.π_epi`

English:
instance coequalizer.π_epi
  signature: : Epi (coequalizer.π f g) where
  body: coequalizer.hom_ext w

中文:
实例 coequalizer.π_epi
  签名: : Epi (coequalizer.π f g) where
  定义体: coequalizer.hom_ext w

Depends on / 依赖: coequalizer, coequalizer.hom_ext, hom_ext
-/
instance coequalizer.π_epi : Epi (coequalizer.π f g) where
  left_cancellation _ _ w := coequalizer.hom_ext w

end

section

variable {f g}

/--
theorem `epi_of_isColimit_cofork` / 定理 `epi_of_isColimit_cofork`

English:
theorem epi_of_isColimit_cofork
  given: {c : Cofork f g} (i : IsColimit c)
  statement: Epi c.π
  proof: { left_cancellation := fun _ _ w => Cofork.IsColimit.hom_ext i w }

中文:
定理 epi_of_isColimit_cofork
  条件: {c : Cofork f g} (i : IsColimit c)
  结论: Epi c.π
  证明: { left_cancellation := fun _ _ w => Cofork.IsColimit.hom_ext i w }

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, hom_ext, left_cancellation
-/
theorem epi_of_isColimit_cofork {c : Cofork f g} (i : IsColimit c) : Epi c.π :=
  { left_cancellation := fun _ _ w => Cofork.IsColimit.hom_ext i w }

end

section

variable {f g}

/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/
@[implicit_reducible]
/--
Definition of `idCofork` / `idCofork` 的定义

English:
definition idCofork
  signature: (h : f = g)
  body: Cofork.ofπ (𝟙 Y) h ▸ rfl

中文:
定义 idCofork
  签名: (h : f = g)
  定义体: Cofork.ofπ (𝟙 Y) h ▸ rfl

Depends on / 依赖: Cofork, Cofork.of
-/
def idCofork (h : f = g) : Cofork f g :=
Cofork.ofπ (𝟙 Y) h ▸ rfl

/--
Definition of `isColimitIdCofork` / `isColimitIdCofork` 的定义

English:
definition isColimitIdCofork
  signature: (h : f = g)
  body: Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun _ => Category.id_comp _) fun s m h => by
    convert! h
    exact (Category.id_comp _).symm

中文:
定义 isColimitIdCofork
  签名: (h : f = g)
  定义体: Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun _ => Category.id_comp _) fun s m h => by
    convert! h
    exact (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, Cofork, Cofork.IsColimit.mk, IsColimit, convert, id_comp
-/
def isColimitIdCofork (h : f = g) : IsColimit (idCofork h) :=
  Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun _ => Category.id_comp _) fun s m h => by
    convert! h
    exact (Category.id_comp _).symm

/--
theorem `isIso_colimit_cocone_parallelPair_of_eq` / 定理 `isIso_colimit_cocone_parallelPair_of_eq`

English:
theorem isIso_colimit_cocone_parallelPair_of_eq
  given: (h₀ : f = g) {c : Cofork f g} (h : IsColimit c)
  proof: Iso.isIso_hom IsColimit.coconePointUniqueUpToIso (isColimitIdCofork h₀) h

中文:
定理 isIso_colimit_cocone_parallelPair_of_eq
  条件: (h₀ : f = g) {c : Cofork f g} (h : IsColimit c)
  证明: Iso.isIso_hom IsColimit.coconePointUniqueUpToIso (isColimitIdCofork h₀) h

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, Iso.isIso_hom, coconePointUniqueUpToIso, isColimitIdCofork, isIso_hom
-/
theorem isIso_colimit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h : IsColimit c) :
    IsIso c.π :=
Iso.isIso_hom IsColimit.coconePointUniqueUpToIso (isColimitIdCofork h₀) h

/--
theorem `coequalizer.π_of_eq` / 定理 `coequalizer.π_of_eq`

English:
theorem coequalizer.π_of_eq
  given: [HasCoequalizer f g] (h : f = g)
  statement: IsIso (coequalizer.π f g)
  proof: isIso_colimit_cocone_parallelPair_of_eq h colimit.isColimit _

中文:
定理 coequalizer.π_of_eq
  条件: [HasCoequalizer f g] (h : f = g)
  结论: IsIso (coequalizer.π f g)
  证明: isIso_colimit_cocone_parallelPair_of_eq h colimit.isColimit _

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isIso_colimit_cocone_parallelPair_of_eq
-/
theorem coequalizer.π_of_eq [HasCoequalizer f g] (h : f = g) : IsIso (coequalizer.π f g) :=
isIso_colimit_cocone_parallelPair_of_eq h colimit.isColimit _

/--
theorem `isIso_colimit_cocone_parallelPair_of_self` / 定理 `isIso_colimit_cocone_parallelPair_of_self`

English:
theorem isIso_colimit_cocone_parallelPair_of_self
  given: {c : Cofork f f} (h : IsColimit c)
  statement: IsIso c.π
  proof: isIso_colimit_cocone_parallelPair_of_eq rfl h

中文:
定理 isIso_colimit_cocone_parallelPair_of_self
  条件: {c : Cofork f f} (h : IsColimit c)
  结论: IsIso c.π
  证明: isIso_colimit_cocone_parallelPair_of_eq rfl h

Depends on / 依赖: isIso_colimit_cocone_parallelPair_of_eq
-/
theorem isIso_colimit_cocone_parallelPair_of_self {c : Cofork f f} (h : IsColimit c) : IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq rfl h

/--
theorem `isIso_limit_cocone_parallelPair_of_epi` / 定理 `isIso_limit_cocone_parallelPair_of_epi`

English:
theorem isIso_limit_cocone_parallelPair_of_epi
  given: {c : Cofork f g} (h : IsColimit c) [Mono c.π]
  proof: isIso_colimit_cocone_parallelPair_of_eq ((cancel_mono _).1 (Cofork.condition c)) h

中文:
定理 isIso_limit_cocone_parallelPair_of_epi
  条件: {c : Cofork f g} (h : IsColimit c) [Mono c.π]
  证明: isIso_colimit_cocone_parallelPair_of_eq ((cancel_mono _).1 (Cofork.condition c)) h

Depends on / 依赖: Cofork, Cofork.condition, cancel_mono, condition, isIso_colimit_cocone_parallelPair_of_eq
-/
theorem isIso_limit_cocone_parallelPair_of_epi {c : Cofork f g} (h : IsColimit c) [Mono c.π] :
    IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq ((cancel_mono _).1 (Cofork.condition c)) h

/--
theorem `eq_of_mono_cofork_π` / 定理 `eq_of_mono_cofork_π`

English:
theorem eq_of_mono_cofork_π
  given: (t : Cofork f g) [Mono (Cofork.π t)]
  statement: f = g
  proof: (cancel_mono (Cofork.π t)).1 Cofork.condition t

中文:
定理 eq_of_mono_cofork_π
  条件: (t : Cofork f g) [Mono (Cofork.π t)]
  结论: f = g
  证明: (cancel_mono (Cofork.π t)).1 Cofork.condition t

Depends on / 依赖: Cofork, Cofork.condition, cancel_mono, condition
-/
theorem eq_of_mono_cofork_π (t : Cofork f g) [Mono (Cofork.π t)] : f = g :=
(cancel_mono (Cofork.π t)).1 Cofork.condition t

/--
theorem `eq_of_mono_coequalizer` / 定理 `eq_of_mono_coequalizer`

English:
theorem eq_of_mono_coequalizer
  given: [HasCoequalizer f g] [Mono (coequalizer.π f g)]
  statement: f = g
  proof: (cancel_mono (coequalizer.π f g)).1 coequalizer.condition _ _

中文:
定理 eq_of_mono_coequalizer
  条件: [HasCoequalizer f g] [Mono (coequalizer.π f g)]
  结论: f = g
  证明: (cancel_mono (coequalizer.π f g)).1 coequalizer.condition _ _

Depends on / 依赖: cancel_mono, coequalizer, coequalizer.condition, condition
-/
theorem eq_of_mono_coequalizer [HasCoequalizer f g] [Mono (coequalizer.π f g)] : f = g :=
(cancel_mono (coequalizer.π f g)).1 coequalizer.condition _ _

end

/--
Instance `hasCoequalizer_of_self` / 实例 `hasCoequalizer_of_self`

English:
instance hasCoequalizer_of_self
  signature: : HasCoequalizer f f
  body: HasColimit.mk
    { cocone := idCofork rfl
      isColimit := isColimitIdCofork rfl }

中文:
实例 hasCoequalizer_of_self
  签名: : HasCoequalizer f f
  定义体: HasColimit.mk
    { cocone := idCofork rfl
      isColimit := isColimitIdCofork rfl }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, idCofork, isColimit, isColimitIdCofork
-/
instance hasCoequalizer_of_self : HasCoequalizer f f :=
  HasColimit.mk
    { cocone := idCofork rfl
      isColimit := isColimitIdCofork rfl }

/--
Instance `coequalizer.π_of_self` / 实例 `coequalizer.π_of_self`

English:
instance coequalizer.π_of_self
  signature: : IsIso (coequalizer.π f f)
  body: coequalizer.π_of_eq rfl

中文:
实例 coequalizer.π_of_self
  签名: : IsIso (coequalizer.π f f)
  定义体: coequalizer.π_of_eq rfl

Depends on / 依赖: coequalizer
-/
instance coequalizer.π_of_self : IsIso (coequalizer.π f f) :=
  coequalizer.π_of_eq rfl

/--
Definition of `coequalizer.isoTargetOfSelf` / `coequalizer.isoTargetOfSelf` 的定义

English:
definition coequalizer.isoTargetOfSelf
  signature: : coequalizer f f ≅ Y
  body: (asIso (coequalizer.π f f)).symm

@[simp]

中文:
定义 coequalizer.isoTargetOfSelf
  签名: : coequalizer f f ≅ Y
  定义体: (asIso (coequalizer.π f f)).symm

@[simp]

Depends on / 依赖: coequalizer
-/
noncomputable def coequalizer.isoTargetOfSelf : coequalizer f f ≅ Y :=
  (asIso (coequalizer.π f f)).symm

@[simp]
/--
theorem `coequalizer.isoTargetOfSelf_hom` / 定理 `coequalizer.isoTargetOfSelf_hom`

English:
theorem coequalizer.isoTargetOfSelf_hom
  proof: by
  ext
  simp [coequalizer.isoTargetOfSelf]

@[simp]

中文:
定理 coequalizer.isoTargetOfSelf_hom
  证明: by
  ext
  simp [coequalizer.isoTargetOfSelf]

@[simp]

Depends on / 依赖: coequalizer, coequalizer.isoTargetOfSelf, isoTargetOfSelf
-/
theorem coequalizer.isoTargetOfSelf_hom :
    (coequalizer.isoTargetOfSelf f).hom = coequalizer.desc (𝟙 Y) (by simp) := by
  ext
  simp [coequalizer.isoTargetOfSelf]

@[simp]
/--
theorem `coequalizer.isoTargetOfSelf_inv` / 定理 `coequalizer.isoTargetOfSelf_inv`

English:
theorem coequalizer.isoTargetOfSelf_inv
  statement: (coequalizer.isoTargetOfSelf f).inv = coequalizer.π f f
  proof: rfl

中文:
定理 coequalizer.isoTargetOfSelf_inv
  结论: (coequalizer.isoTargetOfSelf f).inv = coequalizer.π f f
  证明: rfl
-/
theorem coequalizer.isoTargetOfSelf_inv : (coequalizer.isoTargetOfSelf f).inv = coequalizer.π f f :=
  rfl

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/--
Definition of `equalizerComparison` / `equalizerComparison` 的定义

English:
definition equalizerComparison
  signature: [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)]
  body: equalizer.lift (G.map (equalizer.ι _ _))
    (by simp only [← G.map_comp]; rw [equalizer.condition])

@[reassoc (attr := simp)]

中文:
定义 equalizerComparison
  签名: [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)]
  定义体: equalizer.lift (G.map (equalizer.ι _ _))
    (by simp only [← G.map_comp]; rw [equalizer.condition])

@[reassoc (attr := simp)]

Depends on / 依赖: G.map, G.map_comp, condition, equalizer, equalizer.condition, equalizer.lift, map_comp
-/
noncomputable def equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
  equalizer.lift (G.map (equalizer.ι _ _))
    (by simp only [← G.map_comp]; rw [equalizer.condition])

@[reassoc (attr := simp)]
/--
theorem `equalizerComparison_comp_π` / 定理 `equalizerComparison_comp_π`

English:
theorem equalizerComparison_comp_π
  given: [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)]
  proof: equalizer.lift_ι _ _

@[reassoc (attr := simp)]

中文:
定理 equalizerComparison_comp_π
  条件: [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)]
  证明: equalizer.lift_ι _ _

@[reassoc (attr := simp)]

Depends on / 依赖: equalizer, equalizer.lift_
-/
theorem equalizerComparison_comp_π [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    equalizerComparison f g G ≫ equalizer.ι (G.map f) (G.map g) = G.map (equalizer.ι f g) :=
  equalizer.lift_ι _ _

@[reassoc (attr := simp)]
/--
theorem `map_lift_equalizerComparison` / 定理 `map_lift_equalizerComparison`

English:
theorem map_lift_equalizerComparison
  statement: [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] {Z : C}
  proof: by
  apply equalizer.hom_ext
  simp [← G.map_comp]

中文:
定理 map_lift_equalizerComparison
  结论: [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] {Z : C}
  证明: by
  apply equalizer.hom_ext
  simp [← G.map_comp]

Depends on / 依赖: G.map_comp, equalizer, equalizer.hom_ext, hom_ext, map_comp
-/
theorem map_lift_equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] {Z : C}
    {h : Z ⟶ X} (w : h ≫ f = h ≫ g) :
    G.map (equalizer.lift h w) ≫ equalizerComparison f g G =
      equalizer.lift (G.map h) (by simp only [← G.map_comp, w]) := by
  apply equalizer.hom_ext
  simp [← G.map_comp]

/--
Definition of `coequalizerComparison` / `coequalizerComparison` 的定义

English:
definition coequalizerComparison
  signature: [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
  body: coequalizer.desc (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp]; rw [coequalizer.condition])

@[reassoc (attr := simp)]

中文:
定义 coequalizerComparison
  签名: [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
  定义体: coequalizer.desc (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp]; rw [coequalizer.condition])

@[reassoc (attr := simp)]

Depends on / 依赖: G.map, G.map_comp, coequalizer, coequalizer.condition, coequalizer.desc, condition, map_comp
-/
noncomputable def coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)] :
    coequalizer (G.map f) (G.map g) ⟶ G.obj (coequalizer f g) :=
  coequalizer.desc (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp]; rw [coequalizer.condition])

@[reassoc (attr := simp)]
/--
theorem `ι_comp_coequalizerComparison` / 定理 `ι_comp_coequalizerComparison`

English:
theorem ι_comp_coequalizerComparison
  given: [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
  proof: coequalizer.π_desc _ _

@[reassoc (attr := simp)]

中文:
定理 ι_comp_coequalizerComparison
  条件: [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
  证明: coequalizer.π_desc _ _

@[reassoc (attr := simp)]

Depends on / 依赖: coequalizer
-/
theorem ι_comp_coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)] :
    coequalizer.π _ _ ≫ coequalizerComparison f g G = G.map (coequalizer.π _ _) :=
  coequalizer.π_desc _ _

@[reassoc (attr := simp)]
/--
theorem `coequalizerComparison_map_desc` / 定理 `coequalizerComparison_map_desc`

English:
theorem coequalizerComparison_map_desc
  statement: [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
  proof: by
  apply coequalizer.hom_ext
  simp [← G.map_comp]

中文:
定理 coequalizerComparison_map_desc
  结论: [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
  证明: by
  apply coequalizer.hom_ext
  simp [← G.map_comp]

Depends on / 依赖: G.map_comp, coequalizer, coequalizer.hom_ext, hom_ext, map_comp
-/
theorem coequalizerComparison_map_desc [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
    {Z : C} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) :
    coequalizerComparison f g G ≫ G.map (coequalizer.desc h w) =
      coequalizer.desc (G.map h) (by simp only [← G.map_comp, w]) := by
  apply coequalizer.hom_ext
  simp [← G.map_comp]

end Comparison

variable (C)

/--
Definition of `HasEqualizers` / `HasEqualizers` 的定义

English:
abbreviation HasEqualizers
  body: HasLimitsOfShape WalkingParallelPair C

中文:
缩写 HasEqualizers
  定义体: HasLimitsOfShape WalkingParallelPair C

Depends on / 依赖: HasLimitsOfShape, WalkingParallelPair
-/
abbrev HasEqualizers :=
  HasLimitsOfShape WalkingParallelPair C

/--
Definition of `HasCoequalizers` / `HasCoequalizers` 的定义

English:
abbreviation HasCoequalizers
  body: HasColimitsOfShape WalkingParallelPair C

中文:
缩写 HasCoequalizers
  定义体: HasColimitsOfShape WalkingParallelPair C

Depends on / 依赖: HasColimitsOfShape, WalkingParallelPair
-/
abbrev HasCoequalizers :=
  HasColimitsOfShape WalkingParallelPair C

/--
theorem `hasEqualizers_of_hasLimit_parallelPair` / 定理 `hasEqualizers_of_hasLimit_parallelPair`

English:
theorem hasEqualizers_of_hasLimit_parallelPair
  proof: { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm }

中文:
定理 hasEqualizers_of_hasLimit_parallelPair
  证明: { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm }

Depends on / 依赖: diagramIsoParallelPair, hasLimit_of_iso, has_limit
-/
theorem hasEqualizers_of_hasLimit_parallelPair
    [forall {X Y : C} {f g : X ⟶ Y}, HasLimit (parallelPair f g)] : HasEqualizers C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm }

/--
theorem `hasCoequalizers_of_hasColimit_parallelPair` / 定理 `hasCoequalizers_of_hasColimit_parallelPair`

English:
theorem hasCoequalizers_of_hasColimit_parallelPair
  proof: { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelPair F) }

中文:
定理 hasCoequalizers_of_hasColimit_parallelPair
  证明: { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelPair F) }

Depends on / 依赖: diagramIsoParallelPair, hasColimit_of_iso, has_colimit
-/
theorem hasCoequalizers_of_hasColimit_parallelPair
    [forall {X Y : C} {f g : X ⟶ Y}, HasColimit (parallelPair f g)] : HasCoequalizers C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelPair F) }

section

-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
variable {C} [IsSplitMono f]

/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `isSplitMonoEqualizes` that it is a limit cone.
-/
@[simps (rhsMd := default)]
/--
Definition of `coneOfIsSplitMono` / `coneOfIsSplitMono` 的定义

English:
definition coneOfIsSplitMono
  signature: : Fork (𝟙 Y) (retraction f ≫ f)
  body: Fork.ofι f (by simp)

@[simp]

中文:
定义 coneOfIsSplitMono
  签名: : Fork (𝟙 Y) (retraction f ≫ f)
  定义体: Fork.ofι f (by simp)

@[simp]

Depends on / 依赖: Fork.of
-/
noncomputable def coneOfIsSplitMono : Fork (𝟙 Y) (retraction f ≫ f) :=
  Fork.ofι f (by simp)

@[simp]
/--
theorem `coneOfIsSplitMono_ι` / 定理 `coneOfIsSplitMono_ι`

English:
theorem coneOfIsSplitMono_ι
  statement: (coneOfIsSplitMono f).ι = f
  proof: rfl

中文:
定理 coneOfIsSplitMono_ι
  结论: (coneOfIsSplitMono f).ι = f
  证明: rfl
-/
theorem coneOfIsSplitMono_ι : (coneOfIsSplitMono f).ι = f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isSplitMonoEqualizes` / `isSplitMonoEqualizes` 的定义

English:
definition isSplitMonoEqualizes
  signature: {X Y : C} (f : X ⟶ Y) [IsSplitMono f]
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ retraction f, by
      dsimp
      rw [Category.assoc]; rw [← s.condition]
      apply Category.comp_id, fun hm => by simp [← hm]⟩

中文:
定义 isSplitMonoEqualizes
  签名: {X Y : C} (f : X ⟶ Y) [IsSplitMono f]
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ retraction f, by
      dsimp
      rw [Category.assoc]; rw [← s.condition]
      apply Category.comp_id, fun hm => by simp [← hm]⟩

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Fork.IsLimit.mk, IsLimit, comp_id, condition, retraction, s.condition
-/
noncomputable def isSplitMonoEqualizes {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsLimit (coneOfIsSplitMono f) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ retraction f, by
      dsimp
      rw [Category.assoc]; rw [← s.condition]
      apply Category.comp_id, fun hm => by simp [← hm]⟩

end

/--
Definition of `splitMonoOfEqualizer` / `splitMonoOfEqualizer` 的定义

English:
definition splitMonoOfEqualizer
  signature: {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f)
  body: r
  id := Fork.IsLimit.hom_ext h ((Category.assoc _ _ _).trans <| hr.trans (Category.id_comp _).symm)

中文:
定义 splitMonoOfEqualizer
  签名: {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f)
  定义体: r
  id := Fork.IsLimit.hom_ext h ((Category.assoc _ _ _).trans <| hr.trans (Category.id_comp _).symm)
-/
def splitMonoOfEqualizer {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f)
    (h : IsLimit (Fork.ofι f (hr.trans (Category.comp_id _).symm : f ≫ r ≫ f = f ≫ 𝟙 Y))) :
    SplitMono f where
  retraction := r
  id := Fork.IsLimit.hom_ext h ((Category.assoc _ _ _).trans <| hr.trans (Category.id_comp _).symm)

variable {C f g}

/--
Definition of `isEqualizerCompMono` / `isEqualizerCompMono` 的定义

English:
definition isEqualizerCompMono
  signature: {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h]
  body: by
      simp only [← Category.assoc]
      exact congrArg (· ≫ h) c.condition
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork (f ≫ h) (g ≫ h)) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : Fork f g := Fork.ofι s.ι (by apply hm.right_cancellation; simp [s.condition])
    let l := Fork.IsLimit.lift

中文:
定义 isEqualizerCompMono
  签名: {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h]
  定义体: by
      simp only [← Category.assoc]
      exact congrArg (· ≫ h) c.condition
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork (f ≫ h) (g ≫ h)) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : Fork f g := Fork.ofι s.ι (by apply hm.right_cancellation; simp [s.condition])
    let l := Fork.IsLimit.lift

Depends on / 依赖: Category, Category.assoc, Fork.IsLimit.hom_ext, Fork.IsLimit.lift, Fork.IsLimit.mk, Fork.of, IsLimit, adj.unit.app, c.condition, condition, hm.right_cancellation, hom_ext, infer_instance, right_cancellation, s.condition
-/
def isEqualizerCompMono {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h] :
    have : Fork.ι c ≫ f ≫ h = Fork.ι c ≫ g ≫ h := by
      simp only [← Category.assoc]
      exact congrArg (· ≫ h) c.condition
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork (f ≫ h) (g ≫ h)) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : Fork f g := Fork.ofι s.ι (by apply hm.right_cancellation; simp [s.condition])
    let l := Fork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

variable (C f g)

@[instance]
/--
theorem `hasEqualizer_comp_mono` / 定理 `hasEqualizer_comp_mono`

English:
theorem hasEqualizer_comp_mono
  given: [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h]
  proof: ⟨⟨{ cone := _
        isLimit := isEqualizerCompMono (limit.isLimit _) h }⟩⟩

中文:
定理 hasEqualizer_comp_mono
  条件: [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h]
  证明: ⟨⟨{ cone := _
        isLimit := isEqualizerCompMono (limit.isLimit _) h }⟩⟩

Depends on / 依赖: infer_instance, isEqualizerCompMono, isIso_tfae, isLimit, limit.isLimit, revert
-/
theorem hasEqualizer_comp_mono [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h] :
    HasEqualizer (f ≫ h) (g ≫ h) :=
  ⟨⟨{ cone := _
        isLimit := isEqualizerCompMono (limit.isLimit _) h }⟩⟩

/-- An equalizer of an idempotent morphism and the identity is split mono. -/
@[simps]
/--
Definition of `splitMonoOfIdempotentOfIsLimitFork` / `splitMonoOfIdempotentOfIsLimitFork` 的定义

English:
definition splitMonoOfIdempotentOfIsLimitFork
  signature: {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Fork (𝟙 X) f}
  body: i.lift (Fork.ofι f (by simp [hf]))
  id := by
    let := mono_of_isLimit_fork i
    rw [← cancel_mono_id c.ι]; rw [Category.assoc]; rw [Fork.IsLimit.lift_ι]; rw [Fork.ι_ofι]; rw [← c.condition]
    exact Category.comp_id c.ι

中文:
定义 splitMonoOfIdempotentOfIsLimitFork
  签名: {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Fork (𝟙 X) f}
  定义体: i.lift (Fork.ofι f (by simp [hf]))
  id := by
    let := mono_of_isLimit_fork i
    rw [← cancel_mono_id c.ι]; rw [Category.assoc]; rw [Fork.IsLimit.lift_ι]; rw [Fork.ι_ofι]; rw [← c.condition]
    exact Category.comp_id c.ι

Depends on / 依赖: Fork.of, i.lift
-/
def splitMonoOfIdempotentOfIsLimitFork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Fork (𝟙 X) f}
    (i : IsLimit c) : SplitMono c.ι where
  retraction := i.lift (Fork.ofι f (by simp [hf]))
  id := by
    let := mono_of_isLimit_fork i
    rw [← cancel_mono_id c.ι]; rw [Category.assoc]; rw [Fork.IsLimit.lift_ι]; rw [Fork.ι_ofι]; rw [← c.condition]
    exact Category.comp_id c.ι

/--
Definition of `splitMonoOfIdempotentEqualizer` / `splitMonoOfIdempotentEqualizer` 的定义

English:
definition splitMonoOfIdempotentEqualizer
  signature: {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
  body: splitMonoOfIdempotentOfIsLimitFork _ hf (limit.isLimit _)

中文:
定义 splitMonoOfIdempotentEqualizer
  签名: {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
  定义体: splitMonoOfIdempotentOfIsLimitFork _ hf (limit.isLimit _)

Depends on / 依赖: isLimit, limit.isLimit, splitMonoOfIdempotentOfIsLimitFork
-/
noncomputable def splitMonoOfIdempotentEqualizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasEqualizer (𝟙 X) f] : SplitMono (equalizer.ι (𝟙 X) f) :=
  splitMonoOfIdempotentOfIsLimitFork _ hf (limit.isLimit _)

section

-- In this section we show that a split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
variable {C} [IsSplitEpi f]

/-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `isSplitEpiCoequalizes` that it is a colimit cocone.
-/
@[simps (rhsMd := default)]
/--
Definition of `coconeOfIsSplitEpi` / `coconeOfIsSplitEpi` 的定义

English:
definition coconeOfIsSplitEpi
  signature: : Cofork (𝟙 X) (f ≫ section_ f)
  body: Cofork.ofπ f (by simp)

@[simp]

中文:
定义 coconeOfIsSplitEpi
  签名: : Cofork (𝟙 X) (f ≫ section_ f)
  定义体: Cofork.ofπ f (by simp)

@[simp]

Depends on / 依赖: Cofork, Cofork.of
-/
noncomputable def coconeOfIsSplitEpi : Cofork (𝟙 X) (f ≫ section_ f) :=
  Cofork.ofπ f (by simp)

@[simp]
/--
theorem `coconeOfIsSplitEpi_π` / 定理 `coconeOfIsSplitEpi_π`

English:
theorem coconeOfIsSplitEpi_π
  statement: (coconeOfIsSplitEpi f).π = f
  proof: rfl

中文:
定理 coconeOfIsSplitEpi_π
  结论: (coconeOfIsSplitEpi f).π = f
  证明: rfl

Depends on / 依赖: BraidedCategory, BraidedCategory.ofFaithful, CoreMonoidal, Functor, Functor.CoreMonoidal.toLaxMonoidal, Transported, Transported.instBraidedCategory, fromInducedCoreMonoidal, instBraidedCategory, instances, ofFaithful, toLaxMonoidal
-/
theorem coconeOfIsSplitEpi_π : (coconeOfIsSplitEpi f).π = f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isSplitEpiCoequalizes` / `isSplitEpiCoequalizes` 的定义

English:
definition isSplitEpiCoequalizes
  signature: {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨section_ f ≫ s.π, by
      dsimp
      rw [← Category.assoc]; rw [← s.condition]; rw [Category.id_comp], fun hm => by simp [← hm]⟩

中文:
定义 isSplitEpiCoequalizes
  签名: {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨section_ f ≫ s.π, by
      dsimp
      rw [← Category.assoc]; rw [← s.condition]; rw [Category.id_comp], fun hm => by simp [← hm]⟩

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Cofork, Cofork.IsColimit.mk, IsColimit, condition, id_comp, s.condition, section_
-/
noncomputable def isSplitEpiCoequalizes {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsColimit (coconeOfIsSplitEpi f) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨section_ f ≫ s.π, by
      dsimp
      rw [← Category.assoc]; rw [← s.condition]; rw [Category.id_comp], fun hm => by simp [← hm]⟩

end

/--
Definition of `splitEpiOfCoequalizer` / `splitEpiOfCoequalizer` 的定义

English:
definition splitEpiOfCoequalizer
  signature: {X Y : C} {f : X ⟶ Y} {s : Y ⟶ X} (hs : f ≫ s ≫ f = f)
  body: s
  id := Cofork.IsColimit.hom_ext h (hs.trans (Category.comp_id _).symm)

中文:
定义 splitEpiOfCoequalizer
  签名: {X Y : C} {f : X ⟶ Y} {s : Y ⟶ X} (hs : f ≫ s ≫ f = f)
  定义体: s
  id := Cofork.IsColimit.hom_ext h (hs.trans (Category.comp_id _).symm)

Depends on / 依赖: Functor, Functor.LaxMonoidal, Functor.Monoidal, Functor.OplaxMonoidal, LaxMonoidal, Monoidal, OplaxMonoidal, comp_id, functor, inverse, inverse.map_injective, map_braiding, map_injective
-/
def splitEpiOfCoequalizer {X Y : C} {f : X ⟶ Y} {s : Y ⟶ X} (hs : f ≫ s ≫ f = f)
    (h :
      IsColimit
        (Cofork.ofπ f
          ((Category.assoc _ _ _).trans <| hs.trans (Category.id_comp f).symm :
            (f ≫ s) ≫ f = 𝟙 X ≫ f))) :
    SplitEpi f where
  section_ := s
  id := Cofork.IsColimit.hom_ext h (hs.trans (Category.comp_id _).symm)

variable {C f g}

/--
Definition of `isCoequalizerEpiComp` / `isCoequalizerEpiComp` 的定义

English:
definition isCoequalizerEpiComp
  signature: {c : Cofork f g} (i : IsColimit c) {W : C} (h : W ⟶ X) [hm : Epi h]
  body: by
      simp only [Category.assoc]
      exact congrArg (h ≫ ·) c.condition
    IsColimit (Cofork.ofπ c.π (this) : Cofork (h ≫ f) (h ≫ g)) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : Cofork f g :=
      Cofork.ofπ s.π (by apply hm.left_cancellation; simp_rw [← Category.assoc, s.condition])
  

中文:
定义 isCoequalizerEpiComp
  签名: {c : Cofork f g} (i : IsColimit c) {W : C} (h : W ⟶ X) [hm : Epi h]
  定义体: by
      simp only [Category.assoc]
      exact congrArg (h ≫ ·) c.condition
    IsColimit (Cofork.ofπ c.π (this) : Cofork (h ≫ f) (h ≫ g)) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : Cofork f g :=
      Cofork.ofπ s.π (by apply hm.left_cancellation; simp_rw [← Category.assoc, s.condition])
  

Depends on / 依赖: Category, Category.assoc, Cofork, Cofork.IsColimit.desc, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, Cofork.of, IsColimit, c.condition, condition, hm.left_cancellation, hom_ext, left_cancellation, s.condition, simp_rw
-/
def isCoequalizerEpiComp {c : Cofork f g} (i : IsColimit c) {W : C} (h : W ⟶ X) [hm : Epi h] :
    have : (h ≫ f) ≫ Cofork.π c = (h ≫ g) ≫ Cofork.π c := by
      simp only [Category.assoc]
      exact congrArg (h ≫ ·) c.condition
    IsColimit (Cofork.ofπ c.π (this) : Cofork (h ≫ f) (h ≫ g)) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : Cofork f g :=
      Cofork.ofπ s.π (by apply hm.left_cancellation; simp_rw [← Category.assoc, s.condition])
    let l := Cofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩

/--
theorem `hasCoequalizer_epi_comp` / 定理 `hasCoequalizer_epi_comp`

English:
theorem hasCoequalizer_epi_comp
  given: [HasCoequalizer f g] {W : C} (h : W ⟶ X) [Epi h]
  proof: ⟨⟨{ cocone := _
        isColimit := isCoequalizerEpiComp (colimit.isColimit _) h }⟩⟩

中文:
定理 hasCoequalizer_epi_comp
  条件: [HasCoequalizer f g] {W : C} (h : W ⟶ X) [Epi h]
  证明: ⟨⟨{ cocone := _
        isColimit := isCoequalizerEpiComp (colimit.isColimit _) h }⟩⟩

Depends on / 依赖: cocone, colimit, colimit.isColimit, isCoequalizerEpiComp, isColimit
-/
theorem hasCoequalizer_epi_comp [HasCoequalizer f g] {W : C} (h : W ⟶ X) [Epi h] :
    HasCoequalizer (h ≫ f) (h ≫ g) :=
  ⟨⟨{ cocone := _
        isColimit := isCoequalizerEpiComp (colimit.isColimit _) h }⟩⟩

variable (C f g)

/-- A coequalizer of an idempotent morphism and the identity is split epi. -/
@[simps]
/--
Definition of `splitEpiOfIdempotentOfIsColimitCofork` / `splitEpiOfIdempotentOfIsColimitCofork` 的定义

English:
definition splitEpiOfIdempotentOfIsColimitCofork
  signature: {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Cofork (𝟙 X) f}
  body: i.desc (Cofork.ofπ f (by simp [hf]))
  id := by
    let := epi_of_isColimit_cofork i
    rw [← cancel_epi_id c.π]; rw [← Category.assoc]; rw [Cofork.IsColimit.π_desc]; rw [Cofork.π_ofπ]; rw [←
      c.condition]
    exact Category.id_comp _

中文:
定义 splitEpiOfIdempotentOfIsColimitCofork
  签名: {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Cofork (𝟙 X) f}
  定义体: i.desc (Cofork.ofπ f (by simp [hf]))
  id := by
    let := epi_of_isColimit_cofork i
    rw [← cancel_epi_id c.π]; rw [← Category.assoc]; rw [Cofork.IsColimit.π_desc]; rw [Cofork.π_ofπ]; rw [←
      c.condition]
    exact Category.id_comp _
-/
def splitEpiOfIdempotentOfIsColimitCofork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Cofork (𝟙 X) f}
    (i : IsColimit c) : SplitEpi c.π where
  section_ := i.desc (Cofork.ofπ f (by simp [hf]))
  id := by
    let := epi_of_isColimit_cofork i
    rw [← cancel_epi_id c.π]; rw [← Category.assoc]; rw [Cofork.IsColimit.π_desc]; rw [Cofork.π_ofπ]; rw [←
      c.condition]
    exact Category.id_comp _

/--
Definition of `splitEpiOfIdempotentCoequalizer` / `splitEpiOfIdempotentCoequalizer` 的定义

English:
definition splitEpiOfIdempotentCoequalizer
  signature: {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
  body: splitEpiOfIdempotentOfIsColimitCofork _ hf (colimit.isColimit _)

中文:
定义 splitEpiOfIdempotentCoequalizer
  签名: {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
  定义体: splitEpiOfIdempotentOfIsColimitCofork _ hf (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isTerminalEquivUnique, isTerminalTensorUnit, splitEpiOfIdempotentOfIsColimitCofork
-/
noncomputable def splitEpiOfIdempotentCoequalizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasCoequalizer (𝟙 X) f] : SplitEpi (coequalizer.π (𝟙 X) f) :=
  splitEpiOfIdempotentOfIsColimitCofork _ hf (colimit.isColimit _)

end CategoryTheory.Limits

end
