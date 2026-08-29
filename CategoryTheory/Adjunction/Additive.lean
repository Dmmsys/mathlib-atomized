/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Adjunctions between additive functors.

This provides some results and constructions for adjunctions between functors on
preadditive categories:
* If one of the adjoint functors is additive, so is the other.
* If one of the adjoint functors is additive, the equivalence `Adjunction.homEquiv` lifts to
  an additive equivalence `Adjunction.homAddEquiv`.
* We also give a version of this additive equivalence as an isomorphism of `preadditiveYoneda`
  functors (analogous to `Adjunction.compYonedaIso`), in `Adjunction.compPreadditiveYonedaIso`.

-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open CategoryTheory Category CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

/--
lemma `right_adjoint_additive` / 引理 `right_adjoint_additive`

English:
lemma right_adjoint_additive
  given: [F.Additive]
  statement: G.Additive where
  proof: (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

中文:
引理 right_adjoint_additive
  条件: [F.Additive]
  结论: G.Additive where
  证明: (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

Depends on / 依赖: adj.homEquiv, homEquiv, homEquiv_counit, injective, symm.injective
-/
lemma right_adjoint_additive [F.Additive] : G.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

set_option backward.defeqAttrib.useBackward true in
/--
lemma `left_adjoint_additive` / 引理 `left_adjoint_additive`

English:
lemma left_adjoint_additive
  given: [G.Additive]
  statement: F.Additive where
  proof: (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

中文:
引理 left_adjoint_additive
  条件: [G.Additive]
  结论: F.Additive where
  证明: (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

Depends on / 依赖: adj.homEquiv, homEquiv, homEquiv_unit, injective
-/
lemma left_adjoint_additive [G.Additive] : F.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

variable [F.Additive]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `homAddEquiv` / `homAddEquiv` 的定义

English:
definition homAddEquiv
  signature: (X : C) (Y : D)
  body: { adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }

@[simp]

中文:
定义 homAddEquiv
  签名: (X : C) (Y : D)
  定义体: { adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }

@[simp]

Depends on / 依赖: adj.homEquiv, adj.right_adjoint_additive, homEquiv, homEquiv_apply, map_add, right_adjoint_additive
-/
def homAddEquiv (X : C) (Y : D) : AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  { adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }

@[simp]
/--
lemma `homAddEquiv_apply` / 引理 `homAddEquiv_apply`

English:
lemma homAddEquiv_apply
  given: (X : C) (Y : D) (f : F.obj X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 homAddEquiv_apply
  条件: (X : C) (Y : D) (f : F.obj X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma homAddEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homAddEquiv X Y f = adj.homEquiv X Y f := rfl

@[simp]
/--
lemma `homAddEquiv_symm_apply` / 引理 `homAddEquiv_symm_apply`

English:
lemma homAddEquiv_symm_apply
  given: (X : C) (Y : D) (f : X ⟶ G.obj Y)
  proof: rfl

@[simp]

中文:
引理 homAddEquiv_symm_apply
  条件: (X : C) (Y : D) (f : X ⟶ G.obj Y)
  证明: rfl

@[simp]
-/
lemma homAddEquiv_symm_apply (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv X Y).symm f = (adj.homEquiv X Y).symm f := rfl

@[simp]
/--
lemma `homAddEquiv_zero` / 引理 `homAddEquiv_zero`

English:
lemma homAddEquiv_zero
  given: (X : C) (Y : D)
  statement: adj.homEquiv X Y 0 = 0
  proof: map_zero (adj.homAddEquiv X Y)

@[simp]

中文:
引理 homAddEquiv_zero
  条件: (X : C) (Y : D)
  结论: adj.homEquiv X Y 0 = 0
  证明: map_zero (adj.homAddEquiv X Y)

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_zero
-/
lemma homAddEquiv_zero (X : C) (Y : D) : adj.homEquiv X Y 0 = 0 := map_zero (adj.homAddEquiv X Y)

@[simp]
/--
lemma `homAddEquiv_add` / 引理 `homAddEquiv_add`

English:
lemma homAddEquiv_add
  given: (X : C) (Y : D) (f f' : F.obj X ⟶ Y)
  proof: map_add (adj.homAddEquiv X Y) _ _

@[simp]

中文:
引理 homAddEquiv_add
  条件: (X : C) (Y : D) (f f' : F.obj X ⟶ Y)
  证明: map_add (adj.homAddEquiv X Y) _ _

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_add
-/
lemma homAddEquiv_add (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f + f') = adj.homEquiv X Y f + adj.homEquiv X Y f' :=
  map_add (adj.homAddEquiv X Y) _ _

@[simp]
/--
lemma `homAddEquiv_sub` / 引理 `homAddEquiv_sub`

English:
lemma homAddEquiv_sub
  given: (X : C) (Y : D) (f f' : F.obj X ⟶ Y)
  proof: map_sub (adj.homAddEquiv X Y) _ _

@[simp]

中文:
引理 homAddEquiv_sub
  条件: (X : C) (Y : D) (f f' : F.obj X ⟶ Y)
  证明: map_sub (adj.homAddEquiv X Y) _ _

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_sub
-/
lemma homAddEquiv_sub (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f - f') = adj.homEquiv X Y f - adj.homEquiv X Y f' :=
  map_sub (adj.homAddEquiv X Y) _ _

@[simp]
/--
lemma `homAddEquiv_neg` / 引理 `homAddEquiv_neg`

English:
lemma homAddEquiv_neg
  given: (X : C) (Y : D) (f : F.obj X ⟶ Y)
  proof: map_neg (adj.homAddEquiv X Y) _

@[simp]

中文:
引理 homAddEquiv_neg
  条件: (X : C) (Y : D) (f : F.obj X ⟶ Y)
  证明: map_neg (adj.homAddEquiv X Y) _

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_neg
-/
lemma homAddEquiv_neg (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homEquiv X Y (-f) = - adj.homEquiv X Y f := map_neg (adj.homAddEquiv X Y) _

@[simp]
/--
lemma `homAddEquiv_symm_zero` / 引理 `homAddEquiv_symm_zero`

English:
lemma homAddEquiv_symm_zero
  given: (X : C) (Y : D)
  proof: map_zero (adj.homAddEquiv X Y).symm

@[simp]

中文:
引理 homAddEquiv_symm_zero
  条件: (X : C) (Y : D)
  证明: map_zero (adj.homAddEquiv X Y).symm

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_zero
-/
lemma homAddEquiv_symm_zero (X : C) (Y : D) :
    (adj.homEquiv X Y).symm 0 = 0 := map_zero (adj.homAddEquiv X Y).symm

@[simp]
/--
lemma `homAddEquiv_symm_add` / 引理 `homAddEquiv_symm_add`

English:
lemma homAddEquiv_symm_add
  given: (X : C) (Y : D) (f f' : X ⟶ G.obj Y)
  proof: map_add (adj.homAddEquiv X Y).symm _ _

@[simp]

中文:
引理 homAddEquiv_symm_add
  条件: (X : C) (Y : D) (f f' : X ⟶ G.obj Y)
  证明: map_add (adj.homAddEquiv X Y).symm _ _

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_add
-/
lemma homAddEquiv_symm_add (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f + f') = (adj.homEquiv X Y).symm f + (adj.homEquiv X Y).symm f' :=
  map_add (adj.homAddEquiv X Y).symm _ _

@[simp]
/--
lemma `homAddEquiv_symm_sub` / 引理 `homAddEquiv_symm_sub`

English:
lemma homAddEquiv_symm_sub
  given: (X : C) (Y : D) (f f' : X ⟶ G.obj Y)
  proof: map_sub (adj.homAddEquiv X Y).symm _ _

@[simp]

中文:
引理 homAddEquiv_symm_sub
  条件: (X : C) (Y : D) (f f' : X ⟶ G.obj Y)
  证明: map_sub (adj.homAddEquiv X Y).symm _ _

@[simp]

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_sub
-/
lemma homAddEquiv_symm_sub (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f - f') = (adj.homEquiv X Y).symm f - (adj.homEquiv X Y).symm f' :=
  map_sub (adj.homAddEquiv X Y).symm _ _

@[simp]
/--
lemma `homAddEquiv_symm_neg` / 引理 `homAddEquiv_symm_neg`

English:
lemma homAddEquiv_symm_neg
  given: (X : C) (Y : D) (f : X ⟶ G.obj Y)
  proof: map_neg (adj.homAddEquiv X Y).symm _

中文:
引理 homAddEquiv_symm_neg
  条件: (X : C) (Y : D) (f : X ⟶ G.obj Y)
  证明: map_neg (adj.homAddEquiv X Y).symm _

Depends on / 依赖: adj.homAddEquiv, homAddEquiv, map_neg
-/
lemma homAddEquiv_symm_neg (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (-f) = - (adj.homEquiv X Y).symm f :=
  map_neg (adj.homAddEquiv X Y).symm _

open Opposite in
/--
Definition of `compPreadditiveYonedaIso` / `compPreadditiveYonedaIso` 的定义

English:
definition compPreadditiveYonedaIso
  signature: :
  body: NatIso.ofComponents
    (fun Y => NatIso.ofComponents
      (fun X => (AddEquiv.ulift.trans ((adj.homAddEquiv (unop X) Y).symm.trans
        AddEquiv.ulift.symm)).toAddCommGrpIso)
      (fun g => by
        ext ⟨y⟩
        exact AddEquiv.ulift.injective (adj.homEquiv_naturality_left_symm g.unop y)))

中文:
定义 compPreadditiveYonedaIso
  签名: :
  定义体: NatIso.ofComponents
    (fun Y => NatIso.ofComponents
      (fun X => (AddEquiv.ulift.trans ((adj.homAddEquiv (unop X) Y).symm.trans
        AddEquiv.ulift.symm)).toAddCommGrpIso)
      (fun g => by
        ext ⟨y⟩
        exact AddEquiv.ulift.injective (adj.homEquiv_naturality_left_symm g.unop y)))

Depends on / 依赖: AddEquiv, AddEquiv.ulift.injective, AddEquiv.ulift.symm, AddEquiv.ulift.trans, NatIso, NatIso.ofComponents, adj.homAddEquiv, adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm, g.unop, homAddEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, injective, ofComponents, symm.trans, toAddCommGrpIso
-/
def compPreadditiveYonedaIso :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} ≅
      preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
        (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} :=
  NatIso.ofComponents
    (fun Y => NatIso.ofComponents
      (fun X => (AddEquiv.ulift.trans ((adj.homAddEquiv (unop X) Y).symm.trans
        AddEquiv.ulift.symm)).toAddCommGrpIso)
      (fun g => by
        ext ⟨y⟩
        exact AddEquiv.ulift.injective (adj.homEquiv_naturality_left_symm g.unop y)))
    (fun f => by
      ext _ ⟨x⟩
      exact AddEquiv.ulift.injective ((adj.homEquiv_naturality_right_symm x f)))

/--
lemma `compPreadditiveYonedaIso_hom_app_app_apply` / 引理 `compPreadditiveYonedaIso_hom_app_app_apply`

English:
lemma compPreadditiveYonedaIso_hom_app_app_apply
  statement: (X : Cᵒᵖ) (Y : D)
  proof: rfl

中文:
引理 compPreadditiveYonedaIso_hom_app_app_apply
  结论: (X : Cᵒᵖ) (Y : D)
  证明: rfl
-/
lemma compPreadditiveYonedaIso_hom_app_app_apply (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₁} (Opposite.unop X ⟶ G.obj Y)) :
      ((adj.compPreadditiveYonedaIso.hom.app Y).app X) a =
        ULift.up ((adj.homEquiv (Opposite.unop X) Y).symm (AddEquiv.ulift a)) := rfl

/--
lemma `compPreadditiveYonedaIso_inv_app_app_apply` / 引理 `compPreadditiveYonedaIso_inv_app_app_apply`

English:
lemma compPreadditiveYonedaIso_inv_app_app_apply
  statement: (X : Cᵒᵖ) (Y : D)
  proof: rfl

中文:
引理 compPreadditiveYonedaIso_inv_app_app_apply
  结论: (X : Cᵒᵖ) (Y : D)
  证明: rfl
-/
lemma compPreadditiveYonedaIso_inv_app_app_apply (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₂} (F.obj (Opposite.unop X) ⟶ Y)) :
      ((adj.compPreadditiveYonedaIso.inv.app Y).app X) a =
        ULift.up ((adj.homEquiv (Opposite.unop X) Y) (AddEquiv.ulift a)) := rfl

end Adjunction

end CategoryTheory
