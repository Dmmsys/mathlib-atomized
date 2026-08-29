/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# The opposite category of an enriched category

When a monoidal category `V` is braided, we may define the opposite `V`-category of a
`V`-category. The symmetry map is required to define the composition morphism.

This file constructs the opposite `V`-category as an instance on the type `Cᵒᵖ` and constructs an
equivalence between
* `ForgetEnrichment V (Cᵒᵖ)`, the underlying category of the `V`-category `Cᵒᵖ`; and
* `(ForgetEnrichment V C)ᵒᵖ`, the opposite category of the underlying category of `C`.

We also show that if `C` is an enriched ordinary category (i.e. a category enriched in `V`
equipped with an identification `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))`) then `Cᵒᵖ` is again
an enriched ordinary category.

-/

@[expose] public section

universe v₁ u₁ v u

namespace CategoryTheory

open MonoidalCategory BraidedCategory

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]

section

variable (C : Type u) [EnrichedCategory V C]

/--
Instance `EnrichedCategory.opposite` / 实例 `EnrichedCategory.opposite`

English:
instance EnrichedCategory.opposite
  signature: : EnrichedCategory V Cᵒᵖ where
  body: EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left_hom, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right_hom]

中文:
实例 Enriched范畴.opposite
  签名: : Enriched范畴 V Cᵒᵖ where
  定义体: EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left_hom, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right_hom]

Depends on / 依赖: EnrichedCategory, EnrichedCategory.Hom, x.unop, y.unop
-/
instance EnrichedCategory.opposite : EnrichedCategory V Cᵒᵖ where
  Hom y x := EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left_hom, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right_hom]

end

/-- Unfold the definition of composition in the enriched opposite category. -/
@[reassoc]
/--
lemma `eComp_op_eq` / 引理 `eComp_op_eq`

English:
lemma eComp_op_eq
  given: {C : Type u} [EnrichedCategory V C] (x y z : Cᵒᵖ)
  proof: rfl

中文:
引理 eComp_op_eq
  条件: {C : 类型u} [Enriched范畴 V C] (x y z : Cᵒᵖ)
  证明: rfl
-/
lemma eComp_op_eq {C : Type u} [EnrichedCategory V C] (x y z : Cᵒᵖ) :
    eComp V z y x = (β_ _ _).hom ≫ eComp V x.unop y.unop z.unop :=
  rfl

/-- When composing a tensor product of morphisms with the `V`-composition morphism in `Cᵒᵖ`,
this re-writes the `V`-composition to be in `C` and moves the braiding to the left. -/
@[reassoc]
/--
lemma `tensorHom_eComp_op_eq` / 引理 `tensorHom_eComp_op_eq`

English:
lemma tensorHom_eComp_op_eq
  statement: {C : Type u} [EnrichedCategory V C] {x y z : Cᵒᵖ} {v w : V}
  proof: by
  rw [eComp_op_eq]
  exact braiding_naturality_assoc f g _

中文:
引理 tensorHom_eComp_op_eq
  结论: {C : 类型u} [Enriched范畴 V C] {x y z : Cᵒᵖ} {v w : V}
  证明: by
  rw [eComp_op_eq]
  exact braiding_naturality_assoc f g _

Depends on / 依赖: braiding_naturality_assoc, eComp_op_eq
-/
lemma tensorHom_eComp_op_eq {C : Type u} [EnrichedCategory V C] {x y z : Cᵒᵖ} {v w : V}
    (f : v ⟶ EnrichedCategory.Hom z y) (g : w ⟶ EnrichedCategory.Hom y x) :
    (f otimesₘ g) ≫ eComp V z y x = (β_ v w).hom ≫ (g otimesₘ f) ≫ eComp V x.unop y.unop z.unop := by
  rw [eComp_op_eq]
  exact braiding_naturality_assoc f g _

-- This section establishes the equivalence on underlying categories
section

open ForgetEnrichment

variable (C : Type u) [EnrichedCategory V C]

/--
Definition of `forgetEnrichmentOppositeEquivalence.functor` / `forgetEnrichmentOppositeEquivalence.functor` 的定义

English:
definition forgetEnrichmentOppositeEquivalence.functor
  signature: :
  body: x
  map {x y} f := f.op
  map_comp {x y z} f g := by
    have : (f ≫ g) = homTo V (f ≫ g) := rfl
    rw [this]; rw [ForgetEnrichment.homTo_comp]; rw [Category.assoc]; rw [tensorHom_eComp_op_eq]; rw [leftUnitor_inv_braiding_assoc]; rw [← unitors_inv_equal]; rw [← Category.assoc]
    congr 1

中文:
定义 forgetEnrichmentOppositeEquivalence.functor
  签名: :
  定义体: x
  map {x y} f := f.op
  map_comp {x y z} f g := by
    have : (f ≫ g) = homTo V (f ≫ g) := rfl
    rw [this]; rw [ForgetEnrichment.homTo_comp]; rw [Category.assoc]; rw [tensorHom_eComp_op_eq]; rw [leftUnitor_inv_braiding_assoc]; rw [← unitors_inv_equal]; rw [← Category.assoc]
    congr 1
-/
def forgetEnrichmentOppositeEquivalence.functor :
    ForgetEnrichment V Cᵒᵖ ⥤ (ForgetEnrichment V C)ᵒᵖ where
  obj x := x
  map {x y} f := f.op
  map_comp {x y z} f g := by
    have : (f ≫ g) = homTo V (f ≫ g) := rfl
    rw [this]; rw [ForgetEnrichment.homTo_comp]; rw [Category.assoc]; rw [tensorHom_eComp_op_eq]; rw [leftUnitor_inv_braiding_assoc]; rw [← unitors_inv_equal]; rw [← Category.assoc]
    congr 1

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `forgetEnrichmentOppositeEquivalence.inverse` / `forgetEnrichmentOppositeEquivalence.inverse` 的定义

English:
definition forgetEnrichmentOppositeEquivalence.inverse
  signature: :
  body: x
  map {x y} f := f.unop
  map_comp {x y z} f g := by
    have : g.unop ≫ f.unop = homTo V (g.unop ≫ f.unop) := rfl
    dsimp
    rw [this]; rw [ForgetEnrichment.homTo_comp]; rw [Category.assoc]; rw [unitors_inv_equal]; rw [← leftUnitor_inv_braiding_assoc]
    have : (β_ _ _).hom ≫ (homTo V g.unop otimesₘ homTo V f.unop) ≫
      eComp V («to» V z.unop) («to» V y.unop) («to» V x.unop) =
      ((homTo V f.unop) otimesₘ (homTo V g.unop)) ≫ eComp V x y z := (tensorHom_eComp_op_eq V _ _).symm
    rw [this]; rw [← Category.assoc]
    congr 1

中文:
定义 forgetEnrichmentOppositeEquivalence.inverse
  签名: :
  定义体: x
  map {x y} f := f.unop
  map_comp {x y z} f g := by
    have : g.unop ≫ f.unop = homTo V (g.unop ≫ f.unop) := rfl
    dsimp
    rw [this]; rw [ForgetEnrichment.homTo_comp]; rw [Category.assoc]; rw [unitors_inv_equal]; rw [← leftUnitor_inv_braiding_assoc]
    have : (β_ _ _).hom ≫ (homTo V g.unop otimesₘ homTo V f.unop) ≫
      eComp V («to» V z.unop) («to» V y.unop) («to» V x.unop) =
      ((homTo V f.unop) otimesₘ (homTo V g.unop)) ≫ eComp V x y z := (tensorHom_eComp_op_eq V _ _).symm
    rw [this]; rw [← Category.assoc]
    congr 1
-/
def forgetEnrichmentOppositeEquivalence.inverse :
    (ForgetEnrichment V C)ᵒᵖ ⥤ ForgetEnrichment V Cᵒᵖ where
  obj x := x
  map {x y} f := f.unop
  map_comp {x y z} f g := by
    have : g.unop ≫ f.unop = homTo V (g.unop ≫ f.unop) := rfl
    dsimp
    rw [this]; rw [ForgetEnrichment.homTo_comp]; rw [Category.assoc]; rw [unitors_inv_equal]; rw [← leftUnitor_inv_braiding_assoc]
    have : (β_ _ _).hom ≫ (homTo V g.unop otimesₘ homTo V f.unop) ≫
      eComp V («to» V z.unop) («to» V y.unop) («to» V x.unop) =
      ((homTo V f.unop) otimesₘ (homTo V g.unop)) ≫ eComp V x y z := (tensorHom_eComp_op_eq V _ _).symm
    rw [this]; rw [← Category.assoc]
    congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between the underlying category of the enriched category `Cᵒᵖ` and
the opposite of the underlying category of the enriched category `C`. -/
@[simps]
/--
Definition of `forgetEnrichmentOppositeEquivalence` / `forgetEnrichmentOppositeEquivalence` 的定义

English:
definition forgetEnrichmentOppositeEquivalence
  signature: : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnrichment V C)ᵒᵖ where
  body: forgetEnrichmentOppositeEquivalence.functor V C
  inverse := forgetEnrichmentOppositeEquivalence.inverse V C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 forgetEnrichmentOppositeEquivalence
  签名: : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnrichment V C)ᵒᵖ where
  定义体: forgetEnrichmentOppositeEquivalence.functor V C
  inverse := forgetEnrichmentOppositeEquivalence.inverse V C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: forgetEnrichmentOppositeEquivalence, forgetEnrichmentOppositeEquivalence.functor, functor
-/
def forgetEnrichmentOppositeEquivalence : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnrichment V C)ᵒᵖ where
  functor := forgetEnrichmentOppositeEquivalence.functor V C
  inverse := forgetEnrichmentOppositeEquivalence.inverse V C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/--
Instance `EnrichedOrdinaryCategory.opposite` / 实例 `EnrichedOrdinaryCategory.opposite`

English:
instance EnrichedOrdinaryCategory.opposite
  signature: {D : Type u} [Category.{v} D]
  body: Quiver.Hom.opEquiv.symm.trans homEquiv
  homEquiv_id x := homEquiv_id (x.unop)
  homEquiv_comp f g := by
    simp only [tensorHom_eComp_op_eq, leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]
    exact homEquiv_comp g.unop f.unop

中文:
实例 EnrichedOrdinary范畴.opposite
  签名: {D : 类型u} [范畴.{v} D]
  定义体: Quiver.Hom.opEquiv.symm.trans homEquiv
  homEquiv_id x := homEquiv_id (x.unop)
  homEquiv_comp f g := by
    simp only [tensorHom_eComp_op_eq, leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]
    exact homEquiv_comp g.unop f.unop

Depends on / 依赖: Quiver, Quiver.Hom.opEquiv.symm.trans, homEquiv, opEquiv
-/
instance EnrichedOrdinaryCategory.opposite {D : Type u} [Category.{v} D]
    [EnrichedOrdinaryCategory V D] : EnrichedOrdinaryCategory V Dᵒᵖ where
  homEquiv := Quiver.Hom.opEquiv.symm.trans homEquiv
  homEquiv_id x := homEquiv_id (x.unop)
  homEquiv_comp f g := by
    simp only [tensorHom_eComp_op_eq, leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]
    exact homEquiv_comp g.unop f.unop

end

end CategoryTheory
