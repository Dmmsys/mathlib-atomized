/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Monoidal category structure on categories of sheaves

If `A` is a closed braided category with suitable limits,
and `J` is a Grothendieck topology with `HasWeakSheafify J A`,
then `Sheaf J A` can be equipped with a monoidal category
structure. This is not made an instance as in some cases
it may conflict with monoidal structure deduced from
chosen finite products.

## TODO

* show that the monoidal category structure on sheaves is closed,
  and that the internal hom can be defined in such a way that the
  underlying presheaf is the internal hom in the category of presheaves.
  Note that a `MonoidalClosed` instance on sheaves can already be obtained
  abstractly using the material in `CategoryTheory.Monoidal.Braided.Reflection`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A]

open Opposite Limits MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Presheaf

variable [MonoidalClosed A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorEnrichedHomCoyonedaObjEquiv` / `functorEnrichedHomCoyonedaObjEquiv` 的定义

English:
definition functorEnrichedHomCoyonedaObjEquiv
  signature: (M : A) (F G : Cᵒᵖ ⥤ A)
  body: { app j := MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality j j' φ := by
        dsimp
        rw [tensorHom_id]; rw [← uncurry_natural_right]; rw [← uncurry_pre_app]; rw [Category.assoc]; rw [Category.assoc]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRig

中文:
定义 functorEnrichedHomCoyonedaObjEquiv
  签名: (M : A) (F G : Cᵒᵖ ⥤ A)
  定义体: { app j := MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality j j' φ := by
        dsimp
        rw [tensorHom_id]; rw [← uncurry_natural_right]; rw [← uncurry_pre_app]; rw [Category.assoc]; rw [Category.assoc]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRig

Depends on / 依赖: Category, Category.assoc, MonoidalClosed, MonoidalClosed.uncurry, Under.forget, Under.homMk, Under.mk, enrichedHom_condition, enrichedOrdinaryCategorySelf_eHomWhiskerLeft, enrichedOrdinaryCategorySelf_eHomWhiskerRight, forget, j.unop.hom.op, naturality, tensorHom_id, uncurry, uncurry_natural_right, uncurry_pre_app, unop.hom.op
-/
noncomputable def functorEnrichedHomCoyonedaObjEquiv (M : A) (F G : Cᵒᵖ ⥤ A)
    [HasFunctorEnrichedHom A F G] (X : C) :
    (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op X) ≃
    (presheafHom (F otimes (Functor.const _).obj M) G).obj (op X) where
  toFun f :=
    { app j := MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality j j' φ := by
        dsimp
        rw [tensorHom_id]; rw [← uncurry_natural_right]; rw [← uncurry_pre_app]; rw [Category.assoc]; rw [Category.assoc]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        congr 2
        exact (enrichedHom_condition A (Under.forget (op X) ⋙ F) (Under.forget (op X) ⋙ G)
          (i := Under.mk j.unop.hom.op) (j := Under.mk j'.unop.hom.op)
            (Under.homMk φ.unop.left.op (Quiver.Hom.unop_inj (by simp)))).symm }
  invFun g :=
    end_.lift (fun j => MonoidalClosed.curry (g.app (op (Over.mk j.hom.unop)))) (fun j j' φ => by
      dsimp
      rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]; rw [curry_pre_app]; rw [← curry_natural_right]
      congr 1
      let α : Over.mk j'.hom.unop ⟶ Over.mk j.hom.unop := Over.homMk φ.right.unop
        (Quiver.Hom.op_inj (by simp))
      simpa using! (g.naturality α.op).symm)
  left_inv f := by
    dsimp
    ext j
    dsimp
    simp only [curry_uncurry, end_.lift_π]
    rfl
  right_inv g := by
    dsimp
    ext j
    dsimp
    simp only [uncurry_curry, end_.lift_π]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorEnrichedHomCoyonedaObjEquiv_naturality` / 引理 `functorEnrichedHomCoyonedaObjEquiv_naturality`

English:
lemma functorEnrichedHomCoyonedaObjEquiv_naturality
  proof: by
  dsimp
  ext ⟨j⟩
  simp [functorEnrichedHomCoyonedaObjEquiv, presheafHom]
  rfl

中文:
引理 functorEnrichedHomCoyonedaObjEquiv_naturality
  证明: by
  dsimp
  ext ⟨j⟩
  simp [functorEnrichedHomCoyonedaObjEquiv, presheafHom]
  rfl

Depends on / 依赖: functorEnrichedHomCoyonedaObjEquiv, presheafHom
-/
lemma functorEnrichedHomCoyonedaObjEquiv_naturality
    {M : A} {F G : Cᵒᵖ ⥤ A} {X Y : C} (f : X ⟶ Y)
    [HasFunctorEnrichedHom A F G]
    (y : (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op Y)) :
    functorEnrichedHomCoyonedaObjEquiv M F G X
      (y ≫ precompEnrichedHom' _ (Under.map f.op) (Iso.refl _) (Iso.refl _)) =
    (presheafHom (F otimes (Functor.const Cᵒᵖ).obj M) G).map f.op
      (functorEnrichedHomCoyonedaObjEquiv M F G Y y) := by
  dsimp
  ext ⟨j⟩
  simp [functorEnrichedHomCoyonedaObjEquiv, presheafHom]
  rfl

/--
lemma `isSheaf_functorEnrichedHom` / 引理 `isSheaf_functorEnrichedHom`

English:
lemma isSheaf_functorEnrichedHom
  statement: (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
  proof: fun M => by
  rw [Presieve.isSheaf_iff_of_nat_equiv
    (functorEnrichedHomCoyonedaObjEquiv M F G)
    (fun _ _ _ _ => functorEnrichedHomCoyonedaObjEquiv_naturality _ _)]
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom (F otimes (Functor.const _).obj M) G hG

中文:
引理 isSheaf_functorEnrichedHom
  结论: (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
  证明: fun M => by
  rw [Presieve.isSheaf_iff_of_nat_equiv
    (functorEnrichedHomCoyonedaObjEquiv M F G)
    (fun _ _ _ _ => functorEnrichedHomCoyonedaObjEquiv_naturality _ _)]
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom (F otimes (Functor.const _).obj M) G hG

Depends on / 依赖: Functor, Functor.const, IsSheaf, Presheaf, Presheaf.IsSheaf.hom, Presieve, Presieve.isSheaf_iff_of_nat_equiv, functorEnrichedHomCoyonedaObjEquiv, functorEnrichedHomCoyonedaObjEquiv_naturality, isSheaf_iff_isSheaf_of_type, isSheaf_iff_of_nat_equiv, otimes
-/
lemma isSheaf_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
    [HasFunctorEnrichedHom A F G] :
    Presheaf.IsSheaf J (functorEnrichedHom A F G) := fun M => by
  rw [Presieve.isSheaf_iff_of_nat_equiv
    (functorEnrichedHomCoyonedaObjEquiv M F G)
    (fun _ _ _ _ => functorEnrichedHomCoyonedaObjEquiv_naturality _ _)]
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom (F otimes (Functor.const _).obj M) G hG

end Presheaf

namespace GrothendieckTopology

namespace W

variable (J A) in
/--
lemma `transport_isMonoidal` / 引理 `transport_isMonoidal`

English:
lemma transport_isMonoidal
  statement: {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
  proof: by
  rw [← J.W_inverseImage_whiskeringLeft K G]
  infer_instance

中文:
引理 transport_isMonoidal
  结论: {D : 类型u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
  证明: by
  rw [← J.W_inverseImage_whiskeringLeft K G]
  infer_instance

Depends on / 依赖: IsMonoidal
-/
lemma transport_isMonoidal {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
    (G : D ⥤ C) [G.IsCoverDense J] [G.Full] [G.IsContinuous K J]
    [(G.sheafPushforwardContinuous A K J).EssSurj] [(K.W (A := A)).IsMonoidal] :
    (J.W (A := A)).IsMonoidal := by
  rw [← J.W_inverseImage_whiskeringLeft K G]
  infer_instance

variable [MonoidalClosed A]
  [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

open MonoidalClosed.FunctorCategory

set_option backward.isDefEq.respectTransparency false in
/--
lemma `whiskerLeft` / 引理 `whiskerLeft`

English:
lemma whiskerLeft
  given: {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A)
  proof: fun H h => by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).b

中文:
引理 whiskerLeft
  条件: {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A)
  证明: fun H h => by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).b

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, MonoidalClosed, MonoidalClosed.curry, Presheaf, Presheaf.isSheaf_functorEnrichedHom, adjunction, bijective, convert, curry_natural_left, homEquiv, ihom.adjunction, isSheaf_functorEnrichedHom, of_comp_iff
-/
lemma whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) :
    J.W (F ◁ g) := fun H h => by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).bijective] at this
  convert! this using 1
  ext α : 1
  dsimp
  rw [curry_natural_left]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `whiskerRight` / 引理 `whiskerRight`

English:
lemma whiskerRight
  statement: [BraidedCategory A]
  proof: (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)

中文:
引理 whiskerRight
  结论: [BraidedCategory A]
  证明: (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)

Depends on / 依赖: Arrow.isoMk, J.W.arrow_mk_iso_iff, arrow_mk_iso_iff, hf.whiskerLeft, whiskerLeft
-/
lemma whiskerRight [BraidedCategory A]
    {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W f) (G : Cᵒᵖ ⥤ A) :
    J.W (f ▷ G) :=
  (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)

/--
Instance `monoidal` / 实例 `monoidal`

English:
instance monoidal
  signature: [BraidedCategory A]
  body: hg.whiskerLeft F
  whiskerRight _ hf G := hf.whiskerRight G

中文:
实例 monoidal
  签名: [BraidedCategory A]
  定义体: hg.whiskerLeft F
  whiskerRight _ hf G := hf.whiskerRight G

Depends on / 依赖: IsMonoidal
-/
instance monoidal [BraidedCategory A] : (J.W (A := A)).IsMonoidal where
  whiskerLeft F _ _ _ hg := hg.whiskerLeft F
  whiskerRight _ hf G := hf.whiskerRight G

end W

end GrothendieckTopology

namespace Sheaf

variable (J A)

/-- The monoidal category structure on `Sheaf J A` that is obtained
by localization of the monoidal category structure on the category
of presheaves. -/
@[instance_reducible]
/--
Definition of `monoidalCategory` / `monoidalCategory` 的定义

English:
definition monoidalCategory
  signature: [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  body: inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

中文:
定义 monoidalCategory
  签名: [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  定义体: inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

Depends on / 依赖: HasWeakSheafify, IsMonoidal
-/
noncomputable def monoidalCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    MonoidalCategory (Sheaf J A) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

attribute [local instance] monoidalCategory

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory` is
braided when `A` is braided. -/
@[instance_reducible]
/--
Definition of `braidedCategory` / `braidedCategory` 的定义

English:
definition braidedCategory
  signature: [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  body: inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

中文:
定义 braidedCategory
  签名: [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  定义体: inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

Depends on / 依赖: HasWeakSheafify, IsMonoidal
-/
noncomputable def braidedCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [BraidedCategory A] : BraidedCategory (Sheaf J A) :=
  inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory` is
symmetric when `A` is symmetric. -/
@[instance_reducible]
/--
Definition of `symmetricCategory` / `symmetricCategory` 的定义

English:
definition symmetricCategory
  signature: [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  body: inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

中文:
定义 symmetricCategory
  签名: [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  定义体: inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

Depends on / 依赖: HasWeakSheafify, IsMonoidal
-/
noncomputable def symmetricCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [SymmetricCategory A] :
    SymmetricCategory (Sheaf J A) :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(J.W
  signature: (A := A)).IsMonoidal] [HasWeakSheafify J A] :
  body: inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Monoidal

中文:
实例 [(J.W
  签名: (A := A)).IsMonoidal] [HasWeakSheafify J A] :
  定义体: inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Monoidal

Depends on / 依赖: HasWeakSheafify, IsMonoidal
-/
noncomputable instance [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    (presheafToSheaf J A).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Monoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(J.W
  signature: (A := A)).IsMonoidal] [HasWeakSheafify J A] [BraidedCategory A] :
  body: braidedCategory J A
    (presheafToSheaf J A).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Braided

noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), 

中文:
实例 [(J.W
  签名: (A := A)).IsMonoidal] [HasWeakSheafify J A] [BraidedCategory A] :
  定义体: braidedCategory J A
    (presheafToSheaf J A).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Braided

noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), 

Depends on / 依赖: BraidedCategory, HasWeakSheafify, IsMonoidal
-/
noncomputable instance [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [BraidedCategory A] :
    letI := braidedCategory J A
    (presheafToSheaf J A).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Braided

noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    MonoidalCategory (Sheaf J A) :=
  monoidalCategory J A

noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    BraidedCategory (Sheaf J A) :=
  braidedCategory J A

noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [SymmetricCategory A]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [forall (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    SymmetricCategory (Sheaf J A) :=
  symmetricCategory J A

end Sheaf

end CategoryTheory
