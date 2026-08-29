/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Subobject.Classifier.Defs
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!

# (Elementary) Sheaf Topos

We define a subobject classifier for categories of sheaves of (large enough) types.

## Main definitions

Let `C` refer to a category with (when relevant) Grothendieck topology `J`.

* `Presheaf.classifier C` is a construction of a subobject classifier in `Cᵒᵖ ⥤ Type (max u v)`.
* `Sheaf.classifier J` is a construction of a subobject classifier in `Sheaf J (Type (max u v))`.
* `inferInstance : HasClassifier (Cᵒᵖ ⥤ Type w)` says that `Cᵒᵖ ⥤ Type w` has a subobject
  classifier if `C` is `w`-essentially small.
* `inferInstance : HasClassifier (Sheaf J (Type w))` says that `Sheaf J (Type w)` has a
  subobject classifier if `C` is `w`-essentially small.

## Main results

* Any category of sheaves of types has a subobject classifier if the site is essentially small.
* As a consequence, (because categories of sheaves are cartesian monoidal and have finite limits,)
  such categories are Elementary Topoi.

## TODOS:

* generalize `Presheaf.isClosed_χ_app_apply_of` to only assuming `G` is separated

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
open Limits

section presheaf

variable (C) in
/-- The truth morphism in the category of presheaves. At each component `X : C`, it is the constant
map returning `⊤ : Sieve X`. -/
@[simps]
/--
Definition of `Presheaf.truth` / `Presheaf.truth` 的定义

English:
definition Presheaf.truth
  signature: : (Functor.const _).obj PUnit ⟶ Functor.sieves C where
  body: ↾fun _ => (⊤ : Sieve X.unop)

中文:
定义 Presheaf.truth
  签名: : (Functor.const _).obj PUnit ⟶ Functor.sieves C where
  定义体: ↾fun _ => (⊤ : Sieve X.unop)

Depends on / 依赖: X.unop
-/
def Presheaf.truth : (Functor.const _).obj PUnit ⟶ Functor.sieves C where
  app X := ↾fun _ => (⊤ : Sieve X.unop)

variable {F G : Cᵒᵖ ⥤ Type (max u v)}

set_option backward.defeqAttrib.useBackward true in
/--
The characteristic map of an inclusion of presheaves.
Given a monomorphism of sheaves `m : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  `∃ a ∈ F(Y), G(f)(x) = m_Y(a)`
-/
@[simps app]
/--
Definition of `Presheaf.χ` / `Presheaf.χ` 的定义

English:
definition Presheaf.χ
  signature: (m : F ⟶ G)
  body: ↾fun x => ⟨fun Y f => exists a, G.map f.op x = m.app (.op Y) a, by
    intro Y Z f ⟨a, ha⟩ g
    use F.map g.op a
    simp [ha, NatTrans.naturality_apply]⟩

中文:
定义 Presheaf.χ
  签名: (m : F ⟶ G)
  定义体: ↾fun x => ⟨fun Y f => exists a, G.map f.op x = m.app (.op Y) a, by
    intro Y Z f ⟨a, ha⟩ g
    use F.map g.op a
    simp [ha, NatTrans.naturality_apply]⟩

Depends on / 依赖: F.map, G.map, NatTrans, NatTrans.naturality_apply, f.op, g.op, m.app, naturality_apply
-/
def Presheaf.χ (m : F ⟶ G) : G ⟶ Functor.sieves C where
  app X := ↾fun x => ⟨fun Y f => exists a, G.map f.op x = m.app (.op Y) a, by
    intro Y Z f ⟨a, ha⟩ g
    use F.map g.op a
    simp [ha, NatTrans.naturality_apply]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Presheaf.comp_χ_eq` / 引理 `Presheaf.comp_χ_eq`

English:
lemma Presheaf.comp_χ_eq
  given: (m : F ⟶ G)
  statement: m ≫ Presheaf.χ m =
  proof: by
  ext
  apply Sieve.ext
  simp [← NatTrans.naturality_apply]

中文:
引理 Presheaf.comp_χ_eq
  条件: (m : F ⟶ G)
  结论: m ≫ Presheaf.χ m =
  证明: by
  ext
  apply Sieve.ext
  simp [← NatTrans.naturality_apply]

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, Sieve.ext, naturality_apply
-/
lemma Presheaf.comp_χ_eq (m : F ⟶ G) : m ≫ Presheaf.χ m =
    (Functor.isTerminalConst _ Types.isTerminalPUnit).from F ≫ Presheaf.truth C := by
  ext
  apply Sieve.ext
  simp [← NatTrans.naturality_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Presheaf.isPullback_χ_truth` / 引理 `Presheaf.isPullback_χ_truth`

English:
lemma Presheaf.isPullback_χ_truth
  given: (m : F ⟶ G) [Mono m]
  proof: by
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr(($(comp_χ_eq m)).app X), ?_, ?_⟩
  · simpa using! (mono_iff_injective (m.app X)).mp (inferInstance)
  · simp only [Functor.const_obj_obj, Functor.sieves_obj, χ_app, Opposite.op_unop,
      TypeCat

中文:
引理 Presheaf.isPullback_χ_truth
  条件: (m : F ⟶ G) [Mono m]
  证明: by
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr(($(comp_χ_eq m)).app X), ?_, ?_⟩
  · simpa using! (mono_iff_injective (m.app X)).mp (inferInstance)
  · simp only [Functor.const_obj_obj, Functor.sieves_obj, χ_app, Opposite.op_unop,
      TypeCat

Depends on / 依赖: Functor, Functor.const_obj_obj, Functor.isTerminalConst_from_app, Functor.sieves_obj, IsPullback, IsPullback.of_forall_isPullback_app, Opposite, Opposite.op_unop, TypeCat, TypeCat.Fun.coe_mk, TypeCat.hom_ofHom, Types.isPullback_iff, Types.isTerminalPUnit_from_apply, and_true, arrows, coe_mk, const_obj_obj, eq_comm, forall_const, hom_ofHom
-/
lemma Presheaf.isPullback_χ_truth (m : F ⟶ G) [Mono m] :
    IsPullback m ((Functor.isTerminalConst _ Types.isTerminalPUnit).from F) (χ m) (truth C) := by
  refine IsPullback.of_forall_isPullback_app fun X => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr(($(comp_χ_eq m)).app X), ?_, ?_⟩
  · simpa using! (mono_iff_injective (m.app X)).mp (inferInstance)
  · simp only [Functor.const_obj_obj, Functor.sieves_obj, χ_app, Opposite.op_unop,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, truth_app, Functor.isTerminalConst_from_app,
      Types.isTerminalPUnit_from_apply, and_true, forall_const]
    intro p hp
    simpa [eq_comm] using! congr($(hp).arrows (𝟙 _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Presheaf.χ_unique` / 引理 `Presheaf.χ_unique`

English:
lemma Presheaf.χ_unique
  statement: (m : F ⟶ G) (χ' : G ⟶ Functor.sieves C)
  proof: by
  ext X x
  simp only [IsPullback.iff_app, Functor.const_obj_obj, Functor.sieves_obj,
    Functor.isTerminalConst_from_app, truth_app, Types.isPullback_iff,
    Types.isTerminalPUnit_from_apply, and_true, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    forall_const, forall_and] at hχ'
  obtain ⟨h₁, h₂

中文:
引理 Presheaf.χ_unique
  结论: (m : F ⟶ G) (χ' : G ⟶ Functor.sieves C)
  证明: by
  ext X x
  simp only [IsPullback.iff_app, Functor.const_obj_obj, Functor.sieves_obj,
    Functor.isTerminalConst_from_app, truth_app, Types.isPullback_iff,
    Types.isTerminalPUnit_from_apply, and_true, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    forall_const, forall_and] at hχ'
  obtain ⟨h₁, h₂

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Functor, Functor.const_obj_obj, Functor.isTerminalConst_from_app, Functor.sieves_map, Functor.sieves_obj, IsPullback, IsPullback.iff_app, Opposite, Opposite.op_unop, Quiver, Quiver.Hom.unop_op, Sieve.ext, Sieve.mem_iff_pullback_eq_top, TypeCat, TypeCat.Fun.coe_mk, TypeCat.hom_ofHom, Types.isPullback_iff, Types.isTerminalPUnit_from_apply
-/
lemma Presheaf.χ_unique (m : F ⟶ G) (χ' : G ⟶ Functor.sieves C)
    (hχ' : IsPullback m ((Functor.isTerminalConst _ Types.isTerminalPUnit).from _) χ' (truth C)) :
    χ' = χ m := by
  ext X x
  simp only [IsPullback.iff_app, Functor.const_obj_obj, Functor.sieves_obj,
    Functor.isTerminalConst_from_app, truth_app, Types.isPullback_iff,
    Types.isTerminalPUnit_from_apply, and_true, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    forall_const, forall_and] at hχ'
  obtain ⟨h₁, h₂, h₃⟩ := hχ'
  refine Sieve.ext fun Y f => ?_
  simp only [χ_app, Opposite.op_unop]
  rw [Sieve.mem_iff_pullback_eq_top]; rw [← Quiver.Hom.unop_op f]
  dsimp
  have := ConcreteCategory.congr_hom (Functor.sieves_map C (f.op)) (χ'.app X x)
  rw [← dsimp% this]; rw [← dsimp% NatTrans.naturality_apply χ' f.op x]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h₃ _ _ h
    use z, hz.symm
  · rintro ⟨a, h⟩
    rw [h]
    simpa using congr($(h₁ (.op Y)) a)

variable (C) in
/-- A construction of a subject classifier in a category of presheaves. -/
@[simps! Ω truth Ω₀ χ χ₀]
/--
Definition of `Presheaf.classifier` / `Presheaf.classifier` 的定义

English:
definition Presheaf.classifier
  signature: : Subobject.Classifier (Cᵒᵖ ⥤ Type (max u v))
  body: .mkOfTerminalΩ₀ ((Functor.const Cᵒᵖ).obj PUnit)
    (Functor.isTerminalConst _ (Types.isTerminalPUnit)) (Functor.sieves C) (Presheaf.truth C)
    (Presheaf.χ ·) Presheaf.isPullback_χ_truth (Presheaf.χ_unique ·)

中文:
定义 Presheaf.classifier
  签名: : Subobject.Classifier (Cᵒᵖ ⥤ Type (max u v))
  定义体: .mkOfTerminalΩ₀ ((Functor.const Cᵒᵖ).obj PUnit)
    (Functor.isTerminalConst _ (Types.isTerminalPUnit)) (Functor.sieves C) (Presheaf.truth C)
    (Presheaf.χ ·) Presheaf.isPullback_χ_truth (Presheaf.χ_unique ·)

Depends on / 依赖: Functor, Functor.const, Functor.isTerminalConst, Functor.sieves, Presheaf, Presheaf.isPullback_, Presheaf.truth, Types.isTerminalPUnit, isTerminalConst, isTerminalPUnit, sieves
-/
def Presheaf.classifier : Subobject.Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  .mkOfTerminalΩ₀ ((Functor.const Cᵒᵖ).obj PUnit)
    (Functor.isTerminalConst _ (Types.isTerminalPUnit)) (Functor.sieves C) (Presheaf.truth C)
    (Presheaf.χ ·) Presheaf.isPullback_χ_truth (Presheaf.χ_unique ·)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssentiallySmall.{w}
  signature: C] : HasSubobjectClassifier (Cᵒᵖ ⥤ Type w) where
  body: ⟨(Presheaf.classifier (SmallModel C)).ofEquivalence
    (Equivalence.congrLeft (E := Type w) (equivSmallModel C).op).symm⟩

中文:
实例 [EssentiallySmall.{w}
  签名: C] : HasSubobjectClassifier (Cᵒᵖ ⥤ Type w) where
  定义体: ⟨(Presheaf.classifier (SmallModel C)).ofEquivalence
    (Equivalence.congrLeft (E := Type w) (equivSmallModel C).op).symm⟩

Depends on / 依赖: Presheaf, Presheaf.classifier, SmallModel, classifier, ofEquivalence
-/
instance [EssentiallySmall.{w} C] : HasSubobjectClassifier (Cᵒᵖ ⥤ Type w) where
  exists_classifier := ⟨(Presheaf.classifier (SmallModel C)).ofEquivalence
    (Equivalence.congrLeft (E := Type w) (equivSmallModel C).op).symm⟩

end presheaf

variable {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency.types false in
open Presheaf in
/--
lemma `GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated` / 引理 `GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated`

English:
lemma GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated
  proof: by
  intro Y f hf
  simp only [Presheaf.χ_app, Opposite.op_unop] at hf ⊢
  choose a ha using fun Z (g : Z ⟶ Y) (hg : (Sieve.pullback f ((χ m).app X x)).arrows g) => hg
  refine ⟨(hF _ hf).amalgamate a ?_, ?_⟩
  · introv Y₁ h
    apply (mono_iff_injective (m.app (.op Z))).mp inferInstance
    simp_rw

中文:
引理 GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated
  证明: by
  intro Y f hf
  simp only [Presheaf.χ_app, Opposite.op_unop] at hf ⊢
  choose a ha using fun Z (g : Z ⟶ Y) (hg : (Sieve.pullback f ((χ m).app X x)).arrows g) => hg
  refine ⟨(hF _ hf).amalgamate a ?_, ?_⟩
  · introv Y₁ h
    apply (mono_iff_injective (m.app (.op Z))).mp inferInstance
    simp_rw

Depends on / 依赖: Functor, Functor.map_comp_apply, NatTrans, NatTrans.naturality_apply, Opposite, Opposite.op_unop, Presheaf, Sieve.pullback, amalgamate, arrows, introv, m.app, map_comp_apply, mono_iff_injective, naturality_apply, op_comp, op_unop, pullback, reassoc_of, simp_rw
-/
lemma GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated
    {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) [Mono m] (hF : Presieve.IsSheaf J F)
    (hG : Presieve.IsSeparated J G) (X : Cᵒᵖ) (x : G.obj X) :
    J.IsClosed ((Presheaf.χ m).app X x) := by
  intro Y f hf
  simp only [Presheaf.χ_app, Opposite.op_unop] at hf ⊢
  choose a ha using fun Z (g : Z ⟶ Y) (hg : (Sieve.pullback f ((χ m).app X x)).arrows g) => hg
  refine ⟨(hF _ hf).amalgamate a ?_, ?_⟩
  · introv Y₁ h
    apply (mono_iff_injective (m.app (.op Z))).mp inferInstance
    simp_rw [NatTrans.naturality_apply, ← ha, ← Functor.map_comp_apply, ← op_comp,
      reassoc_of% h]
  · refine (hG _ hf).ext fun Z f' hf' => ?_
    rw [← NatTrans.naturality_apply]; rw [(hF _ hf).valid_glue _ _ hf']; rw [← (ha _ _ _)]; rw [op_comp]; rw [Functor.map_comp_apply]

namespace Sheaf
open CategoryTheory.Functor
variable {F G : Sheaf J (Type max u v)}

/-- The sheaf of closed sieves w/r/t `J`. See also `Functor.closedSieves` and `Sheaf.classifier` -/
@[simps]
/--
Definition of `Ω` / `Ω` 的定义

English:
definition Ω
  signature: (J : GrothendieckTopology C)
  body: (Functor.closedSieves J).toFunctor
  property := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

中文:
定义 Ω
  签名: (J : GrothendieckTopology C)
  定义体: (Functor.closedSieves J).toFunctor
  property := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

Depends on / 依赖: Functor, Functor.closedSieves, closedSieves, toFunctor
-/
def Ω (J : GrothendieckTopology C) : Sheaf J (Type max u v) where
  obj := (Functor.closedSieves J).toFunctor
  property := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `t : 1 ⟶ Ω` which picks out the maximal sieve -/
@[simps]
/--
Definition of `truth` / `truth` 的定义

English:
definition truth
  signature: (J : GrothendieckTopology C)
  body: (Functor.closedSieves J).lift (Presheaf.truth C) fun {X} x => by cat_disch

中文:
定义 truth
  签名: (J : GrothendieckTopology C)
  定义体: (Functor.closedSieves J).lift (Presheaf.truth C) fun {X} x => by cat_disch

Depends on / 依赖: Functor, Functor.closedSieves, Presheaf, Presheaf.truth, cat_disch, closedSieves
-/
def truth (J : GrothendieckTopology C) :
    Sheaf.terminal J (Types.isTerminalPUnit) ⟶ Sheaf.Ω J where
  hom := (Functor.closedSieves J).lift (Presheaf.truth C) fun {X} x => by cat_disch

/--
Given a monomorphism of sheaves `η : F ⟶ G`, an object X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  `∃ a ∈ F(Y), G(f)(x) = η_Y(a)`
-/
@[simps]
/--
Definition of `χ` / `χ` 的定义

English:
definition χ
  signature: (m : F ⟶ G) [Mono m]
  body: (closedSieves J).lift (Presheaf.χ m.hom) (by
    intro X
    simp only [Subfunctor.range_obj, closedSieves_obj, Set.range_subset_iff]
    exact J.isClosed_χ_app_apply_of_isSheaf_of_isSeparated m.hom
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)
      ((isSheaf_iff_isSheaf_of_type _ _).mp G

中文:
定义 χ
  签名: (m : F ⟶ G) [Mono m]
  定义体: (closedSieves J).lift (Presheaf.χ m.hom) (by
    intro X
    simp only [Subfunctor.range_obj, closedSieves_obj, Set.range_subset_iff]
    exact J.isClosed_χ_app_apply_of_isSheaf_of_isSeparated m.hom
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)
      ((isSheaf_iff_isSheaf_of_type _ _).mp G

Depends on / 依赖: F.property, G.property, J.isClosed_, Presheaf, Set.range_subset_iff, Subfunctor, Subfunctor.range_obj, closedSieves, closedSieves_obj, isSeparated, isSheaf_iff_isSheaf_of_type, m.hom, property, range_obj, range_subset_iff
-/
def χ (m : F ⟶ G) [Mono m] : G ⟶ Sheaf.Ω J where
  hom := (closedSieves J).lift (Presheaf.χ m.hom) (by
    intro X
    simp only [Subfunctor.range_obj, closedSieves_obj, Set.range_subset_iff]
    exact J.isClosed_χ_app_apply_of_isSheaf_of_isSeparated m.hom
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)
      ((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isPullback_χ_truth` / 引理 `isPullback_χ_truth`

English:
lemma isPullback_χ_truth
  given: (m : F ⟶ G) [Mono m]
  proof: by
  apply IsPullback.of_map (sheafToPresheaf J _)
  · ext : 1
    simp only [Ω_obj, ObjectProperty.FullSubcategory.comp_hom, χ_hom, terminal_obj, truth_hom,
      ← cancel_mono (closedSieves J).ι, Category.assoc, Subfunctor.lift_ι]
    exact Presheaf.comp_χ_eq m.hom
  · simp only [ObjectProperty.ι_

中文:
引理 isPullback_χ_truth
  条件: (m : F ⟶ G) [Mono m]
  证明: by
  apply IsPullback.of_map (sheafToPresheaf J _)
  · ext : 1
    simp only [Ω_obj, ObjectProperty.FullSubcategory.comp_hom, χ_hom, terminal_obj, truth_hom,
      ← cancel_mono (closedSieves J).ι, Category.assoc, Subfunctor.lift_ι]
    exact Presheaf.comp_χ_eq m.hom
  · simp only [ObjectProperty.ι_

Depends on / 依赖: Category, Category.assoc, FullSubcategory, IsPullback, IsPullback.of_map, IsPullback.of_right, ObjectProperty, ObjectProperty.FullSubcategory.comp_hom, Presheaf, Presheaf.comp_, Subfunctor, Subfunctor.lift_, cancel_mono, closedSieves, comp_hom, m.hom, of_horiz_isIso_mono, of_map, of_right, sheafToPresheaf
-/
lemma isPullback_χ_truth (m : F ⟶ G) [Mono m] :
    IsPullback m ((isTerminalTerminal J _).from F) (Sheaf.χ m) (Sheaf.truth J) := by
  apply IsPullback.of_map (sheafToPresheaf J _)
  · ext : 1
    simp only [Ω_obj, ObjectProperty.FullSubcategory.comp_hom, χ_hom, terminal_obj, truth_hom,
      ← cancel_mono (closedSieves J).ι, Category.assoc, Subfunctor.lift_ι]
    exact Presheaf.comp_χ_eq m.hom
  · simp only [ObjectProperty.ι_obj, terminal_obj, Ω_obj, ObjectProperty.ι_map, χ_hom, truth_hom]
    apply IsPullback.of_right _
      ((cancel_mono ((closedSieves J).ι)).mp (by simpa using Presheaf.comp_χ_eq _))
      (.of_horiz_isIso_mono ⟨_⟩ : IsPullback (𝟙 _) _ (Presheaf.χ m.hom) (closedSieves J).ι)
    · simp only [Category.comp_id]
      exact Presheaf.isPullback_χ_truth m.hom
    · simp_all

set_option backward.isDefEq.respectTransparency false in
/--
lemma `χ_unique` / 引理 `χ_unique`

English:
lemma χ_unique
  statement: (m : F ⟶ G) [Mono m] (χ' : G ⟶ Sheaf.Ω J)
  proof: by
  ext : 1
  rw [← cancel_mono (closedSieves J).ι]; rw [χ_hom]; rw [Subfunctor.lift_ι]
  apply Presheaf.χ_unique _
  have pb : IsPullback (𝟙 G.obj) χ'.hom (χ'.hom ≫ (closedSieves J).ι)
    (closedSieves J).ι := IsPullback.of_horiz_isIso_mono (by simp)
have : IsPullback m.hom ?_ χ'.hom (truth J).ho

中文:
引理 χ_unique
  结论: (m : F ⟶ G) [Mono m] (χ' : G ⟶ Sheaf.Ω J)
  证明: by
  ext : 1
  rw [← cancel_mono (closedSieves J).ι]; rw [χ_hom]; rw [Subfunctor.lift_ι]
  apply Presheaf.χ_unique _
  have pb : IsPullback (𝟙 G.obj) χ'.hom (χ'.hom ≫ (closedSieves J).ι)
    (closedSieves J).ι := IsPullback.of_horiz_isIso_mono (by simp)
have : IsPullback m.hom ?_ χ'.hom (truth J).ho

Depends on / 依赖: G.obj, IsPullback, IsPullback.of_horiz_isIso_mono, Presheaf, Subfunctor, Subfunctor.lift_, cancel_mono, closedSieves, m.hom, of_horiz_isIso_mono, paste_horiz, sheafToPresheaf, this.paste_horiz
-/
lemma χ_unique (m : F ⟶ G) [Mono m] (χ' : G ⟶ Sheaf.Ω J)
    (hχ' : IsPullback m ((isTerminalTerminal J _).from F) χ' (Sheaf.truth J)) :
    χ' = Sheaf.χ m := by
  ext : 1
  rw [← cancel_mono (closedSieves J).ι]; rw [χ_hom]; rw [Subfunctor.lift_ι]
  apply Presheaf.χ_unique _
  have pb : IsPullback (𝟙 G.obj) χ'.hom (χ'.hom ≫ (closedSieves J).ι)
    (closedSieves J).ι := IsPullback.of_horiz_isIso_mono (by simp)
have : IsPullback m.hom ?_ χ'.hom (truth J).hom := by
    simpa using hχ'.map (sheafToPresheaf J _)
  simpa using this.paste_horiz pb

/--
A construction of a subobject classifier for sheaf categories. `Ω` is the sheaf of closed sieves,
and `truth` maps for each object `X : C`, an element of `PUnit` to the maximal `Sieve X`, which is
always closed.
-/
@[simps! Ω truth Ω₀ χ χ₀]
/--
Definition of `classifier` / `classifier` 的定义

English:
definition classifier
  signature: (J : GrothendieckTopology C)
  body: .mkOfTerminalΩ₀ (.terminal J Types.isTerminalPUnit) (isTerminalTerminal _ _) (Sheaf.Ω J)
    (Sheaf.truth J) Sheaf.χ Sheaf.isPullback_χ_truth Sheaf.χ_unique

中文:
定义 classifier
  签名: (J : GrothendieckTopology C)
  定义体: .mkOfTerminalΩ₀ (.terminal J Types.isTerminalPUnit) (isTerminalTerminal _ _) (Sheaf.Ω J)
    (Sheaf.truth J) Sheaf.χ Sheaf.isPullback_χ_truth Sheaf.χ_unique

Depends on / 依赖: Sheaf.isPullback_, Sheaf.truth, Types.isTerminalPUnit, isTerminalPUnit, isTerminalTerminal, terminal
-/
def classifier (J : GrothendieckTopology C) : Subobject.Classifier (Sheaf J (Type max u v)) :=
  .mkOfTerminalΩ₀ (.terminal J Types.isTerminalPUnit) (isTerminalTerminal _ _) (Sheaf.Ω J)
    (Sheaf.truth J) Sheaf.χ Sheaf.isPullback_χ_truth Sheaf.χ_unique

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssentiallySmall.{w}
  signature: C] : HasSubobjectClassifier (Sheaf J (Type w)) where
  body: ⟨Sheaf.classifier ((equivSmallModel C).inverse.inducedTopology J)
.ofEquivalence (Equivalence.sheafCongr _ _ (equivSmallModel C) _).symm⟩

中文:
实例 [EssentiallySmall.{w}
  签名: C] : HasSubobjectClassifier (Sheaf J (Type w)) where
  定义体: ⟨Sheaf.classifier ((equivSmallModel C).inverse.inducedTopology J)
.ofEquivalence (Equivalence.sheafCongr _ _ (equivSmallModel C) _).symm⟩

Depends on / 依赖: Sheaf.classifier, classifier, equivSmallModel, inducedTopology, inverse, inverse.inducedTopology
-/
instance [EssentiallySmall.{w} C] : HasSubobjectClassifier (Sheaf J (Type w)) where
  exists_classifier := ⟨Sheaf.classifier ((equivSmallModel C).inverse.inducedTopology J)
.ofEquivalence (Equivalence.sheafCongr _ _ (equivSmallModel C) _).symm⟩

end Sheaf

end CategoryTheory

end
