/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.ExactSequence

/-! # Homological functors

In this file, given a functor `F : C ⥤ A` from a pretriangulated category to
an abelian category, we define the type class `F.IsHomological`, which is the property
that `F` sends distinguished triangles in `C` to exact sequences in `A`.

If `F` has been endowed with `[F.ShiftSequence ℤ]`, then we may think
of the functor `F` as a `H^0`, and then the `H^n` functors are the functors `F.shift n : C ⥤ A`:
we have isomorphisms `(F.shift n).obj X ≅ F.obj (X⟦n⟧)`, but through the choice of this
"shift sequence", the user may provide functors with better definitional properties.

Given a triangle `T` in `C`, we define a connecting homomorphism
`F.homologySequenceδ T n₀ n₁ h : (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁`
under the assumption `h : n₀ + 1 = n₁`. When `T` is distinguished, this connecting
homomorphism is part of a long exact sequence
`... ⟶ (F.shift n₀).obj T.obj₁ ⟶ (F.shift n₀).obj T.obj₂ ⟶ (F.shift n₀).obj T.obj₃ ⟶ ...`

The exactness of this long exact sequence is given by three lemmas
`F.homologySequence_exact₁`, `F.homologySequence_exact₂` and `F.homologySequence_exact₃`.

If `F` is a homological functor, we define the strictly full triangulated subcategory
`F.homologicalKernel`: it consists of objects `X : C` such that for all `n : ℤ`,
`(F.shift n).obj X` (or `F.obj (X⟦n⟧)`) is zero. We show that a morphism `f` in `C`
belongs to `F.homologicalKernel.trW` (i.e. the cone of `f` is in this kernel) iff
`(F.shift n).map f` is an isomorphism for all `n : ℤ`.

Note: depending on the sources, homological functors are sometimes
called cohomological functors, while certain authors use "cohomological functors"
for "contravariant" functors (i.e. functors `Cᵒᵖ ⥤ A`).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C D A : Type*} [Category* C] [HasShift C Int]
  [Category* D] [HasZeroObject D] [HasShift D Int] [Preadditive D]
  [forall (n : Int), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [Category* A]

namespace Functor

variable (F : C ⥤ A)

/--
Definition of `homologicalKernel` / `homologicalKernel` 的定义

English:
definition homologicalKernel
  signature: : ObjectProperty C
  body: fun X => forall (n : Int), IsZero (F.obj (X⟦n⟧))

中文:
定义 homologicalKernel
  签名: : ObjectProperty C
  定义体: fun X => forall (n : Int), IsZero (F.obj (X⟦n⟧))

Depends on / 依赖: F.obj, IsZero
-/
def homologicalKernel : ObjectProperty C :=
  fun X => forall (n : Int), IsZero (F.obj (X⟦n⟧))

/--
lemma `mem_homologicalKernel_iff` / 引理 `mem_homologicalKernel_iff`

English:
lemma mem_homologicalKernel_iff
  given: [F.ShiftSequence Int] (X : C)
  proof: by
  simp only [← fun (n : Int) => Iso.isZero_iff ((F.isoShift n).app X),
    homologicalKernel, comp_obj]

中文:
引理 mem_homologicalKernel_iff
  条件: [F.ShiftSequence 整数] (X : C)
  证明: by
  simp only [← fun (n : Int) => Iso.isZero_iff ((F.isoShift n).app X),
    homologicalKernel, comp_obj]

Depends on / 依赖: F.isoShift, Iso.isZero_iff, comp_obj, homologicalKernel, isZero_iff, isoShift
-/
lemma mem_homologicalKernel_iff [F.ShiftSequence Int] (X : C) :
    F.homologicalKernel X ↔ forall (n : Int), IsZero ((F.shift n).obj X) := by
  simp only [← fun (n : Int) => Iso.isZero_iff ((F.isoShift n).app X),
    homologicalKernel, comp_obj]

section Pretriangulated

variable [HasZeroObject C] [Preadditive C] [forall (n : Int), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/--
Definition of `IsHomological` / `IsHomological` 的定义

English:
class IsHomological
  parameters: : Prop extends F.PreservesZeroMorphisms where
  extends: F.PreservesZeroMorphisms
  axioms and operations (1):
    - exact((T : Triangle C) (hT : T in distTriang C)) : ((shortComplexOfDistTriangle T hT).map F).Exact

中文:
类 是Homological
  参数: : 命题 extends F.保持ZeroMorphisms where
  继承: F.保持ZeroMorphisms
  公理与运算 (1 个):
    - exact((T : Triangle C) (hT : T in distTriang C)) : ((shortComplexOfDistTriangle T hT).map F).正合
-/
class IsHomological : Prop extends F.PreservesZeroMorphisms where
  exact (T : Triangle C) (hT : T in distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact

/--
lemma `map_distinguished_exact` / 引理 `map_distinguished_exact`

English:
lemma map_distinguished_exact
  given: [F.IsHomological] (T : Triangle C) (hT : T in distTriang C)
  proof: IsHomological.exact _ hT

中文:
引理 map_distinguished_exact
  条件: [F.是Homological] (T : Triangle C) (hT : T in distTriang C)
  证明: IsHomological.exact _ hT

Depends on / 依赖: IsHomological, IsHomological.exact
-/
lemma map_distinguished_exact [F.IsHomological] (T : Triangle C) (hT : T in distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact :=
  IsHomological.exact _ hT

instance (L : C ⥤ D) (F : D ⥤ A) [L.CommShift Int] [L.IsTriangulated] [F.IsHomological] :
    (L ⋙ F).IsHomological where
  exact T hT := F.map_distinguished_exact _ (L.map_distinguished T hT)

/--
lemma `IsHomological.mk'` / 引理 `IsHomological.mk'`

English:
lemma IsHomological.mk'
  statement: [F.PreservesZeroMorphisms]
  proof: by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'

中文:
引理 是Homological.mk'
  结论: [F.保持ZeroMorphisms]
  证明: by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'

Depends on / 依赖: F.mapShortComplex.mapIso, ShortComplex, ShortComplex.exact_iff_of_iso, exact_iff_of_iso, mapIso, mapShortComplex, shortComplexOfDistTriangleIsoOfIso
-/
lemma IsHomological.mk' [F.PreservesZeroMorphisms]
    (hF : forall (T : Pretriangulated.Triangle C) (hT : T in distTriang C),
      exists (T' : Pretriangulated.Triangle C) (e : T ≅ T'),
      ((shortComplexOfDistTriangle T' (isomorphic_distinguished _ hT _ e.symm)).map F).Exact) :
    F.IsHomological where
  exact T hT := by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'

/--
lemma `IsHomological.of_iso` / 引理 `IsHomological.of_iso`

English:
lemma IsHomological.of_iso
  given: {F₁ F₂ : C ⥤ A} [F₁.IsHomological] (e : F₁ ≅ F₂)
  proof: have := preservesZeroMorphisms_of_iso e
  ⟨fun T hT => ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)⟩

中文:
引理 是Homological.of_iso
  条件: {F₁ F₂ : C ⥤ A} [F₁.是Homological] (e : F₁ ≅ F₂)
  证明: have := preservesZeroMorphisms_of_iso e
  ⟨fun T hT => ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)⟩

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_iso, ShortComplex.mapNatIso, exact_of_iso, mapNatIso, map_distinguished_exact, preservesZeroMorphisms_of_iso
-/
lemma IsHomological.of_iso {F₁ F₂ : C ⥤ A} [F₁.IsHomological] (e : F₁ ≅ F₂) :
    F₂.IsHomological :=
  have := preservesZeroMorphisms_of_iso e
  ⟨fun T hT => ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)⟩

section

variable [F.IsHomological]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.homologicalKernel.IsClosedUnderIsomorphisms
  body: (hX n).of_iso ((shiftFunctor C n ⋙ F).mapIso e.symm)

中文:
实例 :
  签名: F.homologicalKernel.在同构下封闭
  定义体: (hX n).of_iso ((shiftFunctor C n ⋙ F).mapIso e.symm)

Depends on / 依赖: e.symm, mapIso, of_iso, shiftFunctor
-/
instance : F.homologicalKernel.IsClosedUnderIsomorphisms where
  of_iso e hX n := (hX n).of_iso ((shiftFunctor C n ⋙ F).mapIso e.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.homologicalKernel.IsTriangulated
  body: ⟨0, isZero_zero C,
    fun n => (shiftFunctor C n ⋙ F).map_isZero (isZero_zero C)⟩
  toIsStableUnderShift := ⟨fun a => ⟨fun X hX b =>
    (hX (a + b)).of_iso (F.mapIso ((shiftFunctorAdd C a b).app X).symm)⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n =>
      (F.map_distinguished_exact _
        (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
          ((h₁ n).eq_of_src _ _) ((h₃ n).eq_of_tgt _ _))

中文:
实例 :
  签名: F.homologicalKernel.是三角
  定义体: ⟨0, isZero_zero C,
    fun n => (shiftFunctor C n ⋙ F).map_isZero (isZero_zero C)⟩
  toIsStableUnderShift := ⟨fun a => ⟨fun X hX b =>
    (hX (a + b)).of_iso (F.mapIso ((shiftFunctorAdd C a b).app X).symm)⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n =>
      (F.map_distinguished_exact _
        (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
          ((h₁ n).eq_of_src _ _) ((h₃ n).eq_of_tgt _ _))

Depends on / 依赖: isZero_zero
-/
instance : F.homologicalKernel.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C,
    fun n => (shiftFunctor C n ⋙ F).map_isZero (isZero_zero C)⟩
  toIsStableUnderShift := ⟨fun a => ⟨fun X hX b =>
    (hX (a + b)).of_iso (F.mapIso ((shiftFunctorAdd C a b).app X).symm)⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n =>
      (F.map_distinguished_exact _
        (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
          ((h₁ n).eq_of_src _ _) ((h₃ n).eq_of_tgt _ _))

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
noncomputable instance (priority := 100) [F.IsHomological] :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices forall (X₁ X₂ : C), PreservesLimit (pair X₁ X₂) F from
    ⟨fun {X} => preservesLimit_of_iso_diagram F (diagramIsoPair X).symm⟩
  intro X₁ X₂
  have : HasBinaryBiproduct (F.obj X₁) (F.obj X₂) := HasBinaryBiproducts.has_binary_biproduct _ _
  have : Mono (F.biprodComparison X₁ X₂) := by
    rw [mono_iff_cancel_zero]
    intro Z f hf
    let S := (ShortComplex.mk _ _ (biprod.inl_snd (X := X₁) (Y := X₂))).map F
    have : Mono S.f := by dsimp [S]; infer_instance
    have ex : S.Exact := F.map_distinguished_exact _ (binaryBiproductTriangle_distinguished X₁ X₂)
    obtain ⟨g, rfl⟩ := ex.lift' f (by simpa using! hf =≫ biprod.snd)
    dsimp [S] at hf ⊢
    replace hf := hf =≫ biprod.fst
    simp only [assoc, biprodComparison_fst, zero_comp, ← F.map_comp, biprod.inl_fst,
      F.map_id, comp_id] at hf
    rw [hf]; rw [zero_comp]
  have : PreservesBinaryBiproduct X₁ X₂ F := preservesBinaryBiproduct_of_mono_biprodComparison _
  apply Limits.preservesBinaryProduct_of_preservesBinaryBiproduct

instance (priority := 100) [F.IsHomological] : F.Additive :=
  F.additive_of_preserves_binary_products

/--
lemma `isHomological_of_localization` / 引理 `isHomological_of_localization`

English:
lemma isHomological_of_localization
  statement: (L : C ⥤ D)
  proof: by
  have : F.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (F.mapIso L.mapZeroObject.symm ≪≫ e.app _ ≪≫ G.mapZeroObject)
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine IsHomological.mk' _ (fun T hT => ?_)
  rw [L.distTriang_iff] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

中文:
引理 isHomological_of_localization
  结论: (L : C ⥤ D)
  证明: by
  have : F.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (F.mapIso L.mapZeroObject.symm ≪≫ e.app _ ≪≫ G.mapZeroObject)
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine IsHomological.mk' _ (fun T hT => ?_)
  rw [L.distTriang_iff] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

Depends on / 依赖: F.PreservesZeroMorphisms, F.mapIso, G.mapZeroObject, IsHomological, IsHomological.mk, IsHomological.of_iso, L.distTriang_iff, L.mapTriangle.obj, L.mapZeroObject.symm, PreservesZeroMorphisms, distTriang_iff, e.app, e.symm, mapIso, mapTriangle, mapZeroObject, map_distinguished_exact, of_iso, preservesZeroMorphisms_of_map_zero_object
-/
lemma isHomological_of_localization (L : C ⥤ D)
    [L.CommShift Int] [L.IsTriangulated] [L.mapArrow.EssSurj] (F : D ⥤ A)
    (G : C ⥤ A) (e : L ⋙ F ≅ G) [G.IsHomological] :
    F.IsHomological := by
  have : F.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (F.mapIso L.mapZeroObject.symm ≪≫ e.app _ ≪≫ G.mapZeroObject)
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine IsHomological.mk' _ (fun T hT => ?_)
  rw [L.distTriang_iff] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

end Pretriangulated

section

/--
Definition of `homologySequenceδ` / `homologySequenceδ` 的定义

English:
definition homologySequenceδ
  body: F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

中文:
定义 homologySequenceδ
  定义体: F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

Depends on / 依赖: F.shiftMap, T.mor, add_comm, shiftMap
-/
noncomputable def homologySequenceδ
    [F.ShiftSequence Int] (T : Triangle C) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) :
    (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable {T T'}

@[reassoc]
/--
lemma `homologySequenceδ_naturality` / 引理 `homologySequenceδ_naturality`

English:
lemma homologySequenceδ_naturality
  proof: by
  dsimp only [homologySequenceδ]
  rw [← shiftMap_comp']; rw [← φ.comm₃]; rw [shiftMap_comp]

中文:
引理 homologySequenceδ_naturality
  证明: by
  dsimp only [homologySequenceδ]
  rw [← shiftMap_comp']; rw [← φ.comm₃]; rw [shiftMap_comp]

Depends on / 依赖: shiftMap_comp
-/
lemma homologySequenceδ_naturality
    [F.ShiftSequence Int] (T T' : Triangle C) (φ : T ⟶ T') (n₀ n₁ : Int) (h : n₀ + 1 = n₁) :
    (F.shift n₀).map φ.hom₃ ≫ F.homologySequenceδ T' n₀ n₁ h =
      F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map φ.hom₁ := by
  dsimp only [homologySequenceδ]
  rw [← shiftMap_comp']; rw [← φ.comm₃]; rw [shiftMap_comp]

variable (T)
variable [HasZeroObject C] [Preadditive C] [forall (n : Int), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A] [F.IsHomological]
variable [F.ShiftSequence Int] (T T' : Triangle C) (hT : T in distTriang C)
  (hT' : T' in distTriang C) (φ : T ⟶ T') (n₀ n₁ : Int) (h : n₀ + 1 = n₁)

section
include hT
@[reassoc]
/--
lemma `comp_homologySequenceδ` / 引理 `comp_homologySequenceδ`

English:
lemma comp_homologySequenceδ
  proof: by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp']; rw [comp_distTriang_mor_zero₂₃ _ hT]; rw [shiftMap_zero]

@[reassoc]

中文:
引理 comp_homologySequenceδ
  证明: by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp']; rw [comp_distTriang_mor_zero₂₃ _ hT]; rw [shiftMap_zero]

@[reassoc]

Depends on / 依赖: F.shiftMap_comp, shiftMap_comp, shiftMap_zero
-/
lemma comp_homologySequenceδ :
    (F.shift n₀).map T.mor₂ ≫ F.homologySequenceδ T n₀ n₁ h = 0 := by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp']; rw [comp_distTriang_mor_zero₂₃ _ hT]; rw [shiftMap_zero]

@[reassoc]
/--
lemma `homologySequenceδ_comp` / 引理 `homologySequenceδ_comp`

English:
lemma homologySequenceδ_comp
  proof: by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp]; rw [comp_distTriang_mor_zero₃₁ _ hT]; rw [shiftMap_zero]

@[reassoc]

中文:
引理 homologySequenceδ_comp
  证明: by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp]; rw [comp_distTriang_mor_zero₃₁ _ hT]; rw [shiftMap_zero]

@[reassoc]

Depends on / 依赖: F.shiftMap_comp, shiftMap_comp, shiftMap_zero
-/
lemma homologySequenceδ_comp :
    F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map T.mor₁ = 0 := by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp]; rw [comp_distTriang_mor_zero₃₁ _ hT]; rw [shiftMap_zero]

@[reassoc]
/--
lemma `homologySequence_comp` / 引理 `homologySequence_comp`

English:
lemma homologySequence_comp
  proof: by
  rw [← Functor.map_comp]; rw [comp_distTriang_mor_zero₁₂ _ hT]; rw [Functor.map_zero]

中文:
引理 homologySequence_comp
  证明: by
  rw [← Functor.map_comp]; rw [comp_distTriang_mor_zero₁₂ _ hT]; rw [Functor.map_zero]

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_zero, map_comp, map_zero
-/
lemma homologySequence_comp :
    (F.shift n₀).map T.mor₁ ≫ (F.shift n₀).map T.mor₂ = 0 := by
  rw [← Functor.map_comp]; rw [comp_distTriang_mor_zero₁₂ _ hT]; rw [Functor.map_zero]

attribute [local simp] smul_smul

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `homologySequence_exact₂` / 引理 `homologySequence_exact₂`

English:
lemma homologySequence_exact₂
  proof: by
  refine ShortComplex.exact_of_iso ?_ (F.map_distinguished_exact _
    (Triangle.shift_distinguished _ hT n₀))
  exact ShortComplex.isoMk ((F.isoShift n₀).app _)
    (n₀.negOnePow • ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _)
    (by simp) (by simp)

中文:
引理 homologySequence_exact₂
  证明: by
  refine ShortComplex.exact_of_iso ?_ (F.map_distinguished_exact _
    (Triangle.shift_distinguished _ hT n₀))
  exact ShortComplex.isoMk ((F.isoShift n₀).app _)
    (n₀.negOnePow • ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _)
    (by simp) (by simp)

Depends on / 依赖: F.isoShift, F.map_distinguished_exact, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, Triangle, Triangle.shift_distinguished, exact_of_iso, isoShift, map_distinguished_exact, negOnePow, shift_distinguished
-/
lemma homologySequence_exact₂ :
    (ShortComplex.mk _ _ (F.homologySequence_comp T hT n₀)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.map_distinguished_exact _
    (Triangle.shift_distinguished _ hT n₀))
  exact ShortComplex.isoMk ((F.isoShift n₀).app _)
    (n₀.negOnePow • ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _)
    (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `homologySequence_exact₃` / 引理 `homologySequence_exact₃`

English:
lemma homologySequence_exact₃
  proof: by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (rot_of_distTriang _ hT) n₀)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by lia)).app _) (by simp) (by simp [homologySequenceδ, shiftMap])

中文:
引理 homologySequence_exact₃
  证明: by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (rot_of_distTriang _ hT) n₀)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by lia)).app _) (by simp) (by simp [homologySequenceδ, shiftMap])

Depends on / 依赖: F.homologySequence_exact, F.shiftIso, Iso.refl, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, exact_of_iso, rot_of_distTriang, shiftIso, shiftMap
-/
lemma homologySequence_exact₃ :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (rot_of_distTriang _ hT) n₀)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by lia)).app _) (by simp) (by simp [homologySequenceδ, shiftMap])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologySequence_exact₁` / 引理 `homologySequence_exact₁`

English:
lemma homologySequence_exact₁
  proof: by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (inv_rot_of_distTriang _ hT) n₁)
  refine ShortComplex.isoMk (-((F.shiftIso (-1) n₁ n₀ (by lia)).app _))
    (Iso.refl _) (Iso.refl _) ?_ (by simp)
  dsimp
  simp only [homologySequenceδ, neg_comp, map_neg, comp_id,
    F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1) (neg_add_cancel 1) n₀ n₁
      (by lia)]

中文:
引理 homologySequence_exact₁
  证明: by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (inv_rot_of_distTriang _ hT) n₁)
  refine ShortComplex.isoMk (-((F.shiftIso (-1) n₁ n₀ (by lia)).app _))
    (Iso.refl _) (Iso.refl _) ?_ (by simp)
  dsimp
  simp only [homologySequenceδ, neg_comp, map_neg, comp_id,
    F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1) (neg_add_cancel 1) n₀ n₁
      (by lia)]

Depends on / 依赖: F.homologySequence_exact, F.shiftIso, F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero, Iso.refl, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, T.mor, comp_id, exact_of_iso, inv_rot_of_distTriang, map_neg, neg_add_cancel, neg_comp, shiftIso, shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
-/
lemma homologySequence_exact₁ :
    (ShortComplex.mk _ _ (F.homologySequenceδ_comp T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (inv_rot_of_distTriang _ hT) n₁)
  refine ShortComplex.isoMk (-((F.shiftIso (-1) n₁ n₀ (by lia)).app _))
    (Iso.refl _) (Iso.refl _) ?_ (by simp)
  dsimp
  simp only [homologySequenceδ, neg_comp, map_neg, comp_id,
    F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1) (neg_add_cancel 1) n₀ n₁
      (by lia)]

/--
lemma `homologySequence_epi_shift_map_mor₁_iff` / 引理 `homologySequence_epi_shift_map_mor₁_iff`

English:
lemma homologySequence_epi_shift_map_mor₁_iff
  proof: (F.homologySequence_exact₂ T hT n₀).epi_f_iff

中文:
引理 homologySequence_epi_shift_map_mor₁_iff
  证明: (F.homologySequence_exact₂ T hT n₀).epi_f_iff

Depends on / 依赖: F.homologySequence_exact, epi_f_iff
-/
lemma homologySequence_epi_shift_map_mor₁_iff :
    Epi ((F.shift n₀).map T.mor₁) ↔ (F.shift n₀).map T.mor₂ = 0 :=
  (F.homologySequence_exact₂ T hT n₀).epi_f_iff

/--
lemma `homologySequence_mono_shift_map_mor₁_iff` / 引理 `homologySequence_mono_shift_map_mor₁_iff`

English:
lemma homologySequence_mono_shift_map_mor₁_iff
  proof: (F.homologySequence_exact₁ T hT n₀ n₁ h).mono_g_iff

中文:
引理 homologySequence_mono_shift_map_mor₁_iff
  证明: (F.homologySequence_exact₁ T hT n₀ n₁ h).mono_g_iff

Depends on / 依赖: F.homologySequence_exact, mono_g_iff
-/
lemma homologySequence_mono_shift_map_mor₁_iff :
    Mono ((F.shift n₁).map T.mor₁) ↔ F.homologySequenceδ T n₀ n₁ h = 0 :=
  (F.homologySequence_exact₁ T hT n₀ n₁ h).mono_g_iff

/--
lemma `homologySequence_epi_shift_map_mor₂_iff` / 引理 `homologySequence_epi_shift_map_mor₂_iff`

English:
lemma homologySequence_epi_shift_map_mor₂_iff
  proof: (F.homologySequence_exact₃ T hT n₀ n₁ h).epi_f_iff

中文:
引理 homologySequence_epi_shift_map_mor₂_iff
  证明: (F.homologySequence_exact₃ T hT n₀ n₁ h).epi_f_iff

Depends on / 依赖: F.homologySequence_exact, epi_f_iff
-/
lemma homologySequence_epi_shift_map_mor₂_iff :
    Epi ((F.shift n₀).map T.mor₂) ↔ F.homologySequenceδ T n₀ n₁ h = 0 :=
  (F.homologySequence_exact₃ T hT n₀ n₁ h).epi_f_iff

/--
lemma `homologySequence_mono_shift_map_mor₂_iff` / 引理 `homologySequence_mono_shift_map_mor₂_iff`

English:
lemma homologySequence_mono_shift_map_mor₂_iff
  proof: (F.homologySequence_exact₂ T hT n₀).mono_g_iff

中文:
引理 homologySequence_mono_shift_map_mor₂_iff
  证明: (F.homologySequence_exact₂ T hT n₀).mono_g_iff

Depends on / 依赖: F.homologySequence_exact, mono_g_iff
-/
lemma homologySequence_mono_shift_map_mor₂_iff :
    Mono ((F.shift n₀).map T.mor₂) ↔ (F.shift n₀).map T.mor₁ = 0 :=
  (F.homologySequence_exact₂ T hT n₀).mono_g_iff
end

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mem_homologicalKernel_trW_iff` / 引理 `mem_homologicalKernel_trW_iff`

English:
lemma mem_homologicalKernel_trW_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  apply (F.homologicalKernel.trW_iff_of_distinguished _ hT).trans
  have h₁ := fun n => (F.homologySequence_exact₃ _ hT n _ rfl).isZero_X₂_iff
  have h₂ := fun n => F.homologySequence_mono_shift_map_mor₁_iff _ hT n _ rfl
  have h₃ := fun n => F.homologySequence_epi_shift_map_mor₁_iff _ hT n
  dsimp at h₁ h₂ h₃ ⊢
  simp only [mem_homologicalKernel_iff, h₁, ← h₂, ← h₃]
  constructor
  · intro h n
    obtain ⟨m, rfl⟩ : exists (m : Int), n = m + 1 := ⟨n - 1, by simp⟩
    have := (h (m + 1)).1
    have := (h m).2
    apply isIso_of_mono_of_epi
  · intros
    constructor <;> infer_instance

中文:
引理 mem_homologicalKernel_trW_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  apply (F.homologicalKernel.trW_iff_of_distinguished _ hT).trans
  have h₁ := fun n => (F.homologySequence_exact₃ _ hT n _ rfl).isZero_X₂_iff
  have h₂ := fun n => F.homologySequence_mono_shift_map_mor₁_iff _ hT n _ rfl
  have h₃ := fun n => F.homologySequence_epi_shift_map_mor₁_iff _ hT n
  dsimp at h₁ h₂ h₃ ⊢
  simp only [mem_homologicalKernel_iff, h₁, ← h₂, ← h₃]
  constructor
  · intro h n
    obtain ⟨m, rfl⟩ : exists (m : Int), n = m + 1 := ⟨n - 1, by simp⟩
    have := (h (m + 1)).1
    have := (h m).2
    apply isIso_of_mono_of_epi
  · intros
    constructor <;> infer_instance

Depends on / 依赖: F.homologicalKernel.trW_iff_of_distinguished, F.homologySequence_epi_shift_map_mor, F.homologySequence_exact, F.homologySequence_mono_shift_map_mor, distinguished_cocone_triangle, homologicalKernel, mem_homologicalKernel_iff, trW_iff_of_distinguished
-/
lemma mem_homologicalKernel_trW_iff {X Y : C} (f : X ⟶ Y) :
    F.homologicalKernel.trW f ↔ forall (n : Int), IsIso ((F.shift n).map f) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  apply (F.homologicalKernel.trW_iff_of_distinguished _ hT).trans
  have h₁ := fun n => (F.homologySequence_exact₃ _ hT n _ rfl).isZero_X₂_iff
  have h₂ := fun n => F.homologySequence_mono_shift_map_mor₁_iff _ hT n _ rfl
  have h₃ := fun n => F.homologySequence_epi_shift_map_mor₁_iff _ hT n
  dsimp at h₁ h₂ h₃ ⊢
  simp only [mem_homologicalKernel_iff, h₁, ← h₂, ← h₃]
  constructor
  · intro h n
    obtain ⟨m, rfl⟩ : exists (m : Int), n = m + 1 := ⟨n - 1, by simp⟩
    have := (h (m + 1)).1
    have := (h m).2
    apply isIso_of_mono_of_epi
  · intros
    constructor <;> infer_instance

open ComposableArrows

/--
Definition of `homologySequenceComposableArrows₅` / `homologySequenceComposableArrows₅` 的定义

English:
definition homologySequenceComposableArrows₅
  signature: : ComposableArrows A 5
  body: mk₅ ((F.shift n₀).map T.mor₁) ((F.shift n₀).map T.mor₂)
    (F.homologySequenceδ T n₀ n₁ h) ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂)

include hT in

中文:
定义 homologySequenceComposableArrows₅
  签名: : ComposableArrows A 5
  定义体: mk₅ ((F.shift n₀).map T.mor₁) ((F.shift n₀).map T.mor₂)
    (F.homologySequenceδ T n₀ n₁ h) ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂)

include hT in
-/
@[simp] noncomputable def homologySequenceComposableArrows₅ : ComposableArrows A 5 :=
  mk₅ ((F.shift n₀).map T.mor₁) ((F.shift n₀).map T.mor₂)
    (F.homologySequenceδ T n₀ n₁ h) ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂)

include hT in
/--
lemma `homologySequenceComposableArrows₅_exact` / 引理 `homologySequenceComposableArrows₅_exact`

English:
lemma homologySequenceComposableArrows₅_exact
  proof: exact_of_δ₀ (F.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
    (exact_of_δ₀ (F.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (F.homologySequence_exact₁ T hT n₀ n₁ h).exact_toComposableArrows
        (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows))

中文:
引理 homologySequenceComposableArrows₅_exact
  证明: exact_of_δ₀ (F.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
    (exact_of_δ₀ (F.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (F.homologySequence_exact₁ T hT n₀ n₁ h).exact_toComposableArrows
        (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows))

Depends on / 依赖: F.homologySequence_exact, exact_toComposableArrows
-/
lemma homologySequenceComposableArrows₅_exact :
    (F.homologySequenceComposableArrows₅ T n₀ n₁ h).Exact :=
  exact_of_δ₀ (F.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
    (exact_of_δ₀ (F.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (F.homologySequence_exact₁ T hT n₀ n₁ h).exact_toComposableArrows
        (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows))

end

end Functor

end CategoryTheory
