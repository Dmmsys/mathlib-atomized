/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangle
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# The pretriangulated structure on the opposite category

In this file, we construct the pretriangulated structure
on the opposite category `Cᵒᵖ` of a pretriangulated category `C`.

The shift on `Cᵒᵖ` was constructed in `Mathlib.CategoryTheory.Triangulated.Opposite.Basic`,
and is such that shifting by `n : ℤ` on `Cᵒᵖ` corresponds to the shift by
`-n` on `C`. In `Mathlib.CategoryTheory.Triangulated.Opposite.Triangle`, we constructed
an equivalence `(Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ`, called
`Mathlib.CategoryTheory.Pretriangulated.triangleOpEquivalence`.

Here, we defined the notion of distinguished triangles in `Cᵒᵖ`, such that
`triangleOpEquivalence` sends distinguished triangles in `C` to distinguished triangles
in `Cᵒᵖ`. In other words, if `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is a distinguished triangle in `C`,
then the triangle `op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` that is deduced *without introducing signs*
shall be a distinguished triangle in `Cᵒᵖ`. This is equivalent to the definition
in [Verdier's thesis, p. 96][verdier1996] which would require that the triangle
`(op X)⟦-1⟧ ⟶ op Z ⟶ op Y ⟶ op X` (without signs) is *antidistinguished*.

In the file `Mathlib.Triangulated.Opposite.Triangulated`, we show that `Cᵒᵖ` is
triangulated if `C` is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C] [HasShift C Int] [HasZeroObject C] [Preadditive C]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

open Pretriangulated.Opposite

namespace Opposite

/--
Definition of `distinguishedTriangles` / `distinguishedTriangles` 的定义

English:
definition distinguishedTriangles
  signature: : Set (Triangle Cᵒᵖ)
  body: {T | ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C}

中文:
定义 distinguishedTriangles
  签名: : Set (Triangle Cᵒᵖ)
  定义体: {T | ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C}

Depends on / 依赖: distTriang, inverse, inverse.obj, triangleOpEquivalence
-/
def distinguishedTriangles : Set (Triangle Cᵒᵖ) :=
  {T | ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C}

variable {C}

/--
lemma `mem_distinguishedTriangles_iff` / 引理 `mem_distinguishedTriangles_iff`

English:
lemma mem_distinguishedTriangles_iff
  given: (T : Triangle Cᵒᵖ)
  proof: by
  rfl

中文:
引理 mem_distinguishedTriangles_iff
  条件: (T : Triangle Cᵒᵖ)
  证明: by
  rfl
-/
lemma mem_distinguishedTriangles_iff (T : Triangle Cᵒᵖ) :
    T in distinguishedTriangles C ↔
      ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C := by
  rfl

/--
lemma `mem_distinguishedTriangles_iff'` / 引理 `mem_distinguishedTriangles_iff'`

English:
lemma mem_distinguishedTriangles_iff'
  given: (T : Triangle Cᵒᵖ)
  proof: by
  rw [mem_distinguishedTriangles_iff]
  constructor
  · intro hT
    exact ⟨_, hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine isomorphic_distinguished _ hT' _ ?_
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triang

中文:
引理 mem_distinguishedTriangles_iff'
  条件: (T : Triangle Cᵒᵖ)
  证明: by
  rw [mem_distinguishedTriangles_iff]
  constructor
  · intro hT
    exact ⟨_, hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine isomorphic_distinguished _ hT' _ ?_
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triang

Depends on / 依赖: Iso.unop, Opposite, Opposite.op, counitIso, counitIso.symm.app, e.symm, inverse, inverse.mapIso, isomorphic_distinguished, mapIso, mem_distinguishedTriangles_iff, triangleOpEquivalence, unitIso, unitIso.app
-/
lemma mem_distinguishedTriangles_iff' (T : Triangle Cᵒᵖ) :
    T in distinguishedTriangles C ↔
      exists (T' : Triangle C) (_ : T' in distTriang C),
        Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) := by
  rw [mem_distinguishedTriangles_iff]
  constructor
  · intro hT
    exact ⟨_, hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine isomorphic_distinguished _ hT' _ ?_
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triangleOpEquivalence C).inverse.mapIso e.symm)

/--
lemma `isomorphic_distinguished` / 引理 `isomorphic_distinguished`

English:
lemma isomorphic_distinguished
  statement: (T₁ : Triangle Cᵒᵖ)
  proof: by
  simp only [mem_distinguishedTriangles_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

中文:
引理 isomorphic_distinguished
  结论: (T₁ : Triangle Cᵒᵖ)
  证明: by
  simp only [mem_distinguishedTriangles_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

Depends on / 依赖: Pretriangulated, Pretriangulated.isomorphic_distinguished, inverse, inverse.mapIso, isomorphic_distinguished, mapIso, mem_distinguishedTriangles_iff, triangleOpEquivalence, unop.symm
-/
lemma isomorphic_distinguished (T₁ : Triangle Cᵒᵖ)
    (hT₁ : T₁ in distinguishedTriangles C) (T₂ : Triangle Cᵒᵖ) (e : T₂ ≅ T₁) :
    T₂ in distinguishedTriangles C := by
  simp only [mem_distinguishedTriangles_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Up to rotation, the contractible triangle `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` for `X : Cᵒᵖ` corresponds
to the contractible triangle for `X.unop` in `C`. -/
@[simps!]
/--
Definition of `contractibleTriangleIso` / `contractibleTriangleIso` 的定义

English:
definition contractibleTriangleIso
  signature: (X : Cᵒᵖ)
  body: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (IsZero.iso (isZero_zero _) (by
      dsimp
      rw [IsZero.iff_id_eq_zero]
      change (𝟙 ((0 : C)⟦(-1 : Int)⟧)).op = 0
      rw [← Functor.map_id]; rw [id_zero]; rw [Functor.map_zero]; rw [op_zero]))
    (by simp) (by simp) (by simp)

中文:
定义 contractibleTriangleIso
  签名: (X : Cᵒᵖ)
  定义体: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (IsZero.iso (isZero_zero _) (by
      dsimp
      rw [IsZero.iff_id_eq_zero]
      change (𝟙 ((0 : C)⟦(-1 : Int)⟧)).op = 0
      rw [← Functor.map_id]; rw [id_zero]; rw [Functor.map_zero]; rw [op_zero]))
    (by simp) (by simp) (by simp)

Depends on / 依赖: Functor, Functor.map_id, Functor.map_zero, IsZero, IsZero.iff_id_eq_zero, IsZero.iso, Iso.refl, Triangle, Triangle.isoMk, id_zero, iff_id_eq_zero, isZero_zero, map_id, map_zero, op_zero
-/
noncomputable def contractibleTriangleIso (X : Cᵒᵖ) :
    contractibleTriangle X ≅ (triangleOpEquivalence C).functor.obj
      (Opposite.op (contractibleTriangle X.unop).invRotate) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (IsZero.iso (isZero_zero _) (by
      dsimp
      rw [IsZero.iff_id_eq_zero]
      change (𝟙 ((0 : C)⟦(-1 : Int)⟧)).op = 0
      rw [← Functor.map_id]; rw [id_zero]; rw [Functor.map_zero]; rw [op_zero]))
    (by simp) (by simp) (by simp)

/--
lemma `contractible_distinguished` / 引理 `contractible_distinguished`

English:
lemma contractible_distinguished
  given: (X : Cᵒᵖ)
  proof: by
  rw [mem_distinguishedTriangles_iff']
  exact ⟨_, inv_rot_of_distTriang _ (Pretriangulated.contractible_distinguished X.unop),
    ⟨contractibleTriangleIso X⟩⟩

中文:
引理 contractible_distinguished
  条件: (X : Cᵒᵖ)
  证明: by
  rw [mem_distinguishedTriangles_iff']
  exact ⟨_, inv_rot_of_distTriang _ (Pretriangulated.contractible_distinguished X.unop),
    ⟨contractibleTriangleIso X⟩⟩

Depends on / 依赖: Pretriangulated, Pretriangulated.contractible_distinguished, X.unop, contractibleTriangleIso, contractible_distinguished, inv_rot_of_distTriang, mem_distinguishedTriangles_iff
-/
lemma contractible_distinguished (X : Cᵒᵖ) :
    contractibleTriangle X in distinguishedTriangles C := by
  rw [mem_distinguishedTriangles_iff']
  exact ⟨_, inv_rot_of_distTriang _ (Pretriangulated.contractible_distinguished X.unop),
    ⟨contractibleTriangleIso X⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rotateTriangleOpEquivalenceInverseObjRotateUnopIso` / `rotateTriangleOpEquivalenceInverseObjRotateUnopIso` 的定义

English:
definition rotateTriangleOpEquivalenceInverseObjRotateUnopIso
  signature: (T : Triangle Cᵒᵖ)
  body: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (-((opShiftFunctorEquivalence C 1).unitIso.app T.obj₁).unop) (by simp)
        (Quiver.Hom.op_inj (by simp)) (by simp)

中文:
定义 rotateTriangleOpEquivalenceInverseObjRotateUnopIso
  签名: (T : Triangle Cᵒᵖ)
  定义体: Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (-((opShiftFunctorEquivalence C 1).unitIso.app T.obj₁).unop) (by simp)
        (Quiver.Hom.op_inj (by simp)) (by simp)

Depends on / 依赖: Iso.refl, Quiver, Quiver.Hom.op_inj, T.obj, Triangle, Triangle.isoMk, opShiftFunctorEquivalence, op_inj, unitIso, unitIso.app
-/
noncomputable def rotateTriangleOpEquivalenceInverseObjRotateUnopIso (T : Triangle Cᵒᵖ) :
    ((triangleOpEquivalence C).inverse.obj T.rotate).unop.rotate ≅
      ((triangleOpEquivalence C).inverse.obj T).unop :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (-((opShiftFunctorEquivalence C 1).unitIso.app T.obj₁).unop) (by simp)
        (Quiver.Hom.op_inj (by simp)) (by simp)

/--
lemma `rotate_distinguished_triangle` / 引理 `rotate_distinguished_triangle`

English:
lemma rotate_distinguished_triangle
  given: (T : Triangle Cᵒᵖ)
  proof: by
  simp only [mem_distinguishedTriangles_iff, Pretriangulated.rotate_distinguished_triangle
    ((triangleOpEquivalence C).inverse.obj (T.rotate)).unop]
  exact distinguished_iff_of_iso (rotateTriangleOpEquivalenceInverseObjRotateUnopIso T).symm

中文:
引理 rotate_distinguished_triangle
  条件: (T : Triangle Cᵒᵖ)
  证明: by
  simp only [mem_distinguishedTriangles_iff, Pretriangulated.rotate_distinguished_triangle
    ((triangleOpEquivalence C).inverse.obj (T.rotate)).unop]
  exact distinguished_iff_of_iso (rotateTriangleOpEquivalenceInverseObjRotateUnopIso T).symm

Depends on / 依赖: Pretriangulated, Pretriangulated.rotate_distinguished_triangle, T.rotate, distinguished_iff_of_iso, inverse, inverse.obj, mem_distinguishedTriangles_iff, rotate, rotateTriangleOpEquivalenceInverseObjRotateUnopIso, rotate_distinguished_triangle, triangleOpEquivalence
-/
lemma rotate_distinguished_triangle (T : Triangle Cᵒᵖ) :
    T in distinguishedTriangles C ↔ T.rotate in distinguishedTriangles C := by
  simp only [mem_distinguishedTriangles_iff, Pretriangulated.rotate_distinguished_triangle
    ((triangleOpEquivalence C).inverse.obj (T.rotate)).unop]
  exact distinguished_iff_of_iso (rotateTriangleOpEquivalenceInverseObjRotateUnopIso T).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `distinguished_cocone_triangle` / 引理 `distinguished_cocone_triangle`

English:
lemma distinguished_cocone_triangle
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: by
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle₁ f.unop
  refine ⟨_, g.op, (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op Z) ≫
    (shiftFunctor Cᵒᵖ (1 : Int)).map h.op, ?_⟩
  simp only [mem_distinguishedTriangles_iff]
  refine Pretriangulated.isomorphic_dis

中文:
引理 distinguished_cocone_triangle
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: by
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle₁ f.unop
  refine ⟨_, g.op, (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op Z) ≫
    (shiftFunctor Cᵒᵖ (1 : Int)).map h.op, ?_⟩
  simp only [mem_distinguishedTriangles_iff]
  refine Pretriangulated.isomorphic_dis

Depends on / 依赖: Iso.refl, Opposite, Opposite.op, Pretriangulated, Pretriangulated.distinguished_cocone_triangle, Pretriangulated.isomorphic_distinguished, Quiver, Quiver.Hom.op_inj, Triangle, Triangle.isoMk, counitIso, counitIso.inv.app, f.unop, g.op, h.op, isomorphic_distinguished, mem_distinguishedTriangles_iff, opShiftFunctorEquivalence, op_inj, shiftFunctor
-/
lemma distinguished_cocone_triangle {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    exists (Z : Cᵒᵖ) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧),
      Triangle.mk f g h in distinguishedTriangles C := by
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle₁ f.unop
  refine ⟨_, g.op, (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op Z) ≫
    (shiftFunctor Cᵒᵖ (1 : Int)).map h.op, ?_⟩
  simp only [mem_distinguishedTriangles_iff]
  refine Pretriangulated.isomorphic_distinguished _ H _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (Quiver.Hom.op_inj (by simp [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `complete_distinguished_triangle_morphism` / 引理 `complete_distinguished_triangle_morphism`

English:
lemma complete_distinguished_triangle_morphism
  statement: (T₁ T₂ : Triangle Cᵒᵖ)
  proof: by
  rw [mem_distinguishedTriangles_iff] at hT₁ hT₂
  obtain ⟨c, hc₁, hc₂⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT₂ hT₁
      b.unop a.unop (Quiver.Hom.op_inj comm.symm)
  dsimp at c hc₁ hc₂
  replace hc₂ := ((opShiftFunctorEquivalence C 1).unitIso.hom.app T₂.obj₁).un

中文:
引理 complete_distinguished_triangle_morphism
  结论: (T₁ T₂ : Triangle Cᵒᵖ)
  证明: by
  rw [mem_distinguishedTriangles_iff] at hT₁ hT₂
  obtain ⟨c, hc₁, hc₂⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT₂ hT₁
      b.unop a.unop (Quiver.Hom.op_inj comm.symm)
  dsimp at c hc₁ hc₂
  replace hc₂ := ((opShiftFunctorEquivalence C 1).unitIso.hom.app T₂.obj₁).un

Depends on / 依赖: Iso.unop_hom_inv_id_app_assoc, Pretriangulated, Pretriangulated.complete_distinguished_triangle_morphism, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, a.unop, b.unop, c.op, comm.symm, map_injective, mem_distinguishedTriangles_iff, opShiftFunctorEquivalence, op_inj, replace, shiftFunctor, unitIso, unitIso.hom.app, unop_comp, unop_hom_inv_id_app_assoc
-/
lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle Cᵒᵖ)
    (hT₁ : T₁ in distinguishedTriangles C) (hT₂ : T₂ in distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    exists (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  rw [mem_distinguishedTriangles_iff] at hT₁ hT₂
  obtain ⟨c, hc₁, hc₂⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT₂ hT₁
      b.unop a.unop (Quiver.Hom.op_inj comm.symm)
  dsimp at c hc₁ hc₂
  replace hc₂ := ((opShiftFunctorEquivalence C 1).unitIso.hom.app T₂.obj₁).unop ≫= hc₂
  dsimp at hc₂
  simp only [assoc, Iso.unop_hom_inv_id_app_assoc] at hc₂
  refine ⟨c.op, Quiver.Hom.unop_inj hc₁.symm, Quiver.Hom.unop_inj ?_⟩
  apply (shiftFunctor C (1 : Int)).map_injective
  rw [unop_comp]; rw [unop_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Quiver.Hom.unop_op]; rw [hc₂]; rw [← unop_comp_assoc]; rw [← unop_comp_assoc]; rw [← opShiftFunctorEquivalence_unitIso_inv_naturality]
  simp

/-- The pretriangulated structure on the opposite category of
a pretriangulated category. It is a scoped instance, so that we need to
`open CategoryTheory.Pretriangulated.Opposite` in order to be able
to use it: the reason is that it relies on the definition of the shift
on the opposite category `Cᵒᵖ`, for which it is unclear whether it should
be a global instance or not. -/
noncomputable scoped instance : Pretriangulated Cᵒᵖ where
  distinguishedTriangles := distinguishedTriangles C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

end Opposite

variable {C}

/--
lemma `mem_distTriang_op_iff` / 引理 `mem_distTriang_op_iff`

English:
lemma mem_distTriang_op_iff
  given: (T : Triangle Cᵒᵖ)
  proof: by
  rfl

中文:
引理 mem_distTriang_op_iff
  条件: (T : Triangle Cᵒᵖ)
  证明: by
  rfl
-/
lemma mem_distTriang_op_iff (T : Triangle Cᵒᵖ) :
    (T in distTriang Cᵒᵖ) ↔ ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C := by
  rfl

/--
lemma `mem_distTriang_op_iff'` / 引理 `mem_distTriang_op_iff'`

English:
lemma mem_distTriang_op_iff'
  given: (T : Triangle Cᵒᵖ)
  proof: Opposite.mem_distinguishedTriangles_iff' T

中文:
引理 mem_distTriang_op_iff'
  条件: (T : Triangle Cᵒᵖ)
  证明: Opposite.mem_distinguishedTriangles_iff' T

Depends on / 依赖: Opposite, Opposite.mem_distinguishedTriangles_iff, mem_distinguishedTriangles_iff
-/
lemma mem_distTriang_op_iff' (T : Triangle Cᵒᵖ) :
    (T in distTriang Cᵒᵖ) ↔ exists (T' : Triangle C) (_ : T' in distTriang C),
      Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) :=
  Opposite.mem_distinguishedTriangles_iff' T

/--
lemma `op_distinguished` / 引理 `op_distinguished`

English:
lemma op_distinguished
  given: (T : Triangle C) (hT : T in distTriang C)
  proof: by
  rw [mem_distTriang_op_iff']
  exact ⟨T, hT, ⟨Iso.refl _⟩⟩

中文:
引理 op_distinguished
  条件: (T : Triangle C) (hT : T in distTriang C)
  证明: by
  rw [mem_distTriang_op_iff']
  exact ⟨T, hT, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl, mem_distTriang_op_iff
-/
lemma op_distinguished (T : Triangle C) (hT : T in distTriang C) :
    ((triangleOpEquivalence C).functor.obj (Opposite.op T)) in distTriang Cᵒᵖ := by
  rw [mem_distTriang_op_iff']
  exact ⟨T, hT, ⟨Iso.refl _⟩⟩

/--
lemma `unop_distinguished` / 引理 `unop_distinguished`

English:
lemma unop_distinguished
  given: (T : Triangle Cᵒᵖ) (hT : T in distTriang Cᵒᵖ)
  proof: hT

中文:
引理 unop_distinguished
  条件: (T : Triangle Cᵒᵖ) (hT : T in distTriang Cᵒᵖ)
  证明: hT
-/
lemma unop_distinguished (T : Triangle Cᵒᵖ) (hT : T in distTriang Cᵒᵖ) :
    ((triangleOpEquivalence C).inverse.obj T).unop in distTriang C := hT

end Pretriangulated

namespace Functor

open Pretriangulated.Opposite Pretriangulated

variable {C}

/--
lemma `map_distinguished_op_exact` / 引理 `map_distinguished_op_exact`

English:
lemma map_distinguished_op_exact
  statement: {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A)
  proof: F.map_distinguished_exact _ (op_distinguished T hT)

中文:
引理 map_distinguished_op_exact
  结论: {A : 类型} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A)
  证明: F.map_distinguished_exact _ (op_distinguished T hT)

Depends on / 依赖: F.map_distinguished_exact, map_distinguished_exact, op_distinguished
-/
lemma map_distinguished_op_exact {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A)
    [F.IsHomological] (T : Triangle C) (hT : T in distTriang C) :
    ((shortComplexOfDistTriangle T hT).op.map F).Exact :=
  F.map_distinguished_exact _ (op_distinguished T hT)

end Functor

end CategoryTheory
