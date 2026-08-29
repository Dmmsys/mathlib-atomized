/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final

/-!
# Action of an initial functor on sections

Given `F : C ⥤ D` and `P : D ⥤ Type w`, we define a map
`sectionsPrecomp F : P.sections → (F ⋙ P).sections` and
show that it is a bijection when `F` is initial.
As `Functor.sections` identify to limits of functors to types
(at least under suitable universe assumptions), this could
be deduced from general results about limits and
initial functors, but we provide a more down to earth proof.

We also obtain the dual result that if `F` is final,
then `F.colimitTypePrecomp : (F ⋙ P).ColimitType → P.ColimitType`
is a bijection.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- When `F : C ⥤ D` and `P : D ⥤ Type _`, this is the obvious map
`P.sections → (F ⋙ P).sections`. -/
@[simps]
/--
Definition of `sectionsPrecomp` / `sectionsPrecomp` 的定义

English:
definition sectionsPrecomp
  signature: (F : C ⥤ D) {P : D ⥤ Type w} (x : P.sections)
  body: x.val _
  property _ := x.property _

中文:
定义 sectionsPrecomp
  签名: (F : C ⥤ D) {P : D ⥤ 类型 w} (x : P.sections)
  定义体: x.val _
  property _ := x.property _

Depends on / 依赖: x.val
-/
def sectionsPrecomp (F : C ⥤ D) {P : D ⥤ Type w} (x : P.sections) :
    (F ⋙ P).sections where
  val _ := x.val _
  property _ := x.property _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `bijective_sectionsPrecomp` / 引理 `bijective_sectionsPrecomp`

English:
lemma bijective_sectionsPrecomp
  given: (F : C ⥤ D) (P : D ⥤ Type w) [F.Initial]
  proof: by
  refine ⟨fun s₁ s₂ h => ?_, fun t => ?_⟩
  · ext Y
    let X : CostructuredArrow F Y := Classical.arbitrary _
    have := congr_fun (congr_arg Subtype.val h) X.left
    have h₁ := s₁.property X.hom
    have h₂ := s₂.property X.hom
    dsimp at this h₁ h₂
    rw [← h₁]; rw [this]; rw [h₂]
  · hav

中文:
引理 bijective_sectionsPrecomp
  条件: (F : C ⥤ D) (P : D ⥤ 类型 w) [F.初始]
  证明: by
  refine ⟨fun s₁ s₂ h => ?_, fun t => ?_⟩
  · ext Y
    let X : CostructuredArrow F Y := Classical.arbitrary _
    have := congr_fun (congr_arg Subtype.val h) X.left
    have h₁ := s₁.property X.hom
    have h₂ := s₂.property X.hom
    dsimp at this h₁ h₂
    rw [← h₁]; rw [this]; rw [h₂]
  · hav

Depends on / 依赖: Classical, Classical.arbitrary, CostructuredArrow, P.map, P.obj, Subtype, Subtype.val, X.hom, X.left, arbitrary, comp_apply, congr_arg, congr_fun, constant_of_preserves_morphisms, j.hom, j.left, property, t.property, t.val
-/
lemma bijective_sectionsPrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Initial] :
    Function.Bijective (F.sectionsPrecomp (P := P)) := by
  refine ⟨fun s₁ s₂ h => ?_, fun t => ?_⟩
  · ext Y
    let X : CostructuredArrow F Y := Classical.arbitrary _
    have := congr_fun (congr_arg Subtype.val h) X.left
    have h₁ := s₁.property X.hom
    have h₂ := s₂.property X.hom
    dsimp at this h₁ h₂
    rw [← h₁]; rw [this]; rw [h₂]
  · have h (Y : D) : exists (a : P.obj Y),
        forall (j : CostructuredArrow F Y), P.map j.hom (t.val j.left) = a := by
      apply constant_of_preserves_morphisms'
      intro Z₁ Z₂ φ
      dsimp
      rw [← t.property φ.left]
      dsimp
      rw [← comp_apply]; rw [← Functor.map_comp]; rw [CostructuredArrow.w]
    choose val hval using h
    refine ⟨⟨val, fun {Y₁ Y₂} f => ?_⟩, ?_⟩
    · let X : CostructuredArrow F Y₁ := Classical.arbitrary _
      simp [← hval Y₁ X, ← hval Y₂ ((CostructuredArrow.map f).obj X)]
    · ext X : 2
      simpa using (hval (F.obj X) (CostructuredArrow.mk (𝟙 _))).symm

/--
Definition of `colimitTypePrecomp` / `colimitTypePrecomp` 的定义

English:
definition colimitTypePrecomp
  signature: (F : C ⥤ D) (P : D ⥤ Type w)
  body: (F ⋙ P).descColimitType (P.coconeTypes.precomp F)

@[simp]

中文:
定义 colimitTypePrecomp
  签名: (F : C ⥤ D) (P : D ⥤ 类型 w)
  定义体: (F ⋙ P).descColimitType (P.coconeTypes.precomp F)

@[simp]

Depends on / 依赖: P.coconeTypes.precomp, coconeTypes, descColimitType, precomp
-/
def colimitTypePrecomp (F : C ⥤ D) (P : D ⥤ Type w) :
    (F ⋙ P).ColimitType -> P.ColimitType :=
  (F ⋙ P).descColimitType (P.coconeTypes.precomp F)

@[simp]
/--
lemma `colimitTypePrecomp_ιColimitType` / 引理 `colimitTypePrecomp_ιColimitType`

English:
lemma colimitTypePrecomp_ιColimitType
  statement: (F : C ⥤ D) {P : D ⥤ Type w}
  proof: rfl

中文:
引理 colimitTypePrecomp_ιColimitType
  结论: (F : C ⥤ D) {P : D ⥤ 类型 w}
  证明: rfl
-/
lemma colimitTypePrecomp_ιColimitType (F : C ⥤ D) {P : D ⥤ Type w}
    (i : C) (x : P.obj (F.obj i)) :
    colimitTypePrecomp F P ((F ⋙ P).ιColimitType i x) = P.ιColimitType (F.obj i) x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `bijective_colimitTypePrecomp` / 引理 `bijective_colimitTypePrecomp`

English:
lemma bijective_colimitTypePrecomp
  given: (F : C ⥤ D) (P : D ⥤ Type w) [F.Final]
  proof: by
  refine ⟨?_, fun x => ?_⟩
  · have h (Y : D) : exists (a : P.obj Y -> (F ⋙ P).ColimitType), forall (j : StructuredArrow Y F),
        (F ⋙ P).ιColimitType j.right ∘ P.map j.hom = a := by
      apply constant_of_preserves_morphisms'
      intro Z₁ Z₂ f
      ext x
      dsimp
      rw [← (F ⋙ P).

中文:
引理 bijective_colimitTypePrecomp
  条件: (F : C ⥤ D) (P : D ⥤ 类型 w) [F.终]
  证明: by
  refine ⟨?_, fun x => ?_⟩
  · have h (Y : D) : exists (a : P.obj Y -> (F ⋙ P).ColimitType), forall (j : StructuredArrow Y F),
        (F ⋙ P).ιColimitType j.right ∘ P.map j.hom = a := by
      apply constant_of_preserves_morphisms'
      intro Z₁ Z₂ f
      ext x
      dsimp
      rw [← (F ⋙ P).

Depends on / 依赖: CoconeTypes, ColimitType, Functor, Functor.map_comp, P.CoconeTypes, P.map, P.obj, StructuredArrow, comp_apply, comp_map, constant_of_preserves_morphisms, f.right, j.hom, j.right, map_comp
-/
lemma bijective_colimitTypePrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Final] :
    Function.Bijective (F.colimitTypePrecomp (P := P)) := by
  refine ⟨?_, fun x => ?_⟩
  · have h (Y : D) : exists (a : P.obj Y -> (F ⋙ P).ColimitType), forall (j : StructuredArrow Y F),
        (F ⋙ P).ιColimitType j.right ∘ P.map j.hom = a := by
      apply constant_of_preserves_morphisms'
      intro Z₁ Z₂ f
      ext x
      dsimp
      rw [← (F ⋙ P).ιColimitType_map f.right]; rw [comp_map]
      simp [← comp_apply, ← Functor.map_comp]
    choose φ hφ using h
    let c : P.CoconeTypes :=
      { pt := (F ⋙ P).ColimitType
        ι Y := φ Y
        ι_naturality {Y₁ Y₂} f := by
          ext
          have X : StructuredArrow Y₂ F := Classical.arbitrary _
          rw [← hφ Y₂ X]; rw [← hφ Y₁ ((StructuredArrow.map f).obj X)]
          simp }
    refine Function.RightInverse.injective (g := (P.descColimitType c)) (fun x => ?_)
    obtain ⟨X, x, rfl⟩ := (F ⋙ P).ιColimitType_jointly_surjective x
    simp [c, ← hφ (F.obj X) (StructuredArrow.mk (𝟙 _))]
  · obtain ⟨X, x, rfl⟩ := P.ιColimitType_jointly_surjective x
    let Y : StructuredArrow X F := Classical.arbitrary _
    exact ⟨(F ⋙ P).ιColimitType Y.right (P.map Y.hom x), by simp⟩

end Functor

end CategoryTheory
