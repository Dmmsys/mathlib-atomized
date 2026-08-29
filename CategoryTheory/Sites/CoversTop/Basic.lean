/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Objects which cover the terminal object

In this file, given a site `(C, J)`, we introduce the notion of a family
of objects `Y : I → C` which "cover the final object": this means
that for all `X : C`, the sieve `Sieve.ofObjects Y X` is covering for `J`.
When there is a terminal object `X : C`, then `J.CoversTop Y`
holds iff `Sieve.ofObjects Y X` is covering for `J`.

We introduce a notion of compatible family of elements on objects `Y`
and obtain `Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`
which asserts that if a presheaf of types is a sheaf, then any compatible
family of elements on objects `Y` which cover the final object extends to
a section of this presheaf.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A]

namespace GrothendieckTopology

/--
Definition of `CoversTop` / `CoversTop` 的定义

English:
definition CoversTop
  signature: {I : Type*} (Y : I -> C)
  body: forall (X : C), Sieve.ofObjects Y X in J X

中文:
定义 CoversTop
  签名: {I : 类型} (Y : I -> C)
  定义体: forall (X : C), Sieve.ofObjects Y X in J X

Depends on / 依赖: Sieve.ofObjects, ofObjects
-/
def CoversTop {I : Type*} (Y : I -> C) : Prop :=
  forall (X : C), Sieve.ofObjects Y X in J X

/--
lemma `coversTop_iff_of_isTerminal` / 引理 `coversTop_iff_of_isTerminal`

English:
lemma coversTop_iff_of_isTerminal
  statement: (X : C) (hX : IsTerminal X)
  proof: by
  constructor
  · tauto
  · intro h W
    apply J.superset_covering _ (J.pullback_stable (hX.from W) h)
    rintro T a ⟨i, ⟨b⟩⟩
    exact ⟨i, ⟨b⟩⟩

中文:
引理 coversTop_iff_of_isTerminal
  结论: (X : C) (hX : IsTerminal X)
  证明: by
  constructor
  · tauto
  · intro h W
    apply J.superset_covering _ (J.pullback_stable (hX.from W) h)
    rintro T a ⟨i, ⟨b⟩⟩
    exact ⟨i, ⟨b⟩⟩

Depends on / 依赖: J.pullback_stable, J.superset_covering, hX.from, pullback_stable, superset_covering
-/
lemma coversTop_iff_of_isTerminal (X : C) (hX : IsTerminal X)
    {I : Type*} (Y : I -> C) :
    J.CoversTop Y ↔ Sieve.ofObjects Y X in J X := by
  constructor
  · tauto
  · intro h W
    apply J.superset_covering _ (J.pullback_stable (hX.from W) h)
    rintro T a ⟨i, ⟨b⟩⟩
    exact ⟨i, ⟨b⟩⟩

namespace CoversTop

variable {J}
variable {I : Type*} {Y : I -> C} (hY : J.CoversTop Y)
include hY

/--
Definition of `cover` / `cover` 的定义

English:
abbreviation cover
  signature: (W : C)
  body: ⟨Sieve.ofObjects Y W, hY W⟩

中文:
缩写 cover
  签名: (W : C)
  定义体: ⟨Sieve.ofObjects Y W, hY W⟩

Depends on / 依赖: Sieve.ofObjects, ofObjects
-/
abbrev cover (W : C) : Cover J W := ⟨Sieve.ofObjects Y W, hY W⟩

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.pt}
  proof: by
  refine hc.hom_ext (fun Z => F.2.hom_ext (hY.cover Z.unop) _ _ ?_)
  rintro ⟨W, a, ⟨i, ⟨b⟩⟩⟩
  simpa using h i =≫ F.1.map b.op

中文:
引理 ext
  结论: (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.pt}
  证明: by
  refine hc.hom_ext (fun Z => F.2.hom_ext (hY.cover Z.unop) _ _ ?_)
  rintro ⟨W, a, ⟨i, ⟨b⟩⟩⟩
  simpa using h i =≫ F.1.map b.op

Depends on / 依赖: Z.unop, b.op, hY.cover, hc.hom_ext, hom_ext
-/
lemma ext (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.pt}
    (h : forall (i : I), f ≫ c.π.app (Opposite.op (Y i)) =
      g ≫ c.π.app (Opposite.op (Y i))) :
    f = g := by
  refine hc.hom_ext (fun Z => F.2.hom_ext (hY.cover Z.unop) _ _ ?_)
  rintro ⟨W, a, ⟨i, ⟨b⟩⟩⟩
  simpa using h i =≫ F.1.map b.op

/--
lemma `sections_ext` / 引理 `sections_ext`

English:
lemma sections_ext
  statement: (F : Sheaf J Type*) {x y : F.1.sections}
  proof: by
  ext W
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 F.2).isSeparated _ (hY W.unop)).ext
  rintro T a ⟨i, ⟨b⟩⟩
  simpa using congr_arg (F.1.map b.op) (h i)

中文:
引理 sections_ext
  结论: (F : Sheaf J 类型) {x y : F.1.sections}
  证明: by
  ext W
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 F.2).isSeparated _ (hY W.unop)).ext
  rintro T a ⟨i, ⟨b⟩⟩
  simpa using congr_arg (F.1.map b.op) (h i)

Depends on / 依赖: W.unop, b.op, congr_arg, isSeparated, isSheaf_iff_isSheaf_of_type
-/
lemma sections_ext (F : Sheaf J Type*) {x y : F.1.sections}
    (h : forall (i : I), x.1 (Opposite.op (Y i)) = y.1 (Opposite.op (Y i))) :
    x = y := by
  ext W
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 F.2).isSeparated _ (hY W.unop)).ext
  rintro T a ⟨i, ⟨b⟩⟩
  simpa using congr_arg (F.1.map b.op) (h i)

end CoversTop

end GrothendieckTopology

namespace Presheaf

variable (F : Cᵒᵖ ⥤ Type w) {I : Type*} (Y : I -> C)

/--
Definition of `FamilyOfElementsOnObjects` / `FamilyOfElementsOnObjects` 的定义

English:
definition FamilyOfElementsOnObjects
  body: forall (i : I), F.obj (Opposite.op (Y i))

中文:
定义 FamilyOfElementsOnObjects
  定义体: forall (i : I), F.obj (Opposite.op (Y i))

Depends on / 依赖: F.obj, Opposite, Opposite.op
-/
def FamilyOfElementsOnObjects := forall (i : I), F.obj (Opposite.op (Y i))

namespace FamilyOfElementsOnObjects

variable {F Y}
variable (x : FamilyOfElementsOnObjects F Y)

/--
Definition of `IsCompatible` / `IsCompatible` 的定义

English:
definition IsCompatible
  signature: (x : FamilyOfElementsOnObjects F Y)
  body: forall (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
    F.map f.op (x i) = F.map g.op (x j)

中文:
定义 IsCompatible
  签名: (x : FamilyOfElementsOnObjects F Y)
  定义体: forall (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
    F.map f.op (x i) = F.map g.op (x j)

Depends on / 依赖: F.map, f.op, g.op
-/
def IsCompatible (x : FamilyOfElementsOnObjects F Y) : Prop :=
  forall (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
    F.map f.op (x i) = F.map g.op (x j)

/--
Definition of `familyOfElements` / `familyOfElements` 的定义

English:
definition familyOfElements
  signature: (X : C)
  body: fun _ _ hf => F.map hf.choose_spec.some.op (x _)

中文:
定义 familyOfElements
  签名: (X : C)
  定义体: fun _ _ hf => F.map hf.choose_spec.some.op (x _)

Depends on / 依赖: Arborescence, Arborescence.uniquePath, F.map, choose_spec, hf.choose_spec.some.op, uniquePath
-/
noncomputable def familyOfElements (X : C) :
    Presieve.FamilyOfElements F (Sieve.ofObjects Y X).arrows :=
  fun _ _ hf => F.map hf.choose_spec.some.op (x _)

namespace IsCompatible

variable {x}

/--
lemma `familyOfElements_apply` / 引理 `familyOfElements_apply`

English:
lemma familyOfElements_apply
  given: (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X) (i : I) (φ : Z ⟶ Y i)
  proof: by
  apply hx

中文:
引理 familyOfElements_apply
  条件: (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X) (i : I) (φ : Z ⟶ Y i)
  证明: by
  apply hx
-/
lemma familyOfElements_apply (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X) (i : I) (φ : Z ⟶ Y i) :
    familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i) := by
  apply hx

/--
lemma `familyOfElements_isCompatible` / 引理 `familyOfElements_isCompatible`

English:
lemma familyOfElements_isCompatible
  given: (hx : x.IsCompatible) (X : C)
  proof: by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i₁, ⟨φ₁⟩⟩ ⟨i₂, ⟨φ₂⟩⟩ _
  simpa [hx.familyOfElements_apply f₁ i₁ φ₁,
    hx.familyOfElements_apply f₂ i₂ φ₂] using hx Z i₁ i₂ (g₁ ≫ φ₁) (g₂ ≫ φ₂)

中文:
引理 familyOfElements_isCompatible
  条件: (hx : x.IsCompatible) (X : C)
  证明: by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i₁, ⟨φ₁⟩⟩ ⟨i₂, ⟨φ₂⟩⟩ _
  simpa [hx.familyOfElements_apply f₁ i₁ φ₁,
    hx.familyOfElements_apply f₂ i₂ φ₂] using hx Z i₁ i₂ (g₁ ≫ φ₁) (g₂ ≫ φ₂)

Depends on / 依赖: familyOfElements_apply, hx.familyOfElements_apply
-/
lemma familyOfElements_isCompatible (hx : x.IsCompatible) (X : C) :
    (familyOfElements x X).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i₁, ⟨φ₁⟩⟩ ⟨i₂, ⟨φ₂⟩⟩ _
  simpa [hx.familyOfElements_apply f₁ i₁ φ₁,
    hx.familyOfElements_apply f₂ i₂ φ₂] using hx Z i₁ i₂ (g₁ ≫ φ₁) (g₂ ≫ φ₂)

variable {J}

/--
lemma `existsUnique_section` / 引理 `existsUnique_section`

English:
lemma existsUnique_section
  given: (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F)
  proof: by
  have H := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  apply existsUnique_of_exists_of_unique
  · let s := fun (X : C) => (H _ (hY X)).amalgamate _
      (hx.familyOfElements_isCompatible X)
    have hs : forall {X : C} (i : I) (f : X ⟶ Y i), s X = F.map f.op (x i) := fun {X} i f => by
      have h

中文:
引理 existsUnique_section
  条件: (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F)
  证明: by
  have H := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  apply existsUnique_of_exists_of_unique
  · let s := fun (X : C) => (H _ (hY X)).amalgamate _
      (hx.familyOfElements_isCompatible X)
    have hs : forall {X : C} (i : I) (f : X ⟶ Y i), s X = F.map f.op (x i) := fun {X} i f => by
      have h

Depends on / 依赖: F.map, F.map_id, IsSheafFor, Presieve, Presieve.IsSheafFor.valid_glue, amalgamate, existsUnique_of_exists_of_unique, f.op, familyOfElements_apply, familyOfElements_isCompatible, h.trans, hx.familyOfElements_apply, hx.familyOfElements_isCompatible, isSheaf_iff_isSheaf_of_type, map_id, op_id, types_id_apply, valid_glue
-/
lemma existsUnique_section (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F) :
    exists! (s : F.sections), forall (i : I), s.1 (Opposite.op (Y i)) = x i := by
  have H := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  apply existsUnique_of_exists_of_unique
  · let s := fun (X : C) => (H _ (hY X)).amalgamate _
      (hx.familyOfElements_isCompatible X)
    have hs : forall {X : C} (i : I) (f : X ⟶ Y i), s X = F.map f.op (x i) := fun {X} i f => by
      have h := Presieve.IsSheafFor.valid_glue (H _ (hY X))
          (hx.familyOfElements_isCompatible _) (𝟙 _) ⟨i, ⟨f⟩⟩
      simp only [op_id, F.map_id, types_id_apply] at h
      exact h.trans (hx.familyOfElements_apply _ _ _)
    have hs' : forall {W X : C} (a : W ⟶ X) (i : I) (_ : W ⟶ Y i), F.map a.op (s X) = s W := by
      intro W X a i b
      rw [hs i b]
      exact (Presieve.IsSheafFor.valid_glue (H _ (hY X))
        (hx.familyOfElements_isCompatible _) a ⟨i, ⟨b⟩⟩).trans (familyOfElements_apply hx _ _ _)
    refine ⟨⟨fun X => s X.unop, ?_⟩, fun i => (hs i (𝟙 (Y i))).trans (by simp)⟩
    rintro ⟨Y₁⟩ ⟨Y₂⟩ ⟨f : Y₂ ⟶ Y₁⟩
    change F.map f.op (s Y₁) = s Y₂
    apply (H.isSeparated _ (hY Y₂)).ext
    rintro Z φ ⟨i, ⟨g⟩⟩
    rw [hs' φ i g]; rw [← hs' (φ ≫ f) i g]; rw [op_comp]; rw [F.map_comp]
    rfl
  · intro y₁ y₂ hy₁ hy₂
    exact hY.sections_ext ⟨F, hF⟩ (fun i => by rw [hy₁, hy₂])

variable (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F)

/--
Definition of `section_` / `section_` 的定义

English:
definition section_
  signature: : F.sections
  body: (hx.existsUnique_section hY hF).choose

@[simp]

中文:
定义 section_
  签名: : F.sections
  定义体: (hx.existsUnique_section hY hF).choose

@[simp]

Depends on / 依赖: existsUnique_section, hx.existsUnique_section
-/
noncomputable def section_ : F.sections := (hx.existsUnique_section hY hF).choose

@[simp]
/--
lemma `section_apply` / 引理 `section_apply`

English:
lemma section_apply
  given: (i : I)
  statement: (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i
  proof: (hx.existsUnique_section hY hF).choose_spec.1 i

中文:
引理 section_apply
  条件: (i : I)
  结论: (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i
  证明: (hx.existsUnique_section hY hF).choose_spec.1 i

Depends on / 依赖: choose_spec, existsUnique_section, hx.existsUnique_section
-/
lemma section_apply (i : I) : (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i :=
  (hx.existsUnique_section hY hF).choose_spec.1 i

end IsCompatible

end FamilyOfElementsOnObjects

end Presheaf

end CategoryTheory
