/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Presentation of a colimit of objects equipped with a presentation

## Main definition:
- `CategoryTheory.Limits.ColimitPresentation.bind`: Given a colimit presentation of `X` and
  colimit presentations of the components, this is the colimit presentation over the sigma type.

-/

@[expose] public section

universe s t w v u

namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C]

variable {J : Type*} {I : J -> Type*} [Category* J] [forall j, Category (I j)]
  {D : J ⥤ C} {P : forall j, ColimitPresentation (I j) (D.obj j)}

set_option linter.unusedVariables false in
/-- The type underlying the category used in the construction of the composition
of colimit presentations. This is simply `Σ j, I j` but with a different category structure. -/
@[nolint unusedArguments]
/--
Definition of `Total` / `Total` 的定义

English:
definition Total
  signature: (P : forall j, ColimitPresentation (I j) (D.obj j))
  body: Σ j, I j

中文:
定义 Total
  签名: (P : 对任意 j, ColimitPresentation (I j) (D.obj j))
  定义体: Σ j, I j
-/
def Total (P : forall j, ColimitPresentation (I j) (D.obj j)) : Type _ :=
  Σ j, I j

variable (P) in
/--
Definition of `Total.mk` / `Total.mk` 的定义

English:
abbreviation Total.mk
  signature: (i : J) (k : I i)
  body: ⟨i, k⟩

中文:
缩写 Total.mk
  签名: (i : J) (k : I i)
  定义体: ⟨i, k⟩
-/
abbrev Total.mk (i : J) (k : I i) : Total P := ⟨i, k⟩

/-- Morphisms in the `Total` category. -/
@[ext]
/--
Definition of `Total.Hom` / `Total.Hom` 的定义

English:
structure Total.Hom
  parameters: (k l : Total P)
  axioms and operations (3):
    - base : k.1 ⟶ l.1
    - hom : (P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2
    - w : (P k.1).ι.app k.2 ≫ D.map base = hom ≫ (P l.1).ι.app l.2  [default: by cat_disch]

中文:
结构 Total.Hom
  参数: (k l : Total P)
  公理与运算 (3 个):
    - base : k.1 ⟶ l.1
    - hom : (P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2
    - w : (P k.1).ι.app k.2 ≫ D.map base = hom ≫ (P l.1).ι.app l.2  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Total.Hom (k l : Total P) where
  /-- The underlying morphism in the first component. -/
  base : k.1 ⟶ l.1
  /-- A morphism in `C`. -/
  hom : (P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2
  w : (P k.1).ι.app k.2 ≫ D.map base = hom ≫ (P l.1).ι.app l.2 := by cat_disch

set_option backward.isDefEq.respectTransparency false in -- This is needed below
attribute [reassoc] Total.Hom.w

set_option backward.isDefEq.respectTransparency false in
/-- Composition of morphisms in the `Total` category. -/
@[simps]
/--
Definition of `Total.Hom.comp` / `Total.Hom.comp` 的定义

English:
definition Total.Hom.comp
  signature: {k l m : Total P} (f : k.Hom l) (g : l.Hom m)
  body: f.base ≫ g.base
  hom := f.hom ≫ g.hom
  w := by
    simp only [Functor.map_comp, Category.assoc]
    rw [f.w_assoc]; rw [g.w]

中文:
定义 Total.Hom.comp
  签名: {k l m : Total P} (f : k.Hom l) (g : l.Hom m)
  定义体: f.base ≫ g.base
  hom := f.hom ≫ g.hom
  w := by
    simp only [Functor.map_comp, Category.assoc]
    rw [f.w_assoc]; rw [g.w]

Depends on / 依赖: f.base, g.base
-/
def Total.Hom.comp {k l m : Total P} (f : k.Hom l) (g : l.Hom m) : k.Hom m where
  base := f.base ≫ g.base
  hom := f.hom ≫ g.hom
  w := by
    simp only [Functor.map_comp, Category.assoc]
    rw [f.w_assoc]; rw [g.w]

set_option backward.defeqAttrib.useBackward true in
@[simps! id_base id_hom comp_base comp_hom]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Total P)
  body: Total.Hom
  id _ := { base := 𝟙 _, hom := 𝟙 _ }
  comp := Total.Hom.comp

中文:
实例 :
  签名: Category (Total P)
  定义体: Total.Hom
  id _ := { base := 𝟙 _, hom := 𝟙 _ }
  comp := Total.Hom.comp

Depends on / 依赖: Total.Hom
-/
instance : Category (Total P) where
  Hom := Total.Hom
  id _ := { base := 𝟙 _, hom := 𝟙 _ }
  comp := Total.Hom.comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] [LocallySmall.{w} J] : LocallySmall.{w} (Total P) where
  body: let f (x : k ⟶ l) : (k.1 ⟶ l.1) × ((P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2) :=
      (x.base, x.hom)
    small_of_injective (f := f) (by grind [Function.Injective, Total.Hom.ext])

中文:
实例 [LocallySmall.{w}
  签名: C] [LocallySmall.{w} J] : LocallySmall.{w} (Total P) where
  定义体: let f (x : k ⟶ l) : (k.1 ⟶ l.1) × ((P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2) :=
      (x.base, x.hom)
    small_of_injective (f := f) (by grind [Function.Injective, Total.Hom.ext])

Depends on / 依赖: Function, Function.Injective, Injective, Total.Hom.ext, diag.obj, small_of_injective, x.base, x.hom
-/
instance [LocallySmall.{w} C] [LocallySmall.{w} J] : LocallySmall.{w} (Total P) where
  hom_small k l :=
    let f (x : k ⟶ l) : (k.1 ⟶ l.1) × ((P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2) :=
      (x.base, x.hom)
    small_of_injective (f := f) (by grind [Function.Injective, Total.Hom.ext])

section Small

variable {J : Type w} {I : J -> Type w} [SmallCategory J] [forall j, SmallCategory (I j)]
  {D : J ⥤ C} {P : forall j, ColimitPresentation (I j) (D.obj j)}

/--
lemma `Total.exists_hom_of_hom` / 引理 `Total.exists_hom_of_hom`

English:
lemma Total.exists_hom_of_hom
  statement: {j j' : J} (i : I j) (u : j ⟶ j')
  proof: by
  obtain ⟨i', q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (P j').isColimit
    ((P j).ι.app i ≫ D.map u)
  use i', { base := u, hom := q, w := by simp [← hq] }

中文:
引理 Total.exists_hom_of_hom
  结论: {j j' : J} (i : I j) (u : j ⟶ j')
  证明: by
  obtain ⟨i', q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (P j').isColimit
    ((P j).ι.app i ≫ D.map u)
  use i', { base := u, hom := q, w := by simp [← hq] }

Depends on / 依赖: D.map, IsFinitelyPresentable, IsFinitelyPresentable.exists_hom_of_isColimit, exists_hom_of_isColimit, isColimit
-/
lemma Total.exists_hom_of_hom {j j' : J} (i : I j) (u : j ⟶ j')
    [IsFiltered (I j')] [IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    exists (i' : I j') (f : Total.mk P j i ⟶ Total.mk P j' i'), f.base = u := by
  obtain ⟨i', q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (P j').isColimit
    ((P j).ι.app i ≫ D.map u)
  use i', { base := u, hom := q, w := by simp [← hq] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: J] [forall j, IsFiltered (I j)] : Nonempty (Total P)
  body: by
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨i⟩ : Nonempty (I j) := IsFiltered.nonempty
  exact ⟨⟨j, i⟩⟩

中文:
实例 [IsFiltered
  签名: J] [对任意 j, IsFiltered (I j)] : Nonempty (Total P)
  定义体: by
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨i⟩ : Nonempty (I j) := IsFiltered.nonempty
  exact ⟨⟨j, i⟩⟩

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, Nonempty, nonempty
-/
instance [IsFiltered J] [forall j, IsFiltered (I j)] : Nonempty (Total P) := by
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨i⟩ : Nonempty (I j) := IsFiltered.nonempty
  exact ⟨⟨j, i⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: J] [forall j, IsFiltered (I j)]
  body: by
    let a := IsFiltered.max k.1 l.1
    obtain ⟨a', f, hf⟩ := Total.exists_hom_of_hom (P := P) k.2 (IsFiltered.leftToMax k.1 l.1)
    obtain ⟨b', g, hg⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.rightToMax k.1 l.1)
    refine ⟨⟨a, IsFiltered.max a' b'⟩, ?_, ?_, trivial⟩
    · exact f ≫ 

中文:
实例 [IsFiltered
  签名: J] [对任意 j, IsFiltered (I j)]
  定义体: by
    let a := IsFiltered.max k.1 l.1
    obtain ⟨a', f, hf⟩ := Total.exists_hom_of_hom (P := P) k.2 (IsFiltered.leftToMax k.1 l.1)
    obtain ⟨b', g, hg⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.rightToMax k.1 l.1)
    refine ⟨⟨a, IsFiltered.max a' b'⟩, ?_, ?_, trivial⟩
    · exact f ≫ 

Depends on / 依赖: IsFiltered, IsFiltered.coeq, IsFiltered.leftToMax, IsFiltered.max, IsFiltered.rightToMax, Total.exists_hom_of_hom, cocone_maps, diag.map, exists_hom_of_hom, f.base, g.base, leftToMax, rightToMax
-/
instance [IsFiltered J] [forall j, IsFiltered (I j)]
    [forall j i, IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    IsFiltered (Total P) where
  cocone_objs k l := by
    let a := IsFiltered.max k.1 l.1
    obtain ⟨a', f, hf⟩ := Total.exists_hom_of_hom (P := P) k.2 (IsFiltered.leftToMax k.1 l.1)
    obtain ⟨b', g, hg⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.rightToMax k.1 l.1)
    refine ⟨⟨a, IsFiltered.max a' b'⟩, ?_, ?_, trivial⟩
    · exact f ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.leftToMax _ _) }
    · exact g ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.rightToMax _ _) }
  cocone_maps {k l} f g := by
    let a := IsFiltered.coeq f.base g.base
    obtain ⟨a', u, hu⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.coeqHom f.base g.base)
    have : (f.hom ≫ u.hom) ≫ (P _).ι.app _ = (g.hom ≫ u.hom) ≫ (P _).ι.app _ := by
      simp only [Category.assoc, Functor.const_obj_obj, ← u.w, ← f.w_assoc, ← g.w_assoc]
      rw [← Functor.map_comp]; rw [hu]; rw [IsFiltered.coeq_condition f.base g.base]
      simp
    obtain ⟨j, p, q, hpq⟩ := IsFinitelyPresentable.exists_eq_of_isColimit (P _).isColimit _ _ this
    dsimp at p q
    refine ⟨⟨a, IsFiltered.coeq p q⟩,
      u ≫ { base := 𝟙 _, hom := (P _).diag.map (p ≫ IsFiltered.coeqHom p q) }, ?_⟩
    apply Total.Hom.ext
    · simp [hu, IsFiltered.coeq_condition f.base g.base]
    · rw [Category.assoc] at hpq
      simp only [Functor.map_comp, comp_hom, reassoc_of% hpq]
      simp [← Functor.map_comp, ← IsFiltered.coeq_condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `P` is a colimit presentation over `J` of `X` and for every `j` we are given a colimit
presentation `Qⱼ` over `I j` of the `P.diag.obj j`, this is the refined colimit presentation of `X`
over `Total Q`. -/
@[simps]
/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: {X : C} (P : ColimitPresentation J X) (Q : forall j, ColimitPresentation (I j) (P.diag.obj j))
  body: (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  ι.app k := (Q k.1).ι.app k.2 ≫ P.ι.app k.1
  ι.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
       

中文:
定义 bind
  签名: {X : C} (P : ColimitPresentation J X) (Q : 对任意 j, ColimitPresentation (I j) (P.diag.obj j))
  定义体: (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  ι.app k := (Q k.1).ι.app k.2 ≫ P.ι.app k.1
  ι.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
       

Depends on / 依赖: diag.obj
-/
def bind {X : C} (P : ColimitPresentation J X) (Q : forall j, ColimitPresentation (I j) (P.diag.obj j))
    [forall j, IsFiltered (I j)] [forall j i, IsFinitelyPresentable.{w} ((Q j).diag.obj i)] :
    ColimitPresentation (Total Q) X where
  diag.obj k := (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  ι.app k := (Q k.1).ι.app k.2 ≫ P.ι.app k.1
  ι.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
          ι.naturality {i i'} u := by
            let v : Total.mk Q j i ⟶ .mk _ j i' := { base := 𝟙 _, hom := (Q _).diag.map u }
            simpa using c.ι.naturality v }
      ι.naturality {j j'} u := by
        refine (Q j).isColimit.hom_ext fun i => ?_
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          (Q j).isColimit.fac]
        obtain ⟨i', hom, rfl⟩ := Total.exists_hom_of_hom (P := Q) i u
        rw [reassoc_of% hom.w]; rw [(Q j').isColimit.fac]
        simpa using c.ι.naturality hom }
  isColimit.fac := fun c ⟨j, i⟩ => by simp [P.isColimit.fac, (Q j).isColimit.fac]
  isColimit.uniq c m hm := by
    refine P.isColimit.hom_ext fun j => ?_
    simp only [P.isColimit.fac]
    refine (Q j).isColimit.hom_ext fun i => ?_
    simpa [(Q j).isColimit.fac] using hm (.mk _ j i)

end Small

end CategoryTheory.Limits.ColimitPresentation
