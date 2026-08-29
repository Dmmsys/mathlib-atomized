/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category.

A presheaf on a topological space `X` is a sheaf precisely when it is a sheaf under the
Grothendieck topology on `opens X`, which expands out to say: For each open cover `{ Uᵢ }` of
`U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an `A : X`, there exists a unique
gluing `A ⟶ F(U)` compatible with the restriction.

See the docstring of `TopCat.Presheaf.IsSheaf` for an explanation on the design decisions and a list
of equivalent conditions.

We provide the instance `CategoryTheory.Category (TopCat.Sheaf C X)` as the full subcategory of
presheaves, and the fully faithful functor `Sheaf.forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X`.

-/

@[expose] public section


universe w v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type v} (U : ι -> Opens X)

namespace Presheaf

/-- The sheaf condition has several different equivalent formulations.
The official definition chosen here is in terms of Grothendieck topologies so that the results on
sites could be applied here easily, and this condition does not require additional constraints on
the value category.
The equivalent formulations of the sheaf condition on `presheaf C X` are as follows :

1. `TopCat.Presheaf.IsSheaf`: (the official definition)
  It is a sheaf with respect to the Grothendieck topology on `opens X`, which is to say:
  For each open cover `{ Uᵢ }` of `U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an
  `A : X`, there exists a unique gluing `A ⟶ F(U)` compatible with the restriction.

2. `TopCat.Presheaf.IsSheafEqualizerProducts`: (requires `C` to have all products)
  For each open cover `{ Uᵢ }` of `U`, `F(U) ⟶ ∏ᶜ F(Uᵢ)` is the equalizer of the two morphisms
  `∏ᶜ F(Uᵢ) ⟶ ∏ᶜ F(Uᵢ ∩ Uⱼ)`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`.

3. `TopCat.Presheaf.IsSheafOpensLeCover`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  `F(V₁) ⟶ F(V₂)` for every pair of open sets `V₁ ⊇ V₂` that are contained in some `Uᵢ`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover`.

4. `TopCat.Presheaf.IsSheafPairwiseIntersections`:
  For each open cover `{ Uᵢ }` of `U`, `F(U)` is the limit of the diagram consisting of arrows
  from `F(Uᵢ)` and `F(Uⱼ)` to `F(Uᵢ ∩ Uⱼ)` for each pair `(i, j)`.
  See `TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections`.

The following requires `C` to be concrete and complete, and `forget C` to reflect isomorphisms and
preserve limits. This applies to most "algebraic" categories, e.g. groups, abelian groups and rings.

5. `TopCat.Presheaf.IsSheafUniqueGluing`:
  (requires `C` to be concrete and complete; `forget C` to reflect isomorphisms and preserve limits)
  For each open cover `{ Uᵢ }` of `U`, and a compatible family of elements `x : F(Uᵢ)`, there exists
  a unique gluing `x : F(U)` that restricts to the given elements.
  See `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`.

6. The underlying sheaf of types is a sheaf.
  See `TopCat.Presheaf.isSheaf_iff_isSheaf_comp` and
  `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`.
-/
nonrec def IsSheaf (F : Presheaf.{w, v, u} C X) : Prop :=
  Presheaf.IsSheaf (Opens.grothendieckTopology X) F

/--
theorem `isSheaf_unit` / 定理 `isSheaf_unit`

English:
theorem isSheaf_unit
  given: (F : Presheaf (CategoryTheory.Discrete Unit) X)
  statement: F.IsSheaf
  proof: fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by cat_disch, fun _ => by cat_disch⟩

中文:
定理 isSheaf_unit
  条件: (F : 预层 (范畴论.离散 单元) X)
  结论: F.是层
  证明: fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by cat_disch, fun _ => by cat_disch⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, cat_disch, eqToHom
-/
theorem isSheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf :=
  fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by cat_disch, fun _ => by cat_disch⟩

/--
theorem `isSheaf_iso_iff` / 定理 `isSheaf_iso_iff`

English:
theorem isSheaf_iso_iff
  given: {F G : Presheaf C X} (α : F ≅ G)
  statement: F.IsSheaf ↔ G.IsSheaf
  proof: Presheaf.isSheaf_of_iso_iff α

中文:
定理 isSheaf_iso_iff
  条件: {F G : 预层 C X} (α : F ≅ G)
  结论: F.是层 ↔ G.是层
  证明: Presheaf.isSheaf_of_iso_iff α

Depends on / 依赖: Presheaf, Presheaf.isSheaf_of_iso_iff, isSheaf_of_iso_iff
-/
theorem isSheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf :=
  Presheaf.isSheaf_of_iso_iff α

/--
theorem `isSheaf_of_iso` / 定理 `isSheaf_of_iso`

English:
theorem isSheaf_of_iso
  given: {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf)
  statement: G.IsSheaf
  proof: (isSheaf_iso_iff α).1 h

中文:
定理 isSheaf_of_iso
  条件: {F G : 预层 C X} (α : F ≅ G) (h : F.是层)
  结论: G.是层
  证明: (isSheaf_iso_iff α).1 h

Depends on / 依赖: isSheaf_iso_iff
-/
theorem isSheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsSheaf :=
  (isSheaf_iso_iff α).1 h

end Presheaf

variable (C X)

/-- A `TopCat.Sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
nonrec def Sheaf : Type max u v w :=
  Sheaf (Opens.grothendieckTopology X) C
deriving Category

variable {C X}

/--
Definition of `Sheaf.presheaf` / `Sheaf.presheaf` 的定义

English:
abbreviation Sheaf.presheaf
  signature: (F : X.Sheaf C)
  body: F.1

中文:
缩写 层.presheaf
  签名: (F : X.层 C)
  定义体: F.1
-/
abbrev Sheaf.presheaf (F : X.Sheaf C) : TopCat.Presheaf C X :=
  F.1

variable (C X)

-- Let's construct a trivial example, to keep the inhabited linter happy.
/--
Instance `sheafInhabited` / 实例 `sheafInhabited`

English:
instance sheafInhabited
  signature: : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X)
  body: ⟨⟨Functor.star _, Presheaf.isSheaf_unit _⟩⟩

中文:
实例 sheafInhabited
  签名: : 可居 (层 (范畴论.离散 命题单元) X)
  定义体: ⟨⟨Functor.star _, Presheaf.isSheaf_unit _⟩⟩

Depends on / 依赖: Functor, Functor.star, Presheaf, Presheaf.isSheaf_unit, isSheaf_unit
-/
instance sheafInhabited : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X) :=
  ⟨⟨Functor.star _, Presheaf.isSheaf_unit _⟩⟩

namespace Sheaf

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X
  body: sheafToPresheaf _ _

中文:
定义 forget
  签名: : 顶元素范畴.层 C X ⥤ 顶元素范畴.预层 C X
  定义体: sheafToPresheaf _ _

Depends on / 依赖: sheafToPresheaf
-/
def forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X :=
  sheafToPresheaf _ _

-- The following instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

/--
Instance `forget_full` / 实例 `forget_full`

English:
instance forget_full
  signature: : (forget C X).Full where
  body: ⟨ObjectProperty.homMk f, rfl⟩

中文:
实例 forget_full
  签名: : (forget C X).满 where
  定义体: ⟨ObjectProperty.homMk f, rfl⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk
-/
instance forget_full : (forget C X).Full where
  map_surjective f := ⟨ObjectProperty.homMk f, rfl⟩

/--
Instance `forgetFaithful` / 实例 `forgetFaithful`

English:
instance forgetFaithful
  signature: : (forget C X).Faithful where
  body: Sheaf.hom_ext

中文:
实例 forgetFaithful
  签名: : (forget C X).忠实 where
  定义体: Sheaf.hom_ext

Depends on / 依赖: Sheaf.hom_ext, hom_ext
-/
instance forgetFaithful : (forget C X).Faithful where
  map_injective := Sheaf.hom_ext

-- Note: These can be proved by simp.
/--
theorem `id_app` / 定理 `id_app`

English:
theorem id_app
  given: (F : Sheaf C X) (t)
  statement: (𝟙 F : F ⟶ F).1.app t = 𝟙 _
  proof: rfl

中文:
定理 id_app
  条件: (F : 层 C X) (t)
  结论: (𝟙 F : F ⟶ F).1.app t = 𝟙 _
  证明: rfl
-/
theorem id_app (F : Sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ :=
  rfl

/--
theorem `comp_app` / 定理 `comp_app`

English:
theorem comp_app
  given: {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t)
  proof: rfl

中文:
定理 comp_app
  条件: {F G H : 层 C X} (f : F ⟶ G) (g : G ⟶ H) (t)
  证明: rfl
-/
theorem comp_app {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
    (f ≫ g).1.app t = f.1.app t ≫ g.1.app t :=
  rfl

end Sheaf

/--
lemma `Presheaf.IsSheaf.section_ext` / 引理 `Presheaf.IsSheaf.section_ext`

English:
lemma Presheaf.IsSheaf.section_ext
  statement: {X : TopCat.{u}}
  proof: by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (C := Opens X) (A' := A) _ F (forget _)).mp hF)
  choose V hV hxV H using fun x : U.unop => hst x.1 x.2
  refine (this.isSheafFor (.ofArrows V fun x => homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · exact fun 

中文:
引理 预层.是层.section_ext
  结论: {X : 顶元素范畴.{u}}
  证明: by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (C := Opens X) (A' := A) _ F (forget _)).mp hF)
  choose V hV hxV H using fun x : U.unop => hst x.1 x.2
  refine (this.isSheafFor (.ofArrows V fun x => homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · exact fun 

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_isSheaf_forget, Sieve.ofArrows_mk, U.unop, forget, homOfLE, isSeparatedFor, isSeparatedFor.ext, isSheafFor, isSheaf_iff_isSheaf_forget, isSheaf_iff_isSheaf_of_type, ofArrows, ofArrows_mk, this.isSheafFor
-/
lemma Presheaf.IsSheaf.section_ext {X : TopCat.{u}}
    {A : Type*} [Category.{u} A] {FC : A -> A -> Type*} {CC : A -> Type u}
    [forall X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    [HasLimits A] [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]
    {F : TopCat.Presheaf A X} (hF : TopCat.Presheaf.IsSheaf F)
    {U : (Opens X)ᵒᵖ} {s t : ToType (F.obj U)}
    (hst : forall x in U.unop, exists V, exists hV : V <= U.unop, x in V ∧
      F.map (homOfLE hV).op s = F.map (homOfLE hV).op t) :
    s = t := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (C := Opens X) (A' := A) _ F (forget _)).mp hF)
  choose V hV hxV H using fun x : U.unop => hst x.1 x.2
  refine (this.isSheafFor (.ofArrows V fun x => homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · exact fun x hx => ⟨V ⟨x, hx⟩, homOfLE (hV _), Sieve.ofArrows_mk _ _ _, hxV _⟩
  · rintro _ _ ⟨x⟩; exact H x

end TopCat
