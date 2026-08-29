/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Local sites

A site is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define coconstant sheaves on it, giving its sheaf topos the structure
of a local topos. This is one of the conditions of cohesive sites.

Sheaves of types on any local site form a local topos (i.e. a topos whose global sections functor
has a fully faithful right adjoint), and a subcanonical site is local if and only if its topos of
sheaves of types is (see TODOs).

## Main definitions / results

* `J.IsLocalSite`: typeclass stating that `J` makes the category it is defined on into a local site.
* `IsLocalSite.point J`: the canonical point of any local site, whose fibre functor is given by
  the coyoneda embedding of the terminal object and extends to the global sections functors on
  presheaves and sheaves.
* `coconstantSheaf J A`: the coconstant sheaf functor `A ⥤ Sheaf J A` for any local site and
  sufficiently nice target category `A`, defined as the skyscraper sheaf functor of the canonical
  point.
* `ΓCoconstantSheafAdj J A`: the adjunction between the global sections functor `Γ J A` and
  `coconstantSheaf J A`.
* `fullyFaithfulCoconstantSheaf`: `coconstantSheaf` is fully faithful.
* `fullyFaithfulConstantSheaf`: on local sites, the constant sheaf functor is fully faithful.

## References

* https://ncatlab.org/nlab/show/local+site

## TODO

* Define local topoi and prove that sheaves on any local site form a local topos
* Show that a subcanonical site is local if and only if its global sections functor has a fully
  faithful right adjoint
-/

universe w u v u' v'

@[expose] public section

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/--
Definition of `GrothendieckTopology.IsLocalSite` / `GrothendieckTopology.IsLocalSite` 的定义

English:
class GrothendieckTopology.IsLocalSite
  parameters: extends HasTerminal C
  extends: HasTerminal C
  axioms and operations (1):
    - eq_top_of_mem : forall S in J (⊤_ C), S = ⊤

中文:
类 GrothendieckTopology.IsLocalSite
  参数: extends HasTerminal C
  继承: HasTerminal C
  公理与运算 (1 个):
    - eq_top_of_mem : 对任意 S in J (⊤_ C), S = ⊤
-/
class GrothendieckTopology.IsLocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : forall S in J (⊤_ C), S = ⊤

namespace GrothendieckTopology.IsLocalSite

/--
lemma `from_terminal_mem_of_mem` / 引理 `from_terminal_mem_of_mem`

English:
lemma from_terminal_mem_of_mem
  statement: [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
  proof: (S.mem_iff_pullback_eq_top f).mpr eq_top_of_mem _ J.pullback_stable f hS

中文:
引理 from_terminal_mem_of_mem
  结论: [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
  证明: (S.mem_iff_pullback_eq_top f).mpr eq_top_of_mem _ J.pullback_stable f hS

Depends on / 依赖: J.pullback_stable, S.mem_iff_pullback_eq_top, eq_top_of_mem, mem_iff_pullback_eq_top, pullback_stable
-/
lemma from_terminal_mem_of_mem [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S in J X) : S.arrows f :=
(S.mem_iff_pullback_eq_top f).mpr eq_top_of_mem _ J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : (trivial C).IsLocalSite where
  eq_top_of_mem _ := trivial_covering.mp

/--
Definition of `point` / `point` 的定义

English:
definition point
  signature: [LocallySmall.{w} C] [J.IsLocalSite]
  body: shrinkCoyoneda.obj (op (⊤_ C))
  jointly_surjective R hR x :=
    ⟨(⊤_ C), shrinkCoyonedaObjObjEquiv x,
      (from_terminal_mem_of_mem J (shrinkCoyonedaObjObjEquiv x) hR),
          shrinkCoyonedaObjObjEquiv.symm (𝟙 _), by
        rw [shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm]
        s

中文:
定义 point
  签名: [LocallySmall.{w} C] [J.IsLocalSite]
  定义体: shrinkCoyoneda.obj (op (⊤_ C))
  jointly_surjective R hR x :=
    ⟨(⊤_ C), shrinkCoyonedaObjObjEquiv x,
      (from_terminal_mem_of_mem J (shrinkCoyonedaObjObjEquiv x) hR),
          shrinkCoyonedaObjObjEquiv.symm (𝟙 _), by
        rw [shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm]
        s

Depends on / 依赖: shrinkCoyoneda, shrinkCoyoneda.obj
-/
noncomputable def point [LocallySmall.{w} C] [J.IsLocalSite] : Point.{w} J where
  fiber := shrinkCoyoneda.obj (op (⊤_ C))
  jointly_surjective R hR x :=
    ⟨(⊤_ C), shrinkCoyonedaObjObjEquiv x,
      (from_terminal_mem_of_mem J (shrinkCoyonedaObjObjEquiv x) hR),
          shrinkCoyonedaObjObjEquiv.symm (𝟙 _), by
        rw [shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm]
        simp⟩

variable [LocallySmall.{w} C] [J.IsLocalSite] (A : Type u') [Category.{v'} A]

/--
Definition of `coconstantSheaf` / `coconstantSheaf` 的定义

English:
definition coconstantSheaf
  signature: [HasProducts.{w} A]
  body: (point.{w} J).skyscraperSheafFunctor

中文:
定义 coconstantSheaf
  签名: [HasProducts.{w} A]
  定义体: (point.{w} J).skyscraperSheafFunctor

Depends on / 依赖: skyscraperSheafFunctor
-/
noncomputable def coconstantSheaf [HasProducts.{w} A] : A ⥤ Sheaf J A :=
  (point.{w} J).skyscraperSheafFunctor

variable [HasColimitsOfSize.{w, w} A]

set_option backward.isDefEq.respectTransparency.types false in
variable {A} in
/--
Definition of `pointPresheafFiberIso` / `pointPresheafFiberIso` 的定义

English:
definition pointPresheafFiberIso
  signature: (P : Cᵒᵖ ⥤ A)
  body: (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (Functor.Elements.isInitialOfCorepresentableBy
 shrinkCoyonedaCorepresentableBy op (⊤_ C)).op _)

中文:
定义 pointPresheafFiberIso
  签名: (P : Cᵒᵖ ⥤ A)
  定义体: (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (Functor.Elements.isInitialOfCorepresentableBy
 shrinkCoyonedaCorepresentableBy op (⊤_ C)).op _)

Depends on / 依赖: Elements, Functor, Functor.Elements.isInitialOfCorepresentableBy, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitOfDiagramTerminal, isColimit, isInitialOfCorepresentableBy, shrinkCoyonedaCorepresentableBy
-/
noncomputable def pointPresheafFiberIso (P : Cᵒᵖ ⥤ A) :
    (point J).presheafFiber.obj P ≅ P.obj (op (⊤_ C)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (Functor.Elements.isInitialOfCorepresentableBy
 shrinkCoyonedaCorepresentableBy op (⊤_ C)).op _)

variable {A} in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `toPresheafFiber_pointPresheafFiberIso_hom` / 引理 `toPresheafFiber_pointPresheafFiberIso_hom`

English:
lemma toPresheafFiber_pointPresheafFiberIso_hom
  given: {P : Cᵒᵖ ⥤ A} (X : C) (x : (point J).fiber.obj X)
  proof: by
  simp [Point.toPresheafFiber, pointPresheafFiberIso]
  rfl

中文:
引理 toPresheafFiber_pointPresheafFiberIso_hom
  条件: {P : Cᵒᵖ ⥤ A} (X : C) (x : (point J).fiber.obj X)
  证明: by
  simp [Point.toPresheafFiber, pointPresheafFiberIso]
  rfl

Depends on / 依赖: Point.toPresheafFiber, pointPresheafFiberIso, toPresheafFiber
-/
lemma toPresheafFiber_pointPresheafFiberIso_hom {P : Cᵒᵖ ⥤ A} (X : C) (x : (point J).fiber.obj X) :
    (point J).toPresheafFiber _ x _ ≫ (pointPresheafFiberIso J P).hom =
      P.map (.op <| shrinkCoyonedaObjObjEquiv x) := by
  simp [Point.toPresheafFiber, pointPresheafFiberIso]
  rfl

variable {A} in
@[reassoc (attr := simp)]
/--
lemma `pointPresheafFiberIso_naturality` / 引理 `pointPresheafFiberIso_naturality`

English:
lemma pointPresheafFiberIso_naturality
  given: {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P')
  proof: by
  cat_disch

中文:
引理 pointPresheafFiberIso_naturality
  条件: {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P')
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma pointPresheafFiberIso_naturality {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P') :
    (point J).presheafFiber.map F ≫ (pointPresheafFiberIso J P').hom =
      (pointPresheafFiberIso J P).hom ≫ F.app (op (⊤_ C)) := by
  cat_disch

/--
Definition of `pointPresheafFiberNatIso` / `pointPresheafFiberNatIso` 的定义

English:
definition pointPresheafFiberNatIso
  signature: :
  body: NatIso.ofComponents (pointPresheafFiberIso J) fun F => pointPresheafFiberIso_naturality J F

中文:
定义 pointPresheafFiberNatIso
  签名: :
  定义体: NatIso.ofComponents (pointPresheafFiberIso J) fun F => pointPresheafFiberIso_naturality J F

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, pointPresheafFiberIso, pointPresheafFiberIso_naturality
-/
noncomputable def pointPresheafFiberNatIso :
    ((point J).presheafFiber : _ ⥤ A) ≅ (evaluation _ _).obj (op (⊤_ C)) :=
  NatIso.ofComponents (pointPresheafFiberIso J) fun F => pointPresheafFiberIso_naturality J F

/--
Definition of `pointSheafFiberIso` / `pointSheafFiberIso` 的定义

English:
definition pointSheafFiberIso
  body: ((sheafToPresheaf J A).isoWhiskerLeft (pointPresheafFiberNatIso J A)).trans
    (ΓNatIsoSheafSections J A terminalIsTerminal).symm

中文:
定义 pointSheafFiberIso
  定义体: ((sheafToPresheaf J A).isoWhiskerLeft (pointPresheafFiberNatIso J A)).trans
    (ΓNatIsoSheafSections J A terminalIsTerminal).symm

Depends on / 依赖: isoWhiskerLeft, pointPresheafFiberNatIso, sheafToPresheaf, terminalIsTerminal
-/
noncomputable def pointSheafFiberIso
    [HasWeakSheafify J A] : (point J).sheafFiber ≅ Γ J A :=
  ((sheafToPresheaf J A).isoWhiskerLeft (pointPresheafFiberNatIso J A)).trans
    (ΓNatIsoSheafSections J A terminalIsTerminal).symm

variable [HasProducts.{w} A] [HasWeakSheafify J A]

/--
Definition of `ΓCoconstantSheafAdj` / `ΓCoconstantSheafAdj` 的定义

English:
definition ΓCoconstantSheafAdj
  signature: : Γ J A ⊣ coconstantSheaf.{w} J A
  body: (point.{w} J).skyscraperSheafAdjunction.ofNatIsoLeft (pointSheafFiberIso J A)

中文:
定义 ΓCoconstantSheafAdj
  签名: : Γ J A ⊣ coconstantSheaf.{w} J A
  定义体: (point.{w} J).skyscraperSheafAdjunction.ofNatIsoLeft (pointSheafFiberIso J A)

Depends on / 依赖: ofNatIsoLeft, pointSheafFiberIso, skyscraperSheafAdjunction, skyscraperSheafAdjunction.ofNatIsoLeft
-/
noncomputable def ΓCoconstantSheafAdj : Γ J A ⊣ coconstantSheaf.{w} J A :=
  (point.{w} J).skyscraperSheafAdjunction.ofNatIsoLeft (pointSheafFiberIso J A)

/--
lemma `Γ_isLeftAdjoint` / 引理 `Γ_isLeftAdjoint`

English:
lemma Γ_isLeftAdjoint
  statement: (Γ J A).IsLeftAdjoint
  proof: ⟨coconstantSheaf.{w} J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

中文:
引理 Γ_isLeftAdjoint
  结论: (Γ J A).IsLeftAdjoint
  证明: ⟨coconstantSheaf.{w} J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

Depends on / 依赖: coconstantSheaf
-/
lemma Γ_isLeftAdjoint : (Γ J A).IsLeftAdjoint :=
  ⟨coconstantSheaf.{w} J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

/-- On any local site with morphism types in `Type v`, the global sections functor to any category
with colimits and products of size `v` is a left adjoint. See `ΓIsLeftAdjoint` for a
version for `w`-locally small sites that can't be registered as an instance because of the extra
universe parameter `w`. -/
instance (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{v, v} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (Γ J A).IsLeftAdjoint :=
  Γ_isLeftAdjoint.{v} J A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (coconstantSheaf.{w} J A).IsRightAdjoint
  body: ⟨Γ J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

中文:
实例 :
  签名: (coconstantSheaf.{w} J A).IsRightAdjoint
  定义体: ⟨Γ J A, ⟨ΓCoconstantSheafAdj J A⟩⟩
-/
instance : (coconstantSheaf.{w} J A).IsRightAdjoint :=
  ⟨Γ J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `coconstantSheafΓNatIsoId` / `coconstantSheafΓNatIsoId` 的定义

English:
definition coconstantSheafΓNatIsoId
  signature: :
  body: letI : Unique (unop ((IsLocalSite.point J).fiber.op.obj (op (⊤_ C)))) :=
    (equivShrink (⊤_ C ⟶ ⊤_ C)).symm.unique
  (Functor.isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)) ≪≫
    NatIso.ofComponents (fun X => productUniqueIso _) (by simp [IsLocalSite.coconstantSheaf])

中文:
定义 coconstantSheafΓNatIsoId
  签名: :
  定义体: letI : Unique (unop ((IsLocalSite.point J).fiber.op.obj (op (⊤_ C)))) :=
    (equivShrink (⊤_ C ⟶ ⊤_ C)).symm.unique
  (Functor.isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)) ≪≫
    NatIso.ofComponents (fun X => productUniqueIso _) (by simp [IsLocalSite.coconstantSheaf])

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, IsLocalSite, IsLocalSite.coconstantSheaf, IsLocalSite.point, NatIso, NatIso.ofComponents, Unique, coconstantSheaf, equivShrink, fiber.op.obj, isoWhiskerLeft, ofComponents, productUniqueIso, symm.unique, terminalIsTerminal, unique
-/
noncomputable def coconstantSheafΓNatIsoId :
    IsLocalSite.coconstantSheaf.{w} J A ⋙ Γ J A ≅ 𝟭 A :=
  letI : Unique (unop ((IsLocalSite.point J).fiber.op.obj (op (⊤_ C)))) :=
    (equivShrink (⊤_ C ⟶ ⊤_ C)).symm.unique
  (Functor.isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)) ≪≫
    NatIso.ofComponents (fun X => productUniqueIso _) (by simp [IsLocalSite.coconstantSheaf])

/--
Definition of `fullyFaithfulCoconstantSheaf` / `fullyFaithfulCoconstantSheaf` 的定义

English:
definition fullyFaithfulCoconstantSheaf
  signature: :
  body: (ΓCoconstantSheafAdj J A).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J A)

中文:
定义 fullyFaithfulCoconstantSheaf
  签名: :
  定义体: (ΓCoconstantSheafAdj J A).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J A)

Depends on / 依赖: fullyFaithfulROfCompIsoId
-/
noncomputable def fullyFaithfulCoconstantSheaf :
    (coconstantSheaf.{w} J A).FullyFaithful :=
  (ΓCoconstantSheafAdj J A).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (coconstantSheaf.{w} J A).Full
  body: (fullyFaithfulCoconstantSheaf J A).full

中文:
实例 :
  签名: (coconstantSheaf.{w} J A).Full
  定义体: (fullyFaithfulCoconstantSheaf J A).full

Depends on / 依赖: fullyFaithfulCoconstantSheaf
-/
instance : (coconstantSheaf.{w} J A).Full :=
  (fullyFaithfulCoconstantSheaf J A).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (coconstantSheaf.{w} J A).Faithful
  body: (fullyFaithfulCoconstantSheaf J A).faithful

中文:
实例 :
  签名: (coconstantSheaf.{w} J A).Faithful
  定义体: (fullyFaithfulCoconstantSheaf J A).faithful

Depends on / 依赖: faithful, fullyFaithfulCoconstantSheaf
-/
instance : (coconstantSheaf.{w} J A).Faithful :=
  (fullyFaithfulCoconstantSheaf J A).faithful

/--
Definition of `constantΓCoconstantTriple` / `constantΓCoconstantTriple` 的定义

English:
abbreviation constantΓCoconstantTriple
  signature: :
  body: constantSheafΓAdj J A
  adj₂ := ΓCoconstantSheafAdj J A

中文:
缩写 constantΓCoconstantTriple
  签名: :
  定义体: constantSheafΓAdj J A
  adj₂ := ΓCoconstantSheafAdj J A
-/
noncomputable abbrev constantΓCoconstantTriple :
    Adjunction.Triple (constantSheaf J A) (Γ J A) (coconstantSheaf.{w} J A) where
  adj₁ := constantSheafΓAdj J A
  adj₂ := ΓCoconstantSheafAdj J A

/--
Definition of `fullyFaithfulConstantSheaf` / `fullyFaithfulConstantSheaf` 的定义

English:
definition fullyFaithfulConstantSheaf
  signature: : (constantSheaf J A).FullyFaithful
  body: (constantΓCoconstantTriple J A).fullyFaithfulEquiv.symm
    fullyFaithfulCoconstantSheaf.{w} J A

中文:
定义 fullyFaithfulConstantSheaf
  签名: : (constantSheaf J A).FullyFaithful
  定义体: (constantΓCoconstantTriple J A).fullyFaithfulEquiv.symm
    fullyFaithfulCoconstantSheaf.{w} J A

Depends on / 依赖: fullyFaithfulCoconstantSheaf, fullyFaithfulEquiv, fullyFaithfulEquiv.symm
-/
noncomputable def fullyFaithfulConstantSheaf : (constantSheaf J A).FullyFaithful :=
(constantΓCoconstantTriple J A).fullyFaithfulEquiv.symm
    fullyFaithfulCoconstantSheaf.{w} J A

/--
lemma `full_constantSheaf` / 引理 `full_constantSheaf`

English:
lemma full_constantSheaf
  statement: (constantSheaf J A).Full
  proof: (fullyFaithfulConstantSheaf.{w} J A).full

中文:
引理 full_constantSheaf
  结论: (constantSheaf J A).Full
  证明: (fullyFaithfulConstantSheaf.{w} J A).full

Depends on / 依赖: fullyFaithfulConstantSheaf
-/
lemma full_constantSheaf : (constantSheaf J A).Full :=
  (fullyFaithfulConstantSheaf.{w} J A).full

/--
lemma `faithful_constantSheaf` / 引理 `faithful_constantSheaf`

English:
lemma faithful_constantSheaf
  statement: (constantSheaf J A).Faithful
  proof: (fullyFaithfulConstantSheaf.{w} J A).faithful

中文:
引理 faithful_constantSheaf
  结论: (constantSheaf J A).Faithful
  证明: (fullyFaithfulConstantSheaf.{w} J A).faithful

Depends on / 依赖: faithful, fullyFaithfulConstantSheaf
-/
lemma faithful_constantSheaf : (constantSheaf J A).Faithful :=
  (fullyFaithfulConstantSheaf.{w} J A).faithful

/-- See `IsLocalSite.full_constantSheaf` for a version for `w`-locally small sites. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{v, v} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (constantSheaf J A).Full :=
  full_constantSheaf.{v} J A

/-- See `IsLocalSite.faithful_constantSheaf` for a version for `w`-locally small sites. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{v, v} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (constantSheaf J A).Faithful :=
  faithful_constantSheaf.{v} J A

end GrothendieckTopology.IsLocalSite

end CategoryTheory
