/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Topology.Category.CompHausLike.Basic
/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHausLike P`,
which may be useful due to their definitional properties.

## Main definitions

* `HasExplicitFiniteCoproducts`: A typeclass describing the property that forming all finite
  disjoint unions is stable under the property `P`.
  - Given this property, we deduce that `CompHausLike P` has finite coproducts and the inclusion
    functors to other `CompHausLike P'` and to `TopCat` preserve them.

* `HasExplicitPullbacks`: A typeclass describing the property that forming all "explicit pullbacks"
  is stable under the property `P`. Here, explicit pullbacks are defined as a subset of the product.
  - Given this property, we deduce that `CompHausLike P` has pullbacks and the inclusion
    functors to other `CompHausLike P'` and to `TopCat` preserve them.
  - We also define a variant `HasExplicitPullbacksOfInclusions` which is says that explicit
    pullbacks along inclusion maps into finite disjoint unions exist. `Stonean` has this property
    but not the stronger one.

## Main results

* Given `[HasExplicitPullbacksOfInclusions P]` (which is implied by `[HasExplicitPullbacks P]`),
  we provide an instance `FinitaryExtensive (CompHausLike P)`.
-/

@[expose] public section

open CategoryTheory Limits Topology

namespace CompHausLike

universe w u

section FiniteCoproducts

variable {P : TopCat.{max u w} -> Prop} {α : Type w} [Finite α] (X : α -> CompHausLike P)

/--
Definition of `HasExplicitFiniteCoproduct` / `HasExplicitFiniteCoproduct` 的定义

English:
abbreviation HasExplicitFiniteCoproduct
  body: HasProp P (Σ (a : α), X a)

中文:
缩写 HasExplicitFiniteCoproduct
  定义体: HasProp P (Σ (a : α), X a)

Depends on / 依赖: HasProp
-/
abbrev HasExplicitFiniteCoproduct := HasProp P (Σ (a : α), X a)

variable [HasExplicitFiniteCoproduct X]

/--
Definition of `finiteCoproduct` / `finiteCoproduct` 的定义

English:
abbreviation finiteCoproduct
  signature: : CompHausLike P
  body: CompHausLike.of P (Σ (a : α), X a)

中文:
缩写 finiteCoproduct
  签名: : 余mpHausLike P
  定义体: CompHausLike.of P (Σ (a : α), X a)

Depends on / 依赖: CompHausLike, CompHausLike.of
-/
abbrev finiteCoproduct : CompHausLike P := CompHausLike.of P (Σ (a : α), X a)

/--
Definition of `finiteCoproduct.ι` / `finiteCoproduct.ι` 的定义

English:
definition finiteCoproduct.ι
  signature: (a : α)
  body: ofHom _
  { toFun := fun x => ⟨a, x⟩
    continuous_toFun := continuous_sigmaMk (σ := fun a => X a) }

中文:
定义 finiteCoproduct.ι
  签名: (a : α)
  定义体: ofHom _
  { toFun := fun x => ⟨a, x⟩
    continuous_toFun := continuous_sigmaMk (σ := fun a => X a) }

Depends on / 依赖: continuous_sigmaMk, continuous_toFun
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X :=
  ofHom _
  { toFun := fun x => ⟨a, x⟩
    continuous_toFun := continuous_sigmaMk (σ := fun a => X a) }

/--
Definition of `finiteCoproduct.desc` / `finiteCoproduct.desc` 的定义

English:
definition finiteCoproduct.desc
  signature: {B : CompHausLike P} (e : (a : α) -> (X a ⟶ B))
  body: ofHom _
  { toFun := fun ⟨a, x⟩ => e a x
    continuous_toFun := by
      apply continuous_sigma
      intro a; exact (e a).hom.hom.continuous }

@[reassoc (attr := simp)]

中文:
定义 finiteCoproduct.desc
  签名: {B : 余mpHausLike P} (e : (a : α) -> (X a ⟶ B))
  定义体: ofHom _
  { toFun := fun ⟨a, x⟩ => e a x
    continuous_toFun := by
      apply continuous_sigma
      intro a; exact (e a).hom.hom.continuous }

@[reassoc (attr := simp)]

Depends on / 依赖: continuous, continuous_sigma, continuous_toFun, hom.hom.continuous
-/
def finiteCoproduct.desc {B : CompHausLike P} (e : (a : α) -> (X a ⟶ B)) :
    finiteCoproduct X ⟶ B :=
  ofHom _
  { toFun := fun ⟨a, x⟩ => e a x
    continuous_toFun := by
      apply continuous_sigma
      intro a; exact (e a).hom.hom.continuous }

@[reassoc (attr := simp)]
/--
lemma `finiteCoproduct.ι_desc` / 引理 `finiteCoproduct.ι_desc`

English:
lemma finiteCoproduct.ι_desc
  given: {B : CompHausLike P} (e : (a : α) -> (X a ⟶ B)) (a : α)
  proof: rfl

中文:
引理 finiteCoproduct.ι_desc
  条件: {B : 余mpHausLike P} (e : (a : α) -> (X a ⟶ B)) (a : α)
  证明: rfl
-/
lemma finiteCoproduct.ι_desc {B : CompHausLike P} (e : (a : α) -> (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

/--
lemma `finiteCoproduct.hom_ext` / 引理 `finiteCoproduct.hom_ext`

English:
lemma finiteCoproduct.hom_ext
  statement: {B : CompHausLike P} (f g : finiteCoproduct X ⟶ B)
  proof: by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

中文:
引理 finiteCoproduct.hom_ext
  结论: {B : 余mpHausLike P} (f g : finiteCoproduct X ⟶ B)
  证明: by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

Depends on / 依赖: apply_fun, specialize
-/
lemma finiteCoproduct.hom_ext {B : CompHausLike P} (f g : finiteCoproduct X ⟶ B)
    (h : forall a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/--
Definition of `finiteCoproduct.cofan` / `finiteCoproduct.cofan` 的定义

English:
abbreviation finiteCoproduct.cofan
  signature: : Limits.Cofan X
  body: Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)

中文:
缩写 finiteCoproduct.cofan
  签名: : Limits.Cofan X
  定义体: Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)

Depends on / 依赖: Cofan.mk, finiteCoproduct
-/
abbrev finiteCoproduct.cofan : Limits.Cofan X :=
  Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)

/--
Definition of `finiteCoproduct.isColimit` / `finiteCoproduct.isColimit` 的定义

English:
definition finiteCoproduct.isColimit
  signature: : Limits.IsColimit (finiteCoproduct.cofan X)
  body: Cofan.IsColimit.mk _
    (fun s => desc _ fun a => s.inj a)
    (fun _ _ => ι_desc _ _ _)
    fun _ _ hm => finiteCoproduct.hom_ext _ _ _ fun a =>
      (ConcreteCategory.hom_ext _ _ fun t => ConcreteCategory.congr_hom (hm a) t)

中文:
定义 finiteCoproduct.isColimit
  签名: : Limits.是余极限 (finiteCoproduct.cofan X)
  定义体: Cofan.IsColimit.mk _
    (fun s => desc _ fun a => s.inj a)
    (fun _ _ => ι_desc _ _ _)
    fun _ _ hm => finiteCoproduct.hom_ext _ _ _ fun a =>
      (ConcreteCategory.hom_ext _ _ fun t => ConcreteCategory.congr_hom (hm a) t)

Depends on / 依赖: Cofan.IsColimit.mk, ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ext, IsColimit, congr_hom, finiteCoproduct, finiteCoproduct.hom_ext, hom_ext, s.inj
-/
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cofan X) :=
  Cofan.IsColimit.mk _
    (fun s => desc _ fun a => s.inj a)
    (fun _ _ => ι_desc _ _ _)
    fun _ _ hm => finiteCoproduct.hom_ext _ _ _ fun a =>
      (ConcreteCategory.hom_ext _ _ fun t => ConcreteCategory.congr_hom (hm a) t)

/--
lemma `finiteCoproduct.ι_injective` / 引理 `finiteCoproduct.ι_injective`

English:
lemma finiteCoproduct.ι_injective
  given: (a : α)
  statement: Function.Injective (finiteCoproduct.ι X a)
  proof: by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

中文:
引理 finiteCoproduct.ι_injective
  条件: (a : α)
  结论: 函数.单射 (finiteCoproduct.ι X a)
  证明: by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

Depends on / 依赖: Sigma.ext_iff.mp, eq_of_heq, ext_iff
-/
lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

/--
lemma `finiteCoproduct.ι_jointly_surjective` / 引理 `finiteCoproduct.ι_jointly_surjective`

English:
lemma finiteCoproduct.ι_jointly_surjective
  given: (R : finiteCoproduct X)
  proof: ⟨R.fst, R.snd, rfl⟩

中文:
引理 finiteCoproduct.ι_jointly_surjective
  条件: (R : finiteCoproduct X)
  证明: ⟨R.fst, R.snd, rfl⟩

Depends on / 依赖: R.fst, R.snd
-/
lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    exists (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩

/--
lemma `finiteCoproduct.ι_desc_apply` / 引理 `finiteCoproduct.ι_desc_apply`

English:
lemma finiteCoproduct.ι_desc_apply
  given: {B : CompHausLike P} {π : (a : α) -> X a ⟶ B} (a : α)
  proof: by
  tauto

中文:
引理 finiteCoproduct.ι_desc_apply
  条件: {B : 余mpHausLike P} {π : (a : α) -> X a ⟶ B} (a : α)
  证明: by
  tauto
-/
lemma finiteCoproduct.ι_desc_apply {B : CompHausLike P} {π : (a : α) -> X a ⟶ B} (a : α) :
    forall x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  tauto

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoproduct X
  body: ⟨finiteCoproduct.cofan X, finiteCoproduct.isColimit X⟩

中文:
实例 :
  签名: HasCoproduct X
  定义体: ⟨finiteCoproduct.cofan X, finiteCoproduct.isColimit X⟩

Depends on / 依赖: finiteCoproduct, finiteCoproduct.cofan, finiteCoproduct.isColimit, isColimit
-/
instance : HasCoproduct X where
  exists_colimit := ⟨finiteCoproduct.cofan X, finiteCoproduct.isColimit X⟩

/-
This linter complains that the universes `u` and `w` only occur together, but `w` appears by itself
in the indexing type of the coproduct. In almost all cases, `w` will be either `0` or `u`, but we
want to allow both possibilities.
-/
set_option linter.checkUnivs false in
variable (P) in
/--
Definition of `HasExplicitFiniteCoproducts` / `HasExplicitFiniteCoproducts` 的定义

English:
class HasExplicitFiniteCoproducts
  parameters: : Prop where
  axioms and operations (1):
    - hasProp({α : Type w} [Finite α] (X : α -> CompHausLike.{max u w} P)) : HasExplicitFiniteCoproduct X

中文:
类 有ExplicitFiniteCoproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - hasProp({α : 类型 w} [有限 α] (X : α -> 余mpHausLike.{最大值 u w} P)) : HasExplicitFiniteCoproduct X
-/
class HasExplicitFiniteCoproducts : Prop where
  hasProp {α : Type w} [Finite α] (X : α -> CompHausLike.{max u w} P) : HasExplicitFiniteCoproduct X

attribute [instance] HasExplicitFiniteCoproducts.hasProp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitFiniteCoproducts.{w}
  signature: P] (α
  body: hasColimit_of_iso Discrete.natIsoFunctor

中文:
实例 [有ExplicitFiniteCoproducts.{w}
  签名: P] (α
  定义体: hasColimit_of_iso Discrete.natIsoFunctor

Depends on / 依赖: Discrete, Discrete.natIsoFunctor, hasColimit_of_iso, natIsoFunctor
-/
instance [HasExplicitFiniteCoproducts.{w} P] (α : Type w) [Finite α] :
    HasColimitsOfShape (Discrete α) (CompHausLike P) where
  has_colimit _ := hasColimit_of_iso Discrete.natIsoFunctor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitFiniteCoproducts.{w}
  signature: P] : HasFiniteCoproducts (CompHausLike.{max u w} P) where
  body: by
    let α := ULift.{w} (Fin n)
    let e : Discrete α ≌ Discrete (Fin n) := Discrete.equivalence Equiv.ulift
    exact hasColimitsOfShape_of_equivalence e

中文:
实例 [有ExplicitFiniteCoproducts.{w}
  签名: P] : 有FiniteCoproducts (余mpHausLike.{最大值 u w} P) where
  定义体: by
    let α := ULift.{w} (Fin n)
    let e : Discrete α ≌ Discrete (Fin n) := Discrete.equivalence Equiv.ulift
    exact hasColimitsOfShape_of_equivalence e

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.ulift, equivalence, hasColimitsOfShape_of_equivalence
-/
instance [HasExplicitFiniteCoproducts.{w} P] : HasFiniteCoproducts (CompHausLike.{max u w} P) where
  out n := by
    let α := ULift.{w} (Fin n)
    let e : Discrete α ≌ Discrete (Fin n) := Discrete.equivalence Equiv.ulift
    exact hasColimitsOfShape_of_equivalence e

variable {P : TopCat.{u} -> Prop} [HasExplicitFiniteCoproducts.{0} P]

example : HasFiniteCoproducts (CompHausLike.{u} P) := inferInstance

/--
lemma `finiteCoproduct.isOpenEmbedding_ι` / 引理 `finiteCoproduct.isOpenEmbedding_ι`

English:
lemma finiteCoproduct.isOpenEmbedding_ι
  given: (a : α)
  proof: .sigmaMk (σ := fun a => X a)

中文:
引理 finiteCoproduct.isOpenEmbedding_ι
  条件: (a : α)
  证明: .sigmaMk (σ := fun a => X a)

Depends on / 依赖: sigmaMk
-/
lemma finiteCoproduct.isOpenEmbedding_ι (a : α) :
    IsOpenEmbedding (finiteCoproduct.ι X a) :=
  .sigmaMk (σ := fun a => X a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Sigma.isOpenEmbedding_ι` / 引理 `Sigma.isOpenEmbedding_ι`

English:
lemma Sigma.isOpenEmbedding_ι
  given: (a : α)
  proof: by
  refine IsOpenEmbedding.of_comp _ (homeoOfIso ((colimit.isColimit _).coconePointUniqueUpToIso
    (finiteCoproduct.isColimit X))).isOpenEmbedding ?_
  convert! finiteCoproduct.isOpenEmbedding_ι X a
  ext x
  change (Sigma.ι X a ≫ _) x = _
  simp

中文:
引理 依赖和类型.isOpenEmbedding_ι
  条件: (a : α)
  证明: by
  refine IsOpenEmbedding.of_comp _ (homeoOfIso ((colimit.isColimit _).coconePointUniqueUpToIso
    (finiteCoproduct.isColimit X))).isOpenEmbedding ?_
  convert! finiteCoproduct.isOpenEmbedding_ι X a
  ext x
  change (Sigma.ι X a ≫ _) x = _
  simp

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.of_comp, coconePointUniqueUpToIso, colimit, colimit.isColimit, convert, finiteCoproduct, finiteCoproduct.isColimit, finiteCoproduct.isOpenEmbedding_, homeoOfIso, isColimit, isOpenEmbedding, of_comp
-/
lemma Sigma.isOpenEmbedding_ι (a : α) :
    IsOpenEmbedding (Sigma.ι X a) := by
  refine IsOpenEmbedding.of_comp _ (homeoOfIso ((colimit.isColimit _).coconePointUniqueUpToIso
    (finiteCoproduct.isColimit X))).isOpenEmbedding ?_
  convert! finiteCoproduct.isOpenEmbedding_ι X a
  ext x
  change (Sigma.ι X a ≫ _) x = _
  simp

/-- The functor to `TopCat` preserves finite coproducts if they exist. -/
instance (P) [HasExplicitFiniteCoproducts.{0} P] :
    PreservesFiniteCoproducts (compHausLikeToTop P) := by
  refine ⟨fun n => ⟨fun {F} => ?_⟩⟩
  suffices PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) (compHausLikeToTop P) from
    preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm
  exact preservesColimit_of_preserves_colimit_cocone (CompHausLike.finiteCoproduct.isColimit _)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).2 (TopCat.sigmaCofanIsColimit _))

/-- The functor to another `CompHausLike` preserves finite coproducts if they exist. -/
noncomputable instance {P' : TopCat.{u} -> Prop}
    (h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop) :
    PreservesFiniteCoproducts (toCompHausLike h) := by
  have : PreservesFiniteCoproducts (toCompHausLike h ⋙ compHausLikeToTop P') :=
    inferInstanceAs (PreservesFiniteCoproducts (compHausLikeToTop _))
  exact preservesFiniteCoproducts_of_reflects_of_preserves (toCompHausLike h) (compHausLikeToTop P')

end FiniteCoproducts

section Pullbacks

variable {P : TopCat.{u} -> Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B)

/--
Definition of `HasExplicitPullback` / `HasExplicitPullback` 的定义

English:
abbreviation HasExplicitPullback
  body: HasProp P { xy : X × Y | f xy.fst = g xy.snd }

中文:
缩写 HasExplicitPullback
  定义体: HasProp P { xy : X × Y | f xy.fst = g xy.snd }

Depends on / 依赖: HasProp, xy.fst, xy.snd
-/
abbrev HasExplicitPullback := HasProp P { xy : X × Y | f xy.fst = g xy.snd }

variable [HasExplicitPullback f g] -- (hP : P (TopCat.of { xy : X × Y | f xy.fst = g xy.snd }))

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: : CompHausLike P
  body: letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.hom.hom.continuous.comp continuous_fst)
      (g.hom.hom.continuous.comp continuous_snd)).isCompact
  CompHausLike.of P set

中文:
定义 pullback
  签名: : 余mpHausLike P
  定义体: letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.hom.hom.continuous.comp continuous_fst)
      (g.hom.hom.continuous.comp continuous_snd)).isCompact
  CompHausLike.of P set

Depends on / 依赖: CompHausLike, CompHausLike.of, CompactSpace, continuous, continuous_fst, continuous_snd, f.hom.hom.continuous.comp, g.hom.hom.continuous.comp, isClosed_eq, isCompact, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, xy.fst, xy.snd
-/
def pullback : CompHausLike P :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.hom.hom.continuous.comp continuous_fst)
      (g.hom.hom.continuous.comp continuous_snd)).isCompact
  CompHausLike.of P set

/--
Definition of `pullback.fst` / `pullback.fst` 的定义

English:
definition pullback.fst
  signature: : pullback f g ⟶ X
  body: ConcreteCategory.ofHom
  { toFun := fun ⟨⟨x, _⟩, _⟩ => x
    continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val }

中文:
定义 pullback.fst
  签名: : pullback f g ⟶ X
  定义体: ConcreteCategory.ofHom
  { toFun := fun ⟨⟨x, _⟩, _⟩ => x
    continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val }
-/
def pullback.fst : pullback f g ⟶ X :=
  ConcreteCategory.ofHom
  { toFun := fun ⟨⟨x, _⟩, _⟩ => x
    continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val }

/--
Definition of `pullback.snd` / `pullback.snd` 的定义

English:
definition pullback.snd
  signature: : pullback f g ⟶ Y
  body: ConcreteCategory.ofHom
  { toFun := fun ⟨⟨_,y⟩,_⟩ => y
    continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val }

@[reassoc]

中文:
定义 pullback.snd
  签名: : pullback f g ⟶ Y
  定义体: ConcreteCategory.ofHom
  { toFun := fun ⟨⟨_,y⟩,_⟩ => y
    continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val }

@[reassoc]
-/
def pullback.snd : pullback f g ⟶ Y :=
  ConcreteCategory.ofHom
  { toFun := fun ⟨⟨_,y⟩,_⟩ => y
    continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val }

@[reassoc]
/--
lemma `pullback.condition` / 引理 `pullback.condition`

English:
lemma pullback.condition
  statement: pullback.fst f g ≫ f = pullback.snd f g ≫ g
  proof: by
  ext ⟨_, h⟩; exact h

中文:
引理 pullback.condition
  结论: pullback.fst f g ≫ f = pullback.snd f g ≫ g
  证明: by
  ext ⟨_, h⟩; exact h
-/
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_, h⟩; exact h

/--
Definition of `pullback.lift` / `pullback.lift` 的定义

English:
definition pullback.lift
  signature: {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g)
  body: ConcreteCategory.ofHom
  { toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
    continuous_toFun := by fun_prop }

@[reassoc (attr := simp)]

中文:
定义 pullback.lift
  签名: {Z : 余mpHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g)
  定义体: ConcreteCategory.ofHom
  { toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
    continuous_toFun := by fun_prop }

@[reassoc (attr := simp)]
-/
def pullback.lift {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g :=
  ConcreteCategory.ofHom
  { toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
    continuous_toFun := by fun_prop }

@[reassoc (attr := simp)]
/--
lemma `pullback.lift_fst` / 引理 `pullback.lift_fst`

English:
lemma pullback.lift_fst
  given: {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 pullback.lift_fst
  条件: {Z : 余mpHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma pullback.lift_fst {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
/--
lemma `pullback.lift_snd` / 引理 `pullback.lift_snd`

English:
lemma pullback.lift_snd
  given: {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g)
  proof: rfl

中文:
引理 pullback.lift_snd
  条件: {Z : 余mpHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g)
  证明: rfl
-/
lemma pullback.lift_snd {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

/--
lemma `pullback.hom_ext` / 引理 `pullback.hom_ext`

English:
lemma pullback.hom_ext
  statement: {Z : CompHausLike P} (a b : Z ⟶ pullback f g)
  proof: by
  ext z
  apply_fun (fun q => q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

中文:
引理 pullback.hom_ext
  结论: {Z : 余mpHausLike P} (a b : Z ⟶ pullback f g)
  证明: by
  ext z
  apply_fun (fun q => q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd
-/
lemma pullback.hom_ext {Z : CompHausLike P} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (fun q => q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/--
The pullback cone whose cone point is the explicit pullback.
-/
@[simps! pt π]
/--
Definition of `pullback.cone` / `pullback.cone` 的定义

English:
definition pullback.cone
  signature: : Limits.PullbackCone f g
  body: Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

中文:
定义 pullback.cone
  签名: : Limits.PullbackCone f g
  定义体: Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)
-/
def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/--
The explicit pullback cone is a limit cone.
-/
@[simps! lift]
/--
Definition of `pullback.isLimit` / `pullback.isLimit` 的定义

English:
definition pullback.isLimit
  signature: : Limits.IsLimit (pullback.cone f g)
  body: Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

中文:
定义 pullback.isLimit
  签名: : Limits.是极限 (pullback.cone f g)
  定义体: Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))
-/
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimit (cospan f g)
  body: ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩

中文:
实例 :
  签名: 有极限 (cospan f g)
  定义体: ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩

Depends on / 依赖: isLimit, pullback, pullback.cone, pullback.isLimit
-/
instance : HasLimit (cospan f g) where
  exists_limit := ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimit (cospan f g) (compHausLikeToTop P)
  body: createsLimitOfFullyFaithfulOfIso (pullback f g)
    ((((TopCat.pullbackConeIsLimit f.hom g.hom).conePointUniqueUpToIso
    (limit.isLimit _)) ≪≫ Limits.lim.mapIso (by rfl ≪≫ (diagramIsoCospan _).symm)))

中文:
实例 :
  签名: 创造极限 (cospan f g) (compHausLikeToTop P)
  定义体: createsLimitOfFullyFaithfulOfIso (pullback f g)
    ((((TopCat.pullbackConeIsLimit f.hom g.hom).conePointUniqueUpToIso
    (limit.isLimit _)) ≪≫ Limits.lim.mapIso (by rfl ≪≫ (diagramIsoCospan _).symm)))

Depends on / 依赖: Limits, Limits.lim.mapIso, TopCat, TopCat.pullbackConeIsLimit, conePointUniqueUpToIso, createsLimitOfFullyFaithfulOfIso, diagramIsoCospan, f.hom, g.hom, isLimit, limit.isLimit, mapIso, pullback, pullbackConeIsLimit
-/
noncomputable instance : CreatesLimit (cospan f g) (compHausLikeToTop P) :=
  createsLimitOfFullyFaithfulOfIso (pullback f g)
    ((((TopCat.pullbackConeIsLimit f.hom g.hom).conePointUniqueUpToIso
    (limit.isLimit _)) ≪≫ Limits.lim.mapIso (by rfl ≪≫ (diagramIsoCospan _).symm)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (cospan f g) (compHausLikeToTop P)
  body: preservesLimit_of_createsLimit_and_hasLimit _ _

中文:
实例 :
  签名: 保持极限 (cospan f g) (compHausLikeToTop P)
  定义体: preservesLimit_of_createsLimit_and_hasLimit _ _

Depends on / 依赖: preservesLimit_of_createsLimit_and_hasLimit
-/
noncomputable instance : PreservesLimit (cospan f g) (compHausLikeToTop P) :=
  preservesLimit_of_createsLimit_and_hasLimit _ _

/-- The functor to another `CompHausLike` preserves pullbacks. -/
noncomputable instance {P' : TopCat -> Prop}
    (h : forall (X : CompHausLike P), P X.toTop -> P' X.toTop) :
    PreservesLimit (cospan f g) (toCompHausLike h) := by
  have : PreservesLimit (cospan f g) (toCompHausLike h ⋙ compHausLikeToTop P') :=
    inferInstanceAs (PreservesLimit _ (compHausLikeToTop _))
  exact preservesLimit_of_reflects_of_preserves (toCompHausLike h) (compHausLikeToTop P')

variable (P) in
/--
Definition of `HasExplicitPullbacks` / `HasExplicitPullbacks` 的定义

English:
class HasExplicitPullbacks
  parameters: : Prop where
  axioms and operations (1):
    - hasProp({X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B)) : HasExplicitPullback f g

中文:
类 有ExplicitPullbacks
  参数: : 命题 where
  公理与运算 (1 个):
    - hasProp({X Y B : 余mpHausLike P} (f : X ⟶ B) (g : Y ⟶ B)) : HasExplicitPullback f g
-/
class HasExplicitPullbacks : Prop where
  hasProp {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) : HasExplicitPullback f g

attribute [instance] HasExplicitPullbacks.hasProp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitPullbacks
  signature: P] : HasPullbacks (CompHausLike P) where
  body: hasLimit_of_iso (diagramIsoCospan F).symm

中文:
实例 [有ExplicitPullbacks
  签名: P] : 有Pullbacks (余mpHausLike P) where
  定义体: hasLimit_of_iso (diagramIsoCospan F).symm

Depends on / 依赖: diagramIsoCospan, hasLimit_of_iso
-/
instance [HasExplicitPullbacks P] : HasPullbacks (CompHausLike P) where
  has_limit F := hasLimit_of_iso (diagramIsoCospan F).symm

variable (P) in
/--
Definition of `HasExplicitPullbacksOfInclusions` / `HasExplicitPullbacksOfInclusions` 的定义

English:
class HasExplicitPullbacksOfInclusions
  parameters: [HasExplicitFiniteCoproducts.{0} P]
  axioms and operations (1):
    - hasProp : forall {X Y Z : CompHausLike P} (f : Z ⟶ X ⨿ Y), HasExplicitPullback coprod.inl f

中文:
类 有ExplicitPullbacksOfInclusions
  参数: [有ExplicitFiniteCoproducts.{0} P]
  公理与运算 (1 个):
    - hasProp : 对任意 {X Y Z : 余mpHausLike P} (f : Z ⟶ X ⨿ Y), HasExplicitPullback coprod.inl f
-/
class HasExplicitPullbacksOfInclusions [HasExplicitFiniteCoproducts.{0} P] : Prop where
  hasProp : forall {X Y Z : CompHausLike P} (f : Z ⟶ X ⨿ Y), HasExplicitPullback coprod.inl f

attribute [instance] HasExplicitPullbacksOfInclusions.hasProp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitPullbacks
  signature: P] [HasExplicitFiniteCoproducts.{0} P] :
  body: inferInstance

中文:
实例 [有ExplicitPullbacks
  签名: P] [有ExplicitFiniteCoproducts.{0} P] :
  定义体: inferInstance
-/
instance [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P] :
    HasExplicitPullbacksOfInclusions P where
  hasProp _ := inferInstance

end Pullbacks

section FiniteCoproducts

variable {P : TopCat.{u} -> Prop} [HasExplicitFiniteCoproducts.{0} P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitPullbacksOfInclusions
  signature: P] : HasPullbacksOfInclusions (CompHausLike P) where
  body: inferInstance

中文:
实例 [有ExplicitPullbacksOfInclusions
  签名: P] : 有PullbacksOfInclusions (余mpHausLike P) where
  定义体: inferInstance
-/
instance [HasExplicitPullbacksOfInclusions P] : HasPullbacksOfInclusions (CompHausLike P) where
  hasPullbackInl _ := inferInstance

/--
theorem `hasPullbacksOfInclusions` / 定理 `hasPullbacksOfInclusions`

English:
theorem hasPullbacksOfInclusions
  proof: { hasProp := by
      intro _ _ _ f
      apply hP'
      exact Sigma.isOpenEmbedding_ι _ _ }

中文:
定理 hasPullbacksOfInclusions
  证明: { hasProp := by
      intro _ _ _ f
      apply hP'
      exact Sigma.isOpenEmbedding_ι _ _ }

Depends on / 依赖: Sigma.isOpenEmbedding_, hasProp
-/
theorem hasPullbacksOfInclusions
    (hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
      (_ : IsOpenEmbedding f), HasExplicitPullback f g) :
    HasExplicitPullbacksOfInclusions P :=
  { hasProp := by
      intro _ _ _ f
      apply hP'
      exact Sigma.isOpenEmbedding_ι _ _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitPullbacksOfInclusions
  signature: P] :
  body: { preservesPullbackInl := by
      intro X Y Z f
      infer_instance }

中文:
实例 [有ExplicitPullbacksOfInclusions
  签名: P] :
  定义体: { preservesPullbackInl := by
      intro X Y Z f
      infer_instance }

Depends on / 依赖: infer_instance, preservesPullbackInl
-/
noncomputable instance [HasExplicitPullbacksOfInclusions P] :
    PreservesPullbacksOfInclusions (compHausLikeToTop P) :=
  { preservesPullbackInl := by
      intro X Y Z f
      infer_instance }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitPullbacksOfInclusions
  signature: P] : FinitaryExtensive (CompHausLike P)
  body: finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

中文:
实例 [有ExplicitPullbacksOfInclusions
  签名: P] : 有限广延 (余mpHausLike P)
  定义体: finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

Depends on / 依赖: compHausLikeToTop, finitaryExtensive_of_preserves_and_reflects
-/
instance [HasExplicitPullbacksOfInclusions P] : FinitaryExtensive (CompHausLike P) :=
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

/--
theorem `finitaryExtensive` / 定理 `finitaryExtensive`

English:
theorem finitaryExtensive
  statement: (hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
  proof: have := hasPullbacksOfInclusions hP'
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

中文:
定理 finitaryExtensive
  结论: (hP' : 对任意 ⦃X Y B : 余mpHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
  证明: have := hasPullbacksOfInclusions hP'
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

Depends on / 依赖: compHausLikeToTop, finitaryExtensive_of_preserves_and_reflects, hasPullbacksOfInclusions
-/
theorem finitaryExtensive (hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
    (_ : IsOpenEmbedding f), HasExplicitPullback f g) :
      FinitaryExtensive (CompHausLike P) :=
  have := hasPullbacksOfInclusions hP'
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

end FiniteCoproducts

section Terminal

variable {P : TopCat.{u} -> Prop}

/--
Definition of `isTerminalPUnit` / `isTerminalPUnit` 的定义

English:
definition isTerminalPUnit
  signature: [HasProp P PUnit.{u + 1}]
  body: haveI : forall X, Unique (X ⟶ CompHausLike.of P PUnit.{u + 1}) := fun _ =>
    ⟨⟨ofHom _ ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun _ => rfl⟩
  Limits.IsTerminal.ofUnique _

中文:
定义 isTerminalPUnit
  签名: [有命题 P 命题单元.{u + 1}]
  定义体: haveI : forall X, Unique (X ⟶ CompHausLike.of P PUnit.{u + 1}) := fun _ =>
    ⟨⟨ofHom _ ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun _ => rfl⟩
  Limits.IsTerminal.ofUnique _

Depends on / 依赖: CompHausLike, CompHausLike.of, IsTerminal, Limits, Limits.IsTerminal.ofUnique, PUnit.unit, Unique, continuous_const, ofUnique
-/
def isTerminalPUnit [HasProp P PUnit.{u + 1}] :
    IsTerminal (CompHausLike.of P PUnit.{u + 1}) :=
  haveI : forall X, Unique (X ⟶ CompHausLike.of P PUnit.{u + 1}) := fun _ =>
    ⟨⟨ofHom _ ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun _ => rfl⟩
  Limits.IsTerminal.ofUnique _

end Terminal

end CompHausLike
