/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.Basic
public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.CompHausLike.SigmaComparison
public import Mathlib.Topology.FiberPartition
/-!

# The sheaf of locally constant maps on `CompHausLike P`

This file proves that under suitable conditions, the functor from the category of sets to the
category of sheaves for the coherent topology on `CompHausLike P`, given by mapping a set to the
sheaf of locally constant maps to it, is left adjoint to the "underlying set" functor (evaluation
at the point).

We apply this to prove that the constant sheaf functor into (light) condensed sets is isomorphic to
the functor of sheaves of locally constant maps described above.

## Proof sketch

The hard part of this adjunction is to define the counit. Its components are defined as follows:

Let `S : CompHausLike P` and let `Y` be a finite-product-preserving presheaf on `CompHausLike P`
(e.g. a sheaf for the coherent topology). We need to define a map `LocallyConstant S Y(*) ⟶ Y(S)`.
Given a locally constant map `f : S → Y(*)`, let `S = S₁ ⊔ ⋯ ⊔ Sₙ` be the corresponding
decomposition of `S` into the fibers. Let `yᵢ ∈ Y(*)` denote the value of `f` on `Sᵢ` and denote
by `gᵢ` the canonical map `Y(*) → Y(Sᵢ)`. Our map then takes `f` to the image of
`(g₁(y₁), ⋯, gₙ(yₙ))` under the isomorphism `Y(S₁) × ⋯ × Y(Sₙ) ≅ Y(S₁ ⊔ ⋯ ⊔ Sₙ) = Y(S)`.

Now we need to prove that the counit is natural in `S : CompHausLike P` and
`Y : Sheaf (coherentTopology (CompHausLike P)) (Type _)`. There are two key lemmas in all
naturality proofs in this file (both lemmas are in the `CompHausLike.LocallyConstant` namespace):

* `presheaf_ext`: given `S`, `Y` and `f : LocallyConstant S Y(*)` like above, another presheaf
  `X`, and two elements `x y : X(S)`, to prove that `x = y` it suffices to prove that for every
  inclusion map `ιᵢ : Sᵢ ⟶ S`, `X(ιᵢ)(x) = X(ιᵢ)(y)`.
  Here it is important that we set everything up in such a way that the `Sᵢ` are literally subtypes
  of `S`.

* `incl_of_counitAppApp`: given `S`, `Y` and `f : LocallyConstant S Y(*)` like above, we have
  `Y(ιᵢ)(ε_{S, Y}(f)) = gᵢ(yᵢ)` where `ε` denotes the counit and the other notation is like above.

## Main definitions

* `CompHausLike.LocallyConstant.functor`: the functor from the category of sets to the category of
  sheaves for the coherent topology on `CompHausLike P`, which takes a set `X` to
  `LocallyConstant - X`
  - `CondensedSet.LocallyConstant.functor` is the above functor in the case of condensed sets.
  - `LightCondSet.LocallyConstant.functor` is the above functor in the case of light condensed sets.

* `CompHausLike.LocallyConstant.adjunction`: the functor described above is left adjoint to the
  "underlying set" functor `(sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩`, which takes
  a sheaf `X` to the set `X(*)`.

* `CondensedSet.LocallyConstant.iso`: the functor `CondensedSet.LocallyConstant.functor` is
  isomorphic to the functor `Condensed.discrete (Type _)` (the constant sheaf functor from sets to
  condensed sets).

* `LightCondSet.LocallyConstant.iso`: the functor `LightCondSet.LocallyConstant.functor` is
  isomorphic to the functor `LightCondensed.discrete (Type _)` (the constant sheaf functor from sets
  to light condensed sets).

-/

@[expose] public section

universe u w

open CategoryTheory Limits LocallyConstant TopologicalSpace.Fiber Opposite Function Fiber

variable {P : TopCat.{u} -> Prop}

namespace CompHausLike.LocallyConstant

/--
The functor from the category of sets to presheaves on `CompHausLike P` given by locally constant
maps.
-/
@[simps obj_obj obj_map map_app]
/--
Definition of `functorToPresheaves` / `functorToPresheaves` 的定义

English:
definition functorToPresheaves
  signature: : Type (max u w) ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) where
  body: {
    obj := fun ⟨S⟩ => (LocallyConstant S X)
    map f := ↾fun g => g.comap f.unop.hom.hom }
  map f := { app _ := ↾fun t => t.map f }

中文:
定义 functorToPresheaves
  签名: : 类型 (最大值 u w) ⥤ ((余mpHausLike.{u} P)ᵒᵖ ⥤ 类型 (最大值 u w)) where
  定义体: {
    obj := fun ⟨S⟩ => (LocallyConstant S X)
    map f := ↾fun g => g.comap f.unop.hom.hom }
  map f := { app _ := ↾fun t => t.map f }
-/
def functorToPresheaves : Type (max u w) ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) where
  obj X := {
    obj := fun ⟨S⟩ => (LocallyConstant S X)
    map f := ↾fun g => g.comap f.unop.hom.hom }
  map f := { app _ := ↾fun t => t.map f }

/--
Locally constant maps are the same as continuous maps when the target is equipped with the discrete
topology
-/
@[simps]
/--
Definition of `locallyConstantIsoContinuousMap` / `locallyConstantIsoContinuousMap` 的定义

English:
definition locallyConstantIsoContinuousMap
  signature: (Y X : Type*) [TopologicalSpace Y]
  body: letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := ↾fun f => (f : C(Y, X))
    inv := ↾fun f => ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

中文:
定义 locallyConstantIsoContinuousMap
  签名: (Y X : 类型) [拓扑空间 Y]
  定义体: letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := ↾fun f => (f : C(Y, X))
    inv := ↾fun f => ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

Depends on / 依赖: DiscreteTopology, IsLocallyConstant, IsLocallyConstant.iff_continuous, TopologicalSpace, iff_continuous
-/
def locallyConstantIsoContinuousMap (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := ↾fun f => (f : C(Y, X))
    inv := ↾fun f => ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

section Adjunction

variable [forall (S : CompHausLike.{u} P) (p : S -> Prop), HasProp P (Subtype p)]

section

variable {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) (a : Fiber r)

/--
Definition of `fiber` / `fiber` 的定义

English:
abbreviation fiber
  signature: : CompHausLike.{u} P
  body: CompHausLike.of P a.val

中文:
缩写 fiber
  签名: : 余mpHausLike.{u} P
  定义体: CompHausLike.of P a.val

Depends on / 依赖: CompHausLike, CompHausLike.of, a.val
-/
abbrev fiber : CompHausLike.{u} P := CompHausLike.of P a.val

/--
Definition of `sigmaIncl` / `sigmaIncl` 的定义

English:
definition sigmaIncl
  signature: : fiber r a ⟶ Q
  body: ofHom _ (TopologicalSpace.Fiber.sigmaIncl _ a)

中文:
定义 sigmaIncl
  签名: : fiber r a ⟶ Q
  定义体: ofHom _ (TopologicalSpace.Fiber.sigmaIncl _ a)

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Fiber.sigmaIncl, sigmaIncl
-/
def sigmaIncl : fiber r a ⟶ Q := ofHom _ (TopologicalSpace.Fiber.sigmaIncl _ a)

/--
Definition of `sigmaIso` / `sigmaIso` 的定义

English:
definition sigmaIso
  signature: [HasExplicitFiniteCoproducts.{u} P]
  body: isoOfBijective (ofHom _ (sigmaIsoHom r)) ⟨sigmaIsoHom_inj r, sigmaIsoHom_surj r⟩

中文:
定义 sigmaIso
  签名: [有ExplicitFiniteCoproducts.{u} P]
  定义体: isoOfBijective (ofHom _ (sigmaIsoHom r)) ⟨sigmaIsoHom_inj r, sigmaIsoHom_surj r⟩

Depends on / 依赖: isoOfBijective, sigmaIsoHom, sigmaIsoHom_inj, sigmaIsoHom_surj
-/
noncomputable def sigmaIso [HasExplicitFiniteCoproducts.{u} P] : (finiteCoproduct (fiber r)) ≅ Q :=
  isoOfBijective (ofHom _ (sigmaIsoHom r)) ⟨sigmaIsoHom_inj r, sigmaIsoHom_surj r⟩

/--
lemma `sigmaComparison_comp_sigmaIso` / 引理 `sigmaComparison_comp_sigmaIso`

English:
lemma sigmaComparison_comp_sigmaIso
  statement: [HasExplicitFiniteCoproducts.{u} P]
  proof: by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, sigmaComparison, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
    ← X.map_comp_apply]
  rfl

中文:
引理 sigmaComparison_comp_sigmaIso
  结论: [有ExplicitFiniteCoproducts.{u} P]
  证明: by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, sigmaComparison, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
    ← X.map_comp_apply]
  rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, CoeFun, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.mapIso_hom, Iso.op_hom, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, X.map_comp_apply, coe_mk, comp_apply, hom_ofHom, mapIso_hom, map_comp_apply, op_hom, sigmaComparison, toCoeFun
-/
lemma sigmaComparison_comp_sigmaIso [HasExplicitFiniteCoproducts.{u} P]
    (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) :
    (X.mapIso (sigmaIso r).op).hom ≫ sigmaComparison X (fun a => (fiber r a).1) ≫
      (↾fun g => g a) = X.map (sigmaIncl r a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, sigmaComparison, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
    ← X.map_comp_apply]
  rfl

end

variable {S : CompHausLike.{u} P} {Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)}
  [HasProp P PUnit.{u + 1}] (f : LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u + 1}))))

/--
Definition of `counitAppAppImage` / `counitAppAppImage` 的定义

English:
definition counitAppAppImage
  signature: : (a : Fiber f) -> Y.obj ⟨fiber f a⟩
  body: fun a => Y.map (CompHausLike.isTerminalPUnit.from _).op a.image

中文:
定义 counitAppAppImage
  签名: : (a : Fiber f) -> Y.obj ⟨fiber f a⟩
  定义体: fun a => Y.map (CompHausLike.isTerminalPUnit.from _).op a.image

Depends on / 依赖: CompHausLike, CompHausLike.isTerminalPUnit.from, Y.map, a.image, isTerminalPUnit
-/
noncomputable def counitAppAppImage : (a : Fiber f) -> Y.obj ⟨fiber f a⟩ :=
  fun a => Y.map (CompHausLike.isTerminalPUnit.from _).op a.image

/--
Definition of `counitAppApp` / `counitAppApp` 的定义

English:
definition counitAppApp
  signature: (S : CompHausLike.{u} P)
  body: ↾fun r => (inv (sigmaComparison Y (fun a => (fiber r a).1)) ≫
    (Y.mapIso (sigmaIso r).op).inv) (counitAppAppImage r)

中文:
定义 counitAppApp
  签名: (S : 余mpHausLike.{u} P)
  定义体: ↾fun r => (inv (sigmaComparison Y (fun a => (fiber r a).1)) ≫
    (Y.mapIso (sigmaIso r).op).inv) (counitAppAppImage r)

Depends on / 依赖: Y.mapIso, counitAppAppImage, mapIso, sigmaComparison, sigmaIso
-/
noncomputable def counitAppApp (S : CompHausLike.{u} P)
    (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w))
    [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P] :
    LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u + 1}))) ⟶ Y.obj ⟨S⟩ :=
  ↾fun r => (inv (sigmaComparison Y (fun a => (fiber r a).1)) ≫
    (Y.mapIso (sigmaIso r).op).inv) (counitAppAppImage r)

-- This is the key lemma to prove naturality of the counit:
/--
lemma `presheaf_ext` / 引理 `presheaf_ext`

English:
lemma presheaf_ext
  statement: (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w))
  proof: by
  apply injective_of_mono (X.mapIso (sigmaIso f).op).hom
  apply injective_of_mono (sigmaComparison X (fun a => (fiber f a).1))
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h

中文:
引理 presheaf_ext
  结论: (X : (余mpHausLike.{u} P)ᵒᵖ ⥤ 类型 (最大值 u w))
  证明: by
  apply injective_of_mono (X.mapIso (sigmaIso f).op).hom
  apply injective_of_mono (sigmaComparison X (fun a => (fiber f a).1))
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h

Depends on / 依赖: X.mapIso, injective_of_mono, mapIso, sigmaComparison, sigmaComparison_comp_sigmaIso, sigmaIso, specialize
-/
lemma presheaf_ext (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w))
    [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩)
    [HasExplicitFiniteCoproducts.{u} P]
    (h : forall (a : Fiber f), X.map (sigmaIncl f a).op x = X.map (sigmaIncl f a).op y) : x = y := by
  apply injective_of_mono (X.mapIso (sigmaIso f).op).hom
  apply injective_of_mono (sigmaComparison X (fun a => (fiber f a).1))
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h

/--
lemma `incl_of_counitAppApp` / 引理 `incl_of_counitAppApp`

English:
lemma incl_of_counitAppApp
  statement: [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P]
  proof: by
  rw [← sigmaComparison_comp_sigmaIso]; rw [Functor.mapIso_hom]; rw [Iso.op_hom]; rw [types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Functor.map_comp_apply, Iso.inv_hom_id,
    Functor.map_id_apply]
  exact congrFun (Iso.inv_hom_id_apply (asIso (sigmaComparison Y (fun a => (fiber f a).1)))
    (counitAppAppImage f)) _

中文:
引理 incl_of_counitAppApp
  结论: [保持FiniteProducts Y] [有ExplicitFiniteCoproducts.{u} P]
  证明: by
  rw [← sigmaComparison_comp_sigmaIso]; rw [Functor.mapIso_hom]; rw [Iso.op_hom]; rw [types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Functor.map_comp_apply, Iso.inv_hom_id,
    Functor.map_id_apply]
  exact congrFun (Iso.inv_hom_id_apply (asIso (sigmaComparison Y (fun a => (fiber f a).1)))
    (counitAppAppImage f)) _

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp_apply, Functor.map_id_apply, Iso.inv_hom_id, Iso.inv_hom_id_apply, Iso.op_hom, TypeCat, TypeCat.Fun.coe_mk, coe_fn_eq, coe_fn_eq.symm, coe_mk, comp_apply, counitAppApp, counitAppAppImage
-/
lemma incl_of_counitAppApp [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P]
    (a : Fiber f) : Y.map (sigmaIncl f a).op (counitAppApp S Y f) = counitAppAppImage f a := by
  rw [← sigmaComparison_comp_sigmaIso]; rw [Functor.mapIso_hom]; rw [Iso.op_hom]; rw [types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Functor.map_comp_apply, Iso.inv_hom_id,
    Functor.map_id_apply]
  exact congrFun (Iso.inv_hom_id_apply (asIso (sigmaComparison Y (fun a => (fiber f a).1)))
    (counitAppAppImage f)) _

variable {T : CompHausLike.{u} P} (g : T ⟶ S)

/--
Definition of `componentHom` / `componentHom` 的定义

English:
definition componentHom
  signature: (a : Fiber (f.comap g.hom.hom))
  body: ConcreteCategory.ofHom
  { toFun x := ⟨g x.val, by
      simp only [Fiber.mk, Set.mem_preimage, Set.mem_singleton_iff]
      convert! map_eq_image _ _ x
      exact map_preimage_eq_image_map _ _ a⟩
    continuous_toFun := by fun_prop }

中文:
定义 componentHom
  签名: (a : Fiber (f.comap g.hom.hom))
  定义体: ConcreteCategory.ofHom
  { toFun x := ⟨g x.val, by
      simp only [Fiber.mk, Set.mem_preimage, Set.mem_singleton_iff]
      convert! map_eq_image _ _ x
      exact map_preimage_eq_image_map _ _ a⟩
    continuous_toFun := by fun_prop }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Fiber.mk, Set.mem_preimage, Set.mem_singleton_iff, continuous_toFun, convert, fun_prop, map_eq_image, map_preimage_eq_image_map, mem_preimage, mem_singleton_iff, x.val
-/
noncomputable def componentHom (a : Fiber (f.comap g.hom.hom)) :
    fiber _ a ⟶ fiber _ (Fiber.mk f (g a.preimage)) :=
  ConcreteCategory.ofHom
  { toFun x := ⟨g x.val, by
      simp only [Fiber.mk, Set.mem_preimage, Set.mem_singleton_iff]
      convert! map_eq_image _ _ x
      exact map_preimage_eq_image_map _ _ a⟩
    continuous_toFun := by fun_prop }

/--
lemma `incl_comap` / 引理 `incl_comap`

English:
lemma incl_comap
  statement: {S T : (CompHausLike P)ᵒᵖ}
  proof: rfl

中文:
引理 incl_comap
  结论: {S T : (余mpHausLike P)ᵒᵖ}
  证明: rfl
-/
lemma incl_comap {S T : (CompHausLike P)ᵒᵖ}
    (f : LocallyConstant S.unop (Y.obj (op (CompHausLike.of P PUnit.{u + 1}))))
      (g : S ⟶ T) (a : Fiber (f.comap g.unop.hom.hom)) :
        g ≫ (sigmaIncl (f.comap g.unop.hom.hom) a).op =
          (sigmaIncl f _).op ≫ (componentHom f g.unop a).op :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit is natural in `S : CompHausLike P` -/
@[simps! app]
/--
Definition of `counitApp` / `counitApp` 的定义

English:
definition counitApp
  signature: [HasExplicitFiniteCoproducts.{u} P]
  body: fun ⟨S⟩ => counitAppApp S Y
  naturality := by
    intro S T g
    ext f
    apply presheaf_ext (f.comap g.unop.hom.hom)
    intro a
    simp only [op_unop, functorToPresheaves_obj_obj, functorToPresheaves_obj_map,
      TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk]
    rw [incl_of_counitAppApp]; rw [← Functor.map_comp_apply]; rw [incl_comap]; rw [Functor.map_comp_apply]; rw [incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    apply congrArg
    exact image_eq_image_mk (g := g.unop) (a := a)

中文:
定义 counitApp
  签名: [有ExplicitFiniteCoproducts.{u} P]
  定义体: fun ⟨S⟩ => counitAppApp S Y
  naturality := by
    intro S T g
    ext f
    apply presheaf_ext (f.comap g.unop.hom.hom)
    intro a
    simp only [op_unop, functorToPresheaves_obj_obj, functorToPresheaves_obj_map,
      TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk]
    rw [incl_of_counitAppApp]; rw [← Functor.map_comp_apply]; rw [incl_comap]; rw [Functor.map_comp_apply]; rw [incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    apply congrArg
    exact image_eq_image_mk (g := g.unop) (a := a)

Depends on / 依赖: counitAppApp
-/
noncomputable def counitApp [HasExplicitFiniteCoproducts.{u} P]
    (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts Y] :
    (functorToPresheaves.obj (Y.obj (op (CompHausLike.of P PUnit.{u + 1})))) ⟶ Y where
  app := fun ⟨S⟩ => counitAppApp S Y
  naturality := by
    intro S T g
    ext f
    apply presheaf_ext (f.comap g.unop.hom.hom)
    intro a
    simp only [op_unop, functorToPresheaves_obj_obj, functorToPresheaves_obj_map,
      TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk]
    rw [incl_of_counitAppApp]; rw [← Functor.map_comp_apply]; rw [incl_comap]; rw [Functor.map_comp_apply]; rw [incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    apply congrArg
    exact image_eq_image_mk (g := g.unop) (a := a)

variable (P) (X : TopCat.{max u w})
    [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks P]
    (hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surjective f)

/--
Definition of `functorToPresheavesIso` / `functorToPresheavesIso` 的定义

English:
definition functorToPresheavesIso
  signature: (X : Type (max u w))
  body: NatIso.ofComponents (fun S => locallyConstantIsoContinuousMap _ _)

中文:
定义 functorToPresheavesIso
  签名: (X : 类型 (最大值 u w))
  定义体: NatIso.ofComponents (fun S => locallyConstantIsoContinuousMap _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, locallyConstantIsoContinuousMap, ofComponents
-/
noncomputable def functorToPresheavesIso (X : Type (max u w)) :
    functorToPresheaves.{u, w}.obj X ≅ ((TopCat.discrete.obj X).toSheafCompHausLike P hs).obj :=
  NatIso.ofComponents (fun S => locallyConstantIsoContinuousMap _ _)

/-- `CompHausLike.LocallyConstant.functorToPresheaves` lands in sheaves. -/
@[simps! obj_obj_obj obj_obj_map map_hom_app]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: :
  body: CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) :=
  ObjectProperty.lift _ (functorToPresheaves.{u, w}) (fun X => by
    rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIso P hs X)]
    exact ((TopCat.discrete.obj X).toSheafCompHausLike P hs).property)

@[deprecated (since := "2026-03-20")] alias functor_obj_obj := functor_obj_obj_obj
@[deprecated (since := "2026-03-20")] alias functor_map_hom := functor_map_hom_app

中文:
定义 functor
  签名: :
  定义体: CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) :=
  ObjectProperty.lift _ (functorToPresheaves.{u, w}) (fun X => by
    rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIso P hs X)]
    exact ((TopCat.discrete.obj X).toSheafCompHausLike P hs).property)

@[deprecated (since := "2026-03-20")] alias functor_obj_obj := functor_obj_obj_obj
@[deprecated (since := "2026-03-20")] alias functor_map_hom := functor_map_hom_app

Depends on / 依赖: CompHausLike, CompHausLike.preregular, preregular
-/
def functor :
    haveI := CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) :=
  ObjectProperty.lift _ (functorToPresheaves.{u, w}) (fun X => by
    rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIso P hs X)]
    exact ((TopCat.discrete.obj X).toSheafCompHausLike P hs).property)

@[deprecated (since := "2026-03-20")] alias functor_obj_obj := functor_obj_obj_obj
@[deprecated (since := "2026-03-20")] alias functor_map_hom := functor_map_hom_app

/--
Definition of `functorIso` / `functorIso` 的定义

English:
definition functorIso
  signature: :
  body: NatIso.ofComponents (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIso P hs X))

中文:
定义 functorIso
  签名: :
  定义体: NatIso.ofComponents (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIso P hs X))

Depends on / 依赖: NatIso, NatIso.ofComponents, fullyFaithfulSheafToPresheaf, functorToPresheavesIso, ofComponents, preimageIso
-/
noncomputable def functorIso :
    functor.{u, w} P hs ≅ TopCat.discrete.{max w u} ⋙ topCatToSheafCompHausLike P hs :=
  NatIso.ofComponents (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIso P hs X))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit is natural in both `S : CompHausLike P` and
`Y : Sheaf (coherentTopology (CompHausLike P)) (Type (max u w))` -/
@[simps!]
/--
Definition of `counit` / `counit` 的定义

English:
definition counit
  signature: [HasExplicitFiniteCoproducts.{u} P]
  body: CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ ⋙ functor.{u, w} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X := haveI := CompHausLike.preregular hs
    (ObjectProperty.homMk) (counitApp X.obj)
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply InducedCategory.hom_ext
    simp only [functor, Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj,
      ObjectProperty.lift_obj_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      ObjectProperty.ι_map, ObjectProperty.lift_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, Functor.id_map]
    ext S (f : LocallyConstant _ _)
    simp only [NatTrans.comp_app, counitApp_app, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply]
    apply presheaf_ext (f.map (g.hom.app (op (CompHausLike.of P PUnit.{u + 1}))))
    intro a
    simp only [functorToPresheaves_obj_obj, functorToPresheaves_map_app, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, dsimp% incl_of_counitAppApp]
    apply presheaf_ext (f.comap (sigmaIncl _ _).hom.hom)
    intro b
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp,
      map_apply, IsTerminal.comp_from, ← map_preimage_eq_image_map]
    change (_ ≫ Y.obj.map _) _ = (_ ≫ Y.obj.map _) _
    simp only [← g.hom.naturality]
    rw [show sigmaIncl (f.comap (sigmaIncl (f.map _) a).hom.hom) b ≫ sigmaIncl (f.map _) a =
        CompHausLike.ofHom P (X := fiber _ b) (sigmaInclIncl f _ a b) ≫ sigmaIncl f (Fiber.mk f _)
      by ext; rfl]
    simp only [op_comp, Functor.map_comp, types_comp_apply, dsimp% incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    rw [mk_image]
    change (X.obj.map _ ≫ _) _ = (X.obj.map _ ≫ _) _
    simp only [g.hom.naturality]
    simp only [types_comp_apply]
    have := map_preimage_eq_image (f := g.hom.app _ ∘ f) (a := a)
    simp only [Function.comp_apply] at this
    rw [this]
    apply congrArg
    symm
    convert! (b.preimage).prop
    exact (mem_iff_eq_image (g.hom.app _ ∘ f) _ _).symm

中文:
定义 counit
  签名: [有ExplicitFiniteCoproducts.{u} P]
  定义体: CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ ⋙ functor.{u, w} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X := haveI := CompHausLike.preregular hs
    (ObjectProperty.homMk) (counitApp X.obj)
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply InducedCategory.hom_ext
    simp only [functor, Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj,
      ObjectProperty.lift_obj_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      ObjectProperty.ι_map, ObjectProperty.lift_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, Functor.id_map]
    ext S (f : LocallyConstant _ _)
    simp only [NatTrans.comp_app, counitApp_app, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply]
    apply presheaf_ext (f.map (g.hom.app (op (CompHausLike.of P PUnit.{u + 1}))))
    intro a
    simp only [functorToPresheaves_obj_obj, functorToPresheaves_map_app, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, dsimp% incl_of_counitAppApp]
    apply presheaf_ext (f.comap (sigmaIncl _ _).hom.hom)
    intro b
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp,
      map_apply, IsTerminal.comp_from, ← map_preimage_eq_image_map]
    change (_ ≫ Y.obj.map _) _ = (_ ≫ Y.obj.map _) _
    simp only [← g.hom.naturality]
    rw [show sigmaIncl (f.comap (sigmaIncl (f.map _) a).hom.hom) b ≫ sigmaIncl (f.map _) a =
        CompHausLike.ofHom P (X := fiber _ b) (sigmaInclIncl f _ a b) ≫ sigmaIncl f (Fiber.mk f _)
      by ext; rfl]
    simp only [op_comp, Functor.map_comp, types_comp_apply, dsimp% incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    rw [mk_image]
    change (X.obj.map _ ≫ _) _ = (X.obj.map _ ≫ _) _
    simp only [g.hom.naturality]
    simp only [types_comp_apply]
    have := map_preimage_eq_image (f := g.hom.app _ ∘ f) (a := a)
    simp only [Function.comp_apply] at this
    rw [this]
    apply congrArg
    symm
    convert! (b.preimage).prop
    exact (mem_iff_eq_image (g.hom.app _ ∘ f) _ _).symm

Depends on / 依赖: CompHausLike, CompHausLike.preregular, preregular
-/
noncomputable def counit [HasExplicitFiniteCoproducts.{u} P] : haveI := CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ ⋙ functor.{u, w} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X := haveI := CompHausLike.preregular hs
    (ObjectProperty.homMk) (counitApp X.obj)
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply InducedCategory.hom_ext
    simp only [functor, Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj,
      ObjectProperty.lift_obj_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      ObjectProperty.ι_map, ObjectProperty.lift_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, Functor.id_map]
    ext S (f : LocallyConstant _ _)
    simp only [NatTrans.comp_app, counitApp_app, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply]
    apply presheaf_ext (f.map (g.hom.app (op (CompHausLike.of P PUnit.{u + 1}))))
    intro a
    simp only [functorToPresheaves_obj_obj, functorToPresheaves_map_app, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, dsimp% incl_of_counitAppApp]
    apply presheaf_ext (f.comap (sigmaIncl _ _).hom.hom)
    intro b
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp,
      map_apply, IsTerminal.comp_from, ← map_preimage_eq_image_map]
    change (_ ≫ Y.obj.map _) _ = (_ ≫ Y.obj.map _) _
    simp only [← g.hom.naturality]
    rw [show sigmaIncl (f.comap (sigmaIncl (f.map _) a).hom.hom) b ≫ sigmaIncl (f.map _) a =
        CompHausLike.ofHom P (X := fiber _ b) (sigmaInclIncl f _ a b) ≫ sigmaIncl f (Fiber.mk f _)
      by ext; rfl]
    simp only [op_comp, Functor.map_comp, types_comp_apply, dsimp% incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    rw [mk_image]
    change (X.obj.map _ ≫ _) _ = (X.obj.map _ ≫ _) _
    simp only [g.hom.naturality]
    simp only [types_comp_apply]
    have := map_preimage_eq_image (f := g.hom.app _ ∘ f) (a := a)
    simp only [Function.comp_apply] at this
    rw [this]
    apply congrArg
    symm
    convert! (b.preimage).prop
    exact (mem_iff_eq_image (g.hom.app _ ∘ f) _ _).symm

/--
The unit of the adjunction is given by mapping each element to the corresponding constant map.
-/
@[simps]
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  body: ↾fun x => LocallyConstant.const _ x

中文:
定义 unit
  签名: : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨余mpHausLike.of P 命题单元.{u + 1}⟩ where
  定义体: ↾fun x => LocallyConstant.const _ x

Depends on / 依赖: LocallyConstant, LocallyConstant.const
-/
def unit : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  app _ := ↾fun x => LocallyConstant.const _ x

/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (Type (max u w)) ≅ functor.{u, w} P hs ⋙
  body: unit P hs
  inv := { app _ := ↾fun f => f.toFun PUnit.unit }

中文:
定义 unitIso
  签名: : 𝟭 (类型 (最大值 u w)) ≅ functor.{u, w} P hs ⋙
  定义体: unit P hs
  inv := { app _ := ↾fun f => f.toFun PUnit.unit }

Depends on / 依赖: MyEmbedding, MyEmbedding.toFun
-/
noncomputable def unitIso : 𝟭 (Type (max u w)) ≅ functor.{u, w} P hs ⋙
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  hom := unit P hs
  inv := { app _ := ↾fun f => f.toFun PUnit.unit }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `adjunction_left_triangle` / 引理 `adjunction_left_triangle`

English:
lemma adjunction_left_triangle
  statement: [HasExplicitFiniteCoproducts.{u} P]
  proof: by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, functor_obj_obj_obj, functorToPresheaves_obj_obj, Functor.comp_obj,
    Functor.flip_obj_obj, ObjectProperty.ι_obj, unit_app, NatTrans.comp_app,
    functorToPresheaves_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.Fun.coe_mk, NatTrans.id_app, id_apply]
  simp only [counit]
  have := CompHausLike.preregular hs
  apply presheaf_ext
    (X := ((functor P hs).obj X).obj) (Y := ((functor.{u, w} P hs).obj X).obj)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_obj_obj, Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj,
    ObjectProperty.ι_obj, unit_app, counitAppAppImage, functor_obj_obj_map,
    Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom]
  ext x
  erw [← map_eq_image _ a x]
  rfl

中文:
引理 adjunction_left_triangle
  结论: [有ExplicitFiniteCoproducts.{u} P]
  证明: by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, functor_obj_obj_obj, functorToPresheaves_obj_obj, Functor.comp_obj,
    Functor.flip_obj_obj, ObjectProperty.ι_obj, unit_app, NatTrans.comp_app,
    functorToPresheaves_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.Fun.coe_mk, NatTrans.id_app, id_apply]
  simp only [counit]
  have := CompHausLike.preregular hs
  apply presheaf_ext
    (X := ((functor P hs).obj X).obj) (Y := ((functor.{u, w} P hs).obj X).obj)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_obj_obj, Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj,
    ObjectProperty.ι_obj, unit_app, counitAppAppImage, functor_obj_obj_map,
    Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom]
  ext x
  erw [← map_eq_image _ a x]
  rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, CompHausLike, CompHausLike.preregular, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.comp_obj, Functor.flip_obj_obj, Functor.id_obj, LocallyConstant, MyEmbedding, MyEmbedding.injective, NatTrans, NatTrans.comp_app, NatTrans.id_app, ObjectProperty, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply
-/
lemma adjunction_left_triangle [HasExplicitFiniteCoproducts.{u} P]
    (X : Type (max u w)) : functorToPresheaves.{u, w}.map ((unit P hs).app X) ≫
      ((counit P hs).app ((functor P hs).obj X)).hom = 𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, functor_obj_obj_obj, functorToPresheaves_obj_obj, Functor.comp_obj,
    Functor.flip_obj_obj, ObjectProperty.ι_obj, unit_app, NatTrans.comp_app,
    functorToPresheaves_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.Fun.coe_mk, NatTrans.id_app, id_apply]
  simp only [counit]
  have := CompHausLike.preregular hs
  apply presheaf_ext
    (X := ((functor P hs).obj X).obj) (Y := ((functor.{u, w} P hs).obj X).obj)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_obj_obj, Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj,
    ObjectProperty.ι_obj, unit_app, counitAppAppImage, functor_obj_obj_map,
    Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom]
  ext x
  erw [← map_eq_image _ a x]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
`CompHausLike.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
@[simps]
/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: [HasExplicitFiniteCoproducts.{u} P]
  body: unit P hs
  counit := counit P hs
  left_triangle_components := by
    intro X
    ext : 1
    exact adjunction_left_triangle P hs X
  right_triangle_components X := by
    ext (x : X.obj.obj _)
    dsimp
    have := CompHausLike.preregular hs
    let : PreservesFiniteProducts ((sheafToPresheaf (coherentTopology _) _).obj X) :=
      inferInstanceAs (PreservesFiniteProducts X.obj)
    apply presheaf_ext ((unit P hs).app _ x)
    intro a
    erw [incl_of_counitAppApp]
    simp only [counitAppAppImage]
    erw [← map_eq_image _ a ⟨PUnit.unit, by simp [mem_iff_eq_image, ← map_preimage_eq_image]⟩]
    rfl

中文:
定义 adjunction
  签名: [有ExplicitFiniteCoproducts.{u} P]
  定义体: unit P hs
  counit := counit P hs
  left_triangle_components := by
    intro X
    ext : 1
    exact adjunction_left_triangle P hs X
  right_triangle_components X := by
    ext (x : X.obj.obj _)
    dsimp
    have := CompHausLike.preregular hs
    let : PreservesFiniteProducts ((sheafToPresheaf (coherentTopology _) _).obj X) :=
      inferInstanceAs (PreservesFiniteProducts X.obj)
    apply presheaf_ext ((unit P hs).app _ x)
    intro a
    erw [incl_of_counitAppApp]
    simp only [counitAppAppImage]
    erw [← map_eq_image _ a ⟨PUnit.unit, by simp [mem_iff_eq_image, ← map_preimage_eq_image]⟩]
    rfl

Depends on / 依赖: MyEmbeddingClass, MyEmbeddingClass.map_op, map_op
-/
noncomputable def adjunction [HasExplicitFiniteCoproducts.{u} P] :
    functor.{u, w} P hs ⊣ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  unit := unit P hs
  counit := counit P hs
  left_triangle_components := by
    intro X
    ext : 1
    exact adjunction_left_triangle P hs X
  right_triangle_components X := by
    ext (x : X.obj.obj _)
    dsimp
    have := CompHausLike.preregular hs
    let : PreservesFiniteProducts ((sheafToPresheaf (coherentTopology _) _).obj X) :=
      inferInstanceAs (PreservesFiniteProducts X.obj)
    apply presheaf_ext ((unit P hs).app _ x)
    intro a
    erw [incl_of_counitAppApp]
    simp only [counitAppAppImage]
    erw [← map_eq_image _ a ⟨PUnit.unit, by simp [mem_iff_eq_image, ← map_preimage_eq_image]⟩]
    rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExplicitFiniteCoproducts.{u}
  signature: P] : IsIso (adjunction P hs).unit
  body: inferInstanceAs (IsIso (unitIso P hs).hom)

中文:
实例 [有ExplicitFiniteCoproducts.{u}
  签名: P] : 是同构 (adjunction P hs).unit
  定义体: inferInstanceAs (IsIso (unitIso P hs).hom)

Depends on / 依赖: unitIso
-/
instance [HasExplicitFiniteCoproducts.{u} P] : IsIso (adjunction P hs).unit :=
  inferInstanceAs (IsIso (unitIso P hs).hom)

end Adjunction

end CompHausLike.LocallyConstant

section Condensed

open Condensed CompHausLike

namespace CondensedSet.LocallyConstant

/--
Definition of `functor` / `functor` 的定义

English:
abbreviation functor
  signature: : Type (u + 1) ⥤ CondensedSet.{u}
  body: CompHausLike.LocallyConstant.functor.{u, u + 1} (P := fun _ => True)
    (hs := fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

中文:
缩写 functor
  签名: : 类型 (u + 1) ⥤ CondensedSet.{u}
  定义体: CompHausLike.LocallyConstant.functor.{u, u + 1} (P := fun _ => True)
    (hs := fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, CompHausLike, CompHausLike.LocallyConstant.functor, LocallyConstant, effectiveEpi_tfae, functor
-/
abbrev functor : Type (u + 1) ⥤ CondensedSet.{u} :=
  CompHausLike.LocallyConstant.functor.{u, u + 1} (P := fun _ => True)
    (hs := fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : functor ≅ discrete (Type (u + 1))
  body: (LocallyConstant.adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)

中文:
定义 iso
  签名: : functor ≅ discrete (类型 (u + 1))
  定义体: (LocallyConstant.adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)

Depends on / 依赖: LocallyConstant, LocallyConstant.adjunction, adjunction, discreteUnderlyingAdj, leftAdjointUniq
-/
noncomputable def iso : functor ≅ discrete (Type (u + 1)) :=
  (LocallyConstant.adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)

/--
Definition of `functorFullyFaithful` / `functorFullyFaithful` 的定义

English:
definition functorFullyFaithful
  signature: : functor.FullyFaithful
  body: (LocallyConstant.adjunction.{u, u + 1} _ _).fullyFaithfulLOfIsIsoUnit

中文:
定义 functorFullyFaithful
  签名: : functor.满忠实
  定义体: (LocallyConstant.adjunction.{u, u + 1} _ _).fullyFaithfulLOfIsIsoUnit

Depends on / 依赖: LocallyConstant, LocallyConstant.adjunction, adjunction, fullyFaithfulLOfIsIsoUnit
-/
noncomputable def functorFullyFaithful : functor.FullyFaithful :=
  (LocallyConstant.adjunction.{u, u + 1} _ _).fullyFaithfulLOfIsIsoUnit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: functor.Faithful
  body: functorFullyFaithful.faithful

中文:
实例 :
  签名: functor.忠实
  定义体: functorFullyFaithful.faithful

Depends on / 依赖: faithful, functorFullyFaithful, functorFullyFaithful.faithful
-/
noncomputable instance : functor.Faithful := functorFullyFaithful.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: functor.Full
  body: functorFullyFaithful.full

中文:
实例 :
  签名: functor.满
  定义体: functorFullyFaithful.full

Depends on / 依赖: functorFullyFaithful, functorFullyFaithful.full
-/
noncomputable instance : functor.Full := functorFullyFaithful.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (discrete <| Type _).Faithful
  body: Functor.Faithful.of_iso iso

中文:
实例 :
  签名: (discrete <| 类型 _).忠实
  定义体: Functor.Faithful.of_iso iso

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, of_iso
-/
instance : (discrete <| Type _).Faithful := Functor.Faithful.of_iso iso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (discrete <| Type _).Full
  body: Functor.Full.of_iso iso

中文:
实例 :
  签名: (discrete <| 类型 _).满
  定义体: Functor.Full.of_iso iso

Depends on / 依赖: Functor, Functor.Full.of_iso, of_iso
-/
noncomputable instance : (discrete <| Type _).Full := Functor.Full.of_iso iso

end CondensedSet.LocallyConstant

namespace LightCondSet.LocallyConstant

/--
Definition of `functor` / `functor` 的定义

English:
abbreviation functor
  signature: : Type u ⥤ LightCondSet.{u}
  body: CompHausLike.LocallyConstant.functor.{u, u}
    (P := fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

中文:
缩写 functor
  签名: : 类型u ⥤ LightCondSet.{u}
  定义体: CompHausLike.LocallyConstant.functor.{u, u}
    (P := fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstant.functor, LightProfinite, LightProfinite.effectiveEpi_iff_surjective, LocallyConstant, SecondCountableTopology, TotallyDisconnectedSpace, effectiveEpi_iff_surjective, f.toFun, functor
-/
abbrev functor : Type u ⥤ LightCondSet.{u} :=
  CompHausLike.LocallyConstant.functor.{u, u}
    (P := fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

instance (S : LightProfinite.{u}) (p : S -> Prop) :
    HasProp (fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X) (Subtype p) :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace (Subtype p)),
    (inferInstance : SecondCountableTopology {s | p s})⟩⟩

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : functor ≅ LightCondensed.discrete (Type u)
  body: (LocallyConstant.adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)

中文:
定义 iso
  签名: : functor ≅ LightCondensed.discrete (类型u)
  定义体: (LocallyConstant.adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)

Depends on / 依赖: LightCondensed, LightCondensed.discreteUnderlyingAdj, LocallyConstant, LocallyConstant.adjunction, adjunction, discreteUnderlyingAdj, leftAdjointUniq
-/
noncomputable def iso : functor ≅ LightCondensed.discrete (Type u) :=
  (LocallyConstant.adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)

/--
Definition of `functorFullyFaithful` / `functorFullyFaithful` 的定义

English:
definition functorFullyFaithful
  signature: : functor.{u}.FullyFaithful
  body: (LocallyConstant.adjunction _ _).fullyFaithfulLOfIsIsoUnit

中文:
定义 functorFullyFaithful
  签名: : functor.{u}.满忠实
  定义体: (LocallyConstant.adjunction _ _).fullyFaithfulLOfIsIsoUnit

Depends on / 依赖: LocallyConstant, LocallyConstant.adjunction, adjunction, fullyFaithfulLOfIsIsoUnit
-/
noncomputable def functorFullyFaithful : functor.{u}.FullyFaithful :=
  (LocallyConstant.adjunction _ _).fullyFaithfulLOfIsIsoUnit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: functor.{u}.Faithful
  body: functorFullyFaithful.faithful

中文:
实例 :
  签名: functor.{u}.忠实
  定义体: functorFullyFaithful.faithful

Depends on / 依赖: faithful, functorFullyFaithful, functorFullyFaithful.faithful
-/
instance : functor.{u}.Faithful := functorFullyFaithful.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LightCondSet.LocallyConstant.functor.Full
  body: functorFullyFaithful.full

中文:
实例 :
  签名: LightCondSet.局部常数.functor.满
  定义体: functorFullyFaithful.full

Depends on / 依赖: functorFullyFaithful, functorFullyFaithful.full
-/
instance : LightCondSet.LocallyConstant.functor.Full := functorFullyFaithful.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (LightCondensed.discrete <| Type u).Faithful
  body: Functor.Faithful.of_iso iso.{u}

中文:
实例 :
  签名: (LightCondensed.discrete <| 类型u).忠实
  定义体: Functor.Faithful.of_iso iso.{u}

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, of_iso
-/
instance : (LightCondensed.discrete <| Type u).Faithful := Functor.Faithful.of_iso iso.{u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (LightCondensed.discrete <| Type u).Full
  body: Functor.Full.of_iso iso.{u}

中文:
实例 :
  签名: (LightCondensed.discrete <| 类型u).满
  定义体: Functor.Full.of_iso iso.{u}

Depends on / 依赖: Functor, Functor.Full.of_iso, of_iso
-/
instance : (LightCondensed.discrete <| Type u).Full := Functor.Full.of_iso iso.{u}

end LightCondSet.LocallyConstant

end Condensed
