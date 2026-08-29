/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.Topology.Category.TopCat.OpenNhds
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the composition of the inclusion of categories
`(OpenNhds x)ᵒᵖ ⥤ (Opens X)ᵒᵖ` and the functor `F : (Opens X)ᵒᵖ ⥤ C`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalkFunctor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalkPushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `MonCat`,
`CommRingCat`,...) is that they preserve filtered colimits. Since stalks are filtered colimits,
this ensures that the stalks of presheaves valued in these categories behave exactly as for
`Type`-valued presheaves. For example, in `exists_germ_eq` we prove that in such a category, every
element of the stalk is the germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

TODO(@joelriou): refactor the definitions in this file so as to make them
particular cases of general constructions for points of sites from
`Mathlib/CategoryTheory/Sites/Point/Basic.lean`.

-/

@[expose] public section

assert_not_exists IsOrderedMonoid

noncomputable section

universe v u v' u'

open CategoryTheory

open TopCat

open CategoryTheory.Limits CategoryTheory.Functor

open TopologicalSpace Topology

open Opposite

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]
variable [HasColimits.{v} C]
variable {X Y Z : TopCat.{v}}

namespace TopCat.Presheaf

variable (C) in
/--
Definition of `stalkFunctor` / `stalkFunctor` 的定义

English:
definition stalkFunctor
  signature: (x : X)
  body: (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

中文:
定义 stalkFunctor
  签名: (x : X)
  定义体: (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

Depends on / 依赖: OpenNhds, OpenNhds.inclusion, inclusion, whiskeringLeft
-/
def stalkFunctor (x : X) : X.Presheaf C ⥤ C :=
  (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

/--
Definition of `stalk` / `stalk` 的定义

English:
definition stalk
  signature: (ℱ : X.Presheaf C) (x : X)
  body: (stalkFunctor C x).obj ℱ

中文:
定义 stalk
  签名: (ℱ : X.Presheaf C) (x : X)
  定义体: (stalkFunctor C x).obj ℱ

Depends on / 依赖: stalkFunctor
-/
def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ

-- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)
@[simp]
/--
theorem `stalkFunctor_obj` / 定理 `stalkFunctor_obj`

English:
theorem stalkFunctor_obj
  given: (ℱ : X.Presheaf C) (x : X)
  statement: (stalkFunctor C x).obj ℱ = ℱ.stalk x
  proof: rfl

中文:
定理 stalkFunctor_obj
  条件: (ℱ : X.Presheaf C) (x : X)
  结论: (stalkFunctor C x).obj ℱ = ℱ.stalk x
  证明: rfl
-/
theorem stalkFunctor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ.stalk x :=
  rfl

/--
Definition of `germ` / `germ` 的定义

English:
definition germ
  signature: (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x in U)
  body: colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

中文:
定义 germ
  签名: (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x in U)
  定义体: colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

Depends on / 依赖: OpenNhds, OpenNhds.inclusion, colimit, inclusion
-/
def germ (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x in U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

/--
Definition of `Γgerm` / `Γgerm` 的定义

English:
definition Γgerm
  signature: (F : X.Presheaf C) (x : X)
  body: F.germ ⊤ x True.intro

@[reassoc]

中文:
定义 Γgerm
  签名: (F : X.Presheaf C) (x : X)
  定义体: F.germ ⊤ x True.intro

@[reassoc]

Depends on / 依赖: F.germ, True.intro
-/
def Γgerm (F : X.Presheaf C) (x : X) : F.obj (op ⊤) ⟶ stalk F x :=
  F.germ ⊤ x True.intro

@[reassoc]
/--
theorem `germ_res` / 定理 `germ_res`

English:
theorem germ_res
  given: (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x in U)
  proof: let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.le hx⟩ := i
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

中文:
定理 germ_res
  条件: (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x in U)
  证明: let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.le hx⟩ := i
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

Depends on / 依赖: OpenNhds, OpenNhds.inclusion, colimit, colimit.w, i.le, inclusion
-/
theorem germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x in U) :
    F.map i.op ≫ F.germ U x hx = F.germ V x (i.le hx) :=
  let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.le hx⟩ := i
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

/-- A variant of `germ_res` with `op V ⟶ op U`
so that the LHS is more general and simp fires more easier. -/
@[reassoc (attr := simp)]
/--
theorem `germ_res'` / 定理 `germ_res'`

English:
theorem germ_res'
  given: (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x in U)
  proof: let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.unop.le hx⟩ := i.unop
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

@[reassoc]

中文:
定理 germ_res'
  条件: (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x in U)
  证明: let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.unop.le hx⟩ := i.unop
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

@[reassoc]

Depends on / 依赖: OpenNhds, OpenNhds.inclusion, colimit, colimit.w, i.unop, i.unop.le, inclusion
-/
theorem germ_res' (F : X.Presheaf C) {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x in U) :
    F.map i ≫ F.germ U x hx = F.germ V x (i.unop.le hx) :=
  let i' : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.unop.le hx⟩ := i.unop
  colimit.w ((OpenNhds.inclusion x).op ⋙ F) i'.op

@[reassoc]
/--
lemma `map_germ_eq_Γgerm` / 引理 `map_germ_eq_Γgerm`

English:
lemma map_germ_eq_Γgerm
  given: (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x in U)
  proof: germ_res F i x hx

中文:
引理 map_germ_eq_Γgerm
  条件: (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x in U)
  证明: germ_res F i x hx

Depends on / 依赖: germ_res
-/
lemma map_germ_eq_Γgerm (F : X.Presheaf C) {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x in U) :
    F.map i.op ≫ F.germ U x hx = F.Γgerm x :=
  germ_res F i x hx

variable {FC : C -> C -> Type*} {CC : C -> Type*} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]

@[simp]
/--
theorem `germ_res_apply` / 定理 `germ_res_apply`

English:
theorem germ_res_apply
  statement: (F : X.Presheaf C)
  proof: by
  rw [← ConcreteCategory.comp_apply]; rw [germ_res]

中文:
定理 germ_res_apply
  结论: (F : X.Presheaf C)
  证明: by
  rw [← ConcreteCategory.comp_apply]; rw [germ_res]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, comp_apply, germ_res
-/
theorem germ_res_apply (F : X.Presheaf C)
    {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) :
    F.germ U x hx (F.map i.op s) = F.germ V x (i.le hx) s := by
  rw [← ConcreteCategory.comp_apply]; rw [germ_res]

/--
theorem `germ_res_apply'` / 定理 `germ_res_apply'`

English:
theorem germ_res_apply'
  statement: (F : X.Presheaf C)
  proof: by
  rw [← ConcreteCategory.comp_apply]; rw [germ_res']

中文:
定理 germ_res_apply'
  结论: (F : X.Presheaf C)
  证明: by
  rw [← ConcreteCategory.comp_apply]; rw [germ_res']

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, comp_apply, germ_res
-/
theorem germ_res_apply' (F : X.Presheaf C)
    {U V : Opens X} (i : op V ⟶ op U) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) :
    F.germ U x hx (F.map i s) = F.germ V x (i.unop.le hx) s := by
  rw [← ConcreteCategory.comp_apply]; rw [germ_res']

/--
lemma `Γgerm_res_apply` / 引理 `Γgerm_res_apply`

English:
lemma Γgerm_res_apply
  statement: (F : X.Presheaf C)
  proof: F.germ_res_apply i x hx s

中文:
引理 Γgerm_res_apply
  结论: (F : X.Presheaf C)
  证明: F.germ_res_apply i x hx s

Depends on / 依赖: F.germ_res_apply, germ_res_apply
-/
lemma Γgerm_res_apply (F : X.Presheaf C)
    {U : Opens X} {i : U ⟶ ⊤} (x : X) (hx : x in U) [ConcreteCategory C FC] (s) :
    F.germ U x hx (F.map i.op s) = F.Γgerm x s :=
  F.germ_res_apply i x hx s

/-- A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
@[ext]
/--
theorem `stalk_hom_ext` / 定理 `stalk_hom_ext`

English:
theorem stalk_hom_ext
  statement: (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
  proof: colimit.hom_ext fun U => by
    induction U with | op U => obtain ⟨U, hxU⟩ := U; exact ih U hxU

中文:
定理 stalk_hom_ext
  结论: (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
  证明: colimit.hom_ext fun U => by
    induction U with | op U => obtain ⟨U, hxU⟩ := U; exact ih U hxU

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext
-/
theorem stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
    (ih : forall (U : Opens X) (hxU : x in U), F.germ U x hxU ≫ f₁ = F.germ U x hxU ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext fun U => by
    induction U with | op U => obtain ⟨U, hxU⟩ := U; exact ih U hxU

set_option backward.isDefEq.respectTransparency false in -- This is needed in Geometry/RingedSpace/Stalks.lean
@[reassoc (attr := simp)]
/--
theorem `stalkFunctor_map_germ` / 定理 `stalkFunctor_map_germ`

English:
theorem stalkFunctor_map_germ
  given: {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G)
  proof: colimit.ι_map (whiskerLeft (OpenNhds.inclusion x).op f) (op ⟨U, hx⟩)

中文:
定理 stalkFunctor_map_germ
  条件: {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G)
  证明: colimit.ι_map (whiskerLeft (OpenNhds.inclusion x).op f) (op ⟨U, hx⟩)

Depends on / 依赖: OpenNhds, OpenNhds.inclusion, colimit, inclusion, whiskerLeft
-/
theorem stalkFunctor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) :
    F.germ U x hx ≫ (stalkFunctor C x).map f = f.app (op U) ≫ G.germ U x hx :=
  colimit.ι_map (whiskerLeft (OpenNhds.inclusion x).op f) (op ⟨U, hx⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `stalkFunctor_map_germ_apply` / 定理 `stalkFunctor_map_germ_apply`

English:
theorem stalkFunctor_map_germ_apply
  statement: [ConcreteCategory C FC]
  proof: by
  rw [← ConcreteCategory.comp_apply]; rw [← stalkFunctor_map_germ]; rw [ConcreteCategory.comp_apply]
  rfl

中文:
定理 stalkFunctor_map_germ_apply
  结论: [ConcreteCategory C FC]
  证明: by
  rw [← ConcreteCategory.comp_apply]; rw [← stalkFunctor_map_germ]; rw [ConcreteCategory.comp_apply]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, comp_apply, stalkFunctor_map_germ
-/
theorem stalkFunctor_map_germ_apply [ConcreteCategory C FC]
    {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) (s) :
    (stalkFunctor C x).map f (F.germ U x hx s) = G.germ U x hx (f.app (op U) s) := by
  rw [← ConcreteCategory.comp_apply]; rw [← stalkFunctor_map_germ]; rw [ConcreteCategory.comp_apply]
  rfl

-- a variant of `stalkFunctor_map_germ_apply` that makes simpNF happy.
@[simp]
/--
theorem `stalkFunctor_map_germ_apply'` / 定理 `stalkFunctor_map_germ_apply'`

English:
theorem stalkFunctor_map_germ_apply'
  statement: [ConcreteCategory C FC]
  proof: stalkFunctor_map_germ_apply U x hx f s

中文:
定理 stalkFunctor_map_germ_apply'
  结论: [ConcreteCategory C FC]
  证明: stalkFunctor_map_germ_apply U x hx f s

Depends on / 依赖: F.stalk, G.stalk
-/
theorem stalkFunctor_map_germ_apply' [ConcreteCategory C FC]
    {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U) (f : F ⟶ G) (s) :
    DFunLike.coe (F := ToHom (F.stalk x) (G.stalk x))
        (ConcreteCategory.hom ((stalkFunctor C x).map f)) (F.germ U x hx s) =
      G.germ U x hx (f.app (op U) s) :=
  stalkFunctor_map_germ_apply U x hx f s

variable (C)

/--
Definition of `stalkPushforward` / `stalkPushforward` 的定义

English:
definition stalkPushforward
  signature: (f : X ⟶ Y) (F : X.Presheaf C) (x : X)
  body: by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  refine ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)

中文:
定义 stalkPushforward
  签名: (f : X ⟶ Y) (F : X.Presheaf C) (x : X)
  定义体: by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  refine ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)
-/
def stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x := by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  refine ?_ ≫ colimit.pre _ (OpenNhds.map f x).op
  exact colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `stalkPushforward_germ` / 定理 `stalkPushforward_germ`

English:
theorem stalkPushforward_germ
  statement: (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
  proof: by
  simp [germ, stalkPushforward]

中文:
定理 stalkPushforward_germ
  结论: (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
  证明: by
  simp [germ, stalkPushforward]

Depends on / 依赖: stalkPushforward
-/
theorem stalkPushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y)
    (x : X) (hx : f x in U) :
      (f _* F).germ U (f x) hx ≫ F.stalkPushforward C f x = F.germ ((Opens.map f).obj U) x hx := by
  simp [germ, stalkPushforward]

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.
-- def stalkPushforward'' (f : X ⟶ Y) (ℱ : X.Presheaf C) (x : X) :
-- (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((Functor.associator _ _ _).inv ≫
-- whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) ℱ) ≫
-- colimit.pre ((OpenNhds.inclusion x).op ⋙ ℱ) (OpenNhds.map f x).op
-- def stalkPushforward''' (f : X ⟶ Y) (ℱ : X.Presheaf C) (x : X) :
-- (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whiskerRight (NatTrans.op (OpenNhds.inclusionMapIso f x).inv) ℱ) :
-- colim.obj ((OpenNhds.inclusion (f x) ⋙ Opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((OpenNhds.inclusion x).op ⋙ ℱ) (OpenNhds.map f x).op

namespace stalkPushforward

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `id` / 定理 `id`

English:
theorem id
  given: (ℱ : X.Presheaf C) (x : X)
  proof: by
  ext
  simp only [stalkPushforward, germ, colim_map, ι_colimMap_assoc, whiskerRight_app]
  erw [CategoryTheory.Functor.map_id]
  simp [stalkFunctor]

中文:
定理 id
  条件: (ℱ : X.Presheaf C) (x : X)
  证明: by
  ext
  simp only [stalkPushforward, germ, colim_map, ι_colimMap_assoc, whiskerRight_app]
  erw [CategoryTheory.Functor.map_id]
  simp [stalkFunctor]

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, colim_map, map_id, stalkFunctor, stalkPushforward, whiskerRight_app
-/
theorem id (ℱ : X.Presheaf C) (x : X) :
    ℱ.stalkPushforward C (𝟙 X) x = (stalkFunctor C x).map (Pushforward.id ℱ).hom := by
  ext
  simp only [stalkPushforward, germ, colim_map, ι_colimMap_assoc, whiskerRight_app]
  erw [CategoryTheory.Functor.map_id]
  simp [stalkFunctor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by
  ext
  simp [germ, stalkPushforward]

中文:
定理 comp
  条件: (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by
  ext
  simp [germ, stalkPushforward]

Depends on / 依赖: stalkPushforward
-/
theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ℱ.stalkPushforward C (f ≫ g) x =
      (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x := by
  ext
  simp [germ, stalkPushforward]

/--
theorem `stalkPushforward_iso_of_isInducing` / 定理 `stalkPushforward_iso_of_isInducing`

English:
theorem stalkPushforward_iso_of_isInducing
  statement: {f : X ⟶ Y} (hf : IsInducing f)
  proof: by
  have := Functor.initial_of_adjunction (hf.adjunctionNhds x)
  convert!
    (Functor.Final.colimitIso (OpenNhds.map f x).op ((OpenNhds.inclusion x).op ⋙ F)).isIso_hom
  refine stalk_hom_ext _ fun U hU => (stalkPushforward_germ _ f F _ x hU).trans ?_
  symm
  exact colimit.ι_pre ((OpenNhds.inclus

中文:
定理 stalkPushforward_iso_of_isInducing
  结论: {f : X ⟶ Y} (hf : IsInducing f)
  证明: by
  have := Functor.initial_of_adjunction (hf.adjunctionNhds x)
  convert!
    (Functor.Final.colimitIso (OpenNhds.map f x).op ((OpenNhds.inclusion x).op ⋙ F)).isIso_hom
  refine stalk_hom_ext _ fun U hU => (stalkPushforward_germ _ f F _ x hU).trans ?_
  symm
  exact colimit.ι_pre ((OpenNhds.inclus

Depends on / 依赖: Functor, Functor.Final.colimitIso, Functor.initial_of_adjunction, OpenNhds, OpenNhds.inclusion, OpenNhds.map, adjunctionNhds, colimit, colimitIso, convert, hf.adjunctionNhds, inclusion, initial_of_adjunction, isIso_hom, stalkPushforward_germ, stalk_hom_ext
-/
theorem stalkPushforward_iso_of_isInducing {f : X ⟶ Y} (hf : IsInducing f)
    (F : X.Presheaf C) (x : X) : IsIso (F.stalkPushforward _ f x) := by
  have := Functor.initial_of_adjunction (hf.adjunctionNhds x)
  convert!
    (Functor.Final.colimitIso (OpenNhds.map f x).op ((OpenNhds.inclusion x).op ⋙ F)).isIso_hom
  refine stalk_hom_ext _ fun U hU => (stalkPushforward_germ _ f F _ x hU).trans ?_
  symm
  exact colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ F) (OpenNhds.map f x).op _

end stalkPushforward

section stalkPullback

/--
Definition of `stalkPullbackHom` / `stalkPullbackHom` 的定义

English:
definition stalkPullbackHom
  signature: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X)
  body: (stalkFunctor _ (f x)).map ((pullbackPushforwardAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x

中文:
定义 stalkPullbackHom
  签名: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X)
  定义体: (stalkFunctor _ (f x)).map ((pullbackPushforwardAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x

Depends on / 依赖: pullbackPushforwardAdjunction, stalkFunctor, stalkPushforward, unit.app
-/
def stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ⟶ ((pullback C f).obj F).stalk x :=
  (stalkFunctor _ (f x)).map ((pullbackPushforwardAdjunction C f).unit.app F) ≫
    stalkPushforward _ _ _ x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `germ_stalkPullbackHom` / 引理 `germ_stalkPullbackHom`

English:
lemma germ_stalkPullbackHom
  proof: by
  simp [stalkPullbackHom, germ, stalkFunctor, stalkPushforward]

中文:
引理 germ_stalkPullbackHom
  证明: by
  simp [stalkPullbackHom, germ, stalkFunctor, stalkPushforward]

Depends on / 依赖: stalkFunctor, stalkPullbackHom, stalkPushforward
-/
lemma germ_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (U : Opens Y) (hU : f x in U) :
    F.germ U (f x) hU ≫ stalkPullbackHom C f F x =
      ((pullbackPushforwardAdjunction C f).unit.app F).app _ ≫
        ((pullback C f).obj F).germ ((Opens.map f).obj U) x hU := by
  simp [stalkPullbackHom, germ, stalkFunctor, stalkPushforward]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `germToPullbackStalk` / `germToPullbackStalk` 的定义

English:
definition germToPullbackStalk
  signature: (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U)
  body: ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).desc
    { pt := F.stalk ((f : X -> Y) (x : X))
      ι :=
        { app := fun V => F.germ _ (f x) (V.hom.unop.le hx)
          naturality := fun _ _ i => by simp } }

中文:
定义 germToPullbackStalk
  签名: (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U)
  定义体: ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).desc
    { pt := F.stalk ((f : X -> Y) (x : X))
      ι :=
        { app := fun V => F.germ _ (f x) (V.hom.unop.le hx)
          naturality := fun _ _ i => by simp } }

Depends on / 依赖: F.germ, F.stalk, Opens.map, V.hom.unop.le, isPointwiseLeftKanExtensionLeftKanExtensionUnit, naturality, op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
-/
def germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U) :
    ((pullback C f).obj F).obj (op U) ⟶ F.stalk (f x) :=
  ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).desc
    { pt := F.stalk ((f : X -> Y) (x : X))
      ι :=
        { app := fun V => F.germ _ (f x) (V.hom.unop.le hx)
          naturality := fun _ _ i => by simp } }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {C} in
@[ext]
/--
lemma `pullback_obj_obj_ext` / 引理 `pullback_obj_obj_ext`

English:
lemma pullback_obj_obj_ext
  statement: {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ)
  proof: by
  apply ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F _).hom_ext
  rintro ⟨⟨V⟩, ⟨⟩, ⟨b⟩⟩
  simpa [pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    using! h V (leOfHom b)

中文:
引理 pullback_obj_obj_ext
  结论: {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ)
  证明: by
  apply ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F _).hom_ext
  rintro ⟨⟨V⟩, ⟨⟩, ⟨b⟩⟩
  simpa [pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    using! h V (leOfHom b)

Depends on / 依赖: Functor, Functor.lanAdjunction_unit, Opens.map, hom_ext, isPointwiseLeftKanExtensionLeftKanExtensionUnit, lanAdjunction_unit, leOfHom, op.isPointwiseLeftKanExtensionLeftKanExtensionUnit, pullbackPushforwardAdjunction
-/
lemma pullback_obj_obj_ext {Z : C} {f : X ⟶ Y} {F : Y.Presheaf C} (U : (Opens X)ᵒᵖ)
    {φ ψ : ((pullback C f).obj F).obj U ⟶ Z}
    (h : forall (V : Opens Y) (hV : U.unop <= (Opens.map f).obj V),
      ((pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ φ =
      ((pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
        ((pullback C f).obj F).map (homOfLE hV).op ≫ ψ) : φ = ψ := by
  apply ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F _).hom_ext
  rintro ⟨⟨V⟩, ⟨⟩, ⟨b⟩⟩
  simpa [pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    using! h V (leOfHom b)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk` / 引理 `pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk`

English:
lemma pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
  proof: by
  simpa [pullbackPushforwardAdjunction] using!
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).fac _
      (CostructuredArrow.mk (homOfLE hV).op)

中文:
引理 pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
  证明: by
  simpa [pullbackPushforwardAdjunction] using!
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).fac _
      (CostructuredArrow.mk (homOfLE hV).op)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, Opens.map, homOfLE, isPointwiseLeftKanExtensionLeftKanExtensionUnit, op.isPointwiseLeftKanExtensionLeftKanExtensionUnit, pullbackPushforwardAdjunction
-/
lemma pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U) (V : Opens Y)
    (hV : U <= (Opens.map f).obj V) :
    ((pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
      ((pullback C f).obj F).map (homOfLE hV).op ≫ germToPullbackStalk C f F U x hx =
        F.germ _ (f x) (hV hx) := by
  simpa [pullbackPushforwardAdjunction] using!
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op U)).fac _
      (CostructuredArrow.mk (homOfLE hV).op)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `germToPullbackStalk_stalkPullbackHom` / 引理 `germToPullbackStalk_stalkPullbackHom`

English:
lemma germToPullbackStalk_stalkPullbackHom
  proof: by
  ext V hV
  dsimp
  simp only [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc,
    germ_stalkPullbackHom, germ_res]

中文:
引理 germToPullbackStalk_stalkPullbackHom
  证明: by
  ext V hV
  dsimp
  simp only [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc,
    germ_stalkPullbackHom, germ_res]

Depends on / 依赖: germ_res, germ_stalkPullbackHom, pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc
-/
lemma germToPullbackStalk_stalkPullbackHom
    (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : X) (hx : x in U) :
    germToPullbackStalk C f F U x hx ≫ stalkPullbackHom C f F x =
      ((pullback C f).obj F).germ _ x hx := by
  ext V hV
  dsimp
  simp only [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk_assoc,
    germ_stalkPullbackHom, germ_res]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk` / 引理 `pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk`

English:
lemma pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
  proof: by
  simpa using pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
    C f F ((Opens.map f).obj V.unop) x hx V.unop (by rfl)

中文:
引理 pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
  证明: by
  simpa using pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
    C f F ((Opens.map f).obj V.unop) x hx V.unop (by rfl)

Depends on / 依赖: Opens.map, V.unop, pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
-/
lemma pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk
    (f : X ⟶ Y) (F : Y.Presheaf C) (V : (Opens Y)ᵒᵖ) (x : X) (hx : f x in V.unop) :
    ((pullbackPushforwardAdjunction C f).unit.app F).app V ≫ germToPullbackStalk C f F _ x hx =
      F.germ _ (f x) hx := by
  simpa using pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
    C f F ((Opens.map f).obj V.unop) x hx V.unop (by rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `stalkPullbackInv` / `stalkPullbackInv` 的定义

English:
definition stalkPullbackInv
  signature: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X)
  body: colimit.desc ((OpenNhds.inclusion x).op ⋙ (Presheaf.pullback C f).obj F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 x (unop U).2
          naturality := fun U V i => by
            dsimp
            ext W hW
            dsimp [OpenNhds.inclusi

中文:
定义 stalkPullbackInv
  签名: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X)
  定义体: colimit.desc ((OpenNhds.inclusion x).op ⋙ (Presheaf.pullback C f).obj F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 x (unop U).2
          naturality := fun U V i => by
            dsimp
            ext W hW
            dsimp [OpenNhds.inclusi

Depends on / 依赖: Category, Category.comp_id, F.germToPullbackStalk, F.stalk, Functor, Functor.map_comp_assoc, OpenNhds, OpenNhds.inclusion, Presheaf, Presheaf.pullback, colimit, colimit.desc, comp_id, germToPullbackStalk, inclusion, map_comp_assoc, naturality, pullback, pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk
-/
def stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    ((pullback C f).obj F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (Presheaf.pullback C f).obj F)
    { pt := F.stalk (f x)
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 x (unop U).2
          naturality := fun U V i => by
            dsimp
            ext W hW
            dsimp [OpenNhds.inclusion]
            rw [Category.comp_id]; rw [← Functor.map_comp_assoc]; rw [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk]
            erw [pullbackPushforwardAdjunction_unit_pullback_map_germToPullbackStalk] } }

@[reassoc (attr := simp)]
/--
lemma `germ_stalkPullbackInv` / 引理 `germ_stalkPullbackInv`

English:
lemma germ_stalkPullbackInv
  given: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X) (hV : x in V)
  proof: by
  apply colimit.ι_desc

中文:
引理 germ_stalkPullbackInv
  条件: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X) (hV : x in V)
  证明: by
  apply colimit.ι_desc

Depends on / 依赖: colimit
-/
lemma germ_stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) (V : Opens X) (hV : x in V) :
    ((pullback C f).obj F).germ _ x hV ≫ stalkPullbackInv C f F x =
    F.germToPullbackStalk _ f V x hV := by
  apply colimit.ι_desc

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `stalkPullbackIso` / `stalkPullbackIso` 的定义

English:
definition stalkPullbackIso
  signature: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X)
  body: stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    ext U hU
    dsimp
    rw [germ_stalkPullbackHom_assoc]; rw [germ_stalkPullbackInv]; rw [Category.comp_id]; rw [pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk]
  inv_hom_id := by
    ext V hV
    dsimp


中文:
定义 stalkPullbackIso
  签名: (f : X ⟶ Y) (F : Y.Presheaf C) (x : X)
  定义体: stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    ext U hU
    dsimp
    rw [germ_stalkPullbackHom_assoc]; rw [germ_stalkPullbackInv]; rw [Category.comp_id]; rw [pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk]
  inv_hom_id := by
    ext V hV
    dsimp


Depends on / 依赖: stalkPullbackHom
-/
def stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) :
    F.stalk (f x) ≅ ((pullback C f).obj F).stalk x where
  hom := stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id := by
    ext U hU
    dsimp
    rw [germ_stalkPullbackHom_assoc]; rw [germ_stalkPullbackInv]; rw [Category.comp_id]; rw [pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk]
  inv_hom_id := by
    ext V hV
    dsimp
    rw [germ_stalkPullbackInv_assoc]; rw [Category.comp_id]; rw [germToPullbackStalk_stalkPullbackHom]

end stalkPullback

section stalkSpecializes

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `stalkSpecializes` / `stalkSpecializes` 的定义

English:
definition stalkSpecializes
  signature: (F : X.Presheaf C) {x y : X} (h : x ⤳ y)
  body: by
  refine colimit.desc _ ⟨_, fun U => ?_, ?_⟩
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 :)⟩)
  · intro U V i
    dsimp
    rw [Category.comp_id]
    let U' : OpenNhds x := ⟨_, (specializes_iff_fora

中文:
定义 stalkSpecializes
  签名: (F : X.Presheaf C) {x y : X} (h : x ⤳ y)
  定义体: by
  refine colimit.desc _ ⟨_, fun U => ?_, ?_⟩
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 :)⟩)
  · intro U V i
    dsimp
    rw [Category.comp_id]
    let U' : OpenNhds x := ⟨_, (specializes_iff_fora

Depends on / 依赖: Category, Category.comp_id, OpenNhds, OpenNhds.inclusion, colimit, colimit.desc, colimit.w, comp_id, i.unop, inclusion, specializes_iff_forall_open, specializes_iff_forall_open.mp
-/
noncomputable def stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    F.stalk y ⟶ F.stalk x := by
  refine colimit.desc _ ⟨_, fun U => ?_, ?_⟩
  · exact
      colimit.ι ((OpenNhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 :)⟩)
  · intro U V i
    dsimp
    rw [Category.comp_id]
    let U' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 :)⟩
    let V' : OpenNhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 :)⟩
    exact colimit.w ((OpenNhds.inclusion x).op ⋙ F) (show V' ⟶ U' from i.unop).op

@[reassoc (attr := simp), elementwise nosimp]
/--
theorem `germ_stalkSpecializes` / 定理 `germ_stalkSpecializes`

English:
theorem germ_stalkSpecializes
  statement: (F : X.Presheaf C)
  proof: colimit.ι_desc _ _

@[simp]

中文:
定理 germ_stalkSpecializes
  结论: (F : X.Presheaf C)
  证明: colimit.ι_desc _ _

@[simp]

Depends on / 依赖: colimit
-/
theorem germ_stalkSpecializes (F : X.Presheaf C)
    {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) :
    F.germ U y hy ≫ F.stalkSpecializes h = F.germ U x (h.mem_open U.isOpen hy) :=
  colimit.ι_desc _ _

@[simp]
/--
theorem `stalkSpecializes_refl` / 定理 `stalkSpecializes_refl`

English:
theorem stalkSpecializes_refl
  given: (F : X.Presheaf C) (x : X)
  proof: by
  ext
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 stalkSpecializes_refl
  条件: (F : X.Presheaf C) (x : X)
  证明: by
  ext
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
-/
theorem stalkSpecializes_refl (F : X.Presheaf C) (x : X) :
    F.stalkSpecializes (specializes_refl x) = 𝟙 _ := by
  ext
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `stalkSpecializes_comp` / 定理 `stalkSpecializes_comp`

English:
theorem stalkSpecializes_comp
  given: (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z)
  proof: by
  ext
  simp

中文:
定理 stalkSpecializes_comp
  条件: (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z)
  证明: by
  ext
  simp
-/
theorem stalkSpecializes_comp (F : X.Presheaf C) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z) :
    F.stalkSpecializes h' ≫ F.stalkSpecializes h = F.stalkSpecializes (h.trans h') := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `stalkSpecializes_stalkFunctor_map` / 定理 `stalkSpecializes_stalkFunctor_map`

English:
theorem stalkSpecializes_stalkFunctor_map
  given: {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y)
  proof: by
  ext
  simp

中文:
定理 stalkSpecializes_stalkFunctor_map
  条件: {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y)
  证明: by
  ext
  simp
-/
theorem stalkSpecializes_stalkFunctor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (stalkFunctor C x).map f =
      (stalkFunctor C y).map f ≫ G.stalkSpecializes h := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `stalkSpecializes_stalkPushforward` / 定理 `stalkSpecializes_stalkPushforward`

English:
theorem stalkSpecializes_stalkPushforward
  given: (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y)
  proof: by
  ext
  simp

中文:
定理 stalkSpecializes_stalkPushforward
  条件: (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y)
  证明: by
  ext
  simp
-/
theorem stalkSpecializes_stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    (f _* F).stalkSpecializes (f.hom.map_specializes h) ≫ F.stalkPushforward _ f x =
      F.stalkPushforward _ f y ≫ F.stalkSpecializes h := by
  ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalks are isomorphic on inseparable points -/
@[simps]
/--
Definition of `stalkCongr` / `stalkCongr` 的定义

English:
definition stalkCongr
  signature: (F : X.Presheaf C) {x y : X}
  body: ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩

中文:
定义 stalkCongr
  签名: (F : X.Presheaf C) {x y : X}
  定义体: ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩

Depends on / 依赖: F.stalkSpecializes, e.ge, e.le, stalkSpecializes
-/
def stalkCongr (F : X.Presheaf C) {x y : X}
    (e : Inseparable x y) : F.stalk x ≅ F.stalk y :=
  ⟨F.stalkSpecializes e.ge, F.stalkSpecializes e.le, by simp, by simp⟩

end stalkSpecializes

section Concrete

variable {C} {CC : C -> Type v} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [instCC : ConcreteCategory.{v} C FC]

/--
theorem `germ_ext` / 定理 `germ_ext`

English:
theorem germ_ext
  statement: (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x in U} {hxV : x in V}
  proof: by
  rw [← F.germ_res iWU x hxW]; rw [← F.germ_res iWV x hxW]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]; rw [ih]

中文:
定理 germ_ext
  结论: (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x in U} {hxV : x in V}
  证明: by
  rw [← F.germ_res iWU x hxW]; rw [← F.germ_res iWV x hxW]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]; rw [ih]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.germ_res, comp_apply, germ_res
-/
theorem germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x in U} {hxV : x in V}
    (W : Opens X) (hxW : x in W) (iWU : W ⟶ U) (iWV : W ⟶ V)
    {sU : ToType (F.obj (op U))} {sV : ToType (F.obj (op V))}
    (ih : F.map iWU.op sU = F.map iWV.op sV) :
      F.germ _ x hxU sU = F.germ _ x hxV sV := by
  rw [← F.germ_res iWU x hxW]; rw [← F.germ_res iWV x hxW]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]; rw [ih]

variable [PreservesFilteredColimits (forget C)]

/--
theorem `exists_germ_eq` / 定理 `exists_germ_eq`

English:
theorem exists_germ_eq
  given: (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x))
  proof: by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{v, v} _ (isColimitOfPreserves (forget C) (colimit.isColimit _)) t
  revert s e
  induction U with | op U => ?_
  obtain ⟨V, m⟩ := U
  intro s e
  exact ⟨V, m, s, e⟩

@[deprecated (since := "2026-05-16")] alias germ_exist := exists_germ_eq

中文:
定理 exists_germ_eq
  条件: (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x))
  证明: by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{v, v} _ (isColimitOfPreserves (forget C) (colimit.isColimit _)) t
  revert s e
  induction U with | op U => ?_
  obtain ⟨V, m⟩ := U
  intro s e
  exact ⟨V, m, s, e⟩

@[deprecated (since := "2026-05-16")] alias germ_exist := exists_germ_eq

Depends on / 依赖: Types.jointly_surjective, colimit, colimit.isColimit, forget, isColimit, isColimitOfPreserves, jointly_surjective, revert
-/
theorem exists_germ_eq (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x)) :
    exists (U : Opens X) (m : x in U) (s : ToType (F.obj (op U))), F.germ _ x m s = t := by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{v, v} _ (isColimitOfPreserves (forget C) (colimit.isColimit _)) t
  revert s e
  induction U with | op U => ?_
  obtain ⟨V, m⟩ := U
  intro s e
  exact ⟨V, m, s, e⟩

@[deprecated (since := "2026-05-16")] alias germ_exist := exists_germ_eq

/--
theorem `exists_le_germ_eq` / 定理 `exists_le_germ_eq`

English:
theorem exists_le_germ_eq
  statement: (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x))
  proof: by
  rcases F.exists_germ_eq t with ⟨U, hxU, s, rfl⟩
  refine ⟨U ⊓ V, inf_le_right, by simp [*], F.map (homOfLE inf_le_left).op s, ?_⟩
  exact germ_res_apply ..

中文:
定理 exists_le_germ_eq
  结论: (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x))
  证明: by
  rcases F.exists_germ_eq t with ⟨U, hxU, s, rfl⟩
  refine ⟨U ⊓ V, inf_le_right, by simp [*], F.map (homOfLE inf_le_left).op s, ?_⟩
  exact germ_res_apply ..

Depends on / 依赖: F.exists_germ_eq, F.map, exists_germ_eq, germ_res_apply, homOfLE, inf_le_left, inf_le_right
-/
theorem exists_le_germ_eq (F : X.Presheaf C) {x : X} (t : ToType (stalk.{v, u} F x))
    {V : Opens X} (hV : x in V) :
    exists U <= V, exists (m : x in U) (s : ToType (F.obj (op U))), F.germ _ x m s = t := by
  rcases F.exists_germ_eq t with ⟨U, hxU, s, rfl⟩
  refine ⟨U ⊓ V, inf_le_right, by simp [*], F.map (homOfLE inf_le_left).op s, ?_⟩
  exact germ_res_apply ..

/--
theorem `germ_eq` / 定理 `germ_eq`

English:
theorem germ_eq
  statement: (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V)
  proof: by
  obtain ⟨W, iU, iV, e⟩ := (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)).eq_iff.mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

中文:
定理 germ_eq
  结论: (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V)
  证明: by
  obtain ⟨W, iU, iV, e⟩ := (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)).eq_iff.mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

Depends on / 依赖: OpenNhds, OpenNhds.inclusion, colimit, colimit.isColimit, eq_iff, eq_iff.mp, iU.unop, iV.unop, inclusion, isColimit
-/
theorem germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V)
    (s : ToType (F.obj (op U))) (t : ToType (F.obj (op V)))
    (h : F.germ U x mU s = F.germ V x mV t) :
    exists (W : Opens X) (_m : x in W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ := (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)).eq_iff.mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `stalkFunctor_map_injective_of_app_injective` / 定理 `stalkFunctor_map_injective_of_app_injective`

English:
theorem stalkFunctor_map_injective_of_app_injective
  statement: {F G : Presheaf C X} {f : F ⟶ G}
  proof: fun s t hst => by
  rcases exists_germ_eq F s with ⟨U₁, hxU₁, s, rfl⟩
  rcases exists_germ_eq F t with ⟨U₂, hxU₂, t, rfl⟩
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← ConcreteCategory.comp_appl

中文:
定理 stalkFunctor_map_injective_of_app_injective
  结论: {F G : Presheaf C X} {f : F ⟶ G}
  证明: fun s t hst => by
  rcases exists_germ_eq F s with ⟨U₁, hxU₁, s, rfl⟩
  rcases exists_germ_eq F t with ⟨U₂, hxU₂, t, rfl⟩
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← ConcreteCategory.comp_appl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.germ, G.germ_eq, comp_apply, congr_arg, convert, exists_germ_eq, f.naturality, germ_eq, naturality, replace, stalkFunctor_map_germ_apply
-/
theorem stalkFunctor_map_injective_of_app_injective {F G : Presheaf C X} {f : F ⟶ G}
    (h : forall U : Opens X, Function.Injective (f.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor C x).map f) := fun s t hst => by
  rcases exists_germ_eq F s with ⟨U₁, hxU₁, s, rfl⟩
  rcases exists_germ_eq F t with ⟨U₂, hxU₂, t, rfl⟩
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← f.naturality]; rw [← f.naturality]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply] at heq
  replace heq := h W heq
  convert! congr_arg (F.germ _ x hxW) heq using 1
  exacts [(F.germ_res_apply iWU₁ x hxW s).symm, (F.germ_res_apply iWU₂ x hxW t).symm]

section IsBasis

variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

include hB

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_mem_germ_eq_of_isBasis` / 引理 `exists_mem_germ_eq_of_isBasis`

English:
lemma exists_mem_germ_eq_of_isBasis
  given: (F : X.Presheaf C) (x : X) (t : ToType (F.stalk x))
  proof: by
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq t
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hxU U.2
  exact ⟨V, hxV, hV, F.map (homOfLE hVU).op s, by rw [← ConcreteCategory.comp_apply, F.germ_res']⟩

中文:
引理 exists_mem_germ_eq_of_isBasis
  条件: (F : X.Presheaf C) (x : X) (t : ToType (F.stalk x))
  证明: by
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq t
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hxU U.2
  exact ⟨V, hxV, hV, F.map (homOfLE hVU).op s, by rw [← ConcreteCategory.comp_apply, F.germ_res']⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.exists_germ_eq, F.germ_res, F.map, comp_apply, exists_germ_eq, exists_subset_of_mem_open, germ_res, hB.exists_subset_of_mem_open, homOfLE
-/
lemma exists_mem_germ_eq_of_isBasis (F : X.Presheaf C) (x : X) (t : ToType (F.stalk x)) :
    exists (U : Opens X) (m : x in U) (_ : U in B) (s : ToType (F.obj (op U))), F.germ _ x m s = t := by
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq t
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hB.exists_subset_of_mem_open hxU U.2
  exact ⟨V, hxV, hV, F.map (homOfLE hVU).op s, by rw [← ConcreteCategory.comp_apply, F.germ_res']⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `germ_eq_of_isBasis` / 引理 `germ_eq_of_isBasis`

English:
lemma germ_eq_of_isBasis
  statement: (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V)
  proof: by
  obtain ⟨W, hxW, hWU, hWV, e⟩ := F.germ_eq x mU mV _ _ h
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'W⟩ := hB.exists_subset_of_mem_open hxW W.2
  refine ⟨W', hxW', hW', hW'W.trans hWU.le, hW'W.trans hWV.le, ?_⟩
  simpa only [← ConcreteCategory.comp_apply, ← F.map_comp] using!
    DFunLike.congr_arg (C

中文:
引理 germ_eq_of_isBasis
  结论: (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V)
  证明: by
  obtain ⟨W, hxW, hWU, hWV, e⟩ := F.germ_eq x mU mV _ _ h
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'W⟩ := hB.exists_subset_of_mem_open hxW W.2
  refine ⟨W', hxW', hW', hW'W.trans hWU.le, hW'W.trans hWV.le, ?_⟩
  simpa only [← ConcreteCategory.comp_apply, ← F.map_comp] using!
    DFunLike.congr_arg (C

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom, DFunLike, DFunLike.congr_arg, F.germ_eq, F.map, F.map_comp, W.trans, comp_apply, congr_arg, exists_subset_of_mem_open, germ_eq, hB.exists_subset_of_mem_open, hWU.le, hWV.le, homOfLE, map_comp
-/
lemma germ_eq_of_isBasis (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x in U) (mV : x in V)
    {s : ToType (F.obj (op U))} {t : ToType (F.obj (op V))}
    (h : F.germ U x mU s = F.germ V x mV t) :
    exists (W : Opens X) (_ : x in W) (_ : W in B) (hWU : W <= U) (hWV : W <= V),
      F.map (homOfLE hWU).op s = F.map (homOfLE hWV).op t := by
  obtain ⟨W, hxW, hWU, hWV, e⟩ := F.germ_eq x mU mV _ _ h
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'W⟩ := hB.exists_subset_of_mem_open hxW W.2
  refine ⟨W', hxW', hW', hW'W.trans hWU.le, hW'W.trans hWV.le, ?_⟩
  simpa only [← ConcreteCategory.comp_apply, ← F.map_comp] using!
    DFunLike.congr_arg (ConcreteCategory.hom (F.map (homOfLE hW'W).op)) e

/--
lemma `stalkFunctor_map_injective_of_isBasis` / 引理 `stalkFunctor_map_injective_of_isBasis`

English:
lemma stalkFunctor_map_injective_of_isBasis
  proof: by
  intro s t hst
  obtain ⟨U₁, hxU₁, hU₁, s, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x s
  obtain ⟨U₂, hxU₂, hU₂, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x t
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, hW, iWU₁, iWU₂, heq⟩ := germ_eq_of_is

中文:
引理 stalkFunctor_map_injective_of_isBasis
  证明: by
  intro s t hst
  obtain ⟨U₁, hxU₁, hU₁, s, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x s
  obtain ⟨U₂, hxU₂, hU₂, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x t
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, hW, iWU₁, iWU₂, heq⟩ := germ_eq_of_is

Depends on / 依赖: F.germ, eq_iff, exists_mem_germ_eq_of_isBasis, germ_eq_of_isBasis, germ_res_apply, naturality_apply, stalkFunctor_map_germ_apply
-/
lemma stalkFunctor_map_injective_of_isBasis
    {F G : X.Presheaf C} {α : F ⟶ G} (hα : forall U in B, Function.Injective (α.app (op U))) (x : X) :
    Function.Injective ((stalkFunctor _ x).map α) := by
  intro s t hst
  obtain ⟨U₁, hxU₁, hU₁, s, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x s
  obtain ⟨U₂, hxU₂, hU₂, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB _ x t
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, hW, iWU₁, iWU₂, heq⟩ := germ_eq_of_isBasis hB _ _ hxU₁ hxU₂ hst
  simp only [← α.naturality_apply, (hα W hW).eq_iff] at heq
  simpa [germ_res_apply'] using congr(F.germ W x hxW $heq)

end IsBasis

variable [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]

/--
theorem `section_ext` / 定理 `section_ext`

English:
theorem section_ext
  statement: (F : Sheaf C X) (U : Opens X) (s t : ToType (F.1.obj (op U)))
  proof: by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x.1 x.2)
  -- Since `F` is a sheaf, we can prove the 

中文:
定理 section_ext
  结论: (F : Sheaf C X) (U : Opens X) (s t : ToType (F.1.obj (op U)))
  证明: by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x.1 x.2)
  -- Since `F` is a sheaf, we can prove the 
-/
theorem section_ext (F : Sheaf C X) (U : Opens X) (s t : ToType (F.1.obj (op U)))
    (h : forall (x : X) (hx : x in U), F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) : s = t := by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.presheaf.germ_eq x.1 x.2 x.2 s t (h x.1 x.2)
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁
  · intro x hxU
    simp only [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  · intro x
    rw [heq]; rw [Subsingleton.elim (i₁ x) (i₂ x)]

/-
Note that the analogous statement for surjectivity is false: Surjectivity on stalks does not
imply surjectivity of the components of a sheaf morphism. However it does imply that the morphism
is an epi, but this fact is not yet formalized.
-/
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `app_injective_of_stalkFunctor_map_injective` / 定理 `app_injective_of_stalkFunctor_map_injective`

English:
theorem app_injective_of_stalkFunctor_map_injective
  statement: {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G)
  proof: fun s t hst =>
  section_ext F _ _ _ fun x hx =>
h x hx by rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]

中文:
定理 app_injective_of_stalkFunctor_map_injective
  结论: {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G)
  证明: fun s t hst =>
  section_ext F _ _ _ fun x hx =>
h x hx by rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]
-/
theorem app_injective_of_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G)
    (U : Opens X) (h : forall x in U, Function.Injective ((stalkFunctor C x).map f)) :
    Function.Injective (f.app (op U)) := fun s t hst =>
  section_ext F _ _ _ fun x hx =>
h x hx by rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]

/--
theorem `app_injective_iff_stalkFunctor_map_injective` / 定理 `app_injective_iff_stalkFunctor_map_injective`

English:
theorem app_injective_iff_stalkFunctor_map_injective
  statement: {F : Sheaf C X} {G : Presheaf C X}
  proof: ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x _ => h x,
    stalkFunctor_map_injective_of_app_injective⟩

中文:
定理 app_injective_iff_stalkFunctor_map_injective
  结论: {F : Sheaf C X} {G : Presheaf C X}
  证明: ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x _ => h x,
    stalkFunctor_map_injective_of_app_injective⟩

Depends on / 依赖: app_injective_of_stalkFunctor_map_injective, stalkFunctor_map_injective_of_app_injective
-/
theorem app_injective_iff_stalkFunctor_map_injective {F : Sheaf C X} {G : Presheaf C X}
    (f : F.1 ⟶ G) :
    (forall x : X, Function.Injective ((stalkFunctor C x).map f)) ↔
      forall U : Opens X, Function.Injective (f.app (op U)) :=
  ⟨fun h U => app_injective_of_stalkFunctor_map_injective f U fun x _ => h x,
    stalkFunctor_map_injective_of_app_injective⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `stalkFunctor_preserves_mono` / 实例 `stalkFunctor_preserves_mono`

English:
instance stalkFunctor_preserves_mono
  signature: (x : X)
  body: ⟨@fun _𝓐 _𝓑 f _ =>
ConcreteCategory.mono_of_injective _
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app f.1).mp
(CategoryTheory.presheaf_mo

中文:
实例 stalkFunctor_preserves_mono
  签名: (x : X)
  定义体: ⟨@fun _𝓐 _𝓑 f _ =>
ConcreteCategory.mono_of_injective _
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app f.1).mp
(CategoryTheory.presheaf_mo

Depends on / 依赖: CategoryTheory, CategoryTheory.presheaf_mono_of_mono, ConcreteCategory, ConcreteCategory.mono_iff_injective_of_preservesPullback, ConcreteCategory.mono_of_injective, NatTrans, NatTrans.mono_iff_mono_app, app_injective_iff_stalkFunctor_map_injective, mono_iff_injective_of_preservesPullback, mono_iff_mono_app, mono_of_injective, presheaf_mono_of_mono
-/
instance stalkFunctor_preserves_mono (x : X) :
    Functor.PreservesMonomorphisms (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) :=
  ⟨@fun _𝓐 _𝓑 f _ =>
ConcreteCategory.mono_of_injective _
      (app_injective_iff_stalkFunctor_map_injective f.1).mpr
        (fun c =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.1.app (op c))).mp
            ((NatTrans.mono_iff_mono_app f.1).mp
(CategoryTheory.presheaf_mono_of_mono ..)
              op c))
        x⟩

include instCC in
/--
theorem `stalk_mono_of_mono` / 定理 `stalk_mono_of_mono`

English:
theorem stalk_mono_of_mono
  given: {F G : Sheaf C X} (f : F ⟶ G) [Mono f]
  proof: fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f

include instCC in

中文:
定理 stalk_mono_of_mono
  条件: {F G : Sheaf C X} (f : F ⟶ G) [Mono f]
  证明: fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f

include instCC in

Depends on / 依赖: Functor, Functor.map_mono, Sheaf.forget, forget, map_mono, stalkFunctor
-/
theorem stalk_mono_of_mono {F G : Sheaf C X} (f : F ⟶ G) [Mono f] :
forall x, Mono (stalkFunctor C x).map f.1 :=
  fun x => Functor.map_mono (Sheaf.forget.{v} C X ⋙ stalkFunctor C x) f

include instCC in
/--
theorem `mono_of_stalk_mono` / 定理 `mono_of_stalk_mono`

English:
theorem mono_of_stalk_mono
  given: {F G : Sheaf C X} (f : F ⟶ G) [forall x, Mono <| (stalkFunctor C x).map f.1]
  proof: (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
(ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun _x _hx =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullba

中文:
定理 mono_of_stalk_mono
  条件: {F G : Sheaf C X} (f : F ⟶ G) [对任意 x, Mono <| (stalkFunctor C x).map f.1]
  证明: (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
(ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun _x _hx =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullba

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_iff_injective_of_preservesPullback, NatTrans, NatTrans.mono_iff_mono_app, Sheaf.Hom.mono_iff_presheaf_mono, U.unop, app_injective_of_stalkFunctor_map_injective, f.hom, mono_iff_injective_of_preservesPullback, mono_iff_mono_app, mono_iff_presheaf_mono, stalkFunctor
-/
theorem mono_of_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) [forall x, Mono <| (stalkFunctor C x).map f.1] :
    Mono f :=
(Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
(ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
        app_injective_of_stalkFunctor_map_injective f.1 U.unop fun _x _hx =>
          (ConcreteCategory.mono_iff_injective_of_preservesPullback
            ((stalkFunctor C _).map f.hom)).mp <| inferInstance

include instCC in
/--
theorem `mono_iff_stalk_mono` / 定理 `mono_iff_stalk_mono`

English:
theorem mono_iff_stalk_mono
  given: {F G : Sheaf C X} (f : F ⟶ G)
  proof: ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩

中文:
定理 mono_iff_stalk_mono
  条件: {F G : Sheaf C X} (f : F ⟶ G)
  证明: ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩

Depends on / 依赖: mono_of_stalk_mono, stalk_mono_of_mono
-/
theorem mono_iff_stalk_mono {F G : Sheaf C X} (f : F ⟶ G) :
    Mono f ↔ forall x, Mono ((stalkFunctor C x).map f.1) :=
  ⟨fun _ => stalk_mono_of_mono _, fun _ => mono_of_stalk_mono _⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `app_surjective_of_injective_of_locally_surjective` / 定理 `app_surjective_of_injective_of_locally_surjective`

English:
theorem app_surjective_of_injective_of_locally_surjective
  statement: {F G : Sheaf C X} (f : F ⟶ G)
  proof: by
  conv at hsurj =>
    enter [t]
    rw [Subtype.forall' (p := (· in U))]
  intro t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- These neighborhoods clearly cover all of `U`

中文:
定理 app_surjective_of_injective_of_locally_surjective
  结论: {F G : Sheaf C X} (f : F ⟶ G)
  证明: by
  conv at hsurj =>
    enter [t]
    rw [Subtype.forall' (p := (· in U))]
  intro t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- These neighborhoods clearly cover all of `U`

Depends on / 依赖: Subtype, Subtype.forall
-/
theorem app_surjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F ⟶ G)
    (U : Opens X) (hinj : forall x in U, Function.Injective ((stalkFunctor C x).map f.1))
    (hsurj : forall (t x) (_ : x in U), exists (V : Opens X) (_ : x in V) (iVU : V ⟶ U)
    (s : ToType (F.1.obj (op V))), f.1.app (op V) s = G.1.map iVU.op t) :
    Function.Surjective (f.1.app (op U)) := by
  conv at hsurj =>
    enter [t]
    rw [Subtype.forall' (p := (· in U))]
  intro t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- These neighborhoods clearly cover all of `U`.
  have V_cover : U <= iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices IsCompatible F.obj V sf by
    -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
    · use s
      apply G.eq_of_locally_eq' V U iVU V_cover
      intro x
      rw [← ConcreteCategory.comp_apply]; rw [← f.1.naturality]; rw [ConcreteCategory.comp_apply]; rw [s_spec]; rw [heq]
  intro x y
  -- What's left to show here is that the sections `sf` are compatible, i.e. they agree on
  -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
  apply section_ext
  intro z hz
  -- Here, we need to use injectivity of the stalk maps.
  apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y <= V x) hz))
  rw [stalkFunctor_map_germ_apply]; rw [stalkFunctor_map_germ_apply]
  simp_rw [← ConcreteCategory.comp_apply, f.1.naturality, ConcreteCategory.comp_apply, heq,
    ← ConcreteCategory.comp_apply, ← G.1.map_comp]
  rfl

/--
theorem `app_surjective_of_stalkFunctor_map_bijective` / 定理 `app_surjective_of_stalkFunctor_map_bijective`

English:
theorem app_surjective_of_stalkFunctor_map_bijective
  statement: {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
  proof: by
  refine app_surjective_of_injective_of_locally_surjective f U (And.left <| h · ·) fun t x hx => ?_
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, h

中文:
定理 app_surjective_of_stalkFunctor_map_bijective
  结论: {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
  证明: by
  refine app_surjective_of_injective_of_locally_surjective f U (And.left <| h · ·) fun t x hx => ?_
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, h

Depends on / 依赖: And.left, app_surjective_of_injective_of_locally_surjective
-/
theorem app_surjective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : forall x in U, Function.Bijective ((stalkFunctor C x).map f.1)) :
    Function.Surjective (f.1.app (op U)) := by
  refine app_surjective_of_injective_of_locally_surjective f U (And.left <| h · ·) fun t x hx => ?_
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, hs₀⟩ := (h x hx).2 (G.presheaf.germ U x hx t)
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁, hxV₁, s₁, rfl⟩ := F.presheaf.exists_germ_eq s₀
  rename' hs₀ => hs₁
  rw [stalkFunctor_map_germ_apply V₁ x hxV₁ f.1 s₁] at hs₁
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x hxV₁ hx _ _ hs₁
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁
  rw [← ConcreteCategory.comp_apply]; rw [f.1.naturality]; rw [ConcreteCategory.comp_apply]; rw [heq]

/--
theorem `app_bijective_of_stalkFunctor_map_bijective` / 定理 `app_bijective_of_stalkFunctor_map_bijective`

English:
theorem app_bijective_of_stalkFunctor_map_bijective
  statement: {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
  proof: ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x hx => (h x hx).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩

include instCC in

中文:
定理 app_bijective_of_stalkFunctor_map_bijective
  结论: {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
  证明: ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x hx => (h x hx).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩

include instCC in

Depends on / 依赖: app_injective_of_stalkFunctor_map_injective, app_surjective_of_stalkFunctor_map_bijective
-/
theorem app_bijective_of_stalkFunctor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : forall x in U, Function.Bijective ((stalkFunctor C x).map f.1)) :
    Function.Bijective (f.1.app (op U)) :=
  ⟨app_injective_of_stalkFunctor_map_injective f.1 U fun x hx => (h x hx).1,
    app_surjective_of_stalkFunctor_map_bijective f U h⟩

include instCC in
/--
theorem `app_isIso_of_stalkFunctor_map_iso` / 定理 `app_isIso_of_stalkFunctor_map_iso`

English:
theorem app_isIso_of_stalkFunctor_map_iso
  statement: {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
  proof: by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijecti

中文:
定理 app_isIso_of_stalkFunctor_map_iso
  结论: {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
  证明: by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijecti
-/
theorem app_isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    [forall x : U, IsIso ((stalkFunctor C x.val).map f.1)] : IsIso (f.1.app (op U)) := by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices IsIso ((forget C).map (f.1.app (op U))) by
    exact isIso_of_reflects_iso (f.1.app (op U)) (forget C)
  rw [isIso_iff_bijective]
  apply app_bijective_of_stalkFunctor_map_bijective
  intro x hx
  apply (bijective_iff_isIso_ofHom _).mpr
  exact Functor.map_isIso (forget C) ((stalkFunctor C (⟨x, hx⟩ : U).1).map f.1)

include instCC in
-- Making this an instance would cause a loop in typeclass resolution with `Functor.map_isIso`
/--
theorem `isIso_of_stalkFunctor_map_iso` / 定理 `isIso_of_stalkFunctor_map_iso`

English:
theorem isIso_of_stalkFunctor_map_iso
  statement: {F G : Sheaf C X} (f : F ⟶ G)
  proof: by
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices IsIso ((Sheaf.forget C X).map f) by exact isIso_of_fully_faithful (Sheaf.forget C X) f
  -- We show that all componen

中文:
定理 isIso_of_stalkFunctor_map_iso
  结论: {F G : Sheaf C X} (f : F ⟶ G)
  证明: by
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices IsIso ((Sheaf.forget C X).map f) by exact isIso_of_fully_faithful (Sheaf.forget C X) f
  -- We show that all componen
-/
theorem isIso_of_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G)
    [forall x : X, IsIso ((stalkFunctor C x).map f.1)] : IsIso f := by
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices IsIso ((Sheaf.forget C X).map f) by exact isIso_of_fully_faithful (Sheaf.forget C X) f
  -- We show that all components of `f` are isomorphisms.
  suffices forall U : (Opens X)ᵒᵖ, IsIso (f.1.app U) by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ F.1 G.1 f.1 this
  intro U; induction U
  apply app_isIso_of_stalkFunctor_map_iso

include instCC in
/--
theorem `isIso_iff_stalkFunctor_map_iso` / 定理 `isIso_iff_stalkFunctor_map_iso`

English:
theorem isIso_iff_stalkFunctor_map_iso
  given: {F G : Sheaf C X} (f : F ⟶ G)
  proof: ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩

中文:
定理 isIso_iff_stalkFunctor_map_iso
  条件: {F G : Sheaf C X} (f : F ⟶ G)
  证明: ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩

Depends on / 依赖: Functor, Functor.map_isIso, Sheaf.forget, forget, isIso_of_stalkFunctor_map_iso, map_isIso, stalkFunctor
-/
theorem isIso_iff_stalkFunctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ forall x : X, IsIso ((stalkFunctor C x).map f.1) :=
  ⟨fun _ x =>
    @Functor.map_isIso _ _ _ _ _ _ (stalkFunctor C x) f.1 ((Sheaf.forget C X).map_isIso f),
   fun _ => isIso_of_stalkFunctor_map_iso f⟩

end Concrete

end TopCat.Presheaf
