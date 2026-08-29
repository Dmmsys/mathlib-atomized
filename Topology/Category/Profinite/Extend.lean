/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.CategoryTheory.Filtered.Final
/-!

# Extending cones in `Profinite`

Let `(Sᵢ)_{i : I}` be a family of finite sets indexed by a cofiltered category `I` and let `S` be
its limit in `Profinite`. Let `G` be a functor from `Profinite` to a category `C` and suppose that
`G` preserves the limit described above. Suppose further that the projection maps `S ⟶ Sᵢ` are
epimorphic for all `i`. Then `G.obj S` is isomorphic to a limit indexed by
`StructuredArrow S toProfinite` (see `Profinite.Extend.isLimitCone`).

We also provide the dual result for a functor of the form `G : Profiniteᵒᵖ ⥤ C`.

We apply this to define `Profinite.diagram'`, `Profinite.asLimitCone'`, and `Profinite.asLimit'`,
analogues to their unprimed versions in `Mathlib/Topology/Category/Profinite/AsLimit.lean`, in which
the indexing category is `StructuredArrow S toProfinite` instead of `DiscreteQuotient S`.
-/

@[expose] public section

universe u w

open CategoryTheory Limits FintypeCat Functor

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone <| F ⋙ toProfinite)

/--
lemma `exists_hom` / 引理 `exists_hom`

English:
lemma exists_hom
  given: (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X)
  proof: by
  have : DiscreteTopology (toProfinite.obj X) := ⟨rfl⟩
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.hom.hom.continuous⟩
  obtain ⟨i, g, h⟩ := exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, ⟨↾g⟩, ?_⟩
  ext x
  exact LocallyConstant.c

中文:
引理 存在_hom
  条件: (hc : 是极限 c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X)
  证明: by
  have : DiscreteTopology (toProfinite.obj X) := ⟨rfl⟩
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.hom.hom.continuous⟩
  obtain ⟨i, g, h⟩ := exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, ⟨↾g⟩, ?_⟩
  ext x
  exact LocallyConstant.c

Depends on / 依赖: DiscreteTopology, IsLocallyConstant, IsLocallyConstant.iff_continuous, LocallyConstant, LocallyConstant.congr_fun, c.pt, congr_fun, continuous, exists_locallyConstant, f.hom.hom.continuous, iff_continuous, toProfinite, toProfinite.obj
-/
lemma exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X) :
    exists (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g := by
  have : DiscreteTopology (toProfinite.obj X) := ⟨rfl⟩
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.hom.hom.continuous⟩
  obtain ⟨i, g, h⟩ := exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, ⟨↾g⟩, ?_⟩
  ext x
  exact LocallyConstant.congr_fun h x

namespace Extend

/--
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofiltered category,
we obtain a functor from the indexing category to `StructuredArrow c.pt toProfinite`.
-/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : I ⥤ StructuredArrow c.pt toProfinite where
  body: StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

中文:
定义 functor
  签名: : I ⥤ 结构化箭头 c.pt toProfinite where
  定义体: StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

-- We check that the original diagram factors through `Profinite.Extend.functor`.
example : functor c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

/--
Given a cone in `Profinite`, consisting of finite sets and indexed by a cofiltered category,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
@[simps! obj map]
/--
Definition of `functorOp` / `functorOp` 的定义

English:
definition functorOp
  signature: : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩
  body: (functor c).op ⋙ StructuredArrow.toCostructuredArrow _ _

中文:
定义 functorOp
  签名: : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩
  定义体: (functor c).op ⋙ StructuredArrow.toCostructuredArrow _ _

Depends on / 依赖: StructuredArrow, StructuredArrow.toCostructuredArrow, functor, toCostructuredArrow
-/
def functorOp : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩ :=
  (functor c).op ⋙ StructuredArrow.toCostructuredArrow _ _

-- We check that the opposite of the original diagram factors through `Profinite.Extend.functorOp`.
example : functorOp c ⋙ CostructuredArrow.proj toProfinite.op ⟨c.pt⟩ ≅ F.op := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] uliftCategory in
/--
lemma `functor_initial` / 引理 `functor_initial`

English:
lemma functor_initial
  given: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  statement: Initial (functor c)
  proof: by
  let e : I ≌ ULiftHom.{w} (ULift.{w} I) := ULiftHomULiftCategory.equiv _
  suffices (e.inverse ⋙ functor c).Initial from initial_of_equivalence_comp e.inverse (functor c)
  rw [initial_iff_of_isCofiltered (F := e.inverse ⋙ functor c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    obtain ⟨i,

中文:
引理 functor_initial
  条件: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)]
  结论: 初始 (functor c)
  证明: by
  let e : I ≌ ULiftHom.{w} (ULift.{w} I) := ULiftHomULiftCategory.equiv _
  suffices (e.inverse ⋙ functor c).Initial from initial_of_equivalence_comp e.inverse (functor c)
  rw [initial_iff_of_isCofiltered (F := e.inverse ⋙ functor c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    obtain ⟨i,

Depends on / 依赖: F.obj, Initial, StructuredArrow, StructuredArrow.homMk, ULiftHom, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, c.pt, e.inverse, exists_hom, functor, h.symm, initial_iff_of_isCofiltered, initial_of_equivalence_comp, inverse
-/
lemma functor_initial (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Initial (functor c) := by
  let e : I ≌ ULiftHom.{w} (ULift.{w} I) := ULiftHomULiftCategory.equiv _
  suffices (e.inverse ⋙ functor c).Initial from initial_of_equivalence_comp e.inverse (functor c)
  rw [initial_iff_of_isCofiltered (F := e.inverse ⋙ functor c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    obtain ⟨i, g, h⟩ := exists_hom c hc f
    exact ⟨⟨i⟩, ⟨StructuredArrow.homMk g h.symm⟩⟩
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩ ⟨i⟩ ⟨_, (s : F.obj i ⟶ X), (w : f = c.π.app i ≫ _)⟩
      ⟨_, (s' : F.obj i ⟶ X), (w' : f = c.π.app i ≫ _)⟩
    simp only [StructuredArrow.hom_eq_iff,
      StructuredArrow.comp_right]
    refine ⟨⟨i⟩, 𝟙 _, ?_⟩
    simp only [CategoryTheory.Functor.map_id]
    rw [w] at w'
exact toProfinite.map_injective Epi.left_cancellation _ _ w'

/--
lemma `functorOp_final` / 引理 `functorOp_final`

English:
lemma functorOp_final
  given: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  statement: Final (functorOp c)
  proof: by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  exact Functor.final_comp (functor c).op _

中文:
引理 functorOp_final
  条件: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)]
  结论: 终 (functorOp c)
  证明: by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  exact Functor.final_comp (functor c).op _

Depends on / 依赖: Functor, Functor.final_comp, IsEquivalence, StructuredArrow, StructuredArrow.toCostructuredArrow, c.pt, final_comp, functor, functor.IsEquivalence, functor_initial, structuredArrowOpEquivalence, toCostructuredArrow, toProfinite
-/
lemma functorOp_final (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Final (functorOp c) := by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  exact Functor.final_comp (functor c).op _

section Limit

variable {C : Type*} [Category* C] (G : Profinite ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `Profinite` and `S : Profinite`, we obtain a cone on
`(StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G)` with cone point `G.obj S`.

Whiskering this cone with `Profinite.Extend.functor c` gives `G.mapCone c` as we check in the
example below.
-/
@[simps]
/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: (S : Profinite)
  body: G.obj S
  π := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by simp [← map_comp]) }

example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

中文:
定义 cone
  签名: (S : Profinite)
  定义体: G.obj S
  π := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by simp [← map_comp]) }

example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

Depends on / 依赖: G.obj
-/
def cone (S : Profinite) :
    Cone (StructuredArrow.proj S toProfinite ⋙ toProfinite ⋙ G) where
  pt := G.obj S
  π := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by simp [← map_comp]) }

example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

/--
If `c` and `G.mapCone c` are limit cones and the projection maps in `c` are epimorphic,
then `cone G c.pt` is a limit cone.
-/
noncomputable
/--
Definition of `isLimitCone` / `isLimitCone` 的定义

English:
definition isLimitCone
  signature: (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsLimit <| G.mapCone c)
  body: (functor_initial c hc).isLimitWhiskerEquiv _ _ hc'

中文:
定义 isLimitCone
  签名: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)] (hc' : 是极限 <| G.mapCone c)
  定义体: (functor_initial c hc).isLimitWhiskerEquiv _ _ hc'

Depends on / 依赖: functor_initial, isLimitWhiskerEquiv
-/
def isLimitCone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsLimit <| G.mapCone c) :
    IsLimit (cone G c.pt) := (functor_initial c hc).isLimitWhiskerEquiv _ _ hc'

end Limit

section Colimit

variable {C : Type*} [Category* C] (G : Profiniteᵒᵖ ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `Profiniteᵒᵖ` and `S : Profinite`, we obtain a cocone on
`(CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G)` with cocone point `G.obj ⟨S⟩`.

Whiskering this cocone with `Profinite.Extend.functorOp c` gives `G.mapCocone c.op` as we check in
the example below.
-/
@[simps]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: (S : Profinite)
  body: G.obj ⟨S⟩
  ι := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp [← map_comp, this]) }

example : G.mapCocone c.op = (coco

中文:
定义 cocone
  签名: (S : Profinite)
  定义体: G.obj ⟨S⟩
  ι := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp [← map_comp, this]) }

example : G.mapCocone c.op = (coco

Depends on / 依赖: G.obj
-/
def cocone (S : Profinite) :
    Cocone (CostructuredArrow.proj toProfinite.op ⟨S⟩ ⋙ toProfinite.op ⋙ G) where
  pt := G.obj ⟨S⟩
  ι := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp [← map_comp, this]) }

example : G.mapCocone c.op = (cocone G c.pt).whisker (functorOp c) := rfl

/--
If `c` is a limit cone, `G.mapCocone c.op` is a colimit cone and the projection maps in `c`
are epimorphic, then `cocone G c.pt` is a colimit cone.
-/
noncomputable
/--
Definition of `isColimitCocone` / `isColimitCocone` 的定义

English:
definition isColimitCocone
  signature: (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op)
  body: (functorOp_final c hc).isColimitWhiskerEquiv _ _ hc'

中文:
定义 isColimitCocone
  签名: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)] (hc' : 是余极限 <| G.mapCocone c.op)
  定义体: (functorOp_final c hc).isColimitWhiskerEquiv _ _ hc'

Depends on / 依赖: functorOp_final, isColimitWhiskerEquiv
-/
def isColimitCocone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op) :
    IsColimit (cocone G c.pt) := (functorOp_final c hc).isColimitWhiskerEquiv _ _ hc'

end Colimit

end Extend

open Extend

section ProfiniteAsLimit

variable (S : Profinite.{u})

/--
Definition of `fintypeDiagram'` / `fintypeDiagram'` 的定义

English:
abbreviation fintypeDiagram'
  signature: : StructuredArrow S toProfinite ⥤ FintypeCat
  body: StructuredArrow.proj S toProfinite

中文:
缩写 fintypeDiagram'
  签名: : 结构化箭头 S toProfinite ⥤ FintypeCat
  定义体: StructuredArrow.proj S toProfinite

Depends on / 依赖: StructuredArrow, StructuredArrow.proj, toProfinite
-/
abbrev fintypeDiagram' : StructuredArrow S toProfinite ⥤ FintypeCat :=
  StructuredArrow.proj S toProfinite

/--
Definition of `diagram'` / `diagram'` 的定义

English:
abbreviation diagram'
  signature: : StructuredArrow S toProfinite ⥤ Profinite
  body: S.fintypeDiagram' ⋙ toProfinite

中文:
缩写 diagram'
  签名: : 结构化箭头 S toProfinite ⥤ Profinite
  定义体: S.fintypeDiagram' ⋙ toProfinite

Depends on / 依赖: S.fintypeDiagram, fintypeDiagram, toProfinite
-/
abbrev diagram' : StructuredArrow S toProfinite ⥤ Profinite :=
  S.fintypeDiagram' ⋙ toProfinite

/--
Definition of `asLimitCone'` / `asLimitCone'` 的定义

English:
abbreviation asLimitCone'
  signature: : Cone (S.diagram')
  body: cone (𝟭 _) S

中文:
缩写 asLimitCone'
  签名: : 锥 (S.diagram')
  定义体: cone (𝟭 _) S
-/
abbrev asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S

instance (i : DiscreteQuotient S) : Epi (S.asLimitCone.π.app i) :=
  (epi_iff_surjective _).mpr i.proj_surjective

/--
Definition of `asLimit'` / `asLimit'` 的定义

English:
definition asLimit'
  signature: : IsLimit S.asLimitCone'
  body: isLimitCone _ (𝟭 _) S.asLimit S.asLimit

中文:
定义 asLimit'
  签名: : 是极限 S.asLimitCone'
  定义体: isLimitCone _ (𝟭 _) S.asLimit S.asLimit

Depends on / 依赖: S.asLimit, asLimit, isLimitCone
-/
noncomputable def asLimit' : IsLimit S.asLimitCone' := isLimitCone _ (𝟭 _) S.asLimit S.asLimit

/--
Definition of `lim'` / `lim'` 的定义

English:
definition lim'
  signature: : LimitCone S.diagram'
  body: ⟨S.asLimitCone', S.asLimit'⟩

中文:
定义 lim'
  签名: : 极限锥 S.diagram'
  定义体: ⟨S.asLimitCone', S.asLimit'⟩

Depends on / 依赖: S.asLimit, S.asLimitCone, asLimit, asLimitCone
-/
noncomputable def lim' : LimitCone S.diagram' := ⟨S.asLimitCone', S.asLimit'⟩

end ProfiniteAsLimit

end Profinite
