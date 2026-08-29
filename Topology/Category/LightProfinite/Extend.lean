/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.LightProfinite.AsLimit
public import Mathlib.Topology.Category.Profinite.Extend

/-!

# Extending cones in `LightProfinite`

Let `(Sₙ)_{n : ℕᵒᵖ}` be a sequential inverse system of finite sets and let `S` be
its limit in `Profinite`. Let `G` be a functor from `LightProfinite` to a category `C` and suppose
that `G` preserves the limit described above. Suppose further that the projection maps `S ⟶ Sₙ` are
epimorphic for all `n`. Then `G.obj S` is isomorphic to a limit indexed by
`StructuredArrow S toLightProfinite` (see `LightProfinite.Extend.isLimitCone`).

We also provide the dual result for a functor of the form `G : LightProfiniteᵒᵖ ⥤ C`.

We apply this to define `LightProfinite.diagram'`, `LightProfinite.asLimitCone'`, and
`LightProfinite.asLimit'`, analogues to their unprimed versions in
`Mathlib/Topology/Category/LightProfinite/AsLimit.lean`, in which the
indexing category is `StructuredArrow S toLightProfinite` instead of `ℕᵒᵖ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits FintypeCat Functor

attribute [local instance] FintypeCat.discreteTopology

namespace LightProfinite

variable {F : Natᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite)

namespace Extend

/--
Given a sequential cone in `LightProfinite` consisting of finite sets,
we obtain a functor from the indexing category to `StructuredArrow c.pt toLightProfinite`.
-/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Natᵒᵖ ⥤ StructuredArrow c.pt toLightProfinite where
  body: StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

中文:
定义 functor
  签名: : 自然数ᵒᵖ ⥤ 结构化箭头 c.pt toLightProfinite where
  定义体: StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def functor : Natᵒᵖ ⥤ StructuredArrow c.pt toLightProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)

-- We check that the original diagram factors through `LightProfinite.Extend.functor`.
example : functor c ⋙ StructuredArrow.proj c.pt toLightProfinite ≅ F := Iso.refl _

/--
Given a sequential cone in `LightProfinite` consisting of finite sets,
we obtain a functor from the opposite of the indexing category to
`CostructuredArrow toProfinite.op ⟨c.pt⟩`.
-/
@[simps! obj map]
/--
Definition of `functorOp` / `functorOp` 的定义

English:
definition functorOp
  signature: : Nat ⥤ CostructuredArrow toLightProfinite.op ⟨c.pt⟩
  body: (functor c).rightOp ⋙ StructuredArrow.toCostructuredArrow _ _

中文:
定义 functorOp
  签名: : 自然数 ⥤ CostructuredArrow toLightProfinite.op ⟨c.pt⟩
  定义体: (functor c).rightOp ⋙ StructuredArrow.toCostructuredArrow _ _

Depends on / 依赖: StructuredArrow, StructuredArrow.toCostructuredArrow, functor, rightOp, toCostructuredArrow
-/
def functorOp : Nat ⥤ CostructuredArrow toLightProfinite.op ⟨c.pt⟩ :=
  (functor c).rightOp ⋙ StructuredArrow.toCostructuredArrow _ _

-- We check that the opposite of the original diagram factors through `Profinite.Extend.functorOp`.
example : functorOp c ⋙ CostructuredArrow.proj toLightProfinite.op ⟨c.pt⟩ ≅ F.rightOp := Iso.refl _

-- We check that `Profinite.Extend.functor` factors through `LightProfinite.Extend.functor`,
-- via the equivalence `StructuredArrow.post _ _ lightToProfinite`.
example : functor c ⋙ (StructuredArrow.post _ _ lightToProfinite) =
    Profinite.Extend.functor (lightToProfinite.mapCone c) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `functor_initial` / 定理 `functor_initial`

English:
theorem functor_initial
  given: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  statement: Initial (functor c)
  proof: by
  rw [initial_iff_comp_equivalence _ (StructuredArrow.post _ _ lightToProfinite)]
  have : forall i, Epi ((lightToProfinite.mapCone c).π.app i) :=
    fun i => inferInstanceAs (Epi (lightToProfinite.map (c.π.app i)))
  exact Profinite.Extend.functor_initial _ (isLimitOfPreserves lightToProfinite 

中文:
定理 functor_initial
  条件: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)]
  结论: 初始 (functor c)
  证明: by
  rw [initial_iff_comp_equivalence _ (StructuredArrow.post _ _ lightToProfinite)]
  have : forall i, Epi ((lightToProfinite.mapCone c).π.app i) :=
    fun i => inferInstanceAs (Epi (lightToProfinite.map (c.π.app i)))
  exact Profinite.Extend.functor_initial _ (isLimitOfPreserves lightToProfinite 

Depends on / 依赖: Extend, Profinite, Profinite.Extend.functor_initial, StructuredArrow, StructuredArrow.post, functor_initial, initial_iff_comp_equivalence, isLimitOfPreserves, lightToProfinite, lightToProfinite.map, lightToProfinite.mapCone, mapCone
-/
theorem functor_initial (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Initial (functor c) := by
  rw [initial_iff_comp_equivalence _ (StructuredArrow.post _ _ lightToProfinite)]
  have : forall i, Epi ((lightToProfinite.mapCone c).π.app i) :=
    fun i => inferInstanceAs (Epi (lightToProfinite.map (c.π.app i)))
  exact Profinite.Extend.functor_initial _ (isLimitOfPreserves lightToProfinite hc)

/--
theorem `functorOp_final` / 定理 `functorOp_final`

English:
theorem functorOp_final
  given: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  statement: Final (functorOp c)
  proof: by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toLightProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  have : (functor c).rightOp.Final :=
    inferInstanceAs ((opOpEquivalence Nat).inverse ⋙ (functor

中文:
定理 functorOp_final
  条件: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)]
  结论: 终 (functorOp c)
  证明: by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toLightProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  have : (functor c).rightOp.Final :=
    inferInstanceAs ((opOpEquivalence Nat).inverse ⋙ (functor

Depends on / 依赖: Functor, Functor.final_comp, IsEquivalence, StructuredArrow, StructuredArrow.toCostructuredArrow, c.pt, final_comp, functor, functor.IsEquivalence, functor_initial, inverse, opOpEquivalence, rightOp, rightOp.Final, structuredArrowOpEquivalence, toCostructuredArrow, toLightProfinite
-/
theorem functorOp_final (hc : IsLimit c) [forall i, Epi (c.π.app i)] : Final (functorOp c) := by
  have := functor_initial c hc
  have : ((StructuredArrow.toCostructuredArrow toLightProfinite c.pt)).IsEquivalence :=
    (inferInstance : (structuredArrowOpEquivalence _ _).functor.IsEquivalence)
  have : (functor c).rightOp.Final :=
    inferInstanceAs ((opOpEquivalence Nat).inverse ⋙ (functor c).op).Final
  exact Functor.final_comp (functor c).rightOp _

section Limit

variable {C : Type*} [Category* C] (G : LightProfinite ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: (S : LightProfinite)
  body: G.obj S
  π :=
    { app i := G.map i.hom
      naturality _ _ f := by simp [← Functor.map_comp] }

example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

中文:
定义 cone
  签名: (S : LightProfinite)
  定义体: G.obj S
  π :=
    { app i := G.map i.hom
      naturality _ _ f := by simp [← Functor.map_comp] }

example : G.mapCone c = (cone G c.pt).whisker (functor c) := rfl

Depends on / 依赖: G.obj
-/
def cone (S : LightProfinite) :
    Cone (StructuredArrow.proj S toLightProfinite ⋙ toLightProfinite ⋙ G) where
  pt := G.obj S
  π :=
    { app i := G.map i.hom
      naturality _ _ f := by simp [← Functor.map_comp] }

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

variable {C : Type*} [Category* C] (G : LightProfiniteᵒᵖ ⥤ C)

set_option backward.defeqAttrib.useBackward true in
/--
Given a functor `G` from `LightProfiniteᵒᵖ` and `S : LightProfinite`, we obtain a cocone on
`(CostructuredArrow.proj toLightProfinite.op ⟨S⟩ ⋙ toLightProfinite.op ⋙ G)` with cocone point
`G.obj ⟨S⟩`.

Whiskering this cocone with `LightProfinite.Extend.functorOp c` gives `G.mapCocone c.op` as we
check in the example below.
-/
@[simps]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: (S : LightProfinite)
  body: G.obj ⟨S⟩
  ι := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp only [comp_obj, CostructuredArrow.proj_obj, op_obj, const

中文:
定义 cocone
  签名: (S : LightProfinite)
  定义体: G.obj ⟨S⟩
  ι := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp only [comp_obj, CostructuredArrow.proj_obj, op_obj, const

Depends on / 依赖: G.obj
-/
def cocone (S : LightProfinite) :
    Cocone (CostructuredArrow.proj toLightProfinite.op ⟨S⟩ ⋙ toLightProfinite.op ⋙ G) where
  pt := G.obj ⟨S⟩
  ι := {
    app := fun i => G.map i.hom
    naturality := fun _ _ f => (by
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      simp only [comp_obj, CostructuredArrow.proj_obj, op_obj, const_obj_obj, Functor.comp_map,
        CostructuredArrow.proj_map, op_map, ← map_comp, this, const_obj_map, Category.comp_id]) }

example : G.mapCocone c.op = (cocone G c.pt).whisker
    ((opOpEquivalence Nat).functor ⋙ functorOp c) := rfl

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
  body: haveI := functorOp_final c hc
  (Functor.final_comp (opOpEquivalence Nat).functor (functorOp c)).isColimitWhiskerEquiv _ _ hc'

中文:
定义 isColimitCocone
  签名: (hc : 是极限 c) [对任意 i, 满态射 (c.π.app i)] (hc' : 是余极限 <| G.mapCocone c.op)
  定义体: haveI := functorOp_final c hc
  (Functor.final_comp (opOpEquivalence Nat).functor (functorOp c)).isColimitWhiskerEquiv _ _ hc'

Depends on / 依赖: Functor, Functor.final_comp, final_comp, functor, functorOp, functorOp_final, isColimitWhiskerEquiv, opOpEquivalence
-/
def isColimitCocone (hc : IsLimit c) [forall i, Epi (c.π.app i)] (hc' : IsColimit <| G.mapCocone c.op) :
    IsColimit (cocone G c.pt) :=
  haveI := functorOp_final c hc
  (Functor.final_comp (opOpEquivalence Nat).functor (functorOp c)).isColimitWhiskerEquiv _ _ hc'

end Colimit

end Extend

open Extend

section LightProfiniteAsLimit

variable (S : LightProfinite.{u})

/--
Definition of `fintypeDiagram'` / `fintypeDiagram'` 的定义

English:
abbreviation fintypeDiagram'
  signature: : StructuredArrow S toLightProfinite ⥤ FintypeCat
  body: StructuredArrow.proj S toLightProfinite

中文:
缩写 fintypeDiagram'
  签名: : 结构化箭头 S toLightProfinite ⥤ FintypeCat
  定义体: StructuredArrow.proj S toLightProfinite

Depends on / 依赖: StructuredArrow, StructuredArrow.proj, toLightProfinite
-/
abbrev fintypeDiagram' : StructuredArrow S toLightProfinite ⥤ FintypeCat :=
  StructuredArrow.proj S toLightProfinite

/--
Definition of `diagram'` / `diagram'` 的定义

English:
abbreviation diagram'
  signature: : StructuredArrow S toLightProfinite ⥤ LightProfinite
  body: S.fintypeDiagram' ⋙ toLightProfinite

中文:
缩写 diagram'
  签名: : 结构化箭头 S toLightProfinite ⥤ LightProfinite
  定义体: S.fintypeDiagram' ⋙ toLightProfinite

Depends on / 依赖: S.fintypeDiagram, fintypeDiagram, toLightProfinite
-/
abbrev diagram' : StructuredArrow S toLightProfinite ⥤ LightProfinite :=
  S.fintypeDiagram' ⋙ toLightProfinite

/--
Definition of `asLimitCone'` / `asLimitCone'` 的定义

English:
definition asLimitCone'
  signature: : Cone (S.diagram')
  body: cone (𝟭 _) S

中文:
定义 asLimitCone'
  签名: : 锥 (S.diagram')
  定义体: cone (𝟭 _) S
-/
def asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S

instance (i : Natᵒᵖ) : Epi (S.asLimitCone.π.app i) :=
  (epi_iff_surjective _).mpr (S.proj_surjective _)

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

end LightProfiniteAsLimit

end LightProfinite
