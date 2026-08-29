/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monad.Adjunction
/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`. We first
prove that `F` is fully faithful iff `H` is, and then prove results about the two special cases
where `G` is fully faithful or `F` and `H` are.

## Main results

All results are about an adjoint triple `F ⊣ G ⊣ H` where `adj₁ : F ⊣ G` and `adj₂ : G ⊣ H`. We
bundle the adjunctions in a structure `Triple F G H`.
* `fullyFaithfulEquiv`: `F` is fully faithful iff `H` is.
* `rightToLeft`: the canonical natural transformation `H ⟶ F` that exists whenever `G` is fully
  faithful. This is defined as the preimage of `adj₂.counit ≫ adj₁.unit` under whiskering with `G`,
  but formulas in terms of the units resp. counits of the adjunctions are also given.
* `whiskerRight_rightToLeft`: whiskering `rightToLeft : H ⟶ F` with `G` yields
  `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G`.
* `epi_rightToLeft_app_iff_epi_map_adj₁_unit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₁.unit.app X` under `H` is.
* `epi_rightToLeft_app_iff_epi_map_adj₂_counit_app`: `rightToLeft : H ⟶ F` is epic at `X` iff the
  image of `adj₂.counit.app X` under `F` is.
* `epi_rightToLeft_app_iff`: when `H` preserves epimorphisms, `rightToLeft : H ⟶ F` is epic at `X`
  iff `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G` is.
* `leftToRight`: the canonical natural transformation `F ⟶ H` that exists whenever `F` and `H` are
  fully faithful. This is defined in terms of the units of the adjunctions, but a formula in terms
  of the counits is also given.
* `whiskerLeft_leftToRight`: whiskering `G` with `leftToRight : F ⟶ H` yields
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H`.
* `mono_leftToRight_app_iff_mono_adj₂_unit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₂.unit` is monic at `F.obj X`.
* `mono_leftToRight_app_iff_mono_adj₁_counit_app`: `leftToRight : F ⟶ H` is monic at `X` iff
  `adj₁.counit` is monic at `H.obj X`.
* `mono_leftToRight_app_iff`: `leftToRight : F ⟶ H` is componentwise monic iff
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H` is.
-/

@[expose] public section

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]
variable (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D)

/--
Definition of `CategoryTheory.Adjunction.Triple` / `CategoryTheory.Adjunction.Triple` 的定义

English:
structure CategoryTheory.Adjunction.Triple
  parameters: where
  axioms and operations (2):
    - adj₁ : F ⊣ G
    - adj₂ : G ⊣ H

中文:
结构 范畴论.伴随.三元组
  参数: where
  公理与运算 (2 个):
    - adj₁ : F ⊣ G
    - adj₂ : G ⊣ H
-/
structure CategoryTheory.Adjunction.Triple where
  /-- Adjunction `F ⊣ G` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₁ : F ⊣ G
  /-- Adjunction `G ⊣ H` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₂ : G ⊣ H

namespace CategoryTheory.Adjunction.Triple

variable {F G H} (t : Triple F G H)

/--
lemma `isIso_unit_iff_isIso_counit` / 引理 `isIso_unit_iff_isIso_counit`

English:
lemma isIso_unit_iff_isIso_counit
  statement: IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit
  proof: by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
  

中文:
引理 isIso_unit_iff_isIso_counit
  结论: 是同构 t.adj₁.unit ↔ 是同构 t.adj₂.counit
  证明: by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
  

Depends on / 依赖: adj.ofNatIsoLeft, adj.ofNatIsoRight, adjId.leftAdjointUniq, counit, idAdj.rightAdjointUniq, isIso_counit_of_iso, isIso_unit_of_iso, leftAdjointUniq, ofNatIsoLeft, ofNatIsoRight, rightAdjointUniq, t.adj
-/
lemma isIso_unit_iff_isIso_counit : IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
    exact t.adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

/--
Definition of `fullyFaithfulEquiv` / `fullyFaithfulEquiv` 的定义

English:
definition fullyFaithfulEquiv
  signature: : F.FullyFaithful ≃ H.FullyFaithful where
  body: haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_if

中文:
定义 fullyFaithfulEquiv
  签名: : F.满忠实 ≃ H.满忠实 where
  定义体: haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_if

Depends on / 依赖: Subsingleton, Subsingleton.elim, counit, faithful, fullyFaithfulLOfIsIsoUnit, fullyFaithfulROfIsIsoCounit, h.faithful, h.full, infer_instance, invFun, isIso_unit_iff_isIso_counit, left_inv, right_inv, t.adj, t.isIso_unit_iff_isIso_counit
-/
noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The adjoint triple `H.op ⊣ G.op ⊣ F.op` dual to an adjoint triple `F ⊣ G ⊣ H`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : Triple H.op G.op F.op where
  body: t.adj₂.op
  adj₂ := t.adj₁.op

中文:
定义 op
  签名: : 三元组 H.op G.op F.op where
  定义体: t.adj₂.op
  adj₂ := t.adj₁.op
-/
protected def op : Triple H.op G.op F.op where
  adj₁ := t.adj₂.op
  adj₂ := t.adj₁.op

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

/--
Definition of `rightToLeft` / `rightToLeft` 的定义

English:
definition rightToLeft
  signature: : H ⟶ F
  body: ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimage (t.adj₂.counit ≫ t.adj₁.unit)

中文:
定义 rightToLeft
  签名: : H ⟶ F
  定义体: ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimage (t.adj₂.counit ≫ t.adj₁.unit)

Depends on / 依赖: FullyFaithful, FullyFaithful.ofFullyFaithful, counit, ofFullyFaithful, preimage, t.adj, whiskeringRight
-/
noncomputable def rightToLeft : H ⟶ F :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).preimage (t.adj₂.counit ≫ t.adj₁.unit)

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, whiskering the natural
transformation `H ⟶ F` with `G` yields the composition of the counit of the second adjunction with
the unit of the first adjunction. -/
@[simp, reassoc]
/--
lemma `whiskerRight_rightToLeft` / 引理 `whiskerRight_rightToLeft`

English:
lemma whiskerRight_rightToLeft
  statement: whiskerRight t.rightToLeft G = t.adj₂.counit ≫ t.adj₁.unit
  proof: ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).map_preimage _

中文:
引理 whiskerRight_rightToLeft
  结论: whiskerRight t.rightToLeft G = t.adj₂.counit ≫ t.adj₁.unit
  证明: ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).map_preimage _

Depends on / 依赖: FullyFaithful, FullyFaithful.ofFullyFaithful, map_preimage, ofFullyFaithful, whiskeringRight
-/
lemma whiskerRight_rightToLeft : whiskerRight t.rightToLeft G = t.adj₂.counit ≫ t.adj₁.unit :=
  ((FullyFaithful.ofFullyFaithful G).whiskeringRight _).map_preimage _

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the images of the components of
the natural transformation `H ⟶ F` under `G` are the components of the composition of counit of the
second adjunction with the unit of the first adjunction. -/
@[simp, reassoc]
/--
lemma `map_rightToLeft_app` / 引理 `map_rightToLeft_app`

English:
lemma map_rightToLeft_app
  given: (X : C)
  proof: congr_app t.whiskerRight_rightToLeft X

中文:
引理 map_rightToLeft_app
  条件: (X : C)
  证明: congr_app t.whiskerRight_rightToLeft X

Depends on / 依赖: congr_app, t.whiskerRight_rightToLeft, whiskerRight_rightToLeft
-/
lemma map_rightToLeft_app (X : C) :
    G.map (t.rightToLeft.app X) = t.adj₂.counit.app X ≫ t.adj₁.unit.app X :=
  congr_app t.whiskerRight_rightToLeft X

set_option backward.defeqAttrib.useBackward true in
/--
lemma `rightToLeft_eq_units` / 引理 `rightToLeft_eq_units`

English:
lemma rightToLeft_eq_units
  proof: by
  ext X; apply G.map_injective; simp [rightToLeft]

中文:
引理 rightToLeft_eq_units
  证明: by
  ext X; apply G.map_injective; simp [rightToLeft]

Depends on / 依赖: G.map_injective, map_injective, rightToLeft
-/
lemma rightToLeft_eq_units :
    t.rightToLeft = H.leftUnitor.inv ≫ whiskerRight t.adj₁.unit H ≫ (Functor.associator _ _ _).hom ≫
    inv (whiskerLeft F t.adj₂.unit) ≫ F.rightUnitor.hom := by
  ext X; apply G.map_injective; simp [rightToLeft]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `rightToLeft_eq_counits` / 引理 `rightToLeft_eq_counits`

English:
lemma rightToLeft_eq_counits
  proof: by
  ext X; apply G.map_injective; simp [rightToLeft]

@[reassoc (attr := simp)]

中文:
引理 rightToLeft_eq_counits
  证明: by
  ext X; apply G.map_injective; simp [rightToLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: G.map_injective, map_injective, rightToLeft
-/
lemma rightToLeft_eq_counits :
    t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerLeft H t.adj₁.counit) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.counit F ≫ F.leftUnitor.hom := by
  ext X; apply G.map_injective; simp [rightToLeft]

@[reassoc (attr := simp)]
/--
lemma `adj₁_counit_app_rightToLeft_app` / 引理 `adj₁_counit_app_rightToLeft_app`

English:
lemma adj₁_counit_app_rightToLeft_app
  given: (X : C)
  proof: G.map_injective (by simp [← cancel_epi (t.adj₁.unit.app _)])

@[reassoc (attr := simp)]

中文:
引理 adj₁_counit_app_rightToLeft_app
  条件: (X : C)
  证明: G.map_injective (by simp [← cancel_epi (t.adj₁.unit.app _)])

@[reassoc (attr := simp)]

Depends on / 依赖: G.map_injective, cancel_epi, map_injective, t.adj, unit.app
-/
lemma adj₁_counit_app_rightToLeft_app (X : C) :
    t.adj₁.counit.app (H.obj X) ≫ t.rightToLeft.app X = F.map (t.adj₂.counit.app X) :=
  G.map_injective (by simp [← cancel_epi (t.adj₁.unit.app _)])

@[reassoc (attr := simp)]
/--
lemma `rightToLeft_app_adj₂_unit_app` / 引理 `rightToLeft_app_adj₂_unit_app`

English:
lemma rightToLeft_app_adj₂_unit_app
  given: (X : C)
  proof: G.map_injective (by simp [← cancel_mono (t.adj₂.counit.app _)])

中文:
引理 rightToLeft_app_adj₂_unit_app
  条件: (X : C)
  证明: G.map_injective (by simp [← cancel_mono (t.adj₂.counit.app _)])

Depends on / 依赖: G.map_injective, cancel_mono, counit, counit.app, map_injective, t.adj
-/
lemma rightToLeft_app_adj₂_unit_app (X : C) :
    t.rightToLeft.app X ≫ t.adj₂.unit.app (F.obj X) = H.map (t.adj₁.unit.app X) :=
  G.map_injective (by simp [← cancel_mono (t.adj₂.counit.app _)])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`F.op ⟶ H.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is dual to the natural
transformation `H ⟶ F`. -/
@[simp]
/--
lemma `op_rightToLeft` / 引理 `op_rightToLeft`

English:
lemma op_rightToLeft
  statement: t.op.rightToLeft = NatTrans.op t.rightToLeft
  proof: by
  ext
  rw [rightToLeft_eq_units]; rw [rightToLeft_eq_counits]
  simp

中文:
引理 op_rightToLeft
  结论: t.op.rightToLeft = 自然变换.op t.rightToLeft
  证明: by
  ext
  rw [rightToLeft_eq_units]; rw [rightToLeft_eq_counits]
  simp

Depends on / 依赖: rightToLeft_eq_counits, rightToLeft_eq_units
-/
lemma op_rightToLeft : t.op.rightToLeft = NatTrans.op t.rightToLeft := by
  ext
  rw [rightToLeft_eq_units]; rw [rightToLeft_eq_counits]
  simp

/--
lemma `epi_rightToLeft_app_iff_epi_map_adj₁_unit_app` / 引理 `epi_rightToLeft_app_iff_epi_map_adj₁_unit_app`

English:
lemma epi_rightToLeft_app_iff_epi_map_adj₁_unit_app
  given: {X : C}
  proof: by
  rw [← epi_comp_iff_of_isIso _ (t.adj₂.unit.app (F.obj X))]; rw [rightToLeft_app_adj₂_unit_app]

中文:
引理 epi_rightToLeft_app_iff_epi_map_adj₁_unit_app
  条件: {X : C}
  证明: by
  rw [← epi_comp_iff_of_isIso _ (t.adj₂.unit.app (F.obj X))]; rw [rightToLeft_app_adj₂_unit_app]

Depends on / 依赖: F.obj, epi_comp_iff_of_isIso, t.adj, unit.app
-/
lemma epi_rightToLeft_app_iff_epi_map_adj₁_unit_app {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (H.map (t.adj₁.unit.app X)) := by
  rw [← epi_comp_iff_of_isIso _ (t.adj₂.unit.app (F.obj X))]; rw [rightToLeft_app_adj₂_unit_app]

/--
lemma `epi_rightToLeft_app_iff_epi_map_adj₂_counit_app` / 引理 `epi_rightToLeft_app_iff_epi_map_adj₂_counit_app`

English:
lemma epi_rightToLeft_app_iff_epi_map_adj₂_counit_app
  given: {X : C}
  proof: by
  rw [← epi_comp_iff_of_epi (t.adj₁.counit.app (H.obj X))]; rw [adj₁_counit_app_rightToLeft_app]

中文:
引理 epi_rightToLeft_app_iff_epi_map_adj₂_counit_app
  条件: {X : C}
  证明: by
  rw [← epi_comp_iff_of_epi (t.adj₁.counit.app (H.obj X))]; rw [adj₁_counit_app_rightToLeft_app]

Depends on / 依赖: H.obj, counit, counit.app, epi_comp_iff_of_epi, t.adj
-/
lemma epi_rightToLeft_app_iff_epi_map_adj₂_counit_app {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (F.map (t.adj₂.counit.app X)) := by
  rw [← epi_comp_iff_of_epi (t.adj₁.counit.app (H.obj X))]; rw [adj₁_counit_app_rightToLeft_app]

/--
lemma `epi_rightToLeft_app_iff` / 引理 `epi_rightToLeft_app_iff`

English:
lemma epi_rightToLeft_app_iff
  given: [H.PreservesEpimorphisms] {X : C}
  proof: by
  have _ := t.adj₂.isLeftAdjoint
  refine ⟨fun h => by rw [← map_rightToLeft_app]; exact G.map_epi _, fun h => ?_⟩
  rw [epi_rightToLeft_app_iff_epi_map_adj₁_unit_app]
  simpa using epi_comp (t.adj₂.unit.app (H.obj X)) (H.map (t.adj₂.counit.app X ≫ t.adj₁.unit.app X))

中文:
引理 epi_rightToLeft_app_iff
  条件: [H.保持Epimorphisms] {X : C}
  证明: by
  have _ := t.adj₂.isLeftAdjoint
  refine ⟨fun h => by rw [← map_rightToLeft_app]; exact G.map_epi _, fun h => ?_⟩
  rw [epi_rightToLeft_app_iff_epi_map_adj₁_unit_app]
  simpa using epi_comp (t.adj₂.unit.app (H.obj X)) (H.map (t.adj₂.counit.app X ≫ t.adj₁.unit.app X))

Depends on / 依赖: G.map_epi, H.map, H.obj, counit, counit.app, epi_comp, isLeftAdjoint, map_epi, map_rightToLeft_app, t.adj, unit.app
-/
lemma epi_rightToLeft_app_iff [H.PreservesEpimorphisms] {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) := by
  have _ := t.adj₂.isLeftAdjoint
  refine ⟨fun h => by rw [← map_rightToLeft_app]; exact G.map_epi _, fun h => ?_⟩
  rw [epi_rightToLeft_app_iff_epi_map_adj₁_unit_app]
  simpa using epi_comp (t.adj₂.unit.app (H.obj X)) (H.map (t.adj₂.counit.app X ≫ t.adj₁.unit.app X))

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful] [H.Full] [H.Faithful]

/--
Definition of `leftToRight` / `leftToRight` 的定义

English:
definition leftToRight
  signature: : F ⟶ H
  body: F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight t.adj₁.unit H) ≫ H.leftUnitor.hom

中文:
定义 leftToRight
  签名: : F ⟶ H
  定义体: F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight t.adj₁.unit H) ≫ H.leftUnitor.hom

Depends on / 依赖: F.rightUnitor.inv, Functor, Functor.associator, H.leftUnitor.hom, associator, leftUnitor, rightUnitor, t.adj, whiskerLeft, whiskerRight
-/
noncomputable def leftToRight : F ⟶ H :=
  F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight t.adj₁.unit H) ≫ H.leftUnitor.hom

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
/--
lemma `leftToRight_app` / 引理 `leftToRight_app`

English:
lemma leftToRight_app
  given: {X : C}
  proof: by
  simp [leftToRight]

中文:
引理 leftToRight_app
  条件: {X : C}
  证明: by
  simp [leftToRight]

Depends on / 依赖: leftToRight
-/
lemma leftToRight_app {X : C} :
    t.leftToRight.app X = t.adj₂.unit.app (F.obj X) ≫ inv (H.map (t.adj₁.unit.app X)) := by
  simp [leftToRight]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `leftToRight_eq_counits` / 引理 `leftToRight_eq_counits`

English:
lemma leftToRight_eq_counits
  proof: by
  ext X; dsimp [leftToRight]; simp only [Category.id_comp, Category.comp_id, NatIso.isIso_inv_app]
  rw [IsIso.comp_inv_eq]; rw [Category.assoc]; rw [IsIso.eq_inv_comp]
  refine Eq.trans ?_ (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X)
  rw [whiskerRight_app _ H]; rw [(asIso (t

中文:
引理 leftToRight_eq_counits
  证明: by
  ext X; dsimp [leftToRight]; simp only [Category.id_comp, Category.comp_id, NatIso.isIso_inv_app]
  rw [IsIso.comp_inv_eq]; rw [Category.assoc]; rw [IsIso.eq_inv_comp]
  refine Eq.trans ?_ (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X)
  rw [whiskerRight_app _ H]; rw [(asIso (t

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Eq.trans, F.obj, G.obj, IsIso.comp_inv_eq, IsIso.eq_inv_comp, NatIso, NatIso.isIso_inv_app, comp_hom_eq_id, comp_id, comp_inv_eq, counit, counit.app, counit_naturality, eq_comp_inv, eq_inv_comp, id_comp
-/
lemma leftToRight_eq_counits :
    t.leftToRight = F.leftUnitor.inv ≫ inv (whiskerRight t.adj₂.counit F) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft H t.adj₁.counit ≫ H.rightUnitor.hom := by
  ext X; dsimp [leftToRight]; simp only [Category.id_comp, Category.comp_id, NatIso.isIso_inv_app]
  rw [IsIso.comp_inv_eq]; rw [Category.assoc]; rw [IsIso.eq_inv_comp]
  refine Eq.trans ?_ (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X)
  rw [whiskerRight_app _ H]; rw [(asIso (t.adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (t.adj₂.counit_naturality (t.adj₁.unit.app X))]; rw [← (asIso _).comp_hom_eq_id.1 t.adj₂.left_triangle_components (F.obj X)]
  simp

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `F ⟶ H` at `G` are precisely the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions. -/
@[simp, reassoc]
/--
lemma `leftToRight_app_obj` / 引理 `leftToRight_app_obj`

English:
lemma leftToRight_app_obj
  given: {X : D}
  proof: by
  refine (((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_).symm
  rw [homEquiv_symm_apply]; rw [map_comp]; rw [Category.assoc]; rw [left_triangle_components]; rw [homEquiv_apply]; rw [leftToRight_app]; rw [← H.map_inv]
  congr
  simpa using IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triang

中文:
引理 leftToRight_app_obj
  条件: {X : D}
  证明: by
  refine (((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_).symm
  rw [homEquiv_symm_apply]; rw [map_comp]; rw [Category.assoc]; rw [left_triangle_components]; rw [homEquiv_apply]; rw [leftToRight_app]; rw [← H.map_inv]
  congr
  simpa using IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triang

Depends on / 依赖: Category, Category.assoc, H.map_inv, IsIso.eq_inv_of_hom_inv_id, apply_symm_apply, eq_inv_of_hom_inv_id, homEquiv, homEquiv_apply, homEquiv_symm_apply, leftToRight_app, left_triangle_components, map_comp, map_inv, right_triangle_components, symm.trans, t.adj
-/
lemma leftToRight_app_obj {X : D} :
    dsimp% t.leftToRight.app (G.obj X) = t.adj₁.counit.app X ≫ t.adj₂.unit.app X := by
  refine (((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_).symm
  rw [homEquiv_symm_apply]; rw [map_comp]; rw [Category.assoc]; rw [left_triangle_components]; rw [homEquiv_apply]; rw [leftToRight_app]; rw [← H.map_inv]
  congr
  simpa using IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triangle_components _)

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, whiskering `G` with the
natural transformation `F ⟶ H` yields the composition of the counit of the first adjunction with
the unit of the second adjunction. -/
@[simp, reassoc]
/--
lemma `whiskerLeft_leftToRight` / 引理 `whiskerLeft_leftToRight`

English:
lemma whiskerLeft_leftToRight
  statement: whiskerLeft G t.leftToRight = t.adj₁.counit ≫ t.adj₂.unit
  proof: by
  ext X; exact t.leftToRight_app_obj

中文:
引理 whiskerLeft_leftToRight
  结论: whiskerLeft G t.leftToRight = t.adj₁.counit ≫ t.adj₂.unit
  证明: by
  ext X; exact t.leftToRight_app_obj

Depends on / 依赖: leftToRight_app_obj, t.leftToRight_app_obj
-/
lemma whiskerLeft_leftToRight : whiskerLeft G t.leftToRight = t.adj₁.counit ≫ t.adj₂.unit := by
  ext X; exact t.leftToRight_app_obj

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
/--
lemma `map_adj₂_counit_app_leftToRight_app` / 引理 `map_adj₂_counit_app_leftToRight_app`

English:
lemma map_adj₂_counit_app_leftToRight_app
  given: (X : C)
  proof: by
  simp

中文:
引理 map_adj₂_counit_app_leftToRight_app
  条件: (X : C)
  证明: by
  simp
-/
lemma map_adj₂_counit_app_leftToRight_app (X : C) :
    F.map (t.adj₂.counit.app X) ≫ t.leftToRight.app X = t.adj₁.counit.app (H.obj X) := by
  simp

set_option backward.defeqAttrib.useBackward true in
omit [H.Full] [H.Faithful] in
@[reassoc (attr := simp)]
/--
lemma `leftToRight_app_map_adj₁_unit_app` / 引理 `leftToRight_app_map_adj₁_unit_app`

English:
lemma leftToRight_app_map_adj₁_unit_app
  given: (X : C)
  proof: by
  simp [leftToRight_app]

中文:
引理 leftToRight_app_map_adj₁_unit_app
  条件: (X : C)
  证明: by
  simp [leftToRight_app]

Depends on / 依赖: leftToRight_app
-/
lemma leftToRight_app_map_adj₁_unit_app (X : C) :
    t.leftToRight.app X ≫ H.map (t.adj₁.unit.app X) = t.adj₂.unit.app (F.obj X) := by
  simp [leftToRight_app]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `H.op ⟶ F.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op` is
dual to the natural transformation `F ⟶ H`. -/
@[simp]
/--
lemma `leftToRight_op` / 引理 `leftToRight_op`

English:
lemma leftToRight_op
  statement: t.op.leftToRight = NatTrans.op t.leftToRight
  proof: by
  ext
  rw [leftToRight]; rw [leftToRight_eq_counits]
  simp

omit [H.Full] [H.Faithful] in

中文:
引理 leftToRight_op
  结论: t.op.leftToRight = 自然变换.op t.leftToRight
  证明: by
  ext
  rw [leftToRight]; rw [leftToRight_eq_counits]
  simp

omit [H.Full] [H.Faithful] in

Depends on / 依赖: leftToRight, leftToRight_eq_counits
-/
lemma leftToRight_op : t.op.leftToRight = NatTrans.op t.leftToRight := by
  ext
  rw [leftToRight]; rw [leftToRight_eq_counits]
  simp

omit [H.Full] [H.Faithful] in
/--
lemma `mono_leftToRight_app_iff_mono_adj₂_unit_app` / 引理 `mono_leftToRight_app_iff_mono_adj₂_unit_app`

English:
lemma mono_leftToRight_app_iff_mono_adj₂_unit_app
  given: {X : C}
  proof: by
  rw [← leftToRight_app_map_adj₁_unit_app]; rw [mono_comp_iff_of_mono]

中文:
引理 mono_leftToRight_app_iff_mono_adj₂_unit_app
  条件: {X : C}
  证明: by
  rw [← leftToRight_app_map_adj₁_unit_app]; rw [mono_comp_iff_of_mono]

Depends on / 依赖: mono_comp_iff_of_mono
-/
lemma mono_leftToRight_app_iff_mono_adj₂_unit_app {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₂.unit.app (F.obj X)) := by
  rw [← leftToRight_app_map_adj₁_unit_app]; rw [mono_comp_iff_of_mono]

/--
lemma `mono_leftToRight_app_iff_mono_adj₁_counit_app` / 引理 `mono_leftToRight_app_iff_mono_adj₁_counit_app`

English:
lemma mono_leftToRight_app_iff_mono_adj₁_counit_app
  given: {X : C}
  proof: by
  rw [← map_adj₂_counit_app_leftToRight_app]; rw [mono_comp_iff_of_isIso]

omit [H.Full] [H.Faithful] in

中文:
引理 mono_leftToRight_app_iff_mono_adj₁_counit_app
  条件: {X : C}
  证明: by
  rw [← map_adj₂_counit_app_leftToRight_app]; rw [mono_comp_iff_of_isIso]

omit [H.Full] [H.Faithful] in

Depends on / 依赖: mono_comp_iff_of_isIso
-/
lemma mono_leftToRight_app_iff_mono_adj₁_counit_app {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₁.counit.app (H.obj X)) := by
  rw [← map_adj₂_counit_app_leftToRight_app]; rw [mono_comp_iff_of_isIso]

omit [H.Full] [H.Faithful] in
/--
lemma `mono_leftToRight_app_iff` / 引理 `mono_leftToRight_app_iff`

English:
lemma mono_leftToRight_app_iff
  proof: by
  refine ⟨fun h X => by rw [← leftToRight_app_obj]; exact h _, fun h X => ?_⟩
  rw [mono_leftToRight_app_iff_mono_adj₂_unit_app]
  simpa using h (F.obj X)

中文:
引理 mono_leftToRight_app_iff
  证明: by
  refine ⟨fun h X => by rw [← leftToRight_app_obj]; exact h _, fun h X => ?_⟩
  rw [mono_leftToRight_app_iff_mono_adj₂_unit_app]
  simpa using h (F.obj X)

Depends on / 依赖: F.obj, leftToRight_app_obj
-/
lemma mono_leftToRight_app_iff :
    dsimp% (forall X, Mono (t.leftToRight.app X)) ↔
      forall X, Mono (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) := by
  refine ⟨fun h X => by rw [← leftToRight_app_obj]; exact h _, fun h X => ?_⟩
  rw [mono_leftToRight_app_iff_mono_adj₂_unit_app]
  simpa using h (F.obj X)

end OuterFullyFaithful

end CategoryTheory.Adjunction.Triple
