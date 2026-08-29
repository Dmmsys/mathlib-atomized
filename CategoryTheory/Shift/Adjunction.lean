/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Tactic.CategoryTheory.CancelIso

/-!
# Adjoints commute with shifts

Given categories `C` and `D` that have shifts by an additive group `A`, functors `F : C ⥤ D`
and `G : C ⥤ D`, an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this file constructs
a `CommShift` structure on `G`. We also do the construction in the other direction: given a
`CommShift` structure on `G`, we construct a `CommShift` structure on `G`; we could do this
using opposite categories, but the construction is simple enough that it is not really worth it.
As an easy application, if `E : C ≌ D` is an equivalence and `E.functor` has a `CommShift`
structure, we get a `CommShift` structure on `E.inverse`.

We now explain the construction of a `CommShift` structure on `G` given a `CommShift` structure
on `F`; the other direction is similar. The `CommShift` structure on `G` must be compatible with
the one on `F` in the following sense (cf. `Adjunction.CommShift`):
for every `a` in `A`, the natural transformation `adj.unit : 𝟭 C ⟶ G ⋙ F` commutes with
the isomorphism `shiftFunctor C A ⋙ G ⋙ F ≅ G ⋙ F ⋙ shiftFunctor C A` induces by
`F.commShiftIso a` and `G.commShiftIso a`. We actually require a similar condition for
`adj.counit`, but it follows from the one for `adj.unit`.

In order to simplify the construction of the `CommShift` structure on `G`, we first introduce
the compatibility condition on `adj.unit` for a fixed `a` in `A` and for isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`. We then prove that:
- If `e₁` and `e₂` satisfy this condition, then `e₁` uniquely determines `e₂` and vice versa.
- If `a = 0`, the isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G`
  satisfy the condition.
- The condition is stable by addition on `A`, if we use `Functor.CommShift.isoAdd` to deduce
  commutation isomorphism for `a + b` from such isomorphism from `a` and `b`.
- Given commutation isomorphisms for `F`, our candidate commutation isomorphisms for `G`,
  constructed in `Adjunction.RightAdjointCommShift.iso`, satisfy the compatibility condition.

Once we have established all this, the compatibility of the commutation isomorphism for
`F` expressed in `CommShift.zero` and `CommShift.add` immediately implies the similar
statements for the commutation isomorphisms for `G`.

-/

@[expose] public section

namespace CategoryTheory

open Category

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]

namespace CommShift

variable {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (f₁ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (f₂ : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)

/--
Definition of `CompatibilityUnit` / `CompatibilityUnit` 的定义

English:
abbreviation CompatibilityUnit
  body: forall (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

中文:
缩写 CompatibilityUnit
  定义体: forall (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

Depends on / 依赖: G.map, adj.unit.app, hom.app
-/
abbrev CompatibilityUnit :=
  forall (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

/--
Definition of `CompatibilityCounit` / `CompatibilityCounit` 的定义

English:
abbreviation CompatibilityCounit
  body: forall (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

中文:
缩写 CompatibilityCounit
  定义体: forall (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

Depends on / 依赖: F.map, adj.counit.app, counit, hom.app
-/
abbrev CompatibilityCounit :=
  forall (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityCounit_of_compatibilityUnit` / 引理 `compatibilityCounit_of_compatibilityUnit`

English:
lemma compatibilityCounit_of_compatibilityUnit
  given: (h : CompatibilityUnit adj e₁ e₂)
  proof: by
  intro Y
  have eq := h (G.obj Y)
  simp only [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _)),
    assoc, Iso.hom_inv_id_app_assoc, comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id] at eq
  apply (adj.homEquiv _ _).injective
  dsimp
  rw [adj.homEquiv_un

中文:
引理 compatibilityCounit_of_compatibilityUnit
  条件: (h : CompatibilityUnit adj e₁ e₂)
  证明: by
  intro Y
  have eq := h (G.obj Y)
  simp only [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _)),
    assoc, Iso.hom_inv_id_app_assoc, comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id] at eq
  apply (adj.homEquiv _ _).injective
  dsimp
  rw [adj.homEquiv_un

Depends on / 依赖: Functor, Functor.comp_obj, Functor.map_comp, Functor.map_id, G.map, G.map_comp, G.obj, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc, adj.homEquiv, adj.homEquiv_unit, adj.unit_naturality_assoc, cancel_mono, comp_id, comp_obj, homEquiv, homEquiv_unit, hom_inv_id_app, hom_inv_id_app_assoc
-/
lemma compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂) :
    CompatibilityCounit adj e₁ e₂ := by
  intro Y
  have eq := h (G.obj Y)
  simp only [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _)),
    assoc, Iso.hom_inv_id_app_assoc, comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id] at eq
  apply (adj.homEquiv _ _).injective
  dsimp
  rw [adj.homEquiv_unit]; rw [adj.homEquiv_unit]; rw [G.map_comp]; rw [adj.unit_naturality_assoc]; rw [← eq]
  simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  erw [← e₂.inv.naturality]
  dsimp
  simp only [right_triangle_components, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
    Iso.hom_inv_id_app, Functor.comp_obj]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityUnit_right` / 引理 `compatibilityUnit_right`

English:
lemma compatibilityUnit_right
  given: (h : CompatibilityUnit adj e₁ e₂) (Y : D)
  proof: by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _)]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc]; rw [← this]; rw [assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Func

中文:
引理 compatibilityUnit_right
  条件: (h : CompatibilityUnit adj e₁ e₂) (Y : D)
  证明: by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _)]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc]; rw [← this]; rw [assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Func

Depends on / 依赖: Functor, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_id, G.obj, Iso.hom_inv_id_app, Iso.inv_hom_id_app, cancel_mono, comp_id, comp_map, comp_obj, hom.app, hom_inv_id_app, id_obj, inv.app, inv.naturality, inv_hom_id_app, map_comp, map_id
-/
lemma compatibilityUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _)]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc]; rw [← this]; rw [assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityCounit_left` / 引理 `compatibilityCounit_left`

English:
lemma compatibilityCounit_left
  given: (h : CompatibilityCounit adj e₁ e₂) (X : C)
  proof: by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _))]; rw [← assoc]; rw [← F.map_comp]; rw [Iso.inv_hom_id_app]; rw [F.map_id]; rw [id_comp] at this
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [this]; rw [dsimp% e₁.hom.naturality_assoc]; rw [← Functor.map_comp]; rw [left_trian

中文:
引理 compatibilityCounit_left
  条件: (h : CompatibilityCounit adj e₁ e₂) (X : C)
  证明: by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _))]; rw [← assoc]; rw [← F.map_comp]; rw [Iso.inv_hom_id_app]; rw [F.map_id]; rw [id_comp] at this
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [this]; rw [dsimp% e₁.hom.naturality_assoc]; rw [← Functor.map_comp]; rw [left_trian

Depends on / 依赖: F.map, F.map_comp, F.map_id, F.obj, Functor, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app, cancel_epi, comp_id, comp_obj, hom.naturality_assoc, id_comp, id_obj, inv.app, inv_hom_id_app, left_triangle_components, map_comp
-/
lemma compatibilityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _))]; rw [← assoc]; rw [← F.map_comp]; rw [Iso.inv_hom_id_app]; rw [F.map_id]; rw [id_comp] at this
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [this]; rw [dsimp% e₁.hom.naturality_assoc]; rw [← Functor.map_comp]; rw [left_triangle_components]
  simp only [Functor.map_id, comp_id]

/--
lemma `compatibilityUnit_unique_right` / 引理 `compatibilityUnit_unique_right`

English:
lemma compatibilityUnit_unique_right
  statement: (h : CompatibilityUnit adj e₁ e₂)
  proof: by
  rw [← Iso.symm_eq_iff]
  ext
  rw [Iso.symm_hom]; rw [Iso.symm_hom]; rw [compatibilityUnit_right adj e₁ e₂ h]; rw [compatibilityUnit_right adj e₁ e₂' h']

中文:
引理 compatibilityUnit_unique_right
  结论: (h : CompatibilityUnit adj e₁ e₂)
  证明: by
  rw [← Iso.symm_eq_iff]
  ext
  rw [Iso.symm_hom]; rw [Iso.symm_hom]; rw [compatibilityUnit_right adj e₁ e₂ h]; rw [compatibilityUnit_right adj e₁ e₂' h']

Depends on / 依赖: Iso.symm_eq_iff, Iso.symm_hom, compatibilityUnit_right, symm_eq_iff, symm_hom
-/
lemma compatibilityUnit_unique_right (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁ e₂') : e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext
  rw [Iso.symm_hom]; rw [Iso.symm_hom]; rw [compatibilityUnit_right adj e₁ e₂ h]; rw [compatibilityUnit_right adj e₁ e₂' h']

/--
lemma `compatibilityUnit_unique_left` / 引理 `compatibilityUnit_unique_left`

English:
lemma compatibilityUnit_unique_left
  statement: (h : CompatibilityUnit adj e₁ e₂)
  proof: by
  ext
  rw [compatibilityCounit_left adj e₁ e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h)]; rw [compatibilityCounit_left adj e₁' e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h')]

中文:
引理 compatibilityUnit_unique_left
  结论: (h : CompatibilityUnit adj e₁ e₂)
  证明: by
  ext
  rw [compatibilityCounit_left adj e₁ e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h)]; rw [compatibilityCounit_left adj e₁' e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h')]

Depends on / 依赖: compatibilityCounit_left, compatibilityCounit_of_compatibilityUnit
-/
lemma compatibilityUnit_unique_left (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁' e₂) : e₁ = e₁' := by
  ext
  rw [compatibilityCounit_left adj e₁ e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h)]; rw [compatibilityCounit_left adj e₁' e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h')]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityUnit_isoZero` / 引理 `compatibilityUnit_isoZero`

English:
lemma compatibilityUnit_isoZero
  statement: CompatibilityUnit adj (Functor.CommShift.isoZero F A)
  proof: by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc,
    ← cancel_mono ((shiftFunctorZero C A).hom.app _), ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, id_comp, NatTrans.natural

中文:
引理 compatibilityUnit_isoZero
  结论: CompatibilityUnit adj (Functor.CommShift.isoZero F A)
  证明: by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc,
    ← cancel_mono ((shiftFunctorZero C A).hom.app _), ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, id_comp, NatTrans.natural

Depends on / 依赖: CommShift, Functor, Functor.CommShift.isoZero_hom_app, Functor.comp_obj, Functor.id_map, Functor.id_obj, Functor.map_comp, Functor.map_id, G.map_comp_assoc, Iso.inv_hom_id_app, NatTrans, NatTrans.naturality, cancel_mono, comp_id, comp_obj, hom.app, id_comp, id_map, id_obj, inv_hom_id_app
-/
lemma compatibilityUnit_isoZero : CompatibilityUnit adj (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc,
    ← cancel_mono ((shiftFunctorZero C A).hom.app _), ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, id_comp, NatTrans.naturality, Functor.id_map, assoc, comp_id]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityUnit_isoAdd` / 引理 `compatibilityUnit_isoAdd`

English:
lemma compatibilityUnit_isoAdd
  statement: (h : CompatibilityUnit adj e₁ e₂)
  proof: by
  intro X
  have := h' (X⟦a⟧)
  simp only [← cancel_mono (f₂.inv.app _), assoc, Iso.hom_inv_id_app,
    Functor.id_obj, Functor.comp_obj, comp_id] at this
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc]
  slice_r

中文:
引理 compatibilityUnit_isoAdd
  结论: (h : CompatibilityUnit adj e₁ e₂)
  证明: by
  intro X
  have := h' (X⟦a⟧)
  simp only [← cancel_mono (f₂.inv.app _), assoc, Iso.hom_inv_id_app,
    Functor.id_obj, Functor.comp_obj, comp_id] at this
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc]
  slice_r

Depends on / 依赖: CommShift, Functor, Functor.CommShift.isoAdd_hom_app, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Functor.map_id, G.map_comp, Iso.hom_inv_id_app, Iso.inv_hom_id_app, cancel_mono, comp_id, comp_obj, hom.app, hom.naturality_assoc, hom_inv_id_app, id_comp, id_obj, inv.app, inv_hom_id_app
-/
lemma compatibilityUnit_isoAdd (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj f₁ f₂) :
    CompatibilityUnit adj (Functor.CommShift.isoAdd e₁ f₁) (Functor.CommShift.isoAdd e₂ f₂) := by
  intro X
  have := h' (X⟦a⟧)
  simp only [← cancel_mono (f₂.inv.app _), assoc, Iso.hom_inv_id_app,
    Functor.id_obj, Functor.comp_obj, comp_id] at this
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  erw [f₂.hom.naturality_assoc]
  rw [← reassoc_of% this]; rw [← cancel_mono ((shiftFunctorAdd C a b).hom.app _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  dsimp
  rw [← (shiftFunctor C b).map_comp_assoc]; rw [← (shiftFunctor C b).map_comp_assoc]; rw [assoc]; rw [← h X]; rw [NatTrans.naturality]
  dsimp
  rw [comp_id]

end CommShift

variable (A) [F.CommShift A] [G.CommShift A]

/--
Definition of `CommShift` / `CommShift` 的定义

English:
class CommShift
  parameters: : Prop where
  axioms and operations (2):
    - commShift_unit : NatTrans.CommShift adj.unit A  [default: by infer_instance]
    - commShift_counit : NatTrans.CommShift adj.counit A  [default: by infer_instance]

中文:
类 CommShift
  参数: : 命题 where
  公理与运算 (2 个):
    - commShift_unit : 自然数Trans.CommShift adj.unit A  [默认: by infer_instance]
    - commShift_counit : 自然数Trans.CommShift adj.counit A  [默认: by infer_instance]

Depends on / 依赖: CommShift, NatTrans, NatTrans.CommShift, adj.counit, commShift_counit, counit, infer_instance
-/
class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

open CommShift in
attribute [instance] commShift_unit commShift_counit

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `unit_app_commShiftIso_hom_app` / 引理 `unit_app_commShiftIso_hom_app`

English:
lemma unit_app_commShiftIso_hom_app
  given: [adj.CommShift A] (a : A) (X : C)
  proof: by
  simpa using (NatTrans.shift_app_comm adj.unit a X).symm

中文:
引理 unit_app_commShiftIso_hom_app
  条件: [adj.CommShift A] (a : A) (X : C)
  证明: by
  simpa using (NatTrans.shift_app_comm adj.unit a X).symm

Depends on / 依赖: NatTrans, NatTrans.shift_app_comm, adj.unit, shift_app_comm
-/
lemma unit_app_commShiftIso_hom_app [adj.CommShift A] (a : A) (X : C) :
    adj.unit.app (X⟦a⟧) ≫ ((F ⋙ G).commShiftIso a).hom.app X = (adj.unit.app X)⟦a⟧' := by
  simpa using (NatTrans.shift_app_comm adj.unit a X).symm

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `unit_app_shift_commShiftIso_inv_app` / 引理 `unit_app_shift_commShiftIso_inv_app`

English:
lemma unit_app_shift_commShiftIso_inv_app
  given: [adj.CommShift A] (a : A) (X : C)
  proof: by
  simp [← cancel_mono (((F ⋙ G).commShiftIso _).hom.app _)]

中文:
引理 unit_app_shift_commShiftIso_inv_app
  条件: [adj.CommShift A] (a : A) (X : C)
  证明: by
  simp [← cancel_mono (((F ⋙ G).commShiftIso _).hom.app _)]

Depends on / 依赖: cancel_mono, commShiftIso, hom.app
-/
lemma unit_app_shift_commShiftIso_inv_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' ≫ ((F ⋙ G).commShiftIso a).inv.app X = adj.unit.app (X⟦a⟧) := by
  simp [← cancel_mono (((F ⋙ G).commShiftIso _).hom.app _)]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `commShiftIso_hom_app_counit_app_shift` / 引理 `commShiftIso_hom_app_counit_app_shift`

English:
lemma commShiftIso_hom_app_counit_app_shift
  given: [adj.CommShift A] (a : A) (Y : D)
  proof: by
  simpa using (NatTrans.shift_app_comm adj.counit a Y)

@[reassoc (attr := simp)]

中文:
引理 commShiftIso_hom_app_counit_app_shift
  条件: [adj.CommShift A] (a : A) (Y : D)
  证明: by
  simpa using (NatTrans.shift_app_comm adj.counit a Y)

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.shift_app_comm, adj.counit, counit, shift_app_comm
-/
lemma commShiftIso_hom_app_counit_app_shift [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).hom.app Y ≫ (adj.counit.app Y)⟦a⟧' = adj.counit.app (Y⟦a⟧) := by
  simpa using (NatTrans.shift_app_comm adj.counit a Y)

@[reassoc (attr := simp)]
/--
lemma `commShiftIso_inv_app_counit_app` / 引理 `commShiftIso_inv_app_counit_app`

English:
lemma commShiftIso_inv_app_counit_app
  given: [adj.CommShift A] (a : A) (Y : D)
  proof: by
  simp [← cancel_epi (((G ⋙ F).commShiftIso _).hom.app _)]

中文:
引理 commShiftIso_inv_app_counit_app
  条件: [adj.CommShift A] (a : A) (Y : D)
  证明: by
  simp [← cancel_epi (((G ⋙ F).commShiftIso _).hom.app _)]

Depends on / 依赖: cancel_epi, commShiftIso, hom.app
-/
lemma commShiftIso_inv_app_counit_app [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).inv.app Y ≫ adj.counit.app (Y⟦a⟧) = (adj.counit.app Y)⟦a⟧' := by
  simp [← cancel_epi (((G ⋙ F).commShiftIso _).hom.app _)]

namespace CommShift


set_option backward.defeqAttrib.useBackward true in
/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (_ : NatTrans.CommShift adj.unit A)
  proof: ⟨fun a => by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, assoc, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, comp_id]
    refine (compatibilityCounit_of_compatibilityUnit adj _ _ (fu

中文:
引理 mk'
  条件: (_ : 自然数Trans.CommShift adj.unit A)
  证明: ⟨fun a => by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, assoc, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, comp_id]
    refine (compatibilityCounit_of_compatibilityUnit adj _ _ (fu

Depends on / 依赖: Functor, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans, NatTrans.comp_app, NatTrans.shift_app_comm, adj.unit, commShiftIso_comp_hom_app, commShiftIso_id_hom_app, comp_app, comp_id, comp_obj, compatibilityCounit_of_compatibilityUnit, id_obj, shift_app_comm, whiskerLeft_app
-/
lemma mk' (_ : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
  commShift_counit := ⟨fun a => by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, assoc, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, comp_id]
    refine (compatibilityCounit_of_compatibilityUnit adj _ _ (fun X => ?_) _).symm
    simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X⟩

/--
Instance `instId` / 实例 `instId`

English:
instance instId
  signature: : (Adjunction.id (C := C)).CommShift A where
  body: inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.hom A)
  commShift_unit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.inv A)

中文:
实例 instId
  签名: : (Adjunction.id (C := C)).CommShift A where
  定义体: inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.hom A)
  commShift_unit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.inv A)

Depends on / 依赖: CommShift
-/
instance instId : (Adjunction.id (C := C)).CommShift A where
  commShift_counit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.hom A)
  commShift_unit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.inv A)

variable {E : Type*} [Category* E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
  [HasShift E A] [F'.CommShift A] [G'.CommShift A] [adj.CommShift A] [adj'.CommShift A]

/--
Instance `instComp` / 实例 `instComp`

English:
instance instComp
  signature: : (adj.comp adj').CommShift A where
  body: by
    rw [comp_counit]
    infer_instance
  commShift_unit := by
    rw [comp_unit]
    infer_instance

中文:
实例 instComp
  签名: : (adj.comp adj').CommShift A where
  定义体: by
    rw [comp_counit]
    infer_instance
  commShift_unit := by
    rw [comp_unit]
    infer_instance

Depends on / 依赖: commShift_unit, comp_counit, comp_unit, infer_instance
-/
instance instComp : (adj.comp adj').CommShift A where
  commShift_counit := by
    rw [comp_counit]
    infer_instance
  commShift_unit := by
    rw [comp_unit]
    infer_instance

end CommShift

variable {A}

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shift_unit_app` / 引理 `shift_unit_app`

English:
lemma shift_unit_app
  given: [adj.CommShift A] (a : A) (X : C)
  proof: by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X

中文:
引理 shift_unit_app
  条件: [adj.CommShift A] (a : A) (X : C)
  证明: by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X

Depends on / 依赖: Functor, Functor.commShiftIso_comp_hom_app, NatTrans, NatTrans.shift_app_comm, adj.unit, commShiftIso_comp_hom_app, shift_app_comm
-/
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        G.map ((F.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (F.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shift_counit_app` / 引理 `shift_counit_app`

English:
lemma shift_counit_app
  given: [adj.CommShift A] (a : A) (Y : D)
  proof: by
  have eq := NatTrans.shift_app_comm adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, Functor.id_obj, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_i

中文:
引理 shift_counit_app
  条件: [adj.CommShift A] (a : A) (Y : D)
  证明: by
  have eq := NatTrans.shift_app_comm adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, Functor.id_obj, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_i

Depends on / 依赖: F.map_comp_assoc, F.map_id, Functor, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, NatTrans, NatTrans.shift_app_comm, adj.counit, commShiftIso_comp_hom_app, commShiftIso_id_hom_app, comp_id, comp_obj, counit, id_comp, id_obj, inv_hom_id_app
-/
lemma shift_counit_app [adj.CommShift A] (a : A) (Y : D) :
    (adj.counit.app Y)⟦a⟧' =
      (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y) ≫
        adj.counit.app (Y⟦a⟧) := by
  have eq := NatTrans.shift_app_comm adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, Functor.id_obj, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_id, id_comp, Iso.inv_hom_id_app_assoc]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]

namespace RightAdjointCommShift

variable (a b : A) (h : b + a = 0) [F.CommShift A]

/--
Definition of `iso'` / `iso'` 的定义

English:
definition iso'
  signature: : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a
  body: (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

中文:
定义 iso'
  签名: : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a
  定义体: (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

Depends on / 依赖: Adjunction, Adjunction.comp, F.commShiftIso, commShiftIso, conjugateIsoEquiv, shiftEquiv, toAdjunction
-/
noncomputable def iso' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a
  body: iso' adj _ _ (neg_add_cancel a)

中文:
定义 iso
  签名: : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a
  定义体: iso' adj _ _ (neg_add_cancel a)

Depends on / 依赖: neg_add_cancel
-/
noncomputable def iso : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  iso' adj _ _ (neg_add_cancel a)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `iso_hom_app` / 引理 `iso_hom_app`

English:
lemma iso_hom_app
  given: (X : D)
  proof: by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', shiftEquiv']

中文:
引理 iso_hom_app
  条件: (X : D)
  证明: by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', shiftEquiv']

Depends on / 依赖: add_left_inj, neg_add_cancel, shiftEquiv
-/
lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (G.map ((F.commShiftIso b).hom.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (G.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (G.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', shiftEquiv']

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `iso_inv_app` / 引理 `iso_inv_app`

English:
lemma iso_inv_app
  given: (Y : D)
  proof: by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [iso, iso', shiftEquiv', Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Functor.comp_obj, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_

中文:
引理 iso_inv_app
  条件: (Y : D)
  证明: by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [iso, iso', shiftEquiv', Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Functor.comp_obj, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_

Depends on / 依赖: Equiv.toFun_as_coe, Equivalence, Equivalence.Equivalence_mk, Equivalence.toAdjunction_counit, Equivalence.toAdjunction_unit, Equivalence_mk, Functor, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Functor.map_shiftFunctorCompIsoId_hom_app, Iso.symm_hom, _counit, _unit, add_left_inj, comp_counit_app, comp_map, comp_obj, comp_unit_app
-/
lemma iso_inv_app (Y : D) :
    (iso adj a).inv.app Y =
      adj.unit.app ((shiftFunctor C a).obj (G.obj Y)) ≫
          G.map ((shiftFunctorCompIsoId D b a h).inv.app
              (F.obj ((shiftFunctor C a).obj (G.obj Y)))) ≫
            G.map ((shiftFunctor D a).map ((shiftFunctor D b).map
                ((F.commShiftIso a).hom.app (G.obj Y)))) ≫
              G.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [eq_neg_of_add_eq_zero_left h, add_neg_cancel])).hom.app
                    (F.obj (G.obj Y)))) ≫
                G.map ((shiftFunctor D a).map (adj.counit.app Y)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [iso, iso', shiftEquiv', Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Functor.comp_obj, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_unit, Iso.symm_hom, Functor.comp_map,
    comp_counit_app, Equivalence.toAdjunction_counit, Equivalence.Equivalence_mk'_counit,
    Functor.map_shiftFunctorCompIsoId_hom_app, assoc, Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityUnit_iso` / 引理 `compatibilityUnit_iso`

English:
lemma compatibilityUnit_iso
  given: (a : A)
  proof: by
  intro
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _)]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id_app]; rw [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [comp_id, homEquiv_counit, Functor.map_comp,

中文:
引理 compatibilityUnit_iso
  条件: (a : A)
  证明: by
  intro
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _)]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id_app]; rw [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [comp_id, homEquiv_counit, Functor.map_comp,

Depends on / 依赖: Functor, Functor.c, Functor.map_comp, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, NatTrans, NatTrans.naturality_assoc, RightAdjointCommShift, RightAdjointCommShift.iso, RightAdjointCommShift.iso_inv_app, adj.homEquiv, cancel_mono, comp_id, counit_naturality, counit_naturality_assoc, homEquiv, homEquiv_counit, hom_inv_id_app, injective, inv.app
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (F.commShiftIso a) (iso adj a) := by
  intro
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _)]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id_app]; rw [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [comp_id, homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    counit_naturality_assoc, left_triangle_components_assoc]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app]; rw [Iso.inv_hom_id_app_assoc]; rw [Functor.commShiftIso_hom_naturality_assoc]; rw [← Functor.map_comp]; rw [left_triangle_components]; rw [Functor.map_id]; rw [comp_id]

end RightAdjointCommShift

variable (A)

open RightAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this constructs
the unique compatible `CommShift` structure on `G`.
-/
@[simps -isSimp, instance_reducible]
/--
Definition of `rightAdjointCommShift` / `rightAdjointCommShift` 的定义

English:
definition rightAdjointCommShift
  signature: [F.CommShift A]
  body: iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso 0) _ _
      (compatibilityUnit_iso adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit

中文:
定义 rightAdjointCommShift
  签名: [F.CommShift A]
  定义体: iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso 0) _ _
      (compatibilityUnit_iso adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit
-/
noncomputable def rightAdjointCommShift [F.CommShift A] : G.CommShift A where
  commShiftIso a := iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso 0) _ _
      (compatibilityUnit_iso adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso (a + b)) _ _
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [F.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `commShift_of_leftAdjoint` / 引理 `commShift_of_leftAdjoint`

English:
lemma commShift_of_leftAdjoint
  given: [F.CommShift A]
  proof: adj.rightAdjointCommShift A
    adj.CommShift A := by
  let := adj.rightAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a => ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! RightAdjointComm

中文:
引理 commShift_of_leftAdjoint
  条件: [F.CommShift A]
  证明: adj.rightAdjointCommShift A
    adj.CommShift A := by
  let := adj.rightAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a => ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! RightAdjointComm

Depends on / 依赖: adj.rightAdjointCommShift, rightAdjointCommShift
-/
lemma commShift_of_leftAdjoint [F.CommShift A] :
    letI := adj.rightAdjointCommShift A
    adj.CommShift A := by
  let := adj.rightAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a => ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! RightAdjointCommShift.compatibilityUnit_iso adj a X

namespace LeftAdjointCommShift

variable {A} (a b : A) (h : a + b = 0) [G.CommShift A]

/--
Definition of `iso'` / `iso'` 的定义

English:
definition iso'
  signature: : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  body: (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a b h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C a b h).toAdjunction adj)).invFun (G.commShiftIso b)

中文:
定义 iso'
  签名: : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  定义体: (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a b h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C a b h).toAdjunction adj)).invFun (G.commShiftIso b)

Depends on / 依赖: Adjunction, Adjunction.comp, G.commShiftIso, commShiftIso, conjugateIsoEquiv, invFun, shiftEquiv, toAdjunction
-/
noncomputable def iso' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a b h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C a b h).toAdjunction adj)).invFun (G.commShiftIso b)

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  body: iso' adj _ _ (add_neg_cancel a)

中文:
定义 iso
  签名: : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  定义体: iso' adj _ _ (add_neg_cancel a)

Depends on / 依赖: add_neg_cancel
-/
noncomputable def iso : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  iso' adj _ _ (add_neg_cancel a)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `iso_hom_app` / 引理 `iso_hom_app`

English:
lemma iso_hom_app
  given: (X : C)
  proof: by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

中文:
引理 iso_hom_app
  条件: (X : C)
  证明: by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

Depends on / 依赖: eq_neg_of_add_eq_zero_right, shiftEquiv
-/
lemma iso_hom_app (X : C) :
    (iso adj a).hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫
      F.map (G.map (((shiftFunctorCompIsoId D a b h).inv.app (F.obj X)))⟦a⟧') ≫
        F.map (((G.commShiftIso b).hom.app ((F.obj X)⟦a⟧))⟦a⟧') ≫
          F.map ((shiftFunctorCompIsoId C b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (G.obj ((F.obj X)⟦a⟧))) ≫ adj.counit.app ((F.obj X)⟦a⟧) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `iso_inv_app` / 引理 `iso_inv_app`

English:
lemma iso_inv_app
  given: (Y : C)
  proof: by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

中文:
引理 iso_inv_app
  条件: (Y : C)
  证明: by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

Depends on / 依赖: eq_neg_of_add_eq_zero_right, shiftEquiv
-/
lemma iso_inv_app (Y : C) :
    (iso adj a).inv.app Y = (F.map ((shiftFunctorCompIsoId C a b h).inv.app Y))⟦a⟧' ≫
      (F.map ((adj.unit.app (Y⟦a⟧))⟦b⟧'))⟦a⟧' ≫ (F.map ((G.commShiftIso b).inv.app
        (F.obj (Y⟦a⟧))))⟦a⟧' ≫ (adj.counit.app ((F.obj (Y⟦a⟧))⟦b⟧))⟦a⟧' ≫
          (shiftFunctorCompIsoId D b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (F.obj (Y⟦a⟧)) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `compatibilityUnit_iso` / 引理 `compatibilityUnit_iso`

English:
lemma compatibilityUnit_iso
  given: (a : A)
  proof: by
  intro
  rw [LeftAdjointCommShift.iso_hom_app adj _ _ (add_neg_cancel a)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_shiftFunctorCompIsoId_inv_app,
    Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.

中文:
引理 compatibilityUnit_iso
  条件: (a : A)
  证明: by
  intro
  rw [LeftAdjointCommShift.iso_hom_app adj _ _ (add_neg_cancel a)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_shiftFunctorCompIsoId_inv_app,
    Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.

Depends on / 依赖: Functor, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Functor.map_id, Functor.map_shiftFunctorCompIsoId_inv_app, Iso.inv_hom_id_app, LeftAdjointCommShift, LeftAdjointCommShift.iso_hom_app, add_neg_cancel, comp_map, comp_obj, hom.naturality_assoc, id_comp, id_obj, inv_hom_id_app, iso_hom_app, map_comp, map_id
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (iso adj a) (G.commShiftIso a) := by
  intro
  rw [LeftAdjointCommShift.iso_hom_app adj _ _ (add_neg_cancel a)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_shiftFunctorCompIsoId_inv_app,
    Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp]
  rw [shift_shiftFunctorCompIsoId_inv_app]; rw [← Functor.comp_map]; rw [(shiftFunctorCompIsoId C _ _ (neg_add_cancel a)).hom.naturality_assoc]
  simp

end LeftAdjointCommShift

open LeftAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, this constructs
the unique compatible `CommShift` structure on `F`.
-/
@[simps -isSimp, instance_reducible]
/--
Definition of `leftAdjointCommShift` / `leftAdjointCommShift` 的定义

English:
definition leftAdjointCommShift
  signature: [G.CommShift A]
  body: iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso 0)
      (compatibilityUnit_iso adj 0) ?_
    rw [G.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_

中文:
定义 leftAdjointCommShift
  签名: [G.CommShift A]
  定义体: iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso 0)
      (compatibilityUnit_iso adj 0) ?_
    rw [G.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_
-/
noncomputable def leftAdjointCommShift [G.CommShift A] : F.CommShift A where
  commShiftIso a := iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso 0)
      (compatibilityUnit_iso adj 0) ?_
    rw [G.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso (a + b))
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [G.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `commShift_of_rightAdjoint` / 引理 `commShift_of_rightAdjoint`

English:
lemma commShift_of_rightAdjoint
  given: [G.CommShift A]
  proof: adj.leftAdjointCommShift A
    adj.CommShift A := by
  let := adj.leftAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a => ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! LeftAdjointCommShi

中文:
引理 commShift_of_rightAdjoint
  条件: [G.CommShift A]
  证明: adj.leftAdjointCommShift A
    adj.CommShift A := by
  let := adj.leftAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a => ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! LeftAdjointCommShi

Depends on / 依赖: adj.leftAdjointCommShift, leftAdjointCommShift
-/
lemma commShift_of_rightAdjoint [G.CommShift A] :
    letI := adj.leftAdjointCommShift A
    adj.CommShift A := by
  let := adj.leftAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a => ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! LeftAdjointCommShift.compatibilityUnit_iso adj a X

end Adjunction

namespace Equivalence

variable {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)

section

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

/--
Definition of `CommShift` / `CommShift` 的定义

English:
abbreviation CommShift
  signature: [E.functor.CommShift A] [E.inverse.CommShift A]
  body: E.toAdjunction.CommShift A

中文:
缩写 CommShift
  签名: [E.functor.CommShift A] [E.inverse.CommShift A]
  定义体: E.toAdjunction.CommShift A

Depends on / 依赖: CommShift, E.toAdjunction.CommShift, toAdjunction
-/
abbrev CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop :=
  E.toAdjunction.CommShift A

namespace CommShift

variable [E.functor.CommShift A] [E.inverse.CommShift A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [E.CommShift
  signature: A] : NatTrans.CommShift E.unitIso.hom A
  body: inferInstanceAs (NatTrans.CommShift E.toAdjunction.unit A)

中文:
实例 [E.CommShift
  签名: A] : 自然数Trans.CommShift E.unitIso.hom A
  定义体: inferInstanceAs (NatTrans.CommShift E.toAdjunction.unit A)

Depends on / 依赖: CommShift, E.toAdjunction.unit, NatTrans, NatTrans.CommShift, toAdjunction
-/
instance [E.CommShift A] : NatTrans.CommShift E.unitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.unit A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [E.CommShift
  signature: A] : NatTrans.CommShift E.counitIso.hom A
  body: inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)

中文:
实例 [E.CommShift
  签名: A] : 自然数Trans.CommShift E.counitIso.hom A
  定义体: inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)

Depends on / 依赖: CommShift, E.toAdjunction.counit, NatTrans, NatTrans.CommShift, counit, toAdjunction
-/
instance [E.CommShift A] : NatTrans.CommShift E.counitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: E.symm.inverse.CommShift A
  body: inferInstanceAs (E.functor.CommShift A)

中文:
实例 :
  签名: E.symm.inverse.CommShift A
  定义体: inferInstanceAs (E.functor.CommShift A)

Depends on / 依赖: CommShift, E.functor.CommShift, functor
-/
instance : E.symm.inverse.CommShift A := inferInstanceAs (E.functor.CommShift A)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: E.symm.functor.CommShift A
  body: inferInstanceAs (E.inverse.CommShift A)

中文:
实例 :
  签名: E.symm.functor.CommShift A
  定义体: inferInstanceAs (E.inverse.CommShift A)

Depends on / 依赖: CommShift, E.inverse.CommShift, inverse
-/
instance : E.symm.functor.CommShift A := inferInstanceAs (E.inverse.CommShift A)

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (h : NatTrans.CommShift E.unitIso.hom A)
  proof: h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

中文:
引理 mk'
  条件: (h : 自然数Trans.CommShift E.unitIso.hom A)
  证明: h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit
-/
lemma mk' (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_unit := h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Equivalence.refl (C := C)).functor.CommShift A
  body: inferInstanceAs (𝟭 C).CommShift A

中文:
实例 :
  签名: (Equivalence.refl (C := C)).functor.CommShift A
  定义体: inferInstanceAs (𝟭 C).CommShift A

Depends on / 依赖: CommShift, functor, functor.CommShift
-/
instance : (Equivalence.refl (C := C)).functor.CommShift A :=
inferInstanceAs (𝟭 C).CommShift A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Equivalence.refl (C := C)).inverse.CommShift A
  body: inferInstanceAs (𝟭 C).CommShift A

中文:
实例 :
  签名: (Equivalence.refl (C := C)).inverse.CommShift A
  定义体: inferInstanceAs (𝟭 C).CommShift A

Depends on / 依赖: CommShift, inverse, inverse.CommShift
-/
instance : (Equivalence.refl (C := C)).inverse.CommShift A :=
inferInstanceAs (𝟭 C).CommShift A


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Equivalence.refl (C := C)).CommShift A
  body: inferInstanceAs Adjunction.id.CommShift A

中文:
实例 :
  签名: (Equivalence.refl (C := C)).CommShift A
  定义体: inferInstanceAs Adjunction.id.CommShift A

Depends on / 依赖: CommShift
-/
instance : (Equivalence.refl (C := C)).CommShift A :=
inferInstanceAs Adjunction.id.CommShift A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [E.CommShift
  signature: A] : E.symm.CommShift A
  body: mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))

中文:
实例 [E.CommShift
  签名: A] : E.symm.CommShift A
  定义体: mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))

Depends on / 依赖: CommShift, E.counitIso.inv, E.symm, NatTrans, NatTrans.CommShift, counitIso
-/
instance [E.CommShift A] : E.symm.CommShift A :=
  mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))

/--
lemma `mk''` / 引理 `mk''`

English:
lemma mk''
  given: (h : NatTrans.CommShift E.counitIso.hom A)
  proof: have := mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))
  inferInstanceAs (E.symm.symm.CommShift A)

中文:
引理 mk''
  条件: (h : 自然数Trans.CommShift E.counitIso.hom A)
  证明: have := mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))
  inferInstanceAs (E.symm.symm.CommShift A)

Depends on / 依赖: CommShift, E.counitIso.inv, E.symm, E.symm.symm.CommShift, NatTrans, NatTrans.CommShift, counitIso
-/
lemma mk'' (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A :=
  have := mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))
  inferInstanceAs (E.symm.symm.CommShift A)

variable {F : Type*} [Category* F] [HasShift F A] {E' : D ≌ F} [E.CommShift A]
    [E'.functor.CommShift A] [E'.inverse.CommShift A] [E'.CommShift A]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (E.trans E').functor.CommShift A
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: (E.trans E').functor.CommShift A
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : (E.trans E').functor.CommShift A := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (E.trans E').inverse.CommShift A
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: (E.trans E').inverse.CommShift A
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : (E.trans E').inverse.CommShift A := by
  dsimp
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (E.trans E').CommShift A
  body: inferInstanceAs ((E.toAdjunction.comp E'.toAdjunction).CommShift A)

中文:
实例 :
  签名: (E.trans E').CommShift A
  定义体: inferInstanceAs ((E.toAdjunction.comp E'.toAdjunction).CommShift A)

Depends on / 依赖: CommShift, E.toAdjunction.comp, toAdjunction
-/
instance : (E.trans E').CommShift A :=
  inferInstanceAs ((E.toAdjunction.comp E'.toAdjunction).CommShift A)

end CommShift

end

variable (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.functor`,
this constructs the unique compatible `CommShift` structure on `E.inverse`.
-/
@[instance_reducible]
/--
Definition of `commShiftInverse` / `commShiftInverse` 的定义

English:
definition commShiftInverse
  signature: [E.functor.CommShift A]
  body: E.toAdjunction.rightAdjointCommShift A

中文:
定义 commShiftInverse
  签名: [E.functor.CommShift A]
  定义体: E.toAdjunction.rightAdjointCommShift A

Depends on / 依赖: E.toAdjunction.rightAdjointCommShift, rightAdjointCommShift, toAdjunction
-/
noncomputable def commShiftInverse [E.functor.CommShift A] : E.inverse.CommShift A :=
  E.toAdjunction.rightAdjointCommShift A

/--
lemma `commShift_of_functor` / 引理 `commShift_of_functor`

English:
lemma commShift_of_functor
  given: [E.functor.CommShift A]
  proof: E.commShiftInverse A
    E.CommShift A := by
  let := E.commShiftInverse A
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint A).commShift_unit

中文:
引理 commShift_of_functor
  条件: [E.functor.CommShift A]
  证明: E.commShiftInverse A
    E.CommShift A := by
  let := E.commShiftInverse A
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint A).commShift_unit

Depends on / 依赖: E.commShiftInverse, commShiftInverse
-/
lemma commShift_of_functor [E.functor.CommShift A] :
    letI := E.commShiftInverse A
    E.CommShift A := by
  let := E.commShiftInverse A
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint A).commShift_unit

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.inverse`,
this constructs the unique compatible `CommShift` structure on `E.functor`.
-/
@[instance_reducible]
/--
Definition of `commShiftFunctor` / `commShiftFunctor` 的定义

English:
definition commShiftFunctor
  signature: [E.inverse.CommShift A]
  body: E.symm.toAdjunction.rightAdjointCommShift A

中文:
定义 commShiftFunctor
  签名: [E.inverse.CommShift A]
  定义体: E.symm.toAdjunction.rightAdjointCommShift A

Depends on / 依赖: E.symm.toAdjunction.rightAdjointCommShift, rightAdjointCommShift, toAdjunction
-/
noncomputable def commShiftFunctor [E.inverse.CommShift A] : E.functor.CommShift A :=
  E.symm.toAdjunction.rightAdjointCommShift A

set_option backward.isDefEq.respectTransparency false in
/--
lemma `commShift_of_inverse` / 引理 `commShift_of_inverse`

English:
lemma commShift_of_inverse
  given: [E.inverse.CommShift A]
  proof: E.commShiftFunctor A
    E.CommShift A := by
  let := E.commShiftFunctor A
  have := E.symm.commShift_of_functor A
  exact inferInstanceAs (E.symm.symm.CommShift A)

中文:
引理 commShift_of_inverse
  条件: [E.inverse.CommShift A]
  证明: E.commShiftFunctor A
    E.CommShift A := by
  let := E.commShiftFunctor A
  have := E.symm.commShift_of_functor A
  exact inferInstanceAs (E.symm.symm.CommShift A)

Depends on / 依赖: E.commShiftFunctor, commShiftFunctor
-/
lemma commShift_of_inverse [E.inverse.CommShift A] :
    letI := E.commShiftFunctor A
    E.CommShift A := by
  let := E.commShiftFunctor A
  have := E.symm.commShift_of_functor A
  exact inferInstanceAs (E.symm.symm.CommShift A)

end Equivalence

end CategoryTheory
