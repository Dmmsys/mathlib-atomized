/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The canonical topology on a category

We define the finest (largest) Grothendieck topology for which a given presheaf `P` is a sheaf.
This is well defined since if `P` is a sheaf for a topology `J`, then it is a sheaf for any
coarser (smaller) topology. Nonetheless we define the topology explicitly by specifying its sieves:
A sieve `S` on `X` is covering for `finestTopologySingle P` iff
  for any `f : Y ⟶ X`, `P` satisfies the sheaf axiom for `S.pullback f`.
Showing that this is a genuine Grothendieck topology (namely that it satisfies the transitivity
axiom) forms the bulk of this file.

This generalises to a set of presheaves, giving the topology `finestTopology Ps` which is the
finest topology for which every presheaf in `Ps` is a sheaf.
Using `Ps` as the set of representable presheaves defines the `canonicalTopology`: the finest
topology for which every representable is a sheaf.

A Grothendieck topology is called `Subcanonical` if it is smaller than the canonical topology,
equivalently it is subcanonical iff every representable presheaf is a sheaf.

## References
* https://ncatlab.org/nlab/show/canonical+topology
* https://ncatlab.org/nlab/show/subcanonical+coverage
* https://stacks.math.columbia.edu/tag/00Z9
* https://math.stackexchange.com/a/358709/
-/

@[expose] public section


universe w v u

namespace CategoryTheory

open CategoryTheory Category Limits Sieve

variable {C : Type u} [Category.{v} C]

variable {P : Cᵒᵖ ⥤ Type w} {X : C} (J : GrothendieckTopology C)

namespace Sheaf

@[deprecated (since := "2026-02-06")] alias isSheafFor_bind := Presieve.isSheafFor_bind

@[deprecated (since := "2026-02-06")] alias isSheafFor_trans := Presieve.isSheafFor_trans

/-- Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf. -/
@[stacks 00Z9 "This is a special case of the Stacks entry, but following a different
proof (see the Stacks comments)."]
/--
Definition of `finestTopologySingle` / `finestTopologySingle` 的定义

English:
definition finestTopologySingle
  signature: (P : Cᵒᵖ ⥤ Type w)
  body: {S | forall (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f : Presieve Y)}
  top_mem' X Y f := by
    rw [Sieve.pullback_top]
    exact Presieve.isSheafFor_top P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g := by
    -- This is the 

中文:
定义 finestTopologySingle
  签名: (P : Cᵒᵖ ⥤ 类型 w)
  定义体: {S | forall (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f : Presieve Y)}
  top_mem' X Y f := by
    rw [Sieve.pullback_top]
    exact Presieve.isSheafFor_top P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g := by
    -- This is the 

Depends on / 依赖: IsSheafFor, Presieve, Presieve.IsSheafFor, S.pullback, pullback
-/
def finestTopologySingle (P : Cᵒᵖ ⥤ Type w) : GrothendieckTopology C where
  sieves X := {S | forall (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f : Presieve Y)}
  top_mem' X Y f := by
    rw [Sieve.pullback_top]
    exact Presieve.isSheafFor_top P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g := by
    -- This is the hard part of the construction, showing that the given set of sieves satisfies
    -- the transitivity axiom.
    refine Presieve.isSheafFor_trans P (pullback g S) _ (hS Z g) ?_ ?_
    · intro Y f _
      rw [← pullback_comp]
      apply (hS _ _).isSeparatedFor
    · intro Y f hf
      have := hR hf _ (𝟙 _)
      rw [pullback_id]; rw [pullback_comp] at this
      apply this

/-- Construct the finest (largest) Grothendieck topology for which all the given presheaves are
sheaves. -/
@[stacks 00Z9 "Equal to that Stacks construction"]
/--
Definition of `finestTopology` / `finestTopology` 的定义

English:
definition finestTopology
  signature: (Ps : Set (Cᵒᵖ ⥤ Type w))
  body: sInf (finestTopologySingle '' Ps)

中文:
定义 finestTopology
  签名: (Ps : 集合 (Cᵒᵖ ⥤ 类型 w))
  定义体: sInf (finestTopologySingle '' Ps)

Depends on / 依赖: finestTopologySingle
-/
def finestTopology (Ps : Set (Cᵒᵖ ⥤ Type w)) : GrothendieckTopology C :=
  sInf (finestTopologySingle '' Ps)

/--
theorem `sheaf_for_finestTopology` / 定理 `sheaf_for_finestTopology`

English:
theorem sheaf_for_finestTopology
  given: (Ps : Set (Cᵒᵖ ⥤ Type w)) (h : P in Ps)
  proof: fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)

中文:
定理 sheaf_for_finestTopology
  条件: (Ps : 集合 (Cᵒᵖ ⥤ 类型 w)) (h : P in Ps)
  证明: fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)
-/
theorem sheaf_for_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type w)) (h : P in Ps) :
    Presieve.IsSheaf (finestTopology Ps) P := fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)

/--
lemma `mem_finestTopology_of_forall_isSheafFor` / 引理 `mem_finestTopology_of_forall_isSheafFor`

English:
lemma mem_finestTopology_of_forall_isSheafFor
  statement: {Ps : Set (Cᵒᵖ ⥤ Type w)} {X : C} {S : Sieve X}
  proof: by
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩ Y f
  exact H P hP _

中文:
引理 mem_finestTopology_of_对任意_isSheafFor
  结论: {Ps : 集合 (Cᵒᵖ ⥤ 类型 w)} {X : C} {S : 筛 X}
  证明: by
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩ Y f
  exact H P hP _
-/
lemma mem_finestTopology_of_forall_isSheafFor {Ps : Set (Cᵒᵖ ⥤ Type w)} {X : C} {S : Sieve X}
    (H : forall P in Ps, forall ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f).arrows) :
    S in finestTopology Ps X := by
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩ Y f
  exact H P hP _

/--
theorem `le_finestTopology` / 定理 `le_finestTopology`

English:
theorem le_finestTopology
  statement: (Ps : Set (Cᵒᵖ ⥤ Type w)) (J : GrothendieckTopology C)
  proof: by
  intro X S hS
  exact mem_finestTopology_of_forall_isSheafFor
    fun P hP Y f => hJ P hP _ (J.pullback_stable _ hS)

中文:
定理 le_finestTopology
  结论: (Ps : 集合 (Cᵒᵖ ⥤ 类型 w)) (J : Grothendieck拓扑 C)
  证明: by
  intro X S hS
  exact mem_finestTopology_of_forall_isSheafFor
    fun P hP Y f => hJ P hP _ (J.pullback_stable _ hS)

Depends on / 依赖: J.pullback_stable, mem_finestTopology_of_forall_isSheafFor, pullback_stable
-/
theorem le_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type w)) (J : GrothendieckTopology C)
    (hJ : forall P in Ps, Presieve.IsSheaf J P) : J <= finestTopology Ps := by
  intro X S hS
  exact mem_finestTopology_of_forall_isSheafFor
    fun P hP Y f => hJ P hP _ (J.pullback_stable _ hS)

/-- The `canonicalTopology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf. -/
@[stacks 00ZA]
/--
Definition of `canonicalTopology` / `canonicalTopology` 的定义

English:
definition canonicalTopology
  signature: (C : Type u) [Category.{v} C]
  body: finestTopology (Set.range yoneda.obj)

中文:
定义 canonicalTopology
  签名: (C : 类型u) [范畴.{v} C]
  定义体: finestTopology (Set.range yoneda.obj)

Depends on / 依赖: Set.range, finestTopology, yoneda, yoneda.obj
-/
def canonicalTopology (C : Type u) [Category.{v} C] : GrothendieckTopology C :=
  finestTopology (Set.range yoneda.obj)

/--
theorem `isSheaf_yoneda_obj` / 定理 `isSheaf_yoneda_obj`

English:
theorem isSheaf_yoneda_obj
  given: (X : C)
  statement: Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X)
  proof: fun _ _ hS => sheaf_for_finestTopology _ (Set.mem_range_self _) _ hS

中文:
定理 isSheaf_yoneda_obj
  条件: (X : C)
  结论: Presieve.是层 (canonicalTopology C) (yoneda.obj X)
  证明: fun _ _ hS => sheaf_for_finestTopology _ (Set.mem_range_self _) _ hS

Depends on / 依赖: Set.mem_range_self, mem_range_self, sheaf_for_finestTopology
-/
theorem isSheaf_yoneda_obj (X : C) : Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X) :=
  fun _ _ hS => sheaf_for_finestTopology _ (Set.mem_range_self _) _ hS

/--
theorem `isSheaf_of_isRepresentable` / 定理 `isSheaf_of_isRepresentable`

English:
theorem isSheaf_of_isRepresentable
  given: (P : Cᵒᵖ ⥤ Type w) [P.IsRepresentable]
  proof: by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff]
  refine Presieve.isSheaf_iso (canonicalTopology C) (P ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  rw [← isSheaf_iff_isSheaf_of_type]
  refine GrothendieckTopology.HasSheafCompose.isSheaf _ ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact isSheaf_yone

中文:
定理 isSheaf_of_isRepresentable
  条件: (P : Cᵒᵖ ⥤ 类型 w) [P.是Representable]
  证明: by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff]
  refine Presieve.isSheaf_iso (canonicalTopology C) (P ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  rw [← isSheaf_iff_isSheaf_of_type]
  refine GrothendieckTopology.HasSheafCompose.isSheaf _ ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact isSheaf_yone

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.HasSheafCompose.isSheaf, HasSheafCompose, Presieve, Presieve.isSheaf_comp_uliftFunctor_iff, Presieve.isSheaf_iso, canonicalTopology, isSheaf, isSheaf_comp_uliftFunctor_iff, isSheaf_iff_isSheaf_of_type, isSheaf_iso, isSheaf_yoneda_obj, uliftFunctor, uliftYonedaReprXIso
-/
theorem isSheaf_of_isRepresentable (P : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] :
    Presieve.IsSheaf (canonicalTopology C) P := by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff]
  refine Presieve.isSheaf_iso (canonicalTopology C) (P ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  rw [← isSheaf_iff_isSheaf_of_type]
  refine GrothendieckTopology.HasSheafCompose.isSheaf _ ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact isSheaf_yoneda_obj _

end Sheaf

namespace GrothendieckTopology

open Sheaf

/--
Definition of `Subcanonical` / `Subcanonical` 的定义

English:
class Subcanonical
  parameters: (J : GrothendieckTopology C)
  axioms and operations (1):
    - le_canonical : J <= canonicalTopology C

中文:
类 子典范
  参数: (J : Grothendieck拓扑 C)
  公理与运算 (1 个):
    - le_canonical : J <= canonicalTopology C
-/
class Subcanonical (J : GrothendieckTopology C) : Prop where
  le_canonical : J <= canonicalTopology C

/--
lemma `le_canonical` / 引理 `le_canonical`

English:
lemma le_canonical
  given: (J : GrothendieckTopology C) [Subcanonical J]
  statement: J <= canonicalTopology C
  proof: Subcanonical.le_canonical

中文:
引理 le_canonical
  条件: (J : Grothendieck拓扑 C) [子典范 J]
  结论: J <= canonicalTopology C
  证明: Subcanonical.le_canonical

Depends on / 依赖: Subcanonical, Subcanonical.le_canonical, le_canonical
-/
lemma le_canonical (J : GrothendieckTopology C) [Subcanonical J] : J <= canonicalTopology C :=
  Subcanonical.le_canonical

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (canonicalTopology C).Subcanonical
  body: le_rfl

中文:
实例 :
  签名: (canonicalTopology C).子典范
  定义体: le_rfl

Depends on / 依赖: le_rfl
-/
instance : (canonicalTopology C).Subcanonical where
  le_canonical := le_rfl

namespace Subcanonical

/--
theorem `of_isSheaf_yoneda_obj` / 定理 `of_isSheaf_yoneda_obj`

English:
theorem of_isSheaf_yoneda_obj
  statement: (J : GrothendieckTopology C)
  proof: le_finestTopology _ _ (by rintro P ⟨X, rfl⟩; apply h)

中文:
定理 of_isSheaf_yoneda_obj
  结论: (J : Grothendieck拓扑 C)
  证明: le_finestTopology _ _ (by rintro P ⟨X, rfl⟩; apply h)

Depends on / 依赖: le_finestTopology
-/
theorem of_isSheaf_yoneda_obj (J : GrothendieckTopology C)
    (h : forall X, Presieve.IsSheaf J (yoneda.obj X)) : Subcanonical J where
  le_canonical := le_finestTopology _ _ (by rintro P ⟨X, rfl⟩; apply h)

/--
theorem `isSheaf_of_isRepresentable` / 定理 `isSheaf_of_isRepresentable`

English:
theorem isSheaf_of_isRepresentable
  statement: {J : GrothendieckTopology C} [Subcanonical J]
  proof: Presieve.isSheaf_of_le _ J.le_canonical (Sheaf.isSheaf_of_isRepresentable P)

中文:
定理 isSheaf_of_isRepresentable
  结论: {J : Grothendieck拓扑 C} [子典范 J]
  证明: Presieve.isSheaf_of_le _ J.le_canonical (Sheaf.isSheaf_of_isRepresentable P)

Depends on / 依赖: J.le_canonical, Presieve, Presieve.isSheaf_of_le, Sheaf.isSheaf_of_isRepresentable, isSheaf_of_isRepresentable, isSheaf_of_le, le_canonical
-/
theorem isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J]
    (P : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P :=
  Presieve.isSheaf_of_le _ J.le_canonical (Sheaf.isSheaf_of_isRepresentable P)

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: {J K : GrothendieckTopology C} (h : J <= K) [K.Subcanonical]
  statement: J.Subcanonical
  proof: of_isSheaf_yoneda_obj _ fun _ _ _ _ => (isSheaf_of_isRepresentable (J := K) _).isSheafFor _
    (h _ (by simpa))

中文:
引理 of_le
  条件: {J K : Grothendieck拓扑 C} (h : J <= K) [K.子典范]
  结论: J.子典范
  证明: of_isSheaf_yoneda_obj _ fun _ _ _ _ => (isSheaf_of_isRepresentable (J := K) _).isSheafFor _
    (h _ (by simpa))

Depends on / 依赖: isSheafFor, isSheaf_of_isRepresentable, of_isSheaf_yoneda_obj
-/
lemma of_le {J K : GrothendieckTopology C} (h : J <= K) [K.Subcanonical] : J.Subcanonical :=
  of_isSheaf_yoneda_obj _ fun _ _ _ _ => (isSheaf_of_isRepresentable (J := K) _).isSheafFor _
    (h _ (by simpa))

end Subcanonical

variable (J : GrothendieckTopology C)

/--
If `J` is subcanonical, we obtain a "Yoneda" functor from the defining site
into the sheaf category.
-/
@[simps! obj_obj map_hom, implicit_reducible]
/--
Definition of `yoneda` / `yoneda` 的定义

English:
definition yoneda
  signature: [J.Subcanonical]
  body: ObjectProperty.lift _ CategoryTheory.yoneda fun X => by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subcanonical.isSheaf_of_isRepresentable

中文:
定义 yoneda
  签名: [J.子典范]
  定义体: ObjectProperty.lift _ CategoryTheory.yoneda fun X => by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subcanonical.isSheaf_of_isRepresentable

Depends on / 依赖: CategoryTheory, CategoryTheory.yoneda, ObjectProperty, ObjectProperty.lift, Subcanonical, Subcanonical.isSheaf_of_isRepresentable, isSheaf_iff_isSheaf_of_type, isSheaf_of_isRepresentable, yoneda
-/
def yoneda [J.Subcanonical] : C ⥤ Sheaf J (Type v) :=
ObjectProperty.lift _ CategoryTheory.yoneda fun X => by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subcanonical.isSheaf_of_isRepresentable

/-- Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ, simps! +dsimpLhs]
/--
Definition of `uliftYoneda` / `uliftYoneda` 的定义

English:
definition uliftYoneda
  signature: [J.Subcanonical]
  body: J.yoneda ⋙ sheafCompose J uliftFunctor.{w}

#adaptation_note

中文:
定义 uliftYoneda
  签名: [J.子典范]
  定义体: J.yoneda ⋙ sheafCompose J uliftFunctor.{w}

#adaptation_note

Depends on / 依赖: J.yoneda, sheafCompose, uliftFunctor, yoneda
-/
def uliftYoneda [J.Subcanonical] : C ⥤ Sheaf J (Type (max v w)) :=
  J.yoneda ⋙ sheafCompose J uliftFunctor.{w}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `C` is a category with `[Category.{max w v} C]`, this is the isomorphism
`uliftYoneda.{w} (C := C) ≅ yoneda`. -/
@[simps!]
/--
Definition of `uliftYonedaIsoYoneda` / `uliftYonedaIsoYoneda` 的定义

English:
definition uliftYonedaIsoYoneda
  signature: {C : Type u} [Category.{max w v} C] (J : GrothendieckTopology C)
  body: dsimp% NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun _ => Equiv.ulift.toIso)))

中文:
定义 uliftYonedaIsoYoneda
  签名: {C : 类型u} [范畴.{最大值 w v} C] (J : Grothendieck拓扑 C)
  定义体: dsimp% NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun _ => Equiv.ulift.toIso)))

Depends on / 依赖: Equiv.ulift.toIso, NatIso, NatIso.ofComponents, fullyFaithfulSheafToPresheaf, ofComponents, preimageIso
-/
def uliftYonedaIsoYoneda {C : Type u} [Category.{max w v} C] (J : GrothendieckTopology C)
    [J.Subcanonical] :
    GrothendieckTopology.uliftYoneda.{w} J ≅ J.yoneda :=
  dsimp% NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun _ => Equiv.ulift.toIso)))

variable [Subcanonical J]

/--
Definition of `yonedaCompSheafToPresheaf` / `yonedaCompSheafToPresheaf` 的定义

English:
definition yonedaCompSheafToPresheaf
  signature: :
  body: Iso.refl _

#adaptation_note

中文:
定义 yonedaCompSheafToPresheaf
  签名: :
  定义体: Iso.refl _

#adaptation_note

Depends on / 依赖: Iso.refl
-/
def yonedaCompSheafToPresheaf :
    J.yoneda ⋙ sheafToPresheaf J (Type v) ≅ CategoryTheory.yoneda :=
  Iso.refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `yonedaCompSheafToPresheaf` with a raise in the universe level. -/
@[simps! +dsimpLhs]
/--
Definition of `uliftYonedaCompSheafToPresheaf` / `uliftYonedaCompSheafToPresheaf` 的定义

English:
definition uliftYonedaCompSheafToPresheaf
  signature: :
  body: Iso.refl _

中文:
定义 uliftYonedaCompSheafToPresheaf
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def uliftYonedaCompSheafToPresheaf :
    GrothendieckTopology.uliftYoneda.{w} J ⋙ sheafToPresheaf J (Type (max v w)) ≅
      CategoryTheory.uliftYoneda.{w} :=
  Iso.refl _

/--
Definition of `yonedaFullyFaithful` / `yonedaFullyFaithful` 的定义

English:
definition yonedaFullyFaithful
  signature: : (J.yoneda).FullyFaithful
  body: Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (Type v)) Yoneda.fullyFaithful

中文:
定义 yonedaFullyFaithful
  签名: : (J.yoneda).满忠实
  定义体: Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (Type v)) Yoneda.fullyFaithful

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofCompFaithful, Yoneda, Yoneda.fullyFaithful, fullyFaithful, ofCompFaithful, sheafToPresheaf
-/
def yonedaFullyFaithful : (J.yoneda).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (Type v)) Yoneda.fullyFaithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (J.yoneda).Full
  body: (J.yonedaFullyFaithful).full

中文:
实例 :
  签名: (J.yoneda).满
  定义体: (J.yonedaFullyFaithful).full

Depends on / 依赖: J.yonedaFullyFaithful, yonedaFullyFaithful
-/
instance : (J.yoneda).Full := (J.yonedaFullyFaithful).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (J.yoneda).Faithful
  body: (J.yonedaFullyFaithful).faithful

中文:
实例 :
  签名: (J.yoneda).忠实
  定义体: (J.yonedaFullyFaithful).faithful

Depends on / 依赖: J.yonedaFullyFaithful, faithful, yonedaFullyFaithful
-/
instance : (J.yoneda).Faithful := (J.yonedaFullyFaithful).faithful

/--
Definition of `fullyFaithfulUliftYoneda` / `fullyFaithfulUliftYoneda` 的定义

English:
definition fullyFaithfulUliftYoneda
  signature: : (GrothendieckTopology.uliftYoneda.{w} J).FullyFaithful
  body: J.yonedaFullyFaithful.comp (fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor)

中文:
定义 fullyFaithfulUliftYoneda
  签名: : (Grothendieck拓扑.uliftYoneda.{w} J).满忠实
  定义体: J.yonedaFullyFaithful.comp (fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor)

Depends on / 依赖: J.yonedaFullyFaithful.comp, fullyFaithfulSheafCompose, fullyFaithfulULiftFunctor, yonedaFullyFaithful
-/
def fullyFaithfulUliftYoneda : (GrothendieckTopology.uliftYoneda.{w} J).FullyFaithful :=
  J.yonedaFullyFaithful.comp (fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (GrothendieckTopology.uliftYoneda.{w} J).Full
  body: (J.fullyFaithfulUliftYoneda).full

中文:
实例 :
  签名: (Grothendieck拓扑.uliftYoneda.{w} J).满
  定义体: (J.fullyFaithfulUliftYoneda).full

Depends on / 依赖: J.fullyFaithfulUliftYoneda, fullyFaithfulUliftYoneda
-/
instance : (GrothendieckTopology.uliftYoneda.{w} J).Full :=
  (J.fullyFaithfulUliftYoneda).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (GrothendieckTopology.uliftYoneda.{w} J).Faithful
  body: (J.fullyFaithfulUliftYoneda).faithful

中文:
实例 :
  签名: (Grothendieck拓扑.uliftYoneda.{w} J).忠实
  定义体: (J.fullyFaithfulUliftYoneda).faithful

Depends on / 依赖: J.fullyFaithfulUliftYoneda, faithful, fullyFaithfulUliftYoneda
-/
instance : (GrothendieckTopology.uliftYoneda.{w} J).Faithful :=
  (J.fullyFaithfulUliftYoneda).faithful

end GrothendieckTopology

end CategoryTheory
