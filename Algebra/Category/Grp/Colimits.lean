/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sophie Morel
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.DFinsupp.Small
public import Mathlib.GroupTheory.QuotientGroup.Defs
/-!
# The category of additive commutative groups has all colimits.

This file constructs colimits in the category of additive commutative groups, as
quotients of finitely supported functions.

-/

@[expose] public section

universe u' w u v

open CategoryTheory Limits

namespace AddCommGrpCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

namespace Colimits

/-!
We build the colimit of a diagram in `AddCommGrpCat` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

/--
Definition of `Relations` / `Relations` 的定义

English:
abbreviation Relations
  signature: [DecidableEq J]
  body: AddSubgroup.closure {x | exists (j j' : J) (u : j ⟶ j') (a : F.obj j),
    x = DFinsupp.single j' (F.map u a) - DFinsupp.single j a}

中文:
缩写 Relations
  签名: [DecidableEq J]
  定义体: AddSubgroup.closure {x | exists (j j' : J) (u : j ⟶ j') (a : F.obj j),
    x = DFinsupp.single j' (F.map u a) - DFinsupp.single j a}

Depends on / 依赖: AddSubgroup, AddSubgroup.closure, DFinsupp, DFinsupp.single, F.map, F.obj, closure, single
-/
abbrev Relations [DecidableEq J] : AddSubgroup (DFinsupp (fun j => F.obj j)) :=
  AddSubgroup.closure {x | exists (j j' : J) (u : j ⟶ j') (a : F.obj j),
    x = DFinsupp.single j' (F.map u a) - DFinsupp.single j a}

/--
Definition of `Quot` / `Quot` 的定义

English:
definition Quot
  signature: [DecidableEq J]
  body: DFinsupp (fun j => F.obj j) ⧸ Relations F

中文:
定义 Quot
  签名: [DecidableEq J]
  定义体: DFinsupp (fun j => F.obj j) ⧸ Relations F

Depends on / 依赖: DFinsupp, F.obj, Relations
-/
def Quot [DecidableEq J] : Type (max u w) :=
  DFinsupp (fun j => F.obj j) ⧸ Relations F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: J] : AddCommGroup (Quot F)
  body: QuotientAddGroup.Quotient.addCommGroup (Relations F)

中文:
实例 [DecidableEq
  签名: J] : AddCommGroup (Quot F)
  定义体: QuotientAddGroup.Quotient.addCommGroup (Relations F)

Depends on / 依赖: Quotient, QuotientAddGroup, QuotientAddGroup.Quotient.addCommGroup, Relations, addCommGroup
-/
instance [DecidableEq J] : AddCommGroup (Quot F) :=
  QuotientAddGroup.Quotient.addCommGroup (Relations F)

/--
Definition of `Quot.ι` / `Quot.ι` 的定义

English:
definition Quot.ι
  signature: [DecidableEq J] (j : J)
  body: (QuotientAddGroup.mk' _).comp (DFinsupp.singleAddHom (fun j => F.obj j) j)

中文:
定义 Quot.ι
  签名: [DecidableEq J] (j : J)
  定义体: (QuotientAddGroup.mk' _).comp (DFinsupp.singleAddHom (fun j => F.obj j) j)

Depends on / 依赖: DFinsupp, DFinsupp.singleAddHom, F.obj, QuotientAddGroup, QuotientAddGroup.mk, singleAddHom
-/
def Quot.ι [DecidableEq J] (j : J) : F.obj j ->+ Quot F :=
  (QuotientAddGroup.mk' _).comp (DFinsupp.singleAddHom (fun j => F.obj j) j)

/--
lemma `Quot.addMonoidHom_ext` / 引理 `Quot.addMonoidHom_ext`

English:
lemma Quot.addMonoidHom_ext
  statement: [DecidableEq J] {α : Type*} [AddMonoid α] {f g : Quot F ->+ α}
  proof: QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

中文:
引理 Quot.addMonoidHom_ext
  结论: [DecidableEq J] {α : 类型} [AddMonoid α] {f g : Quot F ->+ α}
  证明: QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

Depends on / 依赖: DFinsupp, DFinsupp.addHom_ext, QuotientAddGroup, QuotientAddGroup.addMonoidHom_ext, addHom_ext, addMonoidHom_ext
-/
lemma Quot.addMonoidHom_ext [DecidableEq J] {α : Type*} [AddMonoid α] {f g : Quot F ->+ α}
    (h : forall (j : J) (x : F.obj j), f (Quot.ι F j x) = g (Quot.ι F j x)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

variable (c : Cocone F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Quot.desc` / `Quot.desc` 的定义

English:
definition Quot.desc
  signature: [DecidableEq J]
  body: by
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom fun x => (c.ι.app x).hom) ?_
  dsimp
  rw [AddSubgroup.closure_le]
  intro _ ⟨_, _, _, _, eq⟩
  rw [eq]
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single]
  change (F.map _ ≫ c.ι.app _) _ - _ = 0
  rw [c.ι.n

中文:
定义 Quot.desc
  签名: [DecidableEq J]
  定义体: by
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom fun x => (c.ι.app x).hom) ?_
  dsimp
  rw [AddSubgroup.closure_le]
  intro _ ⟨_, _, _, _, eq⟩
  rw [eq]
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single]
  change (F.map _ ≫ c.ι.app _) _ - _ = 0
  rw [c.ι.n

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, AddSubgroup, AddSubgroup.closure_le, Category, Category.comp_id, DFinsupp, DFinsupp.sumAddHom, DFinsupp.sumAddHom_single, F.map, Functor, Functor.const_obj_map, Functor.const_obj_obj, QuotientAddGroup, QuotientAddGroup.lift, SetLike, SetLike.mem_coe, closure_le, comp_id, const_obj_map
-/
def Quot.desc [DecidableEq J] : Quot.{w} F ->+ c.pt := by
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom fun x => (c.ι.app x).hom) ?_
  dsimp
  rw [AddSubgroup.closure_le]
  intro _ ⟨_, _, _, _, eq⟩
  rw [eq]
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single]
  change (F.map _ ≫ c.ι.app _) _ - _ = 0
  rw [c.ι.naturality]
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, sub_self]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Quot.ι_desc` / 引理 `Quot.ι_desc`

English:
lemma Quot.ι_desc
  given: [DecidableEq J] (j : J) (x : F.obj j)
  proof: by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

中文:
引理 Quot.ι_desc
  条件: [DecidableEq J] (j : J) (x : F.obj j)
  证明: by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.lift_mk, lift_mk
-/
lemma Quot.ι_desc [DecidableEq J] (j : J) (x : F.obj j) :
    Quot.desc F c (Quot.ι F j x) = c.ι.app j x := by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Quot.map_ι` / 引理 `Quot.map_ι`

English:
lemma Quot.map_ι
  given: [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j)
  proof: by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

中文:
引理 Quot.map_ι
  条件: [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j)
  证明: by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, AddSubgroup, AddSubgroup.subset_closure, DFinsupp, DFinsupp.singleAddHom_apply, QuotientAddGroup, QuotientAddGroup.ker_mk, QuotientAddGroup.mk, Relations, eq_of_sub_eq_zero, ker_mk, map_sub, mem_ker, singleAddHom_apply, subset_closure
-/
lemma Quot.map_ι [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j) :
    Quot.ι F j' (F.map f x) = Quot.ι F j x := by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `quotToQuotUlift` / `quotToQuotUlift` 的定义

English:
definition quotToQuotUlift
  signature: [DecidableEq J]
  body: by
  refine QuotientAddGroup.lift (Relations F) (DFinsupp.sumAddHom (fun j => (Quot.ι _ j).comp
    AddEquiv.ulift.symm.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  rw [SetLike.mem_coe]; rw [AddMonoidHom.mem_ker]; rw [map_sub]; rw [DFinsupp.sumAd

中文:
定义 quotToQuotUlift
  签名: [DecidableEq J]
  定义体: by
  refine QuotientAddGroup.lift (Relations F) (DFinsupp.sumAddHom (fun j => (Quot.ι _ j).comp
    AddEquiv.ulift.symm.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  rw [SetLike.mem_coe]; rw [AddMonoidHom.mem_ker]; rw [map_sub]; rw [DFinsupp.sumAd

Depends on / 依赖: AddEquiv, AddEquiv.ulift.symm, AddEquiv.ulift.symm.toAddMonoidHom, AddMonoidHom, AddMonoidHom.mem_ker, AddSubgroup, AddSubgroup.closure_le, DFinsupp, DFinsupp.sumAddHom, DFinsupp.sumAddHom_single, Quot.map_, QuotientAddGroup, QuotientAddGroup.lift, Relations, SetLike, SetLike.mem_coe, closure_le, map_sub, mem_coe, mem_ker
-/
def quotToQuotUlift [DecidableEq J] : Quot F ->+ Quot (F ⋙ uliftFunctor.{u'}) := by
  refine QuotientAddGroup.lift (Relations F) (DFinsupp.sumAddHom (fun j => (Quot.ι _ j).comp
    AddEquiv.ulift.symm.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  rw [SetLike.mem_coe]; rw [AddMonoidHom.mem_ker]; rw [map_sub]; rw [DFinsupp.sumAddHom_single]; rw [DFinsupp.sumAddHom_single]
  change Quot.ι (F ⋙ uliftFunctor) j' ((F ⋙ uliftFunctor).map u (AddEquiv.ulift.symm a)) - _ = _
  rw [Quot.map_ι]
  dsimp
  rw [sub_self]

/--
lemma `quotToQuotUlift_ι` / 引理 `quotToQuotUlift_ι`

English:
lemma quotToQuotUlift_ι
  given: [DecidableEq J] (j : J) (x : F.obj j)
  proof: by
  dsimp [quotToQuotUlift, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single]
  rfl

中文:
引理 quotToQuotUlift_ι
  条件: [DecidableEq J] (j : J) (x : F.obj j)
  证明: by
  dsimp [quotToQuotUlift, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single]
  rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, DFinsupp, DFinsupp.singleAddHom, DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single, QuotientAddGroup, QuotientAddGroup.lift_mk, QuotientAddGroup.mk, Relations, comp_apply, conv_lhs, lift_mk, quotToQuotUlift, singleAddHom, singleAddHom_apply, sumAddHom_single
-/
lemma quotToQuotUlift_ι [DecidableEq J] (j : J) (x : F.obj j) :
    quotToQuotUlift F (Quot.ι F j x) = Quot.ι _ j (ULift.up x) := by
  dsimp [quotToQuotUlift, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `quotUliftToQuot` / `quotUliftToQuot` 的定义

English:
definition quotUliftToQuot
  signature: [DecidableEq J]
  body: by
  refine QuotientAddGroup.lift (Relations (F ⋙ uliftFunctor))
    (DFinsupp.sumAddHom (fun j => (Quot.ι _ j).comp AddEquiv.ulift.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  simp

中文:
定义 quotUliftToQuot
  签名: [DecidableEq J]
  定义体: by
  refine QuotientAddGroup.lift (Relations (F ⋙ uliftFunctor))
    (DFinsupp.sumAddHom (fun j => (Quot.ι _ j).comp AddEquiv.ulift.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  simp

Depends on / 依赖: AddEquiv, AddEquiv.ulift.toAddMonoidHom, AddSubgroup, AddSubgroup.closure_le, DFinsupp, DFinsupp.sumAddHom, QuotientAddGroup, QuotientAddGroup.lift, Relations, closure_le, sumAddHom, toAddMonoidHom, uliftFunctor
-/
def quotUliftToQuot [DecidableEq J] : Quot (F ⋙ uliftFunctor.{u'}) ->+ Quot F := by
  refine QuotientAddGroup.lift (Relations (F ⋙ uliftFunctor))
    (DFinsupp.sumAddHom (fun j => (Quot.ι _ j).comp AddEquiv.ulift.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `quotUliftToQuot_ι` / 引理 `quotUliftToQuot_ι`

English:
lemma quotUliftToQuot_ι
  given: [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j)
  proof: by
  dsimp [quotUliftToQuot, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, Function.c

中文:
引理 quotUliftToQuot_ι
  条件: [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j)
  证明: by
  dsimp [quotUliftToQuot, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, Function.c

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_comp, AddMonoidHom.comp_apply, DFinsupp, DFinsupp.singleAddHom, DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single, Function, Function.comp_apply, QuotientAddGroup, QuotientAddGroup.lift_mk, QuotientAddGroup.mk, Relations, coe_comp, comp_apply, conv_lhs, lift_mk, quotUliftToQuot, singleAddHom, singleAddHom_apply
-/
lemma quotUliftToQuot_ι [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j) :
    quotUliftToQuot F (Quot.ι _ j x) = Quot.ι F j x.down := by
  dsimp [quotUliftToQuot, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, Function.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
The additive equivalence between `Quot F` and `Quot (F ⋙ uliftFunctor.{u'})`.
-/
@[simp]
/--
Definition of `quotQuotUliftAddEquiv` / `quotQuotUliftAddEquiv` 的定义

English:
definition quotQuotUliftAddEquiv
  signature: [DecidableEq J]
  body: quotToQuotUlift F
  invFun := quotUliftToQuot F
  left_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply]; rw [Quot.addMonoidHom_ext F (f := (quotUliftToQuot F).comp
      (quotToQuotUlift F)) (fun j a => ?_)]
    rw [AddMonoidHom.comp_apply]; rw [AddMono

中文:
定义 quotQuotUliftAddEquiv
  签名: [DecidableEq J]
  定义体: quotToQuotUlift F
  invFun := quotUliftToQuot F
  left_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply]; rw [Quot.addMonoidHom_ext F (f := (quotUliftToQuot F).comp
      (quotToQuotUlift F)) (fun j a => ?_)]
    rw [AddMonoidHom.comp_apply]; rw [AddMono

Depends on / 依赖: quotToQuotUlift
-/
def quotQuotUliftAddEquiv [DecidableEq J] : Quot F ≃+ Quot (F ⋙ uliftFunctor.{u'}) where
  toFun := quotToQuotUlift F
  invFun := quotUliftToQuot F
  left_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply]; rw [Quot.addMonoidHom_ext F (f := (quotUliftToQuot F).comp
      (quotToQuotUlift F)) (fun j a => ?_)]
    rw [AddMonoidHom.comp_apply]; rw [AddMonoidHom.id_apply]; rw [quotToQuotUlift_ι]; rw [quotUliftToQuot_ι]
  right_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply]; rw [Quot.addMonoidHom_ext _ (f := (quotToQuotUlift F).comp
      (quotUliftToQuot F)) (fun j a => ?_)]
    rw [AddMonoidHom.comp_apply]; rw [AddMonoidHom.id_apply]; rw [quotUliftToQuot_ι]; rw [quotToQuotUlift_ι]
    rfl
  map_add' _ _ := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Quot.desc_quotQuotUliftAddEquiv` / 引理 `Quot.desc_quotQuotUliftAddEquiv`

English:
lemma Quot.desc_quotQuotUliftAddEquiv
  given: [DecidableEq J] (c : Cocone F)
  proof: by
  refine Quot.addMonoidHom_ext _ (fun j a => ?_)
  dsimp
  simp only [quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [Quot.ι_desc]
  rfl

中文:
引理 Quot.desc_quotQuotUliftAddEquiv
  条件: [DecidableEq J] (c : Cocone F)
  证明: by
  refine Quot.addMonoidHom_ext _ (fun j a => ?_)
  dsimp
  simp only [quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [Quot.ι_desc]
  rfl

Depends on / 依赖: Functor, Functor.comp_obj, Functor.const_obj_obj, Quot.addMonoidHom_ext, addMonoidHom_ext, comp_obj, const_obj_obj, uliftFunctor_obj
-/
lemma Quot.desc_quotQuotUliftAddEquiv [DecidableEq J] (c : Cocone F) :
    (Quot.desc (F ⋙ uliftFunctor.{u'}) (uliftFunctor.{u'}.mapCocone c)).comp
    (quotQuotUliftAddEquiv F).toAddMonoidHom =
    AddEquiv.ulift.symm.toAddMonoidHom.comp (Quot.desc F c) := by
  refine Quot.addMonoidHom_ext _ (fun j a => ?_)
  dsimp
  simp only [quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [Quot.ι_desc]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- (implementation detail) A morphism of commutative additive groups `Quot F →+ A`
induces a cocone on `F` as long as the universes work out.
-/
@[simps]
/--
Definition of `toCocone` / `toCocone` 的定义

English:
definition toCocone
  signature: [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
  body: AddCommGrpCat.of A
ι.app j := ofHom f.comp (Quot.ι F j)

中文:
定义 toCocone
  签名: [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
  定义体: AddCommGrpCat.of A
ι.app j := ofHom f.comp (Quot.ι F j)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of
-/
def toCocone [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A) : Cocone F where
  pt := AddCommGrpCat.of A
ι.app j := ofHom f.comp (Quot.ι F j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Quot.desc_toCocone_desc` / 引理 `Quot.desc_toCocone_desc`

English:
lemma Quot.desc_toCocone_desc
  statement: [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
  proof: by
  refine Quot.addMonoidHom_ext F (fun j x => ?_)
  rw [AddMonoidHom.comp_apply]; rw [ι_desc]
  change (c.ι.app j ≫ hc.desc (toCocone F f)) _ = _
  rw [hc.fac]
  simp

中文:
引理 Quot.desc_toCocone_desc
  结论: [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
  证明: by
  refine Quot.addMonoidHom_ext F (fun j x => ?_)
  rw [AddMonoidHom.comp_apply]; rw [ι_desc]
  change (c.ι.app j ≫ hc.desc (toCocone F f)) _ = _
  rw [hc.fac]
  simp

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, Quot.addMonoidHom_ext, addMonoidHom_ext, comp_apply, hc.desc, hc.fac, toCocone
-/
lemma Quot.desc_toCocone_desc [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
    (hc : IsColimit c) : (hc.desc (toCocone F f)).hom.comp (Quot.desc F c) = f := by
  refine Quot.addMonoidHom_ext F (fun j x => ?_)
  rw [AddMonoidHom.comp_apply]; rw [ι_desc]
  change (c.ι.app j ≫ hc.desc (toCocone F f)) _ = _
  rw [hc.fac]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Quot.desc_toCocone_desc_app` / 引理 `Quot.desc_toCocone_desc_app`

English:
lemma Quot.desc_toCocone_desc_app
  statement: [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
  proof: by
  conv_rhs => rw [← Quot.desc_toCocone_desc F c f hc]
  dsimp

中文:
引理 Quot.desc_toCocone_desc_app
  结论: [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
  证明: by
  conv_rhs => rw [← Quot.desc_toCocone_desc F c f hc]
  dsimp

Depends on / 依赖: Quot.desc_toCocone_desc, conv_rhs, desc_toCocone_desc
-/
lemma Quot.desc_toCocone_desc_app [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A)
    (hc : IsColimit c) (x : Quot F) : hc.desc (toCocone F f) (Quot.desc F c x) = f x := by
  conv_rhs => rw [← Quot.desc_toCocone_desc F c f hc]
  dsimp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimit_of_bijective_desc` / `isColimit_of_bijective_desc` 的定义

English:
definition isColimit_of_bijective_desc
  signature: [DecidableEq J]
  body: AddCommGrpCat.ofHom ((Quot.desc F s).comp (AddEquiv.ofBijective
    (Quot.desc F c) h).symm.toAddMonoidHom)
  fac s j := by
    ext x
    dsimp
    conv_lhs => erw [← Quot.ι_desc F c j x]
    rw [← AddEquiv.ofBijective_apply _ h]; rw [AddEquiv.symm_apply_apply]
    simp only [Quot.ι_desc, Functor.co

中文:
定义 isColimit_of_bijective_desc
  签名: [DecidableEq J]
  定义体: AddCommGrpCat.ofHom ((Quot.desc F s).comp (AddEquiv.ofBijective
    (Quot.desc F c) h).symm.toAddMonoidHom)
  fac s j := by
    ext x
    dsimp
    conv_lhs => erw [← Quot.ι_desc F c j x]
    rw [← AddEquiv.ofBijective_apply _ h]; rw [AddEquiv.symm_apply_apply]
    simp only [Quot.ι_desc, Functor.co

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ofHom, AddEquiv, AddEquiv.ofBijective, Quot.desc, ofBijective
-/
noncomputable def isColimit_of_bijective_desc [DecidableEq J]
     (h : Function.Bijective (Quot.desc F c)) : IsColimit c where
  desc s := AddCommGrpCat.ofHom ((Quot.desc F s).comp (AddEquiv.ofBijective
    (Quot.desc F c) h).symm.toAddMonoidHom)
  fac s j := by
    ext x
    dsimp
    conv_lhs => erw [← Quot.ι_desc F c j x]
    rw [← AddEquiv.ofBijective_apply _ h]; rw [AddEquiv.symm_apply_apply]
    simp only [Quot.ι_desc, Functor.const_obj_obj]
  uniq s m hm := by
    ext x
    obtain ⟨x, rfl⟩ := h.2 x
    dsimp
    rw [← AddEquiv.ofBijective_apply _ h]; rw [AddEquiv.symm_apply_apply]
    suffices eq : m.hom.comp (AddEquiv.ofBijective (Quot.desc F c) h) = Quot.desc F s by
      rw [← eq]; rfl
    exact Quot.addMonoidHom_ext F (by simp [← hm])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (internal implementation) The colimit cocone of a functor `F`, implemented as a quotient of
`DFinsupp (fun j ↦ F.obj j)`, under the assumption that said quotient is small.
-/
@[simps pt ι_app]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: [DecidableEq J] [Small.{w} (Quot.{w} F)]
  body: AddCommGrpCat.of (Shrink (Quot F))
  ι :=
    { app j :=
        AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp (Quot.ι F j))
      naturality _ _ _ := by
        ext
        dsimp
        change Shrink.addEquiv.symm _ = _
        rw [Quot.map_ι] }

@[simp]

中文:
定义 colimitCocone
  签名: [DecidableEq J] [Small.{w} (Quot.{w} F)]
  定义体: AddCommGrpCat.of (Shrink (Quot F))
  ι :=
    { app j :=
        AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp (Quot.ι F j))
      naturality _ _ _ := by
        ext
        dsimp
        change Shrink.addEquiv.symm _ = _
        rw [Quot.map_ι] }

@[simp]

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, Shrink
-/
noncomputable def colimitCocone [DecidableEq J] [Small.{w} (Quot.{w} F)] : Cocone F where
  pt := AddCommGrpCat.of (Shrink (Quot F))
  ι :=
    { app j :=
        AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp (Quot.ι F j))
      naturality _ _ _ := by
        ext
        dsimp
        change Shrink.addEquiv.symm _ = _
        rw [Quot.map_ι] }

@[simp]
/--
theorem `Quot.desc_colimitCocone` / 定理 `Quot.desc_colimitCocone`

English:
theorem Quot.desc_colimitCocone
  given: [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (Quot F)]
  proof: by
  refine Quot.addMonoidHom_ext F (fun j x => ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using! Quot.ι_desc F (colimitCocone F) j x

中文:
定理 Quot.desc_colimitCocone
  条件: [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (Quot F)]
  证明: by
  refine Quot.addMonoidHom_ext F (fun j x => ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using! Quot.ι_desc F (colimitCocone F) j x

Depends on / 依赖: AddEquiv, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom, AddMonoidHom.coe_coe, Quot.addMonoidHom_ext, addMonoidHom_ext, coe_coe, colimitCocone, colimitCocone_pt, symm.toAddMonoidHom, toAddMonoidHom, toAddMonoidHom_eq_coe
-/
theorem Quot.desc_colimitCocone [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (Quot F)] :
    Quot.desc F (colimitCocone F) = (Shrink.addEquiv (α := Quot F)).symm.toAddMonoidHom := by
  refine Quot.addMonoidHom_ext F (fun j x => ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using! Quot.ι_desc F (colimitCocone F) j x

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: [DecidableEq J] [Small.{w} (Quot F)]
  body: by
  refine isColimit_of_bijective_desc F _ ?_
  rw [Quot.desc_colimitCocone]
  exact Shrink.addEquiv.symm.bijective

中文:
定义 colimitCoconeIsColimit
  签名: [DecidableEq J] [Small.{w} (Quot F)]
  定义体: by
  refine isColimit_of_bijective_desc F _ ?_
  rw [Quot.desc_colimitCocone]
  exact Shrink.addEquiv.symm.bijective

Depends on / 依赖: Quot.desc_colimitCocone, Shrink, Shrink.addEquiv.symm.bijective, addEquiv, bijective, desc_colimitCocone, isColimit_of_bijective_desc
-/
noncomputable def colimitCoconeIsColimit [DecidableEq J] [Small.{w} (Quot F)] :
    IsColimit (colimitCocone F) := by
  refine isColimit_of_bijective_desc F _ ?_
  rw [Quot.desc_colimitCocone]
  exact Shrink.addEquiv.symm.bijective

end Colimits

open Colimits

/--
lemma `hasColimit_of_small_quot` / 引理 `hasColimit_of_small_quot`

English:
lemma hasColimit_of_small_quot
  given: [DecidableEq J] (h : Small.{w} (Quot F))
  statement: HasColimit F
  proof: ⟨_, colimitCoconeIsColimit F⟩

中文:
引理 hasColimit_of_small_quot
  条件: [DecidableEq J] (h : Small.{w} (Quot F))
  结论: HasColimit F
  证明: ⟨_, colimitCoconeIsColimit F⟩

Depends on / 依赖: colimitCoconeIsColimit
-/
lemma hasColimit_of_small_quot [DecidableEq J] (h : Small.{w} (Quot F)) : HasColimit F :=
  ⟨_, colimitCoconeIsColimit F⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: J] [Small.{w} J] : Small.{w} (Quot F)
  body: small_of_surjective (QuotientAddGroup.mk'_surjective _)

中文:
实例 [DecidableEq
  签名: J] [Small.{w} J] : Small.{w} (Quot F)
  定义体: small_of_surjective (QuotientAddGroup.mk'_surjective _)

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk, _surjective, small_of_surjective
-/
instance [DecidableEq J] [Small.{w} J] : Small.{w} (Quot F) :=
  small_of_surjective (QuotientAddGroup.mk'_surjective _)

/--
Instance `hasColimit` / 实例 `hasColimit`

English:
instance hasColimit
  signature: [Small.{w} J] (F : J ⥤ AddCommGrpCat.{w})
  body: by
  classical
  exact hasColimit_of_small_quot F inferInstance

中文:
实例 hasColimit
  签名: [Small.{w} J] (F : J ⥤ AddCommGrpCat.{w})
  定义体: by
  classical
  exact hasColimit_of_small_quot F inferInstance

Depends on / 依赖: Classical, Multiset, Multiset.count_nsmul, Multiset.ext, Nat.mul_right_inj, classical, count_nsmul, hasColimit_of_small_quot, mul_right_inj, scoped
-/
instance hasColimit [Small.{w} J] (F : J ⥤ AddCommGrpCat.{w}) : HasColimit F := by
  classical
  exact hasColimit_of_small_quot F inferInstance


/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: [Small.{w} J]

中文:
实例 hasColimitsOfShape
  签名: [Small.{w} J]
-/
instance hasColimitsOfShape [Small.{w} J] : HasColimitsOfShape J (AddCommGrpCat.{w}) where

/-- The category of additive commutative groups has all small colimits.
-/
instance (priority := 1300) hasColimitsOfSize [UnivLE.{u, w}] :
    HasColimitsOfSize.{v, u} (AddCommGrpCat.{w}) where

end AddCommGrpCat

namespace AddCommGrpCat

open QuotientAddGroup

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cokernelIsoQuotient` / `cokernelIsoQuotient` 的定义

English:
definition cokernelIsoQuotient
  signature: {G H : AddCommGrpCat.{u}} (f : G ⟶ H)
  body: cokernel.desc f (ofHom (mk' _)) by
        ext x
        simp
inv := ofHom
QuotientAddGroup.lift _ (cokernel.π f).hom by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc

中文:
定义 cokernelIsoQuotient
  签名: {G H : AddCommGrpCat.{u}} (f : G ⟶ H)
  定义体: cokernel.desc f (ofHom (mk' _)) by
        ext x
        simp
inv := ofHom
QuotientAddGroup.lift _ (cokernel.π f).hom by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_comp, AddMonoidHom.coe_id, AddMonoidHom.zero_apply, Category, Category.comp_id, Function, Function.comp_apply, QuotientAddGroup, QuotientAddGroup.in, QuotientAddGroup.lift, coe_comp, coe_id, coe_mk, coequalizer, coequalizer.hom_ext, coequalizer_as_cokernel, cokernel, cokernel.condition_apply, cokernel.desc
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGrpCat.of (H ⧸ AddMonoidHom.range f.hom) where
hom := cokernel.desc f (ofHom (mk' _)) by
        ext x
        simp
inv := ofHom
QuotientAddGroup.lift _ (cokernel.π f).hom by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc, Category.comp_id]
    rfl
  inv_hom_id := by
    ext x
    dsimp only [hom_comp, hom_ofHom, hom_zero, AddMonoidHom.coe_comp, coe_mk',
      Function.comp_apply, AddMonoidHom.zero_apply, id_eq, lift_mk, hom_id, AddMonoidHom.coe_id]
exact QuotientAddGroup.induction_on (α := H) x cokernel.π_desc_apply f _ _

end AddCommGrpCat
