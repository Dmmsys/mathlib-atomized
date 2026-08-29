/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Additional results about the `liftToFinset` construction

If `f` is a family of objects of `C`, then there is a canonical cocone whose cocone point is the
coproduct of `f` and whose legs are given by the inclusions of the finite subcoproducts. If `C`
is preadditive, then we can describe the legs of this cocone as finite sums of projections followed
by inclusions.
-/

public section

universe w v u


namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CoproductsFromFiniteFiltered

variable [HasFiniteCoproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `finiteSubcoproductsCocone_ι_app_eq_sum` / 定理 `finiteSubcoproductsCocone_ι_app_eq_sum`

English:
theorem finiteSubcoproductsCocone_ι_app_eq_sum
  statement: {α : Type w} [DecidableEq α] (f : α -> C)
  proof: by
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj, finiteSubcoproductsCocone_ι_app]
  ext v
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Preadditive.comp_sum]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hb

中文:
定理 finiteSubcoproductsCocone_ι_app_eq_sum
  结论: {α : 类型 w} [DecidableEq α] (f : α -> C)
  证明: by
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj, finiteSubcoproductsCocone_ι_app]
  ext v
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Preadditive.comp_sum]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hb

Depends on / 依赖: Cofan.mk_, Cofan.mk_pt, Discrete, Discrete.functor_obj_eq_as, Finset, Finset.sum_eq_single, Functor, Functor.const_obj_obj, Ne.symm, Preadditive, Preadditive.comp_sum, colimit, comp_sum, const_obj_obj, finiteSubcoproductsCocone_pt, functor_obj_eq_as, liftToFinsetObj_obj, mk_pt, sum_eq_single, zero_comp
-/
theorem finiteSubcoproductsCocone_ι_app_eq_sum {α : Type w} [DecidableEq α] (f : α -> C)
    [HasCoproduct f] (S : Finset (Discrete α)) :
    (finiteSubcoproductsCocone f).ι.app S = ∑ a in S.attach, Sigma.π _ a ≫ Sigma.ι _ a.1.as := by
  dsimp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
    Functor.const_obj_obj, finiteSubcoproductsCocone_ι_app]
  ext v
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Preadditive.comp_sum]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hb₁
    rw [Sigma.ι_π_of_ne_assoc _ (Ne.symm hb₁)]; rw [zero_comp]
  · simp

end CoproductsFromFiniteFiltered

namespace ProductsFromFiniteCofiltered

variable [HasFiniteProducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `finiteSubproductsCocone_π_app_eq_sum` / 定理 `finiteSubproductsCocone_π_app_eq_sum`

English:
theorem finiteSubproductsCocone_π_app_eq_sum
  statement: {α : Type w} [DecidableEq α] (f : α -> C) [HasProduct f]
  proof: by
  dsimp only [finiteSubproductsCone_pt, Functor.const_obj_obj, liftToFinsetObj_obj,
    Discrete.functor_obj_eq_as, finiteSubproductsCone_π_app]
  ext v
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb 

中文:
定理 finiteSubproductsCocone_π_app_eq_sum
  结论: {α : 类型 w} [DecidableEq α] (f : α -> C) [HasProduct f]
  证明: by
  dsimp only [finiteSubproductsCone_pt, Functor.const_obj_obj, liftToFinsetObj_obj,
    Discrete.functor_obj_eq_as, finiteSubproductsCone_π_app]
  ext v
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb 

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.functor_obj_eq_as, Fan.mk_, Fan.mk_pt, Finset, Finset.sum_eq_single, Functor, Functor.const_obj_obj, Preadditive, Preadditive.sum_comp, comp_zero, const_obj_obj, finiteSubproductsCone_pt, functor_obj_eq_as, liftToFinsetObj_obj, limit.lift_, mk_pt, sum_comp
-/
theorem finiteSubproductsCocone_π_app_eq_sum {α : Type w} [DecidableEq α] (f : α -> C) [HasProduct f]
    (S : (Finset (Discrete α))ᵒᵖ) :
    (finiteSubproductsCone f).π.app S =
      ∑ a in S.unop.attach, Pi.π f a.1.as ≫ Pi.ι (fun a => f a.1.as) a := by
  dsimp only [finiteSubproductsCone_pt, Functor.const_obj_obj, liftToFinsetObj_obj,
    Discrete.functor_obj_eq_as, finiteSubproductsCone_π_app]
  ext v
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hb₁
    rw [Pi.ι_π_of_ne _ hb₁]; rw [comp_zero]
  · simp

end ProductsFromFiniteCofiltered

end CategoryTheory.Limits
