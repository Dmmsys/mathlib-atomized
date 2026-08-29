/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Equivalence between subobjects and quotients in an abelian category

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

noncomputable section

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In an abelian category, the subobjects and quotient objects of an object `X` are
order-isomorphic via taking kernels and cokernels.
Implemented here using subobjects in the opposite category,
since mathlib does not have a notion of quotient objects at the time of writing. -/
@[simps!]
/--
Definition of `subobjectIsoSubobjectOp` / `subobjectIsoSubobjectOp` 的定义

English:
definition subobjectIsoSubobjectOp
  signature: [Abelian C] (X : C)
  body: by
  refine OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) ?_ ?_
  · change (cokernelOrderHom X).comp (kernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, kernelOrderHom_coe, Subobject.lif

中文:
定义 subobjectIsoSubobjectOp
  签名: [交换 C] (X : C)
  定义体: by
  refine OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) ?_ ?_
  · change (cokernelOrderHom X).comp (kernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, kernelOrderHom_coe, Subobject.lif

Depends on / 依赖: Abelian, Abelian.epiDesc, Function, Function.comp_apply, OrderHom, OrderHom.comp_coe, OrderHom.ext, OrderHom.id_coe, OrderIso, OrderIso.ofHomInv, Quiver, Quiver.Hom.unop_inj, Subobject, Subobject.ind, Subobject.lift_mk, Subobject.mk_eq_mk_of_comm, cokernel, cokernel.condition, cokernelOrderHom, cokernelOrderHom_coe
-/
def subobjectIsoSubobjectOp [Abelian C] (X : C) : Subobject X ≃o (Subobject (op X))ᵒᵈ := by
  refine OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) ?_ ?_
  · change (cokernelOrderHom X).comp (kernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, kernelOrderHom_coe, Subobject.lift_mk,
      cokernelOrderHom_coe, OrderHom.id_coe, id]
    refine Subobject.mk_eq_mk_of_comm _ _
        ⟨?_, ?_, Quiver.Hom.unop_inj ?_, Quiver.Hom.unop_inj ?_⟩ ?_
    · exact (Abelian.epiDesc f.unop _ (cokernel.condition (kernel.ι f.unop))).op
    · exact (cokernel.desc _ _ (kernel.condition f.unop)).op
    · rw [← cancel_epi (cokernel.π (kernel.ι f.unop))]
      simp only [unop_comp, Quiver.Hom.unop_op, unop_id_op, cokernel.π_desc_assoc,
        comp_epiDesc, Category.comp_id]
    · simp only [← cancel_epi f.unop, unop_comp, Quiver.Hom.unop_op, unop_id, comp_epiDesc_assoc,
        cokernel.π_desc, Category.comp_id]
    · exact Quiver.Hom.unop_inj (by simp only [unop_comp, Quiver.Hom.unop_op, comp_epiDesc])
  · change (kernelOrderHom X).comp (cokernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, cokernelOrderHom_coe, Subobject.lift_mk,
      kernelOrderHom_coe, OrderHom.id_coe, id, unop_op, Quiver.Hom.unop_op]
    refine Subobject.mk_eq_mk_of_comm _ _ ⟨?_, ?_, ?_, ?_⟩ ?_
    · exact Abelian.monoLift f _ (kernel.condition (cokernel.π f))
    · exact kernel.lift _ _ (cokernel.condition f)
    · simp only [← cancel_mono (kernel.ι (cokernel.π f)), Category.assoc, image.fac, monoLift_comp,
        Category.id_comp]
    · simp only [← cancel_mono f, Category.assoc, monoLift_comp, image.fac, Category.id_comp]
    · simp only [monoLift_comp]

/--
Instance `wellPowered_opposite` / 实例 `wellPowered_opposite`

English:
instance wellPowered_opposite
  signature: [Abelian C] [LocallySmall.{w} C] [WellPowered.{w} C]
  body: (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance

中文:
实例 wellPowered_opposite
  签名: [交换 C] [LocallySmall.{w} C] [良幂.{w} C]
  定义体: (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance

Depends on / 依赖: small_congr, subobjectIsoSubobjectOp, toEquiv
-/
instance wellPowered_opposite [Abelian C] [LocallySmall.{w} C] [WellPowered.{w} C] :
    WellPowered.{w} Cᵒᵖ where
  subobject_small X :=
    (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance

end CategoryTheory.Abelian
