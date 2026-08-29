/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# The sigma-comparison map

This file defines the map `CompHausLike.sigmaComparison` associated to a presheaf `X` on
`CompHausLike P`, and a finite family `S₁,...,Sₙ` of spaces in `CompHausLike P`, where `P` is
stable under taking finite disjoint unions.

The map `sigmaComparison` is the canonical map `X(S₁ ⊔ ... ⊔ Sₙ) ⟶ X(S₁) × ... × X(Sₙ)` induced by
the inclusion maps `Sᵢ ⟶ S₁ ⊔ ... ⊔ Sₙ`, and it is an isomorphism when `X` preserves finite
products.
-/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} -> Prop} [HasExplicitFiniteCoproducts.{u} P]
  (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts X]
  {α : Type u} [Finite α] (σ : α -> Type u)
  [forall a, TopologicalSpace (σ a)] [forall a, CompactSpace (σ a)] [forall a, T2Space (σ a)]
  [forall a, HasProp P (σ a)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasProp P (Σ (a : α), (σ a))
  body: HasExplicitFiniteCoproducts.hasProp (fun a => of P (σ a))

中文:
实例 :
  签名: 有命题 P (Σ (a : α), (σ a))
  定义体: HasExplicitFiniteCoproducts.hasProp (fun a => of P (σ a))

Depends on / 依赖: HasExplicitFiniteCoproducts, HasExplicitFiniteCoproducts.hasProp, hasProp
-/
instance : HasProp P (Σ (a : α), (σ a)) := HasExplicitFiniteCoproducts.hasProp (fun a => of P (σ a))

/--
Definition of `sigmaComparison` / `sigmaComparison` 的定义

English:
definition sigmaComparison
  signature: : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) -> X.obj ⟨of P (σ a)⟩)
  body: ↾fun x a => X.map (ofHom _ ⟨Sigma.mk a, continuous_sigmaMk⟩).op x

中文:
定义 sigmaComparison
  签名: : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) -> X.obj ⟨of P (σ a)⟩)
  定义体: ↾fun x a => X.map (ofHom _ ⟨Sigma.mk a, continuous_sigmaMk⟩).op x

Depends on / 依赖: Sigma.mk, X.map, continuous_sigmaMk
-/
def sigmaComparison : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) -> X.obj ⟨of P (σ a)⟩) :=
  ↾fun x a => X.map (ofHom _ ⟨Sigma.mk a, continuous_sigmaMk⟩).op x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `sigmaComparison_eq_comp_isos` / 定理 `sigmaComparison_eq_comp_isos`

English:
theorem sigmaComparison_eq_comp_isos
  statement: sigmaComparison X σ =
  proof: by
  ext x a
  simp only [TypeCat.Fun.toFun_apply, Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, comp_apply, Types.productIso_hom_comp_eval_apply]
  have := ConcreteCategory.congr_hom (piComparison_comp_π X (fun a => ⟨of P (σ a)⟩) a)
  simp only [comp_apply] at this
  rw 

中文:
定理 sigmaComparison_eq_comp_isos
  结论: sigmaComparison X σ =
  证明: by
  ext x a
  simp only [TypeCat.Fun.toFun_apply, Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, comp_apply, Types.productIso_hom_comp_eval_apply]
  have := ConcreteCategory.congr_hom (piComparison_comp_π X (fun a => ⟨of P (σ a)⟩) a)
  simp only [comp_apply] at this
  rw 

Depends on / 依赖: Cofan.mk_pt, ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ofHom, Fan.mk_pt, Functor, Functor.mapIso_hom, Functor.map_comp, PreservesProduct, PreservesProduct.iso_hom, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, Types.productIso_hom_comp_eval_apply, coe_mk, comp_apply, congr_hom, hom_ofHom, iso_hom, mapIso_hom
-/
theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.mapIso (opCoproductIsoProduct'
      (finiteCoproduct.isColimit.{u, u} (fun a => of P (σ a)))
      (productIsProduct fun x => Opposite.op (of P (σ x))))).hom ≫
    (PreservesProduct.iso X fun a => ⟨of P (σ a)⟩).hom ≫
    (Types.productIso.{u, max u w} fun a => X.obj ⟨of P (σ a)⟩).hom := by
  ext x a
  simp only [TypeCat.Fun.toFun_apply, Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, comp_apply, Types.productIso_hom_comp_eval_apply]
  have := ConcreteCategory.congr_hom (piComparison_comp_π X (fun a => ⟨of P (σ a)⟩) a)
  simp only [comp_apply] at this
  rw [this]; rw [← comp_apply]; rw [← Functor.map_comp]
  simp only [sigmaComparison, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  apply ConcreteCategory.congr_hom
  congr 2
  rw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  simp only [opCoproductIsoProduct, ← unop_comp, opCoproductIsoProduct'_comp_self]
  erw [IsColimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isIsoSigmaComparison` / 实例 `isIsoSigmaComparison`

English:
instance isIsoSigmaComparison
  signature: : IsIso sigmaComparison X σ
  body: by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

中文:
实例 isIsoSigmaComparison
  签名: : 是同构 sigmaComparison X σ
  定义体: by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

Depends on / 依赖: infer_instance, sigmaComparison_eq_comp_isos
-/
instance isIsoSigmaComparison : IsIso sigmaComparison X σ := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end CompHausLike
