/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!

# Yoneda presheaves on topologically concrete categories

This file develops some API for "topologically concrete" categories, defining universe polymorphic
"Yoneda presheaves" on such categories.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Opposite Limits

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w}) (Y : Type w') [TopologicalSpace Y]

namespace ContinuousMap

/--
A universe polymorphic "Yoneda presheaf" on `C` given by continuous maps into a topological space
`Y`.
-/
@[simps]
/--
Definition of `yonedaPresheaf` / `yonedaPresheaf` 的定义

English:
definition yonedaPresheaf
  signature: : Cᵒᵖ ⥤ Type (max w w') where
  body: C(F.obj (unop X), Y)
  map f := ↾fun g => ContinuousMap.comp g (F.map f.unop).hom

中文:
定义 yonedaPresheaf
  签名: : Cᵒᵖ ⥤ 类型 (最大值 w w') where
  定义体: C(F.obj (unop X), Y)
  map f := ↾fun g => ContinuousMap.comp g (F.map f.unop).hom

Depends on / 依赖: F.obj
-/
def yonedaPresheaf : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f := ↾fun g => ContinuousMap.comp g (F.map f.unop).hom

/--
A universe polymorphic Yoneda presheaf on `TopCat` given by continuous maps into a topological
space `Y`.
-/
@[simps]
/--
Definition of `yonedaPresheaf'` / `yonedaPresheaf'` 的定义

English:
definition yonedaPresheaf'
  signature: : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where
  body: C((unop X).1, Y)
  map f := ↾fun g => ContinuousMap.comp g
    (ConcreteCategory.hom f.unop)

中文:
定义 yonedaPresheaf'
  签名: : 顶元素范畴.{w}ᵒᵖ ⥤ 类型 (最大值 w w') where
  定义体: C((unop X).1, Y)
  map f := ↾fun g => ContinuousMap.comp g
    (ConcreteCategory.hom f.unop)
-/
def yonedaPresheaf' : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where
  obj X := C((unop X).1, Y)
  map f := ↾fun g => ContinuousMap.comp g
    (ConcreteCategory.hom f.unop)

/--
theorem `comp_yonedaPresheaf'` / 定理 `comp_yonedaPresheaf'`

English:
theorem comp_yonedaPresheaf'
  statement: yonedaPresheaf F Y = F.op ⋙ yonedaPresheaf' Y
  proof: rfl

中文:
定理 comp_yonedaPresheaf'
  结论: yonedaPresheaf F Y = F.op ⋙ yonedaPresheaf' Y
  证明: rfl
-/
theorem comp_yonedaPresheaf' : yonedaPresheaf F Y = F.op ⋙ yonedaPresheaf' Y := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `piComparison_fac` / 定理 `piComparison_fac`

English:
theorem piComparison_fac
  given: {α : Type} (X : α -> TopCat)
  proof: by
  rw [← Category.assoc]; rw [Iso.eq_comp_inv]
  ext
  simp [yonedaPresheaf', piComparison, ← opCoproductIsoProduct_inv_comp_ι]
  rfl

中文:
定理 piComparison_fac
  条件: {α : 类型} (X : α -> 顶元素范畴)
  证明: by
  rw [← Category.assoc]; rw [Iso.eq_comp_inv]
  ext
  simp [yonedaPresheaf', piComparison, ← opCoproductIsoProduct_inv_comp_ι]
  rfl

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, eq_comp_inv, piComparison, yonedaPresheaf
-/
theorem piComparison_fac {α : Type} (X : α -> TopCat) :
    piComparison (yonedaPresheaf'.{w, w'} Y) (fun x => op (X x)) =
    (yonedaPresheaf' Y).map ((opCoproductIsoProduct X).inv ≫ (TopCat.sigmaIsoSigma X).inv.op) ≫
    (equivEquivIso (sigmaEquiv Y (fun x => (X x).1))).inv ≫ (Types.productIso _).inv := by
  rw [← Category.assoc]; rw [Iso.eq_comp_inv]
  ext
  simp [yonedaPresheaf', piComparison, ← opCoproductIsoProduct_inv_comp_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteProducts (yonedaPresheaf'.{w, w'} Y)
  body: { preservesLimit := fun {K} =>
      have : forall {α : Type} (X : α -> TopCat), PreservesLimit (Discrete.functor (fun x => op (X x)))
          (yonedaPresheaf'.{w, w'} Y) := fun X => @PreservesProduct.of_iso_comparison _ _ _ _
          (yonedaPresheaf' Y) _ (fun x => op (X x)) _ _ (by rw [piComparison_fac]; infer_instance)
      let i : K ≅ Discrete.functor (fun i => op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      preservesLimit_of_iso_diagram _ i.symm }

中文:
实例 :
  签名: 保持FiniteProducts (yonedaPresheaf'.{w, w'} Y)
  定义体: { preservesLimit := fun {K} =>
      have : forall {α : Type} (X : α -> TopCat), PreservesLimit (Discrete.functor (fun x => op (X x)))
          (yonedaPresheaf'.{w, w'} Y) := fun X => @PreservesProduct.of_iso_comparison _ _ _ _
          (yonedaPresheaf' Y) _ (fun x => op (X x)) _ _ (by rw [piComparison_fac]; infer_instance)
      let i : K ≅ Discrete.functor (fun i => op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      preservesLimit_of_iso_diagram _ i.symm }

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIsoFunctor, K.obj, PreservesLimit, PreservesProduct, PreservesProduct.of_iso_comparison, TopCat, functor, i.symm, infer_instance, natIsoFunctor, of_iso_comparison, piComparison_fac, preservesLimit, preservesLimit_of_iso_diagram, yonedaPresheaf
-/
noncomputable instance : PreservesFiniteProducts (yonedaPresheaf'.{w, w'} Y) where
  preserves _ :=
    { preservesLimit := fun {K} =>
      have : forall {α : Type} (X : α -> TopCat), PreservesLimit (Discrete.functor (fun x => op (X x)))
          (yonedaPresheaf'.{w, w'} Y) := fun X => @PreservesProduct.of_iso_comparison _ _ _ _
          (yonedaPresheaf' Y) _ (fun x => op (X x)) _ _ (by rw [piComparison_fac]; infer_instance)
      let i : K ≅ Discrete.functor (fun i => op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      preservesLimit_of_iso_diagram _ i.symm }

end ContinuousMap
