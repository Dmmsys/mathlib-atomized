/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive category and `F` is an additive endofunctor on `C` then `Algebra F` is
also preadditive. Dually, the category `Coalgebra F` is also preadditive.
-/

public section


universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (F : C ⥤ C) [Functor.Additive (F : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive endofunctor on a preadditive category is preadditive.
-/
@[simps]
/--
Instance `Endofunctor.algebraPreadditive` / 实例 `Endofunctor.algebraPreadditive`

English:
instance Endofunctor.algebraPreadditive
  signature: : Preadditive (Endofunctor.Algebra F) where
  body: { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Endofunctor.Algebra.Hom.h, comp_add] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [comp_nsmul, Functor.map_nsmul, nsmul_comp, Endofunctor.Algebra.Hom.h] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Endofunctor.Algebra.Hom.h, comp_neg] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Endofunctor.Algebra.Hom.h, comp_sub] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [comp_zsmul, Functor.map_zsmul, zsmul_comp, Endofunctor.Algebra.Hom.h] }
add_assoc _ _ _ := Algebra.Hom.ext add_assoc _ _ _
zero_add _ := Algebra.Hom.ext zero_add _
add_zero _ := Algebra.Hom.ext add_zero _
nsmul_zero _ := Algebra.Hom.ext zero_nsmul _
nsmul_succ _ _ := Algebra.Hom.ext succ_nsmul _ _
sub_eq_add_neg _ _ := Algebra.Hom.ext sub_eq_add_neg _ _
zsmul_zero' _ := Algebra.Hom.ext zero_zsmul _
zsmul_succ' _ _ := Algebra.Hom.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := Algebra.Hom.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := Algebra.Hom.ext neg_add_cancel _
add_comm _ _ := Algebra.Hom.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := Algebra.Hom.ext add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := Algebra.Hom.ext comp_add _ _ _ _ _ _

中文:
实例 Endofunctor.algebraPreadditive
  签名: : 预加性 (Endofunctor.代数 F) where
  定义体: { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Endofunctor.Algebra.Hom.h, comp_add] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [comp_nsmul, Functor.map_nsmul, nsmul_comp, Endofunctor.Algebra.Hom.h] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Endofunctor.Algebra.Hom.h, comp_neg] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Endofunctor.Algebra.Hom.h, comp_sub] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [comp_zsmul, Functor.map_zsmul, zsmul_comp, Endofunctor.Algebra.Hom.h] }
add_assoc _ _ _ := Algebra.Hom.ext add_assoc _ _ _
zero_add _ := Algebra.Hom.ext zero_add _
add_zero _ := Algebra.Hom.ext add_zero _
nsmul_zero _ := Algebra.Hom.ext zero_nsmul _
nsmul_succ _ _ := Algebra.Hom.ext succ_nsmul _ _
sub_eq_add_neg _ _ := Algebra.Hom.ext sub_eq_add_neg _ _
zsmul_zero' _ := Algebra.Hom.ext zero_zsmul _
zsmul_succ' _ _ := Algebra.Hom.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := Algebra.Hom.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := Algebra.Hom.ext neg_add_cancel _
add_comm _ _ := Algebra.Hom.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := Algebra.Hom.ext add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := Algebra.Hom.ext comp_add _ _ _ _ _ _

Depends on / 依赖: Algebra, Endofunctor, Endofunctor.Alg, Endofunctor.Algebra.Hom.h, Functor, Functor.map_add, Functor.map_neg, Functor.map_nsmul, Functor.map_sub, Functor.map_zero, add_comp, comp_add, comp_neg, comp_nsmul, comp_zero, map_add, map_neg, map_nsmul, map_sub, map_zero
-/
instance Endofunctor.algebraPreadditive : Preadditive (Endofunctor.Algebra F) where
  homGroup A₁ A₂ :=
    { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Endofunctor.Algebra.Hom.h, comp_add] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [comp_nsmul, Functor.map_nsmul, nsmul_comp, Endofunctor.Algebra.Hom.h] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Endofunctor.Algebra.Hom.h, comp_neg] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Endofunctor.Algebra.Hom.h, comp_sub] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [comp_zsmul, Functor.map_zsmul, zsmul_comp, Endofunctor.Algebra.Hom.h] }
add_assoc _ _ _ := Algebra.Hom.ext add_assoc _ _ _
zero_add _ := Algebra.Hom.ext zero_add _
add_zero _ := Algebra.Hom.ext add_zero _
nsmul_zero _ := Algebra.Hom.ext zero_nsmul _
nsmul_succ _ _ := Algebra.Hom.ext succ_nsmul _ _
sub_eq_add_neg _ _ := Algebra.Hom.ext sub_eq_add_neg _ _
zsmul_zero' _ := Algebra.Hom.ext zero_zsmul _
zsmul_succ' _ _ := Algebra.Hom.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := Algebra.Hom.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := Algebra.Hom.ext neg_add_cancel _
add_comm _ _ := Algebra.Hom.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := Algebra.Hom.ext add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := Algebra.Hom.ext comp_add _ _ _ _ _ _

/--
Instance `Algebra.forget_additive` / 实例 `Algebra.forget_additive`

English:
instance Algebra.forget_additive
  signature: : (Endofunctor.Algebra.forget F).Additive where

中文:
实例 代数.forget_additive
  签名: : (Endofunctor.代数.forget F).加性 where
-/
instance Algebra.forget_additive : (Endofunctor.Algebra.forget F).Additive where

@[simps]
/--
Instance `Endofunctor.coalgebraPreadditive` / 实例 `Endofunctor.coalgebraPreadditive`

English:
instance Endofunctor.coalgebraPreadditive
  signature: : Preadditive (Endofunctor.Coalgebra F) where
  body: { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Endofunctor.Coalgebra.Hom.h, add_comp] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Endofunctor.Coalgebra.Hom.h, nsmul_comp] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Endofunctor.Coalgebra.Hom.h, neg_comp] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Endofunctor.Coalgebra.Hom.h, sub_comp] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Endofunctor.Coalgebra.Hom.h, zsmul_comp] }
add_assoc _ _ _ := Coalgebra.Hom.ext add_assoc _ _ _
zero_add _ := Coalgebra.Hom.ext zero_add _
add_zero _ := Coalgebra.Hom.ext add_zero _
nsmul_zero _ := Coalgebra.Hom.ext zero_nsmul _
nsmul_succ _ _ := Coalgebra.Hom.ext succ_nsmul _ _
sub_eq_add_neg _ _ := Coalgebra.Hom.ext sub_eq_add_neg _ _
zsmul_zero' _ := Coalgebra.Hom.ext zero_zsmul _
zsmul_succ' _ _ := Coalgebra.Hom.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := Coalgebra.Hom.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := Coalgebra.Hom.ext neg_add_cancel _
add_comm _ _ := Coalgebra.Hom.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := Coalgebra.Hom.ext add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := Coalgebra.Hom.ext comp_add _ _ _ _ _ _

中文:
实例 Endofunctor.coalgebraPreadditive
  签名: : 预加性 (Endofunctor.余algebra F) where
  定义体: { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Endofunctor.Coalgebra.Hom.h, add_comp] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Endofunctor.Coalgebra.Hom.h, nsmul_comp] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Endofunctor.Coalgebra.Hom.h, neg_comp] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Endofunctor.Coalgebra.Hom.h, sub_comp] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Endofunctor.Coalgebra.Hom.h, zsmul_comp] }
add_assoc _ _ _ := Coalgebra.Hom.ext add_assoc _ _ _
zero_add _ := Coalgebra.Hom.ext zero_add _
add_zero _ := Coalgebra.Hom.ext add_zero _
nsmul_zero _ := Coalgebra.Hom.ext zero_nsmul _
nsmul_succ _ _ := Coalgebra.Hom.ext succ_nsmul _ _
sub_eq_add_neg _ _ := Coalgebra.Hom.ext sub_eq_add_neg _ _
zsmul_zero' _ := Coalgebra.Hom.ext zero_zsmul _
zsmul_succ' _ _ := Coalgebra.Hom.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := Coalgebra.Hom.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := Coalgebra.Hom.ext neg_add_cancel _
add_comm _ _ := Coalgebra.Hom.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := Coalgebra.Hom.ext add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := Coalgebra.Hom.ext comp_add _ _ _ _ _ _

Depends on / 依赖: Coalgebra, Endofunct, Endofunctor, Endofunctor.Coalgebra.Hom.h, Functor, Functor.map_add, Functor.map_neg, Functor.map_nsmul, Functor.map_sub, Functor.map_zero, add_comp, comp_add, comp_neg, comp_nsmul, comp_sub, comp_zero, map_add, map_neg, map_nsmul, map_sub
-/
instance Endofunctor.coalgebraPreadditive : Preadditive (Endofunctor.Coalgebra F) where
  homGroup A₁ A₂ :=
    { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Endofunctor.Coalgebra.Hom.h, add_comp] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Endofunctor.Coalgebra.Hom.h, nsmul_comp] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Endofunctor.Coalgebra.Hom.h, neg_comp] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Endofunctor.Coalgebra.Hom.h, sub_comp] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Endofunctor.Coalgebra.Hom.h, zsmul_comp] }
add_assoc _ _ _ := Coalgebra.Hom.ext add_assoc _ _ _
zero_add _ := Coalgebra.Hom.ext zero_add _
add_zero _ := Coalgebra.Hom.ext add_zero _
nsmul_zero _ := Coalgebra.Hom.ext zero_nsmul _
nsmul_succ _ _ := Coalgebra.Hom.ext succ_nsmul _ _
sub_eq_add_neg _ _ := Coalgebra.Hom.ext sub_eq_add_neg _ _
zsmul_zero' _ := Coalgebra.Hom.ext zero_zsmul _
zsmul_succ' _ _ := Coalgebra.Hom.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := Coalgebra.Hom.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := Coalgebra.Hom.ext neg_add_cancel _
add_comm _ _ := Coalgebra.Hom.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := Coalgebra.Hom.ext add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := Coalgebra.Hom.ext comp_add _ _ _ _ _ _

/--
Instance `Coalgebra.forget_additive` / 实例 `Coalgebra.forget_additive`

English:
instance Coalgebra.forget_additive
  signature: : (Endofunctor.Coalgebra.forget F).Additive where

中文:
实例 余algebra.forget_additive
  签名: : (Endofunctor.余algebra.forget F).加性 where
-/
instance Coalgebra.forget_additive : (Endofunctor.Coalgebra.forget F).Additive where

end CategoryTheory
