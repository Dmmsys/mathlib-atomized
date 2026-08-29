/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.Central.End
public import Mathlib.Algebra.Central.TensorProduct
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Basic properties of Azumaya algebras

In this file we prove basic facts about Azumaya algebras such as `R` is an Azumaya algebra
over itself where `R` is a commutative ring.

## Main Results

- `IsAzumaya.id`: `R` is an Azumaya algebra over itself.

- `IsAzumaya.ofAlgEquiv`: If `A` is an Azumaya algebra over `R` and `A` is isomorphic to `B`
  as an `R`-algebra, then `B` is an Azumaya algebra over `R`.

## Tags
Noncommutative algebra, Azumaya algebra, Brauer Group

-/

public section

open scoped TensorProduct

open MulOpposite

namespace IsAzumaya

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/--
lemma `AlgHom.mulLeftRight_bij` / 引理 `AlgHom.mulLeftRight_bij`

English:
lemma AlgHom.mulLeftRight_bij
  given: [h : IsAzumaya R A]
  proof: h.bij

中文:
引理 AlgHom.mulLeftRight_bij
  条件: [h : IsAzumaya R A]
  证明: h.bij

Depends on / 依赖: h.bij
-/
lemma AlgHom.mulLeftRight_bij [h : IsAzumaya R A] :
    Function.Bijective (AlgHom.mulLeftRight R A) := h.bij

/--
Definition of `tensorEquivEnd` / `tensorEquivEnd` 的定义

English:
abbreviation tensorEquivEnd
  signature: : R otimes[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R
  body: .trans .moduleEndSelf R Algebra.TensorProduct.lid R Rᵐᵒᵖ

中文:
缩写 tensorEquivEnd
  签名: : R otimes[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R
  定义体: .trans .moduleEndSelf R Algebra.TensorProduct.lid R Rᵐᵒᵖ

Depends on / 依赖: Algebra, Algebra.TensorProduct.lid, TensorProduct, moduleEndSelf
-/
abbrev tensorEquivEnd : R otimes[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
.trans .moduleEndSelf R Algebra.TensorProduct.lid R Rᵐᵒᵖ

/--
lemma `coe_tensorEquivEnd` / 引理 `coe_tensorEquivEnd`

English:
lemma coe_tensorEquivEnd
  statement: tensorEquivEnd R = AlgHom.mulLeftRight R R
  proof: by
  ext; simp

中文:
引理 coe_tensorEquivEnd
  结论: tensorEquivEnd R = AlgHom.mulLeftRight R R
  证明: by
  ext; simp
-/
lemma coe_tensorEquivEnd : tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext; simp

/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : IsAzumaya R R where
  body: by rw [← coe_tensorEquivEnd]; exact tensorEquivEnd R

中文:
实例 id
  签名: : IsAzumaya R R where
  定义体: by rw [← coe_tensorEquivEnd]; exact tensorEquivEnd R

Depends on / 依赖: coe_tensorEquivEnd, tensorEquivEnd
-/
instance id : IsAzumaya R R where
.bijective bij := by rw [← coe_tensorEquivEnd]; exact tensorEquivEnd R

/--
lemma `mulLeftRight_comp_congr` / 引理 `mulLeftRight_comp_congr`

English:
lemma mulLeftRight_comp_congr
  given: (e : A ≃ₐ[R] B)
  proof: by
  ext <;> simp

中文:
引理 mulLeftRight_comp_congr
  条件: (e : A ≃ₐ[R] B)
  证明: by
  ext <;> simp
-/
lemma mulLeftRight_comp_congr (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.conjAlgEquiv R).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  ext <;> simp

/--
theorem `of_AlgEquiv` / 定理 `of_AlgEquiv`

English:
theorem of_AlgEquiv
  given: (e : A ≃ₐ[R] B) [IsAzumaya R A]
  statement: IsAzumaya R B
  proof: let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
.1 by (Algebra.TensorProduct.congr e e.op).bijective
    rw [← AlgEqu

中文:
定理 of_AlgEquiv
  条件: (e : A ≃ₐ[R] B) [IsAzumaya R A]
  结论: IsAzumaya R B
  证明: let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
.1 by (Algebra.TensorProduct.congr e e.op).bijective
    rw [← AlgEqu

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.coe_comp, AlgHom.mulLeftRight, AlgHom.mulLeftRight_bij, Algebra, Algebra.TensorProduct.congr, Bijective, FaithfulSMul, Finite, Function, Function.Bijective.of_comp_iff, Module, Module.Finite, Module.Projective, Projective, TensorProduct, bijective, coe_comp
-/
theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
.1 by (Algebra.TensorProduct.congr e e.op).bijective
    rw [← AlgEquiv.coe_toAlgHom]; rw [← AlgHom.coe_comp]; rw [mulLeftRight_comp_congr]
    simp [AlgHom.mulLeftRight_bij]⟩

end IsAzumaya

/--
Instance `Algebra.IsCentral.instIsAzumaya` / 实例 `Algebra.IsCentral.instIsAzumaya`

English:
instance Algebra.IsCentral.instIsAzumaya
  signature: {R A : Type*} [CommSemiring R] [Semiring A]
  body: have := of_algEquiv R _ _ (AlgEquiv.ofBijective (.mulLeftRight R A) IsAzumaya.bij).symm
left_of_tensor R A Aᵐᵒᵖ FaithfulSMul.algebraMap_injective _ _

中文:
实例 Algebra.IsCentral.instIsAzumaya
  签名: {R A : 类型} [CommSemiring R] [Semiring A]
  定义体: have := of_algEquiv R _ _ (AlgEquiv.ofBijective (.mulLeftRight R A) IsAzumaya.bij).symm
left_of_tensor R A Aᵐᵒᵖ FaithfulSMul.algebraMap_injective _ _

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsAzumaya, IsAzumaya.bij, algebraMap_injective, left_of_tensor, mulLeftRight, ofBijective, of_algEquiv
-/
instance Algebra.IsCentral.instIsAzumaya {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Module.Free R A] [IsAzumaya R A] : IsCentral R A :=
  have := of_algEquiv R _ _ (AlgEquiv.ofBijective (.mulLeftRight R A) IsAzumaya.bij).symm
left_of_tensor R A Aᵐᵒᵖ FaithfulSMul.algebraMap_injective _ _
