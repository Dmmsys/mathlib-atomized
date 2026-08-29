/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.WithConv
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Convolution product on linear maps from a coalgebra to an algebra

This file constructs the ring and algebra structure on linear maps `C → A` where `C` is a
coalgebra and `A` an algebra, where multiplication is given by
`(f * g)(x) = ∑ f x₍₁₎ * g x₍₂₎` in Sweedler notation or
```
         |
         μ
| | / \
f * g = f g
| | \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.

## Implementation notes

Because there is a global multiplication instance on `Module.End R A` (defined as composition),
which is mathematically distinct from this product, we provide this instance on
`WithConv (C →ₗ[R] A)`.
-/

@[expose] public section

suppress_compilation

open Coalgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R S A B C ι : Type*} [CommSemiring R]

namespace LinearMap
section NonUnitalNonAssocSemiring
variable
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/--
Instance `convMul` / 实例 `convMul`

English:
instance convMul
  signature: : Mul (WithConv (C ->ₗ[R] A)) where
  body: toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul)

中文:
实例 convMul
  签名: : 乘法 (WithConv (C ->ₗ[R] A)) where
  定义体: toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul)

Depends on / 依赖: f.ofConv, g.ofConv, ofConv, toConv
-/
instance convMul : Mul (WithConv (C ->ₗ[R] A)) where
  mul f g := toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul)

/--
lemma `convMul_def` / 引理 `convMul_def`

English:
lemma convMul_def
  given: (f g : WithConv (C ->ₗ[R] A))
  proof: rfl

@[simp]

中文:
引理 convMul_def
  条件: (f g : WithConv (C ->ₗ[R] A))
  证明: rfl

@[simp]
-/
lemma convMul_def (f g : WithConv (C ->ₗ[R] A)) :
    f * g = toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul) := rfl

@[simp]
/--
lemma `convMul_apply` / 引理 `convMul_apply`

English:
lemma convMul_apply
  given: (f g : WithConv (C ->ₗ[R] A)) (c : C)
  proof: rfl

中文:
引理 convMul_apply
  条件: (f g : WithConv (C ->ₗ[R] A)) (c : C)
  证明: rfl
-/
lemma convMul_apply (f g : WithConv (C ->ₗ[R] A)) (c : C) :
    (f * g) c = mul' R A (.map f.ofConv g.ofConv (comul c)) := rfl

/--
lemma `_root_.Coalgebra.Repr.convMul_apply` / 引理 `_root_.Coalgebra.Repr.convMul_apply`

English:
lemma _root_.Coalgebra.Repr.convMul_apply
  statement: {a : C} (𝓡 : Coalgebra.Repr R a ι)
  proof: by
  simp [convMul_def, ← 𝓡.eq]

中文:
引理 _root_.余algebra.Repr.convMul_apply
  结论: {a : C} (𝓡 : 余algebra.Repr R a ι)
  证明: by
  simp [convMul_def, ← 𝓡.eq]

Depends on / 依赖: convMul_def
-/
lemma _root_.Coalgebra.Repr.convMul_apply {a : C} (𝓡 : Coalgebra.Repr R a ι)
    (f g : WithConv (C ->ₗ[R] A)) : (f * g) a = ∑ i in 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [convMul_def, ← 𝓡.eq]

/--
Instance `convNonUnitalNonAssocSemiring` / 实例 `convNonUnitalNonAssocSemiring`

English:
instance convNonUnitalNonAssocSemiring
  signature: : NonUnitalNonAssocSemiring (WithConv (C ->ₗ[R] A)) where
  body: by ext; simp [map_add_right]
  right_distrib f g h := by ext; simp [map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp

中文:
实例 convNonUnitalNonAssocSemiring
  签名: : 非幺非结合半环 (WithConv (C ->ₗ[R] A)) where
  定义体: by ext; simp [map_add_right]
  right_distrib f g h := by ext; simp [map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp

Depends on / 依赖: map_add_left, map_add_right, mul_zero, right_distrib, zero_mul
-/
instance convNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (WithConv (C ->ₗ[R] A)) where
  left_distrib f g h := by ext; simp [map_add_right]
  right_distrib f g h := by ext; simp [map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [DistribMulAction S A] [SMulCommClass R S A] [IsScalarTower S A A] :
  body: by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, smul_mul_assoc]

中文:
实例 [幺半群
  签名: S] [分配乘法作用 S A] [标量交换类 R S A] [标量塔 S A A] :
  定义体: by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, smul_mul_assoc]

Depends on / 依赖: Finset, Finset.smul_sum, convMul_apply, smul_mul_assoc, smul_sum
-/
instance [Monoid S] [DistribMulAction S A] [SMulCommClass R S A] [IsScalarTower S A A] :
    IsScalarTower S (WithConv (C ->ₗ[R] A)) (WithConv (C ->ₗ[R] A)) where
  smul_assoc s f g := by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, smul_mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [DistribMulAction S A] [SMulCommClass R S A] [SMulCommClass S A A] :
  body: by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, mul_smul_comm]

中文:
实例 [幺半群
  签名: S] [分配乘法作用 S A] [标量交换类 R S A] [标量交换类 S A A] :
  定义体: by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, mul_smul_comm]

Depends on / 依赖: Finset, Finset.smul_sum, convMul_apply, mul_smul_comm, smul_sum
-/
instance [Monoid S] [DistribMulAction S A] [SMulCommClass R S A] [SMulCommClass S A A] :
    SMulCommClass S (WithConv (C ->ₗ[R] A)) (WithConv (C ->ₗ[R] A)) where
  smul_comm s f g := by ext c; simp [(ℛ R c).convMul_apply, Finset.smul_sum, mul_smul_comm]

/--
lemma `toSpanSingleton_convMul_toSpanSingleton` / 引理 `toSpanSingleton_convMul_toSpanSingleton`

English:
lemma toSpanSingleton_convMul_toSpanSingleton
  given: (x y : A)
  proof: by ext; simp

中文:
引理 toSpanSingleton_convMul_toSpanSingleton
  条件: (x y : A)
  证明: by ext; simp
-/
@[simp] lemma toSpanSingleton_convMul_toSpanSingleton (x y : A) :
    toConv (toSpanSingleton R A x) * toConv (toSpanSingleton R A y) =
      toConv (toSpanSingleton R A (x * y)) := by ext; simp

/--
theorem `_root_.TensorProduct.map_convMul_map` / 定理 `_root_.TensorProduct.map_convMul_map`

English:
theorem _root_.TensorProduct.map_convMul_map
  statement: {D : Type*} [AddCommMonoid B] [Module R B]
  proof: by
  simp_rw [convMul_def, comul_def, mul'_tensor, comp_assoc, AlgebraTensorModule.map_eq,
    ← comp_assoc _ _ (tensorTensorTensorComm R _ _ _ _).toLinearMap]
  nth_rw 2 [← comp_assoc, comp_assoc]
  simp [AlgebraTensorModule.tensorTensorTensorComm_eq, ← tensorTensorTensorComm_comp_map,
    ← comp_assoc, map_comp]

中文:
定理 _root_.张量积.map_convMul_map
  结论: {D : 类型} [加法交换幺半群 B] [模 R B]
  证明: by
  simp_rw [convMul_def, comul_def, mul'_tensor, comp_assoc, AlgebraTensorModule.map_eq,
    ← comp_assoc _ _ (tensorTensorTensorComm R _ _ _ _).toLinearMap]
  nth_rw 2 [← comp_assoc, comp_assoc]
  simp [AlgebraTensorModule.tensorTensorTensorComm_eq, ← tensorTensorTensorComm_comp_map,
    ← comp_assoc, map_comp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map_eq, AlgebraTensorModule.tensorTensorTensorComm_eq, _tensor, comp_assoc, comul_def, convMul_def, map_comp, map_eq, nth_rw, simp_rw, tensorTensorTensorComm, tensorTensorTensorComm_comp_map, tensorTensorTensorComm_eq, toLinearMap
-/
theorem _root_.TensorProduct.map_convMul_map {D : Type*} [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R B] [NonUnitalNonAssocSemiring D] [Module R D] [SMulCommClass R D D]
    [IsScalarTower R D D] {f h : WithConv (C ->ₗ[R] A)} {g k : WithConv (B ->ₗ[R] D)} :
    toConv (f.ofConv otimesₘ g.ofConv) * toConv (h.ofConv otimesₘ k.ofConv) =
      toConv ((f * h).ofConv otimesₘ (g * k).ofConv) := by
  simp_rw [convMul_def, comul_def, mul'_tensor, comp_assoc, AlgebraTensorModule.map_eq,
    ← comp_assoc _ _ (tensorTensorTensorComm R _ _ _ _).toLinearMap]
  nth_rw 2 [← comp_assoc, comp_assoc]
  simp [AlgebraTensorModule.tensorTensorTensorComm_eq, ← tensorTensorTensorComm_comp_map,
    ← comp_assoc, map_comp]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/--
Instance `convNonUnitalNonAssocRing` / 实例 `convNonUnitalNonAssocRing`

English:
instance convNonUnitalNonAssocRing
  signature: : NonUnitalNonAssocRing (WithConv (C ->ₗ[R] A)) where

中文:
实例 convNonUnitalNonAssocRing
  签名: : 非幺非结合环 (WithConv (C ->ₗ[R] A)) where
-/
instance convNonUnitalNonAssocRing : NonUnitalNonAssocRing (WithConv (C ->ₗ[R] A)) where

end NonUnitalNonAssocRing

section NonUnitalSemiring
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

/--
lemma `nonUnitalAlgHom_comp_convMul_distrib` / 引理 `nonUnitalAlgHom_comp_convMul_distrib`

English:
lemma nonUnitalAlgHom_comp_convMul_distrib
  proof: by
  simp [convMul_def, map_comp, ← comp_assoc, NonUnitalAlgHom.comp_mul']

中文:
引理 nonUnitalAlgHom_comp_convMul_distrib
  证明: by
  simp [convMul_def, map_comp, ← comp_assoc, NonUnitalAlgHom.comp_mul']

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.comp_mul, comp_assoc, comp_mul, convMul_def, map_comp
-/
lemma nonUnitalAlgHom_comp_convMul_distrib
    [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    (h : A ->ₙₐ[R] B) (f g : WithConv (C ->ₗ[R] A)) :
    (h : A ->ₗ[R] B).comp (f * g).ofConv =
      (toConv ((h : A ->ₗ[R] B).comp f.ofConv) * toConv ((h : A ->ₗ[R] B).comp g.ofConv)).ofConv := by
  simp [convMul_def, map_comp, ← comp_assoc, NonUnitalAlgHom.comp_mul']

/--
lemma `convMul_comp_coalgHom_distrib` / 引理 `convMul_comp_coalgHom_distrib`

English:
lemma convMul_comp_coalgHom_distrib
  statement: [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]
  proof: by
  simp [convMul_def, map_comp, comp_assoc]

中文:
引理 convMul_comp_coalgHom_distrib
  结论: [加法交换幺半群 B] [模 R B] [余algebraStruct R B]
  证明: by
  simp [convMul_def, map_comp, comp_assoc]

Depends on / 依赖: comp_assoc, convMul_def, map_comp
-/
lemma convMul_comp_coalgHom_distrib [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]
    (f g : WithConv (C ->ₗ[R] A)) (h : B ->ₗc[R] C) :
    (f * g).ofConv.comp h.toLinearMap =
      (toConv (f.ofConv.comp h.toLinearMap) * toConv (g.ofConv.comp h.toLinearMap)).ofConv := by
  simp [convMul_def, map_comp, comp_assoc]

/--
Instance `convNonUnitalSemiring` / 实例 `convNonUnitalSemiring`

English:
instance convNonUnitalSemiring
  signature: : NonUnitalSemiring (WithConv (C ->ₗ[R] A)) where
  body: toConv_injective.eq_iff.mpr calc
    _ = (μ ∘ₗ rTensor _ μ) ∘ₗ (((f.ofConv otimesₘ g.ofConv) otimesₘ h.ofConv) ∘ₗ
        (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ := by
      ext; simp [comp_assoc, coassoc_symm, convMul_def]
    _ = (μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm) ∘ₗ
        (f.ofConv otimesₘ (g.ofConv otimesₘ h.ofConv)) ∘ₗ lTensor C δ ∘ₗ δ := by
      simp only [map_map_comp_assoc_symm_eq, comp_assoc]
    _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f.ofConv otimesₘ (g.ofConv otimesₘ h.ofConv)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
      congr 1
      ext
      simp [mul_assoc]
    _ = μ ∘ₗ (f.ofConv otimesₘ μ ∘ₗ (g.ofConv otimesₘ h.ofConv) ∘ₗ δ) ∘ₗ δ := by ext; simp

中文:
实例 convNonUnitalSemiring
  签名: : 非幺半环 (WithConv (C ->ₗ[R] A)) where
  定义体: toConv_injective.eq_iff.mpr calc
    _ = (μ ∘ₗ rTensor _ μ) ∘ₗ (((f.ofConv otimesₘ g.ofConv) otimesₘ h.ofConv) ∘ₗ
        (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ := by
      ext; simp [comp_assoc, coassoc_symm, convMul_def]
    _ = (μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm) ∘ₗ
        (f.ofConv otimesₘ (g.ofConv otimesₘ h.ofConv)) ∘ₗ lTensor C δ ∘ₗ δ := by
      simp only [map_map_comp_assoc_symm_eq, comp_assoc]
    _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f.ofConv otimesₘ (g.ofConv otimesₘ h.ofConv)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
      congr 1
      ext
      simp [mul_assoc]
    _ = μ ∘ₗ (f.ofConv otimesₘ μ ∘ₗ (g.ofConv otimesₘ h.ofConv) ∘ₗ δ) ∘ₗ δ := by ext; simp

Depends on / 依赖: eq_iff, toConv_injective, toConv_injective.eq_iff.mpr
-/
instance convNonUnitalSemiring : NonUnitalSemiring (WithConv (C ->ₗ[R] A)) where
mul_assoc f g h := toConv_injective.eq_iff.mpr calc
    _ = (μ ∘ₗ rTensor _ μ) ∘ₗ (((f.ofConv otimesₘ g.ofConv) otimesₘ h.ofConv) ∘ₗ
        (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ := by
      ext; simp [comp_assoc, coassoc_symm, convMul_def]
    _ = (μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm) ∘ₗ
        (f.ofConv otimesₘ (g.ofConv otimesₘ h.ofConv)) ∘ₗ lTensor C δ ∘ₗ δ := by
      simp only [map_map_comp_assoc_symm_eq, comp_assoc]
    _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f.ofConv otimesₘ (g.ofConv otimesₘ h.ofConv)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
      congr 1
      ext
      simp [mul_assoc]
    _ = μ ∘ₗ (f.ofConv otimesₘ μ ∘ₗ (g.ofConv otimesₘ h.ofConv) ∘ₗ δ) ∘ₗ δ := by ext; simp

end NonUnitalSemiring

section NonUnitalRing
variable [NonUnitalRing A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [Coalgebra R C]

/--
Instance `convNonUnitalRing` / 实例 `convNonUnitalRing`

English:
instance convNonUnitalRing
  signature: : NonUnitalRing (WithConv (C ->ₗ[R] A)) where

中文:
实例 convNonUnitalRing
  签名: : 非幺环 (WithConv (C ->ₗ[R] A)) where
-/
instance convNonUnitalRing : NonUnitalRing (WithConv (C ->ₗ[R] A)) where

end NonUnitalRing

section Semiring
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [AddCommMonoid C] [Module R C]

section CoalgebraStruct
variable [CoalgebraStruct R C]

/--
lemma `algHom_comp_convMul_distrib` / 引理 `algHom_comp_convMul_distrib`

English:
lemma algHom_comp_convMul_distrib
  given: (h : A ->ₐ B) (f g : WithConv (C ->ₗ[R] A))
  proof: by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

中文:
引理 algHom_comp_convMul_distrib
  条件: (h : A ->ₐ B) (f g : WithConv (C ->ₗ[R] A))
  证明: by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

Depends on / 依赖: AlgHom, AlgHom.comp_mul, comp_assoc, comp_mul, convMul_def, map_comp
-/
lemma algHom_comp_convMul_distrib (h : A ->ₐ B) (f g : WithConv (C ->ₗ[R] A)) :
    h.toLinearMap.comp (f * g).ofConv =
      (toConv (h.toLinearMap.comp f.ofConv) * toConv (h.toLinearMap.comp g.ofConv)).ofConv := by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

end CoalgebraStruct

variable [Coalgebra R C]

/--
Instance `convOne` / 实例 `convOne`

English:
instance convOne
  signature: : One (WithConv (C ->ₗ[R] A)) where one
  body: toConv (Algebra.linearMap R A ∘ₗ counit)

中文:
实例 convOne
  签名: : 幺 (WithConv (C ->ₗ[R] A)) where one
  定义体: toConv (Algebra.linearMap R A ∘ₗ counit)

Depends on / 依赖: Algebra, Algebra.linearMap, counit, linearMap, toConv
-/
instance convOne : One (WithConv (C ->ₗ[R] A)) where one := toConv (Algebra.linearMap R A ∘ₗ counit)

/--
lemma `convOne_def` / 引理 `convOne_def`

English:
lemma convOne_def
  statement: (1 : WithConv (C ->ₗ[R] A)) = toConv (Algebra.linearMap R A ∘ₗ counit)
  proof: rfl

中文:
引理 convOne_def
  结论: (1 : WithConv (C ->ₗ[R] A)) = toConv (代数.linearMap R A ∘ₗ counit)
  证明: rfl
-/
lemma convOne_def : (1 : WithConv (C ->ₗ[R] A)) = toConv (Algebra.linearMap R A ∘ₗ counit) := rfl

/--
lemma `convOne_apply` / 引理 `convOne_apply`

English:
lemma convOne_apply
  given: (c : C)
  proof: rfl

中文:
引理 convOne_apply
  条件: (c : C)
  证明: rfl
-/
@[simp] lemma convOne_apply (c : C) :
    (1 : WithConv (C ->ₗ[R] A)) c = algebraMap R A (counit (R := R) c) := rfl

/--
Instance `convSemiring` / 实例 `convSemiring`

English:
instance convSemiring
  signature: : Semiring (WithConv (C ->ₗ[R] A)) where
  body: by ext; simp [convOne_def, ← map_comp_rTensor]
  mul_one f := by ext; simp [convOne_def, ← map_comp_lTensor]

中文:
实例 convSemiring
  签名: : 半环 (WithConv (C ->ₗ[R] A)) where
  定义体: by ext; simp [convOne_def, ← map_comp_rTensor]
  mul_one f := by ext; simp [convOne_def, ← map_comp_lTensor]

Depends on / 依赖: convOne_def, map_comp_lTensor, map_comp_rTensor, mul_one
-/
instance convSemiring : Semiring (WithConv (C ->ₗ[R] A)) where
  one_mul f := by ext; simp [convOne_def, ← map_comp_rTensor]
  mul_one f := by ext; simp [convOne_def, ← map_comp_lTensor]

/--
Instance `convAlgebra` / 实例 `convAlgebra`

English:
instance convAlgebra
  signature: [CommSemiring S] [Algebra S A] [SMulCommClass R S A]
  body: .ofModule smul_mul_assoc mul_smul_comm

@[simp]

中文:
实例 convAlgebra
  签名: [交换半环 S] [代数 S A] [标量交换类 R S A]
  定义体: .ofModule smul_mul_assoc mul_smul_comm

@[simp]

Depends on / 依赖: mul_smul_comm, ofModule, smul_mul_assoc
-/
instance convAlgebra [CommSemiring S] [Algebra S A] [SMulCommClass R S A] :
    Algebra S (WithConv (C ->ₗ[R] A)) :=
  .ofModule smul_mul_assoc mul_smul_comm

@[simp]
/--
lemma `convAlgebraMap_apply` / 引理 `convAlgebraMap_apply`

English:
lemma convAlgebraMap_apply
  given: [CommSemiring S] [Algebra S A] [SMulCommClass R S A] (s : S) (c : C)
  proof: rfl

中文:
引理 convAlgebraMap_apply
  条件: [交换半环 S] [代数 S A] [标量交换类 R S A] (s : S) (c : C)
  证明: rfl
-/
lemma convAlgebraMap_apply [CommSemiring S] [Algebra S A] [SMulCommClass R S A] (s : S) (c : C) :
    algebraMap S (WithConv (C ->ₗ[R] A)) s c = s • algebraMap R A (counit c) := rfl

end Semiring

section CommSemiring
variable [CommSemiring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

/--
Instance `convCommSemiring` / 实例 `convCommSemiring`

English:
instance convCommSemiring
  signature: : CommSemiring (WithConv (C ->ₗ[R] A)) where
  body: by ext x; rw [convMul_apply, ← comm_comul R x, map_comm, mul'_comm, convMul_apply]

中文:
实例 convCommSemiring
  签名: : 交换半环 (WithConv (C ->ₗ[R] A)) where
  定义体: by ext x; rw [convMul_apply, ← comm_comul R x, map_comm, mul'_comm, convMul_apply]

Depends on / 依赖: _comm, comm_comul, convMul_apply, map_comm
-/
instance convCommSemiring : CommSemiring (WithConv (C ->ₗ[R] A)) where
  mul_comm f g := by ext x; rw [convMul_apply, ← comm_comul R x, map_comm, mul'_comm, convMul_apply]

end CommSemiring

section Ring
variable [Ring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]

/--
Instance `convRing` / 实例 `convRing`

English:
instance convRing
  signature: : Ring (WithConv (C ->ₗ[R] A)) where

中文:
实例 convRing
  签名: : 环 (WithConv (C ->ₗ[R] A)) where
-/
instance convRing : Ring (WithConv (C ->ₗ[R] A)) where

end Ring

section CommRing
variable [CommRing A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C] [IsCocomm R C]

/--
Instance `convCommRing` / 实例 `convCommRing`

English:
instance convCommRing
  signature: : CommRing (WithConv (C ->ₗ[R] A)) where

中文:
实例 convCommRing
  签名: : 交换环 (WithConv (C ->ₗ[R] A)) where
-/
instance convCommRing : CommRing (WithConv (C ->ₗ[R] A)) where

end CommRing
end LinearMap
