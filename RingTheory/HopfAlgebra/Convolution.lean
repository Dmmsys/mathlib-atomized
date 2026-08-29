/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
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
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace HopfAlgebra
section Semiring
variable [Semiring A] [HopfAlgebra R A]

/--
lemma `antipode_comp_mul_comp_comm` / 引理 `antipode_comp_mul_comp_comm`

English:
lemma antipode_comp_mul_comp_comm
  proof: by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A) <;>
    ext a b
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R b).mul (ℛ R a)),
      ← Finset.map_swap_product (ℛ R b).index (ℛ R a).index]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply,
      ← Finset.map_swap_product (ℛ R a).index (ℛ R b).index,
      Finset.sum_product (ℛ R b).index, ← Finset.mul_sum, mul_assoc ((ℛ R b).left _),
      ← mul_assoc ((ℛ R a).left _), ← Finset.sum_mul, sum_mul_antipode_eq_algebraMap_counit,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).left_comm,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).eq]

中文:
引理 antipode_comp_mul_comp_comm
  证明: by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A) <;>
    ext a b
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R b).mul (ℛ R a)),
      ← Finset.map_swap_product (ℛ R b).index (ℛ R a).index]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply,
      ← Finset.map_swap_product (ℛ R a).index (ℛ R b).index,
      Finset.sum_product (ℛ R b).index, ← Finset.mul_sum, mul_assoc ((ℛ R b).left _),
      ← mul_assoc ((ℛ R a).left _), ← Finset.sum_mul, sum_mul_antipode_eq_algebraMap_counit,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).left_comm,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).eq]

Depends on / 依赖: Bialgebra, Bialgebra.counit_mul, Finset, Finset.map_swap_product, Finset.mul_sum, Finset.sum_product, LinearMap, LinearMap.mul, TensorProduct, TensorProduct.comm, WithConv, WithConv.toConv_injective, convMul_apply, counit_mul, left_inv_eq_right_inv, map_swap_product, mul_assoc, mul_sum, sum_antipode_mul_eq_algebraMap_counit, sum_product
-/
lemma antipode_comp_mul_comp_comm :
    antipode R ∘ₗ .mul' R A ∘ₗ (TensorProduct.comm R A A).toLinearMap =
      .mul' R A ∘ₗ map (antipode R) (antipode R) := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A) <;>
    ext a b
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R b).mul (ℛ R a)),
      ← Finset.map_swap_product (ℛ R b).index (ℛ R a).index]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply,
      ← Finset.map_swap_product (ℛ R a).index (ℛ R b).index,
      Finset.sum_product (ℛ R b).index, ← Finset.mul_sum, mul_assoc ((ℛ R b).left _),
      ← mul_assoc ((ℛ R a).left _), ← Finset.sum_mul, sum_mul_antipode_eq_algebraMap_counit,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).left_comm,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).eq]

/--
lemma `antipode_mul_antidistrib` / 引理 `antipode_mul_antidistrib`

English:
lemma antipode_mul_antidistrib
  given: (a b : A)
  statement: antipode R (a * b) = antipode R b * antipode R a
  proof: by
  exact congr($antipode_comp_mul_comp_comm (b otimesₜ a))

@[deprecated (since := "2026-06-05")] alias antipode_mul := antipode_mul_antidistrib

中文:
引理 antipode_mul_antidistrib
  条件: (a b : A)
  结论: antipode R (a * b) = antipode R b * antipode R a
  证明: by
  exact congr($antipode_comp_mul_comp_comm (b otimesₜ a))

@[deprecated (since := "2026-06-05")] alias antipode_mul := antipode_mul_antidistrib

Depends on / 依赖: antipode_comp_mul_comp_comm
-/
lemma antipode_mul_antidistrib (a b : A) : antipode R (a * b) = antipode R b * antipode R a := by
  exact congr($antipode_comp_mul_comp_comm (b otimesₜ a))

@[deprecated (since := "2026-06-05")] alias antipode_mul := antipode_mul_antidistrib

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an anti-algebra hom. -/
@[expose, simps!]
/--
Definition of `antipodeAlgHomOp` / `antipodeAlgHomOp` 的定义

English:
definition antipodeAlgHomOp
  signature: : A ->ₐ[R] Aᵐᵒᵖ
  body: .ofLinearMap
    ((MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ antipode R)
    (MulOpposite.op_injective (by simp))
    (fun x y => MulOpposite.op_injective (by simp [antipode_mul_antidistrib]))

中文:
定义 antipodeAlgHomOp
  签名: : A ->ₐ[R] Aᵐᵒᵖ
  定义体: .ofLinearMap
    ((MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ antipode R)
    (MulOpposite.op_injective (by simp))
    (fun x y => MulOpposite.op_injective (by simp [antipode_mul_antidistrib]))

Depends on / 依赖: ofLinearMap
-/
def antipodeAlgHomOp : A ->ₐ[R] Aᵐᵒᵖ := .ofLinearMap
    ((MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ antipode R)
    (MulOpposite.op_injective (by simp))
    (fun x y => MulOpposite.op_injective (by simp [antipode_mul_antidistrib]))

end Semiring

variable [CommSemiring A] [HopfAlgebra R A]

/--
lemma `antipode_mul_distrib` / 引理 `antipode_mul_distrib`

English:
lemma antipode_mul_distrib
  given: (a b : A)
  statement: antipode R (a * b) = antipode R a * antipode R b
  proof: by
  rw [antipode_mul_antidistrib]; rw [mul_comm]

中文:
引理 antipode_mul_distrib
  条件: (a b : A)
  结论: antipode R (a * b) = antipode R a * antipode R b
  证明: by
  rw [antipode_mul_antidistrib]; rw [mul_comm]

Depends on / 依赖: antipode_mul_antidistrib, mul_comm
-/
lemma antipode_mul_distrib (a b : A) : antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib]; rw [mul_comm]

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an algebra hom. -/
@[expose, simps!]
/--
Definition of `antipodeAlgHom` / `antipodeAlgHom` 的定义

English:
definition antipodeAlgHom
  signature: : A ->ₐ[R] A
  body: .ofLinearMap (antipode R) antipode_one antipode_mul_distrib

中文:
定义 antipodeAlgHom
  签名: : A ->ₐ[R] A
  定义体: .ofLinearMap (antipode R) antipode_one antipode_mul_distrib

Depends on / 依赖: antipode, antipode_mul_distrib, antipode_one, ofLinearMap
-/
def antipodeAlgHom : A ->ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul_distrib

/--
lemma `toLinearMap_antipodeAlgHom` / 引理 `toLinearMap_antipodeAlgHom`

English:
lemma toLinearMap_antipodeAlgHom
  statement: (antipodeAlgHom R A).toLinearMap = antipode R
  proof: rfl

中文:
引理 toLinearMap_antipodeAlgHom
  结论: (antipodeAlgHom R A).toLinearMap = antipode R
  证明: rfl
-/
@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

variable [Semiring C] [HopfAlgebra R C]

/--
lemma `antipode_mul_id` / 引理 `antipode_mul_id`

English:
lemma antipode_mul_id
  statement: toConv (antipode R (A := C)) * toConv id = 1
  proof: by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]

中文:
引理 antipode_mul_id
  结论: toConv (antipode R (A := C)) * toConv id = 1
  证明: by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]
-/
@[simp] lemma antipode_mul_id : toConv (antipode R (A := C)) * toConv id = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]

/--
lemma `id_mul_antipode` / 引理 `id_mul_antipode`

English:
lemma id_mul_antipode
  statement: toConv id * toConv (antipode R (A := C)) = 1
  proof: by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]

中文:
引理 id_mul_antipode
  结论: toConv id * toConv (antipode R (A := C)) = 1
  证明: by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]
-/
@[simp] lemma id_mul_antipode : toConv id * toConv (antipode R (A := C)) = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 otimesₘ 𝑺) ∘ₗ TensorProduct.comm R C C ∘ₗ δ

/--
lemma `comul_right_inv` / 引理 `comul_right_inv`

English:
lemma comul_right_inv
  statement: toConv δ * toConv 𝑭 = 1
  proof: by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ ∘ₗ map δ (δ ∘ₗ 𝑺) ∘ₗ δ
      = μ ∘ₗ ((δ ∘ₗ id) otimesₘ (δ ∘ₗ 𝑺)) ∘ₗ δ := rfl
    _ = μ ∘ₗ (δ otimesₘ δ) ∘ₗ (id otimesₘ 𝑺) ∘ₗ δ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ ∘ₗ μ ∘ₗ (id otimesₘ 𝑺) ∘ₗ δ := by
        have : (μ ∘ₗ (δ otimesₘ δ) : C otimes[R] C ->ₗ[R] C otimes[R] C) = δ ∘ₗ μ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ ∘ₗ (1 : WithConv (C ->ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = η ∘ₗ ε := by
        simp [LinearMap.convOne_def, show (δ ∘ₗ η : R ->ₗ[R] C otimes[R] C) = η by ext; simp; rfl,
          ← comp_assoc]

中文:
引理 comul_right_inv
  结论: toConv δ * toConv 𝑭 = 1
  证明: by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ ∘ₗ map δ (δ ∘ₗ 𝑺) ∘ₗ δ
      = μ ∘ₗ ((δ ∘ₗ id) otimesₘ (δ ∘ₗ 𝑺)) ∘ₗ δ := rfl
    _ = μ ∘ₗ (δ otimesₘ δ) ∘ₗ (id otimesₘ 𝑺) ∘ₗ δ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ ∘ₗ μ ∘ₗ (id otimesₘ 𝑺) ∘ₗ δ := by
        have : (μ ∘ₗ (δ otimesₘ δ) : C otimes[R] C ->ₗ[R] C otimes[R] C) = δ ∘ₗ μ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ ∘ₗ (1 : WithConv (C ->ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = η ∘ₗ ε := by
        simp [LinearMap.convOne_def, show (δ ∘ₗ η : R ->ₗ[R] C otimes[R] C) = η by ext; simp; rfl,
          ← comp_assoc]

Depends on / 依赖: LinearMap, LinearMap.convM, LinearMap.convMul_def, LinearMap.convOne_def, TensorProduct, WithConv, WithConv.ext, _root_, _root_.TensorProduct.map_comp, comp_assoc, convMul_def, convOne_def, map_comp, ofConv, ofConv_toConv, otimes, toConv
-/
lemma comul_right_inv : toConv δ * toConv 𝑭 = 1 := by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ ∘ₗ map δ (δ ∘ₗ 𝑺) ∘ₗ δ
      = μ ∘ₗ ((δ ∘ₗ id) otimesₘ (δ ∘ₗ 𝑺)) ∘ₗ δ := rfl
    _ = μ ∘ₗ (δ otimesₘ δ) ∘ₗ (id otimesₘ 𝑺) ∘ₗ δ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ ∘ₗ μ ∘ₗ (id otimesₘ 𝑺) ∘ₗ δ := by
        have : (μ ∘ₗ (δ otimesₘ δ) : C otimes[R] C ->ₗ[R] C otimes[R] C) = δ ∘ₗ μ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ ∘ₗ (1 : WithConv (C ->ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = η ∘ₗ ε := by
        simp [LinearMap.convOne_def, show (δ ∘ₗ η : R ->ₗ[R] C otimes[R] C) = η by ext; simp; rfl,
          ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommSemiring A] [CommSemiring C] [Bialgebra R C] [HopfAlgebra R A]

/--
Instance `convInv` / 实例 `convInv`

English:
instance convInv
  signature: : Inv (WithConv <| A ->ₐ[R] C) where
  body: toConv f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)

中文:
实例 convInv
  签名: : 取逆 (WithConv <| A ->ₐ[R] C) where
  定义体: toConv f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)

Depends on / 依赖: HopfAlgebra, HopfAlgebra.antipodeAlgHom, antipodeAlgHom, f.ofConv.comp, ofConv, toConv
-/
instance convInv : Inv (WithConv <| A ->ₐ[R] C) where
inv f := toConv f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)

/--
Instance `convGroup` / 实例 `convGroup`

English:
instance convGroup
  signature: : Group (WithConv <| A ->ₐ[R] C) where
  body: by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
trans toConv ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H]; rw [AlgHom.comp_assoc]; rw [WithConv.ext_iff]; rw [← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A ->ₗ[R] C)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

中文:
实例 convGroup
  签名: : 群 (WithConv <| A ->ₐ[R] C) where
  定义体: by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
trans toConv ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H]; rw [AlgHom.comp_assoc]; rw [WithConv.ext_iff]; rw [← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A ->ₗ[R] C)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

Depends on / 依赖: AlgHom, AlgHom.comp_assoc, AlgHom.toLine, Algebra, Algebra.TensorProduct.map, Algebra.TensorProduct.map_comp, HopfAlgebra, HopfAlgebra.antipodeAlgHom, TensorProduct, WithConv, WithConv.ext_iff, antipodeAlgHom, comp_assoc, comulAlgHom, ext_iff, f.ofConv, f.ofConv.comp, map_comp, ofConv, toConv
-/
instance convGroup : Group (WithConv <| A ->ₐ[R] C) where
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
trans toConv ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H]; rw [AlgHom.comp_assoc]; rw [WithConv.ext_iff]; rw [← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A ->ₗ[R] C)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCocomm
  signature: R A] : CommGroup (WithConv <| A ->ₐ[R] C) where

中文:
实例 [是余comm
  签名: R A] : 交换群 (WithConv <| A ->ₐ[R] C) where
-/
instance [IsCocomm R A] : CommGroup (WithConv <| A ->ₐ[R] C) where

/--
lemma `antipode_id_cancel` / 引理 `antipode_id_cancel`

English:
lemma antipode_id_cancel
  proof: by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]; rw [AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]

中文:
引理 antipode_id_cancel
  证明: by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]; rw [AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne, AlgHom.toLinearMap_injective, LinearMap, LinearMap.antipode_mul_id, WithConv, WithConv.ofConv_injective, WithConv.toConv_injective, antipode_mul_id, ofConv_injective, toConv_injective, toLinearMap_convMul, toLinearMap_convOne, toLinearMap_injective
-/
lemma antipode_id_cancel :
    toConv (HopfAlgebra.antipodeAlgHom R A) * toConv (AlgHom.id R A) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]; rw [AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]

/--
lemma `counitAlgHom_comp_antipodeAlgHom` / 引理 `counitAlgHom_comp_antipodeAlgHom`

English:
lemma counitAlgHom_comp_antipodeAlgHom
  proof: AlgHom.toLinearMap_injective by simp

中文:
引理 counitAlgHom_comp_antipodeAlgHom
  证明: AlgHom.toLinearMap_injective by simp

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, toLinearMap_injective
-/
lemma counitAlgHom_comp_antipodeAlgHom :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
AlgHom.toLinearMap_injective by simp

end AlgHom
