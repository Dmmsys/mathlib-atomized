/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The star structure on tensor products

This file defines the `Star` structure on tensor products. This also
defines the `StarAddMonoid` and `StarModule` instances for tensor products.
-/

public section

namespace TensorProduct
variable {R A B : Type*}
  [CommSemiring R] [StarRing R]
  [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]
  [AddCommMonoid B] [StarAddMonoid B] [Module R B] [StarModule R B]

open scoped TensorProduct

/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (A ⊗[R] B) where
  star x := congr (starLinearEquiv R) (starLinearEquiv R) x

@[simp]
/-
**TensorProduct.star_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：star_tmul (x : A) (y : B) : star (x otimesₜ[R] y) = star x otimesₜ[R] star
 y
参数：x : A；y : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_tmul (x : A) (y : B) : star (x ⊗ₜ[R] y) = star x ⊗ₜ[R] star y := rfl
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : InvolutiveStar (A ⊗[R] B) where
  star_involutive x := by
    simp_rw [star]
    rw [congr_congr]
    convert! congr($congr_refl_refl x) <;> ext <;> simp
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : StarAddMonoid (A ⊗[R] B) where
  star_add := map_add _
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule R (A ⊗[R] B) where
  star_smul := map_smulₛₗ _
/-
**TensorProduct._root_.starLinearEquiv_tensor** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.starLinearEquiv_tensor :
    starLinearEquiv R (A := A ⊗[R] B) = congr (starLinearEquiv R) (starLinearEquiv R) := rfl

end TensorProduct

