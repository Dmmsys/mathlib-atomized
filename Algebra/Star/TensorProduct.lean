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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (A otimes[R] B)
  body: congr (starLinearEquiv R) (starLinearEquiv R) x

@[simp]

中文:
实例 :
  签名: 对合 (A otimes[R] B)
  定义体: congr (starLinearEquiv R) (starLinearEquiv R) x

@[simp]

Depends on / 依赖: starLinearEquiv
-/
instance : Star (A otimes[R] B) where
  star x := congr (starLinearEquiv R) (starLinearEquiv R) x

@[simp]
/--
theorem `star_tmul` / 定理 `star_tmul`

English:
theorem star_tmul
  given: (x : A) (y : B)
  statement: star (x otimesₜ[R] y) = star x otimesₜ[R] star y
  proof: rfl

中文:
定理 star_tmul
  条件: (x : A) (y : B)
  结论: star (x otimesₜ[R] y) = star x otimesₜ[R] star y
  证明: rfl
-/
theorem star_tmul (x : A) (y : B) : star (x otimesₜ[R] y) = star x otimesₜ[R] star y := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar (A otimes[R] B)
  body: by
    simp_rw [star]
    rw [congr_congr]
    convert! congr($congr_refl_refl x) <;> ext <;> simp

中文:
实例 :
  签名: InvolutiveStar (A otimes[R] B)
  定义体: by
    simp_rw [star]
    rw [congr_congr]
    convert! congr($congr_refl_refl x) <;> ext <;> simp

Depends on / 依赖: congr_congr, congr_refl_refl, convert, simp_rw
-/
noncomputable instance : InvolutiveStar (A otimes[R] B) where
  star_involutive x := by
    simp_rw [star]
    rw [congr_congr]
    convert! congr($congr_refl_refl x) <;> ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarAddMonoid (A otimes[R] B)
  body: map_add _

中文:
实例 :
  签名: StarAdd幺半群 (A otimes[R] B)
  定义体: map_add _

Depends on / 依赖: map_add
-/
noncomputable instance : StarAddMonoid (A otimes[R] B) where
  star_add := map_add _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule R (A otimes[R] B)
  body: map_smulₛₗ _

中文:
实例 :
  签名: 对合模 R (A otimes[R] B)
  定义体: map_smulₛₗ _
-/
instance : StarModule R (A otimes[R] B) where
  star_smul := map_smulₛₗ _

/--
theorem `_root_.starLinearEquiv_tensor` / 定理 `_root_.starLinearEquiv_tensor`

English:
theorem _root_.starLinearEquiv_tensor
  proof: rfl

中文:
定理 _root_.starLinearEquiv_tensor
  证明: rfl

Depends on / 依赖: otimes, starLinearEquiv
-/
theorem _root_.starLinearEquiv_tensor :
    starLinearEquiv R (A := A otimes[R] B) = congr (starLinearEquiv R) (starLinearEquiv R) := rfl

end TensorProduct
