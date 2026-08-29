/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import Mathlib.Algebra.Star.Unitary

import Mathlib.Tactic.FieldSimp

/-!
# Quadratic algebras: involution, norm, and trace.

Let `R` be a commutative ring. We define:

* `QuadraticAlgebra.star`: the quadratic involution

* `QuadraticAlgebra.norm`: the norm

* `QuadraticAlgebra.trace`: the trace, as an `R`-linear map

We prove:

* `QuadraticAlgebra.isUnit_iff_norm_isUnit`:
  `w : QuadraticAlgebra R a b` is a unit iff `w.norm` is a unit in `R`.

* `QuadraticAlgebra.norm_mem_nonZeroDivisors_iff`:
  `w : QuadraticAlgebra R a b` isn't a zero divisor iff
  `w.norm` isn't a zero divisor in `R`.

* If `K` is a field, and `∀ r, r ^ 2 ≠ a + b * r`, then `QuadraticAlgebra K a b` is a field.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {K R : Type*} {a b : R}

section omega

section

variable [Zero R] [One R]

/--
Definition of `omega` / `omega` 的定义

English:
definition omega
  signature: : QuadraticAlgebra R a b
  body: ⟨0, 1⟩

中文:
定义 omega
  签名: : QuadraticAlgebra R a b
  定义体: ⟨0, 1⟩

Depends on / 依赖: star_smul
-/
def omega : QuadraticAlgebra R a b :=
  ⟨0, 1⟩

/-- the canonical element `⟨0, 1⟩` in a quadratic algebra `QuadraticAlgebra R a b`. -/
scoped notation "ω" => omega

@[simp]
/--
theorem `omega_re` / 定理 `omega_re`

English:
theorem omega_re
  statement: (ω : QuadraticAlgebra R a b).re = 0
  proof: rfl

@[simp]

中文:
定理 omega_re
  结论: (ω : QuadraticAlgebra R a b).re = 0
  证明: rfl

@[simp]
-/
theorem omega_re : (ω : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
/--
theorem `omega_im` / 定理 `omega_im`

English:
theorem omega_im
  statement: (ω : QuadraticAlgebra R a b).im = 1
  proof: rfl

中文:
定理 omega_im
  结论: (ω : QuadraticAlgebra R a b).im = 1
  证明: rfl
-/
theorem omega_im : (ω : QuadraticAlgebra R a b).im = 1 :=
  rfl

end

variable [CommSemiring R]

/--
theorem `omega_mul_omega_eq_mk` / 定理 `omega_mul_omega_eq_mk`

English:
theorem omega_mul_omega_eq_mk
  statement: (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩
  proof: by
  ext <;> simp

中文:
定理 omega_mul_omega_eq_mk
  结论: (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩
  证明: by
  ext <;> simp
-/
theorem omega_mul_omega_eq_mk : (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩ := by
  ext <;> simp

/--
theorem `omega_mul_omega_eq_add` / 定理 `omega_mul_omega_eq_add`

English:
theorem omega_mul_omega_eq_add
  proof: by
  ext <;> simp

中文:
定理 omega_mul_omega_eq_add
  证明: by
  ext <;> simp
-/
theorem omega_mul_omega_eq_add :
    (ω : QuadraticAlgebra R a b) * ω = a • 1 + b • ω := by
  ext <;> simp

/--
theorem `omega_mul_omega_eq_algebraMap` / 定理 `omega_mul_omega_eq_algebraMap`

English:
theorem omega_mul_omega_eq_algebraMap
  proof: by
  simp [omega_mul_omega_eq_add, Algebra.algebraMap_eq_smul_one]

@[simp]

中文:
定理 omega_mul_omega_eq_algebraMap
  证明: by
  simp [omega_mul_omega_eq_add, Algebra.algebraMap_eq_smul_one]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, omega_mul_omega_eq_add
-/
theorem omega_mul_omega_eq_algebraMap :
    (ω : QuadraticAlgebra R a b) * ω = algebraMap R _ a + algebraMap R _ b * ω := by
  simp [omega_mul_omega_eq_add, Algebra.algebraMap_eq_smul_one]

@[simp]
/--
theorem `omega_mul_mk` / 定理 `omega_mul_mk`

English:
theorem omega_mul_mk
  given: (x y : R)
  statement: (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩
  proof: by
  ext <;> simp

@[simp]

中文:
定理 omega_mul_mk
  条件: (x y : R)
  结论: (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩
  证明: by
  ext <;> simp

@[simp]
-/
theorem omega_mul_mk (x y : R) : (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩ := by
  ext <;> simp

@[simp]
/--
theorem `omega_mul_algebraMap_mul_mk` / 定理 `omega_mul_algebraMap_mul_mk`

English:
theorem omega_mul_algebraMap_mul_mk
  given: (n x y : R)
  proof: by
  ext <;> simp; ring

中文:
定理 omega_mul_algebraMap_mul_mk
  条件: (n x y : R)
  证明: by
  ext <;> simp; ring
-/
theorem omega_mul_algebraMap_mul_mk (n x y : R) :
    (ω : QuadraticAlgebra R a b) * algebraMap _ _ n * ⟨x, y⟩ = ⟨a * n * y, n * x + n * b * y⟩ := by
  ext <;> simp; ring

/--
theorem `mk_eq_add_smul_omega` / 定理 `mk_eq_add_smul_omega`

English:
theorem mk_eq_add_smul_omega
  given: (x y : R)
  proof: by
  ext <;> simp

中文:
定理 mk_eq_add_smul_omega
  条件: (x y : R)
  证明: by
  ext <;> simp
-/
theorem mk_eq_add_smul_omega (x y : R) :
    (⟨x, y⟩ : QuadraticAlgebra R a b) = algebraMap _ _ x + y • ω := by
  ext <;> simp

variable {A : Type*} [Ring A] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
@[ext]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: {f g : QuadraticAlgebra R a b ->ₐ[R] A}
  proof: by
  ext ⟨x, y⟩
  simp [mk_eq_add_smul_omega, h]

中文:
定理 algHom_ext
  结论: {f g : QuadraticAlgebra R a b ->ₐ[R] A}
  证明: by
  ext ⟨x, y⟩
  simp [mk_eq_add_smul_omega, h]

Depends on / 依赖: mk_eq_add_smul_omega
-/
theorem algHom_ext {f g : QuadraticAlgebra R a b ->ₐ[R] A}
    (h : f ω = g ω) : f = g := by
  ext ⟨x, y⟩
  simp [mk_eq_add_smul_omega, h]

set_option backward.isDefEq.respectTransparency false in
/-- The unique `AlgHom` from `QuadraticAlgebra R a b` to an `R`-algebra `A`,
constructed by replacing `ω` with the provided root.
Conversely, this associates to every algebra morphism `QuadraticAlgebra R a b →ₐ[R] A`
a value of `ω` in `A`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : { u : A // u * u = a • 1 + b • u } ≃ (QuadraticAlgebra R a b ->ₐ[R] A) where
  body: { toFun z := z.re • 1 + z.im • u
      map_zero' := by simp
      map_add' z w := by
        simp only [re_add, im_add, add_smul, ← add_assoc]
        congr 1
        simp only [add_assoc]
        congr 1
        rw [add_comm]
      map_one' := by simp
      map_mul' z w := by
        symm
        c

中文:
定义 lift
  签名: : { u : A // u * u = a • 1 + b • u } ≃ (QuadraticAlgebra R a b ->ₐ[R] A) where
  定义体: { toFun z := z.re • 1 + z.im • u
      map_zero' := by simp
      map_add' z w := by
        simp only [re_add, im_add, add_smul, ← add_assoc]
        congr 1
        simp only [add_assoc]
        congr 1
        rw [add_comm]
      map_one' := by simp
      map_mul' z w := by
        symm
        c

Depends on / 依赖: add_add_add_comm, add_assoc, add_comm, add_mul, add_smul, im_add, map_add, map_mul, map_one, map_zero, mul_add, mul_one, one_mul, re_add, smul_mul_smul, w.im, w.re, z.im, z.re
-/
def lift : { u : A // u * u = a • 1 + b • u } ≃ (QuadraticAlgebra R a b ->ₐ[R] A) where
  toFun u :=
    { toFun z := z.re • 1 + z.im • u
      map_zero' := by simp
      map_add' z w := by
        simp only [re_add, im_add, add_smul, ← add_assoc]
        congr 1
        simp only [add_assoc]
        congr 1
        rw [add_comm]
      map_one' := by simp
      map_mul' z w := by
        symm
        calc
          (z.re • (1 : A) + z.im • ↑u) * (w.re • 1 + w.im • ↑u) =
            (z.re * w.re) • (1 : A) + (z.re * w.im) • u +
              (z.im * w.re) • u + (z.im * w.im) • (u * u) := by
              simp only [mul_add, mul_one, add_mul, one_mul, ← add_assoc, smul_mul_smul]
              apply add_add_add_comm'
          _ = (z.re * w.re) • (1 : A) + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (u * u) := by
              congr 1
              simp only [add_assoc]
              rw [← add_smul]
          _ = (z.re * w.re) • 1 + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (a • 1 + b • u) := by
              simp [u.prop]
          _ = (z.re * w.re + a * z.im * w.im) • 1 +
                (z.re * w.im + z.im * w.re + b * z.im * w.im) • u := by
              simp only [smul_add]
              module
            _ = (z * w).re • 1 + (z * w).im • u := by
              simp
      commutes' r := by
        simp [← Algebra.algebraMap_eq_smul_one] }
  invFun f := ⟨f (ω), by
    simp [← map_mul, omega_mul_omega_eq_add]
    ⟩
  left_inv r := by
    simp
  right_inv f := by
    ext
    simp

end omega

section star

variable [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (QuadraticAlgebra R a b)
  body: ⟨z.re + b * z.im, -z.im⟩

@[simp]

中文:
实例 :
  签名: Star (QuadraticAlgebra R a b)
  定义体: ⟨z.re + b * z.im, -z.im⟩

@[simp]

Depends on / 依赖: z.im, z.re
-/
instance : Star (QuadraticAlgebra R a b) where
  star z := ⟨z.re + b * z.im, -z.im⟩

@[simp]
/--
theorem `star_mk` / 定理 `star_mk`

English:
theorem star_mk
  given: (x y : R)
  proof: rfl

@[simp]

中文:
定理 star_mk
  条件: (x y : R)
  证明: rfl

@[simp]
-/
theorem star_mk (x y : R) :
    star (⟨x, y⟩ : QuadraticAlgebra R a b) = ⟨x + b * y, -y⟩ :=
  rfl

@[simp]
/--
theorem `re_star` / 定理 `re_star`

English:
theorem re_star
  given: (z : QuadraticAlgebra R a b)
  proof: rfl

@[simp]

中文:
定理 re_star
  条件: (z : QuadraticAlgebra R a b)
  证明: rfl

@[simp]
-/
theorem re_star (z : QuadraticAlgebra R a b) :
    (star z).re = z.re + b * z.im :=
  rfl

@[simp]
/--
theorem `im_star` / 定理 `im_star`

English:
theorem im_star
  given: (z : QuadraticAlgebra R a b)
  proof: rfl

中文:
定理 im_star
  条件: (z : QuadraticAlgebra R a b)
  证明: rfl
-/
theorem im_star (z : QuadraticAlgebra R a b) :
    (star z).im = -z.im :=
  rfl

/--
theorem `mul_star` / 定理 `mul_star`

English:
theorem mul_star
  given: (x y : R)
  proof: by
  ext <;> simp <;> ring

中文:
定理 mul_star
  条件: (x y : R)
  证明: by
  ext <;> simp <;> ring
-/
theorem mul_star (x y : R) :
    (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra R a b) = (algebraMap _ _ x) * (algebraMap _ _ x) +
      (algebraMap _ _ b) * (algebraMap _ _ x) * (algebraMap _ _ y) - (algebraMap _ _ a) *
      (algebraMap _ _ y) * (algebraMap _ _ y) := by
  ext <;> simp <;> ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (QuadraticAlgebra R a b)
  body: by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;>
    simp only [re_star, re_mul, im_mul, im_star, mul_neg, neg_mul, neg_neg] <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp only [re_star, re_add, im_add]; ring) (neg_add _ _)

中文:
实例 :
  签名: StarRing (QuadraticAlgebra R a b)
  定义体: by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;>
    simp only [re_star, re_mul, im_mul, im_star, mul_neg, neg_mul, neg_neg] <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp only [re_star, re_add, im_add]; ring) (neg_add _ _)

Depends on / 依赖: QuadraticAlgebra, QuadraticAlgebra.ext, im_add, im_mul, im_star, mul_neg, neg_add, neg_mul, neg_neg, re_add, re_mul, re_star, star_add, star_mul
-/
instance : StarRing (QuadraticAlgebra R a b) where
  star_involutive _ := by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;>
    simp only [re_star, re_mul, im_mul, im_star, mul_neg, neg_mul, neg_neg] <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp only [re_star, re_add, im_add]; ring) (neg_add _ _)

/--
theorem `sub_star` / 定理 `sub_star`

English:
theorem sub_star
  given: (z : QuadraticAlgebra R a b)
  proof: by
  ext <;> simp <;> ring

中文:
定理 sub_star
  条件: (z : QuadraticAlgebra R a b)
  证明: by
  ext <;> simp <;> ring
-/
theorem sub_star (z : QuadraticAlgebra R a b) :
    z - star z = z.im • (ω - star ω) := by
  ext <;> simp <;> ring

end star

section norm

variable [CommRing R]

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : QuadraticAlgebra R a b ->* R where
  body: z.re * z.re + b * z.re * z.im - a * z.im * z.im
  map_mul' z w := by simp only [re_mul, im_mul]; ring
  map_one' := by simp

中文:
定义 norm
  签名: : QuadraticAlgebra R a b ->* R where
  定义体: z.re * z.re + b * z.re * z.im - a * z.im * z.im
  map_mul' z w := by simp only [re_mul, im_mul]; ring
  map_one' := by simp

Depends on / 依赖: z.im, z.re
-/
def norm : QuadraticAlgebra R a b ->* R where
  toFun z := z.re * z.re + b * z.re * z.im - a * z.im * z.im
  map_mul' z w := by simp only [re_mul, im_mul]; ring
  map_one' := by simp

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (z : QuadraticAlgebra R a b)
  proof: rfl

@[simp]

中文:
定理 norm_def
  条件: (z : QuadraticAlgebra R a b)
  证明: rfl

@[simp]
-/
theorem norm_def (z : QuadraticAlgebra R a b) :
    z.norm = z.re * z.re + b * z.re * z.im - a * z.im * z.im :=
  rfl

@[simp]
/--
theorem `norm_zero` / 定理 `norm_zero`

English:
theorem norm_zero
  statement: norm (0 : QuadraticAlgebra R a b) = 0
  proof: by simp [norm]

@[simp]

中文:
定理 norm_zero
  结论: norm (0 : QuadraticAlgebra R a b) = 0
  证明: by simp [norm]

@[simp]
-/
theorem norm_zero : norm (0 : QuadraticAlgebra R a b) = 0 := by simp [norm]

@[simp]
/--
theorem `norm_one` / 定理 `norm_one`

English:
theorem norm_one
  statement: norm (1 : QuadraticAlgebra R a b) = 1
  proof: by simp [norm]

@[simp]

中文:
定理 norm_one
  结论: norm (1 : QuadraticAlgebra R a b) = 1
  证明: by simp [norm]

@[simp]
-/
theorem norm_one : norm (1 : QuadraticAlgebra R a b) = 1 := by simp [norm]

@[simp]
/--
theorem `norm_algebraMap` / 定理 `norm_algebraMap`

English:
theorem norm_algebraMap
  given: (r : R)
  statement: norm (algebraMap R (QuadraticAlgebra R a b) r) = r ^ 2
  proof: by
  simp [norm_def, pow_two]

@[simp]

中文:
定理 norm_algebraMap
  条件: (r : R)
  结论: norm (algebraMap R (QuadraticAlgebra R a b) r) = r ^ 2
  证明: by
  simp [norm_def, pow_two]

@[simp]

Depends on / 依赖: norm_def, pow_two
-/
theorem norm_algebraMap (r : R) : norm (algebraMap R (QuadraticAlgebra R a b) r) = r ^ 2 := by
  simp [norm_def, pow_two]

@[simp]
/--
theorem `norm_natCast` / 定理 `norm_natCast`

English:
theorem norm_natCast
  given: (n : Nat)
  statement: norm (n : QuadraticAlgebra R a b) = n ^ 2
  proof: by
  simp [norm_def, pow_two]

@[simp]

中文:
定理 norm_natCast
  条件: (n : 自然数)
  结论: norm (n : QuadraticAlgebra R a b) = n ^ 2
  证明: by
  simp [norm_def, pow_two]

@[simp]

Depends on / 依赖: norm_def, pow_two
-/
theorem norm_natCast (n : Nat) : norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [norm_def, pow_two]

@[simp]
/--
theorem `norm_intCast` / 定理 `norm_intCast`

English:
theorem norm_intCast
  given: (n : Int)
  statement: norm (n : QuadraticAlgebra R a b) = n ^ 2
  proof: by
  simp [norm_def, pow_two]

中文:
定理 norm_intCast
  条件: (n : 整数)
  结论: norm (n : QuadraticAlgebra R a b) = n ^ 2
  证明: by
  simp [norm_def, pow_two]

Depends on / 依赖: norm_def, pow_two
-/
theorem norm_intCast (n : Int) : norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [norm_def, pow_two]

/--
theorem `algebraMap_norm_eq_mul_star` / 定理 `algebraMap_norm_eq_mul_star`

English:
theorem algebraMap_norm_eq_mul_star
  given: (z : QuadraticAlgebra R a b)
  proof: by
  ext <;> simp [norm, star, mul_comm] <;> ring

@[simp]

中文:
定理 algebraMap_norm_eq_mul_star
  条件: (z : QuadraticAlgebra R a b)
  证明: by
  ext <;> simp [norm, star, mul_comm] <;> ring

@[simp]

Depends on / 依赖: mul_comm
-/
theorem algebraMap_norm_eq_mul_star (z : QuadraticAlgebra R a b) :
    (algebraMap R _ (norm z : R)) = z * star z := by
  ext <;> simp [norm, star, mul_comm] <;> ring

@[simp]
/--
theorem `norm_neg` / 定理 `norm_neg`

English:
theorem norm_neg
  given: (x : QuadraticAlgebra R a b)
  statement: (-x).norm = x.norm
  proof: by
  simp [norm]

@[simp]

中文:
定理 norm_neg
  条件: (x : QuadraticAlgebra R a b)
  结论: (-x).norm = x.norm
  证明: by
  simp [norm]

@[simp]
-/
theorem norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm := by
  simp [norm]

@[simp]
/--
theorem `norm_star` / 定理 `norm_star`

English:
theorem norm_star
  given: (x : QuadraticAlgebra R a b)
  statement: (star x).norm = x.norm
  proof: by
  simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk, re_star, im_star, mul_neg, neg_mul, neg_neg,
    sub_left_inj]
  ring

中文:
定理 norm_star
  条件: (x : QuadraticAlgebra R a b)
  结论: (star x).norm = x.norm
  证明: by
  simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk, re_star, im_star, mul_neg, neg_mul, neg_neg,
    sub_left_inj]
  ring

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, coe_mk, im_star, mul_neg, neg_mul, neg_neg, re_star, sub_left_inj
-/
theorem norm_star (x : QuadraticAlgebra R a b) : (star x).norm = x.norm := by
  simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk, re_star, im_star, mul_neg, neg_mul, neg_neg,
    sub_left_inj]
  ring

/--
theorem `isUnit_iff_norm_isUnit` / 定理 `isUnit_iff_norm_isUnit`

English:
theorem isUnit_iff_norm_isUnit
  given: {x : QuadraticAlgebra R a b}
  proof: by
  constructor
  · exact IsUnit.map norm
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← C_inj (R := R) (a := a) (b := b)]; rw [C_mul]; rw [C_eq_algebraMap]; rw [algebraMap_norm_eq_mul_star]; rw [mul_assoc]; rw [map_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm]; rw [hr]

中文:
定理 isUnit_iff_norm_isUnit
  条件: {x : QuadraticAlgebra R a b}
  证明: by
  constructor
  · exact IsUnit.map norm
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← C_inj (R := R) (a := a) (b := b)]; rw [C_mul]; rw [C_eq_algebraMap]; rw [algebraMap_norm_eq_mul_star]; rw [mul_assoc]; rw [map_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm]; rw [hr]

Depends on / 依赖: C_eq_algebraMap, C_inj, C_mul, IsUnit, IsUnit.map, Prod.ext, algebraMap_norm_eq_mul_star, isUnit_iff_exists, map_one, mul_assoc, mul_comm, star_add
-/
theorem isUnit_iff_norm_isUnit {x : QuadraticAlgebra R a b} :
    IsUnit x ↔ IsUnit (x.norm) := by
  constructor
  · exact IsUnit.map norm
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← C_inj (R := R) (a := a) (b := b)]; rw [C_mul]; rw [C_eq_algebraMap]; rw [algebraMap_norm_eq_mul_star]; rw [mul_assoc]; rw [map_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm]; rw [hr]

/--
theorem `norm_eq_one_iff_mem_unitary` / 定理 `norm_eq_one_iff_mem_unitary`

English:
theorem norm_eq_one_iff_mem_unitary
  given: {z : QuadraticAlgebra R a b}
  proof: by
  rw [Unitary.mem_iff_self_mul_star]; rw [← algebraMap_norm_eq_mul_star]
  simp [← algebraMap_inj (R := R) (a := a) (b := b)]

alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary

中文:
定理 norm_eq_one_iff_mem_unitary
  条件: {z : QuadraticAlgebra R a b}
  证明: by
  rw [Unitary.mem_iff_self_mul_star]; rw [← algebraMap_norm_eq_mul_star]
  simp [← algebraMap_inj (R := R) (a := a) (b := b)]

alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary

Depends on / 依赖: Unitary, Unitary.mem_iff_self_mul_star, algebraMap_inj, algebraMap_norm_eq_mul_star, mem_iff_self_mul_star
-/
theorem norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra R a b} :
    z.norm = 1 ↔ z in unitary (QuadraticAlgebra R a b) := by
  rw [Unitary.mem_iff_self_mul_star]; rw [← algebraMap_norm_eq_mul_star]
  simp [← algebraMap_inj (R := R) (a := a) (b := b)]

alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary

/--
theorem `mker_norm_eq_unitary` / 定理 `mker_norm_eq_unitary`

English:
theorem mker_norm_eq_unitary
  proof: Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

中文:
定理 mker_norm_eq_unitary
  证明: Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

Depends on / 依赖: Prod.ext, Submonoid, Submonoid.ext, norm_eq_one_iff_mem_unitary, star_smul
-/
theorem mker_norm_eq_unitary :
    MonoidHom.mker (@norm R a b _) = unitary (QuadraticAlgebra R a b) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

open nonZeroDivisors

/--
theorem `algebraMap_mem_nonZeroDivisors_iff` / 定理 `algebraMap_mem_nonZeroDivisors_iff`

English:
theorem algebraMap_mem_nonZeroDivisors_iff
  given: {r : R}
  proof: by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← algebraMap_inj]; rw [map_zero]
    apply H
    rw [← map_mul]; rw [hxr]; rw [map_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff]; rw [re_zero]; rw [im_zero] at hz
    simp only [re_mul, algebraMap_re, a

中文:
定理 algebraMap_mem_nonZeroDivisors_iff
  条件: {r : R}
  证明: by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← algebraMap_inj]; rw [map_zero]
    apply H
    rw [← map_mul]; rw [hxr]; rw [map_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff]; rw [re_zero]; rw [im_zero] at hz
    simp only [re_mul, algebraMap_re, a

Depends on / 依赖: QuadraticAlgebra, QuadraticAlgebra.ext_iff, add_zero, algebraMap_im, algebraMap_inj, algebraMap_re, ext_iff, hz.left, hz.right, im_mul, im_zero, map_mul, map_zero, mem_nonZeroDivisors_iff_right, mul_zero, re_mul, re_zero, zero_add
-/
theorem algebraMap_mem_nonZeroDivisors_iff {r : R} :
    algebraMap R (QuadraticAlgebra R a b) r in (QuadraticAlgebra R a b)⁰ ↔ r in R⁰ := by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← algebraMap_inj]; rw [map_zero]
    apply H
    rw [← map_mul]; rw [hxr]; rw [map_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff]; rw [re_zero]; rw [im_zero] at hz
    simp only [re_mul, algebraMap_re, algebraMap_im, mul_zero, add_zero, im_mul, zero_add] at hz
    simp [QuadraticAlgebra.ext_iff, re_zero, im_zero, h _ hz.left, h _ hz.right]

/--
theorem `star_mem_nonZeroDivisors` / 定理 `star_mem_nonZeroDivisors`

English:
theorem star_mem_nonZeroDivisors
  statement: {z : QuadraticAlgebra R a b}
  proof: by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z]; rw [← star_mul]; rw [mul_comm]; rw [hw]; rw [star_zero]

中文:
定理 star_mem_nonZeroDivisors
  结论: {z : QuadraticAlgebra R a b}
  证明: by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z]; rw [← star_mul]; rw [mul_comm]; rw [hw]; rw [star_zero]

Depends on / 依赖: injective, mem_nonZeroDivisors_iff_right, mul_comm, star_involutive, star_involutive.injective, star_mul, star_zero
-/
theorem star_mem_nonZeroDivisors {z : QuadraticAlgebra R a b}
    (hz : z in (QuadraticAlgebra R a b)⁰) :
    star z in (QuadraticAlgebra R a b)⁰ := by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z]; rw [← star_mul]; rw [mul_comm]; rw [hw]; rw [star_zero]

/--
theorem `star_mem_nonZeroDivisors_iff` / 定理 `star_mem_nonZeroDivisors_iff`

English:
theorem star_mem_nonZeroDivisors_iff
  given: {z : QuadraticAlgebra R a b}
  proof: by
  refine ⟨fun h => ?_, star_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact star_mem_nonZeroDivisors h

中文:
定理 star_mem_nonZeroDivisors_iff
  条件: {z : QuadraticAlgebra R a b}
  证明: by
  refine ⟨fun h => ?_, star_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact star_mem_nonZeroDivisors h

Depends on / 依赖: star_involutive, star_mem_nonZeroDivisors
-/
theorem star_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    star z in (QuadraticAlgebra R a b)⁰ ↔ z in (QuadraticAlgebra R a b)⁰ := by
  refine ⟨fun h => ?_, star_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact star_mem_nonZeroDivisors h

/--
theorem `norm_mem_nonZeroDivisors_iff` / 定理 `norm_mem_nonZeroDivisors_iff`

English:
theorem norm_mem_nonZeroDivisors_iff
  given: {z : QuadraticAlgebra R a b}
  proof: by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : norm z • w = 0 := by
      rw [← C_mul_eq_smul]; rw [C_eq_algebraMap]; rw [algebraMap_norm_eq_mul_star]; rw [mul_comm]; rw [← mul_assoc]; rw [hw]; rw [zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul

中文:
定理 norm_mem_nonZeroDivisors_iff
  条件: {z : QuadraticAlgebra R a b}
  证明: by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : norm z • w = 0 := by
      rw [← C_mul_eq_smul]; rw [C_eq_algebraMap]; rw [algebraMap_norm_eq_mul_star]; rw [mul_comm]; rw [← mul_assoc]; rw [hw]; rw [zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul

Depends on / 依赖: C_eq_algebraMap, C_mul_eq_smul, QuadraticAlgebra, QuadraticAlgebra.ext_iff, Submonoid, Submonoid.mul_mem, algebraMap_mem_nonZeroDivisors_iff, algebraMap_norm_eq_mul_star, ext_iff, im_smul, im_zero, mem_nonZeroDivisors_iff_right, mul_assoc, mul_comm, mul_mem, re_smul, re_zero, smul_eq_mul, this.left, this.right
-/
theorem norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    z.norm in R⁰ ↔ z in (QuadraticAlgebra R a b)⁰ := by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : norm z • w = 0 := by
      rw [← C_mul_eq_smul]; rw [C_eq_algebraMap]; rw [algebraMap_norm_eq_mul_star]; rw [mul_comm]; rw [← mul_assoc]; rw [hw]; rw [zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul, smul_eq_mul, mul_comm, re_zero, im_smul,
      im_zero] at this
    ext <;> simp [h _ this.left, h _ this.right]
  · intro hz
    rw [← algebraMap_mem_nonZeroDivisors_iff]; rw [algebraMap_norm_eq_mul_star]
    exact Submonoid.mul_mem _ hz (star_mem_nonZeroDivisors hz)

end norm

section trace

variable [CommRing R]

attribute [local grind =] re_add im_add im_star re_star re_smul im_smul RingHom.id_apply
  algebraMap_re algebraMap_im

/--
Definition of `trace` / `trace` 的定义

English:
definition trace
  signature: : QuadraticAlgebra R a b ->ₗ[R] R where
  body: 2 * z.re + b * z.im
  map_add' := by grind
  map_smul' := by grind [smul_eq_mul]

中文:
定义 trace
  签名: : QuadraticAlgebra R a b ->ₗ[R] R where
  定义体: 2 * z.re + b * z.im
  map_add' := by grind
  map_smul' := by grind [smul_eq_mul]

Depends on / 依赖: z.im, z.re
-/
def trace : QuadraticAlgebra R a b ->ₗ[R] R where
  toFun z := 2 * z.re + b * z.im
  map_add' := by grind
  map_smul' := by grind [smul_eq_mul]

variable (z : QuadraticAlgebra R a b)

/--
theorem `trace_def` / 定理 `trace_def`

English:
theorem trace_def
  statement: trace z = 2 * z.re + b * z.im
  proof: rfl

@[simp]

中文:
定理 trace_def
  结论: trace z = 2 * z.re + b * z.im
  证明: rfl

@[simp]
-/
theorem trace_def : trace z = 2 * z.re + b * z.im := rfl

@[simp]
/--
theorem `trace_algebraMap` / 定理 `trace_algebraMap`

English:
theorem trace_algebraMap
  given: (r : R)
  proof: by
  grind [trace_def]

@[simp]

中文:
定理 trace_algebraMap
  条件: (r : R)
  证明: by
  grind [trace_def]

@[simp]

Depends on / 依赖: trace_def
-/
theorem trace_algebraMap (r : R) :
    trace (algebraMap R (QuadraticAlgebra R a b) r) = 2 * r := by
  grind [trace_def]

@[simp]
/--
theorem `trace_natCast` / 定理 `trace_natCast`

English:
theorem trace_natCast
  given: (n : Nat)
  statement: trace (n : QuadraticAlgebra R a b) = 2 * n
  proof: by
  simp [trace_def, re_natCast, im_natCast]

@[simp]

中文:
定理 trace_natCast
  条件: (n : 自然数)
  结论: trace (n : QuadraticAlgebra R a b) = 2 * n
  证明: by
  simp [trace_def, re_natCast, im_natCast]

@[simp]

Depends on / 依赖: im_natCast, re_natCast, trace_def
-/
theorem trace_natCast (n : Nat) : trace (n : QuadraticAlgebra R a b) = 2 * n := by
  simp [trace_def, re_natCast, im_natCast]

@[simp]
/--
theorem `trace_intCast` / 定理 `trace_intCast`

English:
theorem trace_intCast
  given: (n : Int)
  statement: trace (n : QuadraticAlgebra R a b) = 2 * n
  proof: by
  simp [trace_def, re_intCast, im_intCast]

@[simp]

中文:
定理 trace_intCast
  条件: (n : 整数)
  结论: trace (n : QuadraticAlgebra R a b) = 2 * n
  证明: by
  simp [trace_def, re_intCast, im_intCast]

@[simp]

Depends on / 依赖: im_intCast, re_intCast, trace_def
-/
theorem trace_intCast (n : Int) : trace (n : QuadraticAlgebra R a b) = 2 * n := by
  simp [trace_def, re_intCast, im_intCast]

@[simp]
/--
theorem `trace_omega` / 定理 `trace_omega`

English:
theorem trace_omega
  statement: trace (ω : QuadraticAlgebra R a b) = b
  proof: by
  simp [trace_def]

@[simp]

中文:
定理 trace_omega
  结论: trace (ω : QuadraticAlgebra R a b) = b
  证明: by
  simp [trace_def]

@[simp]

Depends on / 依赖: trace_def
-/
theorem trace_omega : trace (ω : QuadraticAlgebra R a b) = b := by
  simp [trace_def]

@[simp]
/--
theorem `trace_one` / 定理 `trace_one`

English:
theorem trace_one
  statement: trace (1 : QuadraticAlgebra R a b) = 2
  proof: by
  simp [trace_def]

@[simp]

中文:
定理 trace_one
  结论: trace (1 : QuadraticAlgebra R a b) = 2
  证明: by
  simp [trace_def]

@[simp]

Depends on / 依赖: trace_def
-/
theorem trace_one : trace (1 : QuadraticAlgebra R a b) = 2 := by
  simp [trace_def]

@[simp]
/--
theorem `trace_star` / 定理 `trace_star`

English:
theorem trace_star
  statement: trace (star z) = trace z
  proof: by
  grind [trace_def]

中文:
定理 trace_star
  结论: trace (star z) = trace z
  证明: by
  grind [trace_def]

Depends on / 依赖: trace_def
-/
theorem trace_star : trace (star z) = trace z := by
  grind [trace_def]

/--
theorem `algebraMap_trace_eq_add_star` / 定理 `algebraMap_trace_eq_add_star`

English:
theorem algebraMap_trace_eq_add_star
  proof: by
  ext <;> grind [trace_def]

中文:
定理 algebraMap_trace_eq_add_star
  证明: by
  ext <;> grind [trace_def]

Depends on / 依赖: trace_def
-/
theorem algebraMap_trace_eq_add_star :
    algebraMap R (QuadraticAlgebra R a b) (trace z) = z + star z := by
  ext <;> grind [trace_def]

/--
theorem `star_eq` / 定理 `star_eq`

English:
theorem star_eq
  proof: by
  rw [algebraMap_trace_eq_add_star]; rw [add_sub_cancel_left]

中文:
定理 star_eq
  证明: by
  rw [algebraMap_trace_eq_add_star]; rw [add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, algebraMap_trace_eq_add_star
-/
theorem star_eq :
    star z = algebraMap R (QuadraticAlgebra R a b) (trace z) - z := by
  rw [algebraMap_trace_eq_add_star]; rw [add_sub_cancel_left]

/--
theorem `sq_sub_trace_smul_add_norm_eq_zero` / 定理 `sq_sub_trace_smul_add_norm_eq_zero`

English:
theorem sq_sub_trace_smul_add_norm_eq_zero
  proof: by
  rw [Algebra.smul_def]; rw [algebraMap_trace_eq_add_star]; rw [algebraMap_norm_eq_mul_star]; ring

中文:
定理 sq_sub_trace_smul_add_norm_eq_zero
  证明: by
  rw [Algebra.smul_def]; rw [algebraMap_trace_eq_add_star]; rw [algebraMap_norm_eq_mul_star]; ring

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap_norm_eq_mul_star, algebraMap_trace_eq_add_star, smul_def
-/
theorem sq_sub_trace_smul_add_norm_eq_zero :
    z ^ 2 - trace z • z + algebraMap R _ (norm z) = 0 := by
  rw [Algebra.smul_def]; rw [algebraMap_trace_eq_add_star]; rw [algebraMap_norm_eq_mul_star]; ring

/--
theorem `sq_eq_trace_smul_sub_norm` / 定理 `sq_eq_trace_smul_sub_norm`

English:
theorem sq_eq_trace_smul_sub_norm
  proof: by
  rw [← sub_eq_zero]; rw [← sub_add]; rw [sq_sub_trace_smul_add_norm_eq_zero]

中文:
定理 sq_eq_trace_smul_sub_norm
  证明: by
  rw [← sub_eq_zero]; rw [← sub_add]; rw [sq_sub_trace_smul_add_norm_eq_zero]

Depends on / 依赖: sq_sub_trace_smul_add_norm_eq_zero, sub_add, sub_eq_zero
-/
theorem sq_eq_trace_smul_sub_norm :
    z ^ 2 = trace z • z - algebraMap R _ (norm z) := by
  rw [← sub_eq_zero]; rw [← sub_add]; rw [sq_sub_trace_smul_add_norm_eq_zero]

end trace

section field

variable [Field K] {a b : K} [Hab : Fact (forall r, r ^ 2 != a + b * r)]

/--
lemma `norm_eq_zero_iff_eq_zero` / 引理 `norm_eq_zero_iff_eq_zero`

English:
lemma norm_eq_zero_iff_eq_zero
  given: {z : QuadraticAlgebra K a b}
  proof: by
  constructor
  · intro hz
    rw [norm_def] at hz
    by_cases h : z.im = 0
    · simp [h] at hz
      aesop
    · exfalso
      rw [← pow_two]; rw [sub_eq_zero]; rw [← eq_sub_iff_add_eq] at hz
      apply Hab.out (-z.re / z.im)
      grind
  · intro hz
    simp [hz]

中文:
引理 norm_eq_zero_iff_eq_zero
  条件: {z : QuadraticAlgebra K a b}
  证明: by
  constructor
  · intro hz
    rw [norm_def] at hz
    by_cases h : z.im = 0
    · simp [h] at hz
      aesop
    · exfalso
      rw [← pow_two]; rw [sub_eq_zero]; rw [← eq_sub_iff_add_eq] at hz
      apply Hab.out (-z.re / z.im)
      grind
  · intro hz
    simp [hz]

Depends on / 依赖: Hab.out, eq_sub_iff_add_eq, norm_def, pow_two, sub_eq_zero, z.im, z.re
-/
lemma norm_eq_zero_iff_eq_zero {z : QuadraticAlgebra K a b} :
    norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [norm_def] at hz
    by_cases h : z.im = 0
    · simp [h] at hz
      aesop
    · exfalso
      rw [← pow_two]; rw [sub_eq_zero]; rw [← eq_sub_iff_add_eq] at hz
      apply Hab.out (-z.re / z.im)
      grind
  · intro hz
    simp [hz]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NNRatCast (QuadraticAlgebra K a b)
  body: ⟨q, 0⟩

中文:
实例 :
  签名: NNRatCast (QuadraticAlgebra K a b)
  定义体: ⟨q, 0⟩
-/
@[simps] instance : NNRatCast (QuadraticAlgebra K a b) where nnratCast q := ⟨q, 0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RatCast (QuadraticAlgebra K a b)
  body: ⟨q, 0⟩

中文:
实例 :
  签名: RatCast (QuadraticAlgebra K a b)
  定义体: ⟨q, 0⟩
-/
@[simps] instance : RatCast (QuadraticAlgebra K a b) where ratCast q := ⟨q, 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (QuadraticAlgebra K a b)
  body: (norm z)⁻¹ • star z

中文:
实例 :
  签名: Inv (QuadraticAlgebra K a b)
  定义体: (norm z)⁻¹ • star z
-/
@[simps -isSimp, simps!] instance : Inv (QuadraticAlgebra K a b) where inv z := (norm z)⁻¹ • star z
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (QuadraticAlgebra K a b)
  body: w * z⁻¹

中文:
实例 :
  签名: Div (QuadraticAlgebra K a b)
  定义体: w * z⁻¹
-/
@[simps -isSimp, simps!] instance : Div (QuadraticAlgebra K a b) where div w z := w * z⁻¹

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (QuadraticAlgebra K a b)
  body: by ext <;> simp
  mul_inv_cancel z hz := by
    rw [ne_eq]; rw [← norm_eq_zero_iff_eq_zero] at hz
    simp only [inv_def, Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul]; rw [C_eq_algebraMap]; rw [← algebraMap_norm_eq_mul_star]; rw [← map_mul]; rw [inv_mul_cancel₀ hz]; rw [map_one]
  nnratCast_def q

中文:
实例 :
  签名: Field (QuadraticAlgebra K a b)
  定义体: by ext <;> simp
  mul_inv_cancel z hz := by
    rw [ne_eq]; rw [← norm_eq_zero_iff_eq_zero] at hz
    simp only [inv_def, Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul]; rw [C_eq_algebraMap]; rw [← algebraMap_norm_eq_mul_star]; rw [← map_mul]; rw [inv_mul_cancel₀ hz]; rw [map_one]
  nnratCast_def q

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, C_eq_algebraMap, C_mul_eq_smul, NNRat.cast_def, NNRat.smul_de, Rat.cast_def, algebraMap_norm_eq_mul_star, cast_def, inv_def, map_mul, map_one, mul_inv_cancel, mul_smul_comm, ne_eq, nnqsmul, nnqsmul_def, nnratCast_def, norm_eq_zero_iff_eq_zero, ratCast_def
-/
instance : Field (QuadraticAlgebra K a b) where
  inv_zero := by ext <;> simp
  mul_inv_cancel z hz := by
    rw [ne_eq]; rw [← norm_eq_zero_iff_eq_zero] at hz
    simp only [inv_def, Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul]; rw [C_eq_algebraMap]; rw [← algebraMap_norm_eq_mul_star]; rw [← map_mul]; rw [inv_mul_cancel₀ hz]; rw [map_one]
  nnratCast_def q := by ext <;> simp [sq]; field_simp; simp [NNRat.cast_def]
  ratCast_def q := by ext <;> simp [sq]; field_simp; simp [Rat.cast_def]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext <;> simp [NNRat.smul_def]
  qsmul_def q x := by ext <;> simp [Rat.smul_def]

end field

end QuadraticAlgebra
