/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Lifting monoid algebras

This file defines `liftNC`. For the definition of `MonoidAlgebra.lift`, see
`Mathlib/Algebra/MonoidAlgebra/Basic.lean`.

## Main results
* `MonoidAlgebra.liftNC`, `AddMonoidAlgebra.liftNC`: lift a homomorphism `f : k →+ R` and a
  function `g : G → R` to a homomorphism `k[G] →+ R`.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

/--
Definition of `liftNC` / `liftNC` 的定义

English:
definition liftNC
  signature: (f : k ->+ R) (g : G -> R)
  body: (liftAddHom fun x => .comp (.mulRight (g x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]

中文:
定义 liftNC
  签名: (f : k ->+ R) (g : G -> R)
  定义体: (liftAddHom fun x => .comp (.mulRight (g x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.toAddMonoidHom, liftAddHom, mulRight, toAddMonoidHom
-/
def liftNC (f : k ->+ R) (g : G -> R) : k[G] ->+ R :=
  (liftAddHom fun x => .comp (.mulRight (g x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]
/--
theorem `liftNC_single` / 定理 `liftNC_single`

English:
theorem liftNC_single
  given: (f : k ->+ R) (g : G -> R) (a : G) (b : k)
  proof: liftAddHom_apply_single _ _ _

中文:
定理 liftNC_single
  条件: (f : k ->+ R) (g : G -> R) (a : G) (b : k)
  证明: liftAddHom_apply_single _ _ _

Depends on / 依赖: liftAddHom_apply_single
-/
theorem liftNC_single (f : k ->+ R) (g : G -> R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g a :=
  liftAddHom_apply_single _ _ _

end

section Mul

variable [Semiring k] [Mul G] [Semiring R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftNC_mul` / 定理 `liftNC_mul`

English:
theorem liftNC_mul
  statement: {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R]
  proof: by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

中文:
定理 liftNC_mul
  结论: {g_hom : 类型} [函数状 g_hom G R] [乘法态射类 g_hom G R]
  证明: by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

Depends on / 依赖: Finset, Finset.sum_congr, Finsupp, Finsupp.mul_sum, Finsupp.sum_mul, conv_rhs, h_comm, left_comm, liftNC_single, map_finsuppSum, mul_assoc, mul_def, mul_sum, simp_rw, sum_coeff_single, sum_congr, sum_mul
-/
theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R]
    (f : k ->+* R) (g : g_hom) (a b : k[G])
    (h_comm : forall {x y}, y in a.coeff.support -> Commute (f (b.coeff x)) (g y)) :
    liftNC (f : k ->+ R) g (a * b) = liftNC (f : k ->+ R) g a * liftNC (f : k ->+ R) g b := by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

end Mul

section One

variable [NonAssocSemiring R] [Semiring k] [One G]

@[simp]
/--
theorem `liftNC_one` / 定理 `liftNC_one`

English:
theorem liftNC_one
  statement: {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R]
  proof: by simp [one_def]

中文:
定理 liftNC_one
  结论: {g_hom : 类型} [函数状 g_hom G R] [幺态射类 g_hom G R]
  证明: by simp [one_def]

Depends on / 依赖: one_def
-/
theorem liftNC_one {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R]
    (f : k ->+* R) (g : g_hom) :
    liftNC (f : k ->+ R) g 1 = 1 := by simp [one_def]

end One

/-! #### Semiring structure -/
section Semiring

variable [Semiring k] [Monoid G] [Semiring R] [Semiring S] [Semiring T] [Monoid M]

/--
Definition of `liftNCRingHom` / `liftNCRingHom` 的定义

English:
definition liftNCRingHom
  signature: (f : k ->+* R) (g : G ->* R) (h_comm : forall x y, Commute (f x) (g y))
  body: { liftNC (f : k ->+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]

中文:
定义 liftNCRingHom
  签名: (f : k ->+* R) (g : G ->* R) (h_comm : 对任意 x y, Commute (f x) (g y))
  定义体: { liftNC (f : k ->+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]

Depends on / 依赖: h_comm, liftNC, liftNC_mul, liftNC_one, map_mul, map_one
-/
def liftNCRingHom (f : k ->+* R) (g : G ->* R) (h_comm : forall x y, Commute (f x) (g y)) : k[G] ->+* R :=
  { liftNC (f : k ->+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]
/--
lemma `liftNCRingHom_single` / 引理 `liftNCRingHom_single`

English:
lemma liftNCRingHom_single
  given: (f : k ->+* R) (g : G ->* R) (h_comm) (a : G) (b : k)
  proof: liftNC_single _ _ _ _

中文:
引理 liftNCRingHom_single
  条件: (f : k ->+* R) (g : G ->* R) (h_comm) (a : G) (b : k)
  证明: liftNC_single _ _ _ _

Depends on / 依赖: liftNC_single
-/
lemma liftNCRingHom_single (f : k ->+* R) (g : G ->* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end Semiring

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

/--
Definition of `liftNC` / `liftNC` 的定义

English:
definition liftNC
  signature: (f : k ->+ R) (g : Multiplicative G -> R)
  body: (liftAddHom fun x => .comp (.mulRight (g <| .ofAdd x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]

中文:
定义 liftNC
  签名: (f : k ->+ R) (g : Multiplicative G -> R)
  定义体: (liftAddHom fun x => .comp (.mulRight (g <| .ofAdd x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.toAddMonoidHom, liftAddHom, mulRight, toAddMonoidHom
-/
def liftNC (f : k ->+ R) (g : Multiplicative G -> R) : k[G] ->+ R :=
  (liftAddHom fun x => .comp (.mulRight (g <| .ofAdd x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]
/--
theorem `liftNC_single` / 定理 `liftNC_single`

English:
theorem liftNC_single
  given: (f : k ->+ R) (g : Multiplicative G -> R) (a : G) (b : k)
  proof: liftAddHom_apply_single _ _ _

中文:
定理 liftNC_single
  条件: (f : k ->+ R) (g : Multiplicative G -> R) (a : G) (b : k)
  证明: liftAddHom_apply_single _ _ _

Depends on / 依赖: liftAddHom_apply_single
-/
theorem liftNC_single (f : k ->+ R) (g : Multiplicative G -> R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g (Multiplicative.ofAdd a) :=
  liftAddHom_apply_single _ _ _

end

section Mul

variable [Semiring k] [Add G] [Semiring R]

/--
theorem `liftNC_mul` / 定理 `liftNC_mul`

English:
theorem liftNC_mul
  statement: {g_hom : Type*}
  proof: by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

中文:
定理 liftNC_mul
  结论: {g_hom : 类型}
  证明: by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

Depends on / 依赖: Finset, Finset.sum_congr, Finsupp, Finsupp.mul_sum, Finsupp.sum_mul, conv_rhs, h_comm, left_comm, liftNC_single, map_finsuppSum, mul_assoc, mul_def, mul_sum, simp_rw, sum_coeff_single, sum_congr, sum_mul
-/
theorem liftNC_mul {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [MulHomClass g_hom (Multiplicative G) R]
    (f : k ->+* R) (g : g_hom) (a b : k[G])
    (h_comm : forall {x y}, y in a.coeff.support -> Commute (f (b.coeff x)) (g <| .ofAdd y)) :
    liftNC (f : k ->+ R) g (a * b) = liftNC (f : k ->+ R) g a * liftNC (f : k ->+ R) g b := by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

end Mul

section One

variable [Semiring k] [Zero G] [NonAssocSemiring R]

@[simp]
/--
theorem `liftNC_one` / 定理 `liftNC_one`

English:
theorem liftNC_one
  statement: {g_hom : Type*}
  proof: MonoidAlgebra.liftNC_one f g

中文:
定理 liftNC_one
  结论: {g_hom : 类型}
  证明: MonoidAlgebra.liftNC_one f g

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.liftNC_one, liftNC_one
-/
theorem liftNC_one {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [OneHomClass g_hom (Multiplicative G) R]
    (f : k ->+* R) (g : g_hom) : liftNC (f : k ->+ R) g 1 = 1 :=
  MonoidAlgebra.liftNC_one f g

end One

/-! #### Semiring structure -/
section Semiring

variable [Semiring k] [AddMonoid G] [Semiring R] [Semiring S] [Semiring T] [AddMonoid M]

/--
Definition of `liftNCRingHom` / `liftNCRingHom` 的定义

English:
definition liftNCRingHom
  signature: (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm : forall x y, Commute (f x) (g y))
  body: { liftNC (f : k ->+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]

中文:
定义 liftNCRingHom
  签名: (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm : 对任意 x y, Commute (f x) (g y))
  定义体: { liftNC (f : k ->+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]

Depends on / 依赖: h_comm, liftNC, liftNC_mul, liftNC_one, map_mul, map_one
-/
def liftNCRingHom (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm : forall x y, Commute (f x) (g y)) :
    k[G] ->+* R :=
  { liftNC (f : k ->+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]
/--
lemma `liftNCRingHom_single` / 引理 `liftNCRingHom_single`

English:
lemma liftNCRingHom_single
  given: (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm) (a : G) (b : k)
  proof: liftNC_single _ _ _ _

中文:
引理 liftNCRingHom_single
  条件: (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm) (a : G) (b : k)
  证明: liftNC_single _ _ _ _

Depends on / 依赖: liftNC_single
-/
lemma liftNCRingHom_single (f : k ->+* R) (g : Multiplicative G ->* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g (.ofAdd a) :=
  liftNC_single _ _ _ _

end Semiring

end AddMonoidAlgebra
