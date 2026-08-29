/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Conjugation-negation operator

This file defines the conjugation-negation operator, useful in Fourier analysis.

The way this operator enters the picture is that the adjoint of convolution with a function `f` is
convolution with `conjneg f`.
-/

@[expose] public section

open Function
open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

section CommSemiring
variable [CommSemiring R] [StarRing R] {f g : G -> R}

/--
Definition of `conjneg` / `conjneg` 的定义

English:
definition conjneg
  signature: (f : G -> R)
  body: conj fun x => f (-x)

中文:
定义 conjneg
  签名: (f : G -> R)
  定义体: conj fun x => f (-x)
-/
def conjneg (f : G -> R) : G -> R := conj fun x => f (-x)

/--
lemma `conjneg_apply` / 引理 `conjneg_apply`

English:
lemma conjneg_apply
  given: (f : G -> R) (x : G)
  statement: conjneg f x = conj (f (-x))
  proof: rfl

中文:
引理 conjneg_apply
  条件: (f : G -> R) (x : G)
  结论: conjneg f x = conj (f (-x))
  证明: rfl
-/
@[simp] lemma conjneg_apply (f : G -> R) (x : G) : conjneg f x = conj (f (-x)) := rfl
/--
lemma `conjneg_conjneg` / 引理 `conjneg_conjneg`

English:
lemma conjneg_conjneg
  given: (f : G -> R)
  statement: conjneg (conjneg f) = f
  proof: by ext; simp

中文:
引理 conjneg_conjneg
  条件: (f : G -> R)
  结论: conjneg (conjneg f) = f
  证明: by ext; simp
-/
@[simp] lemma conjneg_conjneg (f : G -> R) : conjneg (conjneg f) = f := by ext; simp

/--
lemma `conjneg_involutive` / 引理 `conjneg_involutive`

English:
lemma conjneg_involutive
  statement: Involutive (conjneg : (G -> R) -> G -> R)
  proof: conjneg_conjneg

中文:
引理 conjneg_involutive
  结论: Involutive (conjneg : (G -> R) -> G -> R)
  证明: conjneg_conjneg

Depends on / 依赖: conjneg_conjneg
-/
lemma conjneg_involutive : Involutive (conjneg : (G -> R) -> G -> R) := conjneg_conjneg
/--
lemma `conjneg_bijective` / 引理 `conjneg_bijective`

English:
lemma conjneg_bijective
  statement: Bijective (conjneg : (G -> R) -> G -> R)
  proof: conjneg_involutive.bijective

中文:
引理 conjneg_bijective
  结论: Bijective (conjneg : (G -> R) -> G -> R)
  证明: conjneg_involutive.bijective

Depends on / 依赖: bijective, conjneg_involutive, conjneg_involutive.bijective
-/
lemma conjneg_bijective : Bijective (conjneg : (G -> R) -> G -> R) := conjneg_involutive.bijective
/--
lemma `conjneg_injective` / 引理 `conjneg_injective`

English:
lemma conjneg_injective
  statement: Injective (conjneg : (G -> R) -> G -> R)
  proof: conjneg_involutive.injective

中文:
引理 conjneg_injective
  结论: Injective (conjneg : (G -> R) -> G -> R)
  证明: conjneg_involutive.injective

Depends on / 依赖: conjneg_involutive, conjneg_involutive.injective, injective
-/
lemma conjneg_injective : Injective (conjneg : (G -> R) -> G -> R) := conjneg_involutive.injective
/--
lemma `conjneg_surjective` / 引理 `conjneg_surjective`

English:
lemma conjneg_surjective
  statement: Surjective (conjneg : (G -> R) -> G -> R)
  proof: conjneg_involutive.surjective

中文:
引理 conjneg_surjective
  结论: Surjective (conjneg : (G -> R) -> G -> R)
  证明: conjneg_involutive.surjective

Depends on / 依赖: conjneg_involutive, conjneg_involutive.surjective, surjective
-/
lemma conjneg_surjective : Surjective (conjneg : (G -> R) -> G -> R) := conjneg_involutive.surjective

/--
lemma `conjneg_inj` / 引理 `conjneg_inj`

English:
lemma conjneg_inj
  statement: conjneg f = conjneg g ↔ f = g
  proof: conjneg_injective.eq_iff

中文:
引理 conjneg_inj
  结论: conjneg f = conjneg g ↔ f = g
  证明: conjneg_injective.eq_iff
-/
@[simp] lemma conjneg_inj : conjneg f = conjneg g ↔ f = g := conjneg_injective.eq_iff
/--
lemma `conjneg_ne_conjneg` / 引理 `conjneg_ne_conjneg`

English:
lemma conjneg_ne_conjneg
  statement: conjneg f != conjneg g ↔ f != g
  proof: conjneg_injective.ne_iff

中文:
引理 conjneg_ne_conjneg
  结论: conjneg f != conjneg g ↔ f != g
  证明: conjneg_injective.ne_iff

Depends on / 依赖: conjneg_injective, conjneg_injective.ne_iff, ne_iff
-/
lemma conjneg_ne_conjneg : conjneg f != conjneg g ↔ f != g := conjneg_injective.ne_iff

/--
lemma `conjneg_conj` / 引理 `conjneg_conj`

English:
lemma conjneg_conj
  given: (f : G -> R)
  statement: conjneg (conj f) = conj (conjneg f)
  proof: rfl

中文:
引理 conjneg_conj
  条件: (f : G -> R)
  结论: conjneg (conj f) = conj (conjneg f)
  证明: rfl
-/
@[simp] lemma conjneg_conj (f : G -> R) : conjneg (conj f) = conj (conjneg f) := rfl

/--
lemma `conjneg_zero` / 引理 `conjneg_zero`

English:
lemma conjneg_zero
  statement: conjneg (0 : G -> R) = 0
  proof: by ext; simp

中文:
引理 conjneg_zero
  结论: conjneg (0 : G -> R) = 0
  证明: by ext; simp
-/
@[simp] lemma conjneg_zero : conjneg (0 : G -> R) = 0 := by ext; simp
/--
lemma `conjneg_one` / 引理 `conjneg_one`

English:
lemma conjneg_one
  statement: conjneg (1 : G -> R) = 1
  proof: by ext; simp

中文:
引理 conjneg_one
  结论: conjneg (1 : G -> R) = 1
  证明: by ext; simp
-/
@[simp] lemma conjneg_one : conjneg (1 : G -> R) = 1 := by ext; simp
/--
lemma `conjneg_add` / 引理 `conjneg_add`

English:
lemma conjneg_add
  given: (f g : G -> R)
  statement: conjneg (f + g) = conjneg f + conjneg g
  proof: by ext; simp

中文:
引理 conjneg_add
  条件: (f g : G -> R)
  结论: conjneg (f + g) = conjneg f + conjneg g
  证明: by ext; simp
-/
@[simp] lemma conjneg_add (f g : G -> R) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
/--
lemma `conjneg_mul` / 引理 `conjneg_mul`

English:
lemma conjneg_mul
  given: (f g : G -> R)
  statement: conjneg (f * g) = conjneg f * conjneg g
  proof: by ext; simp

中文:
引理 conjneg_mul
  条件: (f g : G -> R)
  结论: conjneg (f * g) = conjneg f * conjneg g
  证明: by ext; simp
-/
@[simp] lemma conjneg_mul (f g : G -> R) : conjneg (f * g) = conjneg f * conjneg g := by ext; simp

/--
lemma `conjneg_sum` / 引理 `conjneg_sum`

English:
lemma conjneg_sum
  given: (s : Finset ι) (f : ι -> G -> R)
  proof: by ext; simp

中文:
引理 conjneg_sum
  条件: (s : Finset ι) (f : ι -> G -> R)
  证明: by ext; simp
-/
@[simp] lemma conjneg_sum (s : Finset ι) (f : ι -> G -> R) :
    conjneg (∑ i in s, f i) = ∑ i in s, conjneg (f i) := by ext; simp

/--
lemma `conjneg_prod` / 引理 `conjneg_prod`

English:
lemma conjneg_prod
  given: (s : Finset ι) (f : ι -> G -> R)
  proof: by ext; simp

中文:
引理 conjneg_prod
  条件: (s : Finset ι) (f : ι -> G -> R)
  证明: by ext; simp
-/
@[simp] lemma conjneg_prod (s : Finset ι) (f : ι -> G -> R) :
    conjneg (∏ i in s, f i) = ∏ i in s, conjneg (f i) := by ext; simp

/--
lemma `conjneg_eq_zero` / 引理 `conjneg_eq_zero`

English:
lemma conjneg_eq_zero
  statement: conjneg f = 0 ↔ f = 0
  proof: by
  rw [← conjneg_inj]; rw [conjneg_conjneg]; rw [conjneg_zero]

中文:
引理 conjneg_eq_zero
  结论: conjneg f = 0 ↔ f = 0
  证明: by
  rw [← conjneg_inj]; rw [conjneg_conjneg]; rw [conjneg_zero]
-/
@[simp] lemma conjneg_eq_zero : conjneg f = 0 ↔ f = 0 := by
  rw [← conjneg_inj]; rw [conjneg_conjneg]; rw [conjneg_zero]

/--
lemma `conjneg_eq_one` / 引理 `conjneg_eq_one`

English:
lemma conjneg_eq_one
  statement: conjneg f = 1 ↔ f = 1
  proof: by
  rw [← conjneg_inj]; rw [conjneg_conjneg]; rw [conjneg_one]

中文:
引理 conjneg_eq_one
  结论: conjneg f = 1 ↔ f = 1
  证明: by
  rw [← conjneg_inj]; rw [conjneg_conjneg]; rw [conjneg_one]
-/
@[simp] lemma conjneg_eq_one : conjneg f = 1 ↔ f = 1 := by
  rw [← conjneg_inj]; rw [conjneg_conjneg]; rw [conjneg_one]

/--
lemma `conjneg_ne_zero` / 引理 `conjneg_ne_zero`

English:
lemma conjneg_ne_zero
  statement: conjneg f != 0 ↔ f != 0
  proof: conjneg_eq_zero.not

中文:
引理 conjneg_ne_zero
  结论: conjneg f != 0 ↔ f != 0
  证明: conjneg_eq_zero.not

Depends on / 依赖: conjneg_eq_zero, conjneg_eq_zero.not
-/
lemma conjneg_ne_zero : conjneg f != 0 ↔ f != 0 := conjneg_eq_zero.not
/--
lemma `conjneg_ne_one` / 引理 `conjneg_ne_one`

English:
lemma conjneg_ne_one
  statement: conjneg f != 1 ↔ f != 1
  proof: conjneg_eq_one.not

中文:
引理 conjneg_ne_one
  结论: conjneg f != 1 ↔ f != 1
  证明: conjneg_eq_one.not

Depends on / 依赖: conjneg_eq_one, conjneg_eq_one.not
-/
lemma conjneg_ne_one : conjneg f != 1 ↔ f != 1 := conjneg_eq_one.not

/--
lemma `sum_conjneg` / 引理 `sum_conjneg`

English:
lemma sum_conjneg
  given: [Fintype G] (f : G -> R)
  statement: ∑ a, conjneg f a = ∑ a, conj (f a)
  proof: Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

中文:
引理 sum_conjneg
  条件: [Fintype G] (f : G -> R)
  结论: ∑ a, conjneg f a = ∑ a, conj (f a)
  证明: Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

Depends on / 依赖: Equiv.neg, Fintype, Fintype.sum_equiv, sum_equiv
-/
lemma sum_conjneg [Fintype G] (f : G -> R) : ∑ a, conjneg f a = ∑ a, conj (f a) :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

/--
lemma `support_conjneg` / 引理 `support_conjneg`

English:
lemma support_conjneg
  given: (f : G -> R)
  statement: support (conjneg f) = -support f
  proof: by
  ext; simp [starRingEnd_apply]

中文:
引理 support_conjneg
  条件: (f : G -> R)
  结论: support (conjneg f) = -support f
  证明: by
  ext; simp [starRingEnd_apply]
-/
@[simp] lemma support_conjneg (f : G -> R) : support (conjneg f) = -support f := by
  ext; simp [starRingEnd_apply]

/--
Definition of `conjnegRingHom` / `conjnegRingHom` 的定义

English:
definition conjnegRingHom
  signature: : (G -> R) ->+* (G -> R) where
  body: conjneg
  map_zero' := conjneg_zero
  map_one' := conjneg_one
  map_add' := conjneg_add
  map_mul' := conjneg_mul

中文:
定义 conjnegRingHom
  签名: : (G -> R) ->+* (G -> R) where
  定义体: conjneg
  map_zero' := conjneg_zero
  map_one' := conjneg_one
  map_add' := conjneg_add
  map_mul' := conjneg_mul
-/
@[simps] def conjnegRingHom : (G -> R) ->+* (G -> R) where
  toFun := conjneg
  map_zero' := conjneg_zero
  map_one' := conjneg_one
  map_add' := conjneg_add
  map_mul' := conjneg_mul

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R]

/--
lemma `conjneg_sub` / 引理 `conjneg_sub`

English:
lemma conjneg_sub
  given: (f g : G -> R)
  statement: conjneg (f - g) = conjneg f - conjneg g
  proof: by ext; simp

中文:
引理 conjneg_sub
  条件: (f g : G -> R)
  结论: conjneg (f - g) = conjneg f - conjneg g
  证明: by ext; simp
-/
@[simp] lemma conjneg_sub (f g : G -> R) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
/--
lemma `conjneg_neg` / 引理 `conjneg_neg`

English:
lemma conjneg_neg
  given: (f : G -> R)
  statement: conjneg (-f) = -conjneg f
  proof: by ext; simp

中文:
引理 conjneg_neg
  条件: (f : G -> R)
  结论: conjneg (-f) = -conjneg f
  证明: by ext; simp
-/
@[simp] lemma conjneg_neg (f : G -> R) : conjneg (-f) = -conjneg f := by ext; simp

end CommRing
