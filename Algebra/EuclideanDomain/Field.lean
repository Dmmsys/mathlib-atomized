/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Instances for Euclidean domains

* `Field.toEuclideanDomain`: shows that any field is a Euclidean domain.
-/

public section

namespace Field

variable {K : Type*} [Field K]

-- see Note [lower instance priority]
instance (priority := 100) toEuclideanDomain : EuclideanDomain K :=
{ toCommRing := toCommRing
  quotient := (· / ·), remainder := fun a b => a - a * b / b, quotient_zero := div_zero,
  quotient_mul_add_remainder_eq := fun a b => by
    by_cases h : b = 0 <;> simp [h, mul_div_cancel₀]
  r := fun a b => a = 0 ∧ b != 0,
  r_wellFounded :=
    WellFounded.intro fun _ =>
(Acc.intro _) fun _ ⟨hb, _⟩ => (Acc.intro _) fun _ ⟨_, hnb⟩ => False.elim hnb hb,
  remainder_lt := fun a b hnb => by simp [hnb],
  mul_left_not_lt := fun _ _ hnb ⟨hab, hna⟩ => Or.casesOn (mul_eq_zero.1 hab) hna hnb }

@[simp]
/--
theorem `mod_eq` / 定理 `mod_eq`

English:
theorem mod_eq
  given: (a b : K)
  statement: a % b = a - a * b / b
  proof: rfl

@[simp]

中文:
定理 mod_eq
  条件: (a b : K)
  结论: a % b = a - a * b / b
  证明: rfl

@[simp]
-/
protected theorem mod_eq (a b : K) : a % b = a - a * b / b := rfl

@[simp]
/--
theorem `gcd_eq` / 定理 `gcd_eq`

English:
theorem gcd_eq
  given: [DecidableEq K] (a b : K)
  proof: by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]

中文:
定理 gcd_eq
  条件: [DecidableEq K] (a b : K)
  证明: by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]
-/
protected theorem gcd_eq [DecidableEq K] (a b : K) :
    EuclideanDomain.gcd a b = if a = 0 then b else a := by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]

/--
theorem `gcd_zero_eq` / 定理 `gcd_zero_eq`

English:
theorem gcd_zero_eq
  given: [DecidableEq K] (b : K)
  proof: by
  rw [Field.gcd_eq]; rw [if_pos rfl]

中文:
定理 gcd_zero_eq
  条件: [DecidableEq K] (b : K)
  证明: by
  rw [Field.gcd_eq]; rw [if_pos rfl]
-/
protected theorem gcd_zero_eq [DecidableEq K] (b : K) :
    EuclideanDomain.gcd 0 b = b := by
  rw [Field.gcd_eq]; rw [if_pos rfl]

/--
theorem `gcd_eq_of_ne` / 定理 `gcd_eq_of_ne`

English:
theorem gcd_eq_of_ne
  given: [DecidableEq K] {a : K} (ha : a != 0) (b : K)
  proof: by
  rw [Field.gcd_eq]; rw [if_neg ha]

中文:
定理 gcd_eq_of_ne
  条件: [DecidableEq K] {a : K} (ha : a != 0) (b : K)
  证明: by
  rw [Field.gcd_eq]; rw [if_neg ha]
-/
protected theorem gcd_eq_of_ne [DecidableEq K] {a : K} (ha : a != 0) (b : K) :
    EuclideanDomain.gcd a b = a := by
  rw [Field.gcd_eq]; rw [if_neg ha]

end Field
