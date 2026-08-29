/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists MulAction IsOrderedMonoid Field

open Function
open scoped Pointwise

variable {α : Type*}

namespace Set

/-- `Set α` has distributive negation if `α` has. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def hasDistribNeg [Mul α] [HasDistribNeg α]
  body: Set.involutiveNeg
  neg_mul _ _ := by simp_rw [← image_neg_eq_neg]; exact image2_image_left_comm neg_mul
  mul_neg _ _ := by simp_rw [← image_neg_eq_neg]; exact image_image2_right_comm mul_neg

scoped[Pointwise] attribute [instance] Set.hasDistribNeg

中文:
定义 noncomputable
  签名: def hasDistribNeg [Mul α] [HasDistribNeg α]
  定义体: Set.involutiveNeg
  neg_mul _ _ := by simp_rw [← image_neg_eq_neg]; exact image2_image_left_comm neg_mul
  mul_neg _ _ := by simp_rw [← image_neg_eq_neg]; exact image_image2_right_comm mul_neg

scoped[Pointwise] attribute [instance] Set.hasDistribNeg
-/
protected noncomputable def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) where
  __ := Set.involutiveNeg
  neg_mul _ _ := by simp_rw [← image_neg_eq_neg]; exact image2_image_left_comm neg_mul
  mul_neg _ _ := by simp_rw [← image_neg_eq_neg]; exact image_image2_right_comm mul_neg

scoped[Pointwise] attribute [instance] Set.hasDistribNeg

section Distrib
variable [Distrib α] (s t u : Set α)


/--
lemma `mul_add_subset` / 引理 `mul_add_subset`

English:
lemma mul_add_subset
  statement: s * (t + u) subseteq s * t + s * u
  proof: image2_distrib_subset_left mul_add

中文:
引理 mul_add_subset
  结论: s * (t + u) subseteq s * t + s * u
  证明: image2_distrib_subset_left mul_add

Depends on / 依赖: image2_distrib_subset_left, mul_add
-/
lemma mul_add_subset : s * (t + u) subseteq s * t + s * u := image2_distrib_subset_left mul_add
/--
lemma `add_mul_subset` / 引理 `add_mul_subset`

English:
lemma add_mul_subset
  statement: (s + t) * u subseteq s * u + t * u
  proof: image2_distrib_subset_right add_mul

中文:
引理 add_mul_subset
  结论: (s + t) * u subseteq s * u + t * u
  证明: image2_distrib_subset_right add_mul

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, X.residue_surjective, add_mul, epi_of_surjective, image2_distrib_subset_right, residue_surjective
-/
lemma add_mul_subset : (s + t) * u subseteq s * u + t * u := image2_distrib_subset_right add_mul

end Distrib
end Set
