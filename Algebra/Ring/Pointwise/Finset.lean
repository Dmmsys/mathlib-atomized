/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Pointwise.Set
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists MulAction

open scoped Pointwise

namespace Finset
variable {α β : Type*}

/-- `Finset α` has distributive negation if `α` has. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def distribNeg [DecidableEq α] [Mul α] [HasDistribNeg α]
  body: coe_injective.hasDistribNeg _ coe_neg coe_mul

scoped[Pointwise] attribute [instance] Finset.distribNeg

中文:
定义 noncomputable
  签名: def distribNeg [DecidableEq α] [乘法 α] [有DistribNeg α]
  定义体: coe_injective.hasDistribNeg _ coe_neg coe_mul

scoped[Pointwise] attribute [instance] Finset.distribNeg

Depends on / 依赖: Unique
-/
protected noncomputable def distribNeg [DecidableEq α] [Mul α] [HasDistribNeg α] :
    HasDistribNeg (Finset α) :=
  coe_injective.hasDistribNeg _ coe_neg coe_mul

scoped[Pointwise] attribute [instance] Finset.distribNeg

section Distrib
variable [DecidableEq α] [Distrib α] (s t u : Finset α)


/--
lemma `mul_add_subset` / 引理 `mul_add_subset`

English:
lemma mul_add_subset
  statement: s * (t + u) subseteq s * t + s * u
  proof: image₂_distrib_subset_left mul_add

中文:
引理 mul_add_subset
  结论: s * (t + u) subseteq s * t + s * u
  证明: image₂_distrib_subset_left mul_add

Depends on / 依赖: mul_add
-/
lemma mul_add_subset : s * (t + u) subseteq s * t + s * u :=
  image₂_distrib_subset_left mul_add

/--
lemma `add_mul_subset` / 引理 `add_mul_subset`

English:
lemma add_mul_subset
  statement: (s + t) * u subseteq s * u + t * u
  proof: image₂_distrib_subset_right add_mul

中文:
引理 add_mul_subset
  结论: (s + t) * u subseteq s * u + t * u
  证明: image₂_distrib_subset_right add_mul

Depends on / 依赖: Ideal.Quotient.mk_surjective, IsPreimmersion, IsPreimmersion.mk_SpecMap, PrimeSpectrum, PrimeSpectrum.isClosedEmbedding_comap_of_surjective, Quotient, RingHom, RingHom.surjectiveOnStalks_of_surjective, add_mul, isClosedEmbedding_comap_of_surjective, isEmbedding, mk_SpecMap, mk_surjective, surjectiveOnStalks_of_surjective
-/
lemma add_mul_subset : (s + t) * u subseteq s * u + t * u :=
  image₂_distrib_subset_right add_mul

end Distrib
end Finset
