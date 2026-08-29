/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Subrings of local rings

We prove basic properties of subrings of local rings.
-/

public section

namespace IsLocalRing

variable {R S} [Semiring R] [Semiring S]

open nonZeroDivisors

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  statement: [IsLocalRing S] {f : R ->+* S} (hf : Function.Injective f)
  proof: by
  have : Nontrivial R := f.domain_nontrivial
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab =>
    (IsLocalRing.isUnit_or_isUnit_of_add_one (map_add f .. ▸ map_one f ▸ congrArg f hab)).imp ?_ ?_
  <;> exact h _ ∘ mem_nonZeroDivisors_of_injective hf ∘ IsUnit.mem_nonZeroDivisors

中文:
定理 of_injective
  结论: [是局部环 S] {f : R ->+* S} (hf : 函数.单射 f)
  证明: by
  have : Nontrivial R := f.domain_nontrivial
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab =>
    (IsLocalRing.isUnit_or_isUnit_of_add_one (map_add f .. ▸ map_one f ▸ congrArg f hab)).imp ?_ ?_
  <;> exact h _ ∘ mem_nonZeroDivisors_of_injective hf ∘ IsUnit.mem_nonZeroDivisors

Depends on / 依赖: IsLocalRing, IsLocalRing.isUnit_or_isUnit_of_add_one, IsUnit, IsUnit.mem_nonZeroDivisors, Nontrivial, domain_nontrivial, f.domain_nontrivial, isUnit_or_isUnit_of_add_one, map_add, map_one, mem_nonZeroDivisors, mem_nonZeroDivisors_of_injective, of_is_unit_or_is_unit_of_add_one
-/
theorem of_injective [IsLocalRing S] {f : R ->+* S} (hf : Function.Injective f)
    (h : forall a, a in R⁰ -> IsUnit a) : IsLocalRing R := by
  have : Nontrivial R := f.domain_nontrivial
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab =>
    (IsLocalRing.isUnit_or_isUnit_of_add_one (map_add f .. ▸ map_one f ▸ congrArg f hab)).imp ?_ ?_
  <;> exact h _ ∘ mem_nonZeroDivisors_of_injective hf ∘ IsUnit.mem_nonZeroDivisors

/--
theorem `of_subring` / 定理 `of_subring`

English:
theorem of_subring
  given: [IsLocalRing S] {R : Subsemiring S} (h : forall a, a in R⁰ -> IsUnit a)
  proof: of_injective R.subtype_injective h

中文:
定理 of_subring
  条件: [是局部环 S] {R : 子半环 S} (h : 对任意 a, a in R⁰ -> 是单位 a)
  证明: of_injective R.subtype_injective h

Depends on / 依赖: R.subtype_injective, of_injective, subtype_injective
-/
theorem of_subring [IsLocalRing S] {R : Subsemiring S} (h : forall a, a in R⁰ -> IsUnit a) :
    IsLocalRing R :=
  of_injective R.subtype_injective h

/--
theorem `of_subring'` / 定理 `of_subring'`

English:
theorem of_subring'
  statement: {R R' : Subsemiring S} [IsLocalRing R'] (inc : R <= R')
  proof: of_injective (Subsemiring.inclusion_injective inc) h

中文:
定理 of_subring'
  结论: {R R' : 子半环 S} [是局部环 R'] (inc : R <= R')
  证明: of_injective (Subsemiring.inclusion_injective inc) h

Depends on / 依赖: Subsemiring, Subsemiring.inclusion_injective, inclusion_injective, of_injective
-/
theorem of_subring' {R R' : Subsemiring S} [IsLocalRing R'] (inc : R <= R')
    (h : forall a, a in R⁰ -> IsUnit a) : IsLocalRing R :=
  of_injective (Subsemiring.inclusion_injective inc) h

end IsLocalRing
