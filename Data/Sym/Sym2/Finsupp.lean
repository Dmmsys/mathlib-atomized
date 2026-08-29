/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finsupp.Defs

/-!
# Finitely supported functions from the symmetric square

This file lifts functions `α →₀ M₀` to functions `Sym2 α →₀ M₀` by precomposing with multiplication.
-/

@[expose] public section

open Sym2

variable {α M₀ : Type*} [CommMonoidWithZero M₀] {f : α ->₀ M₀}

namespace Finsupp

/--
lemma `sym2_support_eq_preimage_support_mul` / 引理 `sym2_support_eq_preimage_support_mul`

English:
lemma sym2_support_eq_preimage_support_mul
  given: [NoZeroDivisors M₀] (f : α ->₀ M₀)
  proof: by ext ⟨a, b⟩; simp

中文:
引理 sym2_support_eq_preimage_support_mul
  条件: [NoZeroDivisors M₀] (f : α ->₀ M₀)
  证明: by ext ⟨a, b⟩; simp
-/
lemma sym2_support_eq_preimage_support_mul [NoZeroDivisors M₀] (f : α ->₀ M₀) :
    f.support.sym2 = map f ⁻¹' mul.support := by ext ⟨a, b⟩; simp

/--
lemma `mem_sym2_support_of_mul_ne_zero` / 引理 `mem_sym2_support_of_mul_ne_zero`

English:
lemma mem_sym2_support_of_mul_ne_zero
  given: (p : Sym2 α) (hp : mul (p.map f) != 0)
  proof: by
  obtain ⟨a, b⟩ := p
  simp only [map_mk, mul_mk, ne_eq] at hp
  simpa using .intro (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)

中文:
引理 mem_sym2_support_of_mul_ne_zero
  条件: (p : Sym2 α) (hp : mul (p.map f) != 0)
  证明: by
  obtain ⟨a, b⟩ := p
  simp only [map_mk, mul_mk, ne_eq] at hp
  simpa using .intro (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)

Depends on / 依赖: left_ne_zero_of_mul, map_mk, mul_mk, ne_eq, right_ne_zero_of_mul
-/
lemma mem_sym2_support_of_mul_ne_zero (p : Sym2 α) (hp : mul (p.map f) != 0) :
    p in f.support.sym2 := by
  obtain ⟨a, b⟩ := p
  simp only [map_mk, mul_mk, ne_eq] at hp
  simpa using .intro (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)

/--
Definition of `sym2Mul` / `sym2Mul` 的定义

English:
definition sym2Mul
  signature: (f : α ->₀ M₀)
  body: .onFinset f.support.sym2 (fun p => mul (p.map f)) mem_sym2_support_of_mul_ne_zero

中文:
定义 sym2Mul
  签名: (f : α ->₀ M₀)
  定义体: .onFinset f.support.sym2 (fun p => mul (p.map f)) mem_sym2_support_of_mul_ne_zero

Depends on / 依赖: f.support.sym2, mem_sym2_support_of_mul_ne_zero, onFinset, p.map, support
-/
noncomputable def sym2Mul (f : α ->₀ M₀) : Sym2 α ->₀ M₀ :=
  .onFinset f.support.sym2 (fun p => mul (p.map f)) mem_sym2_support_of_mul_ne_zero

/--
lemma `support_sym2Mul_subset` / 引理 `support_sym2Mul_subset`

English:
lemma support_sym2Mul_subset
  statement: f.sym2Mul.support subseteq f.support.sym2
  proof: support_onFinset_subset

中文:
引理 support_sym2Mul_subset
  结论: f.sym2Mul.support subseteq f.support.sym2
  证明: support_onFinset_subset

Depends on / 依赖: support_onFinset_subset
-/
lemma support_sym2Mul_subset : f.sym2Mul.support subseteq f.support.sym2 := support_onFinset_subset

/--
lemma `coe_sym2Mul` / 引理 `coe_sym2Mul`

English:
lemma coe_sym2Mul
  given: (f : α ->₀ M₀)
  statement: f.sym2Mul = mul ∘ map f
  proof: rfl

中文:
引理 coe_sym2Mul
  条件: (f : α ->₀ M₀)
  结论: f.sym2Mul = mul ∘ map f
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sym2Mul (f : α ->₀ M₀) : f.sym2Mul = mul ∘ map f := rfl

/--
lemma `sym2Mul_apply_mk` / 引理 `sym2Mul_apply_mk`

English:
lemma sym2Mul_apply_mk
  given: (a b : α)
  statement: f.sym2Mul s(a, b) = f a * f b
  proof: rfl

中文:
引理 sym2Mul_apply_mk
  条件: (a b : α)
  结论: f.sym2Mul s(a, b) = f a * f b
  证明: rfl
-/
lemma sym2Mul_apply_mk (a b : α) : f.sym2Mul s(a, b) = f a * f b := rfl

end Finsupp
