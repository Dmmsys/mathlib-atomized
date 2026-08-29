/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of `IsScalarTower`

We prove that given `IsScalarTower F K A`, if `A` is finite as a module over `F` then
`A` is finite over `K`, and
(as long as `A` is Noetherian over `F` and torsion-free over `K`) `K` is finite over `F`.

In particular these conditions hold when `A`, `F`, and `K` are fields.

The formulas for the dimensions are given elsewhere by `Module.finrank_mul_finrank`.

## Tags

tower law

-/

public section


universe u v w u₁ v₁ w₁

open Cardinal Submodule

variable (F : Type u) (K : Type v) (A : Type w)

namespace Module.Finite

variable [Ring F] [Ring K] [Module F K]
  [AddCommGroup A] [Module K A] [Module.IsTorsionFree K A]
  [Module F A] [IsNoetherian F A] [IsScalarTower F K A] in
/--
theorem `left` / 定理 `left`

English:
theorem left
  given: [IsDomain K] [Nontrivial A]
  statement: Module.Finite F K
  proof: let ⟨x, hx⟩ := exists_ne (0 : A)
  Module.Finite.of_injective
    (LinearMap.ringLmapEquivSelf K Nat A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)

中文:
定理 left
  条件: [是整环 K] [非平凡 A]
  结论: 模.有限 F K
  证明: let ⟨x, hx⟩ := exists_ne (0 : A)
  Module.Finite.of_injective
    (LinearMap.ringLmapEquivSelf K Nat A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)

Depends on / 依赖: Finite, LinearMap, LinearMap.ringLmapEquivSelf, Module, Module.Finite.of_injective, exists_ne, of_injective, restrictScalars, ringLmapEquivSelf, smul_left_injective
-/
theorem left [IsDomain K] [Nontrivial A] : Module.Finite F K :=
  let ⟨x, hx⟩ := exists_ne (0 : A)
  Module.Finite.of_injective
    (LinearMap.ringLmapEquivSelf K Nat A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)

variable [Semiring F] [Semiring K] [Module F K]
  [AddCommMonoid A] [Module K A] [Module F A] [IsScalarTower F K A] in
@[stacks 09G5]
/--
theorem `right` / 定理 `right`

English:
theorem right
  given: [hf : Module.Finite F A]
  statement: Module.Finite K A
  proof: let ⟨⟨b, hb⟩⟩ := hf
⟨⟨b, Submodule.restrictScalars_injective F _ _ by
    rw [Submodule.restrictScalars_top]; rw [eq_top_iff]; rw [← hb]; rw [Submodule.span_le]
    exact Submodule.subset_span⟩⟩

中文:
定理 right
  条件: [hf : 模.有限 F A]
  结论: 模.有限 K A
  证明: let ⟨⟨b, hb⟩⟩ := hf
⟨⟨b, Submodule.restrictScalars_injective F _ _ by
    rw [Submodule.restrictScalars_top]; rw [eq_top_iff]; rw [← hb]; rw [Submodule.span_le]
    exact Submodule.subset_span⟩⟩

Depends on / 依赖: Submodule, Submodule.restrictScalars_injective, Submodule.restrictScalars_top, Submodule.span_le, Submodule.subset_span, eq_top_iff, restrictScalars_injective, restrictScalars_top, span_le, subset_span
-/
theorem right [hf : Module.Finite F A] : Module.Finite K A :=
  let ⟨⟨b, hb⟩⟩ := hf
⟨⟨b, Submodule.restrictScalars_injective F _ _ by
    rw [Submodule.restrictScalars_top]; rw [eq_top_iff]; rw [← hb]; rw [Submodule.span_le]
    exact Submodule.subset_span⟩⟩

end Module.Finite

alias FiniteDimensional.left := Module.Finite.left
alias FiniteDimensional.right := Module.Finite.right
