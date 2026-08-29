/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Finset.SMulAntidiagonal

/-!
# Scalar multiplication by (additive) monoid rings on formal functions.

Given sets `G` and `P`, with a left-cancellative scalar-multiplication (or vector-addition) of `G`
on `P`, together with a module `V` over a semiring `R`, we define a convolution action of the monoid
algebra `R[G]` on the set of functions `P → V`.

-/

@[expose] public section

noncomputable section

variable {G P R V : Type*}

namespace MonoidAlgebra

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive]
/--
theorem `mem_smulAntidiagonal_of_group` / 定理 `mem_smulAntidiagonal_of_group`

English:
theorem mem_smulAntidiagonal_of_group
  statement: [Group G] [MulAction G P] [Semiring R] [Zero V]
  proof: by
  rw [Finset.mem_smulAntidiagonal]; rw [eq_inv_smul_iff]; rw [Function.mem_support]; rw [Finset.mem_coe]; rw [Finsupp.mem_support_iff]

中文:
定理 mem_smulAntidiagonal_of_group
  结论: [Group G] [MulAction G P] [Semiring R] [Zero V]
  证明: by
  rw [Finset.mem_smulAntidiagonal]; rw [eq_inv_smul_iff]; rw [Function.mem_support]; rw [Finset.mem_coe]; rw [Finsupp.mem_support_iff]

Depends on / 依赖: Finset, Finset.mem_coe, Finset.mem_smulAntidiagonal, Finsupp, Finsupp.mem_support_iff, Function, Function.mem_support, eq_inv_smul_iff, mem_coe, mem_smulAntidiagonal, mem_support, mem_support_iff
-/
theorem mem_smulAntidiagonal_of_group [Group G] [MulAction G P] [Semiring R] [Zero V]
    (f : R[G]) (x : P -> V) (p : P) (gh : G × P) :
    gh in Finset.SMulAntidiagonal p
      (Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p) ↔
      f.coeff gh.1 != 0 ∧ x gh.2 != 0 ∧ gh.2 = gh.1⁻¹ • p := by
  rw [Finset.mem_smulAntidiagonal]; rw [eq_inv_smul_iff]; rw [Function.mem_support]; rw [Finset.mem_coe]; rw [Finsupp.mem_support_iff]

/-- A convolution-type scalar multiplication of the monoid algebra on the set of formal
functions. -/
@[to_additive (dont_translate := R) /-- A convolution-type scalar multiplication of the additive
monoid algebra on the set of formal functions. -/]
scoped instance [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] :
    SMul (R[G]) (P -> V) where
  smul f x p := ∑ gh in Finset.SMulAntidiagonal p
    (Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p),
      f.coeff gh.1 • x gh.2

@[to_additive (dont_translate := R) smul_eq]
/--
theorem `smul_eq` / 定理 `smul_eq`

English:
theorem smul_eq
  statement: [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
  proof: rfl

@[to_additive (dont_translate := R) smul_apply_addAction]

中文:
定理 smul_eq
  结论: [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
  证明: rfl

@[to_additive (dont_translate := R) smul_apply_addAction]

Depends on / 依赖: Finset, Finset.SMulAntidiagonal, SMulAntidiagonal, Set.SMulAntidiagonal.finite_of_finite_fst, f.coeff, f.coeff.support.finite_toSet, finite_of_finite_fst, finite_toSet, support, x.support
-/
theorem smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
    (f : R[G]) (x : P -> V) (p : P)
    (hp : ((f.coeff.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
      Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p) :
    (f • x) p = ∑ gh in Finset.SMulAntidiagonal p hp, f.coeff gh.1 • x gh.2 :=
  rfl

@[to_additive (dont_translate := R) smul_apply_addAction]
/--
theorem `smul_apply_mulAction` / 定理 `smul_apply_mulAction`

English:
theorem smul_apply_mulAction
  statement: [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
  proof: by
  have hp : ((f.coeff.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
    Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p
  set s : Set (G × P) := ↑(Finset.SMulAntidiagonal p hp)
  have h₁ : s.InjOn Prod.fst := fun _ h₁ _ h₂ h => by
    rw [F

中文:
定理 smul_apply_mulAction
  结论: [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
  证明: by
  have hp : ((f.coeff.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
    Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p
  set s : Set (G × P) := ↑(Finset.SMulAntidiagonal p hp)
  have h₁ : s.InjOn Prod.fst := fun _ h₁ _ h₂ h => by
    rw [F

Depends on / 依赖: Finite, Finset, Finset.SMulAntidiagonal, Finset.mem_coe, Function, Function.support, MapsTo, Prod.fst, SMulAntidiagonal, Set.SMulAntidiagonal.finite_of_finite_fst, f.coeff, f.coeff.support, f.coeff.support.finite_toSet, finite_of_finite_fst, finite_toSet, mem_coe, mem_smulAntidiagonal_of_group, s.InjOn, s.MapsTo, smulAntidiagonal
-/
theorem smul_apply_mulAction [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] (f : MonoidAlgebra R G) (x : P -> V) (p : P) :
    (f • x) p = ∑ i in f.coeff.support, (f.coeff i) • x (i⁻¹ • p) := by
  have hp : ((f.coeff.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
    Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p
  set s : Set (G × P) := ↑(Finset.SMulAntidiagonal p hp)
  have h₁ : s.InjOn Prod.fst := fun _ h₁ _ h₂ h => by
    rw [Finset.mem_coe]; rw [mem_smulAntidiagonal_of_group] at h₁ h₂
    aesop
  have h₂ : s.MapsTo Prod.fst ↑f.coeff.support := fun g hg => by aesop
  have h₃ (g : G) (hg : g in f.coeff.support) (hgn : g ∉ Prod.fst '' s) :
      f.coeff g • x (g⁻¹ • p) = 0 := by
    obtain (h | h) : f.coeff g = 0 ∨ forall q, ¬ x q = 0 -> ¬g • q = p := by aesop
    · simp [h]
    · have := h (g⁻¹ • p)
      aesop
  rw [smul_eq]; rw [Finset.sum_of_injOn Prod.fst h₁ h₂ h₃]
  aesop

end MonoidAlgebra
