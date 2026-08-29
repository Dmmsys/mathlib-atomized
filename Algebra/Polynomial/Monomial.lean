/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Univariate monomials
-/

public section


noncomputable section

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : Nat}
variable [Semiring R] {p q r : R[X]}

/--
theorem `monomial_one_eq_iff` / 定理 `monomial_one_eq_iff`

English:
theorem monomial_one_eq_iff
  given: [Nontrivial R] {i j : Nat}
  proof: by
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  exact AddMonoidAlgebra.of_injective.eq_iff

中文:
定理 monomial_one_eq_iff
  条件: [Nontrivial R] {i j : 自然数}
  证明: by
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  exact AddMonoidAlgebra.of_injective.eq_iff

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.of_injective.eq_iff, eq_iff, ofFinsupp, ofFinsupp.injEq, ofFinsupp_single, of_injective, simp_rw
-/
theorem monomial_one_eq_iff [Nontrivial R] {i j : Nat} :
    (monomial i 1 : R[X]) = monomial j 1 ↔ i = j := by
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  exact AddMonoidAlgebra.of_injective.eq_iff

/--
Instance `infinite` / 实例 `infinite`

English:
instance infinite
  signature: [Nontrivial R]
  body: Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

中文:
实例 infinite
  签名: [Nontrivial R]
  定义体: Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

Depends on / 依赖: Infinite, Infinite.of_injective, monomial, monomial_one_eq_iff, of_injective
-/
instance infinite [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

/--
theorem `card_support_le_one_iff_monomial` / 定理 `card_support_le_one_iff_monomial`

English:
theorem card_support_le_one_iff_monomial
  given: {f : R[X]}
  proof: by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi]
    · have : f.coeff i = 0 := by
        rw [← notMem_support_iff]
        exact fun hi' => hi (Finset.mem_sing

中文:
定理 card_support_le_one_iff_monomial
  条件: {f : R[X]}
  证明: by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi]
    · have : f.coeff i = 0 := by
        rw [← notMem_support_iff]
        exact fun hi' => hi (Finset.mem_sing

Depends on / 依赖: Finset, Finset.card_le_card, Finset.card_le_one_iff_subset_singleton, Finset.card_singleton, Finset.mem_singleton, Ne.symm, card_le_card, card_le_one_iff_subset_singleton, card_singleton, coeff_monomial, f.coeff, mem_singleton, notMem_support_iff, support_monomial_subset
-/
theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support <= 1 ↔ exists n a, f = monomial n a := by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi]
    · have : f.coeff i = 0 := by
        rw [← notMem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_card
    exact support_monomial_subset _ _

/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  statement: {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : forall a, f (C a) = g (C a))
  proof: by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [f', g', h₁, RingEquiv.toRingHom_eq_coe]
    simpa using! h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf']; rw [RingHom.

中文:
定理 ringHom_ext
  结论: {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : 对任意 a, f (C a) = g (C a))
  证明: by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [f', g', h₁, RingEquiv.toRingHom_eq_coe]
    simpa using! h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf']; rw [RingHom.

Depends on / 依赖: Function, Function.comp_apply, RingEquiv, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_comp, RingHom.comp_ass, RingHom.comp_assoc, coe_comp, coe_toRingHom, comp_apply, comp_ass, comp_assoc, f.comp, g.comp, symm.toRingHom, symm_apply_apply, toFinsuppIso
-/
theorem ringHom_ext {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : forall a, f (C a) = g (C a))
    (h₂ : f X = g X) : f = g := by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [f', g', h₁, RingEquiv.toRingHom_eq_coe]
    simpa using! h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf']; rw [RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  have C' : g = g'.comp (toFinsuppIso R) := by
    rw [hg']; rw [RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  rw [B]; rw [C']; rw [A]

@[ext high]
/--
theorem `ringHom_ext'` / 定理 `ringHom_ext'`

English:
theorem ringHom_ext'
  statement: {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : f.comp C = g.comp C)
  proof: ringHom_ext (RingHom.congr_fun h₁) h₂

中文:
定理 ringHom_ext'
  结论: {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : f.comp C = g.comp C)
  证明: ringHom_ext (RingHom.congr_fun h₁) h₂

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun, ringHom_ext
-/
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : f.comp C = g.comp C)
    (h₂ : f X = g X) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂

end Polynomial
