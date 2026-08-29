/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Factorization of monic polynomials of given degree

This file contains two main results:

* `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_one_isMonicOfDegree`
  shows that a monic polynomial of positive degree over an algebraically closed field
  can be written as a monic polynomial of degree 1 times another monic factor.

* `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree`
  shows that a monic polynomial of degree at least two over `ℝ` can be written as
  a monic polynomial of degree two times another monic factor.
-/

public section

namespace Polynomial.IsMonicOfDegree

/--
lemma `eq_isMonicOfDegree_one_mul_isMonicOfDegree` / 引理 `eq_isMonicOfDegree_one_mul_isMonicOfDegree`

English:
lemma eq_isMonicOfDegree_one_mul_isMonicOfDegree
  statement: {F : Type*} [Field F]
  proof: by
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ :=
exists_monic_irreducible_factor f not_isUnit_of_natDegree_pos f
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₂]; rw [add_comm] at hf
  have hf₁ : IsMonicOfDegree f₁ 1 :=
⟨natDegree_eq_of_degree_eq_some IsAlgClosed.degree_eq_one_of_irreducible F hf₁i,

中文:
引理 eq_isMonicOfDegree_one_mul_isMonicOfDegree
  结论: {F : 类型} [Field F]
  证明: by
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ :=
exists_monic_irreducible_factor f not_isUnit_of_natDegree_pos f
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₂]; rw [add_comm] at hf
  have hf₁ : IsMonicOfDegree f₁ 1 :=
⟨natDegree_eq_of_degree_eq_some IsAlgClosed.degree_eq_one_of_irreducible F hf₁i,

Depends on / 依赖: IsAlgClosed, IsAlgClosed.degree_eq_one_of_irreducible, IsMonicOfDegree, IsMonicOfDegree.natDegree_eq, add_comm, degree_eq_one_of_irreducible, exists_monic_irreducible_factor, natDegree_eq, natDegree_eq_of_degree_eq_some, not_isUnit_of_natDegree_pos, of_mul_left
-/
lemma eq_isMonicOfDegree_one_mul_isMonicOfDegree {F : Type*} [Field F]
    [IsAlgClosed F] {f : F[X]} {n : Nat} (hf : IsMonicOfDegree f (n + 1)) :
    exists f₁ f₂ : F[X], IsMonicOfDegree f₁ 1 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ :=
exists_monic_irreducible_factor f not_isUnit_of_natDegree_pos f
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₂]; rw [add_comm] at hf
  have hf₁ : IsMonicOfDegree f₁ 1 :=
⟨natDegree_eq_of_degree_eq_some IsAlgClosed.degree_eq_one_of_irreducible F hf₁i, hf₁m⟩
  exact ⟨f₁, f₂, hf₁, hf₁.of_mul_left hf, hf₂⟩

-- TODO: generalize to real closed fields when they are available.
/--
lemma `eq_isMonicOfDegree_one_or_two_mul` / 引理 `eq_isMonicOfDegree_one_or_two_mul`

English:
lemma eq_isMonicOfDegree_one_or_two_mul
  statement: {f : Real[X]} {n : Nat}
  proof: by
  obtain ⟨f₁, hm, hirr, f₂, hf₂⟩ :=
exists_monic_irreducible_factor f not_isUnit_of_natDegree_pos f
      by grind [IsMonicOfDegree.natDegree_eq]
  refine ⟨f₁, f₂, ?_, hf₂⟩
  have help {P : Nat -> Prop} {m : Nat} (hm₀ : 0 < m) (hm₂ : m <= 2) (h : P m) : P 1 ∨ P 2 := by
    interval_cases m <;> ta

中文:
引理 eq_isMonicOfDegree_one_or_two_mul
  结论: {f : 实数[X]} {n : 自然数}
  证明: by
  obtain ⟨f₁, hm, hirr, f₂, hf₂⟩ :=
exists_monic_irreducible_factor f not_isUnit_of_natDegree_pos f
      by grind [IsMonicOfDegree.natDegree_eq]
  refine ⟨f₁, f₂, ?_, hf₂⟩
  have help {P : Nat -> Prop} {m : Nat} (hm₀ : 0 < m) (hm₂ : m <= 2) (h : P m) : P 1 ∨ P 2 := by
    interval_cases m <;> ta

Depends on / 依赖: IsMonicOfDegree, IsMonicOfDegree.mk, IsMonicOfDegree.natDegree_eq, exists_monic_irreducible_factor, hirr.natDegree_le_two, hirr.natDegree_pos, interval_cases, natDegree_eq, natDegree_le_two, natDegree_pos, not_isUnit_of_natDegree_pos
-/
lemma eq_isMonicOfDegree_one_or_two_mul {f : Real[X]} {n : Nat}
    (hf : IsMonicOfDegree f (n + 1)) :
    exists f₁ f₂ : Real[X], (IsMonicOfDegree f₁ 1 ∨ IsMonicOfDegree f₁ 2) ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hm, hirr, f₂, hf₂⟩ :=
exists_monic_irreducible_factor f not_isUnit_of_natDegree_pos f
      by grind [IsMonicOfDegree.natDegree_eq]
  refine ⟨f₁, f₂, ?_, hf₂⟩
  have help {P : Nat -> Prop} {m : Nat} (hm₀ : 0 < m) (hm₂ : m <= 2) (h : P m) : P 1 ∨ P 2 := by
    interval_cases m <;> tauto
exact help hirr.natDegree_pos hirr.natDegree_le_two IsMonicOfDegree.mk rfl hm

-- TODO: generalize to real closed fields when they are available.
/--
lemma `eq_isMonicOfDegree_two_mul_isMonicOfDegree` / 引理 `eq_isMonicOfDegree_two_mul_isMonicOfDegree`

English:
lemma eq_isMonicOfDegree_two_mul_isMonicOfDegree
  statement: {f : Real[X]} {n : Nat}
  proof: by
  obtain ⟨g₁, g₂, hd₁ | hd₂, h⟩ := hf.eq_isMonicOfDegree_one_or_two_mul
  all_goals rw [h, add_comm] at hf
· have hg₂ := of_mul_left hd₁ (show 2 + n = 1 + (n + 1) by lia) ▸ hf
    obtain ⟨p₁, p₂, hp₁ | hp₂, h'⟩ := hg₂.eq_isMonicOfDegree_one_or_two_mul
    · rw [h', ← mul_assoc] at h hf
      exac

中文:
引理 eq_isMonicOfDegree_two_mul_isMonicOfDegree
  结论: {f : 实数[X]} {n : 自然数}
  证明: by
  obtain ⟨g₁, g₂, hd₁ | hd₂, h⟩ := hf.eq_isMonicOfDegree_one_or_two_mul
  all_goals rw [h, add_comm] at hf
· have hg₂ := of_mul_left hd₁ (show 2 + n = 1 + (n + 1) by lia) ▸ hf
    obtain ⟨p₁, p₂, hp₁ | hp₂, h'⟩ := hg₂.eq_isMonicOfDegree_one_or_two_mul
    · rw [h', ← mul_assoc] at h hf
      exac

Depends on / 依赖: add_comm, all_goals, eq_isMonicOfDegree_one_or_two_mul, hf.eq_isMonicOfDegree_one_or_two_mul, mul_assoc, mul_left_comm, of_mul_left
-/
lemma eq_isMonicOfDegree_two_mul_isMonicOfDegree {f : Real[X]} {n : Nat}
    (hf : IsMonicOfDegree f (n + 2)) :
    exists f₁ f₂ : Real[X], IsMonicOfDegree f₁ 2 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨g₁, g₂, hd₁ | hd₂, h⟩ := hf.eq_isMonicOfDegree_one_or_two_mul
  all_goals rw [h, add_comm] at hf
· have hg₂ := of_mul_left hd₁ (show 2 + n = 1 + (n + 1) by lia) ▸ hf
    obtain ⟨p₁, p₂, hp₁ | hp₂, h'⟩ := hg₂.eq_isMonicOfDegree_one_or_two_mul
    · rw [h', ← mul_assoc] at h hf
      exact ⟨g₁ * p₁, p₂, hd₁.mul hp₁, (hd₁.mul hp₁).of_mul_left hf, h⟩
    · rw [h', mul_left_comm] at h hf
      exact ⟨p₁, g₁ * p₂, hp₂, of_mul_left hp₂ hf, h⟩
  · exact ⟨g₁, g₂, hd₂, of_mul_left hd₂ hf, h⟩

end Polynomial.IsMonicOfDegree
