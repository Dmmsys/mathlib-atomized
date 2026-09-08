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

/-- If `f : F[X]` is monic of degree `≥ 1` and `F` is an algebraically closed field,
then `f = f₁ * f₂` with `f₁` monic of degree `1` and `f₂` monic of degree `f.natDegree - 1`. -/
/-
**Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_one_mul_isMonicOfDegree** 是 Math
lib 中的一个引理，位于命名空间 `Polynomial.IsMonicOfDegree`。
形式化陈述：eq_isMonicOfDegree_one_mul_isMonicOfDegree {F : Type*} [Field F] [IsAlgClo
sed F] {f : F[X]} {n : Nat} (hf : IsMonicOfDegree f (n + 1)) : exists f₁ f₂ : F[
X], IsMonicOfDegree f₁ 1 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂
参数：hf : IsMonicOfDegree f (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_monic_irreducible_factor`：Polynomial.exists_monic_irre
ducible_factor {F : Type*} [Field F] (f : F[X]) (hu : ¬IsUnit f) : exists g : F[
X], g.Monic ∧ Irreducible g ∧ g …
· 使用引理 `Polynomial.not_isUnit_of_natDegree_pos`：not_isUnit_of_natDegree_pos (p :
 R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `IsAlgClosed.degree_eq_one_of_irreducible`：degree_eq_one_of_irreducible [
IsAlgClosed k] {p : k[X]} (hp : Irreducible p) : p.degree = 1
· 使用定理 `Polynomial.IsMonicOfDegree.of_mul_left`：∀ {R : Type u_1} [inst : Semirin
g R] {p q : Polynomial R} {m n : ℕ},   p.IsMonicOfDegree m → (p * q).IsMonicOfDe
gree (m + n) → q.IsMonicOfDe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
If `f : F[X]` is monic of degree `≥ 1` and `F` is an algebraically closed field,
then `f = f₁ * f₂` with `f₁` monic of degree `1` and `f₂` monic of degree `f.nat
Degree - 1`.
-/
lemma eq_isMonicOfDegree_one_mul_isMonicOfDegree {F : Type*} [Field F]
    [IsAlgClosed F] {f : F[X]} {n : ℕ} (hf : IsMonicOfDegree f (n + 1)) :
    ∃ f₁ f₂ : F[X], IsMonicOfDegree f₁ 1 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ :=
    exists_monic_irreducible_factor f <| not_isUnit_of_natDegree_pos f <|
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₂, add_comm] at hf
  have hf₁ : IsMonicOfDegree f₁ 1 :=
    ⟨natDegree_eq_of_degree_eq_some <| IsAlgClosed.degree_eq_one_of_irreducible F hf₁i, hf₁m⟩
  exact ⟨f₁, f₂, hf₁, hf₁.of_mul_left hf, hf₂⟩

/-- If `f : ℝ[X]` is monic of positive degree, then `f = f₁ * f₂` with `f₁` monic
of degree `1` or `2`.

This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
-- TODO: generalize to real closed fields when they are available.
/-
**Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_one_or_two_mul** 是 Mathlib 中的一个引
理，位于命名空间 `Polynomial.IsMonicOfDegree`。
形式化陈述：eq_isMonicOfDegree_one_or_two_mul {f : Real[X]} {n : Nat} (hf : IsMonicOfD
egree f (n + 1)) : exists f₁ f₂ : Real[X], (IsMonicOfDegree f₁ 1 ∨ IsMonicOfDegr
ee f₁ 2) ∧ f = f₁ * f₂
参数：hf : IsMonicOfDegree f (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_monic_irreducible_factor`：Polynomial.exists_monic_irre
ducible_factor {F : Type*} [Field F] (f : F[X]) (hu : ¬IsUnit f) : exists g : F[
X], g.Monic ∧ Irreducible g ∧ g …
· 使用引理 `Polynomial.not_isUnit_of_natDegree_pos`：not_isUnit_of_natDegree_pos (p :
 R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_right`：of_le_right [LE α] (h : (a : α
) <= b) (eq : b = b') : a <= b'
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Nat.gt_of_not_le`：∀ {n m : ℕ}, ¬n ≤ m → n > m
· 使用定理 `Mathlib.Tactic.IntervalCases.of_lt_left`：of_lt_left [LinearOrder α] (h :
 (a : α) < b) (eq : a = a') : ¬b <= a'
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree
· 使用引理 `Irreducible.natDegree_le_two`：Irreducible.natDegree_le_two {p : Real[X]}
 (hp : Irreducible p) : natDegree p <= 2
-/
lemma eq_isMonicOfDegree_one_or_two_mul {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 1)) :
    ∃ f₁ f₂ : ℝ[X], (IsMonicOfDegree f₁ 1 ∨ IsMonicOfDegree f₁ 2) ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hm, hirr, f₂, hf₂⟩ :=
    exists_monic_irreducible_factor f <| not_isUnit_of_natDegree_pos f <|
      by grind [IsMonicOfDegree.natDegree_eq]
  refine ⟨f₁, f₂, ?_, hf₂⟩
  have help {P : ℕ → Prop} {m : ℕ} (hm₀ : 0 < m) (hm₂ : m ≤ 2) (h : P m) : P 1 ∨ P 2 := by
    interval_cases m <;> tauto
  exact help hirr.natDegree_pos hirr.natDegree_le_two <| IsMonicOfDegree.mk rfl hm

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`.

This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
-- TODO: generalize to real closed fields when they are available.
/-
**Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree** 是 Math
lib 中的一个引理，位于命名空间 `Polynomial.IsMonicOfDegree`。
形式化陈述：eq_isMonicOfDegree_two_mul_isMonicOfDegree {f : Real[X]} {n : Nat} (hf : I
sMonicOfDegree f (n + 2)) : exists f₁ f₂ : Real[X], IsMonicOfDegree f₁ 2 ∧ IsMon
icOfDegree f₂ n ∧ f = f₁ * f₂
参数：hf : IsMonicOfDegree f (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_one_or_two_mul`：eq_isMonic
OfDegree_one_or_two_mul {f : Real[X]} {n : Nat} (hf : IsMonicOfDegree f (n + 1))
 : exists f₁ f₂ : Real[X], (IsMonicOfDegree f₁ 1 ∨…
· 使用定理 `Polynomial.IsMonicOfDegree.of_mul_left`：∀ {R : Type u_1} [inst : Semirin
g R] {p q : Polynomial R} {m n : ℕ},   p.IsMonicOfDegree m → (p * q).IsMonicOfDe
gree (m + n) → q.IsMonicOfDe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.IsMonicOfDegree.mul`：∀ {R : Type u_1} [inst : Semiring R] {p 
q : Polynomial R} {m n : ℕ},   p.IsMonicOfDegree m → q.IsMonicOfDegree n → (p * 
q).IsMonicOfDegree (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
lemma eq_isMonicOfDegree_two_mul_isMonicOfDegree {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 2)) :
    ∃ f₁ f₂ : ℝ[X], IsMonicOfDegree f₁ 2 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨g₁, g₂, hd₁ | hd₂, h⟩ := hf.eq_isMonicOfDegree_one_or_two_mul
  all_goals rw [h, add_comm] at hf
  · have hg₂ := of_mul_left hd₁ <| (show 2 + n = 1 + (n + 1) by lia) ▸ hf
    obtain ⟨p₁, p₂, hp₁ | hp₂, h'⟩ := hg₂.eq_isMonicOfDegree_one_or_two_mul
    · rw [h', ← mul_assoc] at h hf
      exact ⟨g₁ * p₁, p₂, hd₁.mul hp₁, (hd₁.mul hp₁).of_mul_left hf, h⟩
    · rw [h', mul_left_comm] at h hf
      exact ⟨p₁, g₁ * p₂, hp₂, of_mul_left hp₂ hf, h⟩
  · exact ⟨g₁, g₂, hd₂, of_mul_left hd₂ hf, h⟩

end Polynomial.IsMonicOfDegree

