/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Degree of polynomials that are units
-/

public section

noncomputable section

open Finsupp Finset Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

/-
**Polynomial.natDegree_eq_zero_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0
参数：h : IsUnit p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `left_ne_zero_of_mul_eq_one`：left_ne_zero_of_mul_eq_one (h : a * b = 1) :
 a != 0
· 使用定理 `right_ne_zero_of_mul_eq_one`：right_ne_zero_of_mul_eq_one (h : a * b = 1)
 : b != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
-/
lemma natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0 := by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq, natDegree_one, eq_comm, add_eq_zero] at this
  exact this.1
/-
**Polynomial.degree_eq_zero_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_eq_zero_of_isUnit [Nontrivial R] (h : IsUnit p) : degree p = 0
参数：h : IsUnit p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用引理 `Polynomial.natDegree_eq_zero_of_isUnit`：natDegree_eq_zero_of_isUnit (h :
 IsUnit p) : natDegree p = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.zero_le_degree_iff`：zero_le_degree_iff : 0 <= degree p ↔ p !=
 0
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
-/
lemma degree_eq_zero_of_isUnit [Nontrivial R] (h : IsUnit p) : degree p = 0 :=
  (natDegree_eq_zero_iff_degree_le_zero.mp <| natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)

@[simp]
/-
**Polynomial.degree_coe_units** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0
参数：u : R[X]ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
-/
lemma degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
  degree_eq_zero_of_isUnit ⟨u, rfl⟩

/-- Characterization of a unit of a polynomial ring over an integral domain `R`.
See `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` when `R` is a commutative ring. -/
/-
**Polynomial.isUnit_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ C r = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用引理 `Polynomial.natDegree_eq_zero_of_isUnit`：natDegree_eq_zero_of_isUnit (h :
 IsUnit p) : natDegree p = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Characterization of a unit of a polynomial ring over an integral domain `R`.
See `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` when `R` is a commutative r
ing.
-/
lemma isUnit_iff : IsUnit p ↔ ∃ r : R, IsUnit r ∧ C r = p :=
  ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩
/-
**Polynomial.not_isUnit_of_degree_pos** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_isUnit_of_degree_pos (p : R[X]) (hpl : 0 < p.degree) : ¬ IsUnit p
参数：p : R[X]；hpl : 0 < p.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
-/
lemma not_isUnit_of_degree_pos (p : R[X]) (hpl : 0 < p.degree) : ¬ IsUnit p := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0] at hpl
  intro h
  simp [degree_eq_zero_of_isUnit h] at hpl
/-
**Polynomial.not_isUnit_of_natDegree_pos** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_isUnit_of_natDegree_pos (p : R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit 
p
参数：p : R[X]；hpl : 0 < p.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.not_isUnit_of_degree_pos`：not_isUnit_of_degree_pos (p : R[X])
 (hpl : 0 < p.degree) : ¬ IsUnit p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
-/
lemma not_isUnit_of_natDegree_pos (p : R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p :=
  not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)
/-
**Polynomial.natDegree_coe_units** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [NoZeroDivisors R] (u : (Polynomial R)ˣ
), (↑u).natDegree = 0
参数：u : (Polynomial R)ˣ；↑u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用引理 `Polynomial.degree_coe_units`：degree_coe_units [Nontrivial R] (u : R[X]ˣ)
 : degree (u : R[X]) = 0
-/
@[simp] lemma natDegree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 := by
  nontriviality R
  exact natDegree_eq_of_degree_eq_some (degree_coe_units u)
/-
**Polynomial.coeff_coe_units_zero_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：coeff_coe_units_zero_ne_zero [Nontrivial R] (u : R[X]ˣ) : coeff (u : R[X])
 0 != 0
参数：u : R[X]ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_coe_units`：∀ {R : Type u} [inst : Semiring R] [NoZe
roDivisors R] (u : (Polynomial R)ˣ), (↑u).natDegree = 0
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
-/
theorem coeff_coe_units_zero_ne_zero [Nontrivial R] (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 := by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff, Ne, leadingCoeff_eq_zero]
  exact Units.ne_zero _

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)
include hp

/-
**Polynomial.Monic.C_dvd_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`
。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {p : Polynomial R}, p.Monic → ∀ {a 
: R}, Polynomial.C a ∣ p ↔ IsUnit a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.C_dvd_iff_dvd_coeff`：C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) :
 C r ∣ φ ↔ forall i, r ∣ φ.coeff i
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma Monic.C_dvd_iff_isUnit {a : R} : C a ∣ p ↔ IsUnit a where
  mp h := isUnit_iff_dvd_one.mpr <| hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree
  mpr ha := (ha.map C).dvd
/-
**Polynomial.Monic.degree_pos_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {p : Polynomial R}, p.Monic → ¬IsUn
it p → 0 < p.degree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.Monic.degree_pos`：∀ {R : Type u} [inst : CommSemiring R] {p :
 Polynomial R}, p.Monic → (0 < p.degree ↔ p ≠ 1)
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
lemma Monic.degree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < degree p :=
  hp.degree_pos.mpr fun hp' ↦ (hp' ▸ hu) isUnit_one
/-
**Polynomial.Monic.natDegree_pos_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {p : Polynomial R}, p.Monic → ¬IsUn
it p → 0 < p.natDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.Monic.natDegree_pos`：∀ {R : Type u} [inst : CommSemiring R] {
p : Polynomial R}, p.Monic → (0 < p.natDegree ↔ p ≠ 1)
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
lemma Monic.natDegree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < natDegree p :=
  hp.natDegree_pos.mpr fun hp' ↦ (hp' ▸ hu) isUnit_one
/-
**Polynomial.degree_pos_of_not_isUnit_of_dvd_monic** 是 Mathlib 中的一个引理，位于命名空间 `Po
lynomial`。
形式化陈述：degree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 <
 degree a
参数：ha : ¬IsUnit a；hap : a ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.Monic.C_dvd_iff_isUnit`：∀ {R : Type u} [inst : CommSemiring R
] {p : Polynomial R}, p.Monic → ∀ {a : R}, Polynomial.C a ∣ p ↔ IsUnit a
-/
lemma degree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < degree a := by
  contrapose! ha with h
  rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
  simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap
/-
**Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic** 是 Mathlib 中的一个引理，位于命名空间 
`Polynomial`。
形式化陈述：natDegree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 
0 < natDegree a
参数：ha : ¬IsUnit a；hap : a ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用引理 `Polynomial.degree_pos_of_not_isUnit_of_dvd_monic`：degree_pos_of_not_isUn
it_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < degree a
-/
lemma natDegree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < natDegree a :=
  natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_not_isUnit_of_dvd_monic hp ha hap

end CommSemiring

end Polynomial

