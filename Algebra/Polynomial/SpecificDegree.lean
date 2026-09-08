/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Polynomials of specific degree

Facts about polynomials that have a specific integer degree.
-/

public section

namespace Polynomial

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
/-
**Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three** 是 Mathlib 
中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] {p : Polynomial
 R},   p.Monic → 2 ≤ p.natDegree → p.natDegree ≤ 3 → (Irreducible p ↔ p.roots = 
0)
参数：Irreducible p ↔ p.roots = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.irreducible_iff_lt_natDegree_lt`：∀ {R : Type u} [inst :
 CommSemiring R] [NoZeroDivisors R] {p : Polynomial R},   p.Monic →     p ≠ 1 → 
(Irreducible p ↔ ∀ (q : Polynomial R),…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.div_le_div_right`：∀ {a b c : ℕ}, a ≤ b → a / c ≤ b / c
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Polynomial.Monic.eq_X_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R},   p.Monic → p.natDegree = 1 → p = Polynomial.X + Polynomial.C (p.coe
ff 0)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a

--- 原说明 ---
A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots.
-/
theorem Monic.irreducible_iff_roots_eq_zero_of_degree_le_three {p : R[X]} (hp : p.Monic)
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : p ≠ 1 := by rintro rfl; rw [natDegree_one] at hp2; cases hp2
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  simp_rw [show p.natDegree / 2 = 1 from
      (Nat.div_le_div_right hp3).antisymm
        (by apply Nat.div_le_div_right (c := 2) hp2),
    show Finset.Ioc 0 1 = {1} from rfl,
    Finset.mem_singleton, Multiset.eq_zero_iff_forall_notMem, mem_roots hp0, ← dvd_iff_isRoot]
  refine ⟨fun h r ↦ h _ (monic_X_sub_C r) (natDegree_X_sub_C r), fun h q hq hq1 ↦ ?_⟩
  rw [hq.eq_X_add_C hq1, ← sub_neg_eq_add, ← C_neg]
  apply h

end IsDomain

section Field

variable {K : Type*} [Field K] {p : K[X]}

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
/-
**Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：irreducible_iff_roots_eq_zero_of_degree_le_three (hp2 : 2 <= p.natDegree) 
(hp3 : p.natDegree <= 3) : Irreducible p ↔ p.roots = 0
参数：hp2 : 2 <= p.natDegree；hp3 : p.natDegree <= 3。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.irreducible_mul_leadingCoeff_inv`：irreducible_mul_leadingCoef
f_inv {p : K[X]} : Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p
· 使用定理 `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`：∀ {R 
: Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] {p : Polynomial R},   p.Mo
nic → 2 ≤ p.natDegree → p.natDegree ≤ 3 → (Irreducible …
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Polynomial.natDegree_mul_leadingCoeff_inv`：natDegree_mul_leadingCoeff_in
v (p : K[X]) {q : K[X]} (h : q != 0) : natDegree (p * C (leadingCoeff q)⁻¹) = na
tDegree p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots.
-/
theorem irreducible_iff_roots_eq_zero_of_degree_le_three
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_roots_eq_zero_of_degree_le_three,
      mul_comm, roots_C_mul]
  · exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]
/-
**Polynomial.irreducible_of_degree_le_three_of_not_isRoot** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial`。
形式化陈述：irreducible_of_degree_le_three_of_not_isRoot (hdeg : p.natDegree in Finset
.Icc 1 3) (hnot : forall x, ¬ IsRoot p x) : Irreducible p
参数：hdeg : p.natDegree in Finset.Icc 1 3；hnot : forall x, ¬ IsRoot p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three`：irreducible
_iff_roots_eq_zero_of_degree_le_three (hp2 : 2 <= p.natDegree) (hp3 : p.natDegre
e <= 3) : Irreducible p ↔ p.roots = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.irreducible_of_degree_eq_one`：irreducible_of_degree_eq_one (h
p1 : degree p = 1) : Irreducible p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq_of_pos`：degree_eq_iff_natDegree_eq
_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma irreducible_of_degree_le_three_of_not_isRoot
    (hdeg : p.natDegree ∈ Finset.Icc 1 3) (hnot : ∀ x, ¬ IsRoot p x) :
    Irreducible p := by
  rw [Finset.mem_Icc] at hdeg
  by_cases hdeg2 : 2 ≤ p.natDegree
  · rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg.2]
    apply Multiset.eq_zero_of_forall_notMem
    simp_all
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [← Nat.cast_one, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by simp)]
    exact le_antisymm (by rwa [not_le, Nat.lt_succ_iff] at hdeg2) hdeg.1

end Field

end Polynomial

