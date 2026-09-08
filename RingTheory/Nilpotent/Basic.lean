/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent elements

This file develops the basic theory of nilpotent elements. In particular it shows that the
nilpotent elements are closed under many operations.

For the definition of `nilradical`, see `Mathlib/RingTheory/Nilpotent/Lemmas.lean`.


## Main definitions

  * `isNilpotent_neg_iff`
  * `Commute.isNilpotent_add`
  * `Commute.isNilpotent_sub`

-/

public section

universe u v

open Function Set

variable {R S : Type*} {x y : R}

/-
**IsNilpotent.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x)
参数：h : IsNilpotent x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, mul_zero]
/-
**not_isNilpotent_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isNilpotent_neg_one [Ring R] [Nontrivial R] : ¬ IsNilpotent (-1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `IsNilpotent.neg`：IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpot
ent (-x)
-/
theorem not_isNilpotent_neg_one [Ring R] [Nontrivial R] : ¬ IsNilpotent (-1 : R) := by
  intro h
  simpa [not_isNilpotent_one] using h.neg
/-
**neg_one_pow_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_one_pow_ne_zero [Ring R] [Nontrivial R] (n : Nat) : (-1 : R) ^ n != 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isNilpotent_neg_one`：not_isNilpotent_neg_one [Ring R] [Nontrivial R]
 : ¬ IsNilpotent (-1 : R)
-/
theorem neg_one_pow_ne_zero [Ring R] [Nontrivial R] (n : ℕ) : (-1 : R) ^ n ≠ 0 := by
  intro h
  exact not_isNilpotent_neg_one ⟨n, h⟩

@[simp]
/-
**isNilpotent_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.neg`：IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpot
ent (-x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩
/-
**IsNilpotent.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero 
R S] [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha : IsNilpotent a) (t
 : R) : IsNilpotent (t • a)
参数：ha : IsNilpotent a；t : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha : IsNilpotent a) (t : R) :
    IsNilpotent (t • a) := by
  obtain ⟨k, ha⟩ := ha
  use k
  rw [smul_pow, ha, smul_zero]
/-
**IsNilpotent.isUnit_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_sub_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUni
t (r - 1)
参数：hnil : IsNilpotent r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `mul_geom_sum`：mul_geom_sum (x : R) (n : Nat) : ((x - 1) * ∑ i in range n
, x ^ i) = x ^ n - 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
-/
theorem IsNilpotent.isUnit_sub_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨⟨r - 1, -∑ i ∈ Finset.range n, r ^ i, ?_, ?_⟩, rfl⟩
  · simp [mul_geom_sum, hn]
  · simp [geom_sum_mul, hn]
/-
**IsNilpotent.isUnit_one_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_one_sub [Ring R] {r : R} (hnil : IsNilpotent r) : IsUni
t (1 - r)
参数：hnil : IsNilpotent r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.neg_iff`：IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : Is
Unit (-a) ↔ IsUnit a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `IsNilpotent.isUnit_sub_one`：IsNilpotent.isUnit_sub_one [Ring R] {r : R} 
(hnil : IsNilpotent r) : IsUnit (r - 1)
-/
theorem IsNilpotent.isUnit_one_sub [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (1 - r) := by
  rw [← IsUnit.neg_iff, neg_sub]
  exact isUnit_sub_one hnil
/-
**IsNilpotent.isUnit_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_add_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUni
t (r + 1)
参数：hnil : IsNilpotent r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.neg_iff`：IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : Is
Unit (-a) ↔ IsUnit a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `IsNilpotent.isUnit_sub_one`：IsNilpotent.isUnit_sub_one [Ring R] {r : R} 
(hnil : IsNilpotent r) : IsUnit (r - 1)
· 使用定理 `IsNilpotent.neg`：IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpot
ent (-x)
-/
theorem IsNilpotent.isUnit_add_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r + 1) := by
  rw [← IsUnit.neg_iff, neg_add']
  exact isUnit_sub_one hnil.neg
/-
**IsNilpotent.isUnit_one_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_one_add [Ring R] {r : R} (hnil : IsNilpotent r) : IsUni
t (1 + r)
参数：hnil : IsNilpotent r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.isUnit_add_one`：IsNilpotent.isUnit_add_one [Ring R] {r : R} 
(hnil : IsNilpotent r) : IsUnit (r + 1)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsNilpotent.isUnit_one_add [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (1 + r) :=
  add_comm r 1 ▸ isUnit_add_one hnil
/-
**IsNilpotent.isUnit_add_left_of_commute** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_add_left_of_commute [Ring R] {r u : R} (hnil : IsNilpot
ent r) (hu : IsUnit u) (h_comm : Commute r u) : IsUnit (u + r)
参数：hnil : IsNilpotent r；hu : IsUnit u；h_comm : Commute r u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.isUnit_mul_units`：Units.isUnit_mul_units [Monoid M] (a : M) (u : M
ˣ) : IsUnit (a * u) ↔ IsUnit a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `Commute.units_inv_right`：units_inv_right : Commute a u -> Commute a ↑u⁻¹
· 使用定理 `IsNilpotent.isUnit_one_add`：IsNilpotent.isUnit_one_add [Ring R] {r : R} 
(hnil : IsNilpotent r) : IsUnit (1 + r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUnit.isNilpotent_mul_unit_of_commute_iff`：IsUnit.isNilpotent_mul_unit_
of_commute_iff [MonoidWithZero R] {r u : R} (hu : IsUnit u) (h_comm : Commute r 
u) : IsNilpotent (r * u) ↔ IsNil…
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem IsNilpotent.isUnit_add_left_of_commute [Ring R] {r u : R}
    (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commute r u) :
    IsUnit (u + r) := by
  rw [← Units.isUnit_mul_units _ hu.unit⁻¹, add_mul, IsUnit.mul_val_inv]
  replace h_comm : Commute r (↑hu.unit⁻¹) := Commute.units_inv_right h_comm
  refine IsNilpotent.isUnit_one_add ?_
  exact (hu.unit⁻¹.isUnit.isNilpotent_mul_unit_of_commute_iff h_comm).mpr hnil
/-
**IsNilpotent.isUnit_add_right_of_commute** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_add_right_of_commute [Ring R] {r u : R} (hnil : IsNilpo
tent r) (hu : IsUnit u) (h_comm : Commute r u) : IsUnit (r + u)
参数：hnil : IsNilpotent r；hu : IsUnit u；h_comm : Commute r u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.isUnit_add_left_of_commute`：IsNilpotent.isUnit_add_left_of_c
ommute [Ring R] {r u : R} (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commu
te r u) : IsUnit (u + r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsNilpotent.isUnit_add_right_of_commute [Ring R] {r u : R}
    (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commute r u) :
    IsUnit (r + u) :=
  add_comm r u ▸ hnil.isUnit_add_left_of_commute hu h_comm
/-
**IsUnit.not_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.not_isNilpotent [Ring R] [Nontrivial R] {x : R} (hx : IsUnit x) : ¬
 IsNilpotent x
参数：hx : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `IsNilpotent.isUnit_add_right_of_commute`：IsNilpotent.isUnit_add_right_of
_commute [Ring R] {r u : R} (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Com
mute r u) : IsUnit (r + u)
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma IsUnit.not_isNilpotent [Ring R] [Nontrivial R] {x : R} (hx : IsUnit x) :
    ¬ IsNilpotent x := by
  intro H
  simpa using H.isUnit_add_right_of_commute hx.neg (by simp)
/-
**IsNilpotent.not_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.not_isUnit [Ring R] [Nontrivial R] {x : R} (hx : IsNilpotent x
) : ¬ IsUnit x
参数：hx : IsNilpotent x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `IsUnit.not_isNilpotent`：IsUnit.not_isNilpotent [Ring R] [Nontrivial R] {
x : R} (hx : IsUnit x) : ¬ IsNilpotent x
-/
lemma IsNilpotent.not_isUnit [Ring R] [Nontrivial R] {x : R} (hx : IsNilpotent x) :
    ¬ IsUnit x :=
  mt IsUnit.not_isNilpotent (by simpa only [not_not] using hx)
/-
**IsIdempotentElem.eq_zero_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.eq_zero_of_isNilpotent [MonoidWithZero R] {e : R} (idem :
 IsIdempotentElem e) (nilp : IsNilpotent e) : e = 0
参数：idem : IsIdempotentElem e；nilp : IsNilpotent e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `IsIdempotentElem.pow_succ_eq`：pow_succ_eq (n : Nat) (h : IsIdempotentEle
m a) : a ^ (n + 1) = a
-/
lemma IsIdempotentElem.eq_zero_of_isNilpotent [MonoidWithZero R] {e : R}
    (idem : IsIdempotentElem e) (nilp : IsNilpotent e) : e = 0 := by
  obtain ⟨rfl | n, hn⟩ := nilp
  · rw [pow_zero] at hn; rw [← one_mul e, hn, zero_mul]
  · rw [← hn, idem.pow_succ_eq]

alias IsNilpotent.eq_zero_of_isIdempotentElem := IsIdempotentElem.eq_zero_of_isNilpotent
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [Pow R ℕ] [Zero S] [Pow S ℕ] [IsReduced R] [IsReduced S] : IsReduced (R × S) where
  eq_zero _ := fun ⟨n, hn⟩ ↦ have hn := Prod.ext_iff.1 hn
    Prod.ext (IsReduced.eq_zero _ ⟨n, hn.1⟩) (IsReduced.eq_zero _ ⟨n, hn.2⟩)
/-
**Prime.isRadical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.isRadical [CommMonoidWithZero R] {y : R} (hy : Prime y) : IsRadical 
y
参数：hy : Prime y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
-/
theorem Prime.isRadical [CommMonoidWithZero R] {y : R} (hy : Prime y) : IsRadical y :=
  fun _ _ ↦ hy.dvd_of_dvd_pow
/-
**zero_isRadical_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R := by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_comm
/-
**isReduced_iff_pow_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isReduced_iff_pow_one_lt [MonoidWithZero R] (k : Nat) (hk : 1 < k) : IsRed
uced R ↔ forall x : R, x ^ k = 0 -> x = 0
参数：k : Nat；hk : 1 < k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRadical_iff_pow_one_lt`：isRadical_iff_pow_one_lt [Monoid R] (k : Nat) 
(hk : 1 < k) : IsRadical y ↔ forall x, y ∣ x ^ k -> y ∣ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isReduced_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsReduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 := by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]
/-
**IsRadical.of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRadical.of_dvd [CommMonoidWithZero R] [IsCancelMulZero R] {x y : R} (hy 
: IsRadical y) (h0 : y != 0) (hxy : x ∣ y) : IsRadical x
参数：hy : IsRadical y；h0 : y != 0；hxy : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isRadical_iff_pow_one_lt`：isRadical_iff_pow_one_lt [Monoid R] (k : Nat) 
(hk : 1 < k) : IsRadical y ↔ forall x, y ∣ x ^ k -> y ∣ x
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_dvd_mul_iff_right`：mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsC
ancelMulZero α] {a b c : α} (hc : c != 0) : a * c ∣ b * c ↔ a ∣ b
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRadical.of_dvd [CommMonoidWithZero R] [IsCancelMulZero R] {x y : R} (hy : IsRadical y)
    (h0 : y ≠ 0) (hxy : x ∣ y) : IsRadical x := (isRadical_iff_pow_one_lt 2 one_lt_two).2 <| by
  obtain ⟨z, rfl⟩ := hxy
  refine fun w dvd ↦ ((mul_dvd_mul_iff_right <| right_ne_zero_of_mul h0).mp <| hy 2 _ ?_)
  rw [mul_pow]
  gcongr
  exact dvd_pow_self _ two_ne_zero

namespace Commute

section Semiring

variable [Semiring R]

/-
**Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Commute`。
形式化陈述：add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (h_comm : Commute x y) {m n 
k : Nat} (hx : x ^ m = 0) (hy : y ^ n = 0) (h : m + n <= k + 1) : (x + y) ^ k = 
0
参数：h_comm : Commute x y；hx : x ^ m = 0；hy : y ^ n = 0；h : m + n <= k + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.add_pow'`：add_pow' (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑
 m in antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2)
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 57 条，此处仅展示前 30 条）
-/
theorem add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (h_comm : Commute x y) {m n k : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) (h : m + n ≤ k + 1) :
    (x + y) ^ k = 0 := by
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  by_cases hi : m ≤ i
  · rw [pow_eq_zero_of_le hi hx, zero_mul]
  rw [pow_eq_zero_of_le ?_ hy, mul_zero]
  linarith [Finset.mem_antidiagonal.mp hij]
/-
**Commute.add_pow_add_eq_zero_of_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Commute`
。
形式化陈述：add_pow_add_eq_zero_of_pow_eq_zero (h_comm : Commute x y) {m n : Nat} (hx 
: x ^ m = 0) (hy : y ^ n = 0) : (x + y) ^ (m + n - 1) = 0
参数：h_comm : Commute x y；hx : x ^ m = 0；hy : y ^ n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero`：add_pow_eq_zero_o
f_add_le_succ_of_pow_eq_zero (h_comm : Commute x y) {m n k : Nat} (hx : x ^ m = 
0) (hy : y ^ n = 0) (h : m + n <= k + 1) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem add_pow_add_eq_zero_of_pow_eq_zero (h_comm : Commute x y) {m n : ℕ}
    (hx : x ^ m = 0) (hy : y ^ n = 0) :
    (x + y) ^ (m + n - 1) = 0 :=
  h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hy <| by rw [← Nat.sub_le_iff_le_add]
/-
**Commute.isNilpotent_add** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：isNilpotent_add (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpot
ent y) : IsNilpotent (x + y)
参数：h_comm : Commute x y；hx : IsNilpotent x；hy : IsNilpotent y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.add_pow_add_eq_zero_of_pow_eq_zero`：add_pow_add_eq_zero_of_pow_e
q_zero (h_comm : Commute x y) {m n : Nat} (hx : x ^ m = 0) (hy : y ^ n = 0) : (x
 + y) ^ (m + n - 1) = 0
-/
theorem isNilpotent_add (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  exact ⟨_, add_pow_add_eq_zero_of_pow_eq_zero h_comm hn hm⟩
/-
**Commute.isNilpotent_sum** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {ι : Type u_3} {s : Finset ι} {f : ι 
→ R},   (∀ i ∈ s, IsNilpotent (f i)) → (∀ (i j : ι), i ∈ s → j ∈ s → Commute (f 
i) (f j)) → IsNilpotent (∑ i ∈ s, f i)
参数：∀ i ∈ s, IsNilpotent (f i)；∀ (i j : ι), i ∈ s → j ∈ s → Commute (f i) (f j)；∑
 i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Commute.isNilpotent_add`：isNilpotent_add (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y)
· 使用定理 `Commute.sum_right`：∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonA
ssocSemiring R] (s : Finset ι) (f : ι → R) (b : R),   (∀ i ∈ s, Commute b (f i))
 → Comm…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
protected lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) (h_comm : ∀ i j, i ∈ s → j ∈ s → Commute (f i) (f j)) :
    IsNilpotent (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi ↦ h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi ↦ hnp i (by simp [hi]))
      (fun i j hi hj ↦ h_comm i j (by simp [hi]) (by simp [hj]))
/-
**Commute.isNilpotent_finsum** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：isNilpotent_finsum {ι : Type*} {f : ι -> R} (hf : forall b, IsNilpotent (f
 b)) (h_comm : forall i j, Commute (f i) (f j)) : IsNilpotent (finsum f)
参数：hf : forall b, IsNilpotent (f b)；h_comm : forall i j, Commute (f i) (f j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_def`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] (f 
: α → M) [inst_1 : Decidable (Function.HasFiniteSupport f)],   ∑ᶠ (i : α), f i =
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Commute.isNilpotent_sum`：∀ {R : Type u_1} [inst : Semiring R] {ι : Type 
u_3} {s : Finset ι} {f : ι → R},   (∀ i ∈ s, IsNilpotent (f i)) → (∀ (i j : ι), 
i ∈ s → j ∈ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem isNilpotent_finsum {ι : Type*} {f : ι → R}
    (hf : ∀ b, IsNilpotent (f b)) (h_comm : ∀ i j, Commute (f i) (f j)) :
    IsNilpotent (finsum f) := by
  classical
  by_cases h : HasFiniteSupport f
  · rw [finsum_def, dif_pos h]
    exact Commute.isNilpotent_sum (fun b _ ↦ hf b) (fun _ _ _ _ ↦ h_comm _ _)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]
/-
**Commute.isNilpotent_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} {x y : R} [inst : Semiring R],   Commute x y → y ∈ nonZer
oDivisorsRight R → (IsNilpotent (x * y) ↔ IsNilpotent x)
参数：IsNilpotent (x * y) ↔ IsNilpotent x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.pow_mem`：∀ {M : Type u_5} [inst : Monoid M] (S : Submonoid M) 
{x : M}, x ∈ S → ∀ (n : ℕ), x ^ n ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Commute.isNilpotent_mul_right`：isNilpotent_mul_right (h_comm : Commute x
 y) (h : IsNilpotent x) : IsNilpotent (x * y)
-/
protected lemma isNilpotent_mul_right_iff (h_comm : Commute x y) (hy : y ∈ nonZeroDivisorsRight R) :
    IsNilpotent (x * y) ↔ IsNilpotent x := by
  refine ⟨?_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hy k _ hk⟩
/-
**Commute.isNilpotent_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u_1} {x y : R} [inst : Semiring R],   Commute x y → x ∈ nonZer
oDivisorsLeft R → (IsNilpotent (x * y) ↔ IsNilpotent y)
参数：IsNilpotent (x * y) ↔ IsNilpotent y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.pow_mem`：∀ {M : Type u_5} [inst : Monoid M] (S : Submonoid M) 
{x : M}, x ∈ S → ∀ (n : ℕ), x ^ n ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
-/
protected lemma isNilpotent_mul_left_iff (h_comm : Commute x y) (hx : x ∈ nonZeroDivisorsLeft R) :
    IsNilpotent (x * y) ↔ IsNilpotent y := by
  refine ⟨?_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hx k _ hk⟩

end Semiring

section Ring

variable [Ring R]

/-
**Commute.isNilpotent_sub** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：isNilpotent_sub (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpot
ent y) : IsNilpotent (x - y)
参数：h_comm : Commute x y；hx : IsNilpotent x；hy : IsNilpotent y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Commute.isNilpotent_add`：isNilpotent_add (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.neg_right_iff`：neg_right_iff : Commute a (-b) ↔ Commute a b
· 使用定理 `isNilpotent_neg_iff`：isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ I
sNilpotent x
-/
theorem isNilpotent_sub (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x - y) := by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy

end Ring

end Commute

section CommSemiring

variable [CommSemiring R] {x y : R}

/-
**isNilpotent_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι -> R} (hnp : forall i in
 s, IsNilpotent (f i)) : IsNilpotent (∑ i in s, f i)
参数：hnp : forall i in s, IsNilpotent (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isNilpotent_sum`：∀ {R : Type u_1} [inst : Semiring R] {ι : Type 
u_3} {s : Finset ι} {f : ι → R},   (∀ i ∈ s, IsNilpotent (f i)) → (∀ (i j : ι), 
i ∈ s → j ∈ s…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) :
    IsNilpotent (∑ i ∈ s, f i) :=
  Commute.isNilpotent_sum hnp fun _ _ _ _ ↦ Commute.all _ _
/-
**isNilpotent_finsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNilpotent_finsum {ι : Type*} {f : ι -> R} (hf : forall b, IsNilpotent (f
 b)) : IsNilpotent (finsum f)
参数：hf : forall b, IsNilpotent (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isNilpotent_finsum`：isNilpotent_finsum {ι : Type*} {f : ι -> R} 
(hf : forall b, IsNilpotent (f b)) (h_comm : forall i j, Commute (f i) (f j)) : 
IsNilpotent (fin…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem isNilpotent_finsum {ι : Type*} {f : ι → R}
    (hf : ∀ b, IsNilpotent (f b)) :
    IsNilpotent (finsum f) :=
  Commute.isNilpotent_finsum hf fun _ _ ↦ Commute.all _ _

end CommSemiring

