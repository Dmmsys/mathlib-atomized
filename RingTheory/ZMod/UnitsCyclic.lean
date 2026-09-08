/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Junyan Xu
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic

/-! # Cyclicity of the units of `ZMod n`

`ZMod.isCyclic_units_iff` : `(ZMod n)ˣ` is cyclic iff
one of the following mutually exclusive cases happens:
  - `n = 0` (then `ZMod 0 ≃+* ℤ` and the group of units is cyclic of order 2);
  - `n = 1`, `2` or `4`
  - `n` is a power `p ^ e` of an odd prime number, or twice such a power
    (with `1 ≤ e`).

The individual cases are proved by `inferInstance` and are
also directly provided by :

* `ZMod.isCyclic_units_zero`
* `ZMod.isCyclic_units_one`
* `ZMod.isCyclic_units_two`
* `ZMod.isCyclic_units_four`

The case of prime numbers is also an instance:

* `ZMod.isCyclic_units_prime`

* `ZMod.not_isCyclic_units_eight`: `(ZMod 8)ˣ` is not cyclic

* `ZMod.orderOf_one_add_mul_prime`: the order of `1 + a * p`
  modulo `p ^ (n + 1)` is `p ^ n` when `p` does not divide `a`.

* `ZMod.orderOf_five` : the order of `5` modulo `2 ^ (n + 3)` is `2 ^ (n + 1)`.

* `ZMod.isCyclic_units_of_prime_pow` : the case of odd prime powers

* `ZMod.isCyclic_units_two_pow_iff` : `(ZMod (2 ^ n))ˣ` is cyclic iff `n ≤ 2`.

The proofs mostly follow [Ireland and Rosen,
  *A classical introduction to modern number theory*, chapter 4]
  [IrelandRosen1990].

-/

public section

open scoped Nat

namespace ZMod

section EasyCases

/-
**ZMod.isCyclic_units_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_zero : IsCyclic (ZMod 0)ˣ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `ZMod.instIsDomainOfNatNat`：IsDomain (ZMod 0)
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
-/
theorem isCyclic_units_zero :
    IsCyclic (ZMod 0)ˣ := inferInstance
/-
**ZMod.isCyclic_units_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_one : IsCyclic (ZMod 1)ˣ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_subsingleton`：∀ {α : Type u_1} [inst : Group α] [Subsingleto
n α], IsCyclic α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem isCyclic_units_one :
    IsCyclic (ZMod 1)ˣ := inferInstance
/-
**ZMod.isCyclic_units_two** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_two : IsCyclic (ZMod 2)ˣ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
-/
theorem isCyclic_units_two :
    IsCyclic (ZMod 2)ˣ := inferInstance
/-
**ZMod.isCyclic_units_four** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_four : IsCyclic (ZMod 4)ˣ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_prime_card`：isCyclic_of_prime_card {p : Nat} [hp : Fact p.Pr
ime] (h : Nat.card α = p) : IsCyclic α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem isCyclic_units_four :
    IsCyclic (ZMod 4)ˣ := by
  apply isCyclic_of_prime_card (p := 2)
  simp only [Nat.card_eq_fintype_card, card_units_eq_totient]
  decide

/-- The multiplicative group of `ZMod p` is cyclic. -/
/-
**ZMod.isCyclic_units_prime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_prime {p : Nat} (hp : p.Prime) : IsCyclic (ZMod p)ˣ
参数：hp : p.Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ

--- 原说明 ---
The multiplicative group of `ZMod p` is cyclic.
-/
theorem isCyclic_units_prime {p : ℕ} (hp : p.Prime) :
    IsCyclic (ZMod p)ˣ :=
  have : Fact (p.Prime) := ⟨hp⟩
  inferInstance
/-
**ZMod.not_isCyclic_units_eight** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：not_isCyclic_units_eight : ¬ IsCyclic (ZMod 8)ˣ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclic.iff_exponent_eq_card`：IsCyclic.iff_exponent_eq_card [CommGroup 
α] [Finite α] : IsCyclic α ↔ exponent α = Nat.card α
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Monoid.exponent_dvd_of_forall_pow_eq_one`：∀ {G : Type u} [inst : Monoid 
G] {n : ℕ}, (∀ (g : G), g ^ n = 1) → Monoid.exponent G ∣ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.dvd_eq_false_of_mod_ne_zero`：∀ {m n : ℕ}, (n % m != 0) = true → (m ∣
 n) = False
-/
theorem not_isCyclic_units_eight :
    ¬ IsCyclic (ZMod 8)ˣ := by
  rw [IsCyclic.iff_exponent_eq_card, Nat.card_eq_fintype_card, card_units_eq_totient]
  have h : Monoid.exponent (ZMod 8)ˣ ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
  intro (h' : Monoid.exponent (ZMod 8)ˣ = 4)
  simp [h'] at h

end EasyCases

section Divisibility

variable {R : Type*} [CommSemiring R] {u v : R} {p : ℕ}

/-
**ZMod.exists_one_add_mul_pow_prime_eq** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：exists_one_add_mul_pow_prime_eq (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u
 * v ∣ u ^ p) (x : R) : exists y, (1 + u * x) ^ p = 1 + p * u * (x + v * y)
参数：hp : p.Prime；hvu : v ∣ u；hpuv : p * u * v ∣ u ^ p；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 83 条，此处仅展示前 30 条）
-/
lemma exists_one_add_mul_pow_prime_eq
    (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) :
    ∃ y, (1 + u * x) ^ p = 1 + p * u * (x + v * y) := by
  rw [add_comm, add_pow]
  rw [← Finset.add_sum_erase (a := 0) _ _ (by simp)]
  simp_rw [one_pow, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [← Finset.add_sum_erase (a := 1) _ _ (by simp [hp.pos])]
  rw [← Finset.sum_erase_add (a := p) _ _ (by -- aesop works but is slow
      simp only [Finset.mem_erase]
      rw [← and_assoc, and_comm (a := ¬ _), ← Nat.two_le_iff]
      simp [hp.two_le])]
  obtain ⟨a, ha⟩ := hvu
  obtain ⟨b, hb⟩ := hpuv
  use a * x ^ 2 * ∑ i ∈ (((Finset.range (p + 1)).erase 0).erase 1).erase p,
    (u * x) ^ (i - 2) * (p.choose i / p : ℕ) + b * x ^ p
  rw [mul_add]
  congr 2
  · rw [Nat.choose_one_right]; ring
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · congr! 1 with i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
    have hi' : 2 ≤ i := by lia
    calc
      (u * x) ^ i * p.choose i =
        (u * x) ^ (2 + (i - 2)) * p.choose i := by rw [Nat.add_sub_of_le hi']
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * p.choose i := by ring_nf
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * (p * (p.choose i / p) : ℕ) := by
        rw [Nat.mul_div_cancel' (hp.dvd_choose_self hi.2.2.1 <| by lia)]
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * p * (p.choose i / p : ℕ) := by
        simp only [Nat.cast_mul]; ring_nf
      _ = p * u * (v * (a * x ^ 2 * ((u * x) ^ (i - 2) * (p.choose i / p : ℕ)))) := by
        rw [ha]; ring
  · calc
      (u * x) ^ p * (p.choose p) = u ^ p * x ^ p := by simp [Nat.choose_self, mul_pow]
    _ = p * u * v * b * x ^ p := by rw [hb]
    _ = p * u * (v * (b * x ^ p)) := by ring_nf
/-
**ZMod.exists_one_add_mul_pow_prime_pow_eq** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：exists_one_add_mul_pow_prime_pow_eq {u v : R} (hp : p.Prime) (hvu : v ∣ u)
 (hpuv : p * u * v ∣ u ^ p) (x : R) (m : Nat) : exists y, (1 + u * x) ^ (p ^ m) 
= 1 + p ^ m * u * (x + v * y)
参数：hp : p.Prime；hvu : v ∣ u；hpuv : p * u * v ∣ u ^ p；x : R；m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_one_add_mul_pow_prime_pow_eq {u v : R}
    (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) (m : ℕ) :
    ∃ y, (1 + u * x) ^ (p ^ m) = 1 + p ^ m * u * (x + v * y) :=
  match m with
  | 0 => ⟨0, by simp⟩
  | m + 1 => by
    rw [pow_succ', pow_mul]
    obtain ⟨y, hy⟩ := exists_one_add_mul_pow_prime_eq hp hvu hpuv x
    rw [hy]
    obtain ⟨z, hz⟩ :=
      exists_one_add_mul_pow_prime_pow_eq (u := p * u) (v := p * v) hp
      (mul_dvd_mul_left _ hvu)
      (by
        rw [mul_pow]
        simp only [← mul_assoc]
        rw [mul_assoc, mul_assoc, ← mul_assoc u, mul_comm u]
        apply mul_dvd_mul _ hpuv
        rw [← pow_two]
        exact pow_dvd_pow _ hp.two_le)
      (x + v * y) m
    use y + p * z
    rw [hz]
    ring

end Divisibility

section PrimePow

/-
**ZMod.orderOf_one_add_mul_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：orderOf_one_add_mul_prime_pow {p : Nat} (hp : p.Prime) (m : Nat) (hm0 : m 
!= 0) (hpm : m + 2 <= p * m) (a : Int) (ha : ¬ (p : Int) ∣ a) (n : Nat) : orderO
f (1 + p ^ m * a : ZMod (p ^ (n + m))) = p ^ n
参数：hp : p.Prime；m : Nat；hm0 : m != 0；hpm : m + 2 <= p * m；a : Int；ha : ¬ (p : In
t) ∣ a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ZMod.exists_one_add_mul_pow_prime_pow_eq`：exists_one_add_mul_pow_prime_p
ow_eq {u v : R} (hp : p.Prime) (hvu : v ∣ u) (hpuv : p * u * v ∣ u ^ p) (x : R) 
(m : Nat) : exists y, (1 + u *…
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `orderOf_eq_prime_pow`：orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin
 : x ^ p ^ (n + 1) = 1) : orderOf x = p ^ (n + 1)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
（共 40 条，此处仅展示前 30 条）
-/
theorem orderOf_one_add_mul_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) (hm0 : m ≠ 0)
    (hpm : m + 2 ≤ p * m) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + p ^ m * a : ZMod (p ^ (n + m))) = p ^ n := by
  match n with
  | 0 => rw [← Nat.cast_pow, zero_add m, ZMod.natCast_self]; simp
  | n + 1 =>
    have := Fact.mk hp
    have := exists_one_add_mul_pow_prime_pow_eq
      (R := ZMod (p ^ (n + 1 + m))) (u := p ^ m) (v := p) hp (dvd_pow_self _ hm0) ?_ a
    · apply orderOf_eq_prime_pow
      · obtain ⟨y, hy⟩ := this n
        rw [hy, ← pow_add, add_eq_left, mul_add, ← mul_assoc, ← pow_succ]
        simp_rw [add_right_comm n _ 1, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
        rwa [← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd, add_right_comm,
          pow_succ, Nat.cast_mul, Int.mul_dvd_mul_iff_left (by simp [hp.ne_zero])]
      · obtain ⟨y, hy⟩ := this (n + 1)
        rw [hy, ← pow_add, ← Nat.cast_pow]
        simp
    · rw [← pow_succ', ← pow_succ, ← pow_mul, mul_comm]
      exact pow_dvd_pow _ hpm
/-
**ZMod.orderOf_one_add_mul_prime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：orderOf_one_add_mul_prime {p : Nat} (hp : p.Prime) (hp2 : p != 2) (a : Int
) (ha : ¬ (p : Int) ∣ a) (n : Nat) : orderOf (1 + p * a : ZMod (p ^ (n + 1))) = 
p ^ n
参数：hp : p.Prime；hp2 : p != 2；a : Int；ha : ¬ (p : Int) ∣ a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ZMod.orderOf_one_add_mul_prime_pow`：orderOf_one_add_mul_prime_pow {p : N
at} (hp : p.Prime) (m : Nat) (hm0 : m != 0) (hpm : m + 2 <= p * m) (a : Int) (ha
 : ¬ (p : Int) ∣ a) (n :…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem orderOf_one_add_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (n : ℕ) :
    orderOf (1 + p * a : ZMod (p ^ (n + 1))) = p ^ n := by
  convert! orderOf_one_add_mul_prime_pow hp 1 one_ne_zero _ a ha n using 1
  · rw [pow_one]
  · have := hp.two_le; lia
/-
**ZMod.orderOf_one_add_prime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：orderOf_one_add_prime {p : Nat} (hp : p.Prime) (hp2 : p != 2) (n : Nat) : 
orderOf (1 + p : ZMod (p ^ (n + 1))) = p ^ n
参数：hp : p.Prime；hp2 : p != 2；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ZMod.orderOf_one_add_mul_prime`：orderOf_one_add_mul_prime {p : Nat} (hp 
: p.Prime) (hp2 : p != 2) (a : Int) (ha : ¬ (p : Int) ∣ a) (n : Nat) : orderOf (
1 + p * a : ZMod (p …
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Int.eq_one_of_dvd_one`：∀ {a : ℤ}, 0 ≤ a → a ∣ 1 → a = 1
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
theorem orderOf_one_add_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    orderOf (1 + p : ZMod (p ^ (n + 1))) = p ^ n := by
  convert! orderOf_one_add_mul_prime hp hp2 1 _ n
  · simp
  · intro H
    apply hp.ne_one
    simpa using Int.eq_one_of_dvd_one (Int.natCast_nonneg p) H

/-- If `p` is an odd prime, then `(ZMod (p ^ n))ˣ` is cyclic for all n -/
/-
**ZMod.isCyclic_units_of_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_of_prime_pow (p : Nat) (hp : p.Prime) (hp2 : p != 2) (n : N
at) : IsCyclic (ZMod (p ^ n))ˣ
参数：p : Nat；hp : p.Prime；hp2 : p != 2；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `isCyclic_of_subsingleton`：∀ {α : Type u_1} [inst : Group α] [Subsingleto
n α], IsCyclic α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Nat.Coprime.pow_right`：∀ {k m : ℕ} (n : ℕ), k.Coprime m → k.Coprime (m ^
 n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.coprime_one_left_eq_true`：∀ (n : ℕ), Nat.Coprime 1 n = True
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Units.coeHom_injective`：coeHom_injective : Function.Injective (coeHom M)
· 使用定理 `Units.coeHom_apply`：coeHom_apply (x : Mˣ) : coeHom M x = ↑x
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `ZMod.orderOf_one_add_prime`：orderOf_one_add_prime {p : Nat} (hp : p.Prim
e) (hp2 : p != 2) (n : Nat) : orderOf (1 + p : ZMod (p ^ (n + 1))) = p ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isCyclic_iff_exists_orderOf_eq_natCard`：isCyclic_iff_exists_orderOf_eq_n
atCard [Finite α] : IsCyclic α ↔ exists g : α, orderOf g = Nat.card α
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `ZMod.isCyclic_units_prime`：isCyclic_units_prime {p : Nat} (hp : p.Prime)
 : IsCyclic (ZMod p)ˣ
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
· 使用定理 `instNeZeroNatHMul`：∀ {n m : ℕ} [hn : NeZero n] [hm : NeZero m], NeZero (
n * m)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `orderOf_map_dvd`：orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G ->* H) (x
 : G) : orderOf (ψ x) ∣ orderOf x
· 使用引理 `orderOf_pow_orderOf_div`：orderOf_pow_orderOf_div {x : G} {n : Nat} (hx :
 orderOf x != 0) (hn : n ∣ orderOf x) : orderOf (x ^ (orderOf x / n)) = n
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is an odd prime, then `(ZMod (p ^ n))ˣ` is cyclic for all n
-/
theorem isCyclic_units_of_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    IsCyclic (ZMod (p ^ n))ˣ := by
  have := Fact.mk hp
  rcases n with _ | n
  · rw [pow_zero]; infer_instance
  -- We first consider the element `1 + p` of order `p ^ n`
  set a := (1 + p : ZMod (p ^ (n + 1))) with ha_def
  have ha : IsUnit a := by
    rw [ha_def, ← Nat.cast_one (R := ZMod _), ← Nat.cast_add, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    simp only [Nat.coprime_add_self_left, Nat.coprime_one_left_eq_true]
  have ha' : orderOf ha.unit = p ^ n := by
    rw [← orderOf_injective _ Units.coeHom_injective ha.unit, Units.coeHom_apply, IsUnit.unit_spec]
    exact orderOf_one_add_prime hp hp2 n
  -- We lift a primitive root of unity mod `p`, an adequate power of which has order `p - 1`.
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  obtain ⟨(b : (ZMod (p ^ (n + 1)))ˣ), rfl⟩ :=
    ZMod.unitsMap_surjective (Dvd.intro_left (p ^ n) rfl) c
  have : p - 1 ∣ orderOf b := hc ▸ orderOf_map_dvd _ b
  let k := orderOf b / (p - 1)
  have : orderOf (b ^ k) = p - 1 := orderOf_pow_orderOf_div (orderOf_pos b).ne' this
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  -- The product of `ha.unit` and `b ^ k` has the required order
  use ha.unit * b ^ k
  rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, this, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp, ← ha']
  rw [ha', this]
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_self_sub_right hp.pos]
  simp
/-
**ZMod.isCyclic_units_two_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_two_pow_iff (n : Nat) : IsCyclic (ZMod (2 ^ n))ˣ ↔ n <= 2
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZMod.isCyclic_units_prime`：isCyclic_units_prime {p : Nat} (hp : p.Prime)
 : IsCyclic (ZMod p)ˣ
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.Simproc.add_le_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b ≤ c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `ZMod.not_isCyclic_units_eight`：not_isCyclic_units_eight : ¬ IsCyclic (ZM
od 8)ˣ
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
-/
theorem isCyclic_units_two_pow_iff (n : ℕ) :
    IsCyclic (ZMod (2 ^ n))ˣ ↔ n ≤ 2 := by
  match n with
  | 0 => simp [isCyclic_units_one]
  | 1 => simp [isCyclic_units_prime Nat.prime_two]
  | 2 => simp [isCyclic_units_four]
  | n + 3 =>
    simp only [Nat.reduceLeDiff, iff_false]
    intro H
    apply not_isCyclic_units_eight
    have h : 2 ^ 3 ∣ 2 ^ (n + 3) := pow_dvd_pow _ (by lia)
    exact isCyclic_of_surjective _ (unitsMap_surjective h)
/-
**ZMod.orderOf_one_add_four_mul** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：orderOf_one_add_four_mul (a : Int) (ha : Odd a) (n : Nat) : orderOf (1 + 4
 * a : ZMod (2 ^ (n + 2))) = 2 ^ n
参数：a : Int；ha : Odd a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZMod.orderOf_one_add_mul_prime_pow`：orderOf_one_add_mul_prime_pow {p : N
at} (hp : p.Prime) (m : Nat) (hm0 : m != 0) (hpm : m + 2 <= p * m) (a : Int) (ha
 : ¬ (p : Int) ∣ a) (n :…
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
-/
lemma orderOf_one_add_four_mul (a : ℤ) (ha : Odd a) (n : ℕ) :
    orderOf (1 + 4 * a : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  convert! orderOf_one_add_mul_prime_pow Nat.prime_two 2 two_ne_zero le_rfl a ?_ n using 1
  · norm_num
  · rwa [← Int.not_even_iff_odd, even_iff_two_dvd] at ha
/-
**ZMod.orderOf_five** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：orderOf_five (n : Nat) : orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_intCast`：isNat_intCast {R} [Ring R] (n : Int)
 (m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用引理 `ZMod.orderOf_one_add_four_mul`：orderOf_one_add_four_mul (a : Int) (ha : 
Odd a) (n : Nat) : orderOf (1 + 4 * a : ZMod (2 ^ (n + 2))) = 2 ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem orderOf_five (n : ℕ) :
    orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n := by
  convert! orderOf_one_add_four_mul 1 (by simp) n
  norm_num

end PrimePow

section Products

/-
**ZMod.isCyclic_units_four_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_four_mul_iff (n : Nat) : IsCyclic (ZMod (4 * n))ˣ ↔ n = 0 ∨
 n = 1
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
· 使用定理 `instNeZeroNatHMul`：∀ {n m : ℕ} [hn : NeZero n] [hm : NeZero m], NeZero (
n * m)
· 使用定理 `ZMod.not_isCyclic_units_eight`：not_isCyclic_units_eight : ¬ IsCyclic (ZM
od 8)ˣ
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `MulEquiv.isCyclic`：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCycl
ic G'
（共 37 条，此处仅展示前 30 条）
-/
theorem isCyclic_units_four_mul_iff (n : ℕ) :
    IsCyclic (ZMod (4 * n))ˣ ↔ n = 0 ∨ n = 1 := by
  obtain rfl | hn0 := eq_or_ne n 0
  · simp [isCyclic_units_zero]
  obtain rfl | hn1 := eq_or_ne n 1
  · simp [isCyclic_units_four]
  refine iff_of_false ?_ (by simp [hn0, hn1])
  obtain ⟨n, rfl⟩ | h2n := em (2 ∣ n)
  · rw [← mul_assoc]
    have : NeZero n := ⟨by simpa using hn0⟩
    refine mt (fun _ ↦ ?_) not_isCyclic_units_eight
    exact isCyclic_of_surjective _ (ZMod.unitsMap_surjective (m := 4 * 2 * n) (dvd_mul_right 8 _))
  have : Nat.Coprime 4 n := (Nat.prime_two.coprime_iff_not_dvd.mpr h2n).pow_left 2
  rw [((Units.mapEquiv (chineseRemainder this).toMulEquiv).trans .prodUnits).isCyclic,
    Group.isCyclic_prod_iff]
  rintro ⟨-, -, h⟩
  have : NeZero n := ⟨hn0⟩
  have : Odd (φ n) := by simpa [show φ 4 = 2 from rfl] using h
  rw [Nat.odd_totient_iff] at this
  lia
/-
**ZMod.isCyclic_units_two_mul_iff_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_two_mul_iff_of_odd (n : Nat) (hn : Odd n) : IsCyclic (ZMod 
(2 * n))ˣ ↔ IsCyclic (ZMod n)ˣ
参数：n : Nat；hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.isCyclic`：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCycl
ic G'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_two_left`：∀ {n : ℕ}, Nat.Coprime 2 n ↔ Odd n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.coprime_one_left_eq_true`：∀ (n : ℕ), Nat.Coprime 1 n = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCyclic_units_two_mul_iff_of_odd (n : ℕ) (hn : Odd n) :
    IsCyclic (ZMod (2 * n))ˣ ↔ IsCyclic (ZMod n)ˣ := by
  simp [((Units.mapEquiv (chineseRemainder <| Nat.coprime_two_left.mpr hn).toMulEquiv).trans
    .prodUnits).isCyclic, Group.isCyclic_prod_iff, isCyclic_units_two]
/-
**ZMod.not_isCyclic_units_of_mul_coprime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：not_isCyclic_units_of_mul_coprime (m n : Nat) (hm : Odd m) (hm1 : m != 1) 
(hn : Odd n) (hn1 : n != 1) (hmn : m.Coprime n) : ¬ IsCyclic (ZMod (m * n))ˣ
参数：m n : Nat；hm : Odd m；hm1 : m != 1；hn : Odd n；hn1 : n != 1；hmn : m.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ne_of_odd_add`：ne_of_odd_add (h : Odd (m + n)) : m != n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.isCyclic`：MulEquiv.isCyclic (e : G ≃* G') : IsCyclic G ↔ IsCycl
ic G'
· 使用定理 `Group.isCyclic_prod_iff`：Group.isCyclic_prod_iff {M N : Type*} [Group M]
 [Group N] : IsCyclic (M × N) ↔ IsCyclic M ∧ IsCyclic N ∧ (Nat.card M).Coprime (
Nat.card N)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem not_isCyclic_units_of_mul_coprime (m n : ℕ)
    (hm : Odd m) (hm1 : m ≠ 1) (hn : Odd n) (hn1 : n ≠ 1) (hmn : m.Coprime n) :
    ¬ IsCyclic (ZMod (m * n))ˣ := by
  have _ : NeZero m := ⟨Nat.ne_of_odd_add hm⟩
  have _ : NeZero n := ⟨Nat.ne_of_odd_add hn⟩
  let e := (Units.mapEquiv (chineseRemainder hmn).toMulEquiv).trans .prodUnits
  rw [e.isCyclic, Group.isCyclic_prod_iff]
  rintro ⟨-, -, h⟩
  simp_rw [Nat.card_eq_fintype_card, card_units_eq_totient,
    Nat.totient_coprime_totient_iff, hm1, hn1, false_or] at h
  rcases h with (rfl | rfl)
  · simp [← Nat.not_even_iff_odd] at hm
  · simp [← Nat.not_even_iff_odd] at hn
/-
**ZMod.isCyclic_units_iff_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_iff_of_odd {n : Nat} (hn : Odd n) : IsCyclic (ZMod n)ˣ ↔ ex
ists (p m : Nat), p.Prime ∧ Odd p ∧ n = p ^ m
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_odd_zero`：¬Odd 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用引理 `Odd.of_dvd_nat`：Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `ZMod.isCyclic_units_of_prime_pow`：isCyclic_units_of_prime_pow (p : Nat) 
(hp : p.Prime) (hp2 : p != 2) (n : Nat) : IsCyclic (ZMod (p ^ n))ˣ
· 使用引理 `Odd.ne_two_of_dvd_nat`：Odd.ne_two_of_dvd_nat {m n : Nat} (hn : Odd n) (h
m : m ∣ n) : m != 2
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `ZMod.not_isCyclic_units_of_mul_coprime`：not_isCyclic_units_of_mul_coprim
e (m n : Nat) (hm : Odd m) (hm1 : m != 1) (hn : Odd n) (hn1 : n != 1) (hmn : m.C
oprime n) : ¬ IsCyclic (ZMod…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.factorization_pos_of_dvd`：∀ {n p : ℕ}, Nat.Prime p → n ≠ 0 → p
 ∣ n → 0 < n.factorization p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 40 条，此处仅展示前 30 条）
-/
theorem isCyclic_units_iff_of_odd {n : ℕ} (hn : Odd n) :
    IsCyclic (ZMod n)ˣ ↔ ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ n = p ^ m := by
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  obtain rfl | h1 := eq_or_ne n 1
  · simp_rw [isCyclic_units_one, true_iff]
    exact ⟨3, 0, Nat.prime_three, by simp [Nat.odd_iff], by rw [pow_zero]⟩
  have ⟨p, hp, dvd⟩ := n.exists_prime_and_dvd h1
  have odd := hn.of_dvd_nat dvd
  by_cases hnp : n = p ^ n.factorization p
  · exact hnp ▸ iff_of_true (isCyclic_units_of_prime_pow p hp (odd.ne_two_of_dvd_nat dvd_rfl) _)
      ⟨p, _, hp, odd, rfl⟩
  refine iff_of_false ?_ (mt ?_ hnp)
  · have := n.ordProj_dvd p
    rw [← Nat.mul_div_cancel' this]
    refine not_isCyclic_units_of_mul_coprime _ _ (hn.of_dvd_nat this) ?_
      (hn.of_dvd_nat (Nat.div_dvd_of_dvd this)) ?_ ((Nat.coprime_ordCompl hp hn0).pow_left ..)
    · simpa [(hp.factorization_pos_of_dvd hn0 dvd).ne'] using hp.ne_one
    · contrapose hnp
      conv_lhs => rw [← Nat.div_mul_cancel this, hnp, one_mul]
  rintro ⟨q, m, hq, -, rfl⟩
  cases (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow dvd)
  simp [hp.factorization_self] at hnp

end Products

/-- `(ZMod n)ˣ` is cyclic iff `n` is of the form
`0`, `1`, `2`, `4`, `p ^ m`, or `2 * p ^ m`,
where `p` is an odd prime and `1 ≤ m`. -/
/-
**ZMod.isCyclic_units_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isCyclic_units_iff (n : Nat) : IsCyclic (ZMod n)ˣ ↔ n = 0 ∨ n = 1 ∨ n = 2 
∨ n = 4 ∨ exists (p m : Nat), p.Prime ∧ Odd p ∧ 1 <= m ∧ (n = p ^ m ∨ n = 2 * p 
^ m)
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `ZMod.isCyclic_units_iff_of_odd`：isCyclic_units_iff_of_odd {n : Nat} (hn 
: Odd n) : IsCyclic (ZMod n)ˣ ↔ exists (p m : Nat), p.Prime ∧ Odd p ∧ n = p ^ m
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
`(ZMod n)ˣ` is cyclic iff `n` is of the form
`0`, `1`, `2`, `4`, `p ^ m`, or `2 * p ^ m`,
where `p` is an odd prime and `1 ≤ m`.
-/
theorem isCyclic_units_iff (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨
      ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) := by
  by_cases h0 : n = 0
  · rw [h0]; simp [isCyclic_units_zero]
  by_cases h1 : n = 1
  · rw [h1]; simp [isCyclic_units_one]
  by_cases h2 : n = 2
  · rw [h2]; simp [isCyclic_units_two]
  by_cases h4 : n = 4
  · rw [h4]; simp [isCyclic_units_four]
  simp only [h0, h1, h2, h4, false_or, and_or_left, exists_or]
  rcases (n.even_or_odd).symm with hn | hn
  · rw [isCyclic_units_iff_of_odd hn, or_iff_left]
    · congr! with p m
      rw [and_iff_right_of_imp]
      rintro rfl
      contrapose! h1
      cases Nat.lt_one_iff.mp h1
      apply pow_zero
    · rintro ⟨p, m, -, -, -, rfl⟩
      simp [← Nat.not_even_iff_odd] at hn
  obtain ⟨n, rfl⟩ := hn.two_dvd
  rcases (n.even_or_odd).symm with hn | hn
  · rw [isCyclic_units_two_mul_iff_of_odd _ hn, isCyclic_units_iff_of_odd hn, or_iff_right]
    · congr! with p m
      rw [Nat.mul_left_cancel_iff zero_lt_two, and_iff_right_of_imp]
      rintro rfl
      contrapose! h2
      cases Nat.lt_one_iff.mp h2
      rw [pow_zero, mul_one]
    · rintro ⟨p, m, -, odd, -, eq⟩
      have := eq ▸ odd.pow
      simp [← Nat.not_even_iff_odd] at this
  obtain ⟨n, rfl⟩ := hn.two_dvd
  apply iff_of_false
  · rw [← mul_assoc, show 2 * 2 = 4 from rfl, isCyclic_units_four_mul_iff]
    lia
  grind

end ZMod

