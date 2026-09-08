/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Unique factorization and multiplicity

## Main results

* `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`: The multiplicity of an
  irreducible factor of a nonzero element is exactly the number of times the normalized factor
  occurs in the `normalizedFactors`.
-/

public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/-
**WfDvdMonoid.max_power_factor'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WfDvdMonoid.max_power_factor' [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x
 : α} (h : a₀ != 0) (hx : ¬IsUnit x) : exists (n : Nat) (a : α), ¬x ∣ a ∧ a₀ = x
 ^ n * a
参数：h : a₀ != 0；hx : ¬IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem WfDvdMonoid.max_power_factor' [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : ¬IsUnit x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a := by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | ∃ n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _⟩
/-
**WfDvdMonoid.max_power_factor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WfDvdMonoid.max_power_factor [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x 
: α} (h : a₀ != 0) (hx : Irreducible x) : exists (n : Nat) (a : α), ¬x ∣ a ∧ a₀ 
= x ^ n * a
参数：h : a₀ != 0；hx : Irreducible x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.max_power_factor'`：WfDvdMonoid.max_power_factor' [CommMonoid
WithZero α] [WfDvdMonoid α] {a₀ x : α} (h : a₀ != 0) (hx : ¬IsUnit x) : exists (
n : Nat) (a : α), ¬…
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
-/
theorem WfDvdMonoid.max_power_factor [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : Irreducible x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a :=
  max_power_factor' h hx.not_isUnit
/-
**FiniteMultiplicity.of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.of_not_isUnit [CommMonoidWithZero α] [IsCancelMulZero α
] [WfDvdMonoid α] {a b : α} (ha : ¬IsUnit a) (hb : b != 0) : FiniteMultiplicity 
a b
参数：ha : ¬IsUnit a；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.max_power_factor'`：WfDvdMonoid.max_power_factor' [CommMonoid
WithZero α] [WfDvdMonoid α] {a₀ x : α} (h : a₀ != 0) (hx : ¬IsUnit x) : exists (
n : Nat) (a : α), ¬…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem FiniteMultiplicity.of_not_isUnit [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : ¬IsUnit a) (hb : b ≠ 0) : FiniteMultiplicity a b := by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩
/-
**FiniteMultiplicity.of_prime_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.of_prime_left [CommMonoidWithZero α] [IsCancelMulZero α
] [WfDvdMonoid α] {a b : α} (ha : Prime a) (hb : b != 0) : FiniteMultiplicity a 
b
参数：ha : Prime a；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.of_not_isUnit`：FiniteMultiplicity.of_not_isUnit [Comm
MonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {a b : α} (ha : ¬IsUnit a)
 (hb : b != 0) : Finit…
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
-/
theorem FiniteMultiplicity.of_prime_left [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : Prime a) (hb : b ≠ 0) : FiniteMultiplicity a b :=
  .of_not_isUnit ha.not_isUnit hb

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section multiplicity

variable [NormalizationMonoid R]

open Multiset

/-
**UniqueFactorizationMonoid.le_emultiplicity_iff_replicate_le_normalizedFactors*
* 是 Mathlib 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：le_emultiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : Nat} (h
a : Irreducible a) (hb : b != 0) : ↑n <= emultiplicity a b ↔ replicate n (normal
ize a) <= normalizedFactors b
参数：ha : Irreducible a；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Multiset.instCanonicallyOrderedAdd`：∀ {α : Type u_1}, CanonicallyOrdered
Add (Multiset α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Multiset.replicate_succ`：∀ {α : Type u_1} (a : α) (n : ℕ), Multiset.repl
icate (n + 1) a = a ::ₘ Multiset.replicate n a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
（共 39 条，此处仅展示前 30 条）
-/
theorem le_emultiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : ℕ} (ha : Irreducible a)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n (normalize a) ≤ normalizedFactors b := by
  rw [← pow_dvd_iff_le_emultiplicity]
  revert b
  induction n with
  | zero => simp
  | succ n ih => ?_
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne, pow_succ', mul_assoc, mul_eq_zero, not_or] at hb
    rw [pow_succ', mul_assoc, normalizedFactors_mul hb.1 hb.2, replicate_succ,
      normalizedFactors_irreducible ha, singleton_add, cons_le_cons_iff, ← ih hb.2]
    apply Dvd.intro _ rfl
  · rw [Multiset.le_iff_exists_add]
    rintro ⟨u, hu⟩
    rw [← (prod_normalizedFactors hb).dvd_iff_dvd_right, hu, prod_add, prod_replicate]
    exact (Associated.pow_pow <| associated_normalize a).dvd.trans (Dvd.intro u.prod rfl)

variable [DecidableEq R]

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `multiplicity`, see `multiplicity_eq_count_normalizedFactors`.

See also `count_normalizedFactors_eq` which expands the definition of `multiplicity`
to produce a specification for `count (normalizedFactors _) _`..
-/
/-
**UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors** 是 Mathlib
 中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：emultiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (h
b : b != 0) : emultiplicity a b = (normalizedFactors b).count (normalize a)
参数：ha : Irreducible a；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.le_of_lt_add_one`：le_of_lt_add_one (h : x < y + 1) : x <= y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `UniqueFactorizationMonoid.le_emultiplicity_iff_replicate_le_normalizedFa
ctors`：le_emultiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : Nat} (
ha : Irreducible a) (hb : b != 0) : ↑n <= emultiplicity a b ↔ repli…
· 使用定理 `Multiset.le_count_iff_replicate_le`：le_count_iff_replicate_le {a : α} {s
 : Multiset α} {n : Nat} : n <= count a s ↔ replicate n a <= s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The multiplicity of an irreducible factor of a nonzero element is exactly the nu
mber of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `multiplicity`, see `multiplicity_eq_count_normalizedFactors
`.

See also `count_normalizedFactors_eq` which expands the definition of `multiplic
ity`
to produce a specification for `count (normalizedFactors _) _`..
-/
theorem emultiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    emultiplicity a b = (normalizedFactors b).count (normalize a) := by
  apply le_antisymm
  · apply Order.le_of_lt_add_one
    rw [← Nat.cast_one, ← Nat.cast_add, lt_iff_not_ge,
      le_emultiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]
    simp
  rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `emultiplicity`, see `emultiplicity_eq_count_normalizedFactors`. -/
/-
**UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors** 是 Mathlib 
中的一个定理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：multiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb
 : b != 0) : multiplicity a b = (normalizedFactors b).count (normalize a)
参数：ha : Irreducible a；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `finiteMultiplicity_of_emultiplicity_eq_natCast`：finiteMultiplicity_of_em
ultiplicity_eq_natCast {n : Nat} (h : emultiplicity a b = n) : FiniteMultiplicit
y a b

--- 原说明 ---
The multiplicity of an irreducible factor of a nonzero element is exactly the nu
mber of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `emultiplicity`, see `emultiplicity_eq_count_normalizedFacto
rs`.
-/
theorem multiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rwa [(finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity,
    ENat.natCast_inj] at this

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
/-
**UniqueFactorizationMonoid.count_normalizedFactors_eq** 是 Mathlib 中的一个定理，位于命名空间
 `UniqueFactorizationMonoid`。
形式化陈述：count_normalizedFactors_eq {p x : R} (hp : Irreducible p) (hnorm : normali
ze p = p) {n : Nat} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) : (normalizedFact
ors x).count p = n
参数：hp : Irreducible p；hnorm : normalize p = p；hle : p ^ n ∣ x；hlt : ¬p ^ (n + 1)
 ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…

--- 原说明 ---
The number of times an irreducible factor `p` appears in `normalizedFactors x` i
s defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplic
ity p x`.
-/
theorem count_normalizedFactors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : ℕ}
    (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := ℕ∞)
  convert! (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`. This is a slightly more general version of
`UniqueFactorizationMonoid.count_normalizedFactors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
/-
**UniqueFactorizationMonoid.count_normalizedFactors_eq'** 是 Mathlib 中的一个定理，位于命名空
间 `UniqueFactorizationMonoid`。
形式化陈述：count_normalizedFactors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm 
: normalize p = p) {n : Nat} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) : (norma
lizedFactors x).count p = n
参数：hp : p = 0 ∨ Irreducible p；hnorm : normalize p = p；hle : p ^ n ∣ x；hlt : ¬p ^
 (n + 1) ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `UniqueFactorizationMonoid.zero_notMem_normalizedFactors`：zero_notMem_nor
malizedFactors (x : α) : (0 : α) ∉ normalizedFactors x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `UniqueFactorizationMonoid.count_normalizedFactors_eq`：count_normalizedFa
ctors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : Nat} (hle
 : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) : (…

--- 原说明 ---
The number of times an irreducible factor `p` appears in `normalizedFactors x` i
s defined by
the number of times it divides `x`. This is a slightly more general version of
`UniqueFactorizationMonoid.count_normalizedFactors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplic
ity p x`.
-/
theorem count_normalizedFactors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p)
    {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_notMem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt
/-
**UniqueFactorizationMonoid.associated_finprod_pow_count** 是 Mathlib 中的一个引理，位于命名
空间 `UniqueFactorizationMonoid`。
形式化陈述：associated_finprod_pow_count {x : R} (hx : x != 0) : Associated (∏ᶠ p : R,
 p ^ (normalizedFactors x).count p) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.prod_map_eq_finprod`：prod_map_eq_finprod (s : Multiset α) (f : 
α -> M) : (s.map f).prod = ∏ᶠ a, f a ^ s.count a
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
-/
lemma associated_finprod_pow_count {x : R} (hx : x ≠ 0) :
    Associated (∏ᶠ p : R, p ^ (normalizedFactors x).count p) x := by
  rw [← Multiset.prod_map_eq_finprod, Multiset.map_id']
  exact prod_normalizedFactors hx
/-
**UniqueFactorizationMonoid.finprod_pow_count_eq_of_subsingleton_units** 是 Mathl
ib 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：finprod_pow_count_eq_of_subsingleton_units [Subsingleton Rˣ] {x : R} (hx :
 x != 0) : ∏ᶠ p : R, p ^ (normalizedFactors x).count p = x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用引理 `UniqueFactorizationMonoid.associated_finprod_pow_count`：associated_finpr
od_pow_count {x : R} (hx : x != 0) : Associated (∏ᶠ p : R, p ^ (normalizedFactor
s x).count p) x
-/
lemma finprod_pow_count_eq_of_subsingleton_units [Subsingleton Rˣ] {x : R} (hx : x ≠ 0) :
    ∏ᶠ p : R, p ^ (normalizedFactors x).count p = x :=
  associated_iff_eq.mp <| associated_finprod_pow_count hx

end multiplicity

/-
**UniqueFactorizationMonoid.dvd_iff_emultiplicity_le** 是 Mathlib 中的一个引理，位于命名空间 `
UniqueFactorizationMonoid`。
形式化陈述：dvd_iff_emultiplicity_le {a b : R} (ha : a != 0) : a ∣ b ↔ forall p : R, P
rime p -> emultiplicity p a <= emultiplicity p b
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_le_emultiplicity_of_dvd_right`：emultiplicity_le_emultiplic
ity_of_dvd_right {a b c : α} (h : b ∣ c) : emultiplicity a b <= emultiplicity a 
c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma dvd_iff_emultiplicity_le {a b : R} (ha : a ≠ 0) :
    a ∣ b ↔ ∀ p : R, Prime p → emultiplicity p a ≤ emultiplicity p b := by
  classical
  refine ⟨fun h _ _ ↦ emultiplicity_le_emultiplicity_of_dvd_right h, fun h ↦ ?_⟩
  by_cases hb : b = 0
  · simp_all
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb, Multiset.le_iff_count]
  intro q
  by_cases hq : q ∈ normalizedFactors a
  · have hqprime : Prime q := prime_of_normalized_factor q hq
    have h1 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible ha
    have h2 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible hb
    rw [normalize_normalized_factor q hq] at h1 h2
    simpa [h1, h2] using h q hqprime
  · simp [Multiset.count_eq_zero_of_notMem hq]
/-
**UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Uniqu
eFactorizationMonoid`。
形式化陈述：pow_dvd_pow_iff_dvd {a b : R} {n : Nat} (hn : n != 0) : a ^ n ∣ b ^ n ↔ a 
∣ b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `UniqueFactorizationMonoid.dvd_iff_emultiplicity_le`：dvd_iff_emultiplicit
y_le {a b : R} (ha : a != 0) : a ∣ b ↔ forall p : R, Prime p -> emultiplicity p 
a <= emultiplicity p b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用引理 `ENat.mul_le_mul_left_iff`：mul_le_mul_left_iff {x y : Nat∞} (ha : a != 0)
 (h_top : a != ⊤) : a * x <= a * y ↔ x <= y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `emultiplicity_pow`：emultiplicity_pow {p a : α} (hp : Prime p) {k : Nat} 
: emultiplicity p (a ^ k) = k * emultiplicity p a
· 使用定理 `pow_dvd_pow_of_dvd`：pow_dvd_pow_of_dvd (h : a ∣ b) (n : Nat) : a ^ n ∣ b
 ^ n
-/
lemma pow_dvd_pow_iff_dvd {a b : R} {n : ℕ} (hn : n ≠ 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  by_cases ha : a = 0
  · simp [ha, hn]
  refine ⟨?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  rw [dvd_iff_emultiplicity_le (pow_ne_zero n ha), dvd_iff_emultiplicity_le ha]
  intro H p hp
  have := H p hp
  rwa [emultiplicity_pow hp, emultiplicity_pow hp,
    ENat.mul_le_mul_left_iff (by exact_mod_cast hn) (ENat.natCast_ne_top _)] at this

@[fun_prop]
/-
**UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity** 是 Mathlib
 中的一个引理，位于命名空间 `UniqueFactorizationMonoid`。
形式化陈述：hasFiniteMulSupport_fun_pow_multiplicity {α M : Type*} [CommMonoid M] [Sub
singleton Rˣ] (f : α -> M) {g : α -> R} (hgi : g.Injective) (hg : forall s, Irre
ducible (g s)) {r : R} (hr : r != 0) : (fun s : α => f s ^ multiplicity (g s) r)
.HasFiniteMulSupport
参数：f : α -> M；hgi : g.Injective；hg : forall s, Irreducible (g s)；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors`：multi
plicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0) 
: multiplicity a b = (normalizedFactors b).count (norma…
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Function.HasFiniteSupport.hasFiniteMulSupport_fun_pow`：∀ {α : Type u_1} 
{M : Type u_4} [inst : Monoid M] (f : α → M) {g : α → ℕ},   Function.HasFiniteSu
pport g → Function.HasFiniteMulSupport fun …
· 使用定理 `Function.HasFiniteSupport.comp_of_injective`：∀ {α : Type u_1} {M : Type 
u_2} [inst : Zero M] {β : Type u_3} {f : β → M} {g : α → β},   Function.Injectiv
e g → Function.HasFiniteSupport f…
· 使用引理 `Multiset.hasFiniteSupport_count`：Multiset.hasFiniteSupport_count {α : Ty
pe*} [DecidableEq α] (s : Multiset α) : (count · s).HasFiniteSupport
-/
lemma hasFiniteMulSupport_fun_pow_multiplicity {α M : Type*} [CommMonoid M] [Subsingleton Rˣ]
    (f : α → M) {g : α → R} (hgi : g.Injective) (hg : ∀ s, Irreducible (g s)) {r : R} (hr : r ≠ 0) :
    (fun s : α ↦ f s ^ multiplicity (g s) r).HasFiniteMulSupport := by
  classical
  simp only [multiplicity_eq_count_normalizedFactors (hg _) hr, normalize_eq]
  fun_prop

end UniqueFactorizationMonoid

