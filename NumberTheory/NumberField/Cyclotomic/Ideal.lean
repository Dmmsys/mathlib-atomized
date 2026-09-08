/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Ideals in cyclotomic fields

In this file, we prove results about ideals in cyclotomic extensions of `ℚ`.

## Main results

* `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`: there is only one prime ideal above
  the prime `p` in `ℚ(ζ_pᵏ)`

* `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow`: the residual degree of the prime ideal
  above `p` in `ℚ(ζ_pᵏ)` is `1`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`: the ramification index of the prime
  ideal above `p` in `ℚ(ζ_pᵏ)` is `p ^ (k - 1) * (p - 1)`.

* `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd`: if the prime `p` does not divide `m`, then
  the inertia degree of `p` in `ℚ(ζₘ)` is the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd`: if the prime `p` does not divide `m`,
  then the ramification index of `p` in `ℚ(ζₘ)` is `1`.

* `IsCyclotomicExtension.Rat.inertiaDegIn_eq`: write `n = p ^ (k + 1) * m` where the prime `p` does
  not divide `m`, then the inertia degree of `p` in `ℚ(ζₙ)` is the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq`: write `n = p ^ (k + 1) * m` where the prime `p`
  does not divide `m`, then the ramification index of `p` in `ℚ(ζₙ)` is `p ^ k * (p - 1)`.

-/

public section

namespace IsCyclotomicExtension.Rat

open Ideal NumberField RingOfIntegers

variable (n m p k : ℕ) [hp : Fact (Nat.Prime p)] (K : Type*) [Field K] [NumberField K]
  (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver (span {(p : ℤ)})]

local notation3 "𝒑" => (span {(p : ℤ)})

section PrimePow

variable {K} [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

/-
**IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one** 是 Mathlib 中的一个实例，位于命名空间 
`IsCyclotomicExtension.Rat`。
形式化陈述：isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1})
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `IsPrimitiveRoot.zeta_sub_one_prime`：zeta_sub_one_prime [IsCyclotomicExte
nsion {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.to
Integer - 1)
-/
instance isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1}) := by
  rw [span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime
/-
**IsCyclotomicExtension.Rat.associated_norm_zeta_sub_one** 是 Mathlib 中的一个定理，位于命名
空间 `IsCyclotomicExtension.Rat`。
形式化陈述：associated_norm_zeta_sub_one : Associated (Algebra.norm Int (hζ.toInteger 
- 1)) (p : Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two`：norm_toInteger_sub_one
_of_eq_two [IsCyclotomicExtension {2} Rat K] (hζ : IsPrimitiveRoot ζ 2) : norm I
nt (hζ.toInteger - 1) = -2
· 使用定理 `Int.ofNat_two`：↑2 = 2
· 使用引理 `Associated.neg_left_iff`：neg_left_iff : Associated (-a) b ↔ Associated a
 b
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two_pow`：norm_toInteger_sub
_one_of_eq_two_pow {k : Nat} {K : Type*} [Field K] {ζ : K} [CharZero K] [IsCyclo
tomicExtension {2 ^ (k + 2)} Rat K] (hζ : …
· 使用引理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two`：norm_toInteger_s
ub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimi
tiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : …
-/
theorem associated_norm_zeta_sub_one : Associated (Algebra.norm ℤ (hζ.toInteger - 1)) (p : ℤ) := by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h, zero_add, pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two, h, Int.ofNat_two, Associated.neg_left_iff]
    | succ n =>
      rw [h, add_assoc, one_add_one_eq_two] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two_pow, h, Int.ofNat_two]
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two h]

/-- An integer `n` is divisible by `ζ - 1` in `𝓞 K` if and only if it is divisible by `p`,
where `ζ` is a primitive `p ^ (k + 1)`-th root of unity. -/
/-
**IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff** 是 Mathlib 中的一个定理，位于命名
空间 `IsCyclotomicExtension.Rat`。
形式化陈述：zeta_sub_one_dvd_intCast_iff {n : Int} : hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (p
 : Int) ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.Rat.associated_norm_zeta_sub_one`：associated_norm_
zeta_sub_one : Associated (Algebra.norm Int (hζ.toInteger - 1)) (p : Int)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.norm_dvd_iff`：norm_dvd_iff {x : S} (hx : Prime (Algebra.norm Int x
)) {y : Int} : Algebra.norm Int x ∣ y ↔ x ∣ y
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Associated.prime`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {p q : 
M}, Associated p q → Prime p → Prime q
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Associated.dvd_iff_dvd_left`：Associated.dvd_iff_dvd_left [Monoid M] {a b
 c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c

--- 原说明 ---
An integer `n` is divisible by `ζ - 1` in `𝓞 K` if and only if it is divisible b
y `p`,
where `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
-/
theorem zeta_sub_one_dvd_intCast_iff {n : ℤ} :
    hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (p : ℤ) ∣ n := by
  have h := associated_norm_zeta_sub_one p k hζ
  rw [← Ideal.norm_dvd_iff (h.symm.prime (Nat.prime_iff_prime_int.mp hp.out))]
  exact h.dvd_iff_dvd_left
/-
**IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one** 是 Mathlib 中的一个定理，位于命名空间 
`IsCyclotomicExtension.Rat`。
形式化陈述：absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.norm_self`：norm_self : Algebra.norm R = MonoidHom.id R
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `IsCyclotomicExtension.Rat.associated_norm_zeta_sub_one`：associated_norm_
zeta_sub_one : Associated (Algebra.norm Int (hζ.toInteger - 1)) (p : Int)
-/
theorem absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p := by
  simpa using congr_arg absNorm <|
    span_singleton_eq_span_singleton.mpr <| associated_norm_zeta_sub_one p k hζ
/-
**IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `I
sCyclotomicExtension.Rat`。
形式化陈述：p_mem_span_zeta_sub_one : (p : 𝓞 K) in span {hζ.toInteger - 1}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one`：absNorm_span_zeta_s
ub_one : absNorm (span {hζ.toInteger - 1}) = p
· 使用定理 `Ideal.absNorm_mem`：absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I
-/
theorem p_mem_span_zeta_sub_one : (p : 𝓞 K) ∈ span {hζ.toInteger - 1} := by
  convert! absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm
/-
**IsCyclotomicExtension.Rat.span_zeta_sub_one_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `
IsCyclotomicExtension.Rat`。
形式化陈述：span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one`：p_mem_span_zeta_sub_o
ne : (p : 𝓞 K) in span {hζ.toInteger - 1}
· 使用引理 `NeZero.natCast_ne`：natCast_ne (n : Nat) (R) [AddMonoidWithOne R] [h : Ne
Zero (n : R)] : (n : R) != 0
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
-/
theorem span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩
/-
**IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one** 是 Mathlib 中的一个实例，位于命名空间
 `IsCyclotomicExtension.Rat`。
形式化陈述：liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `algebraMap_int_eq`：algebraMap_int_eq : algebraMap Int R = Int.castRingHo
m R
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one`：p_mem_span_zeta_sub_o
ne : (p : 𝓞 K) in span {hζ.toInteger - 1}
-/
instance liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑 := by
  rw [liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ
/-
**IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one** 是 Mathlib 中的一个定理，位于命名
空间 `IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDeg_span_zeta_sub_one : inertiaDeg (span {hζ.toInteger - 1}) Int = 
1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Ideal.IsMaximal.of_liesOver_isMaximal`：∀ {A : Type u_1} [inst : CommRing
 A] {B : Type u_2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsInt
egral A B] (P : Ideal B) (p…
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralInt`：∀ {K : Type u_1} [inst : F
ield K], Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_right_inj`：∀ {a m n : ℕ}, 1 < a → (a ^ m = a ^ n ↔ m = n)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.pow_inertiaDeg`：pow_inertiaDeg [IsDedekindDomain R] [Module.Free I
nt R] [Module.Finite Int R] (p : Nat) (P : Ideal R) [P.IsPrime] [P.LiesOver (spa
n {(p : In…
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one`：absNorm_span_zeta_s
ub_one : absNorm (span {hζ.toInteger - 1}) = p
-/
theorem inertiaDeg_span_zeta_sub_one : inertiaDeg (span {hζ.toInteger - 1}) ℤ = 1 := by
  have : IsMaximal (span {hζ.toInteger - 1}) := .of_liesOver_isMaximal _ 𝒑
  rw [← Nat.pow_right_inj hp.out.one_lt, pow_one, pow_inertiaDeg,
    absNorm_span_zeta_sub_one]

attribute [local instance] FractionRing.liftAlgebra in
/-
**IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow** 是 Mathlib 中的一个定理，位于命名
空间 `IsCyclotomicExtension.Rat`。
形式化陈述：map_eq_span_zeta_sub_one_pow : (map (algebraMap Int (𝓞 K)) 𝒑) = span {hζ.t
oInteger - 1} ^ Module.finrank Rat K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `IsGalois.of_equiv_equiv`：IsGalois.of_equiv_equiv {M N : Type*} [Field N]
 [Field M] [Algebra M N] [h : IsGalois F E] {f : F ≃+* M} {g : E ≃+* N} (hcomp :
 (algebraMap …
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.algEquiv_commutes`：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f
 : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `Associated.map`：map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [Fun
Like F M N] [MonoidHomClass F M N] (f : F) {x y : M} (ha : Associated x y) : Ass
ocia…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `IsCyclotomicExtension.Rat.associated_norm_zeta_sub_one`：associated_norm_
zeta_sub_one : Associated (Algebra.norm Int (hζ.toInteger - 1)) (p : Int)
（共 56 条，此处仅展示前 30 条）
-/
theorem map_eq_span_zeta_sub_one_pow :
    (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : IsGalois (FractionRing ℤ) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv ℤ ℚ).toRingEquiv.symm)
      (g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm) <|
        RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes (FractionRing.algEquiv ℤ ℚ).symm
          (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [map_span, Set.image_singleton, span_singleton_eq_span_singleton.mpr
    ((associated_norm_zeta_sub_one p k hζ).symm.map (algebraMap ℤ (𝓞 K))),
    ← Algebra.intNorm_eq_norm, Algebra.algebraMap_intNorm_of_isGalois, ← prod_span_singleton]
  conv_lhs =>
    enter [2, σ]
    rw [span_singleton_eq_span_singleton.mpr
      (hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one σ).symm]
  rw [Finset.prod_const, Finset.card_univ, ← Fintype.card_congr (galRestrict ℤ ℚ K (𝓞 K)).toEquiv,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
/-
**IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one** 是 Mathlib 中的一个定理
，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdx_span_zeta_sub_one : ramificationIdx (span {hζ.toInteger - 
1}) Int = p ^ k * (p - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.totient_prime_pow_succ`：totient_prime_pow_succ {p : Nat} (hp : p.Pri
me) (n : Nat) : φ (p ^ (n + 1)) = p ^ n * (p - 1)
· 使用定理 `IsCyclotomicExtension.Rat.finrank`：finrank [NeZero k] [IsCyclotomicExten
sion {k} Rat K] : Module.finrank Rat K = k.totient
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`：ramificationIdx_
eq_multiplicity [IsDedekindDomain S] [q.IsPrime] [q.LiesOver p] (hp : p.map (alg
ebraMap R S) != ⊥) : q.ramificationIdx R = m…
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow`：map_eq_span_zeta
_sub_one_pow : (map (algebraMap Int (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module
.finrank Rat K
· 使用定理 `multiplicity_pow_self`：multiplicity_pow_self {p : α} (h0 : p != 0) (hu :
 ¬IsUnit p) (n : Nat) : multiplicity p (p ^ n) = n
· 使用定理 `IsCyclotomicExtension.Rat.span_zeta_sub_one_ne_bot`：span_zeta_sub_one_ne
_bot : span {hζ.toInteger - 1} != ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem ramificationIdx_span_zeta_sub_one :
    ramificationIdx (span {hζ.toInteger - 1}) ℤ = p ^ k * (p - 1) := by
  have h := isPrime_span_zeta_sub_one p k hζ
  have hp0 : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  rw [← Nat.totient_prime_pow_succ hp.out, ← finrank _ K,
    IsDedekindDomain.ramificationIdx_eq_multiplicity 𝒑, map_eq_span_zeta_sub_one_pow p k hζ,
    multiplicity_pow_self (span_zeta_sub_one_ne_bot p k hζ) (isUnit_iff.not.mpr h.ne_top)]
  exact map_ne_bot_of_ne_bot hp0

variable (K)

include hK in
/-
**IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow** 是 Mathlib 中的一个定理，位于命
名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ncard_primesOver_of_prime_pow : (primesOver 𝒑 (𝓞 K)).ncard = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`：ncard_pri
mesOver_mul_ramificationIdxIn_mul_inertiaDegIn : (primesOver p B).ncard * (ramif
icationIdxIn p B * inertiaDegIn p B) = Nat.card G
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_eq_right`：∀ {b a : ℕ}, b ≠ 0 → (a * b = b ↔ a = 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
（共 46 条，此处仅展示前 30 条）
-/
theorem ncard_primesOver_of_prime_pow :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/ℚ)
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) Gal(K/ℚ),
    inertiaDegIn_eq_inertiaDeg 𝒑 (span {hζ.toInteger - 1}) Gal(K/ℚ),
    inertiaDeg_span_zeta_sub_one,
    ramificationIdx_span_zeta_sub_one, mul_one, ← Nat.totient_prime_pow_succ hp.out,
    ← finrank _ K, IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, Nat.mul_eq_right] at h_main
  exact Module.finrank_pos.ne'
/-
**IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver** 是 Mathlib 中的一个定理，
位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：eq_span_zeta_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ 
: P.LiesOver 𝒑] : P = span {hζ.toInteger - 1}
参数：P : Ideal (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`：ncard_primesOve
r_of_prime_pow : (primesOver 𝒑 (𝓞 K)).ncard = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_span_zeta_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  have : P ∈ primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} ∈ primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in
/-
**IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow** 是 Mathlib 中的一个定理，位于命名空间
 `IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDeg_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.Li
esOver 𝒑] : inertiaDeg P Int = 1
参数：P : Ideal (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver`：eq_span_zeta
_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] : 
P = span {hζ.toInteger - 1}
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one`：inertiaDeg_span_
zeta_sub_one : inertiaDeg (span {hζ.toInteger - 1}) Int = 1
-/
theorem inertiaDeg_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg P ℤ = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one]

include hK in
/-
**IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow** 是 Mathlib 中的一个定理，位
于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdx_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ :
 P.LiesOver 𝒑] : ramificationIdx P Int = p ^ k * (p - 1)
参数：P : Ideal (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver`：eq_span_zeta
_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] : 
P = span {hζ.toInteger - 1}
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one`：ramificatio
nIdx_span_zeta_sub_one : ramificationIdx (span {hζ.toInteger - 1}) Int = p ^ k *
 (p - 1)
-/
theorem ramificationIdx_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx P ℤ = p ^ k * (p - 1) := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one]

include hK in
/-
**IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow** 是 Mathlib 中的一个定理，位于命名
空间 `IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDegIn_eq_of_prime_pow : 𝒑.inertiaDegIn (𝓞 K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one`：inertiaDeg_span_
zeta_sub_one : inertiaDeg (span {hζ.toInteger - 1}) Int = 1
-/
theorem inertiaDegIn_eq_of_prime_pow :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/ℚ),
    inertiaDeg_span_zeta_sub_one]

include hK in
/-
**IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow** 是 Mathlib 中的一个定理
，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdxIn_eq_of_prime_pow : 𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p
 - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one`：ramificatio
nIdx_span_zeta_sub_one : ramificationIdx (span {hζ.toInteger - 1}) Int = p ^ k *
 (p - 1)
-/
theorem ramificationIdxIn_eq_of_prime_pow :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/ℚ),
    ramificationIdx_span_zeta_sub_one]

end PrimePow

section Prime

variable {K} [hK : IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-
**IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one'** 是 Mathlib 中的一个实例，位于命名空间
 `IsCyclotomicExtension.Rat`。
形式化陈述：isPrime_span_zeta_sub_one' : IsPrime (span {hζ.toInteger - 1})
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
instance isPrime_span_zeta_sub_one' : IsPrime (span {hζ.toInteger - 1}) := by
  rw [← pow_one p] at hK hζ
  exact isPrime_span_zeta_sub_one p 0 hζ

/-- If `2 < p`, then `2` is not in the ideal `(ζ - 1)`, where `ζ` is a primitive `p`-th root of
unity. -/
/-
**IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one'** 是 Mathlib 中的一个定理，位于
命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：two_not_mem_span_zeta_sub_one' (h : 2 < p) : (2 : 𝓞 K) ∉ span {hζ.toIntege
r - 1}
参数：h : 2 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用引理 `IsPrimitiveRoot.toInteger_sub_one_not_dvd_two`：toInteger_sub_one_not_dvd
_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k
 + 1))) (hodd : p != 2) : ¬ hζ.toIn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
If `2 < p`, then `2` is not in the ideal `(ζ - 1)`, where `ζ` is a primitive `p`
-th root of
unity.
-/
theorem two_not_mem_span_zeta_sub_one' (h : 2 < p) : (2 : 𝓞 K) ∉ span {hζ.toInteger - 1} := by
  rw [mem_span_singleton]
  rw [← pow_one p] at hK hζ
  exact hζ.toInteger_sub_one_not_dvd_two h.ne'

omit hp hK [NumberField K] in
/-
**IsCyclotomicExtension.Rat.associated_sub_one_of_isPrimitiveRoot** 是 Mathlib 中的
一个引理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：associated_sub_one_of_isPrimitiveRoot [NeZero p] {η : K} (hη : IsPrimitive
Root η p) : Associated (hζ.toInteger - 1) (hη.toInteger - 1)
参数：hη : IsPrimitiveRoot η p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPrimitiveRoot.isPrimitiveRoot_iff`：isPrimitiveRoot_iff {k : Nat} [NeZe
ro k] {ζ ξ : R} (h : IsPrimitiveRoot ζ k) : IsPrimitiveRoot ξ k ↔ exists i < k, 
i.Coprime k ∧ ζ ^ i = ξ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.RingOfIntegers.ext`：∀ {K : Type u_1} [inst : Field K] {x y :
 NumberField.RingOfIntegers K}, ↑x = ↑y → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`：associated_su
b_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) : Ass
ociated (ζ - 1) (ζ ^ j - 1)
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
-/
lemma associated_sub_one_of_isPrimitiveRoot [NeZero p] {η : K} (hη : IsPrimitiveRoot η p) :
    Associated (hζ.toInteger - 1) (hη.toInteger - 1) := by
  obtain ⟨i, -, hi, hζη⟩ := hζ.isPrimitiveRoot_iff.mp hη
  rw [show hη.toInteger = hζ.toInteger ^ i from RingOfIntegers.ext hζη.symm]
  exact hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime hi

omit [NumberField K] hK in
open Polynomial in
/-- `(ζ - 1) ^ (p - 1)` is associated to `p`, where `ζ` is a primitive `p`-th root of unity and
`p` is prime. -/
/-
**IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime** 是 Mathlib 中的一个定理
，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：associated_zeta_sub_one_pow_prime : Associated ((hζ.toInteger - 1) ^ (p - 
1)) (p : 𝓞 K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_one_cyclotomic_prime`：eval_one_cyclotomic_prime {R : Typ
e*} [CommRing R] {p : Nat} [hn : Fact p.Prime] : eval 1 (cyclotomic p R) = p
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`：cyclotomic_eq_prod_X
_sub_primitiveRoots {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : Nat} (hz 
: IsPrimitiveRoot ζ n) : cyclotomic n K …
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsPrimitiveRoot.card_primitiveRoots`：card_primitiveRoots {ζ : R} {k : Na
t} (h : IsPrimitiveRoot ζ k) : #(primitiveRoots k R) = φ k
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Associated.prod`：Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} 
(s : Finset ι) (f : ι -> M) (g : ι -> M) (h : forall i, i in s -> (f i) ~ᵤ (g i)
) : (…
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `isPrimitiveRoot_of_mem_primitiveRoots`：isPrimitiveRoot_of_mem_primitiveR
oots {ζ : R} (h : ζ in primitiveRoots k R) : IsPrimitiveRoot ζ k
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `Associated.neg_right`：neg_right (h : Associated a b) : Associated a (-b)
· 使用引理 `IsCyclotomicExtension.Rat.associated_sub_one_of_isPrimitiveRoot`：associa
ted_sub_one_of_isPrimitiveRoot [NeZero p] {η : K} (hη : IsPrimitiveRoot η p) : A
ssociated (hζ.toInteger - 1) (hη.toInteger - 1)

--- 原说明 ---
`(ζ - 1) ^ (p - 1)` is associated to `p`, where `ζ` is a primitive `p`-th root o
f unity and
`p` is prime.
-/
theorem associated_zeta_sub_one_pow_prime :
    Associated ((hζ.toInteger - 1) ^ (p - 1)) (p : 𝓞 K) := by
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p),
    cyclotomic_eq_prod_X_sub_primitiveRoots hζ.toInteger_isPrimitiveRoot, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out, ← hζ.toInteger_isPrimitiveRoot.card_primitiveRoots,
    ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  have hη' : IsPrimitiveRoot (η : K) p :=
    (isPrimitiveRoot_of_mem_primitiveRoots hη).map_of_injective RingOfIntegers.coe_injective
  simpa using (associated_sub_one_of_isPrimitiveRoot p hζ hη').neg_right

/-- If `ζ - 1` does not divide `x`, then `p` and `x` are coprime, where `ζ` is a primitive `p`-th
root of unity and `p` is prime. -/
/-
**IsCyclotomicExtension.Rat.isCoprime_of_not_zeta_sub_one_dvd** 是 Mathlib 中的一个定理
，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：isCoprime_of_not_zeta_sub_one_dvd {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x) 
: IsCoprime (p : 𝓞 K) x
参数：hx : ¬ hζ.toInteger - 1 ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.isCoprime_span_singleton_iff`：isCoprime_span_singleton_iff (x y : 
R) : IsCoprime (span <| singleton x) (span <| singleton y) ↔ IsCoprime x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime`：associated_
zeta_sub_one_pow_prime : Associated ((hζ.toInteger - 1) ^ (p - 1)) (p : 𝓞 K)
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsCoprime.pow_left_iff`：IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime 
(x ^ m) y ↔ IsCoprime x y
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.isCoprime_iff_gcd`：isCoprime_iff_gcd {I J : Ideal A} : IsCoprime I
 J ↔ gcd I J = 1
· 使用定理 `Irreducible.gcd_eq_one_iff`：Irreducible.gcd_eq_one_iff [NormalizedGCDMon
oid α] {x y : α} (hx : Irreducible x) : gcd x y = 1 ↔ ¬(x ∣ y)
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Ideal.prime_span_singleton_iff`：prime_span_singleton_iff {a : A} : Prime
 (span {a}) ↔ Prime a
· 使用定理 `IsPrimitiveRoot.zeta_sub_one_prime'`：zeta_sub_one_prime' [h : IsCyclotom
icExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p) : Prime ((hζ.toInteger - 1))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_span_singleton`：dvd_span_singleton {I : Ideal A} {x : A} : I ∣
 span {x} ↔ x in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x

--- 原说明 ---
If `ζ - 1` does not divide `x`, then `p` and `x` are coprime, where `ζ` is a pri
mitive `p`-th
root of unity and `p` is prime.
-/
theorem isCoprime_of_not_zeta_sub_one_dvd {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x) :
    IsCoprime (p : 𝓞 K) x := by
  rwa [← isCoprime_span_singleton_iff,  ← span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_pow_prime p hζ), ← span_singleton_pow,
    IsCoprime.pow_left_iff (by grind [hp.out.one_lt]), isCoprime_iff_gcd,
    (prime_span_singleton_iff.mpr
    hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff, dvd_span_singleton, mem_span_singleton]
/-
**IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one'** 是 Mathlib 中的一个定理，位于命
名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDeg_span_zeta_sub_one' : inertiaDeg (span {hζ.toInteger - 1}) Int =
 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one`：inertiaDeg_span_
zeta_sub_one : inertiaDeg (span {hζ.toInteger - 1}) Int = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem inertiaDeg_span_zeta_sub_one' : inertiaDeg (span {hζ.toInteger - 1}) ℤ = 1 := by
  rw [← pow_one p] at hK hζ
  exact inertiaDeg_span_zeta_sub_one p 0 hζ
/-
**IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one'** 是 Mathlib 中的一个定
理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdx_span_zeta_sub_one' : ramificationIdx (span {hζ.toInteger -
 1}) Int = p - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one`：ramificatio
nIdx_span_zeta_sub_one : ramificationIdx (span {hζ.toInteger - 1}) Int = p ^ k *
 (p - 1)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem ramificationIdx_span_zeta_sub_one' :
    ramificationIdx (span {hζ.toInteger - 1}) ℤ = p - 1 := by
  rw [← pow_one p] at hK hζ
  rw [ramificationIdx_span_zeta_sub_one p 0 hζ, pow_zero, one_mul]

/-- An integer `n` is divisible by `ζ - 1` in `𝓞 K` if and only if it is divisible by `p`,
where `ζ` is a primitive `p`-th root of unity. -/
/-
**IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'** 是 Mathlib 中的一个定理，位于命
名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：zeta_sub_one_dvd_intCast_iff' {n : Int} : hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (
p : Int) ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff`：zeta_sub_one_dvd
_intCast_iff {n : Int} : hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (p : Int) ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
An integer `n` is divisible by `ζ - 1` in `𝓞 K` if and only if it is divisible b
y `p`,
where `ζ` is a primitive `p`-th root of unity.
-/
theorem zeta_sub_one_dvd_intCast_iff' {n : ℤ} :
    hζ.toInteger - 1 ∣ (n : 𝓞 K) ↔ (p : ℤ) ∣ n := by
  rw [← pow_one p] at hK hζ
  exact zeta_sub_one_dvd_intCast_iff p 0 hζ

variable (K)

include hK in
/-
**IsCyclotomicExtension.Rat.ncard_primesOver_of_prime** 是 Mathlib 中的一个定理，位于命名空间 
`IsCyclotomicExtension.Rat`。
形式化陈述：ncard_primesOver_of_prime : (primesOver 𝒑 (𝓞 K)).ncard = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`：ncard_primesOve
r_of_prime_pow : (primesOver 𝒑 (𝓞 K)).ncard = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem ncard_primesOver_of_prime :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  rw [← pow_one p] at hK
  exact ncard_primesOver_of_prime_pow p 0 K
/-
**IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'** 是 Mathlib 中的一个定理
，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：eq_span_zeta_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂
 : P.LiesOver 𝒑] : P = span {hζ.toInteger - 1}
参数：P : Ideal (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver`：eq_span_zeta
_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] : 
P = span {hζ.toInteger - 1}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem eq_span_zeta_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P

include hK in
/-
**IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Is
CyclotomicExtension.Rat`。
形式化陈述：inertiaDeg_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOv
er 𝒑] : inertiaDeg P Int = 1
参数：P : Ideal (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'`：eq_span_zet
a_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] 
: P = span {hζ.toInteger - 1}
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one'`：inertiaDeg_span
_zeta_sub_one' : inertiaDeg (span {hζ.toInteger - 1}) Int = 1
-/
theorem inertiaDeg_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg P ℤ = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one']

include hK in
/-
**IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime** 是 Mathlib 中的一个定理，位于命名空
间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdx_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.L
iesOver 𝒑] : ramificationIdx P Int = p - 1
参数：P : Ideal (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'`：eq_span_zet
a_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] 
: P = span {hζ.toInteger - 1}
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one'`：ramificati
onIdx_span_zeta_sub_one' : ramificationIdx (span {hζ.toInteger - 1}) Int = p - 1
-/
theorem ramificationIdx_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx P ℤ = p - 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one']

include hK in
/-
**IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `
IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDegIn_eq_of_prime : 𝒑.inertiaDegIn (𝓞 K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow`：inertiaDegIn_eq_
of_prime_pow : 𝒑.inertiaDegIn (𝓞 K) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem inertiaDegIn_eq_of_prime :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  rw [← pow_one p] at hK
  exact inertiaDegIn_eq_of_prime_pow p 0 K

include hK in
/-
**IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime** 是 Mathlib 中的一个定理，位于命
名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdxIn_eq_of_prime : 𝒑.ramificationIdxIn (𝓞 K) = p - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`：ramificatio
nIdxIn_eq_of_prime_pow : 𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem ramificationIdxIn_eq_of_prime :
    𝒑.ramificationIdxIn (𝓞 K) = p - 1 := by
  rw [← pow_one p] at hK
  rw [ramificationIdxIn_eq_of_prime_pow p 0, pow_zero, one_mul]

end Prime

section notDvd

open NumberField.Ideal Polynomial

variable {m} [NeZero m] [hK : IsCyclotomicExtension {m} ℚ K]

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `
IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDeg_eq_of_not_dvd (hm : ¬ p ∣ m) : inertiaDeg P Int = orderOf (p : 
ZMod m)
参数：hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingOfIntegers.exponent_eq_one_iff`：exponent_eq_one_iff : exponent θ = 1
 ↔ Algebra.adjoin Int {θ} = ⊤
· 使用定理 `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top`：adjoin_singleton_eq_t
op [hK : IsCyclotomicExtension {n} Rat K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) : I
nt[hζ.toInteger] = ⊤
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_app
ly'`：inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ expon
ent θ) {Q : (ZMod p)[X]} (hQ : Q in monicFactorsMod θ p) : inerti…
· 使用定理 `Ideal.IsMaximal.of_liesOver_isMaximal`：∀ {A : Type u_1} [inst : CommRing
 A] {B : Type u_2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsInt
egral A B] (P : Ideal B) (p…
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralInt`：∀ {K : Type u_1} [inst : F
ield K], Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`：natDegree_of_dvd_
cyclotomic_of_irreducible (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) : P.
natDegree = orderOf (unitOfCoprime _ (hn.po…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
（共 52 条，此处仅展示前 30 条）
-/
theorem inertiaDeg_eq_of_not_dvd (hm : ¬ p ∣ m) :
    inertiaDeg P ℤ = orderOf (p : ZMod m) := by
  replace hm : p.Coprime m := hp.out.coprime_iff_not_dvd.mpr hm
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  have : P.IsMaximal := .of_liesOver_isMaximal P 𝒑
  rw [h₃, natDegree_of_dvd_cyclotomic_of_irreducible (by simp) hm (f := 1) _ h₂.1]
  · simpa using (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
  · refine dvd_trans h₂.2.2 ?_
    rw [← map_cyclotomic_int, cyclotomic_eq_minpoly (zeta_spec m ℚ K) (NeZero.pos _),
      ← (zeta_spec m ℚ K).coe_toInteger, ← RingOfIntegers.minpoly_coe ζ]
    simp [ζ]
/-
**IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd** 是 Mathlib 中的一个定理，位于命
名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdx_eq_of_not_dvd (hm : ¬ p ∣ m) : ramificationIdx P Int = 1
参数：hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingOfIntegers.exponent_eq_one_iff`：exponent_eq_one_iff : exponent θ = 1
 ↔ Algebra.adjoin Int {θ} = ⊤
· 使用定理 `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top`：adjoin_singleton_eq_t
op [hK : IsCyclotomicExtension {n} Rat K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) : I
nt[hζ.toInteger] = ⊤
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_sym
m_apply'`：ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬
 p ∣ exponent θ) {Q : (ZMod p)[X]} (hQ : Q in monicFactorsMod θ p) : r…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.emultiplicity_le_one_of_separable`：emultiplicity_le_one_of_se
parable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) : emultiplicity q p <
= 1
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.isUnit_iff_degree_eq_zero`：isUnit_iff_degree_eq_zero : IsUnit
 p ↔ degree p = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Irreducible.degree_pos`：degree_pos (h : Irreducible f) : 0 < f.degree
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
（共 46 条，此处仅展示前 30 条）
-/
theorem ramificationIdx_eq_of_not_dvd (hm : ¬ p ∣ m) :
    ramificationIdx P ℤ = 1 := by
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [h₃]
  refine multiplicity_eq_of_emultiplicity_eq_some (le_antisymm ?_ ?_)
  · apply emultiplicity_le_one_of_separable
    · exact isUnit_iff_degree_eq_zero.not.mpr (Irreducible.degree_pos h₂.1).ne'
    · exact (zeta_spec m ℚ K).toInteger_isPrimitiveRoot.separable_minpoly_mod hm
  · rw [ENat.natCast_one]
    exact Order.one_le_iff_pos.mpr <| emultiplicity_pos_of_dvd h₂.2.2
/-
**IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间
 `IsCyclotomicExtension.Rat`。
形式化陈述：inertiaDegIn_eq_of_not_dvd (hm : ¬ p ∣ m) : 𝒑.inertiaDegIn (𝓞 K) = orderOf
 (p : ZMod m)
参数：hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralInt`：∀ {K : Type u_1} [inst : F
ield K], Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`：inertiaDeg_eq_of_not
_dvd (hm : ¬ p ∣ m) : inertiaDeg P Int = orderOf (p : ZMod m)
-/
theorem inertiaDegIn_eq_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) := by
  have : IsGalois ℚ K := isGalois {m} ℚ K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/ℚ), inertiaDeg_eq_of_not_dvd p K P hm]
/-
**IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd** 是 Mathlib 中的一个定理，位
于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：ramificationIdxIn_eq_of_not_dvd (hm : ¬ p ∣ m) : 𝒑.ramificationIdxIn (𝓞 K)
 = 1
参数：hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralInt`：∀ {K : Type u_1} [inst : F
ield K], Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`：ramificationIdx
_eq_of_not_dvd (hm : ¬ p ∣ m) : ramificationIdx P Int = 1
-/
theorem ramificationIdxIn_eq_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = 1 := by
  have : IsGalois ℚ K := isGalois {m} ℚ K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/ℚ), ramificationIdx_eq_of_not_dvd p K P hm]

end notDvd

section general

variable {m p k} [IsCyclotomicExtension {n} ℚ K]

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
/-
**IsCyclotomicExtension.Rat.inertiaDegIn_ramificationIdxIn_aux** 是 Mathlib 中的一个定
理，位于命名空间 `IsCyclotomicExtension.Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inertiaDegIn_ramificationIdxIn_aux (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) ∧
      𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {n} ℚ K
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  have : NeZero n := ⟨hn ▸ NeZero.ne (p ^ (k + 1) * m)⟩
  let ζ := zeta n ℚ K
  have hζ := zeta_spec n ℚ K
  -- We construct `ℚ⟮ζₘ⟯ ⊆ ℚ⟮ζₙ⟯`
  let ζₘ := ζ ^ (p ^ (k + 1))
  have hζₘ := hζ.pow (NeZero.pos _) hn
  let Fₘ := ℚ⟮ζₘ⟯
  have : IsCyclotomicExtension {m} ℚ Fₘ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₘ).mpr rfl
  -- A prime ideal of `Fₘ` above `𝒑`
  obtain ⟨Pₘ, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral 𝒑 (S := 𝓞 Fₘ)
  -- We construct `ℚ⟮ζ_p^{k+1}⟯ ⊆ ℚ⟮ζₘ⟯`
  let ζₚ := ζ ^ m
  have hζₚ := hζ.pow (NeZero.pos _) (mul_comm _ m ▸ hn)
  let Fₚ := ℚ⟮ζₚ⟯
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ Fₚ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₚ).mpr rfl
  -- A prime ideal of `Fₚ` above `𝒑`
  obtain ⟨Pₚ, hP₁, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral 𝒑 (S := 𝓞 Fₚ)
  suffices Pₚ.ramificationIdxIn (𝓞 K) *
      Pₘ.inertiaDegIn (𝓞 K) * (Pₘ.primesOver (𝓞 K)).ncard = 1 by
    replace this := Nat.eq_one_of_mul_eq_one_right this
    rw [← inertiaDegIn_mul_inertiaDegIn 𝒑 Pₘ Gal(Fₘ/ℚ) _ Gal(K/ℚ) Gal(K/Fₘ),
      ← ramificationIdxIn_mul_ramificationIdxIn Pₚ Gal(Fₚ/ℚ) _ Gal(K/ℚ) Gal(K/Fₚ),
      Nat.eq_one_of_mul_eq_one_left this, Nat.eq_one_of_mul_eq_one_right this, mul_one, mul_one,
      inertiaDegIn_eq_of_not_dvd p _ hm, ramificationIdxIn_eq_of_prime_pow p k Fₚ]
    exact ⟨rfl, rfl⟩
  have h_main : Module.finrank ℚ Fₘ * Module.finrank ℚ Fₚ = Module.finrank ℚ K := by
    rw [finrank m, finrank (p ^ (k + 1)), finrank n, hn, mul_comm, Nat.totient_mul]
    exact Nat.Coprime.pow_left (k + 1) (by rwa [hp.out.coprime_iff_not_dvd])
  rwa [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank,
    ← IsGalois.card_aut_eq_finrank,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 Fₘ) Gal(Fₘ/ℚ),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 Fₚ) Gal(Fₚ/ℚ),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/ℚ),
    ← ncard_primesOver_mul_ncard_primesOver Pₘ Gal(Fₘ/ℚ) (𝓞 K) Gal(K/ℚ),
    ramificationIdxIn_eq_of_not_dvd p Fₘ hm, inertiaDegIn_eq_of_prime_pow p k Fₚ,
    ncard_primesOver_of_prime_pow p k Fₚ, one_mul, one_mul, mul_one, mul_assoc, mul_assoc,
    mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero 𝒑 _), ← mul_assoc,
    ← mul_rotate (𝒑.inertiaDegIn (𝓞 K)),
    ← inertiaDegIn_mul_inertiaDegIn 𝒑 Pₘ Gal(Fₘ/ℚ) (𝓞 K) Gal(K/ℚ) Gal(K/Fₘ), mul_assoc, mul_assoc,
    mul_right_inj' (inertiaDegIn_ne_zero Gal(Fₘ/ℚ)), ← mul_rotate',
    ← ramificationIdxIn_mul_ramificationIdxIn (p := 𝒑) Pₚ Gal(Fₚ/ℚ) (𝓞 K) Gal(K/ℚ) Gal(K/Fₚ),
    eq_comm, mul_assoc, mul_eq_left₀ (ramificationIdxIn_ne_zero Gal(Fₚ/ℚ)), ← mul_assoc]
    at h_main

/--
Write `n = p ^ (k + 1) * m` where the prime `p` does not divide `m`, then the inertia degree of
`p` in `ℚ(ζₙ)` is the order of `p` modulo `m`.
-/
/-
**IsCyclotomicExtension.Rat.inertiaDegIn_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCycloto
micExtension.Rat`。
形式化陈述：inertiaDegIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) : 𝒑.inertiaDegIn
 (𝓞 K) = orderOf (p : ZMod m)
参数：hn : n = p ^ (k + 1) * m；hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal.0.IsCyclotomi
cExtension.Rat.inertiaDegIn_ramificationIdxIn_aux`：∀ (n : ℕ) {m p k : ℕ} [hp : F
act (Nat.Prime p)] (K : Type u_1) [inst : Field K] [inst_1 : NumberField K]   [I
sCyclotomicExtension {n} ℚ K], …

--- 原说明 ---
Write `n = p ^ (k + 1) * m` where the prime `p` does not divide `m`, then the in
ertia degree of
`p` in `ℚ(ζₙ)` is the order of `p` modulo `m`.
-/
theorem inertiaDegIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) :=
  (inertiaDegIn_ramificationIdxIn_aux n K hn hm).1

/--
Write `n = p ^ (k + 1) * m` where the prime `p` does not divide `m`, then the ramification index
of `p` in `ℚ(ζₙ)` is `p ^ k * (p - 1)`.
-/
/-
**IsCyclotomicExtension.Rat.ramificationIdxIn_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCy
clotomicExtension.Rat`。
形式化陈述：ramificationIdxIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) : 𝒑.ramific
ationIdxIn (𝓞 K) = p ^ k * (p - 1)
参数：hn : n = p ^ (k + 1) * m；hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal.0.IsCyclotomi
cExtension.Rat.inertiaDegIn_ramificationIdxIn_aux`：∀ (n : ℕ) {m p k : ℕ} [hp : F
act (Nat.Prime p)] (K : Type u_1) [inst : Field K] [inst_1 : NumberField K]   [I
sCyclotomicExtension {n} ℚ K], …

--- 原说明 ---
Write `n = p ^ (k + 1) * m` where the prime `p` does not divide `m`, then the ra
mification index
of `p` in `ℚ(ζₙ)` is `p ^ k * (p - 1)`.
-/
theorem ramificationIdxIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) :=
  (inertiaDegIn_ramificationIdxIn_aux n K hn hm).2
/-
**IsCyclotomicExtension.Rat.inertiaDeg_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomi
cExtension.Rat`。
形式化陈述：inertiaDeg_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) : inertiaDeg P Int
 = orderOf (p : ZMod m)
参数：hn : n = p ^ (k + 1) * m；hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `IsCyclotomicExtension.Rat.inertiaDegIn_eq`：inertiaDegIn_eq (hn : n = p ^
 (k + 1) * m) (hm : ¬ p ∣ m) : 𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m)
-/
theorem inertiaDeg_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    inertiaDeg P ℤ = orderOf (p : ZMod m) := by
  have : IsGalois ℚ K := isGalois {n} ℚ K
  rw [← inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/ℚ), inertiaDegIn_eq n K hn hm]
/-
**IsCyclotomicExtension.Rat.ramificationIdx_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCycl
otomicExtension.Rat`。
形式化陈述：ramificationIdx_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) : ramificatio
nIdx P Int = p ^ k * (p - 1)
参数：hn : n = p ^ (k + 1) * m；hm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.isGalois`：isGalois [IsCyclotomicExtension S K L] :
 IsGalois K L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsGaloisGroupIntRingOfIntegersOfRat`：∀ (L : Type u_1) [inst : Field 
L] [inst_1 : NumberField L] (G : Type u_2) [inst_2 : Group G]   [inst_3 : MulSem
iringAction G L] [IsGaloisGro…
· 使用定理 `IsCyclotomicExtension.Rat.ramificationIdxIn_eq`：ramificationIdxIn_eq (hn
 : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) : 𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p 
- 1)
-/
theorem ramificationIdx_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    ramificationIdx P ℤ = p ^ k * (p - 1) := by
  have : IsGalois ℚ K := isGalois {n} ℚ K
  rw [← ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/ℚ), ramificationIdxIn_eq n K hn hm]

end general

end IsCyclotomicExtension.Rat

