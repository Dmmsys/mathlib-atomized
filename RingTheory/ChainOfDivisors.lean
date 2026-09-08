/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Order.Atoms
public import Mathlib.Order.Hom.Bounded
/-!

# Chains of divisors

The results in this file show that in the monoid `Associates M` of a `UniqueFactorizationMonoid`
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, meaning that we can find a strictly increasing bijection between `Fin (n + 1)`
and the set of factors of `a`.

## Main results
- `DivisorChain.exists_chain_of_prime_pow` : existence of a chain for prime powers.
- `DivisorChain.is_prime_pow_of_has_chain` : elements that have a chain are prime powers.
- `multiplicity_prime_eq_multiplicity_image_by_factor_orderIso` : if there is a
  monotone bijection `d` between the set of factors of `a : Associates M` and the set of factors of
  `b : Associates N` then for any prime `p ∣ a`, `multiplicity p a = multiplicity (d p) b`.
- `multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalizedFactors` : if there is a bijection
  between the set of factors of `a : M` and `b : N` then for any prime `p ∣ a`,
  `multiplicity p a = multiplicity (d p) b`


## TODO
- Create a structure for chains of divisors.
- Simplify proof of `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors` using
  `mem_normalizedFactors_factor_order_iso_of_mem_normalizedFactors` or vice versa.

-/

@[expose] public section

assert_not_exists Field

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

/-
**Associates.isAtom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Associates.isAtom_iff {p : Associates M} (h₁ : p != 0) : IsAtom p ↔ Irredu
cible p
参数：h₁ : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.isUnit_iff_eq_one`：isUnit_iff_eq_one (a : Associates M) : IsU
nit a ↔ a = 1
· 使用定理 `isUnit_of_associated_mul`：isUnit_of_associated_mul [CommMonoidWithZero M
] [IsCancelMulZero M] {p b : M} (h : Associated (p * b) p) (hp : p != 0) : IsUni
t b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.bot_eq_one`：bot_eq_one [Monoid M] : (⊥ : Associates M) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Associates.isAtom_iff {p : Associates M} (h₁ : p ≠ 0) : IsAtom p ↔ Irreducible p :=
  ⟨fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one] using! hp.1, fun a b h =>
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.isUnit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            apply isUnit_of_associated_mul (show Associated (p * b) p by conv_rhs => rw [h]) h₁)⟩,
    fun hp =>
    ⟨by simpa only [Associates.isUnit_iff_eq_one, Associates.bot_eq_one] using! hp.1,
      fun b ⟨⟨a, hab⟩, hb⟩ =>
      (hp.isUnit_or_isUnit hab).casesOn
        (fun hb => show b = ⊥ by rwa [Associates.isUnit_iff_eq_one, ← Associates.bot_eq_one] at hb)
        fun ha =>
        absurd
          (show p ∣ b from
            ⟨(ha.unit⁻¹ : Units _), by rw [hab, mul_assoc, IsUnit.mul_val_inv ha, mul_one]⟩)
          hb⟩⟩

open UniqueFactorizationMonoid Irreducible Associates

namespace DivisorChain

/-
**DivisorChain.exists_chain_of_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `DivisorChain
`。
形式化陈述：exists_chain_of_prime_pow {p : Associates M} {n : Nat} (hn : n != 0) (hp :
 Prime p) : exists c : Fin (n + 1) -> Associates M, c 1 = p ∧ StrictMono c ∧ for
all {r : Associates M}, r <= p ^ n ↔ exists i, r = c i
参数：hn : n != 0；hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_ofNat_eq_mod`：coe_ofNat_eq_mod (m n : Nat) [NeZero m] : ((ofNat(
n) : Fin m) : Nat) = ofNat(n) % m
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associates.dvdNotUnit_iff_lt`：dvdNotUnit_iff_lt {a b : Associates M} : D
vdNotUnit a b ↔ a < b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Associates.instNoZeroDivisors`：∀ {M : Type u_1} [inst : CommMonoidWithZe
ro M] [IsCancelMulZero M], NoZeroDivisors (Associates M)
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `not_isUnit_of_not_isUnit_dvd`：not_isUnit_of_not_isUnit_dvd {a b : α} (ha
 : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用引理 `dvd_pow`：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ 
n | 0, hn => (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_rig…
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_mul_pow_sub`：pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n -
 m) = a ^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `dvd_prime_pow`：dvd_prime_pow [CommMonoidWithZero M] [IsCancelMulZero M] 
{p q : M} (hp : Prime p) (n : Nat) : q ∣ p ^ n ↔ exists i <= n, Associated q (p 
^ i…
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem exists_chain_of_prime_pow {p : Associates M} {n : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    ∃ c : Fin (n + 1) → Associates M,
      c 1 = p ∧ StrictMono c ∧ ∀ {r : Associates M}, r ≤ p ^ n ↔ ∃ i, r = c i := by
  refine ⟨fun i => p ^ (i : ℕ), ?_, fun n m h => ?_, @fun y => ⟨fun h => ?_, ?_⟩⟩
  · dsimp only
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt, pow_one]
    exact Nat.lt_succ_of_le (Nat.one_le_iff_ne_zero.mpr hn)
  · exact Associates.dvdNotUnit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_zero, p ^ (m - n : ℕ),
          not_isUnit_of_not_isUnit_dvd hp.not_isUnit (dvd_pow dvd_rfl (Nat.sub_pos_of_lt h).ne'),
          (pow_mul_pow_sub p h.le).symm⟩
  · obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h
    rw [associated_iff_eq] at hi
    exact ⟨⟨i, Nat.lt_succ_of_le i_le⟩, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ (n - i : ℕ), (pow_mul_pow_sub p (Nat.succ_le_succ_iff.mp i.2)).symm⟩
/-
**DivisorChain.element_of_chain_not_isUnit_of_index_ne_zero** 是 Mathlib 中的一个定理，位
于命名空间 `DivisorChain`。
形式化陈述：element_of_chain_not_isUnit_of_index_ne_zero {n : Nat} {i : Fin (n + 1)} (
i_pos : i != 0) {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) : ¬IsUnit 
(c i)
参数：n + 1；i_pos : i != 0；n + 1；h₁ : StrictMono c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DvdNotUnit.not_isUnit`：DvdNotUnit.not_isUnit [CommMonoidWithZero M] {p q
 : M} (hp : DvdNotUnit p q) : ¬IsUnit q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.dvdNotUnit_iff_lt`：dvdNotUnit_iff_lt {a b : Associates M} : D
vdNotUnit a b ↔ a < b
· 使用定理 `Fin.pos_iff_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, 0 < a ↔ a 
≠ 0
-/
theorem element_of_chain_not_isUnit_of_index_ne_zero {n : ℕ} {i : Fin (n + 1)} (i_pos : i ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) : ¬IsUnit (c i) :=
  DvdNotUnit.not_isUnit
    (Associates.dvdNotUnit_iff_lt.2
      (h₁ <| show (0 : Fin (n + 1)) < i from Fin.pos_iff_ne_zero.mpr i_pos))
/-
**DivisorChain.first_of_chain_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `DivisorChain`。
形式化陈述：first_of_chain_isUnit {q : Associates M} {n : Nat} {c : Fin (n + 1) -> Ass
ociates M} (h₁ : StrictMono c) (h₂ : forall {r}, r <= q ↔ exists i, r = c i) : I
sUnit (c 0)
参数：n + 1；h₁ : StrictMono c；h₂ : forall {r}, r <= q ↔ exists i, r = c i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `Associates.instIsBotOneClass`：∀ {M : Type u_1} [inst : CommMonoid M], Is
BotOneClass (Associates M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.isUnit_iff_eq_one`：isUnit_iff_eq_one (a : Associates M) : IsU
nit a ↔ a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.le_one_iff`：le_one_iff {p : Associates M} : p <= 1 ↔ p = 1
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
theorem first_of_chain_isUnit {q : Associates M} {n : ℕ} {c : Fin (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp one_le
  rw [Associates.isUnit_iff_eq_one, ← Associates.le_one_iff, hr]
  exact h₁.monotone (Fin.zero_le i)

/-- The second element of a chain is irreducible. -/
/-
**DivisorChain.second_of_chain_is_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Divisor
Chain`。
形式化陈述：second_of_chain_is_irreducible {q : Associates M} {n : Nat} (hn : n != 0) 
{c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r}, r <= q ↔
 exists i, r = c i) (hq : q != 0) : Irreducible (c 1)
参数：hn : n != 0；n + 1；h₁ : StrictMono c；h₂ : forall {r}, r <= q ↔ exists i, r = c
 i；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associates.isAtom_iff`：Associates.isAtom_iff {p : Associates M} (h₁ : p 
!= 0) : IsAtom p ↔ Irreducible p
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Associates.isUnit_iff_eq_one`：isUnit_iff_eq_one (a : Associates M) : IsU
nit a ↔ a = 1
· 使用定理 `DivisorChain.first_of_chain_isUnit`：first_of_chain_isUnit {q : Associate
s M} {n : Nat} {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : foral
l {r}, r <= q ↔ exists i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b

--- 原说明 ---
The second element of a chain is irreducible.
-/
theorem second_of_chain_is_irreducible {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
    (hq : q ≠ 0) : Irreducible (c 1) := by
  rcases n with - | n; · contradiction
  refine (Associates.isAtom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨?_, fun b hb => ?_⟩
  · exact ne_bot_of_gt (h₁ zero_lt_one)
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.isUnit_iff_eq_one _).mp (first_of_chain_isUnit h₁ @h₂)
  · simpa [Fin.lt_def] using h₁.lt_iff_lt.mp hb
/-
**DivisorChain.eq_second_of_chain_of_prime_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Diviso
rChain`。
形式化陈述：eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : Nat} (hn : n !
= 0) {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r : Ass
ociates M}, r <= q ↔ exists i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r
) : p = c 1
参数：hn : n != 0；n + 1；h₁ : StrictMono c；h₂ : forall {r : Associates M}, r <= q ↔ 
exists i, r = c i；hp : Prime p；hr : r ∣ q；hp' : p ∣ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_le_of_not_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 b ≤ a → ¬b < a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_iff_val_le_val`：le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : N
at) <= b
· 使用定理 `Fin.val_one`：∀ (n : ℕ), ↑1 = 1
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Fin.pos_iff_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, 0 < a ↔ a 
≠ 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `DivisorChain.first_of_chain_isUnit`：first_of_chain_isUnit {q : Associate
s M} {n : Nat} {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : foral
l {r}, r <= q ↔ exists i…
· 使用定理 `Fin.eq_zero_or_eq_succ`：∀ {n : ℕ} (i : Fin (n + 1)), i = 0 ∨ ∃ j, i = j.
succ
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_irreducible_of_not_isUnit_of_dvdNotUnit`：not_irreducible_of_not_isUn
it_of_dvdNotUnit [CommMonoidWithZero M] {p q : M} (hp : ¬IsUnit p) (h : DvdNotUn
it p q) : ¬Irreducible q
· 使用定理 `DvdNotUnit.not_isUnit`：DvdNotUnit.not_isUnit [CommMonoidWithZero M] {p q
 : M} (hp : DvdNotUnit p q) : ¬IsUnit q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.dvdNotUnit_iff_lt`：dvdNotUnit_iff_lt {a b : Associates M} : D
vdNotUnit a b ↔ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
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
（共 35 条，此处仅展示前 30 条）
-/
theorem eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r) :
    p = c 1 := by
  rcases n with - | n
  · contradiction
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine congr_arg c (eq_of_le_of_not_lt' ?_ fun hi => ?_)
  · rw [Fin.le_iff_val_le_val, Fin.val_one, Nat.succ_le_iff, ← Fin.val_zero (n.succ + 1), ←
      Fin.lt_def, Fin.pos_iff_ne_zero]
    rintro rfl
    exact hp.not_isUnit (first_of_chain_isUnit h₁ @h₂)
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · cases hi
  refine
    not_irreducible_of_not_isUnit_of_dvdNotUnit
      (DvdNotUnit.not_isUnit
        (Associates.dvdNotUnit_iff_lt.2 (h₁ (show (0 : Fin (n + 2)) < j.castSucc from ?_))))
      ?_ hp.irreducible
  · simpa using Fin.lt_def.mp hi
  · refine Associates.dvdNotUnit_iff_lt.2 (h₁ ?_)
    simpa only [Fin.coe_eq_castSucc] using Fin.castSucc_lt_succ

omit [IsCancelMulZero M]
/-
**DivisorChain.card_subset_divisors_le_length_of_chain** 是 Mathlib 中的一个定理，位于命名空间
 `DivisorChain`。
形式化陈述：card_subset_divisors_le_length_of_chain {q : Associates M} {n : Nat} {c : 
Fin (n + 1) -> Associates M} (h₂ : forall {r}, r <= q ↔ exists i, r = c i) {m : 
Finset (Associates M)} (hm : forall r, r in m -> r <= q) : m.card <= n + 1
参数：n + 1；h₂ : forall {r}, r <= q ↔ exists i, r = c i；Associates M；hm : forall r,
 r in m -> r <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : ℕ}
    {c : Fin (n + 1) → Associates M} (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) {m : Finset (Associates M)}
    (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 := by
  classical
    have mem_image : ∀ r : Associates M, r ≤ q → r ∈ Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_card fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le

variable [UniqueFactorizationMonoid M]
/-
**DivisorChain.element_of_chain_eq_pow_second_of_chain** 是 Mathlib 中的一个定理，位于命名空间
 `DivisorChain`。
形式化陈述：element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : Nat} (hn
 : n != 0) {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r
}, r <= q ↔ exists i, r = c i) (hr : r ∣ q) (hq : q != 0) : exists i : Fin (n + 
1), r = c 1 ^ (i : Nat)
参数：hn : n != 0；n + 1；h₁ : StrictMono c；h₂ : forall {r}, r <= q ↔ exists i, r = c
 i；hr : r ∣ q；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Multiset.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {s : Multiset α},
 (∀ b ∈ s, b = a) → s = Multiset.replicate s.card a
· 使用定理 `DivisorChain.eq_second_of_chain_of_prime_dvd`：eq_second_of_chain_of_prim
e_dvd {p q r : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n + 1) -> Associa
tes M} (h₁ : StrictMono c) (h₂ : f…
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `Finset.card_image_iff`：card_image_iff [DecidableEq β] : #(s.image f) = #
s ↔ Set.InjOn f s
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `pow_injective_of_not_isUnit`：pow_injective_of_not_isUnit {q : M} (hq : ¬
IsUnit q) (hq' : q != 0) : Function.Injective fun n : Nat => q ^ n
· 使用定理 `DivisorChain.element_of_chain_not_isUnit_of_index_ne_zero`：element_of_ch
ain_not_isUnit_of_index_ne_zero {n : Nat} {i : Fin (n + 1)} (i_pos : i != 0) {c 
: Fin (n + 1) -> Associates M} (h₁ : StrictMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `DivisorChain.second_of_chain_is_irreducible`：second_of_chain_is_irreduci
ble {q : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n + 1) -> Associates M}
 (h₁ : StrictMono c) (h₂ : forall…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `pow_mul_pow_sub`：pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n -
 m) = a ^ n
（共 35 条，此处仅展示前 30 条）
-/
theorem element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
    (hr : r ∣ q) (hq : q ≠ 0) : ∃ i : Fin (n + 1), r = c 1 ^ (i : ℕ) := by
  classical
    let i := Multiset.card (normalizedFactors r)
    have hi : normalizedFactors r = Multiset.replicate i (c 1) := by
      apply Multiset.eq_replicate_of_mem
      intro b hb
      refine
        eq_second_of_chain_of_prime_dvd hn h₁ (@fun r' => h₂) (prime_of_normalized_factor b hb) hr
          (dvd_of_mem_normalizedFactors hb)
    have H : r = c 1 ^ i := by
      have := UniqueFactorizationMonoid.prod_normalizedFactors (ne_zero_of_dvd_ne_zero hq hr)
      rw [associated_iff_eq, hi, Multiset.prod_replicate] at this
      rw [this]
    refine ⟨⟨i, ?_⟩, H⟩
    have : (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ)).card = i + 1 := by
      conv_rhs => rw [← Finset.card_fin (i + 1)]
      cases n
      · contradiction
      rw [Finset.card_image_iff]
      refine Set.injOn_of_injective (fun m m' h => Fin.ext ?_)
      refine
        pow_injective_of_not_isUnit (element_of_chain_not_isUnit_of_index_ne_zero (by simp) h₁) ?_ h
      exact Irreducible.ne_zero (second_of_chain_is_irreducible hn h₁ (@h₂) hq)
    suffices H' : ∀ r ∈ Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ), r ≤ q by
      simp only [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← this]
      apply card_subset_divisors_le_length_of_chain (@h₂) H'
    simp only [Finset.mem_image]
    rintro r ⟨a, _, rfl⟩
    refine dvd_trans ?_ hr
    use c 1 ^ (i - (a : ℕ))
    rw [pow_mul_pow_sub (c 1)]
    · exact H
    · exact Nat.succ_le_succ_iff.mp a.2
/-
**DivisorChain.eq_pow_second_of_chain_of_has_chain** 是 Mathlib 中的一个定理，位于命名空间 `Di
visorChain`。
形式化陈述：eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : Nat} (hn : n !
= 0) {c : Fin (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r : Ass
ociates M}, r <= q ↔ exists i, r = c i) (hq : q != 0) : q = c 1 ^ n
参数：hn : n != 0；n + 1；h₁ : StrictMono c；h₂ : forall {r : Associates M}, r <= q ↔ 
exists i, r = c i；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DivisorChain.element_of_chain_eq_pow_second_of_chain`：element_of_chain_e
q_pow_second_of_chain {q r : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n +
 1) -> Associates M} (h₁ : StrictMono c) (…
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_image_iff`：card_image_iff [DecidableEq β] : #(s.image f) = #
s ↔ Set.InjOn f s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `dvd_prime_pow`：dvd_prime_pow [CommMonoidWithZero M] [IsCancelMulZero M] 
{p q : M} (hp : Prime p) (n : Nat) : q ∣ p ^ n ↔ exists i <= n, Associated q (p 
^ i…
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `DivisorChain.second_of_chain_is_irreducible`：second_of_chain_is_irreduci
ble {q : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n + 1) -> Associates M}
 (h₁ : StrictMono c) (h₂ : forall…
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
theorem eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : q = c 1 ^ n := by
  classical
    obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (@fun r => h₂) (dvd_refl q) hq
    convert! hi'
    refine (Nat.lt_succ_iff.1 i.prop).antisymm' (Nat.le_of_succ_le_succ ?_)
    calc
      n + 1 = (Finset.univ : Finset (Fin (n + 1))).card := (Finset.card_fin _).symm
      _ = (Finset.univ.image c).card := (Finset.card_image_iff.mpr h₁.injective.injOn).symm
      _ ≤ (Finset.univ.image fun m : Fin (i + 1) => c 1 ^ (m : ℕ)).card :=
        (Finset.card_le_card ?_)
      _ ≤ (Finset.univ : Finset (Fin (i + 1))).card := Finset.card_image_le
      _ = i + 1 := Finset.card_fin _
    intro r hr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
    have := h₂.2 ⟨j, rfl⟩
    rw [hi'] at this
    have h := (dvd_prime_pow (show Prime (c 1) from ?_) i).1 this
    · rcases h with ⟨u, hu, hu'⟩
      refine Finset.mem_image.mpr ⟨⟨u, Nat.lt_succ_of_le hu⟩, Finset.mem_univ _, ?_⟩
      rwa [associated_iff_eq, eq_comm] at hu'
    · rw [← irreducible_iff_prime]
      exact second_of_chain_is_irreducible hn h₁ (@h₂) hq
/-
**DivisorChain.isPrimePow_of_has_chain** 是 Mathlib 中的一个定理，位于命名空间 `DivisorChain`。
形式化陈述：isPrimePow_of_has_chain {q : Associates M} {n : Nat} (hn : n != 0) {c : Fi
n (n + 1) -> Associates M} (h₁ : StrictMono c) (h₂ : forall {r : Associates M}, 
r <= q ↔ exists i, r = c i) (hq : q != 0) : IsPrimePow q
参数：hn : n != 0；n + 1；h₁ : StrictMono c；h₂ : forall {r : Associates M}, r <= q ↔ 
exists i, r = c i；hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `DivisorChain.second_of_chain_is_irreducible`：second_of_chain_is_irreduci
ble {q : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n + 1) -> Associates M}
 (h₁ : StrictMono c) (h₂ : forall…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DivisorChain.eq_pow_second_of_chain_of_has_chain`：eq_pow_second_of_chain
_of_has_chain {q : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n + 1) -> Ass
ociates M} (h₁ : StrictMono c) (h₂ : f…
-/
theorem isPrimePow_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Fin (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : IsPrimePow q :=
  ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq),
    zero_lt_iff.mpr hn, (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

end DivisorChain

variable {N : Type*} [CommMonoidWithZero N]

/-
**factor_orderIso_map_one_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：factor_orderIso_map_one_eq_bot [IsCancelMulZero N] {m : Associates M} {n :
 Associates N} (d : { l : Associates M // l <= m } ≃o { l : Associates N // l <=
 n }) : (d ⟨1, one_dvd m⟩ : Associates N) = 1
参数：d : { l : Associates M // l <= m } ≃o { l : Associates N // l <= n }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_bot`：mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) 
: mk ⊥ hbot = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OrderIsoClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : LE α] [inst_2 : OrderBot α]   [inst_3 : P
artialOrder β] [i…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
-/
theorem factor_orderIso_map_one_eq_bot [IsCancelMulZero N] {m : Associates M} {n : Associates N}
    (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) :
    (d ⟨1, one_dvd m⟩ : Associates N) = 1 := by
  let : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
  let : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  let : BotHomClass ({ l // l ≤ m } ≃o { l // l ≤ n }) _ _ := OrderIsoClass.toBotHomClass
  exact map_bot d

set_option backward.isDefEq.respectTransparency false in
/-
**coe_factor_orderIso_map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_factor_orderIso_map_eq_one_iff [IsCancelMulZero N] {m u : Associates M
} {n : Associates N} (hu' : u <= m) (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ :
 Associates N) = 1 ↔ u = 1
参数：hu' : u <= m；d : Set.Iic m ≃o Set.Iic n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `factor_orderIso_map_one_eq_bot`：factor_orderIso_map_one_eq_bot [IsCancel
MulZero N] {m : Associates M} {n : Associates N} (d : { l : Associates M // l <=
 m } ≃o { l : Associ…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
theorem coe_factor_orderIso_map_eq_one_iff [IsCancelMulZero N]
    {m u : Associates M} {n : Associates N} (hu' : u ≤ m)
    (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ : Associates N) = 1 ↔ u = 1 :=
  ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u, hu'⟩, (d ⟨u, hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    congr, fun hu => by
    simp_rw [hu]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d]
    rfl⟩

section

variable [UniqueFactorizationMonoid N] [UniqueFactorizationMonoid M]

open DivisorChain


set_option linter.overlappingInstances false

set_option backward.isDefEq.respectTransparency false in
/-
**pow_image_of_prime_by_factor_orderIso_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_image_of_prime_by_factor_orderIso_dvd {m p : Associates M} {n : Associ
ates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Set.Iic 
n) {s : Nat} (hs' : p ^ s <= m) : (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Asso
ciates N) ^ s <= n
参数：hn : n != 0；hp : p in normalizedFactors m；d : Set.Iic m ≃o Set.Iic n；hs' : p 
^ s <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DivisorChain.exists_chain_of_prime_pow`：exists_chain_of_prime_pow {p : A
ssociates M} {n : Nat} (hn : n != 0) (hp : Prime p) : exists c : Fin (n + 1) -> 
Associates M, c 1 = p ∧ Stri…
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DivisorChain.eq_pow_second_of_chain_of_has_chain`：eq_pow_second_of_chain
_of_has_chain {q : Associates M} {n : Nat} (hn : n != 0) {c : Fin (n + 1) -> Ass
ociates M} (h₁ : StrictMono c) (h₂ : f…
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
（共 31 条，此处仅展示前 30 条）
-/
theorem pow_image_of_prime_by_factor_orderIso_dvd
    {m p : Associates M} {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    (d : Set.Iic m ≃o Set.Iic n) {s : ℕ} (hs' : p ^ s ≤ m) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s ≤ n := by
  by_cases hs : s = 0
  · simp [← Associates.bot_eq_one, hs]
  suffices (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ^ s =
      (d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalized_factor p hp)
  let c₂ : Fin (s + 1) → Associates N := fun t => d ⟨c₁ t, le_trans (hc₁''.2 ⟨t, by simp⟩) hs'⟩
  have c₂_def : ∀ t, c₂ t = d ⟨c₁ t, _⟩ := fun t => rfl
  rw [← c₂_def]
  refine (eq_pow_second_of_chain_of_has_chain hs (fun t u h => ?_)
    (@fun r => ⟨@fun hr => ?_, ?_⟩) ?_).symm
  · rw [c₂_def, c₂_def, Subtype.coe_lt_coe, d.lt_iff_lt, Subtype.mk_lt_mk, hc₁'.lt_iff_lt]
    exact h
  · have : r ≤ n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2
    suffices d.symm ⟨r, this⟩ ≤ ⟨c₁ 1 ^ s, hs'⟩ by
      obtain ⟨i, hi⟩ := hc₁''.1 this
      use i
      simp only [c₂_def, ← hi, d.apply_symm_apply, Subtype.coe_eta, Subtype.coe_mk]
    conv_rhs => rw [← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩]
    rw [d.symm.le_iff_le]
    simpa only [← Subtype.coe_le_coe, Subtype.coe_mk] using hr
  · rintro ⟨i, hr⟩
    rw [hr, c₂_def, Subtype.coe_le_coe, d.le_iff_le]
    simpa [Subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩
  exact ne_zero_of_dvd_ne_zero hn (Subtype.prop (d ⟨c₁ 1 ^ s, _⟩))

set_option backward.isDefEq.respectTransparency false in
/-
**map_prime_of_factor_orderIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_prime_of_factor_orderIso {m p : Associates M} {n : Associates N} (hn :
 n != 0) (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) : Prime (d
 ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N)
参数：hn : n != 0；hp : p in normalizedFactors m；d : Set.Iic m ≃o Set.Iic n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associates.isAtom_iff`：Associates.isAtom_iff {p : Associates M} (h₁ : p 
!= 0) : IsAtom p ↔ Irreducible p
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Associates.isUnit_iff_eq_bot`：isUnit_iff_eq_bot {a : Associates M} : IsU
nit a ↔ a = ⊥
· 使用定理 `Associates.isUnit_iff_eq_one`：isUnit_iff_eq_one (a : Associates M) : IsU
nit a ↔ a = 1
· 使用定理 `coe_factor_orderIso_map_eq_one_iff`：coe_factor_orderIso_map_eq_one_iff [
IsCancelMulZero N] {m u : Associates M} {n : Associates N} (hu' : u <= m) (d : S
et.Iic m ≃o Set.Iic n) :…
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Subtype.mk_eq_bot_iff`：mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)]
 (hbot : p ⊥) {x : α} (hx : p x) : (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Subtype.mk_lt_mk`：mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y
（共 33 条，此处仅展示前 30 条）
-/
theorem map_prime_of_factor_orderIso {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    Prime (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) := by
  rw [← irreducible_iff_prime]
  refine (Associates.isAtom_iff <|
    ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop).mp ⟨?_, fun b hb => ?_⟩
  · rw [Ne, ← Associates.isUnit_iff_eq_bot, Associates.isUnit_iff_eq_one,
      coe_factor_orderIso_map_eq_one_iff _ d]
    rintro rfl
    exact (prime_of_normalized_factor 1 hp).not_isUnit isUnit_one
  · have : b ≤ n := le_trans (le_of_lt hb) (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
    obtain ⟨x, hx⟩ := d.surjective ⟨b, this⟩
    rw [← Subtype.coe_mk (p := (· ≤ n)) b this, ← hx] at hb
    let : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
    let : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
    suffices x = ⊥ by
      rw [this, OrderIso.map_bot d] at hx
      refine (Subtype.mk_eq_bot_iff ?_ _).mp hx.symm
      simp
    obtain ⟨a, ha⟩ := x
    rw [Subtype.mk_eq_bot_iff]
    · exact
        ((Associates.isAtom_iff <| Prime.ne_zero <| prime_of_normalized_factor p hp).mpr <|
              irreducible_of_normalized_factor p hp).right
          a (Subtype.mk_lt_mk.mp <| d.lt_iff_lt.mp hb)
    simp
/-
**mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors {m p : Asso
ciates M} {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : 
Set.Iic m ≃o Set.Iic n) : (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N
) in normalizedFactors n
参数：hn : n != 0；hp : p in normalizedFactors m；d : Set.Iic m ≃o Set.Iic n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `map_prime_of_factor_orderIso`：map_prime_of_factor_orderIso {m p : Associ
ates M} {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : Se
t.Iic m ≃o Set.Iic…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
-/
theorem mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors {m p : Associates M}
    {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : Associates N) ∈ normalizedFactors n := by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
      (d ⟨p, dvd_of_mem_normalizedFactors hp⟩).prop
  rw [associated_iff_eq] at hq'
  rwa [hq']
/-
**emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso {m p : Assoc
iates M} {n : Associates N} (hp : p in normalizedFactors m) (d : Set.Iic m ≃o Se
t.Iic n) : emultiplicity p m <= emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFact
ors hp⟩)) n
参数：hp : p in normalizedFactors m；d : Set.Iic m ≃o Set.Iic n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors.congr_simp`：∀ {α : Type u_1}
 [inst : CommMonoidWithZero α] [inst_1 : NormalizationMonoid α] [inst_2 : Unique
FactorizationMonoid α]   (a a_1 : α), a = a_…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `FiniteMultiplicity.of_prime_left`：FiniteMultiplicity.of_prime_left [Comm
MonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {a b : α} (ha : Prime a) (
hb : b != 0) : FiniteM…
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `pow_image_of_prime_by_factor_orderIso_dvd`：pow_image_of_prime_by_factor_
orderIso_dvd {m p : Associates M} {n : Associates N} (hn : n != 0) (hp : p in no
rmalizedFactors m) (d : Set.Iic…
· 使用定理 `pow_multiplicity_dvd`：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity
 a b) ∣ b
-/
theorem emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m ≤ emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm] at hp
  rw [FiniteMultiplicity.of_prime_left (prime_of_normalized_factor p hp) hm
    |>.emultiplicity_eq_multiplicity, ← pow_dvd_iff_le_emultiplicity]
  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicity_dvd ..)
/-
**emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso {m p : Assoc
iates M} {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : S
et.Iic m ≃o Set.Iic n) : emultiplicity p m = emultiplicity (↑(d ⟨p, dvd_of_mem_n
ormalizedFactors hp⟩)) n
参数：hn : n != 0；hp : p in normalizedFactors m；d : Set.Iic m ≃o Set.Iic n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso`：emultipli
city_prime_le_emultiplicity_image_by_factor_orderIso {m p : Associates M} {n : A
ssociates N} (hp : p in normalizedFactors m) (d : S…
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors`：mem_norm
alizedFactors_factor_orderIso_of_mem_normalizedFactors {m p : Associates M} {n :
 Associates N} (hn : n != 0) (hp : p in normalizedFa…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m = emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  refine le_antisymm (emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso hp d) ?_
  suffices emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n ≤
      emultiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalizedFactors hp⟩))) m by
    rw [d.symm_apply_apply ⟨p, dvd_of_mem_normalizedFactors hp⟩, Subtype.coe_mk] at this
    exact this
  let := Classical.decEq (Associates N)
  simpa only [Subtype.coe_eta] using
    emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso
      (mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors hn hp d) d.symm

end

variable [Subsingleton Mˣ] [Subsingleton Nˣ]

/-- The order isomorphism between the factors of `mk m` and the factors of `mk n` induced by a
  bijection between the factors of `m` and the factors of `n` that preserves `∣`. -/
@[simps]
/-
**mkFactorOrderIsoOfFactorDvdEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mkFactorOrderIsoOfFactorDvdEquiv {m : M} {n : N} {d : { l : M // l ∣ m } ≃
 { l : N // l ∣ n }} (hd : forall l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
 Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n) where toFun l
参数：hd : forall l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The order isomorphism between the factors of `mk m` and the factors of `mk n` in
duced by a
  bijection between the factors of `m` and the factors of `n` that preserves `∣`
.
-/
def mkFactorOrderIsoOfFactorDvdEquiv
    {m : M} {n : N} {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n) where
  toFun l :=
    ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  invFun l :=
    ⟨Associates.mk
        (d.symm
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d.symm ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  left_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, mk_out, out_mk, normalize_eq]
  right_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq, mk_out]
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Associates.mk_le_mk_iff_dvd, hd,
        associatesEquivOfUniqueUnits_apply, out_dvd_iff, mk_out]

variable [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N]

set_option linter.overlappingInstances false
/-
**mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors {m p : M} {n
 : N} (hm : m != 0) (hn : n != 0) (hp : p in normalizedFactors m) {d : { l : M /
/ l ∣ m } ≃ { l : N // l ∣ n }} (hd : forall l l', (d l : N) ∣ d l' ↔ (l : M) ∣ 
(l' : M)) : ↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩) in normalizedFactors n
参数：hm : m != 0；hn : n != 0；hp : p in normalizedFactors m；hd : forall l l', (d l 
: N) ∣ d l' ↔ (l : M) ∣ (l' : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `associatesEquivOfUniqueUnits_symm_apply`：∀ {α : Type u_1} [inst : CommMo
noidWithZero α] [inst_1 : Subsingleton αˣ] (a : α),   associatesEquivOfUniqueUni
ts.symm a = Associates.mk a
· 使用定理 `associatesEquivOfUniqueUnits_apply`：∀ {α : Type u_1} [inst : CommMonoidW
ithZero α] [inst_1 : Subsingleton αˣ] (a : Associates α),   associatesEquivOfUni
queUnits a = a.out
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_dvd_mk`：mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates
.mk b ↔ a ∣ b
· 使用定理 `mkFactorOrderIsoOfFactorDvdEquiv_apply_coe`：∀ {M : Type u_1} [inst : Com
mMonoidWithZero M] {N : Type u_2} [inst_1 : CommMonoidWithZero N] [inst_2 : Subs
ingleton Mˣ]   [inst_3 : Subsing…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.prime_mk`：prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime 
p
· 使用定理 `map_prime_of_factor_orderIso`：map_prime_of_factor_orderIso {m p : Associ
ates M} {n : Associates N} (hn : n != 0) (hp : p in normalizedFactors m) (d : Se
t.Iic m ≃o Set.Iic…
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Associates.mk_le_mk_of_dvd`：mk_le_mk_of_dvd {a b : M} : a ∣ b -> Associa
tes.mk a <= Associates.mk b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors {m p : M} {n : N} (hm : m ≠ 0)
    (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    ↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩) ∈ normalizedFactors n := by
  suffices
    Prime (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
            simp [dvd_of_mem_normalizedFactors hp]⟩ : N) by
    simp only [associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq,
      associatesEquivOfUniqueUnits_symm_apply] at this
    obtain ⟨q, hq, hq'⟩ :=
      exists_mem_normalizedFactors_of_dvd hn this.irreducible
        (d ⟨p, by apply dvd_of_mem_normalizedFactors; convert! hp⟩).prop
    rwa [associated_iff_eq.mp hq']
  have :
    Associates.mk
        (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
              simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_apply,
                out_mk, normalize_eq, associatesEquivOfUniqueUnits_symm_apply]⟩ : N) =
      ↑(mkFactorOrderIsoOfFactorDvdEquiv hd
          ⟨associatesEquivOfUniqueUnits.symm p, by
            simp only [associatesEquivOfUniqueUnits_symm_apply]
            exact mk_dvd_mk.mpr (dvd_of_mem_normalizedFactors hp)⟩) := by
    rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [← Associates.prime_mk, this]
  let := Classical.decEq (Associates M)
  refine map_prime_of_factor_orderIso (mk_ne_zero.mpr hn) ?_ _
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      (prime_mk.mpr (prime_of_normalized_factor p (by convert! hp))).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  simpa only [associated_iff_eq.mp hq', associatesEquivOfUniqueUnits_symm_apply] using hq
/-
**emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors {m 
p : M} {n : N} (hm : m != 0) (hn : n != 0) (hp : p in normalizedFactors m) {d : 
{ l : M // l ∣ m } ≃ { l : N // l ∣ n }} (hd : forall l l', (d l : N) ∣ d l' ↔ (
l : M) ∣ l') : emultiplicity (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : N) n = em
ultiplicity p m
参数：hm : m != 0；hn : n != 0；hp : p in normalizedFactors m；hd : forall l l', (d l 
: N) ∣ d l' ↔ (l : M) ∣ l'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `associatesEquivOfUniqueUnits_symm_apply`：∀ {α : Type u_1} [inst : CommMo
noidWithZero α] [inst_1 : Subsingleton αˣ] (a : α),   associatesEquivOfUniqueUni
ts.symm a = Associates.mk a
· 使用定理 `associatesEquivOfUniqueUnits_apply`：∀ {α : Type u_1} [inst : CommMonoidW
ithZero α] [inst_1 : Subsingleton αˣ] (a : Associates α),   associatesEquivOfUni
queUnits a = a.out
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Associates.mk_le_mk_of_dvd`：mk_le_mk_of_dvd {a b : M} : a ∣ b -> Associa
tes.mk a <= Associates.mk b
· 使用定理 `mkFactorOrderIsoOfFactorDvdEquiv_apply_coe`：∀ {M : Type u_1} [inst : Com
mMonoidWithZero M] {N : Type u_2} [inst_1 : CommMonoidWithZero N] [inst_2 : Subs
ingleton Mˣ]   [inst_3 : Subsing…
· 使用定理 `emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso`：emultipli
city_prime_eq_emultiplicity_image_by_factor_orderIso {m p : Associates M} {n : A
ssociates N} (hn : n != 0) (hp : p in normalizedFac…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Associates.prime_mk`：prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime 
p
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `emultiplicity_mk_eq_emultiplicity`：emultiplicity_mk_eq_emultiplicity {a 
b : α} : emultiplicity (Associates.mk a) (Associates.mk b) = emultiplicity a b
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
theorem emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors {m p : M} {n : N}
    (hm : m ≠ 0) (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }} (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ l') :
    emultiplicity (d ⟨p, dvd_of_mem_normalizedFactors hp⟩ : N) n = emultiplicity p m := by
  apply Eq.symm
  suffices emultiplicity (Associates.mk p) (Associates.mk m) = emultiplicity (Associates.mk
    ↑(d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
      simp [dvd_of_mem_normalizedFactors hp]⟩)) (Associates.mk n) by
    simpa only [emultiplicity_mk_eq_emultiplicity, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq] using this
  have : Associates.mk (d ⟨associatesEquivOfUniqueUnits (associatesEquivOfUniqueUnits.symm p), by
    simp only [dvd_of_mem_normalizedFactors hp, associatesEquivOfUniqueUnits_symm_apply,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq]⟩ : N) =
    ↑(mkFactorOrderIsoOfFactorDvdEquiv hd ⟨associatesEquivOfUniqueUnits.symm p, by
      rw [associatesEquivOfUniqueUnits_symm_apply]
      exact mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp)⟩) := by
    rw [mkFactorOrderIsoOfFactorDvdEquiv_apply_coe]
  rw [this]
  refine
    emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso (mk_ne_zero.mpr hn) ?_
      (mkFactorOrderIsoOfFactorDvdEquiv hd)
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalizedFactors_of_dvd (mk_ne_zero.mpr hm)
      (prime_mk.mpr (prime_of_normalized_factor p hp)).irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalizedFactors hp))
  rwa [associated_iff_eq.mp hq']
