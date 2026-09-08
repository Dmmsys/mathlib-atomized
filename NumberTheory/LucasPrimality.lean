/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.IntegralDomain

/-!
# The Lucas test for primes

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the `norm_num` primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`. In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

public section


/-- If `a^(p-1) = 1 mod p`, but `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`, then `p`
is prime. This is true because `a` has order `p-1` in the multiplicative group mod `p`, so this
group must itself have order `p-1`, which only happens when `p` is prime.
-/
/-
**lucas_primality** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lucas_primality (p : Nat) (a : ZMod p) (ha : a ^ (p - 1) = 1) (hd : forall
 q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1) : p.Prime
参数：p : Nat；a : ZMod p；ha : a ^ (p - 1) = 1；hd : forall q : Nat, q.Prime -> q ∣ p
 - 1 -> a ^ ((p - 1) / q) != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_iff_card_units`：prime_iff_card_units (p : Nat) [Fintype (ZMod 
p)ˣ] : p.Prime ↔ Fintype.card (ZMod p)ˣ = p - 1
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.card_units_zmod_lt_sub_one`：card_units_zmod_lt_sub_one {p : Nat} (hp
 : 1 < p) [Fintype (ZMod p)ˣ] : Fintype.card (ZMod p)ˣ <= p - 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `orderOf_eq_of_pow_and_pow_div_prime`：orderOf_eq_of_pow_and_pow_div_prime
 (hn : 0 < n) (hx : x ^ n = 1) (hd : forall p : Nat, p.Prime -> p ∣ n -> x ^ (n 
/ p) != 1) : orderOf x = …
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `orderOf_le_card_univ`：orderOf_le_card_univ [Fintype G] : orderOf x <= Fi
ntype.card G

--- 原说明 ---
If `a^(p-1) = 1 mod p`, but `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of
 `p-1`, then `p`
is prime. This is true because `a` has order `p-1` in the multiplicative group m
od `p`, so this
group must itself have order `p-1`, which only happens when `p` is prime.
-/
theorem lucas_primality (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : p.Prime := by
  have h : p ≠ 0 ∧ p ≠ 1 := by
    constructor <;> rintro rfl <;> exact hd 2 Nat.prime_two (dvd_zero _) (pow_zero _)
  have hp1 : 1 < p := Nat.one_lt_iff_ne_zero_and_ne_one.2 h
  have : NeZero p := ⟨h.1⟩
  rw [Nat.prime_iff_card_units]
  apply (Nat.card_units_zmod_lt_sub_one hp1).antisymm
  let a' : (ZMod p)ˣ := Units.mkOfMulEqOne a _ (by rwa [← pow_succ', tsub_add_eq_add_tsub hp1])
  calc p - 1 = orderOf a := (orderOf_eq_of_pow_and_pow_div_prime (tsub_pos_of_lt hp1) ha hd).symm
    _ = orderOf a' := orderOf_injective (Units.coeHom _) Units.val_injective a'
    _ ≤ Fintype.card (ZMod p)ˣ := orderOf_le_card_univ

/-- If `p` is prime, then there exists an `a` such that `a^(p-1) = 1 mod p`
and `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`.
The multiplicative group mod `p` is cyclic, so `a` can be any generator of the group
(which must have order `p-1`).
-/
/-
**reverse_lucas_primality** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reverse_lucas_primality (p : Nat) (hP : p.Prime) : exists a : ZMod p, a ^ 
(p - 1) = 1 ∧ forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1
参数：p : Nat；hP : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prime_iff_card_units`：prime_iff_card_units (p : Nat) [Fintype (ZMod 
p)ˣ] : p.Prime ↔ Fintype.card (ZMod p)ˣ = p - 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `orderOf_eq_iff`：orderOf_eq_iff {n} (h : 0 < n) : orderOf x = n ↔ x ^ n =
 1 ∧ forall m, m < n -> 0 < m -> x ^ m != 1
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
If `p` is prime, then there exists an `a` such that `a^(p-1) = 1 mod p`
and `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`.
The multiplicative group mod `p` is cyclic, so `a` can be any generator of the g
roup
(which must have order `p-1`).
-/
theorem reverse_lucas_primality (p : ℕ) (hP : p.Prime) :
    ∃ a : ZMod p, a ^ (p - 1) = 1 ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1 := by
  have : Fact p.Prime := ⟨hP⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have h1 : orderOf g = p - 1 := by
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ← Nat.prime_iff_card_units]
  have h2 := tsub_pos_iff_lt.2 hP.one_lt
  rw [← orderOf_injective (Units.coeHom _) Units.val_injective _, orderOf_eq_iff h2] at h1
  refine ⟨g, h1.1, fun q hq hqd ↦ ?_⟩
  replace hq := hq.one_lt
  exact h1.2 _ (Nat.div_lt_self h2 hq) (Nat.div_pos (Nat.le_of_dvd h2 hqd) (zero_lt_one.trans hq))

/-- A number `p` is prime if and only if there exists an `a` such that
`a^(p-1) = 1 mod p` and `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`.
-/
/-
**lucas_primality_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lucas_primality_iff (p : Nat) : p.Prime ↔ exists a : ZMod p, a ^ (p - 1) =
 1 ∧ forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1
参数：p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `reverse_lucas_primality`：reverse_lucas_primality (p : Nat) (hP : p.Prime
) : exists a : ZMod p, a ^ (p - 1) = 1 ∧ forall q : Nat, q.Prime -> q ∣ p - 1 ->
 a ^ ((p - 1)…
· 使用定理 `lucas_primality`：lucas_primality (p : Nat) (a : ZMod p) (ha : a ^ (p - 1
) = 1) (hd : forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1) : p
.Prim…

--- 原说明 ---
A number `p` is prime if and only if there exists an `a` such that
`a^(p-1) = 1 mod p` and `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-
1`.
-/
theorem lucas_primality_iff (p : ℕ) : p.Prime ↔
    ∃ a : ZMod p, a ^ (p - 1) = 1 ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1 :=
  ⟨reverse_lucas_primality p, fun ⟨a, ⟨ha, hb⟩⟩ ↦ lucas_primality p a ha hb⟩
