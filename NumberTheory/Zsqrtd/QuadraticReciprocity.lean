/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Facts about the Gaussian integers relying on quadratic reciprocity.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

-/

public section


open Zsqrtd Complex

open scoped ComplexConjugate

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

open PrincipalIdealRing

/-
**GaussianInt.mod_four_eq_three_of_nat_prime_of_prime** 是 Mathlib 中的一个定理，位于命名空间 
`GaussianInt`。
形式化陈述：mod_four_eq_three_of_nat_prime_of_prime (p : Nat) [hp : Fact p.Prime] (hpi
 : Prime (p : Int[i])) : p % 4 = 3
参数：p : Nat；hpi : Prime (p : Int[i])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.Prime.eq_two_or_odd`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.exists_sq_eq_neg_one_iff`：exists_sq_eq_neg_one_iff : IsSquare (-1 :
 ZMod p) ↔ p % 4 != 3
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
（共 60 条，此处仅展示前 30 条）
-/
theorem mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : Fact p.Prime]
    (hpi : Prime (p : ℤ[i])) : p % 4 = 3 :=
  hp.1.eq_two_or_odd.elim
    (fun hp2 => by
      have := hpi.irreducible.isUnit_or_isUnit (a := ⟨1, 1⟩) (b := ⟨1, -1⟩)
      simp [hp2, Zsqrtd.ext_iff, ← norm_eq_one_iff, norm_def] at this)
    fun hp1 =>
    by_contradiction fun hp3 : p % 4 ≠ 3 => by
      let ⟨k, hk⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hp3
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (_ : k' < p), (k' : ZMod p) = k := by
        exact ⟨k.val, k.val_lt, ZMod.natCast_zmod_val k⟩
      have hpk : p ∣ k ^ 2 + 1 := by
        rw [pow_two, ← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
          ← hk, neg_add_cancel]
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ := by ext <;> simp [sq]
      have hk₀ : k ≠ 0 := by rintro rfl; simp at hk
      have hkltp := calc
          1 + k * k ≤ k * (k + 1) := by lia
          _ < p * p := mul_lt_mul k_lt_p k_lt_p (Nat.succ_pos _) (Nat.zero_le _)
      have hpk₁ : ¬(p : ℤ[i]) ∣ ⟨k, -1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, -1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using! hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (-1 : ℤ) ≠ 0 by decide <| by simpa [hx0] using! congr_arg Zsqrtd.im hx
      have hpk₂ : ¬(p : ℤ[i]) ∣ ⟨k, 1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, 1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using! hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (1 : ℤ) ≠ 0 by decide <| by simpa [hx0] using! congr_arg Zsqrtd.im hx
      obtain ⟨y, hy⟩ := hpk
      have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← Nat.cast_mul p, ← hy]; simp⟩
      tauto
/-
**GaussianInt.prime_of_nat_prime_of_mod_four_eq_three** 是 Mathlib 中的一个定理，位于命名空间 
`GaussianInt`。
形式化陈述：prime_of_nat_prime_of_mod_four_eq_three (p : Nat) [Fact p.Prime] (hp3 : p 
% 4 = 3) : Prime (p : Int[i])
参数：p : Nat；hp3 : p % 4 = 3。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible`：sq_add_sq_of_nat_
prime_of_not_irreducible (p : Nat) [hp : Fact p.Prime] (hpi : ¬Irreducible (p : 
Int[i])) : exists a b, a ^ 2 + b ^ 2 = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_mod`：natCast_mod (a : Nat) (n : Nat) : ((a % n : Nat) : ZMo
d n) = a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [Fact p.Prime] (hp3 : p % 4 = 3) :
    Prime (p : ℤ[i]) :=
  irreducible_iff_prime.1 <|
    by_contradiction fun hpi =>
      let ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi
      have : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ (p : ZMod 4) := by
        rw [← ZMod.natCast_mod p 4, hp3]; decide
      this a b (hab ▸ by simp)

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
/-
**GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime** 是 Mathlib 中的一个定理，位于命名空间
 `GaussianInt`。
形式化陈述：prime_iff_mod_four_eq_three_of_nat_prime (p : Nat) [Fact p.Prime] : Prime 
(p : Int[i]) ↔ p % 4 = 3
参数：p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaussianInt.mod_four_eq_three_of_nat_prime_of_prime`：mod_four_eq_three_o
f_nat_prime_of_prime (p : Nat) [hp : Fact p.Prime] (hpi : Prime (p : Int[i])) : 
p % 4 = 3
· 使用定理 `GaussianInt.prime_of_nat_prime_of_mod_four_eq_three`：prime_of_nat_prime_
of_mod_four_eq_three (p : Nat) [Fact p.Prime] (hp3 : p % 4 = 3) : Prime (p : Int
[i])

--- 原说明 ---
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`
-/
theorem prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [Fact p.Prime] :
    Prime (p : ℤ[i]) ↔ p % 4 = 3 :=
  ⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩

end GaussianInt

