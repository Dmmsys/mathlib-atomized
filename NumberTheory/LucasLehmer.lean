/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Alastair Irving, Kim Morrison, Ainsley Pahljina
-/
module

public import Mathlib.NumberTheory.Fermat
public import Mathlib.RingTheory.Fintype

/-!
# The Lucas-Lehmer test for Mersenne primes

We define `lucasLehmerResidue : Π p : ℕ, ZMod (2^p - 1)`, and
prove `lucasLehmerResidue p = 0 ↔ Prime (mersenne p)`.

We construct a `norm_num` extension to calculate this residue to certify primality of Mersenne
primes using `lucas_lehmer_sufficiency`.


## TODO

- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Kim Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
This tactic was ported by Thomas Murrills to Lean 4, and then it was converted to a `norm_num`
extension and made to use kernel reductions by Kyle Miller.
-/

@[expose] public section

/-- The Mersenne numbers, 2^p - 1. -/
/-
**mersenne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mersenne (p : Nat) : Nat
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mersenne numbers, 2^p - 1.
-/
def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1
/-
**strictMono_mersenne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_mersenne : StrictMono mersenne
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.sub_lt_sub_iff_right`：∀ {a b c : ℕ}, c ≤ a → (a - c < b - c ↔ a < b)
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_lt_pow_right₀`：pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m <
 a ^ n
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem strictMono_mersenne : StrictMono mersenne := fun m n h ↦
  (Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 <| by gcongr; norm_num1

@[simp, gcongr]
/-
**mersenne_lt_mersenne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mersenne_lt_mersenne {p q : Nat} : mersenne p < mersenne q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `strictMono_mersenne`：strictMono_mersenne : StrictMono mersenne
-/
theorem mersenne_lt_mersenne {p q : ℕ} : mersenne p < mersenne q ↔ p < q :=
  strictMono_mersenne.lt_iff_lt

@[simp, gcongr]
/-
**mersenne_le_mersenne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mersenne_le_mersenne {p q : Nat} : mersenne p <= mersenne q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `strictMono_mersenne`：strictMono_mersenne : StrictMono mersenne
-/
theorem mersenne_le_mersenne {p q : ℕ} : mersenne p ≤ mersenne q ↔ p ≤ q :=
  strictMono_mersenne.le_iff_le
/-
**mersenne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mersenne 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mersenne_zero : mersenne 0 = 0 := rfl
/-
**mersenne_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0
参数：mersenne p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Nat.Even.sub_odd`：∀ {m n : ℕ}, n ≤ m → Even m → Odd n → Odd (m - n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_of_ne_zero`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even 
a → ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
-/
@[simp] lemma mersenne_odd : ∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0
  | 0 => by simp
  | p + 1 => by
    simpa using! Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero p.succ_ne_zero) odd_one
/-
**mersenne_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {p : ℕ}, 0 < mersenne p ↔ 0 < p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mersenne_lt_mersenne`：mersenne_lt_mersenne {p q : Nat} : mersenne p < me
rsenne q ↔ p < q
-/
@[simp] theorem mersenne_pos {p : ℕ} : 0 < mersenne p ↔ 0 < p := mersenne_lt_mersenne (p := 0)
/-
**mersenne_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mersenne_succ (n : Nat) : mersenne (n + 1) = 2 * mersenne n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma mersenne_succ (n : ℕ) : mersenne (n + 1) = 2 * mersenne n + 1 := by
  dsimp [mersenne]
  have := Nat.one_le_pow n 2 two_pos
  lia

/-- If `2 ^ p - 1` is prime, then `p` is prime. -/
/-
**Nat.Prime.of_mersenne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Prime.of_mersenne {p : Nat} (h : (mersenne p).Prime) : Nat.Prime p
参数：h : (mersenne p).Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.prime_of_pow_sub_one_prime`：prime_of_pow_sub_one_prime {a n : Nat} (
hn1 : n != 1) (hP : (a ^ n - 1).Prime) : a = 2 ∧ n.Prime
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `2 ^ p - 1` is prime, then `p` is prime.
-/
lemma Nat.Prime.of_mersenne {p : ℕ} (h : (mersenne p).Prime) : Nat.Prime p := by
  apply Nat.prime_of_pow_sub_one_prime _ h |>.2
  rintro rfl
  apply Nat.not_prime_one h

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

alias ⟨_, mersenne_pos_of_pos⟩ := mersenne_pos

/-- Extension for the `positivity` tactic: `mersenne`. -/
@[positivity mersenne _]
meta def evalMersenne : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(mersenne $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(mersenne_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Nat.zero_le (mersenne $a)))
  | _, _, _ => throwError "not mersenne"

end Mathlib.Meta.Positivity

@[simp]
/-
**one_lt_mersenne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_mersenne {p : Nat} : 1 < mersenne p ↔ 1 < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mersenne_lt_mersenne`：mersenne_lt_mersenne {p q : Nat} : mersenne p < me
rsenne q ↔ p < q
-/
theorem one_lt_mersenne {p : ℕ} : 1 < mersenne p ↔ 1 < p :=
  mersenne_lt_mersenne (p := 1)

@[simp]
/-
**succ_mersenne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：succ_mersenne (k : Nat) : mersenne k + 1 = 2 ^ k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mersenne.eq_1`：∀ (p : ℕ), mersenne p = 2 ^ p - 1
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k := by
  rw [mersenne, tsub_add_cancel_of_le]
  exact one_le_pow₀ (by simp)
/-
**mersenne_mod_four** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mersenne_mod_four {n : Nat} (h : 2 <= n) : mersenne n % 4 = 3
参数：h : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mersenne_succ`：mersenne_succ (n : Nat) : mersenne (n + 1) = 2 * mersenne
 n + 1
-/
lemma mersenne_mod_four {n : ℕ} (h : 2 ≤ n) : mersenne n % 4 = 3 := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia
/-
**mersenne_mod_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mersenne_mod_three {n : Nat} (odd : Odd n) (h : 3 <= n) : mersenne n % 3 =
 1
参数：odd : Odd n；h : 3 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mersenne_succ`：mersenne_succ (n : Nat) : mersenne (n + 1) = 2 * mersenne
 n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mersenne_mod_three {n : ℕ} (odd : Odd n) (h : 3 ≤ n) : mersenne n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := odd
  replace h : 1 ≤ k := by lia
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ j _ _ =>
    rw [mersenne_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by lia, mersenne_succ]
    lia
/-
**mersenne_mod_eight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mersenne_mod_eight {n : Nat} (h : 3 <= n) : mersenne n % 8 = 7
参数：h : 3 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mersenne_succ`：mersenne_succ (n : Nat) : mersenne (n + 1) = 2 * mersenne
 n + 1
-/
lemma mersenne_mod_eight {n : ℕ} (h : 3 ≤ n) : mersenne n % 8 = 7 := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; lia

/-- If `2^p - 1` is prime then 2 is a square mod `2^p - 1`. -/
/-
**legendreSym_mersenne_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：legendreSym_mersenne_two {p : Nat} [Fact (mersenne p).Prime] (hp : 3 <= p)
 : legendreSym (mersenne p) 2 = 1
参数：mersenne p；hp : 3 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mersenne_mod_eight`：mersenne_mod_eight {n : Nat} (h : 3 <= n) : mersenne
 n % 8 = 7
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.at_two`：at_two (hp : p != 2) : legendreSym p 2 = χ₈ p
· 使用定理 `ZMod.χ₈_nat_eq_if_mod_eight`：χ₈_nat_eq_if_mod_eight (n : Nat) : χ₈ n = i
f n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1

--- 原说明 ---
If `2^p - 1` is prime then 2 is a square mod `2^p - 1`.
-/
lemma legendreSym_mersenne_two {p : ℕ} [Fact (mersenne p).Prime] (hp : 3 ≤ p) :
    legendreSym (mersenne p) 2 = 1 := by
  have := mersenne_mod_eight hp
  rw [legendreSym.at_two (by lia), ZMod.χ₈_nat_eq_if_mod_eight]
  lia

/-- If `2^p - 1` is prime then 3 is not a square mod `2^p - 1`. -/
/-
**legendreSym_mersenne_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：legendreSym_mersenne_three {p : Nat} [Fact (mersenne p).Prime] (hp : 3 <= 
p) (odd : Odd p) : legendreSym (mersenne p) 3 = -1
参数：mersenne p；hp : 3 <= p；odd : Odd p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.quadratic_reciprocity_three_mod_four`：quadratic_reciprocity_
three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) : legendreSym q p = -legendreSy
m p q
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_natMod`：∀ {a b a' b' c : ℕ},   Mathlib.Meta.N
ormNum.IsNat a a' →     Mathlib.Meta.NormNum.IsNat b b' → a'.mod b' = c → Mathli
b.Meta.NormNum.IsNat (a…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `mersenne_mod_four`：mersenne_mod_four {n : Nat} (h : 2 <= n) : mersenne n
 % 4 = 3
· 使用定理 `legendreSym.mod`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendre
Sym p a = legendreSym p (a % ↑p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `mersenne_mod_three`：mersenne_mod_three {n : Nat} (odd : Odd n) (h : 3 <=
 n) : mersenne n % 3 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `legendreSym.congr_simp`：∀ (p p_1 : ℕ) (e_p : p = p_1) [inst : Fact (Nat.
Prime p)] (a a_1 : ℤ), a = a_1 → legendreSym p a = legendreSym p_1 a_1
· 使用定理 `legendreSym.at_one`：at_one : legendreSym p 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `2^p - 1` is prime then 3 is not a square mod `2^p - 1`.
-/
lemma legendreSym_mersenne_three {p : ℕ} [Fact (mersenne p).Prime] (hp : 3 ≤ p) (odd : Odd p) :
    legendreSym (mersenne p) 3 = -1 := by
  rw [(by rfl : (3 : ℤ) = (3 : ℕ)), legendreSym.quadratic_reciprocity_three_mod_four (by norm_num)
    (mersenne_mod_four (by lia)),
    legendreSym.mod]
  rw_mod_cast [mersenne_mod_three odd hp]
  simp

namespace LucasLehmer

open Nat

/-!
We now define three(!) different versions of the recurrence
`s (i+1) = (s i)^2 - 2`.

These versions take values either in `ℤ`, in `ZMod (2^p - 1)`, or
in `ℤ` but applying `% (2^p - 1)` at each step.

They are each useful at different points in the proof,
so we take a moment setting up the lemmas relating them.
-/

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ℤ`. -/
/-
**LucasLehmer.s** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：ℕ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The recurrence `s (i+1) = (s i)^2 - 2` in `ℤ`.
-/
def s : ℕ → ℤ
  | 0 => 4
  | i + 1 => s i ^ 2 - 2

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ZMod (2^p - 1)`. -/
/-
**LucasLehmer.sZMod** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：(p : ℕ) → ℕ → ZMod (2 ^ p - 1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The recurrence `s (i+1) = (s i)^2 - 2` in `ZMod (2^p - 1)`.
-/
def sZMod (p : ℕ) : ℕ → ZMod (2 ^ p - 1)
  | 0 => 4
  | i + 1 => sZMod p i ^ 2 - 2

/-- The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`. -/
/-
**LucasLehmer.sMod** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：ℕ → ℕ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`.
-/
def sMod (p : ℕ) : ℕ → ℤ
  | 0 => 4 % (2 ^ p - 1)
  | i + 1 => (sMod p i ^ 2 - 2) % (2 ^ p - 1)
/-
**LucasLehmer.mersenne_int_pos** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：mersenne_int_pos {p : Nat} (hp : p != 0) : (0 : Int) < 2 ^ p - 1
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.one_lt_two_pow`：∀ {n : ℕ}, n ≠ 0 → 1 < 2 ^ n
-/
theorem mersenne_int_pos {p : ℕ} (hp : p ≠ 0) : (0 : ℤ) < 2 ^ p - 1 :=
  sub_pos.2 <| mod_cast Nat.one_lt_two_pow hp
/-
**LucasLehmer.mersenne_int_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：mersenne_int_ne_zero (p : Nat) (hp : p != 0) : (2 ^ p - 1 : Int) != 0
参数：p : Nat；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LucasLehmer.mersenne_int_pos`：mersenne_int_pos {p : Nat} (hp : p != 0) :
 (0 : Int) < 2 ^ p - 1
-/
theorem mersenne_int_ne_zero (p : ℕ) (hp : p ≠ 0) : (2 ^ p - 1 : ℤ) ≠ 0 :=
  (mersenne_int_pos hp).ne'
/-
**LucasLehmer.sMod_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：sMod_nonneg (p : Nat) (hp : p != 0) (i : Nat) : 0 <= sMod p i
参数：p : Nat；hp : p != 0；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `LucasLehmer.mersenne_int_ne_zero`：mersenne_int_ne_zero (p : Nat) (hp : p
 != 0) : (2 ^ p - 1 : Int) != 0
-/
theorem sMod_nonneg (p : ℕ) (hp : p ≠ 0) (i : ℕ) : 0 ≤ sMod p i := by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp
/-
**LucasLehmer.sMod_mod** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：sMod_mod (p i : Nat) : sMod p i % (2 ^ p - 1) = sMod p i
参数：p i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sMod_mod (p i : ℕ) : sMod p i % (2 ^ p - 1) = sMod p i := by cases i <;> simp [sMod]
/-
**LucasLehmer.sMod_lt** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：sMod_lt (p : Nat) (hp : p != 0) (i : Nat) : sMod p i < 2 ^ p - 1
参数：p : Nat；hp : p != 0；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LucasLehmer.sMod_mod`：sMod_mod (p i : Nat) : sMod p i % (2 ^ p - 1) = sM
od p i
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Int.emod_lt_abs`：emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < 
|b|
· 使用定理 `LucasLehmer.mersenne_int_ne_zero`：mersenne_int_ne_zero (p : Nat) (hp : p
 != 0) : (2 ^ p - 1 : Int) != 0
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LucasLehmer.mersenne_int_pos`：mersenne_int_pos {p : Nat} (hp : p != 0) :
 (0 : Int) < 2 ^ p - 1
-/
theorem sMod_lt (p : ℕ) (hp : p ≠ 0) (i : ℕ) : sMod p i < 2 ^ p - 1 := by
  rw [← sMod_mod]
  refine (Int.emod_lt_abs _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le
/-
**LucasLehmer.sZMod_eq_s** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：sZMod_eq_s (p' : Nat) (i : Nat) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' 
+ 2) - 1))
参数：p' : Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
-/
theorem sZMod_eq_s (p' : ℕ) (i : ℕ) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1)) := by
  induction i with
  | zero => dsimp [s, sZMod]; simp
  | succ i ih => push_cast [s, sZMod, ih]; rfl
/-
**LucasLehmer.sZMod_eq_sMod** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：sZMod_eq_sMod (p : Nat) (i : Nat) : sZMod p i = (sMod p i : ZMod (2 ^ p - 
1))
参数：p : Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.coe_nat_two_pow_pred`：coe_nat_two_pow_pred (p : Nat) : ((2 ^ p - 1 :
 Nat) : Int) = (2 ^ p - 1 : Int)
· 使用定理 `ZMod.intCast_mod`：intCast_mod (a : Int) (b : Nat) : ((a % b : Int) : ZMo
d b) = (a : ZMod b)
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
-/
theorem sZMod_eq_sMod (p : ℕ) (i : ℕ) : sZMod p i = (sMod p i : ZMod (2 ^ p - 1)) := by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl

/-- The Lucas-Lehmer residue is `s p (p-2)` in `ZMod (2^p - 1)`. -/
/-
**LucasLehmer.lucasLehmerResidue** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：lucasLehmerResidue (p : Nat) : ZMod (2 ^ p - 1)
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lucas-Lehmer residue is `s p (p-2)` in `ZMod (2^p - 1)`.
-/
def lucasLehmerResidue (p : ℕ) : ZMod (2 ^ p - 1) :=
  sZMod p (p - 2)
/-
**LucasLehmer.residue_eq_zero_iff_sMod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LucasL
ehmer`。
形式化陈述：residue_eq_zero_iff_sMod_eq_zero (p : Nat) (w : 1 < p) : lucasLehmerResidu
e p = 0 ↔ sMod p (p - 2) = 0
参数：p : Nat；w : 1 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LucasLehmer.sZMod_eq_sMod`：sZMod_eq_sMod (p : Nat) (i : Nat) : sZMod p i
 = (sMod p i : ZMod (2 ^ p - 1))
· 使用引理 `Int.eq_zero_of_dvd_of_nonneg_of_lt`：eq_zero_of_dvd_of_nonneg_of_lt (hm :
 0 <= m) (hmn : m < n) (hnm : n ∣ m) : m = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LucasLehmer.sMod_nonneg`：sMod_nonneg (p : Nat) (hp : p != 0) (i : Nat) :
 0 <= sMod p i
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `LucasLehmer.sMod_lt`：sMod_lt (p : Nat) (hp : p != 0) (i : Nat) : sMod p 
i < 2 ^ p - 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_pred`：∀ {R : Type u} [inst : AddGroupWithOne R] {n : ℕ}, 0 < n 
→ ↑(n - 1) = ↑n - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem residue_eq_zero_iff_sMod_eq_zero (p : ℕ) (w : 1 < p) :
    lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _
      (by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h) <;> clear h
    · exact sMod_nonneg _ (by positivity) _
    · exact sMod_lt _ (by positivity) _
  · intro h
    rw [h]
    simp

/-- **Lucas-Lehmer Test**: a Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
/-
**LucasLehmer.LucasLehmerTest** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：LucasLehmerTest (p : Nat) : Prop
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Lucas-Lehmer Test**: a Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
def LucasLehmerTest (p : ℕ) : Prop :=
  lucasLehmerResidue p = 0

/-- `q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`. -/
/-
**LucasLehmer.q** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：q (p : Nat) : Nat+
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`.
-/
def q (p : ℕ) : ℕ+ :=
  ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩

-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),
-- obtaining the ring structure for free,
-- but that seems to be more trouble than it's worth;
-- if it were easy to make the definition,
-- cardinality calculations would be somewhat more involved, too.
/-- We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ. -/
/-
**LucasLehmer.X** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
形式化陈述：X (q : Nat) : Type
参数：q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ.
-/
def X (q : ℕ) : Type :=
  ZMod q × ZMod q

namespace X

variable {q : ℕ}

/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (X q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq (X q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (X q) := inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext]
/-
**LucasLehmer.X.ext** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y
参数：h₁ : x.1 = y.1；h₂ : x.2 = y.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; congr
/-
**LucasLehmer.X.zero_fst** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：∀ {q : ℕ}, 0.1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem zero_fst : (0 : X q).1 = 0 := rfl
/-
**LucasLehmer.X.zero_snd** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：∀ {q : ℕ}, 0.2 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem zero_snd : (0 : X q).2 = 0 := rfl

@[simp]
/-
**LucasLehmer.X.add_fst** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：add_fst (x y : X q) : (x + y).1 = x.1 + y.1
参数：x y : X q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_fst (x y : X q) : (x + y).1 = x.1 + y.1 :=
  rfl

@[simp]
/-
**LucasLehmer.X.add_snd** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：add_snd (x y : X q) : (x + y).2 = x.2 + y.2
参数：x y : X q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_snd (x y : X q) : (x + y).2 = x.2 + y.2 :=
  rfl

@[simp]
/-
**LucasLehmer.X.neg_fst** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：neg_fst (x : X q) : (-x).1 = -x.1
参数：x : X q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_fst (x : X q) : (-x).1 = -x.1 :=
  rfl

@[simp]
/-
**LucasLehmer.X.neg_snd** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：neg_snd (x : X q) : (-x).2 = -x.2
参数：x : X q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_snd (x : X q) : (-x).2 = -x.2 :=
  rfl
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (X q) where mul x y := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]
/-
**LucasLehmer.X.mul_fst** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2
参数：x y : X q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 :=
  rfl

@[simp]
/-
**LucasLehmer.X.mul_snd** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1
参数：x y : X q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 :=
  rfl
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (X q) where one := ⟨1, 0⟩

@[simp]
/-
**LucasLehmer.X.one_fst** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：one_fst : (1 : X q).1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_fst : (1 : X q).1 = 1 :=
  rfl

@[simp]
/-
**LucasLehmer.X.one_snd** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：one_snd : (1 : X q).2 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_snd : (1 : X q).2 = 0 :=
  rfl
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (X q) :=
  { (inferInstance : Mul (X q)), (inferInstance : One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (X q) where
    natCast := fun n => ⟨n, 0⟩
/-
**LucasLehmer.X.fst_natCast** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：∀ {q : ℕ} (n : ℕ), (↑n).1 = ↑n
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_natCast (n : ℕ) : (n : X q).fst = (n : ZMod q) := rfl
/-
**LucasLehmer.X.snd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：∀ {q : ℕ} (n : ℕ), (↑n).2 = 0
参数：n : ℕ；↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_natCast (n : ℕ) : (n : X q).snd = (0 : ZMod q) := rfl
/-
**LucasLehmer.X.ofNat_fst** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：∀ {q : ℕ} (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).1 = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofNat_fst (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : X q).fst = OfNat.ofNat n :=
  rfl
/-
**LucasLehmer.X.ofNat_snd** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：∀ {q : ℕ} (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).2 = 0
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofNat_snd (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : X q).snd = 0 :=
  rfl
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroupWithOne (X q) :=
  { (inferInstance : Monoid (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : NatCast (X q)) with
    natCast_zero := by ext <;> simp
    natCast_succ := fun _ ↦ by ext <;> simp
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun n => by ext <;> simp }
/-
**LucasLehmer.X.left_distrib** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：left_distrib (x y z : X q) : x * (y + z) = x * y + x * z
参数：x y z : X q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LucasLehmer.X.ext`：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem left_distrib (x y z : X q) : x * (y + z) = x * y + x * z := by
  ext <;> dsimp <;> ring
/-
**LucasLehmer.X.right_distrib** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：right_distrib (x y z : X q) : (x + y) * z = x * z + y * z
参数：x y z : X q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LucasLehmer.X.ext`：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;> dsimp <;> ring
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring (X q) :=
  { (inferInstance : AddGroupWithOne (X q)), (inferInstance : AddCommGroup (X q)),
      (inferInstance : Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ ↦ by ext <;> simp
    zero_mul := fun _ ↦ by ext <;> simp }
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (X q) :=
  { (inferInstance : Ring (X q)) with
    mul_comm := fun _ _ ↦ by ext <;> dsimp <;> ring }
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact (1 < (q : ℕ))] : Nontrivial (X q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

@[simp]
/-
**LucasLehmer.X.fst_intCast** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：fst_intCast (n : Int) : (n : X q).fst = (n : ZMod q)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_intCast (n : ℤ) : (n : X q).fst = (n : ZMod q) :=
  rfl

@[simp]
/-
**LucasLehmer.X.snd_intCast** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：snd_intCast (n : Int) : (n : X q).snd = (0 : ZMod q)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_intCast (n : ℤ) : (n : X q).snd = (0 : ZMod q) :=
  rfl

@[norm_cast]
/-
**LucasLehmer.X.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：coe_mul (n m : Int) : ((n * m : Int) : X q) = (n : X q) * (m : X q)
参数：n m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LucasLehmer.X.ext`：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) := by ext <;> simp

@[norm_cast]
/-
**LucasLehmer.X.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：coe_natCast (n : Nat) : ((n : Int) : X q) = (n : X q)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LucasLehmer.X.ext`：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_natCast (n : ℕ) : ((n : ℤ) : X q) = (n : X q) := by ext <;> simp

/-- We define `ω = 2 + √3`. -/
/-
**LucasLehmer.X.** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `ω = 2 + √3`.
-/
def ω : X q := (2, 1)

/-- We define `ωb = 2 - √3`, which is the inverse of `ω`. -/
/-
**LucasLehmer.X.** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `ωb = 2 - √3`, which is the inverse of `ω`.
-/
def ωb : X q := (2, -1)

set_option backward.isDefEq.respectTransparency.types false in
/-
**LucasLehmer.X.** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ω_mul_ωb : (ω : X q) * ωb = 1 := by
  dsimp [ω, ωb]
  ext <;> simp; ring
/-
**LucasLehmer.X.** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωb_mul_ω : (ωb : X q) * ω = 1 := by
  rw [mul_comm, ω_mul_ωb]

set_option backward.isDefEq.respectTransparency.types false in
/-- A closed form for the recurrence relation. -/
/-
**LucasLehmer.X.closed_form** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：closed_form (i : Nat) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^
 i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LucasLehmer.X.ext`：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_intCast`：isNat_intCast {R} [Ring R] (n : Int)
 (m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
A closed form for the recurrence relation.
-/
theorem closed_form (i : ℕ) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction i with
  | zero =>
    dsimp [s, ω, ωb]
    ext <;> norm_num
  | succ i ih =>
    calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : ℤ) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by ring
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel_right]
      _ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by rw [← pow_mul, ← pow_mul, _root_.pow_succ]

/-- We define `α = √3`. -/
/-
**LucasLehmer.X.** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `α = √3`.
-/
def α : X q := (0, 1)

set_option backward.isDefEq.respectTransparency.types false in
/-
**LucasLehmer.X.** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma α_sq : (α ^ 2 : X q) = 3 := by
  ext <;> simp [α, sq]

set_option backward.isDefEq.respectTransparency.types false in
/-
**LucasLehmer.X.one_add_** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_add_α_sq : ((1 + α) ^ 2 : X q) = 2 * ω := by
  ext <;> simp [α, ω, sq] <;> norm_num
/-
**LucasLehmer.X.** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma α_pow (i : ℕ) : (α : X q) ^ (2 * i + 1) = 3 ^ i * α := by
  rw [pow_succ, pow_mul, α_sq]

/-! We show that `X q` has characteristic `q`, so that we can apply the binomial theorem. -/

/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We show that `X q` has characteristic `q`, so that we can apply the binomial the
orem.
-/
instance : CharP (X q) q where
  cast_eq_zero_iff x := by
    convert! ZMod.natCast_eq_zero_iff _ _
    exact ⟨congr_arg Prod.fst, fun hx ↦ ext hx (by simp)⟩
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (ZMod ↑q) (X q) where
  coe := ZMod.castHom dvd_rfl (X q)

/-- If `3` is not a square mod `q` then `(1 + α) ^ q = 1 - α` -/
/-
**LucasLehmer.X.one_add_** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `3` is not a square mod `q` then `(1 + α) ^ q = 1 - α`
-/
lemma one_add_α_pow_q [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (1 + α : X q) ^ q = 1 - α := by
  obtain ⟨k, rfl⟩ := odd
  let q := 2 * k + 1
  have : (3 ^ k : ZMod q) = -1 := by
    simpa [leg3, mul_add_div, eq_comm] using legendreSym.eq_pow (2 * k + 1) 3
  rw [add_pow_expChar, α_pow, show (3 : X q) = (3 : ZMod q) by rw [map_ofNat], ← map_pow, this,
    map_neg]
  simp [sub_eq_add_neg]

/-- If `3` is not a square then `(1 + α) ^ (q + 1) = -2`. -/
/-
**LucasLehmer.X.one_add_** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `3` is not a square then `(1 + α) ^ (q + 1) = -2`.
-/
lemma one_add_α_pow_q_succ [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (1 + α : X q) ^ (q + 1) = -2 := by
  rw [pow_succ, one_add_α_pow_q odd leg3, mul_comm, ← _root_.sq_sub_sq, α_sq]
  norm_num

/-- If `3` is not a square then `(2 * ω) ^ ((q + 1) / 2) = -2`. -/
/-
**LucasLehmer.X.two_mul_** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `3` is not a square then `(2 * ω) ^ ((q + 1) / 2) = -2`.
-/
lemma two_mul_ω_pow [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (2 * ω : X q) ^ ((q + 1) / 2) = -2 := by
  rw [← one_add_α_sq, ← pow_mul]
  have : 2 * ((q + 1) / 2) = q + 1 := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    exact Odd.add_one odd
  rw [this, one_add_α_pow_q_succ odd leg3]

/-- If 3 is not a square and 2 is square then $\omega^{(q+1)/2}=-1$. -/
/-
**LucasLehmer.X.pow_** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If 3 is not a square and 2 is square then $\omega^{(q+1)/2}=-1$.
-/
lemma pow_ω [Fact q.Prime] (odd : Odd q)
    (leg3 : legendreSym q 3 = -1)
    (leg2 : legendreSym q 2 = 1) :
    (ω : X q) ^ ((q + 1) / 2) = -1 := by
  have pow2 : (2 : ZMod q) ^ ((q + 1) / 2) = 2 := by
    obtain ⟨_, _⟩ := odd
    rw [(by lia : (q + 1) / 2 = q / 2 + 1), pow_succ]
    have leg := legendreSym.eq_pow q 2
    have : (2 : ZMod q) = ((2 : ℤ) : ZMod q) := by norm_cast
    rw [this, ← leg, leg2]
    ring
  have := two_mul_ω_pow odd leg3
  rw [mul_pow] at this
  have coe : (2 : X q) = (2 : ZMod q) := by rw [map_ofNat]
  rw [coe, ← map_pow, pow2, ← coe,
    (by ring : (-2 : X q) = 2 * -1)] at this
  refine (IsUnit.of_mul_eq_one (M := X q) ↑((q + 1) / 2) ?_).mul_left_cancel this
  norm_cast
  simp [Nat.mul_div_cancel' odd.add_one.two_dvd]

/-- The final evaluation needed to establish the Lucas-Lehmer necessity. -/
/-
**LucasLehmer.X.** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The final evaluation needed to establish the Lucas-Lehmer necessity.
-/
lemma ω_pow_trace [Fact q.Prime] (odd : Odd q)
    (leg3 : legendreSym q 3 = -1)
    (leg2 : legendreSym q 2 = 1)
    (hq4 : 4 ∣ q + 1) :
    (ω : X q) ^ ((q + 1) / 4) + ωb ^ ((q + 1) / 4) = 0 := by
  have : (ω : X q) ^ ((q + 1) / 2) * ωb ^ ((q + 1) / 4) = -ωb ^ ((q + 1) / 4) := by
    rw [pow_ω odd leg3 leg2]
    ring
  have div4 : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by rcases hq4 with ⟨k, hk⟩; lia
  rw [div4, pow_add, mul_assoc, ← mul_pow, ω_mul_ωb, one_pow, mul_one] at this
  rw [this]
  ring

variable [NeZero q]
/-
**LucasLehmer.X.** 是 Mathlib 中的一个实例，位于命名空间 `LucasLehmer.X`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype (X q) := inferInstanceAs <| Fintype (ZMod q × ZMod q)

/-- The cardinality of `X` is `q^2`. -/
/-
**LucasLehmer.X.card_eq** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.X`。
形式化陈述：card_eq : Fintype.card (X q) = q ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
The cardinality of `X` is `q^2`.
-/
theorem card_eq : Fintype.card (X q) = q ^ 2 := by
  change Fintype.card (ZMod q × ZMod q) = q ^ 2
  rw [Fintype.card_prod, ZMod.card q, sq]

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
nonrec theorem card_units_lt (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : ℕ)) := ⟨w⟩
  convert! card_units_lt (X q)
  rw [card_eq]

end X

open X

/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/

/-- If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 2. -/
/-
**LucasLehmer.two_lt_q** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：two_lt_q (p' : Nat) : 2 < q (p' + 2)
参数：p' : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_mersenne`：one_lt_mersenne {p : Nat} : 1 < mersenne p ↔ 1 < p
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.minFac_eq_two_iff`：minFac_eq_two_iff (n : Nat) : minFac n = 2 ↔ 2 ∣ 
n
· 使用定理 `mersenne.eq_1`：∀ (p : ℕ), mersenne p = 2 ^ p - 1
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用引理 `Nat.two_not_dvd_two_mul_sub_one`：two_not_dvd_two_mul_sub_one {n} : 0 < n
 -> ¬2 ∣ 2 * n - 1
· 使用定理 `Nat.one_le_two_pow`：∀ {n : ℕ}, 1 ≤ 2 ^ n

--- 原说明 ---
If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 
2.
-/
theorem two_lt_q (p' : ℕ) : 2 < q (p' + 2) := by
  refine (minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · exact le_add_left _ _
  · rw [Ne, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one Nat.one_le_two_pow
/-
**LucasLehmer.** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ω_pow_formula (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    ∃ k : ℤ,
      (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) =
        k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  replace h : 2 ^ (p' + 2) - 1 ∣ s p' := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  obtain ⟨k, h⟩ := h
  use k
  replace h := congr_arg (fun n : ℤ => (n : X (q (p' + 2)))) h
  rw [closed_form] at h
  replace h := congr_arg (fun x => ω ^ 2 ^ p' * x) h
  have t : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  rw [mul_add, ← pow_add ω, t, ← mul_pow ω ωb (2 ^ p'), ω_mul_ωb, one_pow] at h
  rw [mul_comm, coe_mul] at h
  rw [mul_comm _ (k : X (q (p' + 2)))] at h
  replace h := eq_sub_of_add_eq h
  have : 1 ≤ 2 ^ (p' + 2) := Nat.one_le_pow _ _ (by decide)
  exact mod_cast h

set_option backward.isDefEq.respectTransparency false in
/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
/-
**LucasLehmer.mersenne_coe_X** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：mersenne_coe_X (p : Nat) : (mersenne p : X (q p)) = 0
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LucasLehmer.X.ext`：ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`.
-/
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [mersenne, q, ZMod.natCast_eq_zero_iff, Nat.minFac_dvd, -pow_pos]
/-
**LucasLehmer.** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  obtain ⟨k, w⟩ := ω_pow_formula p' h
  rw [mersenne_coe_X] at w
  simpa using w
/-
**LucasLehmer.** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ω_pow_eq_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp

/-- `ω` as an element of the group of units. -/
/-
**LucasLehmer.** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ω` as an element of the group of units.
-/
def ωUnit (p : ℕ) : Units (X (q p)) where
  val := ω
  inv := ωb
  val_inv := ω_mul_ωb
  inv_val := ωb_mul_ω

@[simp]
/-
**LucasLehmer.** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωUnit_coe (p : ℕ) : (ωUnit p : X (q p)) = ω :=
  rfl

/-- The order of `ω` in the unit group is exactly `2^p`. -/
/-
**LucasLehmer.order_** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of `ω` in the unit group is exactly `2^p`.
-/
theorem order_ω (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · exact Nat.prime_two
  · intro o
    have ω_pow :=
      congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) → X (q (p' + 2))) <|
        orderOf_dvd_iff_pow_eq_one.1 o
    have h : (1 : ZMod (q (p' + 2))) = -1 :=
      congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    have : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q _⟩
    apply ZMod.neg_one_ne_one h.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact ω_pow_eq_one p' h
/-
**LucasLehmer.order_ineq** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer`。
形式化陈述：order_ineq (p' : Nat) (h : lucasLehmerResidue (p' + 2) = 0) : 2 ^ (p' + 2)
 < (q (p' + 2) : Nat) ^ 2
参数：p' : Nat；h : lucasLehmerResidue (p' + 2) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.pnat`：∀ {a : ℕ+}, NeZero ↑a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LucasLehmer.order_ω`：order_ω (p' : Nat) (h : lucasLehmerResidue (p' + 2)
 = 0) : orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2)
· 使用定理 `orderOf_le_card_univ`：orderOf_le_card_univ [Fintype G] : orderOf x <= Fi
ntype.card G
· 使用定理 `LucasLehmer.X.card_units_lt`：∀ {q : ℕ} [inst : NeZero q], 1 < q → Fintyp
e.card (LucasLehmer.X q)ˣ < q ^ 2
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用定理 `LucasLehmer.two_lt_q`：two_lt_q (p' : Nat) : 2 < q (p' + 2)
-/
theorem order_ineq (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    2 ^ (p' + 2) < (q (p' + 2) : ℕ) ^ 2 :=
  calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ ≤ Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < q (p' + 2) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))

end LucasLehmer

export LucasLehmer (LucasLehmerTest lucasLehmerResidue)

open LucasLehmer

/-- **Lucas–Lehmer primality test**: sufficiency direction. -/
@[wikidata Q1138992]
/-
**lucas_lehmer_sufficiency** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lucas_lehmer_sufficiency (p : Nat) (w : 1 < p) : LucasLehmerTest p -> (mer
senne p).Prime
参数：p : Nat；w : 1 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LucasLehmer.order_ineq`：order_ineq (p' : Nat) (h : lucasLehmerResidue (p
' + 2) = 0) : 2 ^ (p' + 2) < (q (p' + 2) : Nat) ^ 2
· 使用定理 `Nat.minFac_sq_le_self`：minFac_sq_le_self {n : Nat} (w : 0 < n) (h : ¬Pri
me n) : minFac n ^ 2 <= n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mersenne_pos`：∀ {p : ℕ}, 0 < mersenne p ↔ 0 < p
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Lucas–Lehmer primality test**: sufficiency direction.
-/
theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) : LucasLehmerTest p → (mersenne p).Prime := by
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  exact not_lt_of_ge (Nat.sub_le _ _) h

set_option backward.isDefEq.respectTransparency false in
/-- If `2^p - 1` is prime then the Lucas-Lehmer test holds, `s (p - 2) % (2^p - 1) = 0`. -/
/-
**lucas_lehmer_necessity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lucas_lehmer_necessity (p : Nat) (w : 3 <= p) (hp : (mersenne p).Prime) : 
LucasLehmerTest p
参数：p : Nat；w : 3 <= p；hp : (mersenne p).Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LucasLehmer.sZMod_eq_s`：sZMod_eq_s (p' : Nat) (i : Nat) : sZMod (p' + 2)
 i = (s i : ZMod (2 ^ (p' + 2) - 1))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LucasLehmer.X.fst_intCast`：fst_intCast (n : Int) : (n : X q).fst = (n : 
ZMod q)
· 使用定理 `LucasLehmer.X.closed_form`：closed_form (i : Nat) : (s i : X q) = (ω : X 
q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `LucasLehmer.X.ω_pow_trace`：ω_pow_trace [Fact q.Prime] (odd : Odd q) (leg
3 : legendreSym q 3 = -1) (leg2 : legendreSym q 2 = 1) (hq4 : 4 ∣ q + 1) : (ω : 
X q) ^ ((q + 1)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `legendreSym_mersenne_three`：legendreSym_mersenne_three {p : Nat} [Fact (
mersenne p).Prime] (hp : 3 <= p) (odd : Odd p) : legendreSym (mersenne p) 3 = -1
· 使用定理 `Nat.Prime.odd_of_ne_two`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
· 使用引理 `Nat.Prime.of_mersenne`：Nat.Prime.of_mersenne {p : Nat} (h : (mersenne p)
.Prime) : Nat.Prime p
· 使用引理 `legendreSym_mersenne_two`：legendreSym_mersenne_two {p : Nat} [Fact (mers
enne p).Prime] (hp : 3 <= p) : legendreSym (mersenne p) 2 = 1
· 使用定理 `succ_mersenne`：succ_mersenne (k : Nat) : mersenne k + 1 = 2 ^ k
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `2^p - 1` is prime then the Lucas-Lehmer test holds, `s (p - 2) % (2^p - 1) =
 0`.
-/
theorem lucas_lehmer_necessity (p : ℕ) (w : 3 ≤ p) (hp : (mersenne p).Prime) :
    LucasLehmerTest p := by
  have : Fact (mersenne p).Prime := ⟨‹_›⟩
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by lia
  dsimp [LucasLehmerTest, lucasLehmerResidue]
  rw [sZMod_eq_s p', ← X.fst_intCast, X.closed_form, add_tsub_cancel_right]
  have := X.ω_pow_trace (q := mersenne (p' + 2)) (by simp)
    (legendreSym_mersenne_three w <| hp.of_mersenne.odd_of_ne_two (by lia))
    (legendreSym_mersenne_two w) (by simp [pow_add])
  rw [succ_mersenne, pow_add, show 2 ^ 2 = 4 by norm_num, mul_div_cancel_right₀ _ (by norm_num)]
    at this
  simp [this]

namespace LucasLehmer

/-!
### `norm_num` extension

Next we define a `norm_num` extension that calculates `LucasLehmerTest p` for `1 < p`.
It makes use of a version of `sMod` that is specifically written to be reducible by the
Lean 4 kernel, which has the capability of efficiently reducing natural number expressions.
With this reduction in hand, it's a simple matter of applying the lemma
`LucasLehmer.residue_eq_zero_iff_sMod_eq_zero`.

See `Archive/Examples/MersennePrimes.lean` for certifications of all Mersenne primes
up through `mersenne 4423`.
-/

namespace norm_num_ext
open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/-- Version of `sMod` that is `ℕ`-valued. One should have `q = 2 ^ p - 1`.
This can be reduced by the kernel. -/
/-
**LucasLehmer.norm_num_ext.sModNat** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer.norm_n
um_ext`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `sMod` that is `ℕ`-valued. One should have `q = 2 ^ p - 1`.
This can be reduced by the kernel.
-/
def sModNat (q : ℕ) : ℕ → ℕ
  | 0 => 4 % q
  | i + 1 => (sModNat q i ^ 2 + (q - 2)) % q
/-
**LucasLehmer.norm_num_ext.sModNat_eq_sMod** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehme
r.norm_num_ext`。
形式化陈述：sModNat_eq_sMod (p k : Nat) (hp : 2 <= p) : (sModNat (2 ^ p - 1) k : Int) 
= sMod p k
参数：p k : Nat；hp : 2 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
-/
theorem sModNat_eq_sMod (p k : ℕ) (hp : 2 ≤ p) : (sModNat (2 ^ p - 1) k : ℤ) = sMod p k := by
  induction k with
  | zero => grind [sModNat, sMod]
  | succ =>
    have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by lia) hp
    grind [sModNat, sMod, Int.emod_eq_add_self_emod]

/-- Tail-recursive version of `sModNat`. -/
meta def sModNatTR (q k : ℕ) : ℕ :=
  go k (4 % q)
where
  /-- Helper function for `sMod''`. -/
  go : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => go n ((acc ^ 2 + (q - 2)) % q)
termination_by structural x => x

/--
Generalization of `sModNat` with arbitrary base case,
useful for proving `sModNatTR` and `sModNat` agree.
-/
/-
**LucasLehmer.norm_num_ext.sModNatAux** 是 Mathlib 中的一个定义，位于命名空间 `LucasLehmer.nor
m_num_ext`。
形式化陈述：ℕ → ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generalization of `sModNat` with arbitrary base case,
useful for proving `sModNatTR` and `sModNat` agree.
-/
def sModNatAux (b q : ℕ) : ℕ → ℕ
  | 0 => b
  | i + 1 => (sModNatAux b q i ^ 2 + (q - 2)) % q
/-
**LucasLehmer.norm_num_ext.sModNatAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `LucasLehmer.
norm_num_ext`。
形式化陈述：sModNatAux_eq (q k : Nat) : sModNatAux (4 % q) q k = sModNat q k
参数：q k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LucasLehmer.norm_num_ext.sModNatAux.eq_2`：∀ (b q i : ℕ),   LucasLehmer.n
orm_num_ext.sModNatAux b q i.succ = (LucasLehmer.norm_num_ext.sModNatAux b q i ^
 2 + (q - 2)) % q
· 使用定理 `LucasLehmer.norm_num_ext.sModNat.eq_2`：∀ (q i : ℕ), LucasLehmer.norm_num
_ext.sModNat q i.succ = (LucasLehmer.norm_num_ext.sModNat q i ^ 2 + (q - 2)) % q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sModNatAux_eq (q k : ℕ) : sModNatAux (4 % q) q k = sModNat q k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sModNatAux, ih, sModNat, ← ih]

@[deprecated (since := "2026-06-06")] alias sModNat_aux := sModNatAux
@[deprecated (since := "2026-06-06")] alias sModNat_aux_eq := sModNatAux_eq
/-
**LucasLehmer.norm_num_ext.sModNatTR_eq_sModNat** 是 Mathlib 中的一个定理，位于命名空间 `Lucas
Lehmer.norm_num_ext`。
形式化陈述：sModNatTR_eq_sModNat (q i : Nat) : sModNatTR q i = sModNat q i
参数：q i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.LucasLehmer.0.LucasLehmer.norm_num_ext.sMo
dNatTR.eq_1`：∀ (q k : ℕ), LucasLehmer.norm_num_ext.sModNatTR q k = LucasLehmer.n
orm_num_ext.sModNatTR.go✝ q k (4 % q)
· 使用定理 `_private.Mathlib.NumberTheory.LucasLehmer.0.LucasLehmer.norm_num_ext.sMo
dNatTR_eq_sModNat.helper`：∀ (b q k : ℕ), LucasLehmer.norm_num_ext.sModNatTR.go✝ 
q k b = LucasLehmer.norm_num_ext.sModNatAux b q k
· 使用定理 `LucasLehmer.norm_num_ext.sModNatAux_eq`：sModNatAux_eq (q k : Nat) : sMod
NatAux (4 % q) q k = sModNat q k
-/
theorem sModNatTR_eq_sModNat (q i : ℕ) : sModNatTR q i = sModNat q i := by
  rw [sModNatTR, helper, sModNatAux_eq]
where
  helper b q k : sModNatTR.go q k b = sModNatAux b q k := by
    induction k generalizing b with
    | zero => rfl
    | succ k ih =>
      rw [sModNatTR.go, ih, sModNatAux]
      clear ih
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [sModNatAux, ih, sModNatAux]
/-
**LucasLehmer.norm_num_ext.testTrueHelper** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehmer
.norm_num_ext`。
形式化陈述：testTrueHelper (p : Nat) (hp : Nat.blt 1 p = true) (h : sModNatTR (2 ^ p -
 1) (p - 2) = 0) : LucasLehmerTest p
参数：p : Nat；hp : Nat.blt 1 p = true；h : sModNatTR (2 ^ p - 1) (p - 2) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LucasLehmer.LucasLehmerTest.eq_1`：∀ (p : ℕ), LucasLehmerTest p = (lucasL
ehmerResidue p = 0)
· 使用定理 `LucasLehmer.residue_eq_zero_iff_sMod_eq_zero`：residue_eq_zero_iff_sMod_e
q_zero (p : Nat) (w : 1 < p) : lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LucasLehmer.norm_num_ext.sModNat_eq_sMod`：sModNat_eq_sMod (p k : Nat) (h
p : 2 <= p) : (sModNat (2 ^ p - 1) k : Int) = sMod p k
· 使用定理 `LucasLehmer.norm_num_ext.sModNatTR_eq_sModNat`：sModNatTR_eq_sModNat (q i
 : Nat) : sModNatTR q i = sModNat q i
-/
lemma testTrueHelper (p : ℕ) (hp : Nat.blt 1 p = true) (h : sModNatTR (2 ^ p - 1) (p - 2) = 0) :
    LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sModNat_eq_sMod p _ hp,
    ← sModNatTR_eq_sModNat, h]
  rfl
/-
**LucasLehmer.norm_num_ext.testFalseHelper** 是 Mathlib 中的一个引理，位于命名空间 `LucasLehme
r.norm_num_ext`。
形式化陈述：testFalseHelper (p : Nat) (hp : Nat.blt 1 p = true) (h : Nat.ble 1 (sModNa
tTR (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p
参数：p : Nat；hp : Nat.blt 1 p = true；h : Nat.ble 1 (sModNatTR (2 ^ p - 1) (p - 2))
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LucasLehmer.LucasLehmerTest.eq_1`：∀ (p : ℕ), LucasLehmerTest p = (lucasL
ehmerResidue p = 0)
· 使用定理 `LucasLehmer.residue_eq_zero_iff_sMod_eq_zero`：residue_eq_zero_iff_sMod_e
q_zero (p : Nat) (w : 1 < p) : lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LucasLehmer.norm_num_ext.sModNat_eq_sMod`：sModNat_eq_sMod (p k : Nat) (h
p : 2 <= p) : (sModNat (2 ^ p - 1) k : Int) = sMod p k
· 使用定理 `LucasLehmer.norm_num_ext.sModNatTR_eq_sModNat`：sModNatTR_eq_sModNat (q i
 : Nat) : sModNatTR q i = sModNat q i
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Nat.ble_eq`：∀ {x y : ℕ}, (x.ble y = true) = (x ≤ y)
-/
lemma testFalseHelper (p : ℕ) (hp : Nat.blt 1 p = true)
    (h : Nat.ble 1 (sModNatTR (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq, Nat.succ_le_iff, Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sModNat_eq_sMod p _ hp,
    ← sModNatTR_eq_sModNat]
  simpa using h
/-
**LucasLehmer.norm_num_ext.isNat_lucasLehmerTest** 是 Mathlib 中的一个定理，位于命名空间 `Luca
sLehmer.norm_num_ext`。
形式化陈述：∀ {p np : ℕ}, Mathlib.Meta.NormNum.IsNat p np → LucasLehmerTest np → Lucas
LehmerTest p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_lucasLehmerTest : {p np : ℕ} →
    IsNat p np → LucasLehmerTest np → LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h
/-
**LucasLehmer.norm_num_ext.isNat_not_lucasLehmerTest** 是 Mathlib 中的一个定理，位于命名空间 `
LucasLehmer.norm_num_ext`。
形式化陈述：∀ {p np : ℕ}, Mathlib.Meta.NormNum.IsNat p np → ¬LucasLehmerTest np → ¬Luc
asLehmerTest p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat_not_lucasLehmerTest : {p np : ℕ} →
    IsNat p np → ¬ LucasLehmerTest np → ¬ LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h

/-- Calculate `LucasLehmer.LucasLehmerTest p` for `2 ≤ p` by using kernel reduction for the
`sMod'` function. -/
@[norm_num LucasLehmer.LucasLehmerTest (_ : ℕ)]
meta def evalLucasLehmerTest : NormNumExt where eval {_ _} e := do
  let .app _ (p : Q(ℕ)) ← Meta.whnfR e | failure
  let ⟨ep, hp⟩ ← deriveNat p _
  let np := ep.natLit!
  unless 1 < np do
    failure
  haveI' h1ltp : Nat.blt 1 $ep =Q true := ⟨⟩
  if sModNatTR (2 ^ np - 1) (np - 2) = 0 then
    haveI' hs : sModNatTR (2 ^ $ep - 1) ($ep - 2) =Q 0 := ⟨⟩
    have pf : Q(LucasLehmerTest $ep) := q(testTrueHelper $ep $h1ltp $hs)
    have pf' : Q(LucasLehmerTest $p) := q(isNat_lucasLehmerTest $hp $pf)
    return .isTrue pf'
  else
    haveI' hs : Nat.ble 1 (sModNatTR (2 ^ $ep - 1) ($ep - 2)) =Q true := ⟨⟩
    have pf : Q(¬ LucasLehmerTest $ep) := q(testFalseHelper $ep $h1ltp $hs)
    have pf' : Q(¬ LucasLehmerTest $p) := q(isNat_not_lucasLehmerTest $hp $pf)
    return .isFalse pf'

end norm_num_ext

end LucasLehmer

/-!
This implementation works successfully to prove `(2^4423 - 1).Prime`,
and all the Mersenne primes up to this point appear in `Archive/Examples/MersennePrimes.lean`.
These can be calculated nearly instantly, and `(2^9689 - 1).Prime` only fails due to deep
recursion.

(Note by kmill: the following notes were for the Lean 3 version. They seem like they could still
be useful, so I'm leaving them here.)

There's still low-hanging fruit available to do faster computations
based on the formula
```
n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
```
and the fact that `% 2^p` and `/ 2^p` can be very efficient on the binary representation.
Someone should do this, too!
-/

/-
**modEq_mersenne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modEq_mersenne (n k : Nat) : k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1]
参数：n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `Nat.ModEq.add_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a + c ≡ b + 
c [MOD n]
· 使用定理 `Nat.ModEq.mul_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * 
c [MOD n]
· 使用引理 `Nat.modEq_sub`：modEq_sub (h : b <= a) : a ≡ b [MOD a - b]
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
This implementation works successfully to prove `(2^4423 - 1).Prime`,
and all the Mersenne primes up to this point appear in `Archive/Examples/Mersenn
ePrimes.lean`.
These can be calculated nearly instantly, and `(2^9689 - 1).Prime` only fails du
e to deep
recursion.

(Note by kmill: the following notes were for the Lean 3 version. They seem like 
they could still
be useful, so I'm leaving them here.)

There's still low-hanging fruit available to do faster computations
based on the formula
```
n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
```
and the fact that `% 2^p` and `/ 2^p` can be very efficient on the binary repres
entation.
Someone should do this, too!
-/
theorem modEq_mersenne (n k : ℕ) : k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1] :=
  -- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
  calc
    k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := (Nat.div_add_mod k (2 ^ n)).symm
    _ ≡ 1 * (k / 2 ^ n) + k % 2 ^ n [MOD 2 ^ n - 1] :=
      ((Nat.modEq_sub <| Nat.succ_le_of_lt <| pow_pos zero_lt_two _).mul_right _).add_right _
    _ = k / 2 ^ n + k % 2 ^ n := by rw [one_mul]

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
