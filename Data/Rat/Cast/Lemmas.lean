/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Nonneg.Field
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic.Positivity.Basic

/-!
# Some exiled lemmas about casting

These lemmas have been removed from `Mathlib/Data/Rat/Cast/Defs.lean`
to avoiding needing to import `Mathlib/Algebra/Field/Basic.lean` there.

In fact, these lemmas don't appear to be used anywhere in Mathlib,
so perhaps this file can simply be deleted.
-/

public section

namespace Rat

variable {α : Type*} [DivisionRing α]

-- Note that this is more general than `(Rat.castHom α).map_pow`.
@[simp, norm_cast]
/-
**Rat.cast_pow** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α)
参数：p : Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `Rat.den_pow`：∀ (q : ℚ) (n : ℕ), (q ^ n).den = q.den ^ n
· 使用定理 `Rat.num_pow`：∀ (q : ℚ) (n : ℕ), (q ^ n).num = q.num ^ n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Int.cast_commute`：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : 
α), Commute (↑n) a
-/
lemma cast_pow (p : ℚ) (n : ℕ) : ↑(p ^ n) = (p ^ n : α) := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Int.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Int.cast_commute _ _).mul_pow, ← div_eq_mul_inv]

@[simp]
/-
**Rat.cast_inv_nat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_inv_nat (n : Nat) : ((n⁻¹ : Rat) : α) = (n : α)⁻¹
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `Rat.inv_natCast_num`：inv_natCast_num (a : Nat) : (a : Rat)⁻¹.num = Int.s
ign a
· 使用定理 `Rat.inv_natCast_den`：inv_natCast_den (a : Nat) : (a : Rat)⁻¹.den = if a 
= 0 then 1 else a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
· 使用定理 `Int.ofNat_succ_pos`：∀ (n : ℕ), 0 < ↑n.succ
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  rcases n with - | n
  · simp
  rw [cast_def, inv_natCast_num, inv_natCast_den, if_neg n.succ_ne_zero,
    Int.sign_eq_one_of_pos (Int.ofNat_succ_pos n), Int.cast_one, one_div]

@[simp]
/-
**Rat.cast_inv_int** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_inv_int (n : Int) : ((n⁻¹ : Rat) : α) = (n : α)⁻¹
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.cast_inv_nat`：cast_inv_nat (n : Nat) : ((n⁻¹ : Rat) : α) = (n : α)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
-/
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  rcases n with n | n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]
/-
**Rat.cast_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_nnratCast {K} [DivisionRing K] (q : Rat>=0) : ((q : Rat) : K) = (q : 
K)
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `Rat.num_div_eq_of_coprime`：num_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : (a / b : Rat).num = a
· 使用定理 `NNRat.den_pos`：∀ (q : ℚ≥0), 0 < q.den
· 使用引理 `NNRat.coprime_num_den`：coprime_num_den (q : Rat>=0) : q.num.Coprime q.de
n
· 使用定理 `Rat.den_div_eq_of_coprime`：den_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : ((a / b : Rat).den : Int) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem cast_nnratCast {K} [DivisionRing K] (q : ℚ≥0) :
    ((q : ℚ) : K) = (q : K) := by
  rw [Rat.cast_def, NNRat.cast_def, NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Int.natCast_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn, hd, Int.cast_natCast]

/-- Casting a scientific literal via `ℚ` is the same as casting directly. -/
@[simp, norm_cast]
/-
**Rat.cast_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_ofScientific {K} [DivisionRing K] (m : Nat) (s : Bool) (e : Nat) : (O
fScientific.ofScientific m s e : Rat) = (OfScientific.ofScientific m s e : K)
参数：m : Nat；s : Bool；e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_ofScientific`：∀ {K : Type u_1} [inst : NNRatCast K] (m : ℕ) (
s : Bool) (e : ℕ),   ↑(OfScientific.ofScientific m s e) = OfScientific.ofScienti
fic m s e
· 使用定理 `Rat.cast_nnratCast`：cast_nnratCast {K} [DivisionRing K] (q : Rat>=0) : (
(q : Rat) : K) = (q : K)

--- 原说明 ---
Casting a scientific literal via `ℚ` is the same as casting directly.
-/
theorem cast_ofScientific {K} [DivisionRing K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ) = (OfScientific.ofScientific m s e : K) := by
  rw [← NNRat.cast_ofScientific (K := K), ← NNRat.cast_ofScientific, cast_nnratCast]

end Rat

namespace NNRat

@[simp, norm_cast]
/-
**NNRat.cast_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_pow {K} [DivisionSemiring K] (q : Rat>=0) (n : Nat) : NNRat.cast (q ^
 n) = (NNRat.cast q : K) ^ n
参数：q : Rat>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `NNRat.den_pow`：∀ (q : ℚ≥0) (n : ℕ), (q ^ n).den = q.den ^ n
· 使用定理 `NNRat.num_pow`：∀ (q : ℚ≥0) (n : ℕ), (q ^ n).num = q.num ^ n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
-/
theorem cast_pow {K} [DivisionSemiring K] (q : ℚ≥0) (n : ℕ) :
    NNRat.cast (q ^ n) = (NNRat.cast q : K) ^ n := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Nat.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Nat.cast_commute _ _).mul_pow, ← div_eq_mul_inv]
/-
**NNRat.cast_zpow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_zpow_of_ne_zero {K} [DivisionSemiring K] (q : Rat>=0) (z : Int) (hq :
 (q.num : K) != 0) : NNRat.cast (q ^ z) = (NNRat.cast q : K) ^ z
参数：q : Rat>=0；z : Int；hq : (q.num : K) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `NNRat.cast_pow`：cast_pow {K} [DivisionSemiring K] (q : Rat>=0) (n : Nat)
 : NNRat.cast (q ^ n) = (NNRat.cast q : K) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NNRat.cast_inv_of_ne_zero`：cast_inv_of_ne_zero (hq : (q.num : α) != 0) :
 (q⁻¹ : Rat>=0) = (q⁻¹ : α)
-/
theorem cast_zpow_of_ne_zero {K} [DivisionSemiring K] (q : ℚ≥0) (z : ℤ) (hq : (q.num : K) ≠ 0) :
    NNRat.cast (q ^ z) = (NNRat.cast q : K) ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp
  · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow]
    congr
    rw [cast_inv_of_ne_zero hq]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**NNRat.cast_mk** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_mk {K} [DivisionRing K] (q : Rat) (h : 0 <= q) : (NNRat.cast ⟨q, h⟩ :
 K) = (q : K)
参数：q : Rat；h : 0 <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
-/
theorem cast_mk {K} [DivisionRing K] (q : ℚ) (h : 0 ≤ q) :
    (NNRat.cast ⟨q, h⟩ : K) = (q : K) := by
  simp only [NNRat.cast_def, NNRat.num_mk, Nat.cast_natAbs, NNRat.den_mk, Rat.cast_def]
  rw [abs_of_nonneg (by simpa)]

open OfScientific in
/-
**NNRat.Nonneg.coe_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `NNRat.Nonneg`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : LinearOrder K] [inst_2 : IsStr
ictOrderedRing K] (m : ℕ) (s : Bool) (e : ℕ),   ↑(OfScientific.ofScientific m s 
e) = OfScientific.ofScientific m s e
参数：m : ℕ；s : Bool；e : ℕ；OfScientific.ofScientific m s e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonneg.coe_ofScientific {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (s : Bool) (e : ℕ) :
    (ofScientific m s e : {x : K // 0 ≤ x}).val = ofScientific m s e := rfl

end NNRat

