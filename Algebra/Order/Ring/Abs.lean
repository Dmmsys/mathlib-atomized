/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Absolute values in linear ordered rings.
-/

@[expose] public section


variable {α : Type*}

section LinearOrderedAddCommGroup
variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

/-
**mabs_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : LinearOrder α] [IsOrderedM
onoid α] (n : ℤ) (a : α),   |a ^ n|ₘ = |a|ₘ ^ |n|
参数：n : ℤ；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `mabs_pow`：∀ {G : Type u_1} [inst : CommGroup G] [inst_1 : LinearOrder G]
 [IsOrderedMonoid G] (n : ℕ) (a : G), |a ^ n|ₘ = |a|ₘ ^ n
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
@[to_additive] lemma mabs_zpow (n : ℤ) (a : α) : |a ^ n|ₘ = |a|ₘ ^ |n| := by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [mabs_pow, zpow_natCast, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← mabs_inv, ← zpow_neg, ← abs_neg, h, zpow_natCast, Nat.abs_cast, zpow_natCast]
    exact mabs_pow m _

end LinearOrderedAddCommGroup

/-
**odd_abs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：odd_abs [LinearOrder α] [Ring α] {a : α} : Odd (abs a) ↔ Odd a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma odd_abs [LinearOrder α] [Ring α] {a : α} : Odd (abs a) ↔ Odd a := by
  rcases abs_choice a with h | h <;> simp only [h, odd_neg]

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

/-
**abs_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOrderedRing α
], |1| = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
@[simp] lemma abs_one : |(1 : α)| = 1 := abs_of_nonneg zero_le_one
/-
**abs_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_two : |(2 : α)| = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
lemma abs_two : |(2 : α)| = 2 := abs_of_nonneg zero_le_two

@[simp, grind =]
/-
**abs_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_mul (a b : α) : |a * b| = |a| * |b|
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma abs_mul (a b : α) : |a * b| = |a| * |b| := by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, neg_mul, mul_neg, neg_neg, *]

/-- `abs` as a `MonoidWithZeroHom`. -/
/-
**absHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：absHom : α ->*₀ α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|

--- 原说明 ---
`abs` as a `MonoidWithZeroHom`.
-/
def absHom : α →*₀ α where
  toFun := abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[simp, grind =]
/-
**abs_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
lemma abs_pow (a : α) (n : ℕ) : |a ^ n| = |a| ^ n := (absHom.toMonoidHom : α →* α).map_pow _ _
/-
**pow_abs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_abs (a : α) (n : Nat) : |a| ^ n = |a ^ n|
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
-/
lemma pow_abs (a : α) (n : ℕ) : |a| ^ n = |a ^ n| := (abs_pow a n).symm
/-
**Even.pow_abs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n
参数：hn : Even n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
lemma Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n := by
  rw [← abs_pow, abs_eq_self]; exact hn.pow_nonneg _
/-
**pow_abs_two_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_abs_two_mul (a : α) : |a| ^ (2 * n) = a ^ (2 * n)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.pow_abs`：Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
lemma pow_abs_two_mul (a : α) : |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a
/-
**abs_neg_one_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_neg_one_pow (n : Nat) : |(-1 : α) ^ n| = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_abs`：pow_abs (a : α) (n : Nat) : |a| ^ n = |a ^ n|
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma abs_neg_one_pow (n : ℕ) : |(-1 : α) ^ n| = 1 := by rw [← pow_abs, abs_neg, abs_one, one_pow]

omit [IsOrderedRing α] in
/-
**abs_mul_abs_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α), |a| * |
a| = a * a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_by_cases`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder
 α] {a : α} (P : α → Prop), P a → P (-a) → P |a|
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
-/
@[simp] lemma abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
  abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)
/-
**abs_mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_mul_self (a : α) : |a * a| = a * a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_mul_self (a : α) : |a * a| = a * a := by simp

omit [IsOrderedRing α] in
/-
**sq_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α), |a| ^ 2
 = a ^ 2
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
-/
@[simp] lemma sq_abs (a : α) : |a| ^ 2 = a ^ 2 := by simpa only [sq] using abs_mul_abs_self a
/-
**abs_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_sq (x : α) : |x ^ 2| = x ^ 2
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `abs_mul_self`：abs_mul_self (a : α) : |a * a| = a * a
-/
lemma abs_sq (x : α) : |x ^ 2| = x ^ 2 := by simpa only [sq] using abs_mul_self x
/-
**exists_abs_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_abs_lt [Nontrivial α] (a : α) : exists b > 0, |a| < b
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
lemma exists_abs_lt [Nontrivial α] (a : α) : ∃ b > 0, |a| < b :=
  ⟨|a| + 1, lt_of_lt_of_le zero_lt_one <| by simp, lt_add_one |a|⟩

end LinearOrderedRing

section LinearStrictOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

/-
**abs_pow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_pow_eq_one (a : α) (h : n != 0) : |a ^ n| = 1 ↔ |a| = 1
参数：a : α；h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_abs`：pow_abs (a : α) (n : Nat) : |a| ^ n = |a ^ n|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
lemma abs_pow_eq_one (a : α) (h : n ≠ 0) : |a ^ n| = 1 ↔ |a| = 1 := by
  convert! pow_left_inj₀ (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]
/-
**abs_eq_iff_mul_self_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_self_inj`：mul_self_inj [PosMulStrictMono R] [MulPosMono R] {a b : R}
 (h1 : 0 <= a) (h2 : 0 <= b) : a * a = b * b ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm
/-
**abs_lt_iff_mul_self_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `mul_self_lt_mul_self_iff`：mul_self_lt_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a < b ↔ a * a < b * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)
/-
**abs_le_iff_mul_self_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_le_iff_mul_self_le : |a| <= |b| ↔ a * a <= b * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)
/-
**abs_le_one_iff_mul_self_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_le_one_iff_mul_self_le_one : |a| <= 1 ↔ a * a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `abs_le_iff_mul_self_le`：abs_le_iff_mul_self_le : |a| <= |b| ↔ a * a <= b
 * b
-/
lemma abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 := by
  simpa only [abs_one, one_mul] using abs_le_iff_mul_self_le (a := a) (b := 1)
/-
**sq_lt_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用引理 `sq_lt_sq₀`：sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b| := by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)
/-
**sq_lt_sq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_lt_sq' (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2
参数：h1 : -b < a；h2 : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
lemma sq_lt_sq' (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2 :=
  sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))
/-
**sq_le_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用引理 `sq_le_sq₀`：sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <=
 b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma sq_le_sq : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b| := by
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)
/-
**sq_le_sq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_le_sq' (h1 : -b <= a) (h2 : a <= b) : a ^ 2 <= b ^ 2
参数：h1 : -b <= a；h2 : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
lemma sq_le_sq' (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))
/-
**abs_lt_of_sq_lt_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 <= b) : |a| < b
参数：h : a ^ 2 < b ^ 2；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
-/
lemma abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : |a| < b := by
  rwa [← abs_of_nonneg hb, ← sq_lt_sq]
/-
**abs_lt_of_sq_lt_sq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_lt_of_sq_lt_sq' (h : a ^ 2 < b ^ 2) (hb : 0 <= b) : -b < a ∧ a < b
参数：h : a ^ 2 < b ^ 2；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `abs_lt_of_sq_lt_sq`：abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 <= b)
 : |a| < b
-/
lemma abs_lt_of_sq_lt_sq' (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : -b < a ∧ a < b :=
  abs_lt.1 <| abs_lt_of_sq_lt_sq h hb
/-
**abs_le_of_sq_le_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : |a| <= b
参数：h : a ^ 2 <= b ^ 2；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
-/
lemma abs_le_of_sq_le_sq (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  rwa [← abs_of_nonneg hb, ← sq_le_sq]
/-
**le_of_sq_le_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <= b
参数：h : a ^ 2 <= b ^ 2；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用引理 `abs_le_of_sq_le_sq`：abs_le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b
) : |a| <= b
-/
theorem le_of_sq_le_sq (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b :=
  le_abs_self a |>.trans <| abs_le_of_sq_le_sq h hb
/-
**abs_le_of_sq_le_sq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_le_of_sq_le_sq' (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : -b <= a ∧ a <= b
参数：h : a ^ 2 <= b ^ 2；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `abs_le_of_sq_le_sq`：abs_le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b
) : |a| <= b
-/
lemma abs_le_of_sq_le_sq' (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : -b ≤ a ∧ a ≤ b :=
  abs_le.1 <| abs_le_of_sq_le_sq h hb
/-
**sq_eq_sq_iff_abs_eq_abs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_eq_sq_iff_abs_eq_abs (a b : α) : a ^ 2 = b ^ 2 ↔ |a| = |b|
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sq_eq_sq_iff_abs_eq_abs (a b : α) : a ^ 2 = b ^ 2 ↔ |a| = |b| := by
  simp only [le_antisymm_iff, sq_le_sq]
/-
**sq_le_one_iff_abs_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrdered
Ring α] (a : α), a ^ 2 ≤ 1 ↔ |a| ≤ 1
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
-/
@[simp] lemma sq_le_one_iff_abs_le_one (a : α) : a ^ 2 ≤ 1 ↔ |a| ≤ 1 := by
  simpa only [one_pow, abs_one] using sq_le_sq (a := a) (b := 1)
/-
**sq_lt_one_iff_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrdered
Ring α] (a : α), a ^ 2 < 1 ↔ |a| < 1
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
-/
@[simp] lemma sq_lt_one_iff_abs_lt_one (a : α) : a ^ 2 < 1 ↔ |a| < 1 := by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := a) (b := 1)
/-
**one_le_sq_iff_one_le_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrdered
Ring α] (a : α), 1 ≤ a ^ 2 ↔ 1 ≤ |a|
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
-/
@[simp] lemma one_le_sq_iff_one_le_abs (a : α) : 1 ≤ a ^ 2 ↔ 1 ≤ |a| := by
  simpa only [one_pow, abs_one] using sq_le_sq (a := 1) (b := a)
/-
**one_lt_sq_iff_one_lt_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrdered
Ring α] (a : α), 1 < a ^ 2 ↔ 1 < |a|
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
-/
@[simp] lemma one_lt_sq_iff_one_lt_abs (a : α) : 1 < a ^ 2 ↔ 1 < |a| := by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := 1) (b := a)

end LinearStrictOrderedRing

section LinearOrderedCommRing

variable [CommRing α] [LinearOrder α] (a b : α) (n : ℕ)

/-
**abs_sub_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b := by
  rw [abs_mul_abs_self]
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg, mul_one, mul_neg,
    neg_add_rev, neg_neg, add_assoc]
/-
**abs_unit_intCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_unit_intCast [IsOrderedRing α] (a : Intˣ) : |((a : Int) : α)| = 1
参数：a : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
lemma abs_unit_intCast [IsOrderedRing α] (a : ℤˣ) : |((a : ℤ) : α)| = 1 := by
  cases Int.units_eq_one_or a <;> simp_all
/-
**geomSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def geomSum : ℕ → α
  | 0 => 1
  | n + 1 => a * geomSum n + b ^ (n + 1)
/-
**abs_geomSum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem abs_geomSum_le [IsOrderedRing α] : |geomSum a b n| ≤ (n + 1) * max |a| |b| ^ n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  refine (abs_add_le ..).trans ?_
  rw [abs_mul, abs_pow, Nat.cast_succ, add_one_mul]
  refine add_le_add ?_ (pow_le_pow_left₀ (abs_nonneg _) le_sup_right _)
  rw [pow_succ, ← mul_assoc, mul_comm |a|]
  gcongr
  exacts [abs_nonneg _, (abs_nonneg _).trans ih, le_sup_left]

omit [LinearOrder α] in
/-
**pow_sub_pow_eq_sub_mul_geomSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pow_sub_pow_eq_sub_mul_geomSum :
    a ^ (n + 1) - b ^ (n + 1) = (a - b) * geomSum a b n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  rw [geomSum, mul_add, mul_comm a, ← mul_assoc, ← ih,
    sub_mul, sub_mul, ← pow_succ, ← pow_succ', mul_comm, sub_add_sub_cancel]
/-
**abs_pow_sub_pow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_pow_sub_pow_le [IsOrderedRing α] : |a ^ n - b ^ n| <= |a - b| * n * ma
x |a| |b| ^ (n - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.Abs.0.pow_sub_pow_eq_sub_mul_geomSum
`：∀ {α : Type u_1} [inst : CommRing α] (a b : α) (n : ℕ), a ^ (n + 1) - b ^ (n +
 1) = (a - b) * geomSum✝ a b n
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.Abs.0.abs_geomSum_le`：∀ {α : Type u_
1} [inst : CommRing α] [inst_1 : LinearOrder α] (a b : α) (n : ℕ) [IsOrderedRing
 α],   |geomSum✝ a b n| ≤ (↑n + 1) * max |a| |…
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem abs_pow_sub_pow_le [IsOrderedRing α] :
    |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := by
  obtain _ | n := n; · simp
  rw [Nat.add_sub_cancel, pow_sub_pow_eq_sub_mul_geomSum, abs_mul, mul_assoc, Nat.cast_succ]
  gcongr
  · exact abs_nonneg _
  · exact abs_geomSum_le ..

end LinearOrderedCommRing

section

variable [Ring α] [LinearOrder α]

@[simp]
/-
**abs_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b := by
  rcases abs_choice a with h | h <;> simp only [h, neg_dvd]
/-
**abs_dvd_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_dvd_self (a : α) : |a| ∣ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_dvd`：abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem abs_dvd_self (a : α) : |a| ∣ a :=
  (abs_dvd a a).mpr (dvd_refl a)

@[simp]
/-
**dvd_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b := by
  rcases abs_choice b with h | h <;> simp only [h, dvd_neg]
/-
**self_dvd_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_dvd_abs (a : α) : a ∣ |a|
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_abs`：dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem self_dvd_abs (a : α) : a ∣ |a| :=
  (dvd_abs a a).mpr (dvd_refl a)
/-
**abs_dvd_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `abs_dvd`：abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b
· 使用定理 `dvd_abs`：dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b
-/
theorem abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
  (abs_dvd _ _).trans (dvd_abs _ _)

end

open Nat

section LinearOrderedRing
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {n : ℕ}

/-
**pow_eq_pow_iff_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_pow_iff_of_ne_zero (hn : n != 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧
 Even n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_xor_odd`：even_xor_odd (n : Nat) : Xor (Even n) (Odd n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_left_inj₀`：pow_left_inj₀ [MulPosMono M₀] (ha : 0 <= a) (hb : 0 <= b)
 (hn : n != 0) : a ^ n = b ^ n ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Even.pow_abs`：Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Odd.strictMono_pow`：Odd.strictMono_pow (hn : Odd n) : StrictMono fun a :
 R => a ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma pow_eq_pow_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj₀ (abs_nonneg a) (abs_nonneg b) hn, hne.1.pow_abs]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff]
/-
**pow_eq_pow_iff_cases** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_pow_iff_cases : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma pow_eq_pow_iff_cases : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]
/-
**pow_eq_one_iff_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_one_iff_of_ne_zero (hn : n != 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Eve
n n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_eq_pow_iff_of_ne_zero`：pow_eq_pow_iff_of_ne_zero (hn : n != 0) : a ^
 n = b ^ n ↔ a = b ∨ a = -b ∧ Even n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_eq_one_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_of_ne_zero hn]
/-
**pow_eq_one_iff_cases** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_one_iff_cases : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_eq_one_iff_cases : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_cases]
/-
**pow_eq_neg_pow_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_neg_pow_iff (hb : b != 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Even.pow_pos`：Even.pow_pos (hn : Even n) (ha : a != 0) : 0 < a ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Odd.strictMono_pow`：Odd.strictMono_pow (hn : Odd n) : StrictMono fun a :
 R => a ^ n
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_eq_neg_pow_iff (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n.even_or_odd with
  | .inl he =>
    suffices a ^ n > -b ^ n by simpa [he, not_odd_iff_even.2 he] using this.ne'
    lt_of_lt_of_le (by simp [he.pow_pos hb]) (he.pow_nonneg _)
  | .inr ho => by
    simp only [ho, and_true, ← ho.neg_pow, (ho.strictMono_pow (R := R)).injective.eq_iff]
/-
**pow_eq_neg_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_neg_one_iff : a ^ n = -1 ↔ a = -1 ∧ Odd n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `pow_eq_neg_pow_iff`：pow_eq_neg_pow_iff (hb : b != 0) : a ^ n = -b ^ n ↔ 
a = -b ∧ Odd n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma pow_eq_neg_one_iff : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

end LinearOrderedRing

variable {m n a : ℕ}

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
/-
**Odd.mod_even_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.mod_even_iff (ha : Even a) : Odd (n % a) ↔ Odd n
参数：ha : Even a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.even_sub'`：even_sub' (h : n <= m) : Even (m - n) ↔ (Odd m ↔ Odd n)
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_sub_mod`：∀ {n : ℕ} (k : ℕ), n ∣ k - k % n

--- 原说明 ---
If `a` is even, then `n` is odd iff `n % a` is odd.
-/
lemma Odd.mod_even_iff (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
/-
**Even.mod_even_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.mod_even_iff (ha : Even a) : Even (n % a) ↔ Even n
参数：ha : Even a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.even_sub`：∀ {m n : ℕ}, n ≤ m → (Even (m - n) ↔ (Even m ↔ Even n))
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_sub_mod`：∀ {n : ℕ} (k : ℕ), n ∣ k - k % n

--- 原说明 ---
If `a` is even, then `n` is even iff `n % a` is even.
-/
lemma Even.mod_even_iff (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
/-
**Odd.mod_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a)
参数：hn : Odd n；ha : Even a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Odd.mod_even_iff`：Odd.mod_even_iff (ha : Even a) : Odd (n % a) ↔ Odd n

--- 原说明 ---
If `n` is odd and `a` is even, then `n % a` is odd.
-/
lemma Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a) := (Odd.mod_even_iff ha).mpr hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
/-
**Even.mod_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Even.mod_even (hn : Even n) (ha : Even a) : Even (n % a)
参数：hn : Even n；ha : Even a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Even.mod_even_iff`：Even.mod_even_iff (ha : Even a) : Even (n % a) ↔ Even
 n

--- 原说明 ---
If `n` is even and `a` is even, then `n % a` is even.
-/
lemma Even.mod_even (hn : Even n) (ha : Even a) : Even (n % a) :=
  (Even.mod_even_iff ha).mpr hn
/-
**Odd.of_dvd_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m
参数：hn : Odd n；hm : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `Dvd.dvd.even`：Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m :=
  not_even_iff_odd.1 <| mt hm.even (not_even_iff_odd.2 hn)

/-- `2` is not a factor of an odd natural number. -/
/-
**Odd.ne_two_of_dvd_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.ne_two_of_dvd_nat {m n : Nat} (hn : Odd n) (hm : m ∣ n) : m != 2
参数：hn : Odd n；hm : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.of_dvd_nat`：Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`2` is not a factor of an odd natural number.
-/
lemma Odd.ne_two_of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : m ≠ 2 := by
  rintro rfl
  exact absurd (hn.of_dvd_nat hm) (by decide)
/-
**Int.le_abs_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.le_abs_of_dvd {a b : Int} (h₁ : b != 0) (h₂ : a ∣ b) : a <= |b|
参数：h₁ : b != 0；h₂ : a ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_of_dvd`：∀ {a b : ℤ}, 0 < b → a ∣ b → a ≤ b
-/
lemma Int.le_abs_of_dvd {a b : ℤ} (h₁ : b ≠ 0) (h₂ : a ∣ b) : a ≤ |b| :=
  le_of_dvd (by simpa) (by simpa)
