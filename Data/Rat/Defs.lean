/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Common

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib/Algebra/Field/Rat.lean`
once the `Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notation

- `/.` is infix notation for `Rat.divInt`.

-/

@[expose] public section

-- TODO: If `Inv` was defined earlier than `Algebra.Group.Defs`, we could have
-- assert_not_exists Monoid
assert_not_exists MonoidWithZero Lattice PNat Nat.gcd_greatest

open Function

namespace Rat
variable {q : ℚ}

/-
**Rat.pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：pos (a : Rat) : 0 < a.den
参数：a : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
-/
theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz
/-
**Rat.mk'_num_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ), { num := q.num, den := q.den, den_nz := ⋯, reduced := ⋯ } = q
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
-/
lemma mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
/-
**Rat.ofInt_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ofInt_eq_cast (n : Int) : ofInt n = Int.cast n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl
/-
**Rat.intCast_injective** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：intCast_injective : Injective (Int.cast : Int -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma intCast_injective : Injective (Int.cast : ℤ → ℚ) := fun _ _ ↦ congr_arg num
/-
**Rat.natCast_injective** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：natCast_injective : Injective (Nat.cast : Nat -> Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `Rat.intCast_injective`：intCast_injective : Injective (Int.cast : Int -> 
Rat)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
-/
lemma natCast_injective : Injective (Nat.cast : ℕ → ℚ) :=
  intCast_injective.comp fun _ _ ↦ Int.natCast_inj.1
/-
**Rat.intCast_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {n : ℤ}, ↑n = 1 ↔ n = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.intCast_inj`：∀ {a b : ℤ}, ↑a = ↑b ↔ a = b
-/
@[simp high, norm_cast] lemma intCast_eq_one_iff {n : ℤ} : (n : ℚ) = 1 ↔ n = 1 := intCast_inj
/-
**Rat.natCast_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {n : ℕ}, ↑n = 1 ↔ n = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.natCast_inj`：∀ {a b : ℕ}, ↑a = ↑b ↔ a = b
-/
@[simp high, norm_cast] lemma natCast_eq_one_iff {n : ℕ} : (n : ℚ) = 1 ↔ n = 1 := natCast_inj
/-
**Rat.mkRat_eq_divInt** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：mkRat_eq_divInt (n d) : mkRat n d = n /. d
参数：n d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl
/-
**Rat.mk'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (d : ℕ) (h : d ≠ 0) (w : (Int.natAbs 0).Coprime d), { num := 0, den := d
, den_nz := h, reduced := w } = 0
参数：d : ℕ；h : d ≠ 0；w : (Int.natAbs 0).Coprime d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr; simp_all
/-
**Rat.num_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：num_ne_zero {q : Rat} : q.num != 0 ↔ q != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Rat.num_eq_zero`：∀ {q : ℚ}, q.num = 0 ↔ q = 0
-/
lemma num_ne_zero {q : ℚ} : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not
/-
**Rat.den_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ), q.den ≠ 0
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
-/
@[simp] lemma den_ne_zero (q : ℚ) : q.den ≠ 0 := q.den_pos.ne'

@[simp]
/-
**Rat.divInt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：divInt_eq_zero {a b : Int} (b0 : b != 0) : a /. b = 0 ↔ a = 0
参数：b0 : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.zero_divInt`：∀ (n : ℤ), Rat.divInt 0 n = 0
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `Int.zero_mul`：∀ (a : ℤ), 0 * a = 0
· 使用定理 `Int.mul_eq_zero`：∀ {a b : ℤ}, a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b, divInt_eq_divInt_iff b0 b0, Int.zero_mul, Int.mul_eq_zero, or_iff_left b0]
/-
**Rat.divInt_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：divInt_ne_zero {a b : Int} (b0 : b != 0) : a /. b != 0 ↔ a != 0
参数：b0 : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Rat.divInt_eq_zero`：divInt_eq_zero {a b : Int} (b0 : b != 0) : a /. b = 
0 ↔ a = 0
-/
theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (divInt_eq_zero b0).not

-- TODO: Rename `mkRat_num_den` in Lean core
alias mkRat_num_den' := mkRat_self
/-
**Rat.intCast_eq_divInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
-/
theorem intCast_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := mk_eq_divInt
/-
**Rat.lift_binop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：lift_binop_eq (f : Rat -> Rat -> Rat) (f₁ : Int -> Int -> Int -> Int -> In
t) (f₂ : Int -> Int -> Int -> Int -> Int) (fv : forall {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂}
, f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂) (f0 : 
forall {n₁ d₁ n₂ d₂}, d₁ != 0 -> d₂ != 0 -> f₂ n₁ d₁ n₂ d₂ != 0) (a b c d : Int)
 (b0 : b != 0) (d0 : d != 0) (H : forall {n₁ d₁ n₂ d₂}, a * d₁ = n₁ * b -> c * d
₂ = n₂ * d -> f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) : f (a 
/. b) (c /. d) = f₁ a b c 
参数：f : Rat -> Rat -> Rat；f₁ : Int -> Int -> Int -> Int -> Int；f₂ : Int -> Int ->
 Int -> Int -> Int；fv : forall {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂}, f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂
, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂；f0 : forall {n₁ d₁ n₂ d₂}, d₁ !
= 0 -> d₂ != 0 -> f₂ n₁ d₁ n₂ d₂ != 0；a b c d : Int；b0 : b != 0；d0 : d != 0；H : 
forall {n₁ d₁ n₂ d₂}, a * d₁ = n₁ * b -> c * d₂ = n₂ * d -> f₁ n₁ d₁ n₂ d₂ * f₂ 
a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
-/
theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
    (fv :
      ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
        f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
    (f0 : ∀ {n₁ d₁ n₂ d₂}, d₁ ≠ 0 → d₂ ≠ 0 → f₂ n₁ d₁ n₂ d₂ ≠ 0) (a b c d : ℤ)
    (b0 : b ≠ 0) (d0 : d ≠ 0)
    (H :
      ∀ {n₁ d₁ n₂ d₂}, a * d₁ = n₁ * b → c * d₂ = n₂ * d →
        f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
    f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d := by
  generalize ha : a /. b = x; obtain ⟨n₁, d₁, h₁, c₁⟩ := x; rw [mk_eq_divInt] at ha
  generalize hc : c /. d = x; obtain ⟨n₂, d₂, h₂, c₂⟩ := x; rw [mk_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_divInt_iff (f0 d₁0 d₂0) (f0 b0 d0)).2
    (H ((divInt_eq_divInt_iff b0 d₁0).1 ha) ((divInt_eq_divInt_iff d0 d₂0).1 hc))
/-
**Rat.neg_def** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：neg_def (q : Rat) : -q = -q.num /. q.den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.neg_divInt`：∀ (n d : ℤ), -Rat.divInt n d = Rat.divInt (-n) d
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
-/
lemma neg_def (q : ℚ) : -q = -q.num /. q.den := by rw [← neg_divInt, num_divInt_den]
/-
**Rat.divInt_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n d : ℤ), Rat.divInt n (-d) = Rat.divInt (-n) d
参数：n d : ℤ；-d；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.divInt_neg'`：∀ (num den : ℤ), Rat.divInt num (-den) = Rat.divInt (-n
um) den
-/
@[simp] lemma divInt_neg (n d : ℤ) : n /. -d = -n /. d := divInt_neg' ..
/-
**Rat.mk'_mul_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hnd₁ : n₁.natAbs.
Coprime d₁) (hnd₂ : n₂.natAbs.Coprime d₂)   (h₁₂ : n₁.natAbs.Coprime d₂) (h₂₁ : 
n₂.natAbs.Coprime d₁),   { num := n₁, den := d₁, den_nz := hd₁, reduced := hnd₁ 
} * { num := n₂, den := d₂, den_nz := hd₂, reduced := hnd₂ } =     { num := n₁ *
 n₂, den := d₁ * d₂, den_nz := ⋯, reduced := ⋯ }
参数：n₁ n₂ : ℤ；d₁ d₂ : ℕ；hd₁ : d₁ ≠ 0；hd₂ : d₂ ≠ 0；hnd₁ : n₁.natAbs.Coprime d₁；hnd
₂ : n₂.natAbs.Coprime d₂；h₁₂ : n₁.natAbs.Coprime d₂；h₂₁ : n₂.natAbs.Coprime d₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_def`：∀ (a b : ℚ), a * b = Rat.normalize (a.num * b.num) (a.den *
 b.den) ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.mk_eq_normalize`：∀ (num : ℤ) (den : ℕ) (nz : den ≠ 0) (c : num.natAb
s.Coprime den),   { num := num, den := den, den_nz := nz, reduced := c } = Rat.n
ormalize …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk'_mul_mk' (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul_left h₂₁).mul_right (h₁₂.mul_left hnd₂)) := by
  rw [mul_def]; simp [mk_eq_normalize]
/-
**Rat.mul_eq_mkRat** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：mul_eq_mkRat (q r : Rat) : q * r = mkRat (q.num * r.num) (q.den * r.den)
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_def`：∀ (a b : ℚ), a * b = Rat.normalize (a.num * b.num) (a.den *
 b.den) ⋯
· 使用定理 `Rat.normalize_eq_mkRat`：∀ {num : ℤ} {den : ℕ} (den_nz : den ≠ 0), Rat.no
rmalize num den den_nz = mkRat num den
-/
lemma mul_eq_mkRat (q r : ℚ) : q * r = mkRat (q.num * r.num) (q.den * r.den) := by
  rw [mul_def, normalize_eq_mkRat]
/-
**Rat.pow_eq_mkRat** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：pow_eq_mkRat (q : Rat) (n : Nat) : q ^ n = mkRat (q.num ^ n) (q.den ^ n)
参数：q : Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.pow_def`：∀ (q : ℚ) (n : ℕ), q ^ n = { num := q.num ^ n, den := q.den
 ^ n, den_nz := ⋯, reduced := ⋯ }
· 使用定理 `Rat.mk_eq_mkRat`：∀ (num : ℤ) (den : ℕ) (nz : den ≠ 0) (c : num.natAbs.Co
prime den),   { num := num, den := den, den_nz := nz, reduced := c } = mkRat num
 den
-/
lemma pow_eq_mkRat (q : ℚ) (n : ℕ) : q ^ n = mkRat (q.num ^ n) (q.den ^ n) := by
  rw [pow_def, mk_eq_mkRat]
/-
**Rat.pow_eq_divInt** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：pow_eq_divInt (q : Rat) (n : Nat) : q ^ n = q.num ^ n /. q.den ^ n
参数：q : Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.pow_def`：∀ (q : ℚ) (n : ℕ), q ^ n = { num := q.num ^ n, den := q.den
 ^ n, den_nz := ⋯, reduced := ⋯ }
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `Int.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
-/
lemma pow_eq_divInt (q : ℚ) (n : ℕ) : q ^ n = q.num ^ n /. q.den ^ n := by
  rw [pow_def, mk_eq_divInt, Int.natCast_pow]
/-
**Rat.mk'_pow** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (num : ℤ) (den : ℕ) (hd : den ≠ 0) (hdn : num.natAbs.Coprime den) (n : ℕ
),   { num := num, den := den, den_nz := hd, reduced := hdn } ^ n =     { num :=
 num ^ n, den := den ^ n, den_nz := ⋯, reduced := ⋯ }
参数：num : ℤ；den : ℕ；hd : den ≠ 0；hdn : num.natAbs.Coprime den；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
-/
@[simp] lemma mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl
/-
**Rat.inv_mkRat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (a : ℤ) (b : ℕ), (mkRat a b)⁻¹ = Rat.divInt (↑b) a
参数：a : ℤ；b : ℕ；mkRat a b；↑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mkRat_eq_divInt`：mkRat_eq_divInt (n d) : mkRat n d = n /. d
· 使用定理 `Rat.inv_divInt`：∀ (n d : ℤ), (Rat.divInt n d)⁻¹ = Rat.divInt d n
-/
@[simp] lemma inv_mkRat (a : ℤ) (b : ℕ) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt, inv_divInt]
/-
**Rat.divInt_div_divInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n₁ d₁ n₂ d₂ : ℤ), Rat.divInt n₁ d₁ / Rat.divInt n₂ d₂ = Rat.divInt (n₁ 
* d₂) (d₁ * n₂)
参数：n₁ d₁ n₂ d₂ : ℤ；n₁ * d₂；d₁ * n₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.div_def`：∀ (a b : ℚ), a / b = a * b⁻¹
· 使用定理 `Rat.inv_divInt`：∀ (n d : ℤ), (Rat.divInt n d)⁻¹ = Rat.divInt d n
· 使用定理 `Rat.divInt_mul_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ}, Rat.divInt n₁ d₁ * Rat
.divInt n₂ d₂ = Rat.divInt (n₁ * n₂) (d₁ * d₂)
-/
@[simp] lemma divInt_div_divInt (n₁ d₁ n₂ d₂) :
    (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂) := by
  rw [div_def, inv_divInt, divInt_mul_divInt]
/-
**Rat.div_def'** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：div_def' (q r : Rat) : q / r = (q.num * r.den) /. (q.den * r.num)
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.divInt_div_divInt`：∀ (n₁ d₁ n₂ d₂ : ℤ), Rat.divInt n₁ d₁ / Rat.divIn
t n₂ d₂ = Rat.divInt (n₁ * d₂) (d₁ * n₂)
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
-/
lemma div_def' (q r : ℚ) : q / r = (q.num * r.den) /. (q.den * r.num) := by
  rw [← divInt_div_divInt, num_divInt_den, num_divInt_den]

variable (a b c : ℚ)
/-
**Rat.divInt_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n : ℤ), Rat.divInt n 1 = ↑n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Nat.gcd_one_right`：∀ (n : ℕ), n.gcd 1 = 1
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Int.ediv_one`：∀ (a : ℤ), a / 1 = a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Rat.maybeNormalize.congr_simp`：∀ (num num_1 : ℤ) (e_num : num = num_1) (
den den_1 : ℕ) (e_den : den = den_1) (g g_1 : ℕ) (e_g : g = g_1)   (dvd_num : ↑g
 ∣ num) (dvd_den : …
· 使用定理 `Rat.maybeNormalize_eq`：∀ {num : ℤ} {den g : ℕ} (dvd_num : ↑g ∣ num) (dvd
_den : g ∣ den) (den_nz : den / g ≠ 0)   (reduced : (num / ↑g).natAbs.Coprime (d
en / g)),  …
· 使用定理 `Rat.mk'.congr_simp`：∀ (num num_1 : ℤ) (e_num : num = num_1) (den den_1 :
 ℕ) (e_den : den = den_1) (den_nz : den ≠ 0)   (reduced : num.natAbs.Coprime den
),   { n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma divInt_one (n : ℤ) : n /. 1 = n := by simp [divInt, mkRat, normalize]
/-
**Rat.divInt_one_one** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：divInt_one_one : 1 /. 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_one`：∀ (n : ℤ), Rat.divInt n 1 = ↑n
· 使用定理 `Rat.intCast_one`：↑1 = 1
-/
lemma divInt_one_one : 1 /. 1 = 1 := by rw [divInt_one, Rat.intCast_one]
/-
**Rat.zero_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：0 ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.divInt_one_one`：divInt_one_one : 1 /. 1 = 1
· 使用定理 `Rat.divInt_ne_zero`：divInt_ne_zero {a b : Int} (b0 : b != 0) : a /. b !=
 0 ↔ a != 0
-/
protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← divInt_one_one, divInt_ne_zero] <;> lia

attribute [simp] mkRat_eq_zero

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Data.Real.Basic
/-
**Rat.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：nontrivial : Nontrivial Rat where exists_pair_ne
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance nontrivial : Nontrivial ℚ where exists_pair_ne := ⟨1, 0, by decide⟩

/-! ### The rational numbers are a group -/

/-
**Rat.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addCommGroup : AddCommGroup Rat where zero_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.add_assoc`：∀ (a b c : ℚ), a + b + c = a + (b + c)
· 使用定理 `Rat.zero_add`：∀ (a : ℚ), 0 + a = a
· 使用定理 `Rat.add_zero`：∀ (a : ℚ), a + 0 = a
· 使用定理 `Rat.zero_mul`：∀ (a : ℚ), 0 * a = 0
· 使用定理 `Rat.sub_eq_add_neg`：∀ (a b : ℚ), a - b = a + -b
· 使用定理 `Rat.neg_add_cancel`：∀ (a : ℚ), -a + a = 0
· 使用定理 `Rat.add_comm`：∀ (a b : ℚ), a + b = b + a

--- 原说明 ---
### The rational numbers are a group
-/
instance addCommGroup : AddCommGroup ℚ where
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := (· * ·)
  zsmul := (· * ·)
  nsmul_zero := Rat.zero_mul
  nsmul_succ n q := by
    change ((n + 1 : Int) : Rat) * q = _
    rw [Rat.intCast_add, Rat.add_mul, Rat.intCast_one, Rat.one_mul]
    rfl
  zsmul_zero' := Rat.zero_mul
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; simp [Rat.add_mul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Int.negSucc_eq, Rat.intCast_neg, Rat.neg_mul]; rfl
/-
**Rat.addGroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addGroup : AddGroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroup : AddGroup ℚ := by infer_instance
/-
**Rat.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addCommMonoid : AddCommMonoid Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid ℚ := by infer_instance
/-
**Rat.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addMonoid : AddMonoid Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid ℚ := by infer_instance
/-
**Rat.addLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addLeftCancelSemigroup : AddLeftCancelSemigroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance
/-
**Rat.addRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addRightCancelSemigroup : AddRightCancelSemigroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance
/-
**Rat.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addCommSemigroup : AddCommSemigroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance
/-
**Rat.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：addSemigroup : AddSemigroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addSemigroup : AddSemigroup ℚ := by infer_instance
/-
**Rat.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：commMonoid : CommMonoid Rat where mul_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.mul_assoc`：∀ (a b c : ℚ), a * b * c = a * (b * c)
· 使用定理 `Rat.one_mul`：∀ (a : ℚ), 1 * a = a
· 使用定理 `Rat.mul_one`：∀ (a : ℚ), a * 1 = a
· 使用定理 `Rat.pow_zero`：∀ (q : ℚ), q ^ 0 = 1
· 使用定理 `Rat.pow_succ`：∀ (q : ℚ) (n : ℕ), q ^ (n + 1) = q ^ n * q
· 使用定理 `Rat.mul_comm`：∀ (a b : ℚ), a * b = b * a
-/
instance commMonoid : CommMonoid ℚ where
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := Rat.pow_zero
  npow_succ n q := Rat.pow_succ q n
/-
**Rat.monoid** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：monoid : Monoid Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid : Monoid ℚ := by infer_instance
/-
**Rat.commSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：commSemigroup : CommSemigroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemigroup : CommSemigroup ℚ := by infer_instance
/-
**Rat.semigroup** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：semigroup : Semigroup Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semigroup : Semigroup ℚ := by infer_instance

@[simp]
/-
**Rat.den_neg_eq_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_neg_eq_den (q : Rat) : (-q).den = q.den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_neg_eq_den (q : ℚ) : (-q).den = q.den :=
  rfl

@[simp]
/-
**Rat.num_neg_eq_neg_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl

-- Not `@[simp]` as `num_ofNat` is stronger.
/-
**Rat.num_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_zero : Rat.num 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_zero : Rat.num 0 = 0 :=
  rfl

-- Not `@[simp]` as `den_ofNat` is stronger.
/-
**Rat.den_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_zero : Rat.den 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_zero : Rat.den 0 = 1 :=
  rfl
/-
**Rat.zero_of_num_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：zero_of_num_zero {q : Rat} (hq : q.num = 0) : q = 0
参数：hq : q.num = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `Rat.zero_mkRat`：∀ (n : ℕ), mkRat 0 n = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
-/
lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.num_divInt_den.symm
/-
**Rat.zero_iff_num_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：zero_iff_num_zero {q : Rat} : q = 0 ↔ q.num = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Rat.zero_of_num_zero`：zero_of_num_zero {q : Rat} (hq : q.num = 0) : q = 
0
-/
theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

-- `Not `@[simp]` as `num_ofNat` is stronger.
/-
**Rat.num_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_one : (1 : Rat).num = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem num_one : (1 : ℚ).num = 1 :=
  rfl

@[simp]
/-
**Rat.den_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_one : (1 : Rat).den = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem den_one : (1 : ℚ).den = 1 :=
  rfl
/-
**Rat.mk_num_ne_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mk_num_ne_zero_of_ne_zero {q : Rat} {n d : Int} (hq : q != 0) (hqnd : q = 
n /. d) : n != 0
参数：hq : q != 0；hqnd : q = n /. d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.zero_divInt`：∀ (n : ℤ), Rat.divInt 0 n = 0
-/
theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd
/-
**Rat.mk_denom_ne_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mk_denom_ne_zero_of_ne_zero {q : Rat} {n d : Int} (hq : q != 0) (hqnd : q 
= n /. d) : d != 0
参数：hq : q != 0；hqnd : q = n /. d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.divInt_zero`：∀ (n : ℤ), Rat.divInt n 0 = 0
-/
theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd
/-
**Rat.divInt_ne_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：divInt_ne_zero_of_ne_zero {n d : Int} (h : n != 0) (hd : d != 0) : n /. d 
!= 0
参数：h : n != 0；hd : d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.divInt_ne_zero`：divInt_ne_zero {a b : Int} (b0 : b != 0) : a /. b !=
 0 ↔ a != 0
-/
theorem divInt_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
  (divInt_ne_zero hd).mpr h

section Casts

/-
**Rat.add_divInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (a b c : ℤ), Rat.divInt (a + b) c = Rat.divInt a c + Rat.divInt b c
参数：a b c : ℤ；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_zero`：∀ (n : ℤ), Rat.divInt n 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Rat.divInt_add_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ},   d₁ ≠ 0 → d₂ ≠ 0 → Ra
t.divInt n₁ d₁ + Rat.divInt n₂ d₂ = Rat.divInt (n₁ * d₂ + n₂ * d₁) (d₁ * d₂)
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `Int.mul_ne_zero`：∀ {a b : ℤ}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
· 使用定理 `Int.add_mul`：∀ (a b c : ℤ), (a + b) * c = a * c + b * c
· 使用定理 `Int.mul_assoc`：∀ (a b c : ℤ), a * b * c = a * (b * c)
-/
protected theorem add_divInt (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h, divInt_eq_divInt_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]
/-
**Rat.intCast_div_eq_divInt** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：intCast_div_eq_divInt (n d : Int) : (n : Rat) / d = n /. d
参数：n d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
-/
lemma intCast_div_eq_divInt (n d : ℤ) : (n : ℚ) / d = n /. d := by rw [divInt_eq_div]
/-
**Rat.natCast_div_eq_divInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_div_eq_divInt (n d : Nat) : (n : Rat) / d = n /. d
参数：n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.intCast_div_eq_divInt`：intCast_div_eq_divInt (n d : Int) : (n : Rat)
 / d = n /. d
-/
theorem natCast_div_eq_divInt (n d : ℕ) : (n : ℚ) / d = n /. d := Rat.intCast_div_eq_divInt n d
/-
**Rat.divInt_mul_divInt_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：divInt_mul_divInt_cancel {x : Int} (hx : x != 0) (n d : Int) : n /. x * (x
 /. d) = n /. d
参数：hx : x != 0；n d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.divInt_zero`：∀ (n : ℤ), Rat.divInt n 0 = 0
· 使用定理 `Rat.mul_zero`：∀ (a : ℚ), a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Rat.divInt_mul_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ}, Rat.divInt n₁ d₁ * Rat
.divInt n₂ d₂ = Rat.divInt (n₁ * n₂) (d₁ * d₂)
· 使用定理 `Int.mul_comm`：∀ (a b : ℤ), a * b = b * a
· 使用定理 `Rat.divInt_mul_right`：∀ {n d a : ℤ}, a ≠ 0 → Rat.divInt (n * a) (d * a) 
= Rat.divInt n d
-/
theorem divInt_mul_divInt_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt, x.mul_comm, divInt_mul_right hx]
/-
**Rat.coe_int_num_of_den_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：coe_int_num_of_den_eq_one {q : Rat} (hq : q.den = 1) : (q.num : Rat) = q
参数：hq : q.den = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `Rat.intCast_eq_divInt`：intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1
-/
theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl
/-
**Rat.eq_num_of_isInt** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：eq_num_of_isInt {q : Rat} (h : q.isInt) : q = q.num
参数：h : q.isInt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.coe_int_num_of_den_eq_one`：coe_int_num_of_den_eq_one {q : Rat} (hq :
 q.den = 1) : (q.num : Rat) = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.beq_eq_true_eq`：∀ (a b : ℕ), ((a == b) = true) = (a = b)
· 使用定理 `Rat.isInt.eq_1`：∀ (a : ℚ), a.isInt = (a.den == 1)
-/
lemma eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm
/-
**Rat.den_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_eq_one_iff (r : Rat) : r.den = 1 ↔ ↑r.num = r
参数：r : Rat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.coe_int_num_of_den_eq_one`：coe_int_num_of_den_eq_one {q : Rat} (hq :
 q.den = 1) : (q.num : Rat) = q
· 使用定理 `Rat.den_intCast`：∀ (a : ℤ), (↑a).den = 1
-/
theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩
/-
**Rat.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：canLift : CanLift Rat Int (↑) fun q => q.den = 1
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.coe_int_num_of_den_eq_one`：coe_int_num_of_den_eq_one {q : Rat} (hq :
 q.den = 1) : (q.num : Rat) = q
-/
instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

@[deprecated (since := "2026-06-06")] alias coe_int_inj := intCast_inj

end Casts

/--
A version of `Rat.casesOn` that uses `/` instead of `Rat.mk'`. Use as
```lean
cases r with
| div p q nonzero coprime =>
```
-/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Rat.divCasesOn** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：divCasesOn {C : Rat -> Sort*} (a : Rat) (div : forall (n : Int) (d : Nat),
 d != 0 -> n.natAbs.Coprime d -> C (n / d)) : C a
参数：a : Rat；div : forall (n : Int) (d : Nat), d != 0 -> n.natAbs.Coprime d -> C (
n / d)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q

--- 原说明 ---
A version of `Rat.casesOn` that uses `/` instead of `Rat.mk'`. Use as
```lean
cases r with
| div p q nonzero coprime =>
```
-/
def divCasesOn {C : ℚ → Sort*} (a : ℚ)
    (div : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → n.natAbs.Coprime d → C (n / d)) : C a :=
  a.casesOn fun n d nz red => by rw [Rat.mk_eq_divInt, Rat.divInt_eq_div]; exact div n d nz red

end Rat

