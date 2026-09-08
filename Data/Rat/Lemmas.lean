/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.PNat.Defs

/-!
# Further lemmas for the Rational Numbers

-/

@[expose] public section


namespace Rat

-- TODO: move this to Lean
attribute [norm_cast] num_intCast den_intCast

/-
**Rat.num_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_dvd (a) {b : Int} (b0 : b != 0) : (a /. b).num ∣ a
参数：a；b0 : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natAbs_dvd`：∀ {a b : ℤ}, ↑a.natAbs ∣ b ↔ a ∣ b
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
-/
theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a := by
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [Rat.mk_eq_divInt, divInt_eq_divInt_iff b0 (mod_cast h)] at e
  refine Int.natAbs_dvd.1 <| Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <|
    c.dvd_of_dvd_mul_right ?_
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at this; simp [this]
/-
**Rat.den_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_dvd (a b : Int) : ((a /. b).den : Int) ∣ b
参数：a b : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_zero`：∀ (n : ℤ), Rat.divInt n 0 = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
-/
theorem den_dvd (a b : ℤ) : ((a /. b).den : ℤ) ∣ b := by
  by_cases b0 : b = 0; · simp [b0]
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [mk_eq_divInt,
    divInt_eq_divInt_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
  refine Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <| c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul, ← Int.natCast_dvd_natCast, Int.dvd_natAbs, ← e]; simp
/-
**Rat.num_den_mk** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_den_mk {q : Rat} {n d : Int} (hd : d != 0) (qdf : q = n /. d) : exists
 c : Int, n = c * q.num ∧ d = c * q.den
参数：hd : d != 0；qdf : q = n /. d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.zero_divInt`：∀ (n : ℤ), Rat.divInt 0 n = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `Rat.num_dvd`：num_dvd (a) {b : Int} (b0 : b != 0) : (a /. b).num ∣ a
· 使用定理 `Int.ediv_mul_cancel`：∀ {a b : ℤ}, b ∣ a → a / b * b = a
· 使用引理 `Int.eq_mul_div_of_mul_eq_mul_of_dvd_left`：eq_mul_div_of_mul_eq_mul_of_dv
d_left (hb : b != 0) (hbc : b ∣ c) (h : b * a = c * d) : a = c / b * d
· 使用引理 `Rat.num_ne_zero`：num_ne_zero {q : Rat} : q.num != 0 ↔ q != 0
· 使用定理 `Rat.divInt_ne_zero`：divInt_ne_zero {a b : Int} (b0 : b != 0) : a /. b !=
 0 ↔ a != 0
-/
theorem num_den_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) :
    ∃ c : ℤ, n = c * q.num ∧ d = c * q.den := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.den := by
    refine (divInt_eq_divInt_iff ?_ hd).mp ?_
    · exact Int.natCast_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_divInt_den]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine ⟨n / q.num, ?_, ?_⟩
  · rw [Int.ediv_mul_cancel hqdn]
  · refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left ?_ hqdn this
    rw [qdf]
    exact Rat.num_ne_zero.2 ((divInt_ne_zero hd).mpr hn)
/-
**Rat.add_den_dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：add_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den
参数：q₁ q₂ : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.add_def`：∀ (a b : ℚ), a + b = Rat.normalize (a.num * ↑b.den + b.num 
* ↑a.den) (a.den * b.den) ⋯
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.normalize.den_nz`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs.
gcd den → den / g ≠ 0
· 使用定理 `Rat.normalize.reduced`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs
.gcd den → (num / ↑g).natAbs.Coprime (den / g)
· 使用定理 `Rat.normalize_eq`：∀ {num : ℤ} {den : ℕ} (den_nz : den ≠ 0),   Rat.normal
ize num den den_nz =     { num := num / ↑(num.natAbs.gcd den), den := den / num.
natAbs…
· 使用定理 `Nat.div_dvd_iff_dvd_mul`：∀ {a b c : ℕ}, b ∣ a → 0 < b → (a / b ∣ c ↔ a ∣
 b * c)
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Nat.gcd_pos_of_pos_right`：∀ (m : ℕ) {n : ℕ}, 0 < n → 0 < m.gcd n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_mul_lcm`：∀ (m n : ℕ), m.gcd n * m.lcm n = m * n
· 使用定理 `mul_dvd_mul_iff_right`：mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsC
ancelMulZero α] {a b c : α} (hc : c != 0) : a * c ∣ b * c ↔ a ∣ b
· 使用定理 `Nat.lcm_ne_zero`：∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.lcm n ≠ 0
· 使用定理 `Nat.dvd_gcd_iff`：∀ {k : ℕ} {m n : ℕ}, k ∣ m.gcd n ↔ k ∣ m ∧ k ∣ n
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Int.dvd_add`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem add_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den := by
  rw [add_def, normalize_eq, Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ (by simp [Nat.pos_iff_ne_zero])), ← Nat.gcd_mul_lcm,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (by simp) (by simp)), Nat.dvd_gcd_iff]
  refine ⟨?_, dvd_mul_right _ _⟩
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  apply Int.dvd_add
    <;> apply dvd_mul_of_dvd_right <;> rw [Int.natCast_dvd_natCast]
    <;> [exact Nat.gcd_dvd_right _ _; exact Nat.gcd_dvd_left _ _]
/-
**Rat.sub_den_dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sub_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ - q₂).den ∣ q₁.den.lcm q₂.den
参数：q₁ q₂ : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Rat.add_den_dvd_lcm`：add_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.
den.lcm q₂.den
-/
theorem sub_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ - q₂).den ∣ q₁.den.lcm q₂.den := by
  simpa only [sub_eq_add_neg, neg_den] using add_den_dvd_lcm q₁ (-q₂)
/-
**Rat.add_den_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：add_den_dvd (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.den * q₂.den
参数：q₁ q₂ : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Rat.add_den_dvd_lcm`：add_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.
den.lcm q₂.den
· 使用定理 `Nat.lcm_dvd_mul`：∀ (m n : ℕ), m.lcm n ∣ m * n
-/
theorem add_den_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den * q₂.den :=
  (add_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)
/-
**Rat.sub_den_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sub_den_dvd (q₁ q₂ : Rat) : (q₁ - q₂).den ∣ q₁.den * q₂.den
参数：q₁ q₂ : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Rat.sub_den_dvd_lcm`：sub_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ - q₂).den ∣ q₁.
den.lcm q₂.den
· 使用定理 `Nat.lcm_dvd_mul`：∀ (m n : ℕ), m.lcm n ∣ m * n
-/
theorem sub_den_dvd (q₁ q₂ : ℚ) : (q₁ - q₂).den ∣ q₁.den * q₂.den :=
  (sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)
/-
**Rat.mul_den_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mul_den_dvd (q₁ q₂ : Rat) : (q₁ * q₂).den ∣ q₁.den * q₂.den
参数：q₁ q₂ : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_def`：∀ (a b : ℚ), a * b = Rat.normalize (a.num * b.num) (a.den *
 b.den) ⋯
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.normalize.den_nz`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs.
gcd den → den / g ≠ 0
· 使用定理 `Rat.normalize.reduced`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs
.gcd den → (num / ↑g).natAbs.Coprime (den / g)
· 使用定理 `Rat.normalize_eq`：∀ {num : ℤ} {den : ℕ} (den_nz : den ≠ 0),   Rat.normal
ize num den den_nz =     { num := num / ↑(num.natAbs.gcd den), den := den / num.
natAbs…
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
-/
theorem mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  rw [mul_def, normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right
/-
**Rat.mul_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mul_num (q₁ q₂ : Rat) : (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num 
* q₂.num).natAbs (q₁.den * q₂.den)
参数：q₁ q₂ : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_def`：∀ (a b : ℚ), a * b = Rat.normalize (a.num * b.num) (a.den *
 b.den) ⋯
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.normalize.den_nz`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs.
gcd den → den / g ≠ 0
· 使用定理 `Rat.normalize.reduced`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs
.gcd den → (num / ↑g).natAbs.Coprime (den / g)
· 使用定理 `Rat.normalize_eq`：∀ {num : ℤ} {den : ℕ} (den_nz : den ≠ 0),   Rat.normal
ize num den den_nz =     { num := num / ↑(num.natAbs.gcd den), den := den / num.
natAbs…
-/
theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]
/-
**Rat.mul_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mul_den (q₁ q₂ : Rat) : (q₁ * q₂).den = q₁.den * q₂.den / Nat.gcd (q₁.num 
* q₂.num).natAbs (q₁.den * q₂.den)
参数：q₁ q₂ : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_def`：∀ (a b : ℚ), a * b = Rat.normalize (a.num * b.num) (a.den *
 b.den) ⋯
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.normalize.den_nz`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs.
gcd den → den / g ≠ 0
· 使用定理 `Rat.normalize.reduced`：∀ {num : ℤ} {den g : ℕ}, den ≠ 0 → g = num.natAbs
.gcd den → (num / ↑g).natAbs.Coprime (den / g)
· 使用定理 `Rat.normalize_eq`：∀ {num : ℤ} {den : ℕ} (den_nz : den ≠ 0),   Rat.normal
ize num den den_nz =     { num := num / ↑(num.natAbs.gcd den), den := den / num.
natAbs…
-/
theorem mul_den (q₁ q₂ : ℚ) :
    (q₁ * q₂).den =
      q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]

@[simp]
/-
**Rat.add_intCast_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：add_intCast_den (q : Rat) (n : Int) : (q + n).den = q.den
参数：q : Rat；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Rat.add_den_dvd`：add_den_dvd (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.den * q₂
.den
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
-/
theorem add_intCast_den (q : ℚ) (n : ℤ) : (q + n).den = q.den := by
  apply Nat.dvd_antisymm
  · simpa using add_den_dvd q n
  · simpa using add_den_dvd (q + n) (-n)

@[simp]
/-
**Rat.intCast_add_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_add_den (n : Int) (q : Rat) : (n + q).den = q.den
参数：n : Int；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Rat.add_intCast_den`：add_intCast_den (q : Rat) (n : Int) : (q + n).den =
 q.den
-/
theorem intCast_add_den (n : ℤ) (q : ℚ) : (n + q).den = q.den := by
  rw [add_comm, add_intCast_den]

@[simp]
/-
**Rat.sub_intCast_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sub_intCast_den (q : Rat) (n : Int) : (q - n).den = q.den
参数：q : Rat；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Rat.add_intCast_den`：add_intCast_den (q : Rat) (n : Int) : (q + n).den =
 q.den
-/
theorem sub_intCast_den (q : ℚ) (n : ℤ) : (q - n).den = q.den := by
  rw [sub_eq_add_neg, ← Int.cast_neg, add_intCast_den]

@[simp]
/-
**Rat.intCast_sub_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_sub_den (n : Int) (q : Rat) : (n - q).den = q.den
参数：n : Int；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Rat.intCast_add_den`：intCast_add_den (n : Int) (q : Rat) : (n + q).den =
 q.den
· 使用定理 `Rat.neg_den`：∀ (a : ℚ), (-a).den = a.den
-/
theorem intCast_sub_den (n : ℤ) (q : ℚ) : (n - q).den = q.den := by
  rw [sub_eq_add_neg, intCast_add_den, neg_den]

@[simp]
/-
**Rat.add_natCast_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：add_natCast_den (q : Rat) (n : Nat) : (q + n).den = q.den
参数：q : Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.add_intCast_den`：add_intCast_den (q : Rat) (n : Int) : (q + n).den =
 q.den
-/
theorem add_natCast_den (q : ℚ) (n : ℕ) : (q + n).den = q.den := mod_cast add_intCast_den q n

@[simp]
/-
**Rat.natCast_add_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_add_den (n : Nat) (q : Rat) : (n + q).den = q.den
参数：n : Nat；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.intCast_add_den`：intCast_add_den (n : Int) (q : Rat) : (n + q).den =
 q.den
-/
theorem natCast_add_den (n : ℕ) (q : ℚ) : (n + q).den = q.den := mod_cast intCast_add_den n q

@[simp]
/-
**Rat.sub_natCast_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sub_natCast_den (q : Rat) (n : Nat) : (q - n).den = q.den
参数：q : Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.sub_intCast_den`：sub_intCast_den (q : Rat) (n : Int) : (q - n).den =
 q.den
-/
theorem sub_natCast_den (q : ℚ) (n : ℕ) : (q - n).den = q.den := mod_cast sub_intCast_den q n

@[simp]
/-
**Rat.natCast_sub_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_sub_den (n : Nat) (q : Rat) : (n - q).den = q.den
参数：n : Nat；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.intCast_sub_den`：intCast_sub_den (n : Int) (q : Rat) : (n - q).den =
 q.den
-/
theorem natCast_sub_den (n : ℕ) (q : ℚ) : (n - q).den = q.den := mod_cast intCast_sub_den n q
/-
**Rat.add_ofNat_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ) (n : ℕ), (q + OfNat.ofNat n).den = q.den
参数：q : ℚ；n : ℕ；q + OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.add_natCast_den`：add_natCast_den (q : Rat) (n : Nat) : (q + n).den =
 q.den
-/
@[simp] theorem add_ofNat_den (q : ℚ) (n : ℕ) : (q + ofNat(n)).den = q.den := add_natCast_den q n
/-
**Rat.ofNat_add_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n : ℕ) (q : ℚ), (OfNat.ofNat n + q).den = q.den
参数：n : ℕ；q : ℚ；OfNat.ofNat n + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.natCast_add_den`：natCast_add_den (n : Nat) (q : Rat) : (n + q).den =
 q.den
-/
@[simp] theorem ofNat_add_den (n : ℕ) (q : ℚ) : (ofNat(n) + q).den = q.den := natCast_add_den n q
/-
**Rat.sub_ofNat_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ) (n : ℕ), (q - OfNat.ofNat n).den = q.den
参数：q : ℚ；n : ℕ；q - OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.sub_natCast_den`：sub_natCast_den (q : Rat) (n : Nat) : (q - n).den =
 q.den
-/
@[simp] theorem sub_ofNat_den (q : ℚ) (n : ℕ) : (q - ofNat(n)).den = q.den := sub_natCast_den ..
/-
**Rat.ofNat_sub_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (n : ℕ) (q : ℚ), (OfNat.ofNat n - q).den = q.den
参数：n : ℕ；q : ℚ；OfNat.ofNat n - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.natCast_sub_den`：natCast_sub_den (n : Nat) (q : Rat) : (n - q).den =
 q.den
-/
@[simp] theorem ofNat_sub_den (n : ℕ) (q : ℚ) : (ofNat(n) - q).den = q.den := natCast_sub_den ..

/-- A version of `Rat.mul_den` without division. -/
/-
**Rat.den_mul_den_eq_den_mul_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_mul_den_eq_den_mul_gcd (q₁ q₂ : Rat) : q₁.den * q₂.den = (q₁ * q₂).den
 * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den))
参数：q₁ q₂ : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_den`：mul_den (q₁ q₂ : Rat) : (q₁ * q₂).den = q₁.den * q₂.den / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_iff_div_mul_eq`：∀ (n d : ℕ), d ∣ n ↔ n / d * d = n
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n

--- 原说明 ---
A version of `Rat.mul_den` without division.
-/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : ℚ) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_den]
  exact ((Nat.dvd_iff_div_mul_eq _ _).mp (Nat.gcd_dvd_right _ _)).symm

/-- A version of `Rat.mul_num` without division. -/
/-
**Rat.num_mul_num_eq_num_mul_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_mul_num_eq_num_mul_gcd (q₁ q₂ : Rat) : q₁.num * q₂.num = (q₁ * q₂).num
 * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den))
参数：q₁ q₂ : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_num`：mul_num (q₁ q₂ : Rat) : (q₁ * q₂).num = q₁.num * q₂.num / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_mul_cancel`：∀ {a b : ℤ}, b ∣ a → a / b * b = a
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m

--- 原说明 ---
A version of `Rat.mul_num` without division.
-/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : ℚ) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_num]
  refine (Int.ediv_mul_cancel ?_).symm
  rw [← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
/-
**Rat.mul_self_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mul_self_num (q : Rat) : (q * q).num = q.num * q.num
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_num`：mul_num (q₁ q₂ : Rat) : (q₁ * q₂).num = q₁.num * q₂.num / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Nat.Coprime.mul_left`：∀ {m k n : ℕ}, m.Coprime k → n.Coprime k → (m * n)
.Coprime k
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Int.ediv_one`：∀ (a : ℤ), a / 1 = a
-/
theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Int.ofNat_one, Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)
/-
**Rat.mul_self_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mul_self_den (q : Rat) : (q * q).den = q.den * q.den
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_den`：mul_den (q₁ q₂ : Rat) : (q₁ * q₂).den = q₁.den * q₂.den / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Nat.Coprime.mul_left`：∀ {m k n : ℕ}, m.Coprime k → n.Coprime k → (m * n)
.Coprime k
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
-/
theorem mul_self_den (q : ℚ) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)
/-
**Rat.add_num_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：add_num_den (q r : Rat) : q + r = (q.num * r.den + q.den * r.num : Int) /.
 (↑q.den * ↑r.den : Int)
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `Rat.divInt_add_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ},   d₁ ≠ 0 → d₂ ≠ 0 → Ra
t.divInt n₁ d₁ + Rat.divInt n₂ d₂ = Rat.divInt (n₁ * d₂ + n₂ * d₁) (d₁ * d₂)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem add_num_den (q r : ℚ) :
    q + r = (q.num * r.den + q.den * r.num : ℤ) /. (↑q.den * ↑r.den : ℤ) := by
  have hqd : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 q.den_pos
  have hrd : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 r.den_pos
  conv_lhs => rw [← num_divInt_den q, ← num_divInt_den r, divInt_add_divInt _ _ hqd hrd]
  rw [mul_comm r.num q.den]
/-
**Rat.isSquare_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isSquare_iff {q : Rat} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mul_self_num`：mul_self_num (q : Rat) : (q * q).num = q.num * q.num
· 使用定理 `Rat.mul_self_den`：mul_self_den (q : Rat) : (q * q).den = q.den * q.den
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
-/
theorem isSquare_iff {q : ℚ} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den := by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num, mul_self_den]
    simp only [IsSquare.mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    refine ⟨nr / dr, ?_⟩
    rw [div_mul_div_comm, ← Int.cast_mul, ← Nat.cast_mul, ← hnr, ← hdr, num_div_den]

@[norm_cast, simp]
/-
**Rat.isSquare_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isSquare_natCast_iff {n : Nat} : IsSquare (n : Rat) ↔ IsSquare n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℚ) ↔ IsSquare n := by
  simp_rw [isSquare_iff, num_natCast, den_natCast, IsSquare.one, and_true, Int.isSquare_natCast_iff]

@[norm_cast, simp]
/-
**Rat.isSquare_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isSquare_intCast_iff {z : Int} : IsSquare (z : Rat) ↔ IsSquare z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSquare_intCast_iff {z : ℤ} : IsSquare (z : ℚ) ↔ IsSquare z := by
  simp_rw [isSquare_iff, num_intCast, den_intCast, IsSquare.one, and_true]

@[simp]
/-
**Rat.isSquare_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isSquare_ofNat_iff {n : Nat} : IsSquare (ofNat(n) : Rat) ↔ IsSquare (OfNat
.ofNat n : Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.isSquare_natCast_iff`：isSquare_natCast_iff {n : Nat} : IsSquare (n :
 Rat) ↔ IsSquare n
-/
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℚ) ↔ IsSquare (OfNat.ofNat n : ℕ) :=
  isSquare_natCast_iff
/-
**Rat.mkRat_add_mkRat_of_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mkRat_add_mkRat_of_den (n₁ n₂ : Int) {d : Nat} (h : d != 0) : mkRat n₁ d +
 mkRat n₂ d = mkRat (n₁ + n₂) d
参数：n₁ n₂ : Int；h : d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.mkRat_add_mkRat`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℕ}, d₁ ≠ 0 → d₂ ≠ 0 → mkRat 
n₁ d₁ + mkRat n₂ d₂ = mkRat (n₁ * ↑d₂ + n₂ * ↑d₁) (d₁ * d₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Rat.mkRat_mul_right`：∀ {n : ℤ} {d a : ℕ}, a ≠ 0 → mkRat (n * ↑a) (d * a)
 = mkRat n d
-/
theorem mkRat_add_mkRat_of_den (n₁ n₂ : Int) {d : Nat} (h : d ≠ 0) :
    mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d := by
  rw [mkRat_add_mkRat _ _ h h, ← add_mul, mkRat_mul_right h]

section Casts

/-
**Rat.exists_eq_mul_div_num_and_eq_mul_div_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：exists_eq_mul_div_num_and_eq_mul_div_den (n : Int) {d : Int} (d_ne_zero : 
d != 0) : exists c : Int, n = c * ((n : Rat) / d).num ∧ (d : Int) = c * ((n : Ra
t) / d).den
参数：n : Int；d_ne_zero : d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.num_den_mk`：num_den_mk {q : Rat} {n d : Int} (hd : d != 0) (qdf : q 
= n /. d) : exists c : Int, n = c * q.num ∧ d = c * q.den
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
-/
theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den :=
  haveI : (n : ℚ) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this
/-
**Rat.mul_num_den'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：mul_num_den' (q r : Rat) : (q * r).num * q.den * r.den = q.num * r.num * (
q * r).den
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `Rat.exists_eq_mul_div_num_and_eq_mul_div_den`：exists_eq_mul_div_num_and_
eq_mul_div_den (n : Int) {d : Int} (d_ne_zero : d != 0) : exists c : Int, n = c 
* ((n : Rat) / d).num ∧ (d : Int) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.mul_assoc`：∀ (a b c : ℤ), a * b * c = a * (b * c)
· 使用定理 `mul_eq_mul_left_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsLeftC
ancelMulZero M₀] {a b c : M₀}, a * b = a * c ↔ b = c ∨ a = 0
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Rat.divInt_mul_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ}, Rat.divInt n₁ d₁ * Rat
.divInt n₂ d₂ = Rat.divInt (n₁ * n₂) (d₁ * d₂)
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.eq_iff_mul_eq_mul`：∀ {p q : ℚ}, p = q ↔ p.num * ↑q.den = q.num * ↑p.
den
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
-/
theorem mul_num_den' (q r : ℚ) :
    (q * r).num * q.den * r.den = q.num * r.num * (q * r).den := by
  let s := q.num * r.num /. (q.den * r.den : ℤ)
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_den]
  rw [Int.mul_assoc, Int.mul_assoc, mul_eq_mul_left_iff, or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_mul_divInt q.num r.num
  rw [num_divInt_den, num_divInt_den] at h
  rw [h, mul_comm, ← Rat.eq_iff_mul_eq_mul, ← divInt_eq_div]
/-
**Rat.add_num_den'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：add_num_den' (q r : Rat) : (q + r).num * q.den * r.den = (q.num * r.den + 
r.num * q.den) * (q + r).den
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `Rat.exists_eq_mul_div_num_and_eq_mul_div_den`：exists_eq_mul_div_num_and_
eq_mul_div_den (n : Int) {d : Int} (d_ne_zero : d != 0) : exists c : Int, n = c 
* ((n : Rat) / d).num ∧ (d : Int) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.mul_assoc`：∀ (a b c : ℤ), a * b * c = a * (b * c)
· 使用定理 `mul_eq_mul_left_iff`：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsLeftC
ancelMulZero M₀] {a b c : M₀}, a * b = a * c ↔ b = c ∨ a = 0
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Rat.divInt_add_divInt`：∀ (n₁ n₂ : ℤ) {d₁ d₂ : ℤ},   d₁ ≠ 0 → d₂ ≠ 0 → Ra
t.divInt n₁ d₁ + Rat.divInt n₂ d₂ = Rat.divInt (n₁ * d₂ + n₂ * d₁) (d₁ * d₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.eq_iff_mul_eq_mul`：∀ {p q : ℚ}, p = q ↔ p.num * ↑q.den = q.num * ↑p.
den
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
-/
theorem add_num_den' (q r : ℚ) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den := by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : ℤ)
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.den + r.num * q.den) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_den]
  repeat rw [Int.mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_add_divInt q.num r.num (mod_cast q.den_ne_zero) (mod_cast r.den_ne_zero)
  rw [num_divInt_den, num_divInt_den] at h
  rw [h]
  rw [mul_comm]
  apply Rat.eq_iff_mul_eq_mul.mp
  rw [← divInt_eq_div]
/-
**Rat.substr_num_den'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：substr_num_den' (q r : Rat) : (q - r).num * q.den * r.den = (q.num * r.den
 - r.num * q.den) * (q - r).den
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Rat.num_neg_eq_neg_num`：num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num
· 使用定理 `Rat.den_neg_eq_den`：den_neg_eq_den (q : Rat) : (-q).den = q.den
· 使用定理 `Rat.add_num_den'`：add_num_den' (q r : Rat) : (q + r).num * q.den * r.den
 = (q.num * r.den + r.num * q.den) * (q + r).den
-/
theorem substr_num_den' (q r : ℚ) :
    (q - r).num * q.den * r.den = (q.num * r.den - r.num * q.den) * (q - r).den := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← den_neg_eq_den r,
    add_num_den' q (-r)]

end Casts

/-
**Rat.inv_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ), (-q)⁻¹ = -q⁻¹
参数：q : ℚ；-q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.neg_divInt`：∀ (n d : ℤ), -Rat.divInt n d = Rat.divInt (-n) d
· 使用定理 `Rat.inv_divInt`：∀ (n d : ℤ), (Rat.divInt n d)⁻¹ = Rat.divInt d n
· 使用定理 `Rat.divInt_neg`：∀ (n d : ℤ), Rat.divInt n (-d) = Rat.divInt (-n) d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem inv_neg (q : ℚ) : (-q)⁻¹ = -q⁻¹ := by
  rw [← num_divInt_den q]
  simp only [Rat.neg_divInt, Rat.inv_divInt, Rat.divInt_neg]
/-
**Rat.num_div_eq_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_div_eq_of_coprime {a b : Int} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs 
b.natAbs) : (a / b : Rat).num = a
参数：hb0 : 0 < b；h : Nat.Coprime a.natAbs b.natAbs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
-/
theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    (a / b : ℚ).num = a := by
  lift b to ℕ using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div, ← mk_eq_divInt (nz := hb0.ne') (c := h)]
/-
**Rat.den_div_eq_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_div_eq_of_coprime {a b : Int} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs 
b.natAbs) : ((a / b : Rat).den : Int) = b
参数：hb0 : 0 < b；h : Nat.Coprime a.natAbs b.natAbs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
-/
theorem den_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = b := by
  lift b to ℕ using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div, ← mk_eq_divInt (nz := hb0.ne') (c := h)]
/-
**Rat.div_int_inj** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：div_int_inj {a b c d : Int} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime 
a.natAbs b.natAbs) (h2 : Nat.Coprime c.natAbs d.natAbs) (h : (a : Rat) / b = (c 
: Rat) / d) : a = c ∧ b = d
参数：hb0 : 0 < b；hd0 : 0 < d；h1 : Nat.Coprime a.natAbs b.natAbs；h2 : Nat.Coprime c
.natAbs d.natAbs；h : (a : Rat) / b = (c : Rat) / d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.num_div_eq_of_coprime`：num_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : (a / b : Rat).num = a
· 使用定理 `Rat.den_div_eq_of_coprime`：den_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : ((a / b : Rat).den : Int) = b
-/
theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
    (h2 : Nat.Coprime c.natAbs d.natAbs) (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d := by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]

@[norm_cast]
/-
**Rat.intCast_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_div_self (n : Int) : ((n / n : Int) : Rat) = n / n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.intCast_inj`：∀ {a b : ℤ}, ↑a = ↑b ↔ a = b
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
-/
theorem intCast_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have : (n : ℚ) ≠ 0 := by rwa [← intCast_inj]  at hn
    simp only [Int.ediv_self hn, Int.cast_one, div_self this]

@[norm_cast]
/-
**Rat.natCast_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_div_self (n : Nat) : ((n / n : Nat) : Rat) = n / n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.intCast_div_self`：intCast_div_self (n : Int) : ((n / n : Int) : Rat)
 = n / n
-/
theorem natCast_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
  intCast_div_self n
/-
**Rat.intCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_div (a b : Int) (h : b ∣ a) : ((a / b : Int) : Rat) = a / b
参数：a b : Int；h : b ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.mul_ediv_assoc`：∀ (a : ℤ) {b c : ℤ}, c ∣ b → a * b / c = a * (b / c)
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Rat.intCast_div_self`：intCast_div_self (n : Int) : ((n / n : Int) : Rat)
 = n / n
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem intCast_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm b, Int.mul_ediv_assoc c (dvd_refl b), Int.cast_mul,
    intCast_div_self, Int.cast_mul, mul_div_assoc]
/-
**Rat.natCast_div** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_div (a b : Nat) (h : b ∣ a) : ((a / b : Nat) : Rat) = a / b
参数：a b : Nat；h : b ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.intCast_div`：intCast_div (a b : Int) (h : b ∣ a) : ((a / b : Int) : 
Rat) = a / b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
-/
theorem natCast_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b :=
  intCast_div a b (Int.ofNat_dvd.mpr h)
/-
**Rat.den_div_intCast_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_div_intCast_eq_one_iff (m n : Int) (hn : n != 0) : ((m : Rat) / n).den
 = 1 ↔ n ∣ m
参数：m n : Int；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Rat.num_ne_zero`：num_ne_zero {q : Rat} : q.num != 0 ↔ q != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.den_eq_one_iff`：den_eq_one_iff (r : Rat) : r.den = 1 ↔ ↑r.num = r
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Rat.intCast_div`：intCast_div (a b : Int) (h : b ∣ a) : ((a / b : Int) : 
Rat) = a / b
-/
theorem den_div_intCast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m := by
  replace hn : (n : ℚ) ≠ 0 := num_ne_zero.mp hn
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff hn]
    exact mod_cast (Dvd.intro_left _)
  · exact (intCast_div _ _ · ▸ rfl)
/-
**Rat.den_div_natCast_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_div_natCast_eq_one_iff (m n : Nat) (hn : n != 0) : ((m : Rat) / n).den
 = 1 ↔ n ∣ m
参数：m n : Nat；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Rat.den_div_intCast_eq_one_iff`：den_div_intCast_eq_one_iff (m n : Int) (
hn : n != 0) : ((m : Rat) / n).den = 1 ↔ n ∣ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
-/
theorem den_div_natCast_eq_one_iff (m n : ℕ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m :=
  (den_div_intCast_eq_one_iff m n (Int.ofNat_ne_zero.mpr hn)).trans Int.ofNat_dvd
/-
**Rat.inv_intCast_num_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_intCast_num_of_pos {a : Int} (ha0 : 0 < a) : (a : Rat)⁻¹.num = 1
参数：ha0 : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.num_inv`：∀ (a : ℚ), a⁻¹.num = a.num.sign * ↑a.den
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem inv_intCast_num_of_pos {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 := by
  simp [*]
/-
**Rat.inv_natCast_num_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_natCast_num_of_pos {a : Nat} (ha0 : 0 < a) : (a : Rat)⁻¹.num = 1
参数：ha0 : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.inv_intCast_num_of_pos`：inv_intCast_num_of_pos {a : Int} (ha0 : 0 < 
a) : (a : Rat)⁻¹.num = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem inv_natCast_num_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  inv_intCast_num_of_pos (mod_cast ha0 : 0 < (a : ℤ))
/-
**Rat.inv_intCast_den_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_intCast_den_of_pos {a : Int} (ha0 : 0 < a) : ((a : Rat)⁻¹.den : Int) =
 a
参数：ha0 : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.den_inv`：∀ (a : ℚ), a⁻¹.den = if a.num = 0 then 1 else a.num.natAbs
-/
theorem inv_intCast_den_of_pos {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.den : ℤ) = a := by
  simp only [den_inv, num_intCast]
  grind
/-
**Rat.inv_natCast_den_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_natCast_den_of_pos {a : Nat} (ha0 : 0 < a) : (a : Rat)⁻¹.den = a
参数：ha0 : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.inv_intCast_den_of_pos`：inv_intCast_den_of_pos {a : Int} (ha0 : 0 < 
a) : ((a : Rat)⁻¹.den : Int) = a
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
-/
theorem inv_natCast_den_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.den = a := by
  rw [← Int.ofNat_inj, ← Int.cast_natCast a, inv_intCast_den_of_pos]
  rwa [Int.natCast_pos]
/-
**Rat.inv_intCast_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_intCast_num (a : Int) : (a : Rat)⁻¹.num = Int.sign a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.num_inv`：∀ (a : ℚ), a⁻¹.num = a.num.sign * ↑a.den
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_intCast_num (a : ℤ) : (a : ℚ)⁻¹.num = Int.sign a := by simp
/-
**Rat.inv_natCast_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_natCast_num (a : Nat) : (a : Rat)⁻¹.num = Int.sign a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.num_inv`：∀ (a : ℚ), a⁻¹.num = a.num.sign * ↑a.den
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_natCast_num (a : ℕ) : (a : ℚ)⁻¹.num = Int.sign a := by simp
/-
**Rat.inv_ofNat_num** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_ofNat_num (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Rat)⁻¹.num = 1
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.num_inv`：∀ (a : ℚ), a⁻¹.num = a.num.sign * ↑a.den
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inv_ofNat_num (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℚ)⁻¹.num = 1 := by
  -- This proof is quite unpleasant: golf / find better simp lemmas?
  have : 2 ≤ a := Nat.AtLeastTwo.prop
  simp only [num_inv, num_ofNat, den_ofNat, Nat.cast_one, mul_one, Int.sign_eq_one_iff_pos,
    gt_iff_lt]
  change 0 < (a : ℤ)
  lia

set_option backward.isDefEq.respectTransparency false in
/-
**Rat.inv_intCast_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_intCast_den (a : Int) : (a : Rat)⁻¹.den = if a = 0 then 1 else a.natAb
s
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.den_inv`：∀ (a : ℚ), a⁻¹.den = if a.num = 0 then 1 else a.num.natAbs
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_intCast_den (a : ℤ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a.natAbs := by simp
/-
**Rat.inv_natCast_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_natCast_den (a : Nat) : (a : Rat)⁻¹.den = if a = 0 then 1 else a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.den_inv`：∀ (a : ℚ), a⁻¹.den = if a.num = 0 then 1 else a.num.natAbs
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_natCast_den (a : ℕ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a := by simp
/-
**Rat.inv_ofNat_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：inv_ofNat_den (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Rat)⁻¹.den = OfNat.of
Nat a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.den_inv`：∀ (a : ℚ), a⁻¹.den = if a.num = 0 then 1 else a.num.natAbs
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem inv_ofNat_den (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℚ)⁻¹.den = OfNat.ofNat a := by
  simp [den_inv, Int.natAbs_eq_iff]
/-
**Rat.den_inv_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_inv_of_ne_zero {q : Rat} (hq : q != 0) : (q⁻¹).den = q.num.natAbs
参数：hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.den_inv`：∀ (a : ℚ), a⁻¹.den = if a.num = 0 then 1 else a.num.natAbs
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem den_inv_of_ne_zero {q : ℚ} (hq : q ≠ 0) : (q⁻¹).den = q.num.natAbs := by
  simp [*]
/-
**Rat.** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, b ≠ 0 → p (a / b) where
  mp h _ _ _ := h _
  mpr h q := by simpa [num_div_den] using h q.num q.den (mod_cast q.den_ne_zero)
/-
**Rat.** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, b ≠ 0 ∧ p (a / b) := by
  simpa using Rat.forall (p := (¬ p ·)).not

/-!
### Denominator as `ℕ+`
-/


section PNatDen

/-- Denominator as `ℕ+`. -/
/-
**Rat.pnatDen** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：pnatDen (x : Rat) : Nat+
参数：x : Rat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den

--- 原说明 ---
Denominator as `ℕ+`.
-/
def pnatDen (x : ℚ) : ℕ+ :=
  ⟨x.den, x.pos⟩

@[simp]
/-
**Rat.coe_pnatDen** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：coe_pnatDen (x : Rat) : (x.pnatDen : Nat) = x.den
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pnatDen (x : ℚ) : (x.pnatDen : ℕ) = x.den :=
  rfl
/-
**Rat.pnatDen_eq_iff_den_eq** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：pnatDen_eq_iff_den_eq {x : Rat} {n : Nat+} : x.pnatDen = n ↔ x.den = ↑n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem pnatDen_eq_iff_den_eq {x : ℚ} {n : ℕ+} : x.pnatDen = n ↔ x.den = ↑n :=
  Subtype.ext_iff

@[simp]
/-
**Rat.pnatDen_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：pnatDen_one : (1 : Rat).pnatDen = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pnatDen_one : (1 : ℚ).pnatDen = 1 :=
  rfl

@[simp]
/-
**Rat.pnatDen_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：pnatDen_zero : (0 : Rat).pnatDen = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pnatDen_zero : (0 : ℚ).pnatDen = 1 :=
  rfl

end PNatDen

end Rat

