/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Order.Nat

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

@[expose] public section

assert_not_exists MulAction IsOrderedMonoid

variable {F ι α β : Type*}

namespace NNRat
variable [DivisionSemiring α] {q r : ℚ≥0}

/-
**NNRat.cast_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma cast_natCast (n : ℕ) : ((n : ℚ≥0) : α) = n := by simp [cast_def]
/-
**NNRat.cast_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ) [inst_1 : n.AtLeastTw
o], ↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
-/
@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : ℚ≥0) = (ofNat(n) : α) := cast_natCast _
/-
**NNRat.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
@[simp, norm_cast] lemma cast_zero : ((0 : ℚ≥0) : α) = 0 := (cast_natCast _).trans Nat.cast_zero
/-
**NNRat.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
@[simp, norm_cast] lemma cast_one : ((1 : ℚ≥0) : α) = 1 := (cast_natCast _).trans Nat.cast_one
/-
**NNRat.cast_commute** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_commute (q : Rat>=0) (a : α) : Commute (↑q) a
参数：q : Rat>=0；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `Commute.div_left`：div_left (hac : Commute a c) (hbc : Commute b c) : Com
mute (a / b) c
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
-/
lemma cast_commute (q : ℚ≥0) (a : α) : Commute (↑q) a := by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)
/-
**NNRat.commute_cast** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：commute_cast (a : α) (q : Rat>=0) : Commute a q
参数：a : α；q : Rat>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用引理 `NNRat.cast_commute`：cast_commute (q : Rat>=0) (a : α) : Commute (↑q) a
-/
lemma commute_cast (a : α) (q : ℚ≥0) : Commute a q := (cast_commute ..).symm
/-
**NNRat.cast_comm** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_comm (q : Rat>=0) (a : α) : q * a = a * q
参数：q : Rat>=0；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNRat.cast_commute`：cast_commute (q : Rat>=0) (a : α) : Commute (↑q) a
-/
lemma cast_comm (q : ℚ≥0) (a : α) : q * a = a * q := cast_commute _ _

set_option backward.isDefEq.respectTransparency false in
/-
**NNRat.cast_divNat_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionSemiring α] (a : ℕ) {b : ℕ}, ↑b ≠ 0 → ↑(N
NRat.divNat a b) = ↑a / ↑b
参数：a : ℕ；NNRat.divNat a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.num_nonneg`：∀ {q : ℚ}, 0 ≤ q.num ↔ 0 ≤ q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.den_dvd`：den_dvd (a b : Int) : ((a /. b).den : Int) ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `Commute.div_eq_div_iff`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a b
 c d : G₀},   Commute b d → b ≠ 0 → d ≠ 0 → (a / b = c / d ↔ a * d = c * b)
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `NNRat.divNat_inj`：divNat_inj (h₁ : d₁ != 0) (h₂ : d₂ != 0) : divNat n₁ d
₁ = divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
@[norm_cast] lemma cast_divNat_of_ne_zero (a : ℕ) {b : ℕ} (hb : (b : α) ≠ 0) :
    divNat a b = (a / b : α) := by
  rcases e : divNat a b with ⟨⟨n, d, h, c⟩, hn⟩
  rw [← Rat.num_nonneg] at hn
  lift n to ℕ using hn
  have hd : (d : α) ≠ 0 := by
    refine fun hd ↦ hb ?_
    have : Rat.divInt a b = _ := congr_arg NNRat.cast e
    obtain ⟨k, rfl⟩ : d ∣ b := by simpa [Int.natCast_dvd_natCast, this] using Rat.den_dvd a b
    simp [*]
  have hb' : b ≠ 0 := by rintro rfl; exact hb Nat.cast_zero
  simp_rw [Rat.mk_eq_divInt, mk_divInt, divNat_inj hb' h] at e
  rw [cast_def]
  dsimp
  rw [Commute.div_eq_div_iff _ hd hb]
  · norm_cast
    rw [e]
  exact b.commute_cast _

@[norm_cast]
/-
**NNRat.cast_add_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_add_of_ne_zero (hq : (q.den : α) != 0) (hr : (r.den : α) != 0) : ↑(q 
+ r) = (q + r : α)
参数：hq : (q.den : α) != 0；hr : (r.den : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.add_def`：add_def (q r : Rat>=0) : q + r = divNat (q.num * r.den + 
r.num * q.den) (q.den * r.den)
· 使用定理 `NNRat.cast_divNat_of_ne_zero`：∀ {α : Type u_3} [inst : DivisionSemiring 
α] (a : ℕ) {b : ℕ}, ↑b ≠ 0 → ↑(NNRat.divNat a b) = ↑a / ↑b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Commute.div_add_div`：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c
 d : K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + 
b * c) / …
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
lemma cast_add_of_ne_zero (hq : (q.den : α) ≠ 0) (hr : (r.den : α) ≠ 0) :
    ↑(q + r) = (q + r : α) := by
  rw [add_def, cast_divNat_of_ne_zero, cast_def, cast_def, mul_comm _ q.den,
    (Nat.commute_cast _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]
/-
**NNRat.cast_mul_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_mul_of_ne_zero (hq : (q.den : α) != 0) (hr : (r.den : α) != 0) : ↑(q 
* r) = (q * r : α)
参数：hq : (q.den : α) != 0；hr : (r.den : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.mul_def`：mul_def (q r : Rat>=0) : q * r = divNat (q.num * r.num) (
q.den * r.den)
· 使用定理 `NNRat.cast_divNat_of_ne_zero`：∀ {α : Type u_3} [inst : DivisionSemiring 
α] (a : ℕ) {b : ℕ}, ↑b ≠ 0 → ↑(NNRat.divNat a b) = ↑a / ↑b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `Commute.div_mul_div_comm`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a 
b c d : G},   Commute b d → Commute b⁻¹ c → a / b * (c / d) = a * c / (b * d)
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma cast_mul_of_ne_zero (hq : (q.den : α) ≠ 0) (hr : (r.den : α) ≠ 0) :
    ↑(q * r) = (q * r : α) := by
  rw [mul_def, cast_divNat_of_ne_zero, cast_def, cast_def,
    (Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

@[norm_cast]
/-
**NNRat.cast_inv_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_inv_of_ne_zero (hq : (q.num : α) != 0) : (q⁻¹ : Rat>=0) = (q⁻¹ : α)
参数：hq : (q.num : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.inv_def`：inv_def (q : Rat>=0) : q⁻¹ = divNat q.den q.num
· 使用定理 `NNRat.cast_divNat_of_ne_zero`：∀ {α : Type u_3} [inst : DivisionSemiring 
α] (a : ℕ) {b : ℕ}, ↑b ≠ 0 → ↑(NNRat.divNat a b) = ↑a / ↑b
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
lemma cast_inv_of_ne_zero (hq : (q.num : α) ≠ 0) : (q⁻¹ : ℚ≥0) = (q⁻¹ : α) := by
  rw [inv_def, cast_divNat_of_ne_zero _ hq, cast_def, inv_div]

@[norm_cast]
/-
**NNRat.cast_div_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：cast_div_of_ne_zero (hq : (q.den : α) != 0) (hr : (r.num : α) != 0) : ↑(q 
/ r) = (q / r : α)
参数：hq : (q.den : α) != 0；hr : (r.num : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.div_def`：div_def (p q : Rat>=0) : p / q = divNat (p.num * q.den) (
p.den * q.num)
· 使用定理 `NNRat.cast_divNat_of_ne_zero`：∀ {α : Type u_3} [inst : DivisionSemiring 
α] (a : ℕ) {b : ℕ}, ↑b ≠ 0 → ↑(NNRat.divNat a b) = ↑a / ↑b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Commute.div_mul_div_comm`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a 
b c d : G},   Commute b d → Commute b⁻¹ c → a / b * (c / d) = a * c / (b * d)
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma cast_div_of_ne_zero (hq : (q.den : α) ≠ 0) (hr : (r.num : α) ≠ 0) :
    ↑(q / r) = (q / r : α) := by
  rw [div_def, cast_divNat_of_ne_zero, cast_def, cast_def, div_eq_mul_inv (_ / _),
    inv_div, (Nat.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr

end NNRat

namespace Rat

variable [DivisionRing α] {p q : ℚ}

@[simp, norm_cast]
/-
**Rat.cast_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_intCast (n : Int) : ((n : Rat) : α) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem cast_intCast (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_def _).trans <| show (n / (1 : ℕ) : α) = n by rw [Nat.cast_one, div_one]

@[simp, norm_cast]
/-
**Rat.cast_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_natCast (n : Nat) : ((n : Rat) : α) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem cast_natCast (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_natCast, cast_intCast, Int.cast_natCast]
/-
**Rat.cast_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1 : n.AtLeastTwo], 
↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℚ) : α) = (ofNat(n) : α) := by
  simp [cast_def]

@[simp, norm_cast]
/-
**Rat.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_zero : ((0 : Rat) : α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_intCast _).trans Int.cast_zero

@[simp, norm_cast]
/-
**Rat.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_one : ((1 : Rat) : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_intCast _).trans Int.cast_one
/-
**Rat.cast_commute** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_commute (r : Rat) (a : α) : Commute (↑r) a
参数：r : Rat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `Commute.div_left`：div_left (hac : Commute a c) (hbc : Commute b c) : Com
mute (a / b) c
· 使用定理 `Int.cast_commute`：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : 
α), Commute (↑n) a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
-/
theorem cast_commute (r : ℚ) (a : α) : Commute (↑r) a := by
  simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)
/-
**Rat.cast_comm** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_comm (r : Rat) (a : α) : (r : α) * a = a * r
参数：r : Rat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Rat.cast_commute`：cast_commute (r : Rat) (a : α) : Commute (↑r) a
-/
theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).eq
/-
**Rat.commute_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：commute_cast (a : α) (r : Rat) : Commute a r
参数：a : α；r : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Rat.cast_commute`：cast_commute (r : Rat) (a : α) : Commute (↑r) a
-/
theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm

@[norm_cast]
/-
**Rat.cast_divInt_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_divInt_of_ne_zero (a : Int) {b : Int} (b0 : (b : α) != 0) : (a /. b :
 α) = a / b
参数：a : Int；b0 : (b : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.den_dvd`：den_dvd (a b : Int) : ((a /. b).den : Int) ∣ b
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.divInt_eq_divInt_iff`：∀ {d₁ d₂ n₁ n₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → (Rat.di
vInt n₁ d₁ = Rat.divInt n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Rat.mk_eq_divInt`：∀ {num : ℤ} {den : ℕ} {nz : den ≠ 0} {c : num.natAbs.C
oprime den},   { num := num, den := den, den_nz := nz, reduced := c } = Rat.divI
nt num…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 32 条，此处仅展示前 30 条）
-/
lemma cast_divInt_of_ne_zero (a : ℤ) {b : ℤ} (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b := by
  have b0' : b ≠ 0 := by
    refine mt ?_ b0
    simp +contextual
  rcases e : a /. b with ⟨n, d, h, c⟩
  have d0 : (d : α) ≠ 0 := by
    intro d0
    have dd := den_dvd a b
    rcases show (d : ℤ) ∣ b by rwa [e] at dd with ⟨k, ke⟩
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_natCast]
    rw [d0, zero_mul] at this
    contradiction
  rw [mk_eq_divInt] at e
  have := congr_arg ((↑) : ℤ → α)
    ((divInt_eq_divInt_iff b0' <| ne_of_gt <| Int.natCast_pos.2 h.bot_lt).1 e)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast] at this
  rw [eq_comm, cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).eq,
    ← mul_assoc, this, mul_assoc, mul_inv_cancel₀ b0, mul_one]

@[norm_cast]
/-
**Rat.cast_mkRat_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_mkRat_of_ne_zero (a : Int) {b : Nat} (hb : (b : α) != 0) : (mkRat a b
 : α) = a / b
参数：a : Int；hb : (b : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mkRat_eq_divInt`：mkRat_eq_divInt (n d) : mkRat n d = n /. d
· 使用引理 `Rat.cast_divInt_of_ne_zero`：cast_divInt_of_ne_zero (a : Int) {b : Int} (
b0 : (b : α) != 0) : (a /. b : α) = a / b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
lemma cast_mkRat_of_ne_zero (a : ℤ) {b : ℕ} (hb : (b : α) ≠ 0) : (mkRat a b : α) = a / b := by
  rw [Rat.mkRat_eq_divInt, cast_divInt_of_ne_zero, Int.cast_natCast]; rwa [Int.cast_natCast]

@[norm_cast]
/-
**Rat.cast_add_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_add_of_ne_zero {q r : Rat} (hq : (q.den : α) != 0) (hr : (r.den : α) 
!= 0) : (q + r : Rat) = (q + r : α)
参数：hq : (q.den : α) != 0；hr : (r.den : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.add_def'`：∀ (a b : ℚ), a + b = mkRat (a.num * ↑b.den + b.num * ↑a.de
n) (a.den * b.den)
· 使用引理 `Rat.cast_mkRat_of_ne_zero`：cast_mkRat_of_ne_zero (a : Int) {b : Nat} (hb
 : (b : α) != 0) : (mkRat a b : α) = a / b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Commute.div_add_div`：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c
 d : K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + 
b * c) / …
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
lemma cast_add_of_ne_zero {q r : ℚ} (hq : (q.den : α) ≠ 0) (hr : (r.den : α) ≠ 0) :
    (q + r : ℚ) = (q + r : α) := by
  rw [add_def', cast_mkRat_of_ne_zero, cast_def, cast_def, mul_comm r.num,
    (Nat.cast_commute _ _).div_add_div (Nat.commute_cast _ _) hq hr]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hq hr
/-
**Rat.cast_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = -↑q
参数：q : ℚ；-q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma cast_neg (q : ℚ) : ↑(-q) = (-q : α) := by simp [cast_def, neg_div]

set_option backward.isDefEq.respectTransparency false in
/-
**Rat.cast_sub_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] {p q : ℚ}, ↑p.den ≠ 0 → ↑q.den ≠ 
0 → ↑(p - q) = ↑p - ↑q
参数：p - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Rat.cast_add_of_ne_zero`：cast_add_of_ne_zero {q r : Rat} (hq : (q.den : 
α) != 0) (hr : (r.den : α) != 0) : (q + r : Rat) = (q + r : α)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma cast_sub_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    ↑(p - q) = (p - q : α) := by simp [sub_eq_add_neg, cast_add_of_ne_zero, hp, hq]
/-
**Rat.cast_mul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] {p q : ℚ}, ↑p.den ≠ 0 → ↑q.den ≠ 
0 → ↑(p * q) = ↑p * ↑q
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mul_eq_mkRat`：mul_eq_mkRat (q r : Rat) : q * r = mkRat (q.num * r.nu
m) (q.den * r.den)
· 使用引理 `Rat.cast_mkRat_of_ne_zero`：cast_mkRat_of_ne_zero (a : Int) {b : Nat} (hb
 : (b : α) != 0) : (mkRat a b : α) = a / b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `Commute.div_mul_div_comm`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a 
b c d : G},   Commute b d → Commute b⁻¹ c → a / b * (c / d) = a * c / (b * d)
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
-/
@[norm_cast] lemma cast_mul_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    ↑(p * q) = (p * q : α) := by
  rw [mul_eq_mkRat, cast_mkRat_of_ne_zero, cast_def, cast_def,
    (Nat.commute_cast _ _).div_mul_div_comm (Int.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

@[norm_cast]
/-
**Rat.cast_inv_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_inv_of_ne_zero (hq : (q.num : α) != 0) : ↑(q⁻¹) = (q⁻¹ : α)
参数：hq : (q.num : α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.inv_def`：∀ (a : ℚ), a⁻¹ = Rat.divInt (↑a.den) a.num
· 使用引理 `Rat.cast_divInt_of_ne_zero`：cast_divInt_of_ne_zero (a : Int) {b : Int} (
b0 : (b : α) != 0) : (a /. b : α) = a / b
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
lemma cast_inv_of_ne_zero (hq : (q.num : α) ≠ 0) : ↑(q⁻¹) = (q⁻¹ : α) := by
  rw [inv_def, cast_divInt_of_ne_zero _ hq, cast_def, inv_div, Int.cast_natCast]
/-
**Rat.cast_div_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {α : Type u_3} [inst : DivisionRing α] {p q : ℚ}, ↑p.den ≠ 0 → ↑q.num ≠ 
0 → ↑(p / q) = ↑p / ↑q
参数：p / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.div_def'`：div_def' (q r : Rat) : q / r = (q.num * r.den) /. (q.den *
 r.num)
· 使用引理 `Rat.cast_divInt_of_ne_zero`：cast_divInt_of_ne_zero (a : Int) {b : Int} (
b0 : (b : α) != 0) : (a /. b : α) = a / b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Commute.div_mul_div_comm`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a 
b c d : G},   Commute b d → Commute b⁻¹ c → a / b * (c / d) = a * c / (b * d)
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
@[norm_cast] lemma cast_div_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.num : α) ≠ 0) :
    ↑(p / q) = (p / q : α) := by
  rw [div_def', cast_divInt_of_ne_zero, cast_def, cast_def, div_eq_mul_inv (_ / _), inv_div,
    (Int.commute_cast _ _).div_mul_div_comm (Nat.commute_cast _ _)]
  · push_cast
    rfl
  · push_cast
    exact mul_ne_zero hp hq

end Rat

open Rat

variable [FunLike F α β]

/-
**map_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {F : Type u_1} {α : Type u_3} {β : Type u_4} [inst : FunLike F α β] [ins
t_1 : DivisionSemiring α]   [inst_2 : DivisionSemiring β] [RingHomClass F α β] (
f : F) (q : ℚ≥0), f ↑q = ↑q
参数：f : F；q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_nnratCast [DivisionSemiring α] [DivisionSemiring β] [RingHomClass F α β] (f : F)
    (q : ℚ≥0) : f q = q := by simp_rw [NNRat.cast_def, map_div₀, map_natCast]

@[simp]
/-
**eq_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_nnratCast [DivisionSemiring α] [FunLike F Rat>=0 α] [RingHomClass F Rat
>=0 α] (f : F) (q : Rat>=0) : f q = q
参数：f : F；q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nnratCast`：∀ {F : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Fu
nLike F α β] [inst_1 : DivisionSemiring α]   [inst_2 : DivisionSemiring β] [Ring
Hom…
· 使用定理 `NNRat.cast_id`：∀ (n : ℚ≥0), ↑n = n
-/
lemma eq_nnratCast [DivisionSemiring α] [FunLike F ℚ≥0 α] [RingHomClass F ℚ≥0 α] (f : F) (q : ℚ≥0) :
    f q = q := by rw [← map_nnratCast f, NNRat.cast_id]

@[simp]
/-
**map_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F)
 (q : Rat) : f q = q
参数：f : F；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : ℚ) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]
/-
**eq_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [inst_1 : FunLike 
F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
参数：f : F；q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用定理 `Rat.cast_id`：∀ (n : ℚ), ↑n = n
-/
@[simp] lemma eq_ratCast [DivisionRing α] [FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ) :
    f q = q := by rw [← map_ratCast f, Rat.cast_id]

namespace MonoidWithZeroHomClass

variable {M₀ : Type*} [MonoidWithZero M₀]

section NNRat
variable [FunLike F ℚ≥0 M₀] [MonoidWithZeroHomClass F ℚ≥0 M₀] {f g : F}

/-- If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the naturals then they are equal. -/
/-
**MonoidWithZeroHomClass.ext_nnrat'** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom
Class`。
形式化陈述：ext_nnrat' (h : forall n : Nat, f n = g n) : f = g
参数：h : forall n : Nat, f n = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.num_div_den`：num_div_den (q : Rat>=0) : (q.num : Rat>=0) / q.den =
 q
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_on_inv₀`：eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h 
: f a = g a) : f a⁻¹ = g a⁻¹

--- 原说明 ---
If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the naturals then they 
are equal.
-/
lemma ext_nnrat' (h : ∀ n : ℕ, f n = g n) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, eq_on_inv₀ f g]
    apply h

/-- If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the naturals then they are equal.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
/-
**MonoidWithZeroHomClass.ext_nnrat** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHomC
lass`。
形式化陈述：ext_nnrat {f g : Rat>=0 ->*₀ M₀} (h : f.comp (.ofClass (Nat.castRingHom Ra
t>=0)) = g.comp (.ofClass (Nat.castRingHom Rat>=0))) : f = g
参数：h : f.comp (.ofClass (Nat.castRingHom Rat>=0)) = g.comp (.ofClass (Nat.castRi
ngHom Rat>=0))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `MonoidWithZeroHomClass.ext_nnrat'`：ext_nnrat' (h : forall n : Nat, f n =
 g n) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the naturals then they 
are equal.

See note [partially-applied ext lemmas] for why `comp` is used here.
-/
lemma ext_nnrat {f g : ℚ≥0 →*₀ M₀} (h : f.comp (.ofClass (Nat.castRingHom ℚ≥0)) =
    g.comp (.ofClass (Nat.castRingHom ℚ≥0))) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun h

/-- If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the positive naturals then they are
equal. -/
/-
**MonoidWithZeroHomClass.ext_nnrat_on_pnat** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWith
ZeroHomClass`。
形式化陈述：ext_nnrat_on_pnat (same_on_pnat : forall n : Nat, 0 < n -> f n = g n) : f 
= g
参数：same_on_pnat : forall n : Nat, 0 < n -> f n = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHomClass.ext_nnrat'`：ext_nnrat' (h : forall n : Nat, f n =
 g n) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ext_nat''`：ext_nat'' [ZeroHomClass F Nat A] (f g : F) (h_pos : forall {n
 : Nat}, 0 < n -> f n = g n) : f = g
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the positive naturals t
hen they are
equal.
-/
lemma ext_nnrat_on_pnat (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun <| ext_nat''
    ((.ofClass f : ℚ≥0 →*₀ M₀).comp (.ofClass (Nat.castRingHom ℚ≥0)))
    ((.ofClass g : ℚ≥0 →*₀ M₀).comp (.ofClass (Nat.castRingHom ℚ≥0))) (by simpa)

end NNRat

section Rat
variable [FunLike F ℚ M₀] [MonoidWithZeroHomClass F ℚ M₀] {f g : F}

/-- If monoid with zero homs `f` and `g` from `ℚ` agree on the integers then they are equal. -/
/-
**MonoidWithZeroHomClass.ext_rat'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHomCl
ass`。
形式化陈述：ext_rat' (h : forall m : Int, f m = g m) : f = g
参数：h : forall m : Int, f m = g m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_on_inv₀`：eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h 
: f a = g a) : f a⁻¹ = g a⁻¹

--- 原说明 ---
If monoid with zero homs `f` and `g` from `ℚ` agree on the integers then they ar
e equal.
-/
theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, ← Int.cast_natCast,
      eq_on_inv₀ f g]
    apply h

/-- If monoid with zero homs `f` and `g` from `ℚ` agree on the integers then they are equal.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
/-
**MonoidWithZeroHomClass.ext_rat** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHomCla
ss`。
形式化陈述：ext_rat {f g : Rat ->*₀ M₀} (h : f.comp (.ofClass (Int.castRingHom Rat)) =
 g.comp (.ofClass (Int.castRingHom Rat))) : f = g
参数：h : f.comp (.ofClass (Int.castRingHom Rat)) = g.comp (.ofClass (Int.castRingH
om Rat))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MonoidWithZeroHomClass.ext_rat'`：ext_rat' (h : forall m : Int, f m = g m
) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If monoid with zero homs `f` and `g` from `ℚ` agree on the integers then they ar
e equal.

See note [partially-applied ext lemmas] for why `comp` is used here.
-/
theorem ext_rat {f g : ℚ →*₀ M₀}
    (h : f.comp (.ofClass (Int.castRingHom ℚ)) = g.comp (.ofClass (Int.castRingHom ℚ))) : f = g :=
  ext_rat' <| DFunLike.congr_fun h

/-- If monoid with zero homs `f` and `g` from `ℚ` agree on the positive naturals and `-1` then
they are equal. -/
/-
**MonoidWithZeroHomClass.ext_rat_on_pnat** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZe
roHomClass`。
形式化陈述：ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1)) (same_on_pnat : forall
 n : Nat, 0 < n -> f n = g n) : f = g
参数：same_on_neg_one : f (-1) = g (-1)；same_on_pnat : forall n : Nat, 0 < n -> f n
 = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.ext_rat'`：ext_rat' (h : forall m : Int, f m = g m
) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ext_int'`：ext_int' [MonoidWithZero α] [FunLike F Int α] [MonoidWithZeroH
omClass F Int α] {f g : F} (h_neg_one : f (-1) = g (-1)) (h_pos : forall n : N…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n

--- 原说明 ---
If monoid with zero homs `f` and `g` from `ℚ` agree on the positive naturals and
 `-1` then
they are equal.
-/
theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <|
    DFunLike.congr_fun <|
      show
        (.ofClass f : ℚ →*₀ M₀).comp (.ofClass (Int.castRingHom ℚ)) =
          (.ofClass g : ℚ →*₀ M₀).comp (.ofClass (Int.castRingHom ℚ))
        from ext_int' (by simpa) (by simpa)

end Rat
end MonoidWithZeroHomClass

/-- Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is a division ring,
then this lemma follows from `eq_ratCast`. -/
/-
**RingHom.ext_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F Rat R] [RingHomClass F
 Rat R] (f g : F) : f = g
参数：f g : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.ext_rat'`：ext_rat' (h : forall m : Int, f m = g m
) : f = g
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g

--- 原说明 ---
Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is 
a division ring,
then this lemma follows from `eq_ratCast`.
-/
theorem RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F ℚ R] [RingHomClass F ℚ R] (f g : F) :
    f = g :=
  MonoidWithZeroHomClass.ext_rat' <|
    RingHom.congr_fun <|
      ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int ((g : ℚ →+* R).comp (Int.castRingHom ℚ))
/-
**NNRat.subsingleton_ringHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (Rat>=0
 ->+* R) where allEq f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHomClass.ext_nnrat'`：ext_nnrat' (h : forall n : Nat, f n =
 g n) : f = g
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ≥0 →+* R) where
  allEq f g := MonoidWithZeroHomClass.ext_nnrat' <| by simp
/-
**Rat.subsingleton_ringHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (Rat ->+*
 R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext_rat`：RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F Rat
 R] [RingHomClass F Rat R] (f g : F) : f = g
-/
instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
