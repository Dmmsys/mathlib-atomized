/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Factorization.Defs

/-!
# Roots of natural numbers, rounded up and down

This file defines the flooring and ceiling root of a natural number.
`Nat.floorRoot n a`/`Nat.ceilRoot n a`, the `n`-th flooring/ceiling root of `a`, is the natural
number whose `p`-adic valuation is the floor/ceil of the `p`-adic valuation of `a`.

For example the `2`-nd flooring and ceiling roots of `2^3 * 3^2 * 5` are `2 * 3` and `2^2 * 3 * 5`
respectively. Note this is **not** the `n`-th root of `a` as a real number, rounded up or down.

These operations are respectively the right and left adjoints to the map `a ↦ a ^ n` where `ℕ` is
ordered by divisibility. This is useful because it lets us characterise the numbers `a` whose `n`-th
power divide `n` as the divisors of some fixed number (aka `floorRoot n b`). See
`Nat.pow_dvd_iff_dvd_floorRoot`. Similarly, it lets us characterise the `b` whose `n`-th power is a
multiple of `a` as the multiples of some fixed number (aka `ceilRoot n a`). See
`Nat.dvd_pow_iff_ceilRoot_dvd`.

## TODO

* `norm_num` extension
-/

@[expose] public section

open Finsupp

namespace Nat
variable {a b n : ℕ}

/-- Flooring root of a natural number. This divides the valuation of every prime number rounding
down.

Eg if `n = 2`, `a = 2^3 * 3^2 * 5`, then `floorRoot n a = 2 * 3`.

In order theory terms, this is the upper or right adjoint of the map `a ↦ a ^ n : ℕ → ℕ` where `ℕ`
is ordered by divisibility.

To ensure that the adjunction (`Nat.pow_dvd_iff_dvd_floorRoot`) holds in as many cases as possible,
we special-case the following values:
* `floorRoot 0 a = 0`
* `floorRoot n 0 = 0`
-/
/-
**Nat.floorRoot** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：floorRoot (n a : Nat) : Nat
参数：n a : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flooring root of a natural number. This divides the valuation of every prime num
ber rounding
down.

Eg if `n = 2`, `a = 2^3 * 3^2 * 5`, then `floorRoot n a = 2 * 3`.

In order theory terms, this is the upper or right adjoint of the map `a ↦ a ^ n 
: ℕ → ℕ` where `ℕ`
is ordered by divisibility.

To ensure that the adjunction (`Nat.pow_dvd_iff_dvd_floorRoot`) holds in as many
 cases as possible,
we special-case the following values:
* `floorRoot 0 a = 0`
* `floorRoot n 0 = 0`
-/
def floorRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ (k / n)

/-- The RHS is a noncomputable version of `Nat.floorRoot` with better order-theoretic
properties. -/
/-
**Nat.floorRoot_def** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：floorRoot_def : floorRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorizat
ion ⌊/⌋ n).prod (· ^ ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.prod_mapRange_index`：prod_mapRange_index {f : M -> M'} {hf : f 0
 = 0} {g : α ->₀ M} {h : α -> M' -> N} (h0 : forall a, h a 0 = 1) : (mapRange f 
hf g).prod h = g.…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_floorDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] 
[inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β]
 [i…

--- 原说明 ---
The RHS is a noncomputable version of `Nat.floorRoot` with better order-theoreti
c
properties.
-/
lemma floorRoot_def :
    floorRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌊/⌋ n).prod (· ^ ·) := by
  unfold floorRoot; split_ifs with h <;> simp [Finsupp.floorDiv_def, prod_mapRange_index pow_zero]
/-
**Nat.floorRoot_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), Nat.floorRoot 0 a = 0
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
@[simp] lemma floorRoot_zero_left (a : ℕ) : floorRoot 0 a = 0 := by simp [floorRoot]
/-
**Nat.floorRoot_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.floorRoot 0 = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma floorRoot_zero_right (n : ℕ) : floorRoot n 0 = 0 := by simp [floorRoot]
/-
**Nat.floorRoot_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), Nat.floorRoot 1 a = a
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma floorRoot_one_left (a : ℕ) : floorRoot 1 a = a := by
  simp [floorRoot]; split_ifs <;> simp [*]
/-
**Nat.floorRoot_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → n.floorRoot 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma floorRoot_one_right (hn : n ≠ 0) : floorRoot n 1 = 1 := by simp [floorRoot, hn]
/-
**Nat.floorRoot_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), n.floorRoot (a ^ n) = a
参数：a : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.floorRoot_def`：floorRoot_def : floorRoot n a = if n = 0 ∨ a = 0 then
 0 else (a.factorization ⌊/⌋ n).prod (· ^ ·)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `smul_floorDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst
_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [ins
t_4…
· 使用定理 `instPosSMulMonoNatOfIsOrderedAddMonoid`：∀ {M : Type u_3} [inst : Partial
Order M] [inst_1 : AddCommMonoid M] [IsOrderedAddMonoid M], PosSMulMono ℕ M
· 使用定理 `PosSMulStrictMono.toPosSMulReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : Preorder α] [inst_2 : LinearOrder β] [inst_3 : Zero α]
   [PosSMulStrictMono α β]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
-/
@[simp] lemma floorRoot_pow_self (hn : n ≠ 0) (a : ℕ) : floorRoot n (a ^ n) = a := by
  simp [floorRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]
/-
**Nat.floorRoot_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：floorRoot_ne_zero : floorRoot n a != 0 ↔ n != 0 ∧ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma floorRoot_ne_zero : floorRoot n a ≠ 0 ↔ n ≠ 0 ∧ a ≠ 0 := by
  simp +contextual [floorRoot, not_or]
/-
**Nat.floorRoot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a n : ℕ}, n.floorRoot a = 0 ↔ n = 0 ∨ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `Nat.floorRoot_ne_zero`：floorRoot_ne_zero : floorRoot n a != 0 ↔ n != 0 ∧
 a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma floorRoot_eq_zero : floorRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
  floorRoot_ne_zero.not_right.trans <| by simp only [not_and_or, ne_eq, not_not]
/-
**Nat.factorization_floorRoot** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n a : ℕ), (n.floorRoot a).factorization = a.factorization ⌊/⌋ n
参数：n a : ℕ；n.floorRoot a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.floorRoot_def`：floorRoot_def : floorRoot n a = if n = 0 ∨ a = 0 then
 0 else (a.factorization ⌊/⌋ n).prod (· ^ ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `floorDiv_of_nonpos`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoi
d α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrd
er β] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_floorDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] 
[inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β]
 [i…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.factorization_prod_pow_eq_self_of_le_factorization`：factorization_pr
od_pow_eq_self_of_le_factorization (hf : f <= n.factorization) : (f.prod (· ^ ·)
).factorization = f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_nsmul`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preorder 
M] [AddLeftMono M] {a : M} {n : ℕ}, 0 ≤ a → n ≠ 0 → a ≤ n • a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `smul_floorDiv_le`：smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) <= b
-/
@[simp] lemma factorization_floorRoot (n a : ℕ) :
    (floorRoot n a).factorization = a.factorization ⌊/⌋ n := by
  rw [floorRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  apply a.factorization_prod_pow_eq_self_of_le_factorization
  exact le_self_nsmul (by simp) (by lia) |>.trans <| smul_floorDiv_le (by lia)

/-- Galois connection between `a ↦ a ^ n : ℕ → ℕ` and `floorRoot n : ℕ → ℕ` where `ℕ` is ordered
by divisibility. -/
/-
**Nat.pow_dvd_iff_dvd_floorRoot** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_dvd_iff_dvd_floorRoot : a ^ n ∣ b ↔ a ∣ floorRoot n b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.floorRoot_zero_left`：∀ (a : ℕ), Nat.floorRoot 0 a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floorRoot_zero_right`：∀ (n : ℕ), n.floorRoot 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.floorRoot_ne_zero`：floorRoot_ne_zero : floorRoot n a != 0 ↔ n != 0 ∧
 a != 0
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.factorization_floorRoot`：∀ (n a : ℕ), (n.floorRoot a).factorization 
= a.factorization ⌊/⌋ n
· 使用定理 `le_floorDiv_iff_smul_le`：∀ {α : Type u_2} {β : Type u_3} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : Parti
alOrder β] [i…
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Galois connection between `a ↦ a ^ n : ℕ → ℕ` and `floorRoot n : ℕ → ℕ` where `ℕ
` is ordered
by divisibility.
-/
lemma pow_dvd_iff_dvd_floorRoot : a ^ n ∣ b ↔ a ∣ floorRoot n b := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  obtain rfl | ha := eq_or_ne a 0
  · simp [hn]
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb,
    ← factorization_le_iff_dvd ha (floorRoot_ne_zero.2 ⟨hn, hb⟩), factorization_pow,
    factorization_floorRoot, le_floorDiv_iff_smul_le (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]
/-
**Nat.floorRoot_pow_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：floorRoot_pow_dvd : floorRoot n a ^ n ∣ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.pow_dvd_iff_dvd_floorRoot`：pow_dvd_iff_dvd_floorRoot : a ^ n ∣ b ↔ a
 ∣ floorRoot n b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
lemma floorRoot_pow_dvd : floorRoot n a ^ n ∣ a := pow_dvd_iff_dvd_floorRoot.2 dvd_rfl

/-- Ceiling root of a natural number. This divides the valuation of every prime number rounding up.

Eg if `n = 3`, `a = 2^4 * 3^2 * 5`, then `ceilRoot n a = 2^2 * 3 * 5`.

In order theory terms, this is the lower or left adjoint of the map `a ↦ a ^ n : ℕ → ℕ` where `ℕ`
is ordered by divisibility.

To ensure that the adjunction (`Nat.dvd_pow_iff_ceilRoot_dvd`) holds in as many cases as possible,
we special-case the following values:
* `ceilRoot 0 a = 0` (this one is not strictly necessary)
* `ceilRoot n 0 = 0`
-/
/-
**Nat.ceilRoot** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ceilRoot (n a : Nat) : Nat
参数：n a : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ceiling root of a natural number. This divides the valuation of every prime numb
er rounding up.

Eg if `n = 3`, `a = 2^4 * 3^2 * 5`, then `ceilRoot n a = 2^2 * 3 * 5`.

In order theory terms, this is the lower or left adjoint of the map `a ↦ a ^ n :
 ℕ → ℕ` where `ℕ`
is ordered by divisibility.

To ensure that the adjunction (`Nat.dvd_pow_iff_ceilRoot_dvd`) holds in as many 
cases as possible,
we special-case the following values:
* `ceilRoot 0 a = 0` (this one is not strictly necessary)
* `ceilRoot n 0 = 0`
-/
def ceilRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ ((k + n - 1) / n)

/-- The RHS is a noncomputable version of `Nat.ceilRoot` with better order-theoretic
properties. -/
/-
**Nat.ceilRoot_def** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ceilRoot_def : ceilRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorizatio
n ⌈/⌉ n).prod (· ^ ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.prod_mapRange_index`：prod_mapRange_index {f : M -> M'} {hf : f 0
 = 0} {g : α ->₀ M} {h : α -> M' -> N} (h0 : forall a, h a 0 = 1) : (mapRange f 
hf g).prod h = g.…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [
inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] 
[i…

--- 原说明 ---
The RHS is a noncomputable version of `Nat.ceilRoot` with better order-theoretic
properties.
-/
lemma ceilRoot_def :
    ceilRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌈/⌉ n).prod (· ^ ·) := by
  unfold ceilRoot
  split_ifs with h <;>
    simp [Finsupp.ceilDiv_def, prod_mapRange_index pow_zero, Nat.ceilDiv_eq_add_pred_div]
/-
**Nat.ceilRoot_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), Nat.ceilRoot 0 a = 0
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
@[simp] lemma ceilRoot_zero_left (a : ℕ) : ceilRoot 0 a = 0 := by simp [ceilRoot]
/-
**Nat.ceilRoot_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.ceilRoot 0 = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma ceilRoot_zero_right (n : ℕ) : ceilRoot n 0 = 0 := by simp [ceilRoot]
/-
**Nat.ceilRoot_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a : ℕ), Nat.ceilRoot 1 a = a
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma ceilRoot_one_left (a : ℕ) : ceilRoot 1 a = a := by
  simp [ceilRoot]; split_ifs <;> simp [*]
/-
**Nat.ceilRoot_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → n.ceilRoot 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ceilRoot_one_right (hn : n ≠ 0) : ceilRoot n 1 = 1 := by simp [ceilRoot, hn]
/-
**Nat.ceilRoot_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), n.ceilRoot (a ^ n) = a
参数：a : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.ceilRoot_def`：ceilRoot_def : ceilRoot n a = if n = 0 ∨ a = 0 then 0 
else (a.factorization ⌈/⌉ n).prod (· ^ ·)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `smul_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst_
1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] [inst
_4…
· 使用定理 `instPosSMulMonoNatOfIsOrderedAddMonoid`：∀ {M : Type u_3} [inst : Partial
Order M] [inst_1 : AddCommMonoid M] [IsOrderedAddMonoid M], PosSMulMono ℕ M
· 使用定理 `PosSMulStrictMono.toPosSMulReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : Preorder α] [inst_2 : LinearOrder β] [inst_3 : Zero α]
   [PosSMulStrictMono α β]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
-/
@[simp] lemma ceilRoot_pow_self (hn : n ≠ 0) (a : ℕ) : ceilRoot n (a ^ n) = a := by
  simp [ceilRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]
/-
**Nat.ceilRoot_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ceilRoot_ne_zero : ceilRoot n a != 0 ↔ n != 0 ∧ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.ceilRoot_def`：ceilRoot_def : ceilRoot n a = if n = 0 ∨ a = 0 then 0 
else (a.factorization ⌈/⌉ n).prod (· ^ ·)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `zero_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [
inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] 
[i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ceilRoot_ne_zero : ceilRoot n a ≠ 0 ↔ n ≠ 0 ∧ a ≠ 0 := by
  simp +contextual [ceilRoot_def, not_or]
/-
**Nat.ceilRoot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a n : ℕ}, n.ceilRoot a = 0 ↔ n = 0 ∨ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `Nat.ceilRoot_ne_zero`：ceilRoot_ne_zero : ceilRoot n a != 0 ↔ n != 0 ∧ a 
!= 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ceilRoot_eq_zero : ceilRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
  ceilRoot_ne_zero.not_right.trans <| by simp only [not_and_or, ne_eq, not_not]
/-
**Nat.factorization_ceilRoot** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n a : ℕ), (n.ceilRoot a).factorization = a.factorization ⌈/⌉ n
参数：n a : ℕ；n.ceilRoot a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.ceilRoot_def`：ceilRoot_def : ceilRoot n a = if n = 0 ∨ a = 0 then 0 
else (a.factorization ⌈/⌉ n).prod (· ^ ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `ceilDiv_of_nonpos`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid
 α] [inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrde
r β] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_ceilDiv`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMonoid α] [
inst_1 : PartialOrder α] [inst_2 : AddCommMonoid β]   [inst_3 : PartialOrder β] 
[i…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.prod_pow_factorization_eq_self`：prod_pow_factorization_eq_self (hf :
 forall p in f.support, Prime p) : (f.prod (· ^ ·)).factorization = f
· 使用引理 `Finsupp.support_ceilDiv_subset`：support_ceilDiv_subset : (f ⌈/⌉ a).suppo
rt subseteq f.support
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
@[simp] lemma factorization_ceilRoot (n a : ℕ) :
    (ceilRoot n a).factorization = a.factorization ⌈/⌉ n := by
  rw [ceilRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_ceilDiv_subset hp
  exact this.1

/-- Galois connection between `ceilRoot n : ℕ → ℕ` and `a ↦ a ^ n : ℕ → ℕ` where `ℕ` is ordered
by divisibility.

Note that this cannot possibly hold for `n = 0`, regardless of the value of `ceilRoot 0 a`, because
the statement reduces to `a = 1 ↔ ceilRoot 0 a ∣ b`, which is false for e.g. `a = 0`,
`b = ceilRoot 0 a`. -/
/-
**Nat.dvd_pow_iff_ceilRoot_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：dvd_pow_iff_ceilRoot_dvd (hn : n != 0) : a ∣ b ^ n ↔ ceilRoot n a ∣ b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.ceilRoot_zero_right`：∀ (n : ℕ), n.ceilRoot 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.ceilRoot_ne_zero`：ceilRoot_ne_zero : ceilRoot n a != 0 ↔ n != 0 ∧ a 
!= 0
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.factorization_ceilRoot`：∀ (n a : ℕ), (n.ceilRoot a).factorization = 
a.factorization ⌈/⌉ n
· 使用引理 `ceilDiv_le_iff_le_smul`：ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a <=
 c ↔ b <= a • c
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Galois connection between `ceilRoot n : ℕ → ℕ` and `a ↦ a ^ n : ℕ → ℕ` where `ℕ`
 is ordered
by divisibility.

Note that this cannot possibly hold for `n = 0`, regardless of the value of `cei
lRoot 0 a`, because
the statement reduces to `a = 1 ↔ ceilRoot 0 a ∣ b`, which is false for e.g. `a 
= 0`,
`b = ceilRoot 0 a`.
-/
lemma dvd_pow_iff_ceilRoot_dvd (hn : n ≠ 0) : a ∣ b ^ n ↔ ceilRoot n a ∣ b := by
  obtain rfl | ha := eq_or_ne a 0
  · aesop
  obtain rfl | hb := eq_or_ne b 0
  · simp [hn]
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ hb),
    ← factorization_le_iff_dvd (ceilRoot_ne_zero.2 ⟨hn, ha⟩) hb, factorization_pow,
    factorization_ceilRoot, ceilDiv_le_iff_le_smul (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]
/-
**Nat.dvd_ceilRoot_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：dvd_ceilRoot_pow (hn : n != 0) : a ∣ ceilRoot n a ^ n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.dvd_pow_iff_ceilRoot_dvd`：dvd_pow_iff_ceilRoot_dvd (hn : n != 0) : a
 ∣ b ^ n ↔ ceilRoot n a ∣ b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
lemma dvd_ceilRoot_pow (hn : n ≠ 0) : a ∣ ceilRoot n a ^ n :=
  (dvd_pow_iff_ceilRoot_dvd hn).2 dvd_rfl

end Nat

