/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# A `norm_num` extension for Jacobi and Legendre symbols

We extend the `norm_num` tactic so that it can be used to provably compute
the value of the Jacobi symbol `J(a | b)` or the Legendre symbol `legendreSym p a` when
the arguments are numerals.

## Implementation notes

We use the Law of Quadratic Reciprocity for the Jacobi symbol to compute the value of `J(a | b)`
efficiently, roughly comparable in effort with the Euclidean algorithm for the computation
of the gcd of `a` and `b`. More precisely, the computation is done in the following steps.

* Use `J(a | 0) = 1` (an artifact of the definition) and `J(a | 1) = 1` to deal
  with corner cases.

* Use `J(a | b) = J(a % b | b)` to reduce to the case that `a` is a natural number.
  We define a version of the Jacobi symbol restricted to natural numbers for use in
  the following steps; see `NormNum.jacobiSymNat`. (But we'll continue to write `J(a | b)`
  in this description.)

* Remove powers of two from `b`. This is done via `J(2a | 2b) = 0` and
  `J(2a+1 | 2b) = J(2a+1 | b)` (another artifact of the definition).

* Now `0 ≤ a < b` and `b` is odd. If `b = 1`, then the value is `1`.
  If `a = 0` (and `b > 1`), then the value is `0`. Otherwise, we remove powers of two from `a`
  via `J(4a | b) = J(a | b)` and `J(2a | b) = ±J(a | b)`, where the sign is determined
  by the residue class of `b` mod 8, to reduce to `a` odd.

* Once `a` is odd, we use Quadratic Reciprocity (QR) in the form
  `J(a | b) = ±J(b % a | a)`, where the sign is determined by the residue classes
  of `a` and `b` mod 4. We are then back in the previous case.

We provide customized versions of these results for the various reduction steps,
where we encode the residue classes mod 2, mod 4, or mod 8 by using hypotheses like
`a % n = b`. In this way, the only divisions we have to compute and prove
are the ones occurring in the use of QR above.
-/

public section


section Lemmas

namespace Mathlib.Meta.NormNum

/-- The Jacobi symbol restricted to natural numbers in both arguments. -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：jacobiSymNat (a b : Nat) : Int
参数：a b : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Jacobi symbol restricted to natural numbers in both arguments.
-/
def jacobiSymNat (a b : ℕ) : ℤ :=
  jacobiSym a b

/-!
### API Lemmas

We repeat part of the API for `jacobiSym` with `NormNum.jacobiSymNat` and without implicit
arguments, in a form that is suitable for constructing proofs in `norm_num`.
-/


/-- Base cases: `b = 0`, `b = 1`, `a = 0`, `a = 1`. -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (a : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a 0 = 1
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `jacobiSym.zero_right`：zero_right (a : Int) : J(a | 0) = 1

--- 原说明 ---
Base cases: `b = 0`, `b = 1`, `a = 0`, `a = 1`.
-/
theorem jacobiSymNat.zero_right (a : ℕ) : jacobiSymNat a 0 = 1 := by
  rw [jacobiSymNat, jacobiSym.zero_right]
/-
**Mathlib.Meta.NormNum.jacobiSymNat.one_right** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (a : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a 1 = 1
参数：a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `jacobiSym.one_right`：one_right (a : Int) : J(a | 1) = 1
-/
theorem jacobiSymNat.one_right (a : ℕ) : jacobiSymNat a 1 = 1 := by
  rw [jacobiSymNat, jacobiSym.one_right]
/-
**Mathlib.Meta.NormNum.jacobiSymNat.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (b : ℕ), (b / 2).beq 0 = false → Mathlib.Meta.NormNum.jacobiSymNat 0 b =
 0
参数：b : ℕ；b / 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `jacobiSym.zero_left`：zero_left {b : Nat} (hb : 1 < b) : J(0 | b) = 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.ne_of_beq_eq_false`：∀ {n m : ℕ}, n.beq m = false → ¬n = m
· 使用定理 `Nat.mul_div_le`：∀ (m n : ℕ), n * (m / n) ≤ m
-/
theorem jacobiSymNat.zero_left (b : ℕ) (hb : Nat.beq (b / 2) 0 = false) : jacobiSymNat 0 b = 0 := by
  rw [jacobiSymNat, Nat.cast_zero, jacobiSym.zero_left ?_]
  calc
    1 < 2 * 1       := by decide
    _ ≤ 2 * (b / 2) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)))
    _ ≤ b           := Nat.mul_div_le b 2
/-
**Mathlib.Meta.NormNum.jacobiSymNat.one_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat 1 b = 1
参数：b : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `jacobiSym.one_left`：one_left (b : Nat) : J(1 | b) = 1
-/
theorem jacobiSymNat.one_left (b : ℕ) : jacobiSymNat 1 b = 1 := by
  rw [jacobiSymNat, Nat.cast_one, jacobiSym.one_left]

/-- Turn a Legendre symbol into a Jacobi symbol. -/
/-
**Mathlib.Meta.NormNum.LegendreSym.to_jacobiSym** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Meta.NormNum.LegendreSym`。
形式化陈述：∀ (p : ℕ) (pp : Fact (Nat.Prime p)) (a r : ℤ),   Mathlib.Meta.NormNum.IsIn
t (jacobiSym a p) r → Mathlib.Meta.NormNum.IsInt (legendreSym p a) r
参数：p : ℕ；pp : Fact (Nat.Prime p)；a r : ℤ；jacobiSym a p；legendreSym p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSym.legendreSym.to_jacobiSym`：∀ (p : ℕ) [fp : Fact (Nat.Prime p)] 
(a : ℤ), legendreSym p a = jacobiSym a p

--- 原说明 ---
Turn a Legendre symbol into a Jacobi symbol.
-/
theorem LegendreSym.to_jacobiSym (p : ℕ) (pp : Fact p.Prime) (a r : ℤ)
    (hr : IsInt (jacobiSym a p) r) : IsInt (legendreSym p a) r := by
  rwa [@jacobiSym.legendreSym.to_jacobiSym p pp a]

/-- The value depends only on the residue class of `a` mod `b`. -/
/-
**Mathlib.Meta.NormNum.JacobiSym.mod_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.NormNum.JacobiSym`。
形式化陈述：∀ (a : ℤ) (b ab' : ℕ) (ab r b' : ℤ),   ↑b = b' → a % b' = ab → ↑ab' = ab →
 Mathlib.Meta.NormNum.jacobiSymNat ab' b = r → jacobiSym a b = r
参数：a : ℤ；b ab' : ℕ；ab r b' : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `jacobiSym.mod_left`：mod_left (a : Int) (b : Nat) : J(a | b) = J(a % b | 
b)

--- 原说明 ---
The value depends only on the residue class of `a` mod `b`.
-/
theorem JacobiSym.mod_left (a : ℤ) (b ab' : ℕ) (ab r b' : ℤ) (hb' : (b : ℤ) = b')
    (hab : a % b' = ab) (h : (ab' : ℤ) = ab) (hr : jacobiSymNat ab' b = r) : jacobiSym a b = r := by
  rw [← hr, jacobiSymNat, jacobiSym.mod_left, hb', hab, ← h]
/-
**Mathlib.Meta.NormNum.jacobiSymNat.mod_left** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (a b ab : ℕ) (r : ℤ),   a % b = ab → Mathlib.Meta.NormNum.jacobiSymNat a
b b = r → Mathlib.Meta.NormNum.jacobiSymNat a b = r
参数：a b ab : ℕ；r : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `jacobiSym.mod_left`：mod_left (a : Int) (b : Nat) : J(a | b) = J(a % b | 
b)
-/
theorem jacobiSymNat.mod_left (a b ab : ℕ) (r : ℤ) (hab : a % b = ab) (hr : jacobiSymNat ab b = r) :
    jacobiSymNat a b = r := by
  rw [← hr, jacobiSymNat, jacobiSymNat, _root_.jacobiSym.mod_left a b, ← hab]; rfl

/-- The symbol vanishes when both entries are even (and `b / 2 ≠ 0`). -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat.even_even** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (a b : ℕ), (b / 2).beq 0 = false → a % 2 = 0 → b % 2 = 0 → Mathlib.Meta.
NormNum.jacobiSymNat a b = 0
参数：a b : ℕ；b / 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `jacobiSym.eq_zero_iff`：eq_zero_iff {a : Int} {b : Nat} : J(a | b) = 0 ↔ 
b != 0 ∧ a.gcd b != 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.ne_of_beq_eq_false`：∀ {n m : ℕ}, n.beq m = false → ¬n = m
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `Nat.not_even_one`：¬Even 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a

--- 原说明 ---
The symbol vanishes when both entries are even (and `b / 2 ≠ 0`).
-/
theorem jacobiSymNat.even_even (a b : ℕ) (hb₀ : Nat.beq (b / 2) 0 = false) (ha : a % 2 = 0)
    (hb₁ : b % 2 = 0) : jacobiSymNat a b = 0 := by
  refine jacobiSym.eq_zero_iff.mpr
    ⟨ne_of_gt ((Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb₀)).trans_le (Nat.div_le_self b 2)),
      fun hf => ?_⟩
  have h : 2 ∣ a.gcd b := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb₁)
  change 2 ∣ (a : ℤ).gcd b at h
  rw [hf, ← even_iff_two_dvd] at h
  exact Nat.not_even_one h

/-- When `a` is odd and `b` is even, we can replace `b` by `b / 2`. -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat.odd_even** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (a b c : ℕ) (r : ℤ),   a % 2 = 1 →     b % 2 = 0 → b / 2 = c → Mathlib.M
eta.NormNum.jacobiSymNat a c = r → Mathlib.Meta.NormNum.jacobiSymNat a b = r
参数：a b c : ℕ；r : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `legendreSym.mod`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendre
Sym p a = legendreSym p (a % ↑p)
· 使用定理 `legendreSym.congr_simp`：∀ (p p_1 : ℕ) (e_p : p = p_1) [inst : Fact (Nat.
Prime p)] (a a_1 : ℤ), a = a_1 → legendreSym p a = legendreSym p_1 a_1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_zero_of_dvd_of_div_eq_zero`：∀ {a b : ℕ}, a ∣ b → b / a = 0 → b = 
0
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `_private.Mathlib.Tactic.NormNum.LegendreSymbol.0.Mathlib.Meta.NormNum.ja
cobiSymNat.eq_1`：∀ (a b : ℕ), Mathlib.Meta.NormNum.jacobiSymNat a b = jacobiSym 
(↑a) b
· 使用定理 `jacobiSym.mul_right`：mul_right (a : Int) (b₁ b₂ : Nat) [NeZero b₁] [NeZe
ro b₂] : J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `jacobiSym.legendreSym.to_jacobiSym`：∀ (p : ℕ) [fp : Fact (Nat.Prime p)] 
(a : ℤ), legendreSym p a = jacobiSym a p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
When `a` is odd and `b` is even, we can replace `b` by `b / 2`.
-/
theorem jacobiSymNat.odd_even (a b c : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : b / 2 = c)
    (hr : jacobiSymNat a c = r) : jacobiSymNat a b = r := by
  have ha' : legendreSym 2 a = 1 := by
    simp only [legendreSym.mod 2 a, Int.ofNat_mod_ofNat, ha]
    decide
  rcases eq_or_ne c 0 with (rfl | hc')
  · rw [← hr, Nat.eq_zero_of_dvd_of_div_eq_zero (Nat.dvd_of_mod_eq_zero hb) hc]
  · have : NeZero c := ⟨hc'⟩
    -- for `jacobiSym.mul_right`
    rwa [← Nat.mod_add_div b 2, hb, hc, Nat.zero_add, jacobiSymNat, jacobiSym.mul_right,
      ← jacobiSym.legendreSym.to_jacobiSym, ha', one_mul]

/-- If `a` is divisible by `4` and `b` is odd, then we can remove the factor `4` from `a`. -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat.double_even** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Meta.NormNum.jacobiSymNat`。
形式化陈述：∀ (a b c : ℕ) (r : ℤ),   a % 4 = 0 →     b % 2 = 1 → a / 4 = c → Mathlib.M
eta.NormNum.jacobiSymNat c b = r → Mathlib.Meta.NormNum.jacobiSymNat a b = r
参数：a b c : ℕ；r : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `jacobiSym.div_four_left`：div_four_left {a : Int} {b : Nat} (ha4 : a % 4 
= 0) (hb2 : b % 2 = 1) : J(a / 4 | b) = J(a | b)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
If `a` is divisible by `4` and `b` is odd, then we can remove the factor `4` fro
m `a`.
-/
theorem jacobiSymNat.double_even (a b c : ℕ) (r : ℤ) (ha : a % 4 = 0) (hb : b % 2 = 1)
    (hc : a / 4 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  exact (jacobiSym.div_four_left (mod_cast ha) hb).symm

/-- If `a` is even and `b` is odd, then we can remove a factor `2` from `a`,
but we may have to change the sign, depending on `b % 8`.
We give one version for each of the four odd residue classes mod `8`. -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat.even_odd** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a` is even and `b` is odd, then we can remove a factor `2` from `a`,
but we may have to change the sign, depending on `b % 8`.
We give one version for each of the four odd residue classes mod `8`.
-/
theorem jacobiSymNat.even_odd₁ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 1)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha), if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd, hb]; simp
/-
**Mathlib.Meta.NormNum.jacobiSymNat.even_odd** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.even_odd₇ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 7)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha), if_neg (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd, hb]; simp
/-
**Mathlib.Meta.NormNum.jacobiSymNat.even_odd** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.even_odd₃ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 3)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha), if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd, hb]; simp
/-
**Mathlib.Meta.NormNum.jacobiSymNat.even_odd** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.even_odd₅ (a b c : ℕ) (r : ℤ) (ha : a % 2 = 0) (hb : b % 8 = 5)
    (hc : a / 2 = c) (hr : jacobiSymNat c b = r) : jacobiSymNat a b = -r := by
  simp only [jacobiSymNat, ← hr, ← hc, Int.natCast_ediv, Nat.cast_ofNat]
  rw [← jacobiSym.even_odd (mod_cast ha), if_pos (by simp [hb])]
  rw [← Nat.mod_mod_of_dvd, hb]; simp

/-- Use quadratic reciprocity to reduce to smaller `b`. -/
/-
**Mathlib.Meta.NormNum.jacobiSymNat.qr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use quadratic reciprocity to reduce to smaller `b`.
-/
theorem jacobiSymNat.qr₁ (a b : ℕ) (r : ℤ) (ha : a % 4 = 1) (hb : b % 2 = 1)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_one_mod_four ha (Nat.odd_iff.mpr hb)]
/-
**Mathlib.Meta.NormNum.jacobiSymNat.qr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.qr₁_mod (a b ab : ℕ) (r : ℤ) (ha : a % 4 = 1) (hb : b % 2 = 1)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
  jacobiSymNat.qr₁ _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
/-
**Mathlib.Meta.NormNum.jacobiSymNat.qr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.qr₁' (a b : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 4 = 1)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = r := by
  rwa [jacobiSymNat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (Nat.odd_iff.mpr ha)]
/-
**Mathlib.Meta.NormNum.jacobiSymNat.qr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.qr₁'_mod (a b ab : ℕ) (r : ℤ) (ha : a % 2 = 1) (hb : b % 4 = 1)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = r :=
  jacobiSymNat.qr₁' _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
/-
**Mathlib.Meta.NormNum.jacobiSymNat.qr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.qr₃ (a b : ℕ) (r : ℤ) (ha : a % 4 = 3) (hb : b % 4 = 3)
    (hr : jacobiSymNat b a = r) : jacobiSymNat a b = -r := by
  rwa [jacobiSymNat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]
/-
**Mathlib.Meta.NormNum.jacobiSymNat.qr** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem jacobiSymNat.qr₃_mod (a b ab : ℕ) (r : ℤ) (ha : a % 4 = 3) (hb : b % 4 = 3)
    (hab : b % a = ab) (hr : jacobiSymNat ab a = r) : jacobiSymNat a b = -r :=
  jacobiSymNat.qr₃ _ _ _ ha hb <| jacobiSymNat.mod_left _ _ ab r hab hr
/-
**Mathlib.Meta.NormNum.isInt_jacobiSym** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：∀ {a na : ℤ} {b nb : ℕ} {r : ℤ},   Mathlib.Meta.NormNum.IsInt a na →     M
athlib.Meta.NormNum.IsNat b nb → jacobiSym na nb = r → Mathlib.Meta.NormNum.IsIn
t (jacobiSym a b) r
参数：jacobiSym a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_jacobiSym : {a na : ℤ} → {b nb : ℕ} → {r : ℤ} →
    IsInt a na → IsNat b nb → jacobiSym na nb = r → IsInt (jacobiSym a b) r
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩
/-
**Mathlib.Meta.NormNum.isInt_jacobiSymNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.NormNum`。
形式化陈述：∀ {a na b nb : ℕ} {r : ℤ},   Mathlib.Meta.NormNum.IsNat a na →     Mathlib
.Meta.NormNum.IsNat b nb →       Mathlib.Meta.NormNum.jacobiSymNat na nb = r → M
athlib.Meta.NormNum.IsInt (Mathlib.Meta.NormNum.jacobiSymNat a b) r
参数：Mathlib.Meta.NormNum.jacobiSymNat a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isInt_jacobiSymNat : {a na : ℕ} → {b nb : ℕ} → {r : ℤ} →
    IsNat a na → IsNat b nb → jacobiSymNat na nb = r → IsInt (jacobiSymNat a b) r
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩


end Mathlib.Meta.NormNum

end Lemmas

meta section

section Evaluation

/-!
### Certified evaluation of the Jacobi symbol

The following functions recursively evaluate a Jacobi symbol and construct the
corresponding proof term.
-/


namespace Mathlib.Meta.NormNum

open Lean Elab Tactic Qq

-- TODO: redefined here for reduction; should this be special-handled in quote4?
/-
**Mathlib.Meta.NormNum.mkRawIntLit'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def mkRawIntLit' (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := .lit <| .natVal n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/-- This evaluates `r := jacobiSymNat a b` recursively using quadratic reciprocity
and produces a proof term for the equality, assuming that `a < b` and `b` is odd. -/
/-
**Mathlib.Meta.NormNum.proveJacobiSymOdd** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：(ea eb : Q(ℕ)) → (er : Q(ℤ)) × Q(Mathlib.Meta.NormNum.jacobiSymNat «$ea» «
$eb» = «$er»)
参数：ℕ；ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This evaluates `r := jacobiSymNat a b` recursively using quadratic reciprocity
and produces a proof term for the equality, assuming that `a < b` and `b` is odd
.
-/
partial def proveJacobiSymOdd (ea eb : Q(ℕ)) : (er : Q(ℤ)) × Q(jacobiSymNat $ea $eb = $er) :=
  match eb.natLit! with
  | 1 =>
    haveI : $eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match ea.natLit! with
    | 0 =>
      haveI : $ea =Q 0 := ⟨⟩
      have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
      ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb $hb)⟩
    | 1 =>
      haveI : $ea =Q 1 := ⟨⟩
      ⟨mkRawIntLit' 1, q(jacobiSymNat.one_left $eb)⟩
    | a =>
      match a % 2 with
      | 0 =>
        match a % 4 with
        | 0 =>
          have ha : Q(Nat.mod $ea 4 = 0) := (q(Eq.refl 0) : Expr)
          have hb : Q(Nat.mod $eb 2 = 1) := (q(Eq.refl 1) : Expr)
          have ec : Q(ℕ) := mkRawNatLit (a / 4)
          have hc : Q(Nat.div $ea 4 = $ec) := (q(Eq.refl $ec) : Expr)
          have ⟨er, p⟩ := proveJacobiSymOdd ec eb
          ⟨er, q(jacobiSymNat.double_even $ea $eb $ec $er $ha $hb $hc $p)⟩
        | _ =>
          have ha : Q(Nat.mod $ea 2 = 0) := (q(Eq.refl 0) : Expr)
          have ec : Q(ℕ) := mkRawNatLit (a / 2)
          have hc : Q(Nat.div $ea 2 = $ec) := (q(Eq.refl $ec) : Expr)
          have ⟨er, p⟩ := proveJacobiSymOdd ec eb
          match b % 8 with
          | 1 =>
            have hb : Q(Nat.mod $eb 8 = 1) := (q(Eq.refl 1) : Expr)
            ⟨er, q(jacobiSymNat.even_odd₁ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | 3 =>
            have er' := mkRawIntLit (-er.intLit!)
            have hb : Q(Nat.mod $eb 8 = 3) := (q(Eq.refl 3) : Expr)
            show (_ : Q(ℤ)) × Q(jacobiSymNat $ea $eb = -$er) from
              ⟨er', q(jacobiSymNat.even_odd₃ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | 5 =>
            have er' := mkRawIntLit (-er.intLit!)
            haveI : $er' =Q -$er := ⟨⟩
            have hb : Q(Nat.mod $eb 8 = 5) := (q(Eq.refl 5) : Expr)
            ⟨er', q(jacobiSymNat.even_odd₅ $ea $eb $ec $er $ha $hb $hc $p)⟩
          | _ =>
            have hb : Q(Nat.mod $eb 8 = 7) := (q(Eq.refl 7) : Expr)
            ⟨er, q(jacobiSymNat.even_odd₇ $ea $eb $ec $er $ha $hb $hc $p)⟩
      | _ =>
        have eab : Q(ℕ) := mkRawNatLit (b % a)
        have hab : Q(Nat.mod $eb $ea = $eab) := (q(Eq.refl $eab) : Expr)
        have ⟨er, p⟩ := proveJacobiSymOdd eab ea
        match a % 4 with
        | 1 =>
          have ha : Q(Nat.mod $ea 4 = 1) := (q(Eq.refl 1) : Expr)
          have hb : Q(Nat.mod $eb 2 = 1) := (q(Eq.refl 1) : Expr)
          ⟨er, q(jacobiSymNat.qr₁_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
        | _ =>
          match b % 4 with
          | 1 =>
            have ha : Q(Nat.mod $ea 2 = 1) := (q(Eq.refl 1) : Expr)
            have hb : Q(Nat.mod $eb 4 = 1) := (q(Eq.refl 1) : Expr)
            ⟨er, q(jacobiSymNat.qr₁'_mod $ea $eb $eab $er $ha $hb $hab $p)⟩
          | _ =>
            have er' := mkRawIntLit (-er.intLit!)
            haveI : $er' =Q -$er := ⟨⟩
            have ha : Q(Nat.mod $ea 4 = 3) := (q(Eq.refl 3) : Expr)
            have hb : Q(Nat.mod $eb 4 = 3) := (q(Eq.refl 3) : Expr)
            ⟨er', q(jacobiSymNat.qr₃_mod $ea $eb $eab $er $ha $hb $hab $p)⟩

/-- This evaluates `r := jacobiSymNat a b` and produces a proof term for the equality
by removing powers of `2` from `b` and then calling `proveJacobiSymOdd`. -/
/-
**Mathlib.Meta.NormNum.proveJacobiSymNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.NormNum`。
形式化陈述：(ea eb : Q(ℕ)) → (er : Q(ℤ)) × Q(Mathlib.Meta.NormNum.jacobiSymNat «$ea» «
$eb» = «$er»)
参数：ℕ；ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This evaluates `r := jacobiSymNat a b` and produces a proof term for the equalit
y
by removing powers of `2` from `b` and then calling `proveJacobiSymOdd`.
-/
partial def proveJacobiSymNat (ea eb : Q(ℕ)) : (er : Q(ℤ)) × Q(jacobiSymNat $ea $eb = $er) :=
  match eb.natLit! with
  | 0 =>
    haveI : $eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.zero_right $ea)⟩
  | 1 =>
    haveI : $eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSymNat.one_right $ea)⟩
  | b =>
    match b % 2 with
    | 0 =>
      match ea.natLit! with
      | 0 =>
        have hb : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
        show (er : Q(ℤ)) × Q(jacobiSymNat 0 $eb = $er) from
          ⟨mkRawIntLit' 0, q(jacobiSymNat.zero_left $eb $hb)⟩
      | 1 =>
        show (er : Q(ℤ)) × Q(jacobiSymNat 1 $eb = $er) from
          ⟨mkRawIntLit' 1, q(jacobiSymNat.one_left $eb)⟩
      | a =>
        match a % 2 with
        | 0 =>
          have hb₀ : Q(Nat.beq ($eb / 2) 0 = false) := (q(Eq.refl false) : Expr)
          have ha : Q(Nat.mod $ea 2 = 0) := (q(Eq.refl 0) : Expr)
          have hb₁ : Q(Nat.mod $eb 2 = 0) := (q(Eq.refl 0) : Expr)
          ⟨mkRawIntLit' 0, q(jacobiSymNat.even_even $ea $eb $hb₀ $ha $hb₁)⟩
        | _ =>
          have ha : Q(Nat.mod $ea 2 = 1) := (q(Eq.refl 1) : Expr)
          have hb : Q(Nat.mod $eb 2 = 0) := (q(Eq.refl 0) : Expr)
          have ec : Q(ℕ) := mkRawNatLit (b / 2)
          have hc : Q(Nat.div $eb 2 = $ec) := (q(Eq.refl $ec) : Expr)
          have ⟨er, p⟩ := proveJacobiSymOdd ea ec
          ⟨er, q(jacobiSymNat.odd_even $ea $eb $ec $er $ha $hb $hc $p)⟩
    | _ =>
      have a := ea.natLit!
      if b ≤ a then
        have eab : Q(ℕ) := mkRawNatLit (a % b)
        have hab : Q(Nat.mod $ea $eb = $eab) := (q(Eq.refl $eab) : Expr)
        have ⟨er, p⟩ := proveJacobiSymOdd eab eb
        ⟨er, q(jacobiSymNat.mod_left $ea $eb $eab $er $hab $p)⟩
      else
        proveJacobiSymOdd ea eb

/-- This evaluates `r := jacobiSym a b` and produces a proof term for the equality.
This is done by reducing to `r := jacobiSymNat (a % b) b`. -/
/-
**Mathlib.Meta.NormNum.proveJacobiSym** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：(ea : Q(ℤ)) → (eb : Q(ℕ)) → (er : Q(ℤ)) × Q(jacobiSym «$ea» «$eb» = «$er»)
参数：ℤ；ℕ；ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This evaluates `r := jacobiSym a b` and produces a proof term for the equality.
This is done by reducing to `r := jacobiSymNat (a % b) b`.
-/
partial def proveJacobiSym (ea : Q(ℤ)) (eb : Q(ℕ)) : (er : Q(ℤ)) × Q(jacobiSym $ea $eb = $er) :=
  match eb.natLit! with
  | 0 =>
    haveI : $eb =Q 0 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.zero_right $ea)⟩
  | 1 =>
    haveI : $eb =Q 1 := ⟨⟩
    ⟨mkRawIntLit' 1, q(jacobiSym.one_right $ea)⟩
  | b =>
    have eb' := mkRawIntLit b
    have hb' : Q(($eb : ℤ) = $eb') := (q(Eq.refl $eb') : Expr)
    have ab := ea.intLit! % b
    have eab := mkRawIntLit ab
    have hab : Q(Int.emod $ea $eb' = $eab) := (q(Eq.refl $eab) : Expr)
    have eab' : Q(ℕ) := mkRawNatLit ab.toNat
    have hab' : Q(($eab' : ℤ) = $eab) := (q(Eq.refl $eab) : Expr)
    have ⟨er, p⟩ := proveJacobiSymNat eab' eb
    ⟨er, q(JacobiSym.mod_left $ea $eb $eab' $eab $er $eb' $hb' $hab $hab' $p)⟩

end Mathlib.Meta.NormNum

end Evaluation

section Tactic

/-!
### The `norm_num` plug-in
-/


namespace Tactic

namespace NormNum

open Lean Elab Tactic Qq Mathlib.Meta.NormNum

/-- This is the `norm_num` plug-in that evaluates Jacobi symbols. -/
@[norm_num jacobiSym _ _]
/-
**Tactic.NormNum.evalJacobiSym** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.NormNum`。
形式化陈述：evalJacobiSym : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `norm_num` plug-in that evaluates Jacobi symbols.
-/
def evalJacobiSym : NormNumExt where eval {u α} e := do
    let .app (.app _ (a : Q(ℤ))) (b : Q(ℕ)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨eb, pb⟩ ← deriveNat b _
    haveI' : u =QL 0 := ⟨⟩ haveI' : $α =Q ℤ := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea eb
    haveI' : $e =Q jacobiSym $a $b := ⟨⟩
    return .isInt _ er er.intLit! q(isInt_jacobiSym $pa $pb $pr)

/-- This is the `norm_num` plug-in that evaluates Jacobi symbols on natural numbers. -/
@[norm_num jacobiSymNat _ _]
/-
**Tactic.NormNum.evalJacobiSymNat** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.NormNum`。
形式化陈述：evalJacobiSymNat : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `norm_num` plug-in that evaluates Jacobi symbols on natural numbers.
-/
def evalJacobiSymNat : NormNumExt where eval {u α} e := do
    let .app (.app _ (a : Q(ℕ))) (b : Q(ℕ)) ← Meta.whnfR e | failure
    let ⟨ea, pa⟩ ← deriveNat a _
    let ⟨eb, pb⟩ ← deriveNat b _
    haveI' : u =QL 0 := ⟨⟩ haveI' : $α =Q ℤ := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSymNat ea eb
    haveI' : $e =Q jacobiSymNat $a $b := ⟨⟩
    return .isInt _ er er.intLit!  q(isInt_jacobiSymNat $pa $pb $pr)

/-- This is the `norm_num` plug-in that evaluates Legendre symbols. -/
@[norm_num legendreSym _ _]
/-
**Tactic.NormNum.evalLegendreSym** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.NormNum`。
形式化陈述：evalLegendreSym : NormNumExt where eval {u α} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `norm_num` plug-in that evaluates Legendre symbols.
-/
def evalLegendreSym : NormNumExt where eval {u α} e := do
    let .app (.app (.app _ (p : Q(ℕ))) (fp : Q(Fact (Nat.Prime $p)))) (a : Q(ℤ)) ← Meta.whnfR e |
      failure
    let ⟨ea, pa⟩ ← deriveInt a _
    let ⟨ep, pp⟩ ← deriveNat p _
    haveI' : u =QL 0 := ⟨⟩ haveI' : $α =Q ℤ := ⟨⟩
    have ⟨er, pr⟩ := proveJacobiSym ea ep
    haveI' : $e =Q legendreSym $p $a := ⟨⟩
    return .isInt _ er er.intLit!
      q(LegendreSym.to_jacobiSym $p $fp $a $er (isInt_jacobiSym $pa $pp $pr))

end NormNum

end Tactic

end Tactic

