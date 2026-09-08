/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Special values of Hurwitz and Riemann zeta functions

This file gives the formula for `ζ (2 * k)`, for `k` a non-zero integer, in terms of Bernoulli
numbers. More generally, we give formulae for any Hurwitz zeta functions at any (strictly) negative
integer in terms of Bernoulli polynomials.

(Note that most of the actual work for these formulae is done elsewhere, in
`Mathlib/NumberTheory/ZetaValues.lean`. This file has only those results which really need the
definition of Hurwitz zeta and related functions, rather than working directly with the defining
sums in the convergence range.)

## Main results

- `hurwitzZeta_neg_nat`: for `k : ℕ` with `k ≠ 0`, and any `x ∈ ℝ / ℤ`, the special value
  `hurwitzZeta x (-k)` is equal to `-(Polynomial.bernoulli (k + 1) x) / (k + 1)`.
- `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
- `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## TODO

* Extend to cover Dirichlet L-functions.
* The formulae are correct for `s = 0` as well, but we do not prove this case, since this requires
  Fourier series which are only conditionally convergent, which is difficult to approach using the
  methods in the library at the present time (May 2024).
-/

public section

open Complex Real Set

open scoped Nat

namespace HurwitzZeta

variable {k : ℕ} {x : ℝ}

/-- Express the value of `cosZeta` at a positive even integer as a value
of the Bernoulli polynomial. -/
/-
**HurwitzZeta.cosZeta_two_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta_two_mul_nat (hk : k != 0) (hx : x in Icc 0 1) : cosZeta x (2 * k) 
= (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! * ((Polynomial.bernoulli (2 
* k)).map (algebraMap Rat Complex)).eval (x : Complex)
参数：hk : k != 0；hx : x in Icc 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HurwitzZeta.hasSum_nat_cosZeta`：hasSum_nat_cosZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.cos (2 * π * a * n) / (n : Com
plex) ^ s) (cosZeta …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
Express the value of `cosZeta` at a positive even integer as a value
of the Bernoulli polynomial.
-/
theorem cosZeta_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
  · refine Eq.trans ?_ <|
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ) = _ :=
        (Polynomial.map_map (algebraMap ℚ ℝ) ofRealHom _).symm
      rw [this, ← ofRealHom_eq_coe, ← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/--
Express the value of `sinZeta` at an odd integer `> 1` as a value of the Bernoulli polynomial.

Note that this formula is also correct for `k = 0` (i.e. for the value at `s = 1`), but we do not
prove it in this case, owing to the additional difficulty of working with series that are only
conditionally convergent.
-/
/-
**HurwitzZeta.sinZeta_two_mul_nat_add_one** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta
`。
形式化陈述：sinZeta_two_mul_nat_add_one (hk : k != 0) (hx : x in Icc 0 1) : sinZeta x 
(2 * k + 1) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! * ((Poly
nomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex)).eval (x : Complex)
参数：hk : k != 0；hx : x in Icc 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HurwitzZeta.hasSum_nat_sinZeta`：hasSum_nat_sinZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.sin (2 * π * a * n) / (n : Com
plex) ^ s) (sinZeta …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
Express the value of `sinZeta` at an odd integer `> 1` as a value of the Bernoul
li polynomial.

Note that this formula is also correct for `k = 0` (i.e. for the value at `s = 1
`), but we do not
prove it in this case, owing to the additional difficulty of working with series
 that are only
conditionally convergent.
-/
theorem sinZeta_two_mul_nat_add_one (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
  · refine Eq.trans ?_ <|
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ) = _ :=
        (Polynomial.map_map (algebraMap ℚ ℝ) ofRealHom _).symm
      rw [this, ← ofRealHom_eq_coe, ← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/-- Reformulation of `cosZeta_two_mul_nat` using `Gammaℂ`. -/
/-
**HurwitzZeta.cosZeta_two_mul_nat'** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta_two_mul_nat' (hk : k != 0) (hx : x in Icc (0 : Real) 1) : cosZeta 
x (2 * k) = (-1) ^ (k + 1) / (2 * k) / GammaComplex (2 * k) * ((Polynomial.berno
ulli (2 * k)).map (algebraMap Rat Complex)).eval (x : Complex)
参数：hk : k != 0；hx : x in Icc (0 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.cosZeta_two_mul_nat`：cosZeta_two_mul_nat (hk : k != 0) (hx :
 x in Icc 0 1) : cosZeta x (2 * k) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2
 * k)! * ((Polynomial…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.Gamma_nat_eq_factorial`：Gamma_nat_eq_factorial (n : Nat) : Gamma
 (n + 1) = n !
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n

--- 原说明 ---
Reformulation of `cosZeta_two_mul_nat` using `Gammaℂ`.
-/
theorem cosZeta_two_mul_nat' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) / (2 * k) / Gammaℂ (2 * k) *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have : (2 * k)! = (2 * k) * Complex.Gamma (2 * k) := by
    rw [(by { norm_cast; lia } : 2 * (k : ℂ) = ↑(2 * k - 1) + 1), Complex.Gamma_nat_eq_factorial,
      ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.sub_add_cancel (by lia)]
  simp_rw [this, Gammaℂ, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div,
    mul_right_comm (2 : ℂ) (k : ℂ)]
  norm_cast

/-- Reformulation of `sinZeta_two_mul_nat_add_one` using `Gammaℂ`. -/
/-
**HurwitzZeta.sinZeta_two_mul_nat_add_one'** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZet
a`。
形式化陈述：sinZeta_two_mul_nat_add_one' (hk : k != 0) (hx : x in Icc (0 : Real) 1) : 
sinZeta x (2 * k + 1) = (-1) ^ (k + 1) / (2 * k + 1) / GammaComplex (2 * k + 1) 
* ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex)).eval (x : Co
mplex)
参数：hk : k != 0；hx : x in Icc (0 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.sinZeta_two_mul_nat_add_one`：sinZeta_two_mul_nat_add_one (hk
 : k != 0) (hx : x in Icc 0 1) : sinZeta x (2 * k + 1) = (-1) ^ (k + 1) * (2 * π
) ^ (2 * k + 1) / 2 / (2 * k …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.Gamma_nat_eq_factorial`：Gamma_nat_eq_factorial (n : Nat) : Gamma
 (n + 1) = n !
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
Reformulation of `sinZeta_two_mul_nat_add_one` using `Gammaℂ`.
-/
theorem sinZeta_two_mul_nat_add_one' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) / (2 * k + 1) / Gammaℂ (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have : (2 * k + 1)! = (2 * k + 1) * Complex.Gamma (2 * k + 1) := by
    rw [(by simp : Complex.Gamma (2 * k + 1) = Complex.Gamma (↑(2 * k) + 1)),
       Complex.Gamma_nat_eq_factorial, ← Nat.cast_ofNat (R := ℂ), ← Nat.cast_mul,
      ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ]
  simp_rw [this, Gammaℂ, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  rw [(by simp : 2 * (k : ℂ) + 1 = ↑(2 * k + 1)), cpow_natCast]
  ring
/-
**HurwitzZeta.hurwitzZetaEven_one_sub_two_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `Hur
witzZeta`。
形式化陈述：hurwitzZetaEven_one_sub_two_mul_nat (hk : k != 0) (hx : x in Icc (0 : Real
) 1) : hurwitzZetaEven x (1 - 2 * k) = -1 / (2 * k) * ((Polynomial.bernoulli (2 
* k)).map (algebraMap Rat Complex)).eval (x : Complex)
参数：hk : k != 0；hx : x in Icc (0 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `neg_nonpos_of_nonneg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, 0 ≤ a → -a ≤ 0
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
（共 61 条，此处仅展示前 30 条）
-/
theorem hurwitzZetaEven_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaEven x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have h1 (n : ℕ) : (2 * k : ℂ) ≠ -n := by
    rw [← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_natCast n, ← Int.cast_neg,
      Ne, Int.cast_inj, ← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt (mul_pos two_pos ?_))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h2 : (2 * k : ℂ) ≠ 1 := by norm_cast; simp
  have h3 : Gammaℂ (2 * k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [hurwitzZetaEven_one_sub _ h1 (Or.inr h2), ← Gammaℂ, cosZeta_two_mul_nat' hk hx, ← mul_assoc,
    ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ h3, ← mul_div_assoc]
  congr 2
  rw [mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero, ← ofReal_natCast, ← ofReal_mul,
    ← ofReal_cos, mul_comm π, ← sub_zero (k * π), cos_nat_mul_pi_sub, Real.cos_zero, mul_one,
    ofReal_pow, ofReal_neg, ofReal_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow, neg_one_mul,
    neg_neg, one_pow]
/-
**HurwitzZeta.hurwitzZetaOdd_neg_two_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZ
eta`。
形式化陈述：hurwitzZetaOdd_neg_two_mul_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) 
: hurwitzZetaOdd x (-(2 * k)) = -1 / (2 * k + 1) * ((Polynomial.bernoulli (2 * k
 + 1)).map (algebraMap Rat Complex)).eval (x : Complex)
参数：hk : k != 0；hx : x in Icc (0 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `neg_nonpos_of_nonneg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, 0 ≤ a → -a ≤ 0
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 75 条，此处仅展示前 30 条）
-/
theorem hurwitzZetaOdd_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaOdd x (-(2 * k)) =
    -1 / (2 * k + 1) * ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have h1 (n : ℕ) : (2 * k + 1 : ℂ) ≠ -n := by
    rw [← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_natCast n, ← Int.cast_neg,
      ← Int.cast_one, ← Int.cast_add, Ne, Int.cast_inj, ← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt ?_)
    positivity
  have h3 : Gammaℂ (2 * k + 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [(by simp : -(2 * k : ℂ) = 1 - (2 * k + 1)),
    hurwitzZetaOdd_one_sub _ h1, ← Gammaℂ, sinZeta_two_mul_nat_add_one' hk hx, ← mul_assoc,
    ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ h3, ← mul_div_assoc]
  congr 2
  rw [mul_div_assoc, add_div, mul_div_cancel_left₀ _ two_ne_zero, ← ofReal_natCast,
    ← ofReal_one, ← ofReal_ofNat, ← ofReal_div, ← ofReal_add, ← ofReal_mul,
    ← ofReal_sin, mul_comm π, add_mul, mul_comm (1 / 2), mul_one_div, Real.sin_add_pi_div_two,
    ← sub_zero (k * π), cos_nat_mul_pi_sub, Real.cos_zero, mul_one,
    ofReal_pow, ofReal_neg, ofReal_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow, neg_one_mul,
    neg_neg, one_pow]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
/-
**HurwitzZeta.hurwitzZeta_one_sub_two_mul_nat** 是 Mathlib 中的一个引理，位于命名空间 `Hurwitz
Zeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hurwitzZeta_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta, this, add_zero, hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ, show (1 : ℂ) - 2 * (k + 1) = -2 * k - 1 by ring,
    hurwitzZetaOdd_neg_two_mul_nat_sub_one]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
/-
**HurwitzZeta.hurwitzZeta_neg_two_mul_nat** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hurwitzZeta_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-(2 * k)) = -1 / (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaEven x (-(2 * k)) = 0 by
    rw [hurwitzZeta, this, zero_add, hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using hurwitzZetaEven_neg_two_mul_nat_add_one x k

/-- Values of Hurwitz zeta functions at (strictly) negative integers.

TODO: This formula is also correct for `k = 0`; but our current proof does not work in this
case. -/
/-
**HurwitzZeta.hurwitzZeta_neg_nat** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZeta_neg_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) : hurwitzZe
ta x (-k) = -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap Rat C
omplex)).eval (x : Complex)
参数：hk : k != 0；hx : x in Icc (0 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd'`：even_or_odd' (n : Nat) : exists k, n = 2 * k ∨ n = 2 *
 k + 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaValues.0.HurwitzZeta.hu
rwitzZeta_neg_two_mul_nat`：∀ {k : ℕ} {x : ℝ},   k ≠ 0 →     x ∈ Set.Icc 0 1 →   
    HurwitzZeta.hurwitzZeta (↑x) (-(2 * ↑k)) =         -1 / (2 * ↑k + 1) * Polyn
omial.e…
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaValues.0.HurwitzZeta.hu
rwitzZeta_one_sub_two_mul_nat`：∀ {k : ℕ} {x : ℝ},   k ≠ 0 →     x ∈ Set.Icc 0 1 
→       HurwitzZeta.hurwitzZeta (↑x) (1 - 2 * ↑k) =         -1 / (2 * ↑k) * Poly
nomial.eval…

--- 原说明 ---
Values of Hurwitz zeta functions at (strictly) negative integers.

TODO: This formula is also correct for `k = 0`; but our current proof does not w
ork in this
case.
-/
theorem hurwitzZeta_neg_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-k) =
    -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by lia : n ≠ 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by lia : n + 1 ≠ 0) hx

end HurwitzZeta

open HurwitzZeta

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`, in terms of the Bernoulli number
`bernoulli (2 * k)`.

Compare `hasSum_zeta_nat` for a version formulated in terms of a sum over `1 / n ^ (2 * k)`, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent to the above via
the functional equation). -/
/-
**riemannZeta_two_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_two_mul_nat {k : Nat} (hk : k != 0) : riemannZeta (2 * k) = (-
1) ^ (k + 1) * (2 : Complex) ^ (2 * k - 1) * (π : Complex) ^ (2 * k) * bernoulli
 (2 * k) / (2 * k)!
参数：hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `zeta_nat_eq_tsum_of_gt_one`：zeta_nat_eq_tsum_of_gt_one {k : Nat} (hk : 1
 < k) : riemannZeta k = ∑' n : Nat, 1 / (n : Complex) ^ k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`, in terms of the Bern
oulli number
`bernoulli (2 * k)`.

Compare `hasSum_zeta_nat` for a version formulated in terms of a sum over `1 / n
 ^ (2 * k)`, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent t
o the above via
the functional equation).
-/
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = (-1) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  convert! congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one (by lia)]
    simp [push_cast]
  · norm_cast

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ`, in terms of the Bernoulli number
`bernoulli (2 * k)`. Compare `riemannZeta_two_mul_nat` which avoids a cast in an exponent
but requires `k ≠ 0`. -/
/-
**riemannZeta_two_mul_nat'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_two_mul_nat' {k : Nat} : riemannZeta (2 * k) = (-1) ^ (k + 1) 
* (2 : Complex) ^ (2 * k - 1 : Int) * (π : Complex) ^ (2 * k) * bernoulli (2 * k
) / (2 * k)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `riemannZeta_zero`：riemannZeta_zero : riemannZeta 0 = -1 / 2
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `bernoulli_zero`：bernoulli_zero : bernoulli 0 = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Meta.NormNum.isRat_eq_true`：∀ {α : Type u} [inst : Ring α] {a b 
: α} {n : ℤ} {d : ℕ},   Mathlib.Meta.NormNum.IsRat a n d → Mathlib.Meta.NormNum.
IsRat b n d → a = b
· 使用定理 `Mathlib.Meta.NormNum.isRat_div`：∀ {α : Type u} [inst : DivisionRing α] {
a b : α} {cn : ℤ} {cd : ℕ},   Mathlib.Meta.NormNum.IsRat (a * b⁻¹) cn cd → Mathl
ib.Meta.NormNum.IsRa…
· 使用定理 `Mathlib.Meta.NormNum.isRat_mul`：isRat_mul {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HMul.hMul -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isRat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → Mathlib.Meta.NormNum.IsRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ`, in terms of the Bernoulli number
`bernoulli (2 * k)`. Compare `riemannZeta_two_mul_nat` which avoids a cast in an
 exponent
but requires `k ≠ 0`.
-/
theorem riemannZeta_two_mul_nat' {k : ℕ} :
    riemannZeta (2 * k) = (-1) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℤ)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [riemannZeta_zero]
    norm_num
  · convert riemannZeta_two_mul_nat hk
    grind [zpow_natCast]
/-
**riemannZeta_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_two : riemannZeta 2 = (π : Complex) ^ 2 / 6
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `zeta_nat_eq_tsum_of_gt_one`：zeta_nat_eq_tsum_of_gt_one {k : Nat} (hk : 1
 < k) : riemannZeta k = ∑' n : Nat, 1 / (n : Complex) ^ k
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_zeta_two`：hasSum_zeta_two : HasSum (fun n : Nat => (1 : Real) / (
n : Real) ^ 2) (π ^ 2 / 6)
-/
theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  convert! congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two]
    simp [push_cast]
  · norm_cast
/-
**riemannZeta_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_four : riemannZeta 4 = π ^ 4 / 90
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zeta_nat_eq_tsum_of_gt_one`：zeta_nat_eq_tsum_of_gt_one {k : Nat} (hk : 1
 < k) : riemannZeta k = ∑' n : Nat, 1 / (n : Complex) ^ k
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_zeta_four`：hasSum_zeta_four : HasSum (fun n : Nat => (1 : Real) /
 (n : Real) ^ 4) (π ^ 4 / 90)
-/
theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert! congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : ℂ) = (4 : ℕ) by simp,
      zeta_nat_eq_tsum_of_gt_one (by simp : 1 < 4)]
    simp only [push_cast]
  · norm_cast

/-- Value of Riemann zeta at `-ℕ` in terms of `bernoulli'`. -/
/-
**riemannZeta_neg_nat_eq_bernoulli'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_neg_nat_eq_bernoulli' (k : Nat) : riemannZeta (-k) = -bernoull
i' (k + 1) / (k + 1)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `riemannZeta_zero`：riemannZeta_zero : riemannZeta 0 = -1 / 2
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `bernoulli'_one`：bernoulli' 1 = 1 / 2
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Rat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1
 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HurwitzZeta.hurwitzZeta_zero`：HurwitzZeta.hurwitzZeta_zero : hurwitzZeta
 0 = riemannZeta
· 使用定理 `QuotientAddGroup.mk_zero`：∀ {G : Type u_1} [inst : AddGroup G] (N : AddS
ubgroup G) [nN : N.Normal], ↑0 = 0
· 使用定理 `HurwitzZeta.hurwitzZeta_neg_nat`：hurwitzZeta_neg_nat (hk : k != 0) (hx :
 x in Icc (0 : Real) 1) : hurwitzZeta x (-k) = -1 / (k + 1) * ((Polynomial.berno
ulli (k + 1)).map (al…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `Polynomial.eval_zero_map`：eval_zero_map (f : R ->+* S) (p : R[X]) : (p.m
ap f).eval 0 = f (p.eval 0)
· 使用定理 `Polynomial.bernoulli_eval_zero`：bernoulli_eval_zero (n : Nat) : (bernoul
li n).eval 0 = _root_.bernoulli n
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Rat.smul_one_eq_cast`：smul_one_eq_cast (A : Type*) [DivisionRing A] (m :
 Rat) : m • (1 : A) = ↑m
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `bernoulli_eq_bernoulli'_of_ne_one`：∀ {n : ℕ}, n ≠ 1 → bernoulli n = bern
oulli' n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Value of Riemann zeta at `-ℕ` in terms of `bernoulli'`.
-/
theorem riemannZeta_neg_nat_eq_bernoulli' (k : ℕ) :
    riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero, zero_add, zero_add, div_one,
      bernoulli'_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

/-- Value of Riemann zeta at `-ℕ` in terms of `bernoulli`. -/
/-
**riemannZeta_neg_nat_eq_bernoulli** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_neg_nat_eq_bernoulli (k : Nat) : riemannZeta (-k) = (-1 : Comp
lex) ^ k * bernoulli (k + 1) / (k + 1)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `riemannZeta_neg_nat_eq_bernoulli'`：riemannZeta_neg_nat_eq_bernoulli' (k 
: Nat) : riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1)
· 使用定理 `bernoulli.eq_1`：∀ (n : ℕ), bernoulli n = (-1) ^ n * bernoulli' n
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用引理 `Rat.cast_pow`：cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Value of Riemann zeta at `-ℕ` in terms of `bernoulli`.
-/
theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rw [riemannZeta_neg_nat_eq_bernoulli', bernoulli, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, ← neg_one_mul, ← mul_assoc, pow_succ, ← mul_assoc, ← mul_pow, neg_one_mul (-1),
    neg_neg, one_pow, one_mul]
