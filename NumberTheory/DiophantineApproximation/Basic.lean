/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.Basic

/-!
# Diophantine Approximation

The first part of this file gives proofs of various versions of
**Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2} \,.$$
The proof is based on the pigeonhole principle.

The second part of the file gives a proof of **Legendre's Theorem** on rational approximation,
which states that if $\xi$ is a real number and $x/y$ is a rational number such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{2y^2} \,,$$
then $x/y$ must be a convergent of the continued fraction expansion of $\xi$.

## Main statements

The main results are three variants of Dirichlet's approximation theorem:
* `Real.exists_int_int_abs_mul_sub_le`, which states that for all real `ξ` and natural `0 < n`,
  there are integers `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `Real.exists_nat_abs_mul_sub_round_le`, which replaces `j` by `round(k*ξ)` and uses
  a natural number `k`,
* `Real.exists_rat_abs_sub_le_and_den_le`, which says that there is a rational number `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.den)` and `q.den ≤ n`,

and
* `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, which states that
  for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.den^2}` is infinite.

We also show a converse,
* `Rat.finite_rat_abs_sub_lt_one_div_den_sq`, which states that the set above is finite
  when `ξ` is a rational number.

Both statements are combined to give an equivalence,
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.

There are two versions of Legendre's Theorem. One, `Real.exists_rat_eq_convergent`, uses
`Real.convergent`, a simple recursive definition of the convergents that is also defined
in this file, whereas the other, `Real.exists_convs_eq_rat` defined in the file
`Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`, uses
`GenContFract.convs` of `GenContFract.of ξ`.

## Implementation notes

We use the namespace `Real` for the results on real numbers and `Rat` for the results
on rational numbers. We introduce a secondary namespace `Real.ContfracLegendre`
to separate off a definition and some technical auxiliary lemmas used in the proof
of Legendre's Theorem. For remarks on the proof of Legendre's Theorem, see below.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>
<https://de.wikipedia.org/wiki/Kettenbruch> (The German Wikipedia page on continued
fractions is much more extensive than the English one.)

## Tags

Diophantine approximation, Dirichlet's approximation theorem, continued fraction
-/

@[expose] public section


namespace Real

section Dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.
-/


open Finset Int

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`,
with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`.

See also `Real.exists_nat_abs_mul_sub_round_le`. -/
/-
**Real.exists_int_int_abs_mul_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_int_int_abs_mul_sub_le (ξ : Real) {n : Nat} (n_pos : 0 < n) : exist
s j k : Int, 0 < k ∧ k <= n ∧ |↑k * ξ - j| <= 1 / (n + 1)
参数：ξ : Real；n_pos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `mul_lt_of_lt_one_left`：mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 
0 < b) (h : a < 1) : a * b < b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Int.fract_zero`：fract_zero : fract (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Int.floor_zero`：floor_zero : ⌊(0 : R)⌋ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 108 条，此处仅展示前 30 条）

--- 原说明 ---
*Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`
,
with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`.

See also `Real.exists_nat_abs_mul_sub_round_le`.
-/
theorem exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1) := by
  let f : ℤ → ℤ := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  have hn : 0 < (n : ℝ) + 1 := mod_cast Nat.succ_pos _
  have hfu := fun m : ℤ => mul_lt_of_lt_one_left hn <| fract_lt_one (ξ * ↑m)
  conv in |_| ≤ _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Icc (0 : ℤ) n
  by_cases! H : ∃ m ∈ D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : ℤ) : ℝ) ≤ fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        simp only [f, cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (mem_Icc.mp hm).1
      exact mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, ?_⟩
    rw [cast_add, ← sub_sub, sub_mul, cast_one, one_mul, abs_le]
    refine
      ⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr <| le_of_lt <| (hfu m).trans <| lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using! hf'
  · have hD : #(Ico (0 : ℤ) n) < #D := by rw [card_Icc, card_Ico]; exact lt_add_one n
    have hfu' : ∀ m, f m ≤ n := fun m => lt_add_one_iff.mp (floor_lt.mpr (mod_cast hfu m))
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    refine
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
        sub_le_iff_le_add.mpr <| le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, ?_⟩
    convert_to! |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1
    · congr; push_cast; simp only [fract]; ring
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a natural number `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
/-
**Real.exists_nat_abs_mul_sub_round_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_nat_abs_mul_sub_round_le (ξ : Real) {n : Nat} (n_pos : 0 < n) : exi
sts k : Nat, 0 < k ∧ k <= n ∧ |↑k * ξ - round (↑k * ξ)| <= 1 / (n + 1)
参数：ξ : Real；n_pos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exists_int_int_abs_mul_sub_le`：exists_int_int_abs_mul_sub_le (ξ : R
eal) {n : Nat} (n_pos : 0 < n) : exists j k : Int, 0 < k ∧ k <= n ∧ |↑k * ξ - j|
 <= 1 / (n + 1)
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `round_le`：round_le (x : α) (z : Int) : |x - round x| <= |x - z|

--- 原说明 ---
*Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a natural number `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
theorem exists_nat_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk := toNat_of_nonneg hk₀.le
  rw [← hk] at hk₀ hk₁ h
  exact ⟨k.toNat, natCast_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.

See also `AddCircle.exists_norm_nsmul_le`. -/
/-
**Real.exists_rat_abs_sub_le_and_den_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_rat_abs_sub_le_and_den_le (ξ : Real) {n : Nat} (n_pos : 0 < n) : ex
ists q : Rat, |ξ - q| <= 1 / ((n + 1) * q.den) ∧ q.den <= n
参数：ξ : Real；n_pos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exists_int_int_abs_mul_sub_le`：exists_int_int_abs_mul_sub_le (ξ : R
eal) {n : Nat} (n_pos : 0 < n) : exists j k : Int, 0 < k ∧ k <= n ∧ |↑k * ξ - j|
 <= 1 / (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.intCast_div_eq_divInt`：intCast_div_eq_divInt (n d : Int) : (n : Rat)
 / d = n /. d
· 使用定理 `Int.le_of_dvd`：∀ {a b : ℤ}, 0 < b → a ∣ b → a ≤ b
· 使用定理 `Rat.den_dvd`：den_dvd (a b : Int) : ((a /. b).den : Int) ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
*Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.

See also `AddCircle.exists_norm_nsmul_le`.
-/
theorem exists_rat_abs_sub_le_and_den_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.den) ∧ q.den ≤ n := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk₀' : (0 : ℝ) < k := Int.cast_pos.mpr hk₀
  have hden : ((j / k : ℚ).den : ℤ) ≤ k := by
    convert! le_of_dvd hk₀ (Rat.den_dvd j k)
    exact Rat.intCast_div_eq_divInt _ _
  refine ⟨j / k, ?_, Nat.cast_le.mp (hden.trans hk₁)⟩
  rw [← div_div, le_div_iff₀ (Nat.cast_pos.mpr <| Rat.pos _ : (0 : ℝ) < _)]
  refine (mul_le_mul_of_nonneg_left (Int.cast_le.mpr hden : _ ≤ (k : ℝ)) (abs_nonneg _)).trans ?_
  rwa [← abs_of_pos hk₀', Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, ← abs_mul, sub_mul,
    div_mul_cancel₀ _ hk₀'.ne', mul_comm]

end Dirichlet

section RatApprox

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/


open Set

/-- Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`. -/
/-
**Real.exists_rat_abs_sub_lt_and_lt_of_irrational** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l`。
形式化陈述：exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : Real} (hξ : Irrational ξ) 
(q : Rat) : exists q' : Rat, |ξ - q'| < 1 / (q'.den : Real) ^ 2 ∧ |ξ - q'| < |ξ 
- q|
参数：hξ : Irrational ξ；q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Irrational.ne_rat`：ne_rat (h : Irrational x) (q : Rat) : x != q
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exists_rat_abs_sub_le_and_den_le`：exists_rat_abs_sub_le_and_den_le 
(ξ : Real) {n : Nat} (n_pos : 0 < n) : exists q : Rat, |ξ - q| <= 1 / ((n + 1) *
 q.den) ∧ q.den <= n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `one_div_lt_one_div`：one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a
 < 1 / b ↔ b < a
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`.
-/
theorem exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : ℝ} (hξ : Irrational ξ) (q : ℚ) :
    ∃ q' : ℚ, |ξ - q'| < 1 / (q'.den : ℝ) ^ 2 ∧ |ξ - q'| < |ξ - q| := by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  have m_pos : (0 : ℝ) < m := (one_div_pos.mpr h).trans hm
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  have den_pos : (0 : ℝ) < q'.den := Nat.cast_pos.mpr q'.pos
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  refine
    ⟨q', lt_of_le_of_lt hbd ?_,
      lt_of_le_of_lt hbd <|
        (one_div_lt md_pos h).mpr <|
          hm.trans <|
            lt_of_lt_of_le (lt_add_one _) <|
              (le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr <|
                mod_cast (q'.pos : 1 ≤ q'.den)⟩
  rw [sq, one_div_lt_one_div md_pos (mul_pos den_pos den_pos), mul_lt_mul_iff_left₀ den_pos]
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
/-
**Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational** 是 Mathlib 中的一个定理，位
于命名空间 `Real`。
形式化陈述：infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : Real} (hξ : Irra
tional ξ) : {q : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2}.Infinite
参数：hξ : Irrational ξ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `Set.exists_min_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Real.exists_rat_abs_sub_lt_and_lt_of_irrational`：exists_rat_abs_sub_lt_a
nd_lt_of_irrational {ξ : Real} (hξ : Irrational ξ) (q : Rat) : exists q' : Rat, 
|ξ - q'| < 1 / (q'.den : Real) ^ 2 ∧ …
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c

--- 原说明 ---
If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`.
-/
theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : ℝ} (hξ : Irrational ξ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)

end RatApprox

end Real

namespace Rat

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/


open Set

/-- If `ξ` is rational, then the good rational approximations to `ξ` have bounded
numerator and denominator. -/
/-
**Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq** 是 Mathlib 中的一个定理，位于命名空间 `R
at`。
形式化陈述：den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : Rat} (h : |ξ - q| < 1
 / (q.den : Rat) ^ 2) : q.den <= ξ.den ∧ ⌈ξ * q.den⌉ - 1 <= q.num ∧ q.num <= ⌊ξ 
* q.den⌋ + 1
参数：h : |ξ - q| < 1 / (q.den : Rat) ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `div_mul`：div_mul : a / b * c = a / (b / c)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_lt_div`：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If `ξ` is rational, then the good rational approximations to `ξ` have bounded
numerator and denominator.
-/
theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : ℚ}
    (h : |ξ - q| < 1 / (q.den : ℚ) ^ 2) :
    q.den ≤ ξ.den ∧ ⌈ξ * q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * q.den⌋ + 1 := by
  have hq₀ : (0 : ℚ) < q.den := Nat.cast_pos.mpr q.pos
  replace h : |ξ * q.den - q.num| < 1 / q.den := by
    rw [← mul_lt_mul_iff_left₀ hq₀] at h
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    rwa [sq, div_mul, mul_div_cancel_left₀ _ hq₀.ne'] at h
  constructor
  · rcases eq_or_ne ξ q with (rfl | H)
    · exact le_rfl
    · have hξ₀ : (0 : ℚ) < ξ.den := Nat.cast_pos.mpr ξ.pos
      rw [← Rat.num_div_den ξ, div_mul_eq_mul_div, div_sub' hξ₀.ne', abs_div, abs_of_pos hξ₀,
        div_lt_iff₀ hξ₀, div_mul_comm, mul_one] at h
      refine Nat.cast_le.mp ((one_lt_div hq₀).mp <| lt_of_le_of_lt ?_ h).le
      norm_cast
      rw [mul_comm _ q.num]
      exact Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
  · obtain ⟨h₁, h₂⟩ :=
      abs_sub_lt_iff.mp
        (h.trans_le <|
          (one_div_le zero_lt_one hq₀).mp <| (@one_div_one ℚ _).symm ▸ Nat.cast_le.mpr q.pos)
    rw [sub_lt_iff_lt_add, add_comm] at h₁ h₂
    rw [← sub_lt_iff_lt_add] at h₂
    norm_cast at h₁ h₂
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩

/-- A rational number has only finitely many good rational approximations. -/
/-
**Rat.finite_rat_abs_sub_lt_one_div_den_sq** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：finite_rat_abs_sub_lt_one_div_den_sq (ξ : Rat) : {q : Rat | |ξ - q| < 1 / 
(q.den : Rat) ^ 2}.Finite
参数：ξ : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq`：den_le_and_le_num_le_
of_sub_lt_one_div_den_sq {ξ q : Rat} (h : |ξ - q| < 1 / (q.den : Rat) ^ 2) : q.d
en <= ξ.den ∧ ⌈ξ * q.den⌉ - 1 <= q.num …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oc a b ↔ a < x ∧ x ≤ b
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_singleton`：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, 
b)) '' s
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Set.finite_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
 α] (b a : α), (Set.Ioc b a).Finite
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
A rational number has only finitely many good rational approximations.
-/
theorem finite_rat_abs_sub_lt_one_div_den_sq (ξ : ℚ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}.Finite := by
  let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  set s := {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  have H : f '' s ⊆ ⋃ (y : ℕ) (_ : y ∈ Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, ?_⟩
    simp only [prod_singleton, mem_image, mem_Icc]
    exact ⟨q.num, hn, hq₂⟩
  refine (Finite.subset ?_ H).of_finite_image hinj.injOn
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)

end Rat

/-- The set of good rational approximations to a real number `ξ` is infinite if and only if
`ξ` is irrational. -/
/-
**Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : Real) : {q
 : Rat | |ξ - q| < 1 / (q.den : Real) ^ 2}.Infinite ↔ Irrational ξ
参数：ξ : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `irrational_iff_ne_rational`：irrational_iff_ne_rational (x : Real) : Irra
tional x ↔ forall a b : Int, b != 0 -> x != a / b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用引理 `Rat.cast_pow`：cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Rat.finite_rat_abs_sub_lt_one_div_den_sq`：finite_rat_abs_sub_lt_one_div_
den_sq (ξ : Rat) : {q : Rat | |ξ - q| < 1 / (q.den : Rat) ^ 2}.Finite
· 使用定理 `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`：infinite_rat_
abs_sub_lt_one_div_den_sq_of_irrational {ξ : Real} (hξ : Irrational ξ) : {q : Ra
t | |ξ - q| < 1 / (q.den : Real) ^ 2}.Infinite

--- 原说明 ---
The set of good rational approximations to a real number `ξ` is infinite if and 
only if
`ξ` is irrational.
-/
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : ℝ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite ↔ Irrational ξ := by
  refine
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b _ => ?_,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  contrapose! h
  convert! Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : ℚ) / b) with q
  rw [h, (by (push_cast; rfl) : (1 : ℝ) / (q.den : ℝ) ^ 2 = (1 / (q.den : ℚ) ^ 2 : ℚ))]
  norm_cast

/-!
### Legendre's Theorem on Rational Approximation

We prove **Legendre's Theorem** on rational approximation: If $\xi$ is a real number and
$x/y$ is a rational number such that $|\xi - x/y| < 1/(2y^2)$,
then $x/y$ is a convergent of the continued fraction expansion of $\xi$.

The proof is by induction. However, the induction proof does not work with the
statement as given, since the assumption is too weak to imply the corresponding
statement for the application of the induction hypothesis. This can be remedied
by making the statement slightly stronger. Namely, we assume that $|\xi - x/y| < 1/(y(2y-1))$
when $y \ge 2$ and $-\frac{1}{2} < \xi - x < 1$ when $y = 1$.
-/


section Convergent

namespace Real

open Int

/-!
### Convergents: definition and API lemmas
-/


/-- We give a direct recursive definition of the convergents of the continued fraction
expansion of a real number `ξ`. The main reason for that is that we want to have the
convergents as rational numbers; the versions `(GenContFract.of ξ).convs` and
`(GenContFract.of ξ).convs'` always give something of the same type as `ξ`.
We can then also use dot notation `ξ.convergent n`.
Another minor reason is that this demonstrates that the proof
of Legendre's theorem does not need anything beyond this definition.
We provide a proof that this definition agrees with the other one;
see `Real.convs_eq_convergent`.
(Note that we use the fact that `1/0 = 0` here to make it work for rational `ξ`.) -/
/-
**Real.convergent** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：ℝ → ℕ → ℚ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We give a direct recursive definition of the convergents of the continued fracti
on
expansion of a real number `ξ`. The main reason for that is that we want to have
 the
convergents as rational numbers; the versions `(GenContFract.of ξ).convs` and
`(GenContFract.of ξ).convs'` always give something of the same type as `ξ`.
We can then also use dot notation `ξ.convergent n`.
Another minor reason is that this demonstrates that the proof
of Legendre's theorem does not need anything beyond this definition.
We provide a proof that this definition agrees with the other one;
see `Real.convs_eq_convergent`.
(Note that we use the fact that `1/0 = 0` here to make it work for rational `ξ`.
)
-/
noncomputable def convergent : ℝ → ℕ → ℚ
  | ξ, 0 => ⌊ξ⌋
  | ξ, n + 1 => ⌊ξ⌋ + (convergent (fract ξ)⁻¹ n)⁻¹

/-- The zeroth convergent of `ξ` is `⌊ξ⌋`. -/
@[simp]
/-
**Real.convergent_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：convergent_zero (ξ : Real) : ξ.convergent 0 = ⌊ξ⌋
参数：ξ : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zeroth convergent of `ξ` is `⌊ξ⌋`.
-/
theorem convergent_zero (ξ : ℝ) : ξ.convergent 0 = ⌊ξ⌋ :=
  rfl

/-- The `(n+1)`th convergent of `ξ` is the `n`th convergent of `1/(fract ξ)`. -/
@[simp]
/-
**Real.convergent_succ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：convergent_succ (ξ : Real) (n : Nat) : ξ.convergent (n + 1) = ⌊ξ⌋ + ((frac
t ξ)⁻¹.convergent n)⁻¹
参数：ξ : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `(n+1)`th convergent of `ξ` is the `n`th convergent of `1/(fract ξ)`.
-/
theorem convergent_succ (ξ : ℝ) (n : ℕ) :
    ξ.convergent (n + 1) = ⌊ξ⌋ + ((fract ξ)⁻¹.convergent n)⁻¹ :=
  rfl

/-- All convergents of `0` are zero. -/
@[simp]
/-
**Real.convergent_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：convergent_of_zero (n : Nat) : convergent 0 n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_zero`：floor_zero : ⌊(0 : R)⌋ = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.fract_zero`：fract_zero : fract (0 : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
All convergents of `0` are zero.
-/
theorem convergent_of_zero (n : ℕ) : convergent 0 n = 0 := by
  induction n with
  | zero => simp only [convergent_zero, floor_zero, cast_zero]
  | succ n ih =>
    simp only [ih, convergent_succ, floor_zero, cast_zero, fract_zero, add_zero, inv_zero]

/-- If `ξ` is an integer, all its convergents equal `ξ`. -/
@[simp]
/-
**Real.convergent_of_int** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：convergent_of_int {ξ : Int} (n : Nat) : convergent ξ n = ξ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.fract_intCast`：fract_intCast (z : Int) : fract (z : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Real.convergent_of_zero`：convergent_of_zero (n : Nat) : convergent 0 n =
 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
If `ξ` is an integer, all its convergents equal `ξ`.
-/
theorem convergent_of_int {ξ : ℤ} (n : ℕ) : convergent ξ n = ξ := by
  cases n
  · simp only [convergent_zero, floor_intCast]
  · simp only [convergent_succ, floor_intCast, fract_intCast, convergent_of_zero, add_zero,
      inv_zero]

end Real

end Convergent

/-!
### The key technical condition for the induction proof
-/


namespace Real

open Int

-- this is not `private`, as it is used in the public `exists_rat_eq_convergent'` below.
/-- Define the technical condition to be used as assumption in the inductive proof. -/
/-
**Real.ContfracLegendre.Ass** 是 Mathlib 中的一个定义，位于命名空间 `Real.ContfracLegendre`。
形式化陈述：ℝ → ℤ → ℤ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the technical condition to be used as assumption in the inductive proof.
-/
def ContfracLegendre.Ass (ξ : ℝ) (u v : ℤ) : Prop :=
  IsCoprime u v ∧ (v = 1 → (-(1 / 2) : ℝ) < ξ - u) ∧
    |ξ - u / v| < ((v : ℝ) * (2 * v - 1))⁻¹

-- ### Auxiliary lemmas
-- This saves a few lines below, as it is frequently needed.
/-
**Real.aux** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux₀ {v : ℤ} (hv : 0 < v) : (0 : ℝ) < v ∧ (0 : ℝ) < 2 * v - 1 :=
  ⟨cast_pos.mpr hv, by norm_cast; lia⟩

-- In the following, we assume that `ass ξ u v` holds and `v ≥ 2`.
variable {ξ : ℝ} {u v : ℤ}

section
variable (hv : 2 ≤ v) (h : ContfracLegendre.Ass ξ u v)
include hv h

-- The fractional part of `ξ` is positive.
/-
**Real.aux** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux₁ : 0 < fract ξ := by
  have hv₀ : (0 : ℝ) < v := cast_pos.mpr (zero_lt_two.trans_le hv)
  obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv)
  obtain ⟨hcop, _, h⟩ := h
  refine fract_pos.mpr fun hf => ?_
  rw [hf] at h
  have H : (2 * v - 1 : ℝ) < 1 := by
    refine (mul_lt_iff_lt_one_right hv₀).1 ((inv_lt_inv₀ hv₀ (mul_pos hv₁ hv₂)).1 (h.trans_le' ?_))
    have h' : (⌊ξ⌋ : ℝ) - u / v = (⌊ξ⌋ * v - u) / v := by field
    rw [h', abs_div, abs_of_pos hv₀, ← one_div, div_le_div_iff_of_pos_right hv₀]
    norm_cast
    rw [← zero_add (1 : ℤ), add_one_le_iff, abs_pos, sub_ne_zero]
    rintro rfl
    cases isUnit_iff.mp (isCoprime_self.mp (IsCoprime.mul_left_iff.mp hcop).2) <;> lia
  norm_cast at H
  linarith only [hv, H]

-- An auxiliary lemma for the inductive step.
/-
**Real.aux** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux₂ : 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v := by
  obtain ⟨hcop, _, h⟩ := h
  obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have hv₁ : 0 < 2 * v - 1 := by linarith only [hv]
  rw [← one_div, lt_div_iff₀ (mul_pos hv₀ hv₀'), ← abs_of_pos (mul_pos hv₀ hv₀'), ← abs_mul,
    sub_mul, ← mul_assoc, ← mul_assoc, div_mul_cancel₀ _ hv₀.ne', abs_sub_comm, abs_lt,
    lt_sub_iff_add_lt, sub_lt_iff_lt_add, mul_assoc] at h
  have hu₀ : 0 ≤ u - ⌊ξ⌋ * v := by
    refine (mul_nonneg_iff_of_pos_right hv₁).mp ?_
    rw [← sub_one_lt_iff, zero_sub]
    replace h := h.1
    rw [← lt_sub_iff_add_lt, ← mul_assoc, ← sub_mul] at h
    exact mod_cast
      h.trans_le
        ((mul_le_mul_iff_left₀ <| hv₀').mpr <|
          (sub_le_sub_iff_left (u : ℝ)).mpr ((mul_le_mul_iff_left₀ hv₀).mpr (floor_le ξ)))
  have hu₁ : u - ⌊ξ⌋ * v ≤ v := by
    refine _root_.le_of_mul_le_mul_right (le_of_lt_add_one ?_) hv₁
    replace h := h.2
    rw [← sub_lt_iff_lt_add, ← mul_assoc, ← sub_mul, ← add_lt_add_iff_right (v * (2 * v - 1) : ℝ),
      add_comm (1 : ℝ)] at h
    have :=
      flip mul_lt_mul_of_pos_right hv₀' <| (sub_lt_sub_iff_left (u : ℝ)).mpr <|
          flip mul_lt_mul_of_pos_right hv₀ <| sub_right_lt_of_lt_add <| lt_floor_add_one ξ
    rw [sub_mul ξ, one_mul, ← sub_add, add_mul] at this
    exact mod_cast this.trans h
  have huv_cop : IsCoprime (u - ⌊ξ⌋ * v) v := by
    rwa [sub_eq_add_neg, ← neg_mul, IsCoprime.add_mul_right_left_iff]
  refine ⟨lt_of_le_of_ne' hu₀ fun hf => ?_, lt_of_le_of_ne hu₁ fun hf => ?_⟩ <;>
    · rw [hf] at huv_cop
      simp only [isCoprime_zero_left, isCoprime_self, isUnit_iff] at huv_cop
      rcases huv_cop with huv_cop | huv_cop <;> linarith only [hv, huv_cop]

-- The key step: the relevant inequality persists in the inductive step.
/-
**Real.aux** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux₃ :
    |(fract ξ)⁻¹ - v / (u - ⌊ξ⌋ * v)| < (((u : ℝ) - ⌊ξ⌋ * v) * (2 * (u - ⌊ξ⌋ * v) - 1))⁻¹ := by
  obtain ⟨hu₀, huv⟩ := aux₂ hv h
  have hξ₀ := aux₁ hv h
  set u' := u - ⌊ξ⌋ * v with hu'
  have hu'ℝ : (u' : ℝ) = u - ⌊ξ⌋ * v := mod_cast hu'
  rw [← hu'ℝ]
  replace hu'ℝ := (eq_sub_iff_add_eq.mp hu'ℝ).symm
  obtain ⟨Hu, Hu'⟩ := aux₀ hu₀
  obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have H₁ := div_pos (div_pos Hv Hu) hξ₀
  replace h := h.2.2
  have h' : |fract ξ - u' / v| < ((v : ℝ) * (2 * v - 1))⁻¹ := by
    rwa [hu'ℝ, add_div, mul_div_cancel_right₀ _ Hv.ne', ← sub_sub, sub_right_comm] at h
  have H : (2 * u' - 1 : ℝ) ≤ (2 * v - 1) * fract ξ := by
    replace h := (abs_lt.mp h).1
    have : (2 * (v : ℝ) - 1) * (-((v : ℝ) * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v := by
      field
    rw [hu'ℝ, add_div, mul_div_cancel_right₀ _ Hv.ne', ← sub_sub, sub_right_comm, self_sub_floor,
      lt_sub_iff_add_lt, ← mul_lt_mul_iff_right₀ Hv', this] at h
    refine LE.le.trans ?_ h.le
    rw [sub_le_sub_iff_left, div_le_one Hv, add_comm]
    exact mod_cast huv
  calc
    |(fract ξ)⁻¹ - v / u'| = |(fract ξ - u' / v) * (v / u' / fract ξ)| := by
      rw [abs_sub_comm]; congr 1; field
    _ = |fract ξ - u' / v| * (v / u' / fract ξ) := by rw [abs_mul, abs_of_pos H₁]
    _ < ((v : ℝ) * (2 * v - 1))⁻¹ * (v / u' / fract ξ) := by gcongr
    _ = (u' * ((2 * v - 1) * fract ξ))⁻¹ := by field
    _ ≤ (u' * (2 * u' - 1) : ℝ)⁻¹ := by gcongr

-- The conditions `ass ξ u v` persist in the inductive step.
/-
**Real.invariant** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem invariant : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * v) := by
  refine ⟨?_, fun huv => ?_, mod_cast aux₃ hv h⟩
  · rw [sub_eq_add_neg, ← neg_mul, isCoprime_comm, IsCoprime.add_mul_right_left_iff]
    exact h.1
  · obtain hv₀' := (aux₀ (zero_lt_two.trans_le hv)).2
    have Hv : (v * (2 * v - 1) : ℝ)⁻¹ + (v : ℝ)⁻¹ = 2 / (2 * v - 1) := by
      simp [field]
    have Huv : (u / v : ℝ) = ⌊ξ⌋ + (v : ℝ)⁻¹ := by
      rw [sub_eq_iff_eq_add'.mp huv]; simp [field]
    have h' := (abs_sub_lt_iff.mp h.2.2).1
    rw [Huv, ← sub_sub, sub_lt_iff_lt_add, self_sub_floor, Hv] at h'
    rwa [lt_sub_iff_add_lt', (by ring : (v : ℝ) + -(1 / 2) = (2 * v - 1) / 2),
      lt_inv_comm₀ (div_pos hv₀' zero_lt_two) (aux₁ hv h), inv_div]

end

/-!
### The main result
-/


/-- The technical version of *Legendre's Theorem*. -/
/-
**Real.exists_rat_eq_convergent'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_rat_eq_convergent' {v : Nat} (h : ContfracLegendre.Ass ξ u v) : exi
sts n, (u / v : Rat) = ξ.convergent n
参数：h : ContfracLegendre.Ass ξ u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Real.convergent_zero`：convergent_zero (ξ : Real) : ξ.convergent 0 = ⌊ξ⌋
· 使用定理 `Rat.intCast_inj`：∀ {a b : ℤ}, ↑a = ↑b ↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Int.floor_eq_iff`：floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
The technical version of *Legendre's Theorem*.
-/
theorem exists_rat_eq_convergent' {v : ℕ} (h : ContfracLegendre.Ass ξ u v) :
    ∃ n, (u / v : ℚ) = ξ.convergent n := by
  induction v using Nat.strong_induction_on generalizing ξ u with | h v ih => ?_
  rcases lt_trichotomy v 1 with (ht | rfl | ht)
  · replace h := h.2.2
    simp only [Nat.lt_one_iff.mp ht, Nat.cast_zero, div_zero, tsub_zero, zero_mul,
      cast_zero, inv_zero] at h
    exact False.elim (lt_irrefl _ <| (abs_nonneg ξ).trans_lt h)
  · rw [Nat.cast_one, div_one]
    obtain ⟨_, h₁, h₂⟩ := h
    rcases le_or_gt (u : ℝ) ξ with ht | ht
    · use 0
      rw [convergent_zero, Rat.intCast_inj, eq_comm, floor_eq_iff]
      convert! And.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2) <;> norm_num
    · replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl)
      have hξ₁ : ⌊ξ⌋ = u - 1 := by
        rw [floor_eq_iff, cast_sub, cast_one, sub_add_cancel]
        exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩
      rcases eq_or_ne ξ ⌊ξ⌋ with Hξ | Hξ
      · rw [Hξ, hξ₁, cast_sub, cast_one, ← sub_eq_add_neg, sub_lt_sub_iff_left] at h₁
        exact False.elim (lt_irrefl _ <| h₁.trans one_half_lt_one)
      · have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1 := by
          rw [floor_eq_iff, cast_one, le_inv_comm₀ zero_lt_one (fract_pos.mpr Hξ), inv_one,
            one_add_one_eq_two, inv_lt_comm₀ (fract_pos.mpr Hξ) zero_lt_two]
          refine ⟨(fract_lt_one ξ).le, ?_⟩
          rw [fract, hξ₁, cast_sub, cast_one, lt_sub_iff_add_lt', sub_add]
          convert! h₁ using 1
          rw [sub_eq_add_neg]
          norm_num
        use 1
        simp [convergent, hξ₁, hξ₂, cast_sub, cast_one]
  · obtain ⟨huv₀, huv₁⟩ := aux₂ (Nat.cast_le.mpr ht) h
    have Hv : (v : ℚ) ≠ 0 := (Nat.cast_pos.mpr (zero_lt_one.trans ht)).ne'
    have huv₁' : (u - ⌊ξ⌋ * v).toNat < v := by zify; rwa [toNat_of_nonneg huv₀.le]
    have inv : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).toNat :=
      (toNat_of_nonneg huv₀.le).symm ▸ invariant (Nat.cast_le.mpr ht) h
    obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).toNat huv₁' inv
    use n + 1
    rw [convergent_succ, ← hn,
      (mod_cast toNat_of_nonneg huv₀.le : ((u - ⌊ξ⌋ * v).toNat : ℚ) = u - ⌊ξ⌋ * v),
      cast_natCast, inv_div, sub_div, mul_div_cancel_right₀ _ Hv, add_sub_cancel]

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This version uses `Real.convergent`. -/
/-
**Real.exists_rat_eq_convergent** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_rat_eq_convergent {q : Rat} (h : |ξ - q| < 1 / (2 * (q.den : Real) 
^ 2)) : exists n, q = ξ.convergent n
参数：h : |ξ - q| < 1 / (2 * (q.den : Real) ^ 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.exists_rat_eq_convergent'`：exists_rat_eq_convergent' {v : Nat} (h :
 ContfracLegendre.Ass ξ u v) : exists n, (u / v : Rat) = ξ.convergent n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.isCoprime_iff_nat_coprime`：isCoprime_iff_nat_coprime {a b : Int} : I
sCoprime a b ↔ Nat.Coprime a.natAbs b.natAbs
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.den_eq_one_iff`：den_eq_one_iff (r : Rat) : r.den = 1 ↔ ↑r.num = r
· 使用定理 `Nat.cast_eq_one`：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
· 使用定理 `_private.Mathlib.NumberTheory.DiophantineApproximation.Basic.0.Real.aux₀
`：∀ {v : ℤ}, 0 < v → 0 < ↑v ∧ 0 < 2 * ↑v - 1
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q
.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This version uses `Real.convergent`.
-/
theorem exists_rat_eq_convergent {q : ℚ} (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, q = ξ.convergent n := by
  refine q.num_div_den ▸ exists_rat_eq_convergent' ⟨?_, fun hd => ?_, ?_⟩
  · exact isCoprime_iff_nat_coprime.mpr (natAbs_natCast q.den ▸ q.reduced)
  · rw [← q.den_eq_one_iff.mp (Nat.cast_eq_one.mp hd)] at h
    simpa only [Rat.den_intCast, Nat.cast_one, one_pow, mul_one] using! (abs_lt.mp h).1
  · obtain ⟨hq₀, hq₁⟩ := aux₀ (Nat.cast_pos.mpr q.pos)
    replace hq₁ := mul_pos hq₀ hq₁
    have hq₂ : (0 : ℝ) < 2 * (q.den * q.den) := mul_pos zero_lt_two (mul_pos hq₀ hq₀)
    rw [cast_natCast] at *
    rw [(by norm_cast : (q.num / q.den : ℝ) = (q.num / q.den : ℚ)), Rat.num_div_den]
    exact h.trans (by rw [← one_div, sq, one_div_lt_one_div hq₂ hq₁, ← sub_pos]; ring_nf; exact hq₀)

end Real

