/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# The Euler-Mascheroni constant `γ`

We define the constant `γ`, and give upper and lower bounds for it.

## Main definitions and results

* `Real.eulerMascheroniConstant`: the constant `γ`
* `Real.tendsto_harmonic_sub_log`: the sequence `n ↦ harmonic n - log n` tends to `γ` as `n → ∞`
* `one_half_lt_eulerMascheroniConstant` and `eulerMascheroniConstant_lt_two_thirds`: upper and
  lower bounds.

## Outline of proofs

We show that

* the sequence `eulerMascheroniSeq` given by `n ↦ harmonic n - log (n + 1)` is strictly increasing;
* the sequence `eulerMascheroniSeq'` given by `n ↦ harmonic n - log n`, modified with a junk value
  for `n = 0`, is strictly decreasing;
* the difference `eulerMascheroniSeq' n - eulerMascheroniSeq n` is non-negative and tends to 0.

It follows that both sequences tend to a common limit `γ`, and we have the inequality
`eulerMascheroniSeq n < γ < eulerMascheroniSeq' n` for all `n`. Taking `n = 6` gives the bounds
`1 / 2 < γ < 2 / 3`.
-/

@[expose] public section

open Filter Topology

namespace Real

section LowerSequence

/-- The sequence with `n`-th term `harmonic n - log (n + 1)`. -/
/-
**Real.eulerMascheroniSeq** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：eulerMascheroniSeq (n : Nat) : Real
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequence with `n`-th term `harmonic n - log (n + 1)`.
-/
noncomputable def eulerMascheroniSeq (n : ℕ) : ℝ := harmonic n - log (n + 1)
/-
**Real.eulerMascheroniSeq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：eulerMascheroniSeq_zero : eulerMascheroniSeq 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eulerMascheroniSeq_zero : eulerMascheroniSeq 0 = 0 := by
  simp [eulerMascheroniSeq, harmonic_zero]
/-
**Real.strictMono_eulerMascheroniSeq** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：strictMono_eulerMascheroniSeq : StrictMono eulerMascheroniSeq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.eulerMascheroniSeq.eq_1`：∀ (n : ℕ), Real.eulerMascheroniSeq n = ↑(h
armonic n) - Real.log (↑n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_sub_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b - (c - d) = a - c - (b - d)
· 使用引理 `harmonic_succ`：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n +
 (↑(n + 1))⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Real.log_div`：log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x 
- log y
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 54 条，此处仅展示前 30 条）
-/
lemma strictMono_eulerMascheroniSeq : StrictMono eulerMascheroniSeq := by
  refine strictMono_nat_of_lt_succ (fun n ↦ ?_)
  rw [eulerMascheroniSeq, eulerMascheroniSeq, ← sub_pos, sub_sub_sub_comm,
    harmonic_succ, add_comm, Rat.cast_add, add_sub_cancel_right,
    ← log_div (by positivity) (by positivity), add_div, Nat.cast_add_one,
    Nat.cast_add_one, div_self (by positivity), sub_pos, one_div, Rat.cast_inv, Rat.cast_add,
    Rat.cast_one, Rat.cast_natCast]
  refine (log_lt_sub_one_of_pos ?_ (ne_of_gt <| lt_add_of_pos_right _ ?_)).trans_le (le_of_eq ?_)
  · positivity
  · positivity
  · simp only [add_sub_cancel_left]
/-
**Real.one_half_lt_eulerMascheroniSeq_six** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：one_half_lt_eulerMascheroniSeq_six : 1 / 2 < eulerMascheroniSeq 6
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.eulerMascheroniSeq.eq_1`：∀ (n : ℕ), Real.eulerMascheroniSeq n = ↑(h
armonic n) - Real.log (↑n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `harmonic_succ`：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n +
 (↑(n + 1))⁻¹
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ratCast`：∀ {R : Type u_1} [inst : DivisionRin
g R] {q : ℚ} {n : ℕ},   Mathlib.Meta.NormNum.IsNat q n → Mathlib.Meta.NormNum.Is
Nat (↑q) n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
（共 65 条，此处仅展示前 30 条）
-/
lemma one_half_lt_eulerMascheroniSeq_six : 1 / 2 < eulerMascheroniSeq 6 := by
  have : eulerMascheroniSeq 6 = 49 / 20 - log 7 := by
    rw [eulerMascheroniSeq]
    norm_num
  rw [this, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', log_lt_iff_lt_exp (by positivity)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

end LowerSequence

section UpperSequence

/-- The sequence with `n`-th term `harmonic n - log n`. We use a junk value for `n = 0`, in order
to have the sequence be strictly decreasing. -/
/-
**Real.eulerMascheroniSeq'** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：eulerMascheroniSeq' (n : Nat) : Real
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequence with `n`-th term `harmonic n - log n`. We use a junk value for `n =
 0`, in order
to have the sequence be strictly decreasing.
-/
noncomputable def eulerMascheroniSeq' (n : ℕ) : ℝ :=
  if n = 0 then 2 else ↑(harmonic n) - log n
/-
**Real.eulerMascheroniSeq'_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.eulerMascheroniSeq' 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `harmonic_succ`：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n +
 (↑(n + 1))⁻¹
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eulerMascheroniSeq'_one : eulerMascheroniSeq' 1 = 1 := by
  simp [eulerMascheroniSeq']
/-
**Real.strictAnti_eulerMascheroniSeq'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：strictAnti_eulerMascheroniSeq' : StrictAnti eulerMascheroniSeq'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictAnti_nat_of_succ_lt`：strictAnti_nat_of_succ_lt {f : Nat -> α} (hf 
: forall n, f (n + 1) < f n) : StrictAnti f
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `harmonic_succ`：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n +
 (↑(n + 1))⁻¹
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `eq_false_intro`：eq_false_intro {a : Prop} (h : ¬a) : a = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 97 条，此处仅展示前 30 条）
-/
lemma strictAnti_eulerMascheroniSeq' : StrictAnti eulerMascheroniSeq' := by
  refine strictAnti_nat_of_succ_lt (fun n ↦ ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerMascheroniSeq']
  simp_rw [eulerMascheroniSeq', eq_false_intro hn.ne', reduceCtorEq, if_false]
  rw [← sub_pos, sub_sub_sub_comm,
    harmonic_succ, Rat.cast_add, ← sub_sub, sub_self, zero_sub, sub_eq_add_neg, neg_sub,
    ← sub_eq_neg_add, sub_pos, ← log_div (by positivity) (by positivity), ← neg_lt_neg_iff,
    ← log_inv]
  refine (log_lt_sub_one_of_pos ?_ ?_).trans_le (le_of_eq ?_)
  · positivity
  · simp [field]
  · simp [field]
/-
**Real.eulerMascheroniSeq'_six_lt_two_thirds** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.eulerMascheroniSeq' 6 < 2 / 3
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.eulerMascheroniSeq'.eq_1`：∀ (n : ℕ), Real.eulerMascheroniSeq' n = i
f n = 0 then 2 else ↑(harmonic n) - Real.log ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `harmonic_succ`：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n +
 (↑(n + 1))⁻¹
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ratCast`：∀ {R : Type u_1} [inst : DivisionRin
g R] {q : ℚ} {n : ℕ},   Mathlib.Meta.NormNum.IsNat q n → Mathlib.Meta.NormNum.Is
Nat (↑q) n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 77 条，此处仅展示前 30 条）
-/
lemma eulerMascheroniSeq'_six_lt_two_thirds : eulerMascheroniSeq' 6 < 2 / 3 := by
  have h1 : eulerMascheroniSeq' 6 = 49 / 20 - log 6 := by
    rw [eulerMascheroniSeq']
    norm_num
  rw [h1, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_log_iff_exp_lt (by positivity)]
  norm_num
  have := rpow_lt_rpow (exp_pos _).le exp_one_lt_d9 (by simp : (0 : ℝ) < 107 / 60)
  rw [exp_one_rpow] at this
  refine lt_trans this ?_
  rw [← rpow_lt_rpow_iff (z := 60), ← rpow_mul, div_mul_cancel₀, ← Nat.cast_ofNat,
    ← Nat.cast_ofNat, rpow_natCast, Nat.cast_ofNat, ← Nat.cast_ofNat (n := 60), rpow_natCast]
  · norm_num
  all_goals positivity
/-
**Real.eulerMascheroniSeq_lt_eulerMascheroniSeq'** 是 Mathlib 中的一个引理，位于命名空间 `Real
`。
形式化陈述：eulerMascheroniSeq_lt_eulerMascheroniSeq' (m n : Nat) : eulerMascheroniSeq
 m < eulerMascheroniSeq' n
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `sub_lt_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] [AddRightStrictMono α] {a b : α},   a < b → ∀ (c : α), c - b <
 c - …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
（共 75 条，此处仅展示前 30 条）
-/
lemma eulerMascheroniSeq_lt_eulerMascheroniSeq' (m n : ℕ) :
    eulerMascheroniSeq m < eulerMascheroniSeq' n := by
  have (r : ℕ) : eulerMascheroniSeq r < eulerMascheroniSeq' r := by
    rcases eq_zero_or_pos r with rfl | hr
    · simp [eulerMascheroniSeq, eulerMascheroniSeq']
    simp only [eulerMascheroniSeq, eulerMascheroniSeq', hr.ne', if_false]
    gcongr
    linarith
  apply (strictMono_eulerMascheroniSeq.monotone (le_max_left m n)).trans_lt
  exact (this _).trans_le (strictAnti_eulerMascheroniSeq'.antitone (le_max_right m n))

end UpperSequence

/-- The Euler-Mascheroni constant `γ`. -/
/-
**Real.eulerMascheroniConstant** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：eulerMascheroniConstant : Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The Euler-Mascheroni constant `γ`.
-/
noncomputable def eulerMascheroniConstant : ℝ := limUnder atTop eulerMascheroniSeq
/-
**Real.tendsto_eulerMascheroniSeq** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_eulerMascheroniSeq : Tendsto eulerMascheroniSeq atTop (𝓝 eulerMasc
heroniConstant)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Real.strictMono_eulerMascheroniSeq`：strictMono_eulerMascheroniSeq : Stri
ctMono eulerMascheroniSeq
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.eulerMascheroniSeq_lt_eulerMascheroniSeq'`：eulerMascheroniSeq_lt_eu
lerMascheroniSeq' (m n : Nat) : eulerMascheroniSeq m < eulerMascheroniSeq' n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.eulerMascheroniConstant.eq_1`：Real.eulerMascheroniConstant = Filter
.atTop.limUnder Real.eulerMascheroniSeq
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
-/
lemma tendsto_eulerMascheroniSeq :
    Tendsto eulerMascheroniSeq atTop (𝓝 eulerMascheroniConstant) := by
  have := tendsto_atTop_ciSup strictMono_eulerMascheroniSeq.monotone ?_
  · rwa [eulerMascheroniConstant, this.limUnder_eq]
  · exact ⟨_, fun _ ⟨_, hn⟩ ↦ hn ▸ (eulerMascheroniSeq_lt_eulerMascheroniSeq' _ 1).le⟩
/-
**Real.tendsto_harmonic_sub_log_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_harmonic_sub_log_add_one : Tendsto (fun n : Nat => harmonic n - lo
g (n + 1)) atTop (𝓝 eulerMascheroniConstant)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.tendsto_eulerMascheroniSeq`：tendsto_eulerMascheroniSeq : Tendsto eu
lerMascheroniSeq atTop (𝓝 eulerMascheroniConstant)
-/
lemma tendsto_harmonic_sub_log_add_one :
    Tendsto (fun n : ℕ ↦ harmonic n - log (n + 1)) atTop (𝓝 eulerMascheroniConstant) :=
  tendsto_eulerMascheroniSeq
/-
**Real.tendsto_eulerMascheroniSeq'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_eulerMascheroniSeq' : Tendsto eulerMascheroniSeq' atTop (𝓝 eulerMa
scheroniConstant)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.tendsto_log_comp_add_sub_log`：tendsto_log_comp_add_sub_log (y : Rea
l) : Tendsto (fun x : Real => log (x + y) - log x) atTop (𝓝 0)
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用引理 `eq_false_intro`：eq_false_intro {a : Prop} (h : ¬a) : a = False
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `Real.tendsto_eulerMascheroniSeq`：tendsto_eulerMascheroniSeq : Tendsto eu
lerMascheroniSeq atTop (𝓝 eulerMascheroniConstant)
-/
lemma tendsto_eulerMascheroniSeq' :
    Tendsto eulerMascheroniSeq' atTop (𝓝 eulerMascheroniConstant) := by
  suffices Tendsto (fun n ↦ eulerMascheroniSeq' n - eulerMascheroniSeq n) atTop (𝓝 0) by
    simpa using this.add tendsto_eulerMascheroniSeq
  suffices Tendsto (fun x : ℝ ↦ log (x + 1) - log x) atTop (𝓝 0) by
    apply (this.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [eulerMascheroniSeq, eulerMascheroniSeq', eq_false_intro hn]
  exact tendsto_log_comp_add_sub_log 1
/-
**Real.tendsto_harmonic_sub_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_harmonic_sub_log : Tendsto (fun n : Nat => harmonic n - log n) atT
op (𝓝 eulerMascheroniConstant)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用引理 `Real.tendsto_eulerMascheroniSeq'`：tendsto_eulerMascheroniSeq' : Tendsto 
eulerMascheroniSeq' atTop (𝓝 eulerMascheroniConstant)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tendsto_harmonic_sub_log :
    Tendsto (fun n : ℕ ↦ harmonic n - log n) atTop (𝓝 eulerMascheroniConstant) := by
  apply tendsto_eulerMascheroniSeq'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp_rw [eulerMascheroniSeq', hn, if_false]
/-
**Real.eulerMascheroniSeq_lt_eulerMascheroniConstant** 是 Mathlib 中的一个引理，位于命名空间 `
Real`。
形式化陈述：eulerMascheroniSeq_lt_eulerMascheroniConstant (n : Nat) : eulerMascheroniS
eq n < eulerMascheroniConstant
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Real.strictMono_eulerMascheroniSeq`：strictMono_eulerMascheroniSeq : Stri
ctMono eulerMascheroniSeq
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Monotone.ge_of_tendsto`：Monotone.ge_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Real.tendsto_eulerMascheroniSeq`：tendsto_eulerMascheroniSeq : Tendsto eu
lerMascheroniSeq atTop (𝓝 eulerMascheroniConstant)
-/
lemma eulerMascheroniSeq_lt_eulerMascheroniConstant (n : ℕ) :
    eulerMascheroniSeq n < eulerMascheroniConstant := by
  refine (strictMono_eulerMascheroniSeq (Nat.lt_succ_self n)).trans_le ?_
  apply strictMono_eulerMascheroniSeq.monotone.ge_of_tendsto tendsto_eulerMascheroniSeq
/-
**Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'** 是 Mathlib 中的一个引理，位于命名空间 
`Real`。
形式化陈述：eulerMascheroniConstant_lt_eulerMascheroniSeq' (n : Nat) : eulerMascheroni
Constant < eulerMascheroniSeq' n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Antitone.le_of_tendsto`：Antitone.le_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用引理 `Real.strictAnti_eulerMascheroniSeq'`：strictAnti_eulerMascheroniSeq' : St
rictAnti eulerMascheroniSeq'
· 使用引理 `Real.tendsto_eulerMascheroniSeq'`：tendsto_eulerMascheroniSeq' : Tendsto 
eulerMascheroniSeq' atTop (𝓝 eulerMascheroniConstant)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma eulerMascheroniConstant_lt_eulerMascheroniSeq' (n : ℕ) :
    eulerMascheroniConstant < eulerMascheroniSeq' n := by
  refine lt_of_le_of_lt ?_ (strictAnti_eulerMascheroniSeq' (Nat.lt_succ_self n))
  apply strictAnti_eulerMascheroniSeq'.antitone.le_of_tendsto tendsto_eulerMascheroniSeq'

/-- Lower bound for `γ`. (The true value is about 0.57.) -/
/-
**Real.one_half_lt_eulerMascheroniConstant** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：one_half_lt_eulerMascheroniConstant : 1 / 2 < eulerMascheroniConstant
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.one_half_lt_eulerMascheroniSeq_six`：one_half_lt_eulerMascheroniSeq_
six : 1 / 2 < eulerMascheroniSeq 6
· 使用引理 `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`：eulerMascheroniSeq_l
t_eulerMascheroniConstant (n : Nat) : eulerMascheroniSeq n < eulerMascheroniCons
tant

--- 原说明 ---
Lower bound for `γ`. (The true value is about 0.57.)
-/
lemma one_half_lt_eulerMascheroniConstant : 1 / 2 < eulerMascheroniConstant :=
  one_half_lt_eulerMascheroniSeq_six.trans (eulerMascheroniSeq_lt_eulerMascheroniConstant _)

/-- Upper bound for `γ`. (The true value is about 0.57.) -/
/-
**Real.eulerMascheroniConstant_lt_two_thirds** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：eulerMascheroniConstant_lt_two_thirds : eulerMascheroniConstant < 2 / 3
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'`：eulerMascheroniCons
tant_lt_eulerMascheroniSeq' (n : Nat) : eulerMascheroniConstant < eulerMascheron
iSeq' n
· 使用定理 `Real.eulerMascheroniSeq'_six_lt_two_thirds`：Real.eulerMascheroniSeq' 6 <
 2 / 3

--- 原说明 ---
Upper bound for `γ`. (The true value is about 0.57.)
-/
lemma eulerMascheroniConstant_lt_two_thirds : eulerMascheroniConstant < 2 / 3 :=
  (eulerMascheroniConstant_lt_eulerMascheroniSeq' _).trans eulerMascheroniSeq'_six_lt_two_thirds

end Real

