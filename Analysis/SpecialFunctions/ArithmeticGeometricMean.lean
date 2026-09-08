/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# The arithmetic-geometric mean

Starting with two nonnegative real numbers, repeatedly replace them with their arithmetic and
geometric means. By the AM-GM inequality, the smaller number (geometric mean) will monotonically
increase and the larger number (arithmetic mean) will monotonically decrease.

The two monotone sequences converge to the same limit – the arithmetic-geometric mean (AGM).
This file defines the AGM in the `NNReal` namespace and proves some of its basic properties.

## References

* https://en.wikipedia.org/wiki/Arithmetic–geometric_mean
-/

@[expose] public section

namespace NNReal

/-- The AM–GM inequality for two `NNReal`s, with means in canonical form. -/
/-
**NNReal.sqrt_mul_le_half_add** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_mul_le_half_add (x y : Real>=0) : sqrt (x * y) <= (x + y) / 2
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.sqrt_le_iff_le_sq`：sqrt_le_iff_le_sq : sqrt x <= y ↔ x <= y ^ 2
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用引理 `four_mul_le_sq_add`：four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMo
no R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) : 4 * a * b <= (a + b) ^ 2
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The AM–GM inequality for two `NNReal`s, with means in canonical form.
-/
lemma sqrt_mul_le_half_add (x y : ℝ≥0) : sqrt (x * y) ≤ (x + y) / 2 := by
  rw [sqrt_le_iff_le_sq, div_pow, le_div_iff₀' (by positivity), ← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

/-- The strict AM–GM inequality for two `NNReal`s, with means in canonical form. -/
/-
**NNReal.sqrt_mul_lt_half_add_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_mul_lt_half_add_of_ne {x y : Real>=0} (h : x != y) : sqrt (x * y) < (
x + y) / 2
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `sq_pos_iff`：sq_pos_iff {a : R} : 0 < a ^ 2 ↔ a != 0
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `NNReal.sqrt_sq`：∀ (x : NNReal), NNReal.sqrt (x ^ 2) = x
· 使用引理 `NNReal.sqrt_lt_sqrt`：sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用引理 `lt_div_iff₀'`：lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
The strict AM–GM inequality for two `NNReal`s, with means in canonical form.
-/
lemma sqrt_mul_lt_half_add_of_ne {x y : ℝ≥0} (h : x ≠ y) : sqrt (x * y) < (x + y) / 2 := by
  wlog hl : y < x generalizing x y
  · specialize this h.symm (h.gt_or_lt.resolve_left hl)
    rwa [mul_comm, add_comm]
  have key : 0 < (x - y) ^ 2 := sq_pos_iff.mpr (by rwa [← zero_lt_iff, tsub_pos_iff_lt])
  rw [sq, tsub_mul, mul_tsub, mul_tsub, tsub_tsub_eq_add_tsub_of_le (by gcongr),
    tsub_add_eq_add_tsub (by gcongr), tsub_tsub, show x * y + y * x = 2 * x * y by ring,
    tsub_pos_iff_lt, ← sq, ← sq] at key
  rw [← sqrt_sq (_ / 2), sqrt_lt_sqrt, div_pow, lt_div_iff₀' (by positivity),
    show (2 : ℝ≥0) ^ 2 * (x * y) = 2 * x * y + 2 * x * y by ring, add_sq, add_right_comm]
  gcongr

open Function Filter Topology

/-- `agmSequences x y` is the sequence of (geometric, arithmetic) means
converging to the arithmetic-geometric mean starting from `x` and `y`. -/
/-
**NNReal.agmSequences** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：agmSequences (x y : Real>=0) : Nat -> Real>=0 × Real>=0
参数：x y : Real>=0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`agmSequences x y` is the sequence of (geometric, arithmetic) means
converging to the arithmetic-geometric mean starting from `x` and `y`.
-/
noncomputable def agmSequences (x y : ℝ≥0) : ℕ → ℝ≥0 × ℝ≥0 :=
  fun n ↦ (fun p ↦ (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)

variable {x y : ℝ≥0} {n : ℕ}

@[simp]
/-
**NNReal.agmSequences_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_zero : agmSequences x y 0 = (sqrt (x * y), (x + y) / 2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma agmSequences_zero : agmSequences x y 0 = (sqrt (x * y), (x + y) / 2) := rfl
/-
**NNReal.agmSequences_succ** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_succ : agmSequences x y (n + 1) = agmSequences (sqrt (x * y))
 ((x + y) / 2) n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma agmSequences_succ : agmSequences x y (n + 1) = agmSequences (sqrt (x * y)) ((x + y) / 2) n :=
  rfl
/-
**NNReal.agmSequences_succ'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_succ' : agmSequences x y (n + 1) = (sqrt ((agmSequences x y n
).1 * (agmSequences x y n).2), ((agmSequences x y n).1 + (agmSequences x y n).2)
 / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.agmSequences.eq_1`：∀ (x y : NNReal) (n : ℕ), x.agmSequences y n =
 (fun p => (NNReal.sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma agmSequences_succ' :
    agmSequences x y (n + 1) =
    (sqrt ((agmSequences x y n).1 * (agmSequences x y n).2),
      ((agmSequences x y n).1 + (agmSequences x y n).2) / 2) := by
  rw [agmSequences, agmSequences, iterate_succ', comp_apply]
/-
**NNReal.agmSequences_comm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_comm : agmSequences x y = agmSequences y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma agmSequences_comm : agmSequences x y = agmSequences y x := by
  funext n
  cases n with
  | zero => simp [mul_comm, add_comm]
  | succ n => simp [agmSequences_succ, mul_comm, add_comm]
/-
**NNReal.le_gm_and_am_le** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y) ∧ (x + y) / 2 <= y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.le_sqrt_iff_sq_le`：le_sqrt_iff_sq_le : x <= sqrt y ↔ x ^ 2 <= y
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NNReal.div_le_of_le_mul'`：div_le_of_le_mul' {a b c : Real>=0} (h : a <= 
b * c) : a / b <= c
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma le_gm_and_am_le (h : x ≤ y) : x ≤ sqrt (x * y) ∧ (x + y) / 2 ≤ y := by
  constructor
  · rw [le_sqrt_iff_sq_le, sq]
    gcongr
  · apply div_le_of_le_mul'
    rw [two_mul]
    gcongr
/-
**NNReal.dist_gm_am_le** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：dist_gm_am_le : dist (sqrt (x * y)) ((x + y) / 2) <= dist x y / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `NNReal.dist_eq`：NNReal.dist_eq (a b : Real>=0) : dist a b = |(a : Real) 
- b|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用引理 `NNReal.sqrt_mul_le_half_add`：sqrt_mul_le_half_add (x y : Real>=0) : sqrt
 (x * y) <= (x + y) / 2
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `NNReal.le_sqrt_iff_sq_le`：le_sqrt_iff_sq_le : x <= sqrt y ↔ x ^ 2 <= y
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_tsub_add_eq_tsub_left`：add_tsub_add_eq_tsub_left (a b c : α) : a + b
 - (a + c) = b - c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `tsub_div`：tsub_div (a b c : α) : (a - b) / c = a / c - b / c
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.coe_div`：∀ (r₁ r₂ : NNReal), ↑(r₁ / r₂) = ↑r₁ / ↑r₂
· 使用定理 `NNReal.coe_two`：↑2 = 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 36 条，此处仅展示前 30 条）
-/
lemma dist_gm_am_le : dist (sqrt (x * y)) ((x + y) / 2) ≤ dist x y / 2 := by
  wlog h : x ≤ y generalizing x y
  · simpa [add_comm, mul_comm, dist_comm] using this (not_le.mp h).le
  rw [dist_comm, dist_eq, ← NNReal.coe_sub (sqrt_mul_le_half_add ..), abs_eq]
  calc
    _ ≤ ((x + y) / 2 - x).toReal := by
      gcongr
      rw [le_sqrt_iff_sq_le, sq]
      gcongr
    _ = _ := by
      nth_rw 2 [← add_halves x]
      rw [add_div, add_tsub_add_eq_tsub_left, ← tsub_div, NNReal.coe_div, NNReal.coe_two, dist_comm,
        dist_eq, ← NNReal.coe_sub h, abs_eq]
/-
**NNReal.agmSequences_monotone_and_antitone** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_monotone_and_antitone : (Monotone fun n => (agmSequences x y 
n).1) ∧ Antitone fun n => (agmSequences x y n).2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.le_gm_and_am_le`：le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y)
 ∧ (x + y) / 2 <= y
· 使用引理 `NNReal.sqrt_mul_le_half_add`：sqrt_mul_le_half_add (x y : Real>=0) : sqrt
 (x * y) <= (x + y) / 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_le_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : L
E β] {a₁ a₂ : α} {b₁ b₂ : β},   (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma agmSequences_monotone_and_antitone :
    (Monotone fun n ↦ (agmSequences x y n).1) ∧ Antitone fun n ↦ (agmSequences x y n).2 := by
  suffices ∀ n, (agmSequences x y n).1 ≤ (agmSequences x y (n + 1)).1 ∧
      (agmSequences x y (n + 1)).2 ≤ (agmSequences x y n).2 from
    ⟨monotone_nat_of_le_succ (this · |>.1), antitone_nat_of_succ_le (this · |>.2)⟩
  intro n
  induction n generalizing x y with
  | zero => exact le_gm_and_am_le (sqrt_mul_le_half_add ..)
  | succ n ih => exact Prod.mk_le_mk.mp ih
/-
**NNReal.agmSequences_fst_monotone** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_fst_monotone : Monotone fun n => (agmSequences x y n).1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `NNReal.agmSequences_monotone_and_antitone`：agmSequences_monotone_and_ant
itone : (Monotone fun n => (agmSequences x y n).1) ∧ Antitone fun n => (agmSeque
nces x y n).2
-/
lemma agmSequences_fst_monotone : Monotone fun n ↦ (agmSequences x y n).1 :=
  agmSequences_monotone_and_antitone.1
/-
**NNReal.agmSequences_snd_antitone** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_snd_antitone : Antitone fun n => (agmSequences x y n).2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `NNReal.agmSequences_monotone_and_antitone`：agmSequences_monotone_and_ant
itone : (Monotone fun n => (agmSequences x y n).1) ∧ Antitone fun n => (agmSeque
nces x y n).2
-/
lemma agmSequences_snd_antitone : Antitone fun n ↦ (agmSequences x y n).2 :=
  agmSequences_monotone_and_antitone.2
/-
**NNReal.agmSequences_fst_le_snd** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_fst_le_snd (n m : Nat) : (agmSequences x y n).1 <= (agmSequen
ces x y m).2
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.sqrt_mul_le_half_add`：sqrt_mul_le_half_add (x y : Real>=0) : sqrt
 (x * y) <= (x + y) / 2
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `NNReal.agmSequences_fst_monotone`：agmSequences_fst_monotone : Monotone f
un n => (agmSequences x y n).1
· 使用引理 `NNReal.agmSequences_snd_antitone`：agmSequences_snd_antitone : Antitone f
un n => (agmSequences x y n).2
-/
lemma agmSequences_fst_le_snd (n m : ℕ) : (agmSequences x y n).1 ≤ (agmSequences x y m).2 := by
  suffices ∀ {k}, (agmSequences x y k).1 ≤ (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans this
    · exact this.trans (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_le_half_add ..
  | succ n ih => exact ih
/-
**NNReal.agmSequences_fst_lt_snd_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_fst_lt_snd_of_ne (h : x != y) (n m : Nat) : (agmSequences x y
 n).1 < (agmSequences x y m).2
参数：h : x != y；n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.sqrt_mul_lt_half_add_of_ne`：sqrt_mul_lt_half_add_of_ne {x y : Rea
l>=0} (h : x != y) : sqrt (x * y) < (x + y) / 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agmSequences_succ'`：agmSequences_succ' : agmSequences x y (n + 1)
 = (sqrt ((agmSequences x y n).1 * (agmSequences x y n).2), ((agmSequences x y n
).1 + (agmSeque…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `NNReal.agmSequences_fst_monotone`：agmSequences_fst_monotone : Monotone f
un n => (agmSequences x y n).1
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `NNReal.agmSequences_snd_antitone`：agmSequences_snd_antitone : Antitone f
un n => (agmSequences x y n).2
-/
lemma agmSequences_fst_lt_snd_of_ne (h : x ≠ y) (n m : ℕ) :
    (agmSequences x y n).1 < (agmSequences x y m).2 := by
  suffices ∀ {k}, (agmSequences x y k).1 < (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans_lt this
    · exact this.trans_le (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_lt_half_add_of_ne h
  | succ n ih =>
    rw [agmSequences_succ']
    exact sqrt_mul_lt_half_add_of_ne (ih h).ne
/-
**NNReal.agmSequences_min_max** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_min_max : agmSequences (min x y) (max x y) = agmSequences x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `NNReal.agmSequences_comm`：agmSequences_comm : agmSequences x y = agmSequ
ences y x
-/
lemma agmSequences_min_max : agmSequences (min x y) (max x y) = agmSequences x y := by
  obtain h | h := le_total x y
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, agmSequences_comm]
/-
**NNReal.dist_agmSequences_fst_snd** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：dist_agmSequences_fst_snd (n : Nat) : dist (agmSequences x y n).1 (agmSequ
ences x y n).2 <= dist x y / 2 ^ (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `NNReal.agmSequences_succ'`：agmSequences_succ' : agmSequences x y (n + 1)
 = (sqrt ((agmSequences x y n).1 * (agmSequences x y n).2), ((agmSequences x y n
).1 + (agmSeque…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `NNReal.dist_gm_am_le`：dist_gm_am_le : dist (sqrt (x * y)) ((x + y) / 2) 
<= dist x y / 2
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
lemma dist_agmSequences_fst_snd (n : ℕ) :
    dist (agmSequences x y n).1 (agmSequences x y n).2 ≤ dist x y / 2 ^ (n + 1) := by
  induction n with
  | zero => simp [dist_gm_am_le]
  | succ n ih =>
    rw [agmSequences_succ']
    apply dist_gm_am_le.trans
    rw [pow_succ, ← div_div]
    gcongr
/-
**NNReal.tendsto_dist_agmSequences_atTop_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`
。
形式化陈述：tendsto_dist_agmSequences_atTop_zero : Tendsto (fun n => dist (agmSequence
s x y n).1 (agmSequences x y n).2) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `NNReal.dist_agmSequences_fst_snd`：dist_agmSequences_fst_snd (n : Nat) : 
dist (agmSequences x y n).1 (agmSequences x y n).2 <= dist x y / 2 ^ (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 32 条，此处仅展示前 30 条）
-/
lemma tendsto_dist_agmSequences_atTop_zero :
    Tendsto (fun n ↦ dist (agmSequences x y n).1 (agmSequences x y n).2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ dist_nonneg) dist_agmSequences_fst_snd
  conv =>
    rw [← zero_mul (dist x y / 2)]
    enter [1, n]
    rw [pow_succ', ← div_div, div_eq_inv_mul, ← inv_pow]
  exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _

/-- The arithmetic-geometric mean of two `NNReal`s, defined as the infimum of arithmetic means. -/
/-
**NNReal.agm** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：agm (x y : Real>=0) : Real>=0
参数：x y : Real>=0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arithmetic-geometric mean of two `NNReal`s, defined as the infimum of arithm
etic means.
-/
noncomputable def agm (x y : ℝ≥0) : ℝ≥0 :=
  ⨅ n, (agmSequences x y n).2
/-
**NNReal.agm_comm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_comm : agm x y = agm y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agmSequences_comm`：agmSequences_comm : agmSequences x y = agmSequ
ences y x
-/
lemma agm_comm : agm x y = agm y x := by
  unfold agm
  conv_rhs =>
    enter [1, n]
    rw [agmSequences_comm]
/-
**NNReal.agm_eq_ciInf** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_eq_ciInf : agm x y = ⨅ n, (agmSequences x y n).2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma agm_eq_ciInf : agm x y = ⨅ n, (agmSequences x y n).2 := rfl
/-
**NNReal.tendsto_agmSequences_snd_agm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：tendsto_agmSequences_snd_agm : Tendsto (fun n => (agmSequences x y n).2) a
tTop (𝓝 (agm x y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_ciInf`：tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : B
ddBelow <| range f) : Tendsto f atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用引理 `NNReal.agmSequences_snd_antitone`：agmSequences_snd_antitone : Antitone f
un n => (agmSequences x y n).2
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
lemma tendsto_agmSequences_snd_agm : Tendsto (fun n ↦ (agmSequences x y n).2) atTop (𝓝 (agm x y)) :=
  tendsto_atTop_ciInf agmSequences_snd_antitone (OrderBot.bddBelow _)
/-
**NNReal.agm_le_agmSequences_snd** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_le_agmSequences_snd (n : Nat) : agm x y <= (agmSequences x y n).2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le'`：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i
-/
lemma agm_le_agmSequences_snd (n : ℕ) : agm x y ≤ (agmSequences x y n).2 := ciInf_le' _ n
/-
**NNReal.agm_le_max** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_le_max : agm x y <= max x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `NNReal.agm_le_agmSequences_snd`：agm_le_agmSequences_snd (n : Nat) : agm 
x y <= (agmSequences x y n).2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `NNReal.agmSequences_zero`：agmSequences_zero : agmSequences x y 0 = (sqrt
 (x * y), (x + y) / 2)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `NNReal.le_gm_and_am_le`：le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y)
 ∧ (x + y) / 2 <= y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `NNReal.agm_comm`：agm_comm : agm x y = agm y x
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma agm_le_max : agm x y ≤ max x y := by
  wlog h : x ≤ y generalizing x y
  · simpa [agm_comm, max_comm] using this (not_le.mp h).le
  rw [max_eq_right h]
  apply (agm_le_agmSequences_snd 0).trans
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).2
/-
**NNReal.bddAbove_range_agmSequences_fst** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：bddAbove_range_agmSequences_fst : BddAbove (Set.range fun n => (agmSequenc
es x y n).1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `NNReal.agmSequences_fst_le_snd`：agmSequences_fst_le_snd (n m : Nat) : (a
gmSequences x y n).1 <= (agmSequences x y m).2
-/
lemma bddAbove_range_agmSequences_fst : BddAbove (Set.range fun n ↦ (agmSequences x y n).1) := by
  rw [bddAbove_def]
  use (agmSequences x y 0).2
  simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ ↦ agmSequences_fst_le_snd ..

/-- The AGM is also the supremum of the geometric means. -/
/-
**NNReal.agm_eq_ciSup** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.congr_dist`：Filter.Tendsto.congr_dist {f₁ f₂ : ι -> α} {p
 : Filter ι} {a : α} (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x
) (f₂ x)) p (𝓝 …
· 使用引理 `NNReal.tendsto_agmSequences_snd_agm`：tendsto_agmSequences_snd_agm : Tend
sto (fun n => (agmSequences x y n).2) atTop (𝓝 (agm x y))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `NNReal.tendsto_dist_agmSequences_atTop_zero`：tendsto_dist_agmSequences_a
tTop_zero : Tendsto (fun n => dist (agmSequences x y n).1 (agmSequences x y n).2
) atTop (𝓝 0)
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用引理 `NNReal.agmSequences_fst_monotone`：agmSequences_fst_monotone : Monotone f
un n => (agmSequences x y n).1
· 使用引理 `NNReal.bddAbove_range_agmSequences_fst`：bddAbove_range_agmSequences_fst 
: BddAbove (Set.range fun n => (agmSequences x y n).1)

--- 原说明 ---
The AGM is also the supremum of the geometric means.
-/
lemma agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).1 := by
  refine tendsto_nhds_unique (tendsto_agmSequences_snd_agm.congr_dist ?_)
    (tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst)
  conv =>
    enter [1, n]
    rw [dist_comm]
  exact tendsto_dist_agmSequences_atTop_zero
/-
**NNReal.tendsto_agmSequences_fst_agm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：tendsto_agmSequences_fst_agm : Tendsto (fun n => (agmSequences x y n).1) a
tTop (𝓝 (agm x y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agm_eq_ciSup`：agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).
1
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用引理 `NNReal.agmSequences_fst_monotone`：agmSequences_fst_monotone : Monotone f
un n => (agmSequences x y n).1
· 使用引理 `NNReal.bddAbove_range_agmSequences_fst`：bddAbove_range_agmSequences_fst 
: BddAbove (Set.range fun n => (agmSequences x y n).1)
-/
lemma tendsto_agmSequences_fst_agm :
    Tendsto (fun n ↦ (agmSequences x y n).1) atTop (𝓝 (agm x y)) := by
  rw [agm_eq_ciSup]
  exact tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst
/-
**NNReal.agmSequences_fst_le_agm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agmSequences_fst_le_agm (n : Nat) : (agmSequences x y n).1 <= agm x y
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agm_eq_ciSup`：agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).
1
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用引理 `NNReal.bddAbove_range_agmSequences_fst`：bddAbove_range_agmSequences_fst 
: BddAbove (Set.range fun n => (agmSequences x y n).1)
-/
lemma agmSequences_fst_le_agm (n : ℕ) : (agmSequences x y n).1 ≤ agm x y := by
  rw [agm_eq_ciSup]
  exact le_ciSup bddAbove_range_agmSequences_fst _
/-
**NNReal.min_le_agm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：min_le_agm : min x y <= agm x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `NNReal.agmSequences_zero`：agmSequences_zero : agmSequences x y 0 = (sqrt
 (x * y), (x + y) / 2)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `NNReal.le_gm_and_am_le`：le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y)
 ∧ (x + y) / 2 <= y
· 使用引理 `NNReal.agmSequences_fst_le_agm`：agmSequences_fst_le_agm (n : Nat) : (agm
Sequences x y n).1 <= agm x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用引理 `NNReal.agm_comm`：agm_comm : agm x y = agm y x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma min_le_agm : min x y ≤ agm x y := by
  wlog h : x ≤ y generalizing x y
  · simpa [agm_comm, min_comm] using this (not_le.mp h).le
  rw [min_eq_left h]
  refine le_trans ?_ (agmSequences_fst_le_agm 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).1

@[simp]
/-
**NNReal.agm_self** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_self : agm x x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用引理 `NNReal.agm_le_max`：agm_le_max : agm x y <= max x y
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用引理 `NNReal.min_le_agm`：min_le_agm : min x y <= agm x y
-/
lemma agm_self : agm x x = x := by
  apply le_antisymm
  · nth_rw 3 [← max_self x]
    exact agm_le_max
  · nth_rw 1 [← min_self x]
    exact min_le_agm

@[simp]
/-
**NNReal.agm_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_zero_left : agm 0 y = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `NNReal.agmSequences_succ'`：agmSequences_succ' : agmSequences x y (n + 1)
 = (sqrt ((agmSequences x y n).1 * (agmSequences x y n).2), ((agmSequences x y n
).1 + (agmSeque…
· 使用引理 `NNReal.agm_eq_ciSup`：agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).
1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma agm_zero_left : agm 0 y = 0 := by
  suffices ∀ n, (agmSequences 0 y n).1 = 0 by simp [agm_eq_ciSup, this]
  intro n
  induction n with
  | zero => simp [agmSequences]
  | succ n ih =>
    rw [agmSequences_succ', ih, zero_mul, sqrt_zero]

@[simp]
/-
**NNReal.agm_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_zero_right : agm x 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agm_comm`：agm_comm : agm x y = agm y x
· 使用引理 `NNReal.agm_zero_left`：agm_zero_left : agm 0 y = 0
-/
lemma agm_zero_right : agm x 0 = 0 := by
  rw [agm_comm, agm_zero_left]
/-
**NNReal.agm_pos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_pos (hx : 0 < x) (hy : 0 < y) : 0 < agm x y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `NNReal.min_le_agm`：min_le_agm : min x y <= agm x y
-/
lemma agm_pos (hx : 0 < x) (hy : 0 < y) : 0 < agm x y := (lt_min hx hy).trans_le min_le_agm
/-
**NNReal.agm_eq_agm_agmSequences_fst_agmSequences_snd** 是 Mathlib 中的一个引理，位于命名空间 
`NNReal`。
形式化陈述：agm_eq_agm_agmSequences_fst_agmSequences_snd (n : Nat) : agm x y = agm (ag
mSequences x y n).1 (agmSequences x y n).2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `NNReal.tendsto_agmSequences_snd_agm`：tendsto_agmSequences_snd_agm : Tend
sto (fun n => (agmSequences x y n).2) atTop (𝓝 (agm x y))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
-/
lemma agm_eq_agm_agmSequences_fst_agmSequences_snd (n : ℕ) :
    agm x y = agm (agmSequences x y n).1 (agmSequences x y n).2 := by
  refine tendsto_nhds_unique ?_ tendsto_agmSequences_snd_agm
  have key := @tendsto_agmSequences_snd_agm x y
  rw [← tendsto_add_atTop_iff_nat (n + 1)] at key
  convert! key using 2 with m
  simp_rw [agmSequences, Prod.mk.eta, ← iterate_add_apply, add_right_comm]
/-
**NNReal.agm_eq_agm_gm_am** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_eq_agm_gm_am : agm x y = agm (sqrt (x * y)) ((x + y) / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.agm_eq_agm_agmSequences_fst_agmSequences_snd`：agm_eq_agm_agmSeque
nces_fst_agmSequences_snd (n : Nat) : agm x y = agm (agmSequences x y n).1 (agmS
equences x y n).2
-/
lemma agm_eq_agm_gm_am : agm x y = agm (sqrt (x * y)) ((x + y) / 2) := by
  simpa using agm_eq_agm_agmSequences_fst_agmSequences_snd 0
/-
**NNReal.agmSequences_fst_lt_agm_of_pos_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`
。
形式化陈述：agmSequences_fst_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x != 
y) (n : Nat) : (agmSequences x y n).1 < agm x y
参数：hx : 0 < x；hy : 0 < y；hn : x != y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agm_eq_agm_agmSequences_fst_agmSequences_snd`：agm_eq_agm_agmSeque
nces_fst_agmSequences_snd (n : Nat) : agm x y = agm (agmSequences x y n).1 (agmS
equences x y n).2
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `NNReal.sqrt_pos_of_pos`：∀ {x : NNReal}, 0 < x → 0 < NNReal.sqrt x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `NNReal.agmSequences_fst_monotone`：agmSequences_fst_monotone : Monotone f
un n => (agmSequences x y n).1
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `NNReal.agmSequences_fst_lt_snd_of_ne`：agmSequences_fst_lt_snd_of_ne (h :
 x != y) (n m : Nat) : (agmSequences x y n).1 < (agmSequences x y m).2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.mul_self_sqrt`：∀ (x : NNReal), NNReal.sqrt x * NNReal.sqrt x = x
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `OrderIso.lt_iff_lt._gcongr_1`：∀ {α : Type u_2} {β : Type u_3} [inst : Pr
eorder α] [inst_1 : Preorder β] (e : α ≃o β) {x y : α}, x < y → e x < e y
· 使用引理 `NNReal.agmSequences_fst_le_agm`：agmSequences_fst_le_agm (n : Nat) : (agm
Sequences x y n).1 <= agm x y
-/
lemma agmSequences_fst_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x ≠ y) (n : ℕ) :
    (agmSequences x y n).1 < agm x y := by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (?_ : p < sqrt (p * q)).trans_le (agmSequences_fst_le_agm 0)
  have ppos : 0 < p :=
    (show 0 < sqrt (x * y) by positivity).trans_le (agmSequences_fst_monotone zero_le)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 1 [← mul_self_sqrt p, sqrt_mul]
  gcongr
/-
**NNReal.agm_lt_agmSequences_snd_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_lt_agmSequences_snd_of_ne (hn : x != y) (n : Nat) : agm x y < (agmSequ
ences x y n).2
参数：hn : x != y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.agm_eq_agm_agmSequences_fst_agmSequences_snd`：agm_eq_agm_agmSeque
nces_fst_agmSequences_snd (n : Nat) : agm x y = agm (agmSequences x y n).1 (agmS
equences x y n).2
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `NNReal.agm_le_agmSequences_snd`：agm_le_agmSequences_snd (n : Nat) : agm 
x y <= (agmSequences x y n).2
· 使用引理 `NNReal.agmSequences_fst_lt_snd_of_ne`：agmSequences_fst_lt_snd_of_ne (h :
 x != y) (n m : Nat) : (agmSequences x y n).1 < (agmSequences x y m).2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
lemma agm_lt_agmSequences_snd_of_ne (hn : x ≠ y) (n : ℕ) : agm x y < (agmSequences x y n).2 := by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (agm_le_agmSequences_snd 0).trans_lt (?_ : (p + q) / 2 < q)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 2 [← add_halves q]
  rw [add_div]
  gcongr
/-
**NNReal.min_lt_agm_of_pos_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：min_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x != y) : min x y 
< agm x y
参数：hx : 0 < x；hy : 0 < y；hn : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `NNReal.agmSequences_zero`：agmSequences_zero : agmSequences x y 0 = (sqrt
 (x * y), (x + y) / 2)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `NNReal.le_gm_and_am_le`：le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y)
 ∧ (x + y) / 2 <= y
· 使用引理 `NNReal.agmSequences_fst_lt_agm_of_pos_of_ne`：agmSequences_fst_lt_agm_of_
pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x != y) (n : Nat) : (agmSequences x y 
n).1 < agm x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用引理 `NNReal.agm_comm`：agm_comm : agm x y = agm y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Ne.gt_or_lt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, a ≠ b → 
b < a ∨ a < b
-/
lemma min_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x ≠ y) : min x y < agm x y := by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, min_comm] using this hy hx hn.symm (hn.gt_or_lt.resolve_right h)
  rw [min_eq_left h.le]
  refine lt_of_le_of_lt ?_ (agmSequences_fst_lt_agm_of_pos_of_ne hx hy hn 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).1
/-
**NNReal.agm_lt_max_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_lt_max_of_ne (hn : x != y) : agm x y < max x y
参数：hn : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `NNReal.agm_lt_agmSequences_snd_of_ne`：agm_lt_agmSequences_snd_of_ne (hn 
: x != y) (n : Nat) : agm x y < (agmSequences x y n).2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `NNReal.agmSequences_zero`：agmSequences_zero : agmSequences x y 0 = (sqrt
 (x * y), (x + y) / 2)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `NNReal.le_gm_and_am_le`：le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y)
 ∧ (x + y) / 2 <= y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `NNReal.agm_comm`：agm_comm : agm x y = agm y x
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Ne.gt_or_lt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, a ≠ b → 
b < a ∨ a < b
-/
lemma agm_lt_max_of_ne (hn : x ≠ y) : agm x y < max x y := by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, max_comm] using this hn.symm (hn.gt_or_lt.resolve_right h)
  rw [max_eq_right h.le]
  apply (agm_lt_agmSequences_snd_of_ne hn 0).trans_le
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).2

/-- The AGM distributes over multiplication. -/
/-
**NNReal.agm_mul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：agm_mul_distrib {k : Real>=0} : agm (k * x) (k * y) = k * agm x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mul_iInf`：mul_iInf (f : ι -> Real>=0) (a : Real>=0) : a * iInf f 
= ⨅ i, a * f i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NNReal.agmSequences_succ`：agmSequences_succ : agmSequences x y (n + 1) =
 agmSequences (sqrt (x * y)) ((x + y) / 2) n
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y
· 使用定理 `NNReal.sqrt_sq`：∀ (x : NNReal), NNReal.sqrt (x ^ 2) = x

--- 原说明 ---
The AGM distributes over multiplication.
-/
lemma agm_mul_distrib {k : ℝ≥0} : agm (k * x) (k * y) = k * agm x y := by
  simp_rw [agm, mul_iInf]
  congr! with n
  induction n generalizing x y with
  | zero => simp [← mul_div_assoc, mul_add]
  | succ n ih =>
    rw [agmSequences_succ, ← mul_add, mul_div_assoc, mul_mul_mul_comm,
      ← sq, sqrt_mul, sqrt_sq, ih, agmSequences_succ]

end NNReal

