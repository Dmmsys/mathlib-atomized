/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Partition.Equipartition

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.stepBound`: During the inductive step, a partition of size `n` is blown to
  size at most `stepBound n`.
* `SzemerediRegularity.initialBound`: The size of the partition we start the induction with.
* `SzemerediRegularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset Fintype Function Real

namespace SzemerediRegularity

/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `stepBound n`. -/
/-
**SzemerediRegularity.stepBound** 是 Mathlib 中的一个定义，位于命名空间 `SzemerediRegularity`。
形式化陈述：stepBound (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of s
ize `n` during
the induction results in a partition of size at most `stepBound n`.
-/
def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n
/-
**SzemerediRegularity.le_stepBound** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularit
y`。
形式化陈述：le_stepBound : id <= stepBound
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem le_stepBound : id ≤ stepBound := fun n =>
  Nat.le_mul_of_pos_right _ <| pow_pos (by simp) n
/-
**SzemerediRegularity.stepBound_mono** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegular
ity`。
形式化陈述：stepBound_mono : Monotone stepBound
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem stepBound_mono : Monotone stepBound := fun _ _ h => by unfold stepBound; gcongr; decide
/-
**SzemerediRegularity.stepBound_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegu
larity`。
形式化陈述：stepBound_pos_iff {n : Nat} : 0 < stepBound n ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos_iff_of_pos_right`：mul_pos_iff_of_pos_right [MulPosStrictMono α] 
[MulPosReflectLT α] (h : 0 < b) : 0 < a * b ↔ 0 < a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
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
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem stepBound_pos_iff {n : ℕ} : 0 < stepBound n ↔ 0 < n :=
  mul_pos_iff_of_pos_right <| by positivity

alias ⟨_, stepBound_pos⟩ := stepBound_pos_iff
/-
**SzemerediRegularity.coe_stepBound** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegulari
ty`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] (n : ℕ), ↑(SzemerediRegularity.stepBo
und n) = ↑n * 4 ^ n
参数：n : ℕ；SzemerediRegularity.stepBound n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[norm_cast] lemma coe_stepBound {α : Type*} [Semiring α] (n : ℕ) :
    (stepBound n : α) = n * 4 ^ n := by unfold stepBound; norm_cast

end SzemerediRegularity

open SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] {P : Finpartition (univ : Finset α)}
  {u : Finset α} {ε : ℝ}

local notation3 "m" => (card α / stepBound #P.parts : ℕ)

local notation3 "a" => (card α / #P.parts - m * 4 ^ #P.parts : ℕ)

namespace SzemerediRegularity.Positivity

set_option backward.privateInPublic true in
/-
**SzemerediRegularity.Positivity.eps_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediReg
ularity.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eps_pos {ε : ℝ} {n : ℕ} (h : 100 ≤ (4 : ℝ) ^ n * ε ^ 5) : 0 < ε :=
  (Odd.pow_pos_iff (by decide)).mp
    (pos_of_mul_pos_right ((show 0 < (100 : ℝ) by simp).trans_le h) (by positivity))

set_option backward.privateInPublic true in
/-
**SzemerediRegularity.Positivity.m_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegul
arity.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α) : 0 < m :=
  Nat.div_pos (hPα.trans' <| by unfold stepBound; gcongr; simp) <|
    stepBound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos

/-- Local extension for the `positivity` tactic: A few facts that are needed many times for the
proof of Szemerédi's regularity lemma. -/
scoped macro "sz_positivity" : tactic =>
  `(tactic|
      { try have := m_pos ‹_›
        try have := eps_pos ‹_›
        positivity })

-- Original meta code
/- meta def positivity_szemeredi_regularity : expr → tactic strictness
| `(%%n / step_bound (finpartition.parts %%P).card) := do
    p ← to_expr
      ``((finpartition.parts %%P).card * 16^(finpartition.parts %%P).card ≤ %%n)
      >>= find_assumption,
    positive <$> mk_app ``m_pos [p]
| ε := do
    typ ← infer_type ε,
    unify typ `(ℝ),
    p ← to_expr ``(100 ≤ 4 ^ _ * %%ε ^ 5) >>= find_assumption,
    positive <$> mk_app ``eps_pos [p] -/

end SzemerediRegularity.Positivity

namespace SzemerediRegularity

open scoped SzemerediRegularity.Positivity

/-
**SzemerediRegularity.m_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularity`。
形式化陈述：m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) : 0 < m
参数：hPα : #P.parts * 16 ^ #P.parts <= card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Regularity.Bound.0.SzemerediR
egularity.Positivity.m_pos`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fi
ntype α] {P : Finpartition Finset.univ} [Nonempty α],   P.parts.card * 16 ^ P.pa
rts.card…
-/
theorem m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α) : 0 < m := by
  sz_positivity
/-
**SzemerediRegularity.coe_m_add_one_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegu
larity`。
形式化陈述：coe_m_add_one_pos : 0 < (m : Real) + 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem coe_m_add_one_pos : 0 < (m : ℝ) + 1 := by positivity
/-
**SzemerediRegularity.one_le_m_coe** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularit
y`。
形式化陈述：one_le_m_coe [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) : (1 
: Real) <= m
参数：hPα : #P.parts * 16 ^ #P.parts <= card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SzemerediRegularity.m_pos`：m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.
parts <= card α) : 0 < m
-/
theorem one_le_m_coe [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α) : (1 : ℝ) ≤ m :=
  Nat.one_le_cast.2 <| m_pos hPα
/-
**SzemerediRegularity.eps_pow_five_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegul
arity`。
形式化陈述：eps_pow_five_pos (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5) : ↑0 < ε ^ 5
参数：hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pos_of_mul_pos_right`：pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < 
a * b) (ha : 0 <= a) : 0 < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem eps_pow_five_pos (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) : ↑0 < ε ^ 5 :=
  pos_of_mul_pos_right ((by simp : (0 : ℝ) < 100).trans_le hPε) <| by positivity
/-
**SzemerediRegularity.eps_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularity`。
形式化陈述：eps_pos (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5) : 0 < ε
参数：hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Odd.pow_pos_iff`：Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `SzemerediRegularity.eps_pow_five_pos`：eps_pow_five_pos (hPε : 100 <= (4 
: Real) ^ #P.parts * ε ^ 5) : ↑0 < ε ^ 5
-/
theorem eps_pos (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) : 0 < ε :=
  (Odd.pow_pos_iff (by decide)).mp (eps_pow_five_pos hPε)
/-
**SzemerediRegularity.hundred_div_** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularit
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hundred_div_ε_pow_five_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) : 100 / ε ^ 5 ≤ m :=
  (div_le_of_le_mul₀ (eps_pow_five_pos hPε).le (by positivity) hPε).trans <| by
    norm_cast
    rwa [Nat.le_div_iff_mul_le (stepBound_pos (P.parts_nonempty <|
      univ_nonempty.ne_empty).card_pos), stepBound, mul_left_comm, ← mul_pow]
/-
**SzemerediRegularity.hundred_le_m** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularit
y`。
形式化陈述：hundred_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPε 
: 100 <= (4 : Real) ^ #P.parts * ε ^ 5) (hε : ε <= 1) : 100 <= m
参数：hPα : #P.parts * 16 ^ #P.parts <= card α；hPε : 100 <= (4 : Real) ^ #P.parts *
 ε ^ 5；hε : ε <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `SzemerediRegularity.hundred_div_ε_pow_five_le_m`：hundred_div_ε_pow_five_
le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPε : 100 <= (4 : 
Real) ^ #P.parts * ε ^ 5) : 100 / ε ^…
· 使用定理 `le_div_self`：le_div_self (ha : 0 <= a) (hb₀ : 0 < b) (hb₁ : b <= 1) : a 
<= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Regularity.Bound.0.SzemerediR
egularity.Positivity.m_pos`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fi
ntype α] {P : Finpartition Finset.univ} [Nonempty α],   P.parts.card * 16 ^ P.pa
rts.card…
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Regularity.Bound.0.SzemerediR
egularity.Positivity.eps_pos`：∀ {ε : ℝ} {n : ℕ}, 100 ≤ 4 ^ n * ε ^ 5 → 0 < ε
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem hundred_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : 100 ≤ (4 : ℝ) ^ #P.parts * ε ^ 5) (hε : ε ≤ 1) : 100 ≤ m :=
  mod_cast
    (hundred_div_ε_pow_five_le_m hPα hPε).trans'
      (le_div_self (by simp) (by sz_positivity) <| pow_le_one₀ (by sz_positivity) hε)
/-
**SzemerediRegularity.a_add_one_le_four_pow_parts_card** 是 Mathlib 中的一个定理，位于命名空间
 `SzemerediRegularity`。
形式化陈述：a_add_one_le_four_pow_parts_card : a + 1 <= 4 ^ #P.parts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SzemerediRegularity.stepBound.eq_1`：∀ (n : ℕ), SzemerediRegularity.stepB
ound n = n * 4 ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Nat.lt_div_mul_add`：∀ {a b : ℕ}, 0 < b → a < a / b * b + b
-/
theorem a_add_one_le_four_pow_parts_card : a + 1 ≤ 4 ^ #P.parts := by
  have h : 1 ≤ 4 ^ #P.parts := one_le_pow₀ (by simp)
  rw [stepBound, ← Nat.div_div_eq_div_mul]
  conv_rhs => rw [← Nat.sub_add_cancel h]
  rw [add_le_add_iff_right, tsub_le_iff_left, ← Nat.add_sub_assoc h]
  exact Nat.le_sub_one_of_lt (Nat.lt_div_mul_add h)
/-
**SzemerediRegularity.card_aux** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_aux₁ (hucard : #u = m * 4 ^ #P.parts + a) :
    (4 ^ #P.parts - a) * m + a * (m + 1) = #u := by
  rw [hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]
/-
**SzemerediRegularity.card_aux** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_aux₂ (hP : P.IsEquipartition) (hu : u ∈ P.parts) (hucard : #u ≠ m * 4 ^ #P.parts + a) :
    (4 ^ #P.parts - (a + 1)) * m + (a + 1) * (m + 1) = #u := by
  have : m * 4 ^ #P.parts ≤ card α / #P.parts := by
    rw [stepBound, ← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  rw [Nat.add_sub_of_le this] at hucard
  rw [(hP.card_parts_eq_average hu).resolve_left hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel a_add_one_le_four_pow_parts_card, ← add_assoc, mul_comm,
    Nat.add_sub_of_le this, card_univ]
/-
**SzemerediRegularity.pow_mul_m_le_card_part** 是 Mathlib 中的一个定理，位于命名空间 `Szemered
iRegularity`。
形式化陈述：pow_mul_m_le_card_part (hP : P.IsEquipartition) (hu : u in P.parts) : (4 :
 Real) ^ #P.parts * m <= #u
参数：hP : P.IsEquipartition；hu : u in P.parts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SzemerediRegularity.stepBound.eq_1`：∀ (n : ℕ), SzemerediRegularity.stepB
ound n = n * 4 ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.mul_div_le`：∀ (m n : ℕ), n * (m / n) ≤ m
· 使用定理 `Finpartition.IsEquipartition.average_le_card_part`：∀ {α : Type u_1} [ins
t : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipartition → 
t ∈ P.parts → s.card / P.parts.card ≤ t…
-/
theorem pow_mul_m_le_card_part (hP : P.IsEquipartition) (hu : u ∈ P.parts) :
    (4 : ℝ) ^ #P.parts * m ≤ #u := by
  norm_cast
  rw [stepBound, ← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)

variable (P ε) (l : ℕ)

/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
/-
**SzemerediRegularity.initialBound** 是 Mathlib 中的一个定义，位于命名空间 `SzemerediRegularit
y`。
形式化陈述：initialBound : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for Szemerédi's regularity lemma. The size of the partition b
y which we start
blowing.
-/
noncomputable def initialBound : ℕ :=
  max 7 <| max l <| ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1
/-
**SzemerediRegularity.le_initialBound** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegula
rity`。
形式化陈述：le_initialBound : l <= initialBound ε l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem le_initialBound : l ≤ initialBound ε l :=
  (le_max_left _ _).trans <| le_max_right _ _
/-
**SzemerediRegularity.seven_le_initialBound** 是 Mathlib 中的一个定理，位于命名空间 `Szemeredi
Regularity`。
形式化陈述：seven_le_initialBound : 7 <= initialBound ε l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem seven_le_initialBound : 7 ≤ initialBound ε l :=
  le_max_left _ _
/-
**SzemerediRegularity.initialBound_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegul
arity`。
形式化陈述：initialBound_pos : 0 < initialBound ε l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Nat.succ_pos'`：succ_pos' : 0 < succ n
· 使用定理 `SzemerediRegularity.seven_le_initialBound`：seven_le_initialBound : 7 <= 
initialBound ε l
-/
theorem initialBound_pos : 0 < initialBound ε l :=
  Nat.succ_pos'.trans_le <| seven_le_initialBound _ _
/-
**SzemerediRegularity.hundred_lt_pow_initialBound_mul** 是 Mathlib 中的一个定理，位于命名空间 
`SzemerediRegularity`。
形式化陈述：hundred_lt_pow_initialBound_mul {ε : Real} (hε : 0 < ε) (l : Nat) : 100 < 
↑4 ^ initialBound ε l * ε ^ 5
参数：hε : 0 < ε；l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.lt_rpow_iff_log_lt`：lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : 
x < y ^ z ↔ log x < z * log y
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_lt_four`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `SzemerediRegularity.initialBound.eq_1`：∀ (ε : ℝ) (l : ℕ), SzemerediRegul
arity.initialBound ε l = max 7 (max l (⌊Real.log (100 / ε ^ 5) / Real.log 4⌋₊ + 
1))
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
-/
theorem hundred_lt_pow_initialBound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    100 < ↑4 ^ initialBound ε l * ε ^ 5 := by
  rw [← rpow_natCast 4, ← div_lt_iff₀ (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four, ←
    div_lt_iff₀, initialBound, Nat.cast_max, Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by simp)
  · exact div_pos (by simp) (pow_pos hε 5)

/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
/-
**SzemerediRegularity.bound** 是 Mathlib 中的一个定义，位于命名空间 `SzemerediRegularity`。
形式化陈述：bound : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An explicit bound on the size of the equipartition whose existence is given by S
zemerédi's
regularity lemma.
-/
noncomputable def bound : ℕ :=
  (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)
/-
**SzemerediRegularity.initialBound_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `Szemeredi
Regularity`。
形式化陈述：initialBound_le_bound : initialBound ε l <= bound ε l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.id_le_iterate_of_id_le`：id_le_iterate_of_id_le (h : id <= f) (n
 : Nat) : id <= f^[n]
· 使用定理 `SzemerediRegularity.le_stepBound`：le_stepBound : id <= stepBound
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
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
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
theorem initialBound_le_bound : initialBound ε l ≤ bound ε l :=
  (id_le_iterate_of_id_le le_stepBound _ _).trans <| Nat.le_mul_of_pos_right _ <| by positivity
/-
**SzemerediRegularity.le_bound** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularity`。
形式化陈述：le_bound : l <= bound ε l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SzemerediRegularity.le_initialBound`：le_initialBound : l <= initialBound
 ε l
· 使用定理 `SzemerediRegularity.initialBound_le_bound`：initialBound_le_bound : initi
alBound ε l <= bound ε l
-/
theorem le_bound : l ≤ bound ε l :=
  (le_initialBound ε l).trans <| initialBound_le_bound ε l
/-
**SzemerediRegularity.bound_pos** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegularity`。
形式化陈述：bound_pos : 0 < bound ε l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `SzemerediRegularity.initialBound_pos`：initialBound_pos : 0 < initialBoun
d ε l
· 使用定理 `SzemerediRegularity.initialBound_le_bound`：initialBound_le_bound : initi
alBound ε l <= bound ε l
-/
theorem bound_pos : 0 < bound ε l :=
  (initialBound_pos ε l).trans_le <| initialBound_le_bound ε l

variable {ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s t : Finset ι} {x : 𝕜}
/-
**SzemerediRegularity.mul_sq_le_sum_sq** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegul
arity`。
形式化陈述：mul_sq_le_sum_sq (hst : s subseteq t) (f : ι -> 𝕜) (hs : x ^ 2 <= ((∑ i in
 s, f i) / #s) ^ 2) (hs' : (#s : 𝕜) != 0) : (#s : 𝕜) * x ^ 2 <= ∑ i in t, f i ^ 
2
参数：hst : s subseteq t；f : ι -> 𝕜；hs : x ^ 2 <= ((∑ i in s, f i) / #s) ^ 2；hs' : 
(#s : 𝕜) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sum_div_card_sq_le_sum_sq_div_card`：sum_div_card_sq_le_sum_sq_div_card :
 ((∑ i in s, f i) / #s) ^ 2 <= (∑ i in s, f i ^ 2) / #s
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
theorem mul_sq_le_sum_sq (hst : s ⊆ t) (f : ι → 𝕜) (hs : x ^ 2 ≤ ((∑ i ∈ s, f i) / #s) ^ 2)
    (hs' : (#s : 𝕜) ≠ 0) : (#s : 𝕜) * x ^ 2 ≤ ∑ i ∈ t, f i ^ 2 := calc
  _ ≤ (#s : 𝕜) * ((∑ i ∈ s, f i ^ 2) / #s) := by
    gcongr
    exact hs.trans sum_div_card_sq_le_sum_sq_div_card
  _ = ∑ i ∈ s, f i ^ 2 := mul_div_cancel₀ _ hs'
  _ ≤ ∑ i ∈ t, f i ^ 2 := by gcongr
/-
**SzemerediRegularity.add_div_le_sum_sq_div_card** 是 Mathlib 中的一个定理，位于命名空间 `Szem
erediRegularity`。
形式化陈述：add_div_le_sum_sq_div_card (hst : s subseteq t) (f : ι -> 𝕜) (d : 𝕜) (hx :
 0 <= x) (hs : x <= |(∑ i in s, f i) / #s - (∑ i in t, f i) / #t|) (ht : d <= ((
∑ i in t, f i) / #t) ^ 2) : d + #s / #t * x ^ 2 <= (∑ i in t, f i ^ 2) / #t
参数：hst : s subseteq t；f : ι -> 𝕜；d : 𝕜；hx : 0 <= x；hs : x <= |(∑ i in s, f i) / 
#s - (∑ i in t, f i) / #t|；ht : d <= ((∑ i in t, f i) / #t) ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sum_div_card_sq_le_sum_sq_div_card`：sum_div_card_sq_le_sum_sq_div_card :
 ((∑ i in s, f i) / #s) ^ 2 <= (∑ i in s, f i ^ 2) / #s
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 100 条，此处仅展示前 30 条）
-/
theorem add_div_le_sum_sq_div_card (hst : s ⊆ t) (f : ι → 𝕜) (d : 𝕜) (hx : 0 ≤ x)
    (hs : x ≤ |(∑ i ∈ s, f i) / #s - (∑ i ∈ t, f i) / #t|) (ht : d ≤ ((∑ i ∈ t, f i) / #t) ^ 2) :
    d + #s / #t * x ^ 2 ≤ (∑ i ∈ t, f i ^ 2) / #t := by
  obtain hscard | hscard := ((#s).cast_nonneg : (0 : 𝕜) ≤ #s).eq_or_lt
  · simpa [← hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card
  have htcard : (0 : 𝕜) < #t := hscard.trans_le (Nat.cast_le.2 (card_le_card hst))
  have h₁ : x ^ 2 ≤ ((∑ i ∈ s, f i) / #s - (∑ i ∈ t, f i) / #t) ^ 2 :=
    sq_le_sq.2 (by rwa [abs_of_nonneg hx])
  have h₂ : x ^ 2 ≤ ((∑ i ∈ s, (f i - (∑ j ∈ t, f j) / #t)) / #s) ^ 2 := by
    apply h₁.trans
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hscard.ne']
  grw [ht]
  rw [← mul_div_right_comm, le_div_iff₀ htcard, add_mul, div_mul_cancel₀ _ htcard.ne']
  have h₃ := mul_sq_le_sum_sq hst (fun i => (f i - (∑ j ∈ t, f j) / #t)) h₂ hscard.ne'
  grw [h₃]
  simp only [sub_div' htcard.ne', div_pow, ← sum_div, ← mul_div_right_comm _ (#t : 𝕜), ← add_div,
    div_le_iff₀ (sq_pos_of_ne_zero htcard.ne'), sub_sq, sum_add_distrib, sum_const,
    sum_sub_distrib, mul_pow, ← sum_mul, nsmul_eq_mul, two_mul]
  ring_nf
  rfl

end SzemerediRegularity

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `SzemerediRegularity.initialBound` is always positive. -/
@[positivity SzemerediRegularity.initialBound _ _]
meta def evalInitialBound : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(SzemerediRegularity.initialBound $ε $l) =>
    assertInstancesCommute
    pure (.positive q(SzemerediRegularity.initialBound_pos $ε $l))
  | _, _, _ => throwError "not initialBound"


/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.initialBound ε l := by positivity

/-- Extension for the `positivity` tactic: `SzemerediRegularity.bound` is always positive. -/
@[positivity SzemerediRegularity.bound _ _]
meta def evalBound : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(SzemerediRegularity.bound $ε $l) =>
    assertInstancesCommute
    pure (.positive q(SzemerediRegularity.bound_pos $ε $l))
  | _, _, _ => throwError "not bound"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.bound ε l := by positivity

end Mathlib.Meta.Positivity

