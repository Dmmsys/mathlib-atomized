/-
Copyright (c) 2021 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
public import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Corollaries From Approximation Lemmas (`Algebra.ContinuedFractions.Computation.Approximations`)

## Summary

Using the equivalence of the convergents computations
(`GenContFract.convs` and `GenContFract.convs'`) for
continued fractions (see `Algebra.ContinuedFractions.ConvergentsEquiv`), it follows that the
convergents computations for `GenContFract.of` are equivalent.

Moreover, we show the convergence of the continued fractions computations, that is
`(GenContFract.of v).convs` indeed computes `v` in the limit.

## Main Definitions

- `ContFract.of` returns the (regular) continued fraction of a value.

## Main Theorems

- `GenContFract.of_convs_eq_convs'` shows that the convergents computations for
  `GenContFract.of` are equivalent.
- `GenContFract.of_convergence` shows that `(GenContFract.of v).convs` converges to `v`.

## Tags

convergence, fractions
-/

public section

variable {K : Type*} (v : K) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

open GenContFract (of)
open scoped Topology

namespace GenContFract

/-
**GenContFract.of_convs_eq_convs'** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_convs_eq_convs' : (of v).convs = (of v).convs'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContFract.convs_eq_convs'`：convs_eq_convs' [Field K] [LinearOrder K] [Is
StrictOrderedRing K] {c : ContFract K} : (↑c : GenContFract K).convs = (↑c : Gen
ContFract K).co…
-/
theorem of_convs_eq_convs' : (of v).convs = (of v).convs' :=
  ContFract.convs_eq_convs' (c := ContFract.of v)

/-- The recurrence relation for the convergents of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
/-
**GenContFract.convs_succ** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：convs_succ (n : Nat) : (of v).convs (n + 1) = ⌊v⌋ + 1 / (of (Int.fract v)⁻
¹).convs n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.of_convs_eq_convs'`：of_convs_eq_convs' : (of v).convs = (of
 v).convs'
· 使用定理 `GenContFract.convs'_succ`：∀ {K : Type u_1} [inst : DivisionRing K] [inst
_1 : LinearOrder K] [inst_2 : FloorRing K] (v : K) (n : ℕ)   [IsStrictOrderedRin
g K], (GenCont…

--- 原说明 ---
The recurrence relation for the convergents of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fract
ional part.
-/
theorem convs_succ (n : ℕ) :
    (of v).convs (n + 1) = ⌊v⌋ + 1 / (of (Int.fract v)⁻¹).convs n := by
  rw [of_convs_eq_convs', convs'_succ, of_convs_eq_convs']

section Convergence

/-!
### Convergence

We next show that `(GenContFract.of v).convs n` converges to `v`.
-/


variable [Archimedean K]

open Nat

/-
**GenContFract.of_convergence_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_convergence_epsilon : forall ε > (0 : K), exists N : Nat, forall n >= N
, |v - (of v).convs n| < ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `GenContFract.of_correctness_of_terminatedAt`：of_correctness_of_terminate
dAt (terminatedAt_n : (of v).TerminatedAt n) : v = (of v).convs n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `GenContFract.abs_sub_convs_le`：abs_sub_convs_le (not_terminatedAt_n : ¬(
of v).TerminatedAt n) : |v - (of v).convs n| <= 1 / ((of v).dens n * ((of v).den
s <| n + 1))
· 使用定理 `GenContFract.succ_nth_fib_le_of_nth_den`：succ_nth_fib_le_of_nth_den (hyp
 : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) : (fib (n + 1) : K) <= (of v).dens n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `GenContFract.terminated_stable`：terminated_stable (n_le_m : n <= m) (ter
minatedAt_n : g.TerminatedAt n) : g.TerminatedAt m
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.fib_pos`：∀ {n : ℕ}, 0 < Nat.fib n ↔ 0 < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 52 条，此处仅展示前 30 条）
-/
theorem of_convergence_epsilon :
    ∀ ε > (0 : K), ∃ N : ℕ, ∀ n ≥ N, |v - (of v).convs n| < ε := by
  intro ε ε_pos
  -- use the archimedean property to obtain a suitable N
  rcases (exists_nat_gt (1 / ε) : ∃ N' : ℕ, 1 / ε < N') with ⟨N', one_div_ε_lt_N'⟩
  let N := max N' 5
  -- set minimum to 5 to have N ≤ fib N work
  exists N
  intro n n_ge_N
  let g := of v
  rcases Decidable.em (g.TerminatedAt n) with terminatedAt_n | not_terminatedAt_n
  · have : v = g.convs n := of_correctness_of_terminatedAt terminatedAt_n
    have : v - g.convs n = 0 := sub_eq_zero.mpr this
    rw [this]
    exact mod_cast ε_pos
  · let B := g.dens n
    let nB := g.dens (n + 1)
    have abs_v_sub_conv_le : |v - g.convs n| ≤ 1 / (B * nB) :=
      abs_sub_convs_le not_terminatedAt_n
    suffices 1 / (B * nB) < ε from lt_of_le_of_lt abs_v_sub_conv_le this
    -- show that `0 < (B * nB)` and then multiply by `B * nB` to get rid of the division
    have nB_ineq : (fib (n + 2) : K) ≤ nB :=
      succ_nth_fib_le_of_nth_den (Or.inr not_terminatedAt_n)
    have B_ineq : (fib (n + 1) : K) ≤ B :=
      haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminatedAt_n
      succ_nth_fib_le_of_nth_den (Or.inr this)
    have zero_lt_B : 0 < B := B_ineq.trans_lt' <| mod_cast fib_pos.2 n.succ_pos
    have nB_pos : 0 < nB := nB_ineq.trans_lt' <| mod_cast fib_pos.2 <| succ_pos _
    have zero_lt_mul_conts : 0 < B * nB := by positivity
    suffices 1 < ε * (B * nB) from (div_lt_iff₀ zero_lt_mul_conts).mpr this
    -- use that `N' ≥ n` was obtained from the archimedean property to show the following
    calc 1 < ε * (N' : K) := (div_lt_iff₀' ε_pos).mp one_div_ε_lt_N'
      _ ≤ ε * (B * nB) := ?_
    -- cancel `ε`
    gcongr
    calc
      (N' : K) ≤ (N : K) := mod_cast le_max_left _ _
      _ ≤ n := mod_cast n_ge_N
      _ ≤ fib n := mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
      _ ≤ fib (n + 1) := mod_cast fib_le_fib_succ
      _ ≤ fib (n + 1) * fib (n + 1) := mod_cast (fib (n + 1)).le_mul_self
      _ ≤ fib (n + 1) * fib (n + 2) := by gcongr; lia
      _ ≤ B * nB := by gcongr

set_option backward.isDefEq.respectTransparency false in
/-
**GenContFract.of_convergence** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_convergence [TopologicalSpace K] [OrderTopology K] : Filter.Tendsto (of
 v).convs Filter.atTop 𝓝 v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `GenContFract.of_convergence_epsilon`：of_convergence_epsilon : forall ε >
 (0 : K), exists N : Nat, forall n >= N, |v - (of v).convs n| < ε
-/
theorem of_convergence [TopologicalSpace K] [OrderTopology K] :
    Filter.Tendsto (of v).convs Filter.atTop <| 𝓝 v := by
  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v

end Convergence

end GenContFract

