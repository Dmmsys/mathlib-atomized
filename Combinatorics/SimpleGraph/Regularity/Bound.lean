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

/--
Definition of `stepBound` / `stepBound` 的定义

English:
definition stepBound
  signature: (n : Nat)
  body: n * 4 ^ n

中文:
定义 stepBound
  签名: (n : 自然数)
  定义体: n * 4 ^ n
-/
def stepBound (n : Nat) : Nat :=
  n * 4 ^ n

/--
theorem `le_stepBound` / 定理 `le_stepBound`

English:
theorem le_stepBound
  statement: id <= stepBound
  proof: fun n =>
Nat.le_mul_of_pos_right _ pow_pos (by simp) n

中文:
定理 le_stepBound
  结论: id <= stepBound
  证明: fun n =>
Nat.le_mul_of_pos_right _ pow_pos (by simp) n
-/
theorem le_stepBound : id <= stepBound := fun n =>
Nat.le_mul_of_pos_right _ pow_pos (by simp) n

/--
theorem `stepBound_mono` / 定理 `stepBound_mono`

English:
theorem stepBound_mono
  statement: Monotone stepBound
  proof: fun _ _ h => by unfold stepBound; gcongr; decide

中文:
定理 stepBound_mono
  结论: Monotone stepBound
  证明: fun _ _ h => by unfold stepBound; gcongr; decide

Depends on / 依赖: stepBound
-/
theorem stepBound_mono : Monotone stepBound := fun _ _ h => by unfold stepBound; gcongr; decide

/--
theorem `stepBound_pos_iff` / 定理 `stepBound_pos_iff`

English:
theorem stepBound_pos_iff
  given: {n : Nat}
  statement: 0 < stepBound n ↔ 0 < n
  proof: mul_pos_iff_of_pos_right by positivity

alias ⟨_, stepBound_pos⟩ := stepBound_pos_iff

中文:
定理 stepBound_pos_iff
  条件: {n : 自然数}
  结论: 0 < stepBound n ↔ 0 < n
  证明: mul_pos_iff_of_pos_right by positivity

alias ⟨_, stepBound_pos⟩ := stepBound_pos_iff

Depends on / 依赖: mul_pos_iff_of_pos_right
-/
theorem stepBound_pos_iff {n : Nat} : 0 < stepBound n ↔ 0 < n :=
mul_pos_iff_of_pos_right by positivity

alias ⟨_, stepBound_pos⟩ := stepBound_pos_iff

/--
lemma `coe_stepBound` / 引理 `coe_stepBound`

English:
lemma coe_stepBound
  given: {α : Type*} [Semiring α] (n : Nat)
  proof: by unfold stepBound; norm_cast

中文:
引理 coe_stepBound
  条件: {α : 类型} [Semiring α] (n : 自然数)
  证明: by unfold stepBound; norm_cast
-/
@[norm_cast] lemma coe_stepBound {α : Type*} [Semiring α] (n : Nat) :
    (stepBound n : α) = n * 4 ^ n := by unfold stepBound; norm_cast

end SzemerediRegularity

open SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] {P : Finpartition (univ : Finset α)}
  {u : Finset α} {ε : Real}

local notation3 "m" => (card α / stepBound #P.parts : Nat)

local notation3 "a" => (card α / #P.parts - m * 4 ^ #P.parts : Nat)

namespace SzemerediRegularity.Positivity

set_option backward.privateInPublic true in
/--
theorem `eps_pos` / 定理 `eps_pos`

English:
theorem eps_pos
  given: {ε : Real} {n : Nat} (h : 100 <= (4 : Real) ^ n * ε ^ 5)
  statement: 0 < ε
  proof: (Odd.pow_pos_iff (by decide)).mp
    (pos_of_mul_pos_right ((show 0 < (100 : Real) by simp).trans_le h) (by positivity))

中文:
定理 eps_pos
  条件: {ε : 实数} {n : 自然数} (h : 100 <= (4 : 实数) ^ n * ε ^ 5)
  结论: 0 < ε
  证明: (Odd.pow_pos_iff (by decide)).mp
    (pos_of_mul_pos_right ((show 0 < (100 : Real) by simp).trans_le h) (by positivity))
-/
private theorem eps_pos {ε : Real} {n : Nat} (h : 100 <= (4 : Real) ^ n * ε ^ 5) : 0 < ε :=
  (Odd.pow_pos_iff (by decide)).mp
    (pos_of_mul_pos_right ((show 0 < (100 : Real) by simp).trans_le h) (by positivity))

set_option backward.privateInPublic true in
/--
theorem `m_pos` / 定理 `m_pos`

English:
theorem m_pos
  given: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  statement: 0 < m
  proof: Nat.div_pos (hPα.trans' <| by unfold stepBound; gcongr; simp)
    stepBound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos

中文:
定理 m_pos
  条件: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  结论: 0 < m
  证明: Nat.div_pos (hPα.trans' <| by unfold stepBound; gcongr; simp)
    stepBound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos
-/
private theorem m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) : 0 < m :=
Nat.div_pos (hPα.trans' <| by unfold stepBound; gcongr; simp)
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

/--
theorem `m_pos` / 定理 `m_pos`

English:
theorem m_pos
  given: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  statement: 0 < m
  proof: by
  sz_positivity

中文:
定理 m_pos
  条件: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  结论: 0 < m
  证明: by
  sz_positivity

Depends on / 依赖: sz_positivity
-/
theorem m_pos [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) : 0 < m := by
  sz_positivity

/--
theorem `coe_m_add_one_pos` / 定理 `coe_m_add_one_pos`

English:
theorem coe_m_add_one_pos
  statement: 0 < (m : Real) + 1
  proof: by positivity

中文:
定理 coe_m_add_one_pos
  结论: 0 < (m : 实数) + 1
  证明: by positivity
-/
theorem coe_m_add_one_pos : 0 < (m : Real) + 1 := by positivity

/--
theorem `one_le_m_coe` / 定理 `one_le_m_coe`

English:
theorem one_le_m_coe
  given: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  statement: (1 : Real) <= m
  proof: Nat.one_le_cast.2 m_pos hPα

中文:
定理 one_le_m_coe
  条件: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  结论: (1 : 实数) <= m
  证明: Nat.one_le_cast.2 m_pos hPα

Depends on / 依赖: Nat.one_le_cast, m_pos, one_le_cast
-/
theorem one_le_m_coe [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) : (1 : Real) <= m :=
Nat.one_le_cast.2 m_pos hPα

/--
theorem `eps_pow_five_pos` / 定理 `eps_pow_five_pos`

English:
theorem eps_pow_five_pos
  given: (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5)
  statement: ↑0 < ε ^ 5
  proof: pos_of_mul_pos_right ((by simp : (0 : Real) < 100).trans_le hPε) by positivity

中文:
定理 eps_pow_five_pos
  条件: (hPε : 100 <= (4 : 实数) ^ #P.parts * ε ^ 5)
  结论: ↑0 < ε ^ 5
  证明: pos_of_mul_pos_right ((by simp : (0 : Real) < 100).trans_le hPε) by positivity

Depends on / 依赖: pos_of_mul_pos_right, trans_le
-/
theorem eps_pow_five_pos (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5) : ↑0 < ε ^ 5 :=
pos_of_mul_pos_right ((by simp : (0 : Real) < 100).trans_le hPε) by positivity

/--
theorem `eps_pos` / 定理 `eps_pos`

English:
theorem eps_pos
  given: (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5)
  statement: 0 < ε
  proof: (Odd.pow_pos_iff (by decide)).mp (eps_pow_five_pos hPε)

中文:
定理 eps_pos
  条件: (hPε : 100 <= (4 : 实数) ^ #P.parts * ε ^ 5)
  结论: 0 < ε
  证明: (Odd.pow_pos_iff (by decide)).mp (eps_pow_five_pos hPε)

Depends on / 依赖: Odd.pow_pos_iff, eps_pow_five_pos, pow_pos_iff
-/
theorem eps_pos (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5) : 0 < ε :=
  (Odd.pow_pos_iff (by decide)).mp (eps_pow_five_pos hPε)

/--
theorem `hundred_div_ε_pow_five_le_m` / 定理 `hundred_div_ε_pow_five_le_m`

English:
theorem hundred_div_ε_pow_five_le_m
  statement: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  proof: (div_le_of_le_mul₀ (eps_pow_five_pos hPε).le (by positivity) hPε).trans by
    norm_cast
    rwa [Nat.le_div_iff_mul_le (stepBound_pos (P.parts_nonempty <|
      univ_nonempty.ne_empty).card_pos), stepBound, mul_left_comm, ← mul_pow]

中文:
定理 hundred_div_ε_pow_five_le_m
  结论: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  证明: (div_le_of_le_mul₀ (eps_pow_five_pos hPε).le (by positivity) hPε).trans by
    norm_cast
    rwa [Nat.le_div_iff_mul_le (stepBound_pos (P.parts_nonempty <|
      univ_nonempty.ne_empty).card_pos), stepBound, mul_left_comm, ← mul_pow]

Depends on / 依赖: Nat.le_div_iff_mul_le, P.parts_nonempty, card_pos, eps_pow_five_pos, le_div_iff_mul_le, mul_left_comm, mul_pow, ne_empty, parts_nonempty, stepBound, stepBound_pos, univ_nonempty, univ_nonempty.ne_empty
-/
theorem hundred_div_ε_pow_five_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
    (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5) : 100 / ε ^ 5 <= m :=
(div_le_of_le_mul₀ (eps_pow_five_pos hPε).le (by positivity) hPε).trans by
    norm_cast
    rwa [Nat.le_div_iff_mul_le (stepBound_pos (P.parts_nonempty <|
      univ_nonempty.ne_empty).card_pos), stepBound, mul_left_comm, ← mul_pow]

/--
theorem `hundred_le_m` / 定理 `hundred_le_m`

English:
theorem hundred_le_m
  statement: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  proof: mod_cast
    (hundred_div_ε_pow_five_le_m hPα hPε).trans'
      (le_div_self (by simp) (by sz_positivity) <| pow_le_one₀ (by sz_positivity) hε)

中文:
定理 hundred_le_m
  结论: [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
  证明: mod_cast
    (hundred_div_ε_pow_five_le_m hPα hPε).trans'
      (le_div_self (by simp) (by sz_positivity) <| pow_le_one₀ (by sz_positivity) hε)

Depends on / 依赖: le_div_self, mod_cast, sz_positivity
-/
theorem hundred_le_m [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α)
    (hPε : 100 <= (4 : Real) ^ #P.parts * ε ^ 5) (hε : ε <= 1) : 100 <= m :=
  mod_cast
    (hundred_div_ε_pow_five_le_m hPα hPε).trans'
      (le_div_self (by simp) (by sz_positivity) <| pow_le_one₀ (by sz_positivity) hε)

/--
theorem `a_add_one_le_four_pow_parts_card` / 定理 `a_add_one_le_four_pow_parts_card`

English:
theorem a_add_one_le_four_pow_parts_card
  statement: a + 1 <= 4 ^ #P.parts
  proof: by
  have h : 1 <= 4 ^ #P.parts := one_le_pow₀ (by simp)
  rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
  conv_rhs => rw [← Nat.sub_add_cancel h]
  rw [add_le_add_iff_right]; rw [tsub_le_iff_left]; rw [← Nat.add_sub_assoc h]
  exact Nat.le_sub_one_of_lt (Nat.lt_div_mul_add h)

中文:
定理 a_add_one_le_four_pow_parts_card
  结论: a + 1 <= 4 ^ #P.parts
  证明: by
  have h : 1 <= 4 ^ #P.parts := one_le_pow₀ (by simp)
  rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
  conv_rhs => rw [← Nat.sub_add_cancel h]
  rw [add_le_add_iff_right]; rw [tsub_le_iff_left]; rw [← Nat.add_sub_assoc h]
  exact Nat.le_sub_one_of_lt (Nat.lt_div_mul_add h)

Depends on / 依赖: Nat.add_sub_assoc, Nat.div_div_eq_div_mul, Nat.le_sub_one_of_lt, Nat.lt_div_mul_add, Nat.sub_add_cancel, P.parts, add_le_add_iff_right, add_sub_assoc, conv_rhs, div_div_eq_div_mul, le_sub_one_of_lt, lt_div_mul_add, stepBound, sub_add_cancel, tsub_le_iff_left
-/
theorem a_add_one_le_four_pow_parts_card : a + 1 <= 4 ^ #P.parts := by
  have h : 1 <= 4 ^ #P.parts := one_le_pow₀ (by simp)
  rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
  conv_rhs => rw [← Nat.sub_add_cancel h]
  rw [add_le_add_iff_right]; rw [tsub_le_iff_left]; rw [← Nat.add_sub_assoc h]
  exact Nat.le_sub_one_of_lt (Nat.lt_div_mul_add h)

/--
theorem `card_aux₁` / 定理 `card_aux₁`

English:
theorem card_aux₁
  given: (hucard : #u = m * 4 ^ #P.parts + a)
  proof: by
  rw [hucard]; rw [mul_add]; rw [mul_one]; rw [← add_assoc]; rw [← add_mul]; rw [Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card)]; rw [mul_comm]

中文:
定理 card_aux₁
  条件: (hucard : #u = m * 4 ^ #P.parts + a)
  证明: by
  rw [hucard]; rw [mul_add]; rw [mul_one]; rw [← add_assoc]; rw [← add_mul]; rw [Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card)]; rw [mul_comm]

Depends on / 依赖: Nat.le_succ, Nat.sub_add_cancel, a_add_one_le_four_pow_parts_card, add_assoc, add_mul, hucard, le_succ, mul_add, mul_comm, mul_one, sub_add_cancel
-/
theorem card_aux₁ (hucard : #u = m * 4 ^ #P.parts + a) :
    (4 ^ #P.parts - a) * m + a * (m + 1) = #u := by
  rw [hucard]; rw [mul_add]; rw [mul_one]; rw [← add_assoc]; rw [← add_mul]; rw [Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card)]; rw [mul_comm]

/--
theorem `card_aux₂` / 定理 `card_aux₂`

English:
theorem card_aux₂
  given: (hP : P.IsEquipartition) (hu : u in P.parts) (hucard : #u != m * 4 ^ #P.parts + a)
  proof: by
  have : m * 4 ^ #P.parts <= card α / #P.parts := by
    rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  rw [Nat.add_sub_of_le this] at hucard
  rw [(hP.card_parts_eq_average hu).resolve_left hucard]; rw [mul_add]; rw [mul_one]; rw [← add_assoc]; rw [← add_mul]; 

中文:
定理 card_aux₂
  条件: (hP : P.IsEquipartition) (hu : u in P.parts) (hucard : #u != m * 4 ^ #P.parts + a)
  证明: by
  have : m * 4 ^ #P.parts <= card α / #P.parts := by
    rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  rw [Nat.add_sub_of_le this] at hucard
  rw [(hP.card_parts_eq_average hu).resolve_left hucard]; rw [mul_add]; rw [mul_one]; rw [← add_assoc]; rw [← add_mul]; 

Depends on / 依赖: Nat.add_sub_of_le, Nat.div_div_eq_div_mul, Nat.div_mul_le_self, Nat.sub_add_cancel, P.parts, a_add_one_le_four_pow_parts_card, add_assoc, add_mul, add_sub_of_le, card_parts_eq_average, card_univ, div_div_eq_div_mul, div_mul_le_self, hP.card_parts_eq_average, hucard, mul_add, mul_comm, mul_one, resolve_left, stepBound
-/
theorem card_aux₂ (hP : P.IsEquipartition) (hu : u in P.parts) (hucard : #u != m * 4 ^ #P.parts + a) :
    (4 ^ #P.parts - (a + 1)) * m + (a + 1) * (m + 1) = #u := by
  have : m * 4 ^ #P.parts <= card α / #P.parts := by
    rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  rw [Nat.add_sub_of_le this] at hucard
  rw [(hP.card_parts_eq_average hu).resolve_left hucard]; rw [mul_add]; rw [mul_one]; rw [← add_assoc]; rw [← add_mul]; rw [Nat.sub_add_cancel a_add_one_le_four_pow_parts_card]; rw [← add_assoc]; rw [mul_comm]; rw [Nat.add_sub_of_le this]; rw [card_univ]

/--
theorem `pow_mul_m_le_card_part` / 定理 `pow_mul_m_le_card_part`

English:
theorem pow_mul_m_le_card_part
  given: (hP : P.IsEquipartition) (hu : u in P.parts)
  proof: by
  norm_cast
  rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)

中文:
定理 pow_mul_m_le_card_part
  条件: (hP : P.IsEquipartition) (hu : u in P.parts)
  证明: by
  norm_cast
  rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)

Depends on / 依赖: Nat.div_div_eq_div_mul, Nat.mul_div_le, average_le_card_part, div_div_eq_div_mul, hP.average_le_card_part, mul_div_le, stepBound
-/
theorem pow_mul_m_le_card_part (hP : P.IsEquipartition) (hu : u in P.parts) :
    (4 : Real) ^ #P.parts * m <= #u := by
  norm_cast
  rw [stepBound]; rw [← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)

variable (P ε) (l : Nat)

/--
Definition of `initialBound` / `initialBound` 的定义

English:
definition initialBound
  signature: : Nat
  body: max 7 max l ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1

中文:
定义 initialBound
  签名: : 自然数
  定义体: max 7 max l ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1
-/
noncomputable def initialBound : Nat :=
max 7 max l ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1

/--
theorem `le_initialBound` / 定理 `le_initialBound`

English:
theorem le_initialBound
  statement: l <= initialBound ε l
  proof: (le_max_left _ _).trans le_max_right _ _

中文:
定理 le_initialBound
  结论: l <= initialBound ε l
  证明: (le_max_left _ _).trans le_max_right _ _

Depends on / 依赖: le_max_left, le_max_right
-/
theorem le_initialBound : l <= initialBound ε l :=
(le_max_left _ _).trans le_max_right _ _

/--
theorem `seven_le_initialBound` / 定理 `seven_le_initialBound`

English:
theorem seven_le_initialBound
  statement: 7 <= initialBound ε l
  proof: le_max_left _ _

中文:
定理 seven_le_initialBound
  结论: 7 <= initialBound ε l
  证明: le_max_left _ _

Depends on / 依赖: le_max_left
-/
theorem seven_le_initialBound : 7 <= initialBound ε l :=
  le_max_left _ _

/--
theorem `initialBound_pos` / 定理 `initialBound_pos`

English:
theorem initialBound_pos
  statement: 0 < initialBound ε l
  proof: Nat.succ_pos'.trans_le seven_le_initialBound _ _

中文:
定理 initialBound_pos
  结论: 0 < initialBound ε l
  证明: Nat.succ_pos'.trans_le seven_le_initialBound _ _

Depends on / 依赖: Nat.succ_pos, seven_le_initialBound, succ_pos, trans_le
-/
theorem initialBound_pos : 0 < initialBound ε l :=
Nat.succ_pos'.trans_le seven_le_initialBound _ _

/--
theorem `hundred_lt_pow_initialBound_mul` / 定理 `hundred_lt_pow_initialBound_mul`

English:
theorem hundred_lt_pow_initialBound_mul
  given: {ε : Real} (hε : 0 < ε) (l : Nat)
  proof: by
  rw [← rpow_natCast 4]; rw [← div_lt_iff₀ (pow_pos hε 5)]; rw [lt_rpow_iff_log_lt _ zero_lt_four]; rw [←
    div_lt_iff₀]; rw [initialBound]; rw [Nat.cast_max]; rw [Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by simp)

中文:
定理 hundred_lt_pow_initialBound_mul
  条件: {ε : 实数} (hε : 0 < ε) (l : 自然数)
  证明: by
  rw [← rpow_natCast 4]; rw [← div_lt_iff₀ (pow_pos hε 5)]; rw [lt_rpow_iff_log_lt _ zero_lt_four]; rw [←
    div_lt_iff₀]; rw [initialBound]; rw [Nat.cast_max]; rw [Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by simp)

Depends on / 依赖: Nat.cast_max, Nat.lt_floor_add_one, cast_max, div_pos, initialBound, log_pos, lt_floor_add_one, lt_max_of_lt_right, lt_rpow_iff_log_lt, pow_pos, rpow_natCast, zero_lt_four
-/
theorem hundred_lt_pow_initialBound_mul {ε : Real} (hε : 0 < ε) (l : Nat) :
    100 < ↑4 ^ initialBound ε l * ε ^ 5 := by
  rw [← rpow_natCast 4]; rw [← div_lt_iff₀ (pow_pos hε 5)]; rw [lt_rpow_iff_log_lt _ zero_lt_four]; rw [←
    div_lt_iff₀]; rw [initialBound]; rw [Nat.cast_max]; rw [Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by simp)
  · exact div_pos (by simp) (pow_pos hε 5)

/--
Definition of `bound` / `bound` 的定义

English:
definition bound
  signature: : Nat
  body: (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)

中文:
定义 bound
  签名: : 自然数
  定义体: (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)

Depends on / 依赖: initialBound, stepBound
-/
noncomputable def bound : Nat :=
  (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)

/--
theorem `initialBound_le_bound` / 定理 `initialBound_le_bound`

English:
theorem initialBound_le_bound
  statement: initialBound ε l <= bound ε l
  proof: (id_le_iterate_of_id_le le_stepBound _ _).trans Nat.le_mul_of_pos_right _ by positivity

中文:
定理 initialBound_le_bound
  结论: initialBound ε l <= bound ε l
  证明: (id_le_iterate_of_id_le le_stepBound _ _).trans Nat.le_mul_of_pos_right _ by positivity

Depends on / 依赖: Nat.le_mul_of_pos_right, id_le_iterate_of_id_le, le_mul_of_pos_right, le_stepBound
-/
theorem initialBound_le_bound : initialBound ε l <= bound ε l :=
(id_le_iterate_of_id_le le_stepBound _ _).trans Nat.le_mul_of_pos_right _ by positivity

/--
theorem `le_bound` / 定理 `le_bound`

English:
theorem le_bound
  statement: l <= bound ε l
  proof: (le_initialBound ε l).trans initialBound_le_bound ε l

中文:
定理 le_bound
  结论: l <= bound ε l
  证明: (le_initialBound ε l).trans initialBound_le_bound ε l

Depends on / 依赖: initialBound_le_bound, le_initialBound
-/
theorem le_bound : l <= bound ε l :=
(le_initialBound ε l).trans initialBound_le_bound ε l

/--
theorem `bound_pos` / 定理 `bound_pos`

English:
theorem bound_pos
  statement: 0 < bound ε l
  proof: (initialBound_pos ε l).trans_le initialBound_le_bound ε l

中文:
定理 bound_pos
  结论: 0 < bound ε l
  证明: (initialBound_pos ε l).trans_le initialBound_le_bound ε l

Depends on / 依赖: initialBound_le_bound, initialBound_pos, trans_le
-/
theorem bound_pos : 0 < bound ε l :=
(initialBound_pos ε l).trans_le initialBound_le_bound ε l

variable {ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s t : Finset ι} {x : 𝕜}

/--
theorem `mul_sq_le_sum_sq` / 定理 `mul_sq_le_sum_sq`

English:
theorem mul_sq_le_sum_sq
  statement: (hst : s subseteq t) (f : ι -> 𝕜) (hs : x ^ 2 <= ((∑ i in s, f i) / #s) ^ 2)
  proof: calc
  _ <= (#s : 𝕜) * ((∑ i in s, f i ^ 2) / #s) := by
    gcongr
    exact hs.trans sum_div_card_sq_le_sum_sq_div_card
  _ = ∑ i in s, f i ^ 2 := mul_div_cancel₀ _ hs'
  _ <= ∑ i in t, f i ^ 2 := by gcongr

中文:
定理 mul_sq_le_sum_sq
  结论: (hst : s subseteq t) (f : ι -> 𝕜) (hs : x ^ 2 <= ((∑ i in s, f i) / #s) ^ 2)
  证明: calc
  _ <= (#s : 𝕜) * ((∑ i in s, f i ^ 2) / #s) := by
    gcongr
    exact hs.trans sum_div_card_sq_le_sum_sq_div_card
  _ = ∑ i in s, f i ^ 2 := mul_div_cancel₀ _ hs'
  _ <= ∑ i in t, f i ^ 2 := by gcongr
-/
theorem mul_sq_le_sum_sq (hst : s subseteq t) (f : ι -> 𝕜) (hs : x ^ 2 <= ((∑ i in s, f i) / #s) ^ 2)
    (hs' : (#s : 𝕜) != 0) : (#s : 𝕜) * x ^ 2 <= ∑ i in t, f i ^ 2 := calc
  _ <= (#s : 𝕜) * ((∑ i in s, f i ^ 2) / #s) := by
    gcongr
    exact hs.trans sum_div_card_sq_le_sum_sq_div_card
  _ = ∑ i in s, f i ^ 2 := mul_div_cancel₀ _ hs'
  _ <= ∑ i in t, f i ^ 2 := by gcongr

/--
theorem `add_div_le_sum_sq_div_card` / 定理 `add_div_le_sum_sq_div_card`

English:
theorem add_div_le_sum_sq_div_card
  statement: (hst : s subseteq t) (f : ι -> 𝕜) (d : 𝕜) (hx : 0 <= x)
  proof: by
  obtain hscard | hscard := ((#s).cast_nonneg : (0 : 𝕜) <= #s).eq_or_lt
  · simpa [← hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card
  have htcard : (0 : 𝕜) < #t := hscard.trans_le (Nat.cast_le.2 (card_le_card hst))
  have h₁ : x ^ 2 <= ((∑ i in s, f i) / #s - (∑ i in t, f i) / #t) ^ 2 

中文:
定理 add_div_le_sum_sq_div_card
  结论: (hst : s subseteq t) (f : ι -> 𝕜) (d : 𝕜) (hx : 0 <= x)
  证明: by
  obtain hscard | hscard := ((#s).cast_nonneg : (0 : 𝕜) <= #s).eq_or_lt
  · simpa [← hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card
  have htcard : (0 : 𝕜) < #t := hscard.trans_le (Nat.cast_le.2 (card_le_card hst))
  have h₁ : x ^ 2 <= ((∑ i in s, f i) / #s - (∑ i in t, f i) / #t) ^ 2 

Depends on / 依赖: Nat.cast_le, abs_of_nonneg, card_le_card, cast_le, cast_nonneg, eq_or_lt, hscard, hscard.trans_le, ht.trans, htcard, nsmul_eq_mul, sq_le_sq, sub_div, sum_const, sum_div_card_sq_le_sum_sq_div_card, sum_sub_distrib, trans_le
-/
theorem add_div_le_sum_sq_div_card (hst : s subseteq t) (f : ι -> 𝕜) (d : 𝕜) (hx : 0 <= x)
    (hs : x <= |(∑ i in s, f i) / #s - (∑ i in t, f i) / #t|) (ht : d <= ((∑ i in t, f i) / #t) ^ 2) :
    d + #s / #t * x ^ 2 <= (∑ i in t, f i ^ 2) / #t := by
  obtain hscard | hscard := ((#s).cast_nonneg : (0 : 𝕜) <= #s).eq_or_lt
  · simpa [← hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card
  have htcard : (0 : 𝕜) < #t := hscard.trans_le (Nat.cast_le.2 (card_le_card hst))
  have h₁ : x ^ 2 <= ((∑ i in s, f i) / #s - (∑ i in t, f i) / #t) ^ 2 :=
    sq_le_sq.2 (by rwa [abs_of_nonneg hx])
  have h₂ : x ^ 2 <= ((∑ i in s, (f i - (∑ j in t, f j) / #t)) / #s) ^ 2 := by
    apply h₁.trans
    rw [sum_sub_distrib]; rw [sum_const]; rw [nsmul_eq_mul]; rw [sub_div]; rw [mul_div_cancel_left₀ _ hscard.ne']
  grw [ht]
  rw [← mul_div_right_comm]; rw [le_div_iff₀ htcard]; rw [add_mul]; rw [div_mul_cancel₀ _ htcard.ne']
  have h₃ := mul_sq_le_sum_sq hst (fun i => (f i - (∑ j in t, f j) / #t)) h₂ hscard.ne'
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
  | 0, ~q(Nat), ~q(SzemerediRegularity.initialBound $ε $l) =>
    assertInstancesCommute
    pure (.positive q(SzemerediRegularity.initialBound_pos $ε $l))
  | _, _, _ => throwError "not initialBound"


example (ε : Real) (l : Nat) : 0 < SzemerediRegularity.initialBound ε l := by positivity

/-- Extension for the `positivity` tactic: `SzemerediRegularity.bound` is always positive. -/
@[positivity SzemerediRegularity.bound _ _]
meta def evalBound : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(SzemerediRegularity.bound $ε $l) =>
    assertInstancesCommute
    pure (.positive q(SzemerediRegularity.bound_pos $ε $l))
  | _, _, _ => throwError "not bound"

example (ε : Real) (l : Nat) : 0 < SzemerediRegularity.bound ε l := by positivity

end Mathlib.Meta.Positivity
