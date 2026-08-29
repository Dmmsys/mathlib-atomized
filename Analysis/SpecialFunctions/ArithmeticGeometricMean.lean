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

/--
lemma `sqrt_mul_le_half_add` / 引理 `sqrt_mul_le_half_add`

English:
lemma sqrt_mul_le_half_add
  given: (x y : Real>=0)
  statement: sqrt (x * y) <= (x + y) / 2
  proof: by
  rw [sqrt_le_iff_le_sq]; rw [div_pow]; rw [le_div_iff₀' (by positivity)]; rw [← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

中文:
引理 sqrt_mul_le_half_add
  条件: (x y : 实数>=0)
  结论: sqrt (x * y) <= (x + y) / 2
  证明: by
  rw [sqrt_le_iff_le_sq]; rw [div_pow]; rw [le_div_iff₀' (by positivity)]; rw [← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

Depends on / 依赖: div_pow, four_mul_le_sq_add, mul_assoc, sqrt_le_iff_le_sq
-/
lemma sqrt_mul_le_half_add (x y : Real>=0) : sqrt (x * y) <= (x + y) / 2 := by
  rw [sqrt_le_iff_le_sq]; rw [div_pow]; rw [le_div_iff₀' (by positivity)]; rw [← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

/--
lemma `sqrt_mul_lt_half_add_of_ne` / 引理 `sqrt_mul_lt_half_add_of_ne`

English:
lemma sqrt_mul_lt_half_add_of_ne
  given: {x y : Real>=0} (h : x != y)
  statement: sqrt (x * y) < (x + y) / 2
  proof: by
  wlog hl : y < x generalizing x y
  · specialize this h.symm (h.gt_or_lt.resolve_left hl)
    rwa [mul_comm, add_comm]
  have key : 0 < (x - y) ^ 2 := sq_pos_iff.mpr (by rwa [← zero_lt_iff, tsub_pos_iff_lt])
  rw [sq]; rw [tsub_mul]; rw [mul_tsub]; rw [mul_tsub]; rw [tsub_tsub_eq_add_tsub_of_le (by gcongr)]; rw [tsub_add_eq_add_tsub (by gcongr)]; rw [tsub_tsub]; rw [show x * y + y * x = 2 * x * y by ring]; rw [tsub_pos_iff_lt]; rw [← sq]; rw [← sq] at key
  rw [← sqrt_sq (_ / 2)]; rw [sqrt_lt_sqrt]; rw [div_pow]; rw [lt_div_iff₀' (by positivity)]; rw [show (2 : Real>=0) ^ 2 * (x * y) = 2 * x * y + 2 * x * y by ring]; rw [add_sq]; rw [add_right_comm]
  gcongr

中文:
引理 sqrt_mul_lt_half_add_of_ne
  条件: {x y : 实数>=0} (h : x != y)
  结论: sqrt (x * y) < (x + y) / 2
  证明: by
  wlog hl : y < x generalizing x y
  · specialize this h.symm (h.gt_or_lt.resolve_left hl)
    rwa [mul_comm, add_comm]
  have key : 0 < (x - y) ^ 2 := sq_pos_iff.mpr (by rwa [← zero_lt_iff, tsub_pos_iff_lt])
  rw [sq]; rw [tsub_mul]; rw [mul_tsub]; rw [mul_tsub]; rw [tsub_tsub_eq_add_tsub_of_le (by gcongr)]; rw [tsub_add_eq_add_tsub (by gcongr)]; rw [tsub_tsub]; rw [show x * y + y * x = 2 * x * y by ring]; rw [tsub_pos_iff_lt]; rw [← sq]; rw [← sq] at key
  rw [← sqrt_sq (_ / 2)]; rw [sqrt_lt_sqrt]; rw [div_pow]; rw [lt_div_iff₀' (by positivity)]; rw [show (2 : Real>=0) ^ 2 * (x * y) = 2 * x * y + 2 * x * y by ring]; rw [add_sq]; rw [add_right_comm]
  gcongr

Depends on / 依赖: add_comm, generalizing, gt_or_lt, h.gt_or_lt.resolve_left, h.symm, mul_comm, mul_tsub, resolve_left, specialize, sq_pos_iff, sq_pos_iff.mpr, sqrt_lt_sqrt, sqrt_sq, tsub_add_eq_add_tsub, tsub_mul, tsub_pos_iff_lt, tsub_tsub, tsub_tsub_eq_add_tsub_of_le, zero_lt_iff
-/
lemma sqrt_mul_lt_half_add_of_ne {x y : Real>=0} (h : x != y) : sqrt (x * y) < (x + y) / 2 := by
  wlog hl : y < x generalizing x y
  · specialize this h.symm (h.gt_or_lt.resolve_left hl)
    rwa [mul_comm, add_comm]
  have key : 0 < (x - y) ^ 2 := sq_pos_iff.mpr (by rwa [← zero_lt_iff, tsub_pos_iff_lt])
  rw [sq]; rw [tsub_mul]; rw [mul_tsub]; rw [mul_tsub]; rw [tsub_tsub_eq_add_tsub_of_le (by gcongr)]; rw [tsub_add_eq_add_tsub (by gcongr)]; rw [tsub_tsub]; rw [show x * y + y * x = 2 * x * y by ring]; rw [tsub_pos_iff_lt]; rw [← sq]; rw [← sq] at key
  rw [← sqrt_sq (_ / 2)]; rw [sqrt_lt_sqrt]; rw [div_pow]; rw [lt_div_iff₀' (by positivity)]; rw [show (2 : Real>=0) ^ 2 * (x * y) = 2 * x * y + 2 * x * y by ring]; rw [add_sq]; rw [add_right_comm]
  gcongr

open Function Filter Topology

/--
Definition of `agmSequences` / `agmSequences` 的定义

English:
definition agmSequences
  signature: (x y : Real>=0)
  body: fun n => (fun p => (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)

中文:
定义 agmSequences
  签名: (x y : 实数>=0)
  定义体: fun n => (fun p => (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)
-/
noncomputable def agmSequences (x y : Real>=0) : Nat -> Real>=0 × Real>=0 :=
  fun n => (fun p => (sqrt (p.1 * p.2), (p.1 + p.2) / 2))^[n + 1] (x, y)

variable {x y : Real>=0} {n : Nat}

@[simp]
/--
lemma `agmSequences_zero` / 引理 `agmSequences_zero`

English:
lemma agmSequences_zero
  statement: agmSequences x y 0 = (sqrt (x * y), (x + y) / 2)
  proof: rfl

中文:
引理 agmSequences_zero
  结论: agmSequences x y 0 = (sqrt (x * y), (x + y) / 2)
  证明: rfl
-/
lemma agmSequences_zero : agmSequences x y 0 = (sqrt (x * y), (x + y) / 2) := rfl

/--
lemma `agmSequences_succ` / 引理 `agmSequences_succ`

English:
lemma agmSequences_succ
  statement: agmSequences x y (n + 1) = agmSequences (sqrt (x * y)) ((x + y) / 2) n
  proof: rfl

中文:
引理 agmSequences_succ
  结论: agmSequences x y (n + 1) = agmSequences (sqrt (x * y)) ((x + y) / 2) n
  证明: rfl
-/
lemma agmSequences_succ : agmSequences x y (n + 1) = agmSequences (sqrt (x * y)) ((x + y) / 2) n :=
  rfl

/--
lemma `agmSequences_succ'` / 引理 `agmSequences_succ'`

English:
lemma agmSequences_succ'
  proof: by
  rw [agmSequences]; rw [agmSequences]; rw [iterate_succ']; rw [comp_apply]

中文:
引理 agmSequences_succ'
  证明: by
  rw [agmSequences]; rw [agmSequences]; rw [iterate_succ']; rw [comp_apply]

Depends on / 依赖: agmSequences, comp_apply, iterate_succ
-/
lemma agmSequences_succ' :
    agmSequences x y (n + 1) =
    (sqrt ((agmSequences x y n).1 * (agmSequences x y n).2),
      ((agmSequences x y n).1 + (agmSequences x y n).2) / 2) := by
  rw [agmSequences]; rw [agmSequences]; rw [iterate_succ']; rw [comp_apply]

/--
lemma `agmSequences_comm` / 引理 `agmSequences_comm`

English:
lemma agmSequences_comm
  statement: agmSequences x y = agmSequences y x
  proof: by
  funext n
  cases n with
  | zero => simp [mul_comm, add_comm]
  | succ n => simp [agmSequences_succ, mul_comm, add_comm]

中文:
引理 agmSequences_comm
  结论: agmSequences x y = agmSequences y x
  证明: by
  funext n
  cases n with
  | zero => simp [mul_comm, add_comm]
  | succ n => simp [agmSequences_succ, mul_comm, add_comm]

Depends on / 依赖: add_comm, agmSequences_succ, mul_comm
-/
lemma agmSequences_comm : agmSequences x y = agmSequences y x := by
  funext n
  cases n with
  | zero => simp [mul_comm, add_comm]
  | succ n => simp [agmSequences_succ, mul_comm, add_comm]

/--
lemma `le_gm_and_am_le` / 引理 `le_gm_and_am_le`

English:
lemma le_gm_and_am_le
  given: (h : x <= y)
  statement: x <= sqrt (x * y) ∧ (x + y) / 2 <= y
  proof: by
  constructor
  · rw [le_sqrt_iff_sq_le, sq]
    gcongr
  · apply div_le_of_le_mul'
    rw [two_mul]
    gcongr

中文:
引理 le_gm_and_am_le
  条件: (h : x <= y)
  结论: x <= sqrt (x * y) ∧ (x + y) / 2 <= y
  证明: by
  constructor
  · rw [le_sqrt_iff_sq_le, sq]
    gcongr
  · apply div_le_of_le_mul'
    rw [two_mul]
    gcongr

Depends on / 依赖: IsRepresentable, IsRepresentable.mk, Iso.refl, div_le_of_le_mul, le_sqrt_iff_sq_le, two_mul
-/
lemma le_gm_and_am_le (h : x <= y) : x <= sqrt (x * y) ∧ (x + y) / 2 <= y := by
  constructor
  · rw [le_sqrt_iff_sq_le, sq]
    gcongr
  · apply div_le_of_le_mul'
    rw [two_mul]
    gcongr

/--
lemma `dist_gm_am_le` / 引理 `dist_gm_am_le`

English:
lemma dist_gm_am_le
  statement: dist (sqrt (x * y)) ((x + y) / 2) <= dist x y / 2
  proof: by
  wlog h : x <= y generalizing x y
  · simpa [add_comm, mul_comm, dist_comm] using this (not_le.mp h).le
  rw [dist_comm]; rw [dist_eq]; rw [← NNReal.coe_sub (sqrt_mul_le_half_add ..)]; rw [abs_eq]
  calc
    _ <= ((x + y) / 2 - x).toReal := by
      gcongr
      rw [le_sqrt_iff_sq_le]; rw [sq]
      gcongr
    _ = _ := by
      nth_rw 2 [← add_halves x]
      rw [add_div]; rw [add_tsub_add_eq_tsub_left]; rw [← tsub_div]; rw [NNReal.coe_div]; rw [NNReal.coe_two]; rw [dist_comm]; rw [dist_eq]; rw [← NNReal.coe_sub h]; rw [abs_eq]

中文:
引理 dist_gm_am_le
  结论: dist (sqrt (x * y)) ((x + y) / 2) <= dist x y / 2
  证明: by
  wlog h : x <= y generalizing x y
  · simpa [add_comm, mul_comm, dist_comm] using this (not_le.mp h).le
  rw [dist_comm]; rw [dist_eq]; rw [← NNReal.coe_sub (sqrt_mul_le_half_add ..)]; rw [abs_eq]
  calc
    _ <= ((x + y) / 2 - x).toReal := by
      gcongr
      rw [le_sqrt_iff_sq_le]; rw [sq]
      gcongr
    _ = _ := by
      nth_rw 2 [← add_halves x]
      rw [add_div]; rw [add_tsub_add_eq_tsub_left]; rw [← tsub_div]; rw [NNReal.coe_div]; rw [NNReal.coe_two]; rw [dist_comm]; rw [dist_eq]; rw [← NNReal.coe_sub h]; rw [abs_eq]

Depends on / 依赖: NNReal, NNReal.coe_div, NNReal.coe_sub, NNReal.coe_two, RepresentableBy, RepresentableBy.isRepresentable, RepresentableBy.yoneda, abs_eq, add_comm, add_div, add_halves, add_tsub_add_eq_tsub_left, coe_div, coe_sub, coe_two, dist_comm, dist_eq, generalizing, isRepresentable, le_sqrt_iff_sq_le
-/
lemma dist_gm_am_le : dist (sqrt (x * y)) ((x + y) / 2) <= dist x y / 2 := by
  wlog h : x <= y generalizing x y
  · simpa [add_comm, mul_comm, dist_comm] using this (not_le.mp h).le
  rw [dist_comm]; rw [dist_eq]; rw [← NNReal.coe_sub (sqrt_mul_le_half_add ..)]; rw [abs_eq]
  calc
    _ <= ((x + y) / 2 - x).toReal := by
      gcongr
      rw [le_sqrt_iff_sq_le]; rw [sq]
      gcongr
    _ = _ := by
      nth_rw 2 [← add_halves x]
      rw [add_div]; rw [add_tsub_add_eq_tsub_left]; rw [← tsub_div]; rw [NNReal.coe_div]; rw [NNReal.coe_two]; rw [dist_comm]; rw [dist_eq]; rw [← NNReal.coe_sub h]; rw [abs_eq]

/--
lemma `agmSequences_monotone_and_antitone` / 引理 `agmSequences_monotone_and_antitone`

English:
lemma agmSequences_monotone_and_antitone
  proof: by
  suffices forall n, (agmSequences x y n).1 <= (agmSequences x y (n + 1)).1 ∧
      (agmSequences x y (n + 1)).2 <= (agmSequences x y n).2 from
    ⟨monotone_nat_of_le_succ (this · |>.1), antitone_nat_of_succ_le (this · |>.2)⟩
  intro n
  induction n generalizing x y with
  | zero => exact le_gm_and_am_le (sqrt_mul_le_half_add ..)
  | succ n ih => exact Prod.mk_le_mk.mp ih

中文:
引理 agmSequences_monotone_and_antitone
  证明: by
  suffices forall n, (agmSequences x y n).1 <= (agmSequences x y (n + 1)).1 ∧
      (agmSequences x y (n + 1)).2 <= (agmSequences x y n).2 from
    ⟨monotone_nat_of_le_succ (this · |>.1), antitone_nat_of_succ_le (this · |>.2)⟩
  intro n
  induction n generalizing x y with
  | zero => exact le_gm_and_am_le (sqrt_mul_le_half_add ..)
  | succ n ih => exact Prod.mk_le_mk.mp ih

Depends on / 依赖: Prod.mk_le_mk.mp, agmSequences, antitone_nat_of_succ_le, generalizing, le_gm_and_am_le, mk_le_mk, monotone_nat_of_le_succ, sqrt_mul_le_half_add
-/
lemma agmSequences_monotone_and_antitone :
    (Monotone fun n => (agmSequences x y n).1) ∧ Antitone fun n => (agmSequences x y n).2 := by
  suffices forall n, (agmSequences x y n).1 <= (agmSequences x y (n + 1)).1 ∧
      (agmSequences x y (n + 1)).2 <= (agmSequences x y n).2 from
    ⟨monotone_nat_of_le_succ (this · |>.1), antitone_nat_of_succ_le (this · |>.2)⟩
  intro n
  induction n generalizing x y with
  | zero => exact le_gm_and_am_le (sqrt_mul_le_half_add ..)
  | succ n ih => exact Prod.mk_le_mk.mp ih

/--
lemma `agmSequences_fst_monotone` / 引理 `agmSequences_fst_monotone`

English:
lemma agmSequences_fst_monotone
  statement: Monotone fun n => (agmSequences x y n).1
  proof: agmSequences_monotone_and_antitone.1

中文:
引理 agmSequences_fst_monotone
  结论: 递增 fun n => (agmSequences x y n).1
  证明: agmSequences_monotone_and_antitone.1

Depends on / 依赖: agmSequences_monotone_and_antitone
-/
lemma agmSequences_fst_monotone : Monotone fun n => (agmSequences x y n).1 :=
  agmSequences_monotone_and_antitone.1

/--
lemma `agmSequences_snd_antitone` / 引理 `agmSequences_snd_antitone`

English:
lemma agmSequences_snd_antitone
  statement: Antitone fun n => (agmSequences x y n).2
  proof: agmSequences_monotone_and_antitone.2

中文:
引理 agmSequences_snd_antitone
  结论: 递减 fun n => (agmSequences x y n).2
  证明: agmSequences_monotone_and_antitone.2

Depends on / 依赖: IsCorepresentable, IsCorepresentable.mk, Iso.refl, agmSequences_monotone_and_antitone
-/
lemma agmSequences_snd_antitone : Antitone fun n => (agmSequences x y n).2 :=
  agmSequences_monotone_and_antitone.2

/--
lemma `agmSequences_fst_le_snd` / 引理 `agmSequences_fst_le_snd`

English:
lemma agmSequences_fst_le_snd
  given: (n m : Nat)
  statement: (agmSequences x y n).1 <= (agmSequences x y m).2
  proof: by
  suffices forall {k}, (agmSequences x y k).1 <= (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans this
    · exact this.trans (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_le_half_add ..
  | succ n ih => exact ih

中文:
引理 agmSequences_fst_le_snd
  条件: (n m : 自然数)
  结论: (agmSequences x y n).1 <= (agmSequences x y m).2
  证明: by
  suffices forall {k}, (agmSequences x y k).1 <= (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans this
    · exact this.trans (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_le_half_add ..
  | succ n ih => exact ih

Depends on / 依赖: CorepresentableBy, CorepresentableBy.coyoneda, CorepresentableBy.isCorepresentable, agmSequences, agmSequences_fst_monotone, agmSequences_snd_antitone, corepresentableByUliftFunctorEquiv, corepresentableByUliftFunctorEquiv.symm, coyoneda, generalizing, isCorepresentable, le_total, sqrt_mul_le_half_add, this.trans
-/
lemma agmSequences_fst_le_snd (n m : Nat) : (agmSequences x y n).1 <= (agmSequences x y m).2 := by
  suffices forall {k}, (agmSequences x y k).1 <= (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans this
    · exact this.trans (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_le_half_add ..
  | succ n ih => exact ih

/--
lemma `agmSequences_fst_lt_snd_of_ne` / 引理 `agmSequences_fst_lt_snd_of_ne`

English:
lemma agmSequences_fst_lt_snd_of_ne
  given: (h : x != y) (n m : Nat)
  proof: by
  suffices forall {k}, (agmSequences x y k).1 < (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans_lt this
    · exact this.trans_le (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_lt_half_add_of_ne h
  | succ n ih =>
    rw [agmSequences_succ']
    exact sqrt_mul_lt_half_add_of_ne (ih h).ne

中文:
引理 agmSequences_fst_lt_snd_of_ne
  条件: (h : x != y) (n m : 自然数)
  证明: by
  suffices forall {k}, (agmSequences x y k).1 < (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans_lt this
    · exact this.trans_le (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_lt_half_add_of_ne h
  | succ n ih =>
    rw [agmSequences_succ']
    exact sqrt_mul_lt_half_add_of_ne (ih h).ne

Depends on / 依赖: agmSequences, agmSequences_fst_monotone, agmSequences_snd_antitone, agmSequences_succ, generalizing, le_total, sqrt_mul_lt_half_add_of_ne, this.trans_le, trans_le, trans_lt
-/
lemma agmSequences_fst_lt_snd_of_ne (h : x != y) (n m : Nat) :
    (agmSequences x y n).1 < (agmSequences x y m).2 := by
  suffices forall {k}, (agmSequences x y k).1 < (agmSequences x y k).2 by
    obtain h | h := le_total n m
    · exact (agmSequences_fst_monotone h).trans_lt this
    · exact this.trans_le (agmSequences_snd_antitone h)
  intro k
  induction k generalizing x y with
  | zero => exact sqrt_mul_lt_half_add_of_ne h
  | succ n ih =>
    rw [agmSequences_succ']
    exact sqrt_mul_lt_half_add_of_ne (ih h).ne

/--
lemma `agmSequences_min_max` / 引理 `agmSequences_min_max`

English:
lemma agmSequences_min_max
  statement: agmSequences (min x y) (max x y) = agmSequences x y
  proof: by
  obtain h | h := le_total x y
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, agmSequences_comm]

中文:
引理 agmSequences_min_max
  结论: agmSequences (最小值 x y) (最大值 x y) = agmSequences x y
  证明: by
  obtain h | h := le_total x y
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, agmSequences_comm]

Depends on / 依赖: agmSequences_comm, le_total, max_eq_left, max_eq_right, min_eq_left, min_eq_right
-/
lemma agmSequences_min_max : agmSequences (min x y) (max x y) = agmSequences x y := by
  obtain h | h := le_total x y
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, agmSequences_comm]

/--
lemma `dist_agmSequences_fst_snd` / 引理 `dist_agmSequences_fst_snd`

English:
lemma dist_agmSequences_fst_snd
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp [dist_gm_am_le]
  | succ n ih =>
    rw [agmSequences_succ']
    apply dist_gm_am_le.trans
    rw [pow_succ]; rw [← div_div]
    gcongr

中文:
引理 dist_agmSequences_fst_snd
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp [dist_gm_am_le]
  | succ n ih =>
    rw [agmSequences_succ']
    apply dist_gm_am_le.trans
    rw [pow_succ]; rw [← div_div]
    gcongr

Depends on / 依赖: agmSequences_succ, dist_gm_am_le, dist_gm_am_le.trans, div_div, pow_succ
-/
lemma dist_agmSequences_fst_snd (n : Nat) :
    dist (agmSequences x y n).1 (agmSequences x y n).2 <= dist x y / 2 ^ (n + 1) := by
  induction n with
  | zero => simp [dist_gm_am_le]
  | succ n ih =>
    rw [agmSequences_succ']
    apply dist_gm_am_le.trans
    rw [pow_succ]; rw [← div_div]
    gcongr

/--
lemma `tendsto_dist_agmSequences_atTop_zero` / 引理 `tendsto_dist_agmSequences_atTop_zero`

English:
lemma tendsto_dist_agmSequences_atTop_zero
  proof: by
  apply squeeze_zero (fun _ => dist_nonneg) dist_agmSequences_fst_snd
  conv =>
    rw [← zero_mul (dist x y / 2)]
    enter [1, n]
    rw [pow_succ']; rw [← div_div]; rw [div_eq_inv_mul]; rw [← inv_pow]
  exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _

中文:
引理 tendsto_dist_agmSequences_atTop_zero
  证明: by
  apply squeeze_zero (fun _ => dist_nonneg) dist_agmSequences_fst_snd
  conv =>
    rw [← zero_mul (dist x y / 2)]
    enter [1, n]
    rw [pow_succ']; rw [← div_div]; rw [div_eq_inv_mul]; rw [← inv_pow]
  exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _

Depends on / 依赖: _root_, _root_.tendsto_pow_atTop_nhds_zero_of_lt_one, dist_agmSequences_fst_snd, dist_nonneg, div_div, div_eq_inv_mul, inv_pow, mul_const, pow_succ, squeeze_zero, tendsto_pow_atTop_nhds_zero_of_lt_one, zero_mul
-/
lemma tendsto_dist_agmSequences_atTop_zero :
    Tendsto (fun n => dist (agmSequences x y n).1 (agmSequences x y n).2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => dist_nonneg) dist_agmSequences_fst_snd
  conv =>
    rw [← zero_mul (dist x y / 2)]
    enter [1, n]
    rw [pow_succ']; rw [← div_div]; rw [div_eq_inv_mul]; rw [← inv_pow]
  exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _

/--
Definition of `agm` / `agm` 的定义

English:
definition agm
  signature: (x y : Real>=0)
  body: ⨅ n, (agmSequences x y n).2

中文:
定义 agm
  签名: (x y : 实数>=0)
  定义体: ⨅ n, (agmSequences x y n).2

Depends on / 依赖: agmSequences
-/
noncomputable def agm (x y : Real>=0) : Real>=0 :=
  ⨅ n, (agmSequences x y n).2

/--
lemma `agm_comm` / 引理 `agm_comm`

English:
lemma agm_comm
  statement: agm x y = agm y x
  proof: by
  unfold agm
  conv_rhs =>
    enter [1, n]
    rw [agmSequences_comm]

中文:
引理 agm_comm
  结论: agm x y = agm y x
  证明: by
  unfold agm
  conv_rhs =>
    enter [1, n]
    rw [agmSequences_comm]

Depends on / 依赖: agmSequences_comm, conv_rhs
-/
lemma agm_comm : agm x y = agm y x := by
  unfold agm
  conv_rhs =>
    enter [1, n]
    rw [agmSequences_comm]

/--
lemma `agm_eq_ciInf` / 引理 `agm_eq_ciInf`

English:
lemma agm_eq_ciInf
  statement: agm x y = ⨅ n, (agmSequences x y n).2
  proof: rfl

中文:
引理 agm_eq_ciInf
  结论: agm x y = ⨅ n, (agmSequences x y n).2
  证明: rfl
-/
lemma agm_eq_ciInf : agm x y = ⨅ n, (agmSequences x y n).2 := rfl

/--
lemma `tendsto_agmSequences_snd_agm` / 引理 `tendsto_agmSequences_snd_agm`

English:
lemma tendsto_agmSequences_snd_agm
  statement: Tendsto (fun n => (agmSequences x y n).2) atTop (𝓝 (agm x y))
  proof: tendsto_atTop_ciInf agmSequences_snd_antitone (OrderBot.bddBelow _)

中文:
引理 tendsto_agmSequences_snd_agm
  结论: 收敛 (fun n => (agmSequences x y n).2) atTop (𝓝 (agm x y))
  证明: tendsto_atTop_ciInf agmSequences_snd_antitone (OrderBot.bddBelow _)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, agmSequences_snd_antitone, bddBelow, tendsto_atTop_ciInf
-/
lemma tendsto_agmSequences_snd_agm : Tendsto (fun n => (agmSequences x y n).2) atTop (𝓝 (agm x y)) :=
  tendsto_atTop_ciInf agmSequences_snd_antitone (OrderBot.bddBelow _)

/--
lemma `agm_le_agmSequences_snd` / 引理 `agm_le_agmSequences_snd`

English:
lemma agm_le_agmSequences_snd
  given: (n : Nat)
  statement: agm x y <= (agmSequences x y n).2
  proof: ciInf_le' _ n

中文:
引理 agm_le_agmSequences_snd
  条件: (n : 自然数)
  结论: agm x y <= (agmSequences x y n).2
  证明: ciInf_le' _ n

Depends on / 依赖: ciInf_le
-/
lemma agm_le_agmSequences_snd (n : Nat) : agm x y <= (agmSequences x y n).2 := ciInf_le' _ n

/--
lemma `agm_le_max` / 引理 `agm_le_max`

English:
lemma agm_le_max
  statement: agm x y <= max x y
  proof: by
  wlog h : x <= y generalizing x y
  · simpa [agm_comm, max_comm] using this (not_le.mp h).le
  rw [max_eq_right h]
  apply (agm_le_agmSequences_snd 0).trans
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).2

中文:
引理 agm_le_max
  结论: agm x y <= 最大值 x y
  证明: by
  wlog h : x <= y generalizing x y
  · simpa [agm_comm, max_comm] using this (not_le.mp h).le
  rw [max_eq_right h]
  apply (agm_le_agmSequences_snd 0).trans
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).2

Depends on / 依赖: agmSequences_zero, agm_comm, agm_le_agmSequences_snd, generalizing, le_gm_and_am_le, max_comm, max_eq_right, not_le, not_le.mp
-/
lemma agm_le_max : agm x y <= max x y := by
  wlog h : x <= y generalizing x y
  · simpa [agm_comm, max_comm] using this (not_le.mp h).le
  rw [max_eq_right h]
  apply (agm_le_agmSequences_snd 0).trans
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).2

/--
lemma `bddAbove_range_agmSequences_fst` / 引理 `bddAbove_range_agmSequences_fst`

English:
lemma bddAbove_range_agmSequences_fst
  statement: BddAbove (Set.range fun n => (agmSequences x y n).1)
  proof: by
  rw [bddAbove_def]
  use (agmSequences x y 0).2
  simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ => agmSequences_fst_le_snd ..

中文:
引理 bddAbove_range_agmSequences_fst
  结论: BddAbove (集合.range fun n => (agmSequences x y n).1)
  证明: by
  rw [bddAbove_def]
  use (agmSequences x y 0).2
  simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ => agmSequences_fst_le_snd ..

Depends on / 依赖: Set.mem_range, agmSequences, agmSequences_fst_le_snd, bddAbove_def, forall_apply_eq_imp_iff, forall_exists_index, mem_range, simp_rw
-/
lemma bddAbove_range_agmSequences_fst : BddAbove (Set.range fun n => (agmSequences x y n).1) := by
  rw [bddAbove_def]
  use (agmSequences x y 0).2
  simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun _ => agmSequences_fst_le_snd ..

/--
lemma `agm_eq_ciSup` / 引理 `agm_eq_ciSup`

English:
lemma agm_eq_ciSup
  statement: agm x y = ⨆ n, (agmSequences x y n).1
  proof: by
  refine tendsto_nhds_unique (tendsto_agmSequences_snd_agm.congr_dist ?_)
    (tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst)
  conv =>
    enter [1, n]
    rw [dist_comm]
  exact tendsto_dist_agmSequences_atTop_zero

中文:
引理 agm_eq_ciSup
  结论: agm x y = ⨆ n, (agmSequences x y n).1
  证明: by
  refine tendsto_nhds_unique (tendsto_agmSequences_snd_agm.congr_dist ?_)
    (tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst)
  conv =>
    enter [1, n]
    rw [dist_comm]
  exact tendsto_dist_agmSequences_atTop_zero

Depends on / 依赖: agmSequences_fst_monotone, bddAbove_range_agmSequences_fst, congr_dist, dist_comm, tendsto_agmSequences_snd_agm, tendsto_agmSequences_snd_agm.congr_dist, tendsto_atTop_ciSup, tendsto_dist_agmSequences_atTop_zero, tendsto_nhds_unique
-/
lemma agm_eq_ciSup : agm x y = ⨆ n, (agmSequences x y n).1 := by
  refine tendsto_nhds_unique (tendsto_agmSequences_snd_agm.congr_dist ?_)
    (tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst)
  conv =>
    enter [1, n]
    rw [dist_comm]
  exact tendsto_dist_agmSequences_atTop_zero

/--
lemma `tendsto_agmSequences_fst_agm` / 引理 `tendsto_agmSequences_fst_agm`

English:
lemma tendsto_agmSequences_fst_agm
  proof: by
  rw [agm_eq_ciSup]
  exact tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst

中文:
引理 tendsto_agmSequences_fst_agm
  证明: by
  rw [agm_eq_ciSup]
  exact tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst

Depends on / 依赖: agmSequences_fst_monotone, agm_eq_ciSup, bddAbove_range_agmSequences_fst, tendsto_atTop_ciSup
-/
lemma tendsto_agmSequences_fst_agm :
    Tendsto (fun n => (agmSequences x y n).1) atTop (𝓝 (agm x y)) := by
  rw [agm_eq_ciSup]
  exact tendsto_atTop_ciSup agmSequences_fst_monotone bddAbove_range_agmSequences_fst

/--
lemma `agmSequences_fst_le_agm` / 引理 `agmSequences_fst_le_agm`

English:
lemma agmSequences_fst_le_agm
  given: (n : Nat)
  statement: (agmSequences x y n).1 <= agm x y
  proof: by
  rw [agm_eq_ciSup]
  exact le_ciSup bddAbove_range_agmSequences_fst _

中文:
引理 agmSequences_fst_le_agm
  条件: (n : 自然数)
  结论: (agmSequences x y n).1 <= agm x y
  证明: by
  rw [agm_eq_ciSup]
  exact le_ciSup bddAbove_range_agmSequences_fst _

Depends on / 依赖: agm_eq_ciSup, bddAbove_range_agmSequences_fst, le_ciSup
-/
lemma agmSequences_fst_le_agm (n : Nat) : (agmSequences x y n).1 <= agm x y := by
  rw [agm_eq_ciSup]
  exact le_ciSup bddAbove_range_agmSequences_fst _

/--
lemma `min_le_agm` / 引理 `min_le_agm`

English:
lemma min_le_agm
  statement: min x y <= agm x y
  proof: by
  wlog h : x <= y generalizing x y
  · simpa [agm_comm, min_comm] using this (not_le.mp h).le
  rw [min_eq_left h]
  refine le_trans ?_ (agmSequences_fst_le_agm 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).1

@[simp]

中文:
引理 min_le_agm
  结论: 最小值 x y <= agm x y
  证明: by
  wlog h : x <= y generalizing x y
  · simpa [agm_comm, min_comm] using this (not_le.mp h).le
  rw [min_eq_left h]
  refine le_trans ?_ (agmSequences_fst_le_agm 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).1

@[simp]

Depends on / 依赖: agmSequences_fst_le_agm, agmSequences_zero, agm_comm, generalizing, le_gm_and_am_le, le_trans, min_comm, min_eq_left, not_le, not_le.mp
-/
lemma min_le_agm : min x y <= agm x y := by
  wlog h : x <= y generalizing x y
  · simpa [agm_comm, min_comm] using this (not_le.mp h).le
  rw [min_eq_left h]
  refine le_trans ?_ (agmSequences_fst_le_agm 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h).1

@[simp]
/--
lemma `agm_self` / 引理 `agm_self`

English:
lemma agm_self
  statement: agm x x = x
  proof: by
  apply le_antisymm
  · nth_rw 3 [← max_self x]
    exact agm_le_max
  · nth_rw 1 [← min_self x]
    exact min_le_agm

@[simp]

中文:
引理 agm_self
  结论: agm x x = x
  证明: by
  apply le_antisymm
  · nth_rw 3 [← max_self x]
    exact agm_le_max
  · nth_rw 1 [← min_self x]
    exact min_le_agm

@[simp]

Depends on / 依赖: agm_le_max, le_antisymm, max_self, min_le_agm, min_self, nth_rw
-/
lemma agm_self : agm x x = x := by
  apply le_antisymm
  · nth_rw 3 [← max_self x]
    exact agm_le_max
  · nth_rw 1 [← min_self x]
    exact min_le_agm

@[simp]
/--
lemma `agm_zero_left` / 引理 `agm_zero_left`

English:
lemma agm_zero_left
  statement: agm 0 y = 0
  proof: by
  suffices forall n, (agmSequences 0 y n).1 = 0 by simp [agm_eq_ciSup, this]
  intro n
  induction n with
  | zero => simp [agmSequences]
  | succ n ih =>
    rw [agmSequences_succ']; rw [ih]; rw [zero_mul]; rw [sqrt_zero]

@[simp]

中文:
引理 agm_zero_left
  结论: agm 0 y = 0
  证明: by
  suffices forall n, (agmSequences 0 y n).1 = 0 by simp [agm_eq_ciSup, this]
  intro n
  induction n with
  | zero => simp [agmSequences]
  | succ n ih =>
    rw [agmSequences_succ']; rw [ih]; rw [zero_mul]; rw [sqrt_zero]

@[simp]

Depends on / 依赖: agmSequences, agmSequences_succ, agm_eq_ciSup, isRepresentable_comp_uliftFunctor_iff, isRepresentable_comp_uliftFunctor_iff.mpr, sqrt_zero, zero_mul
-/
lemma agm_zero_left : agm 0 y = 0 := by
  suffices forall n, (agmSequences 0 y n).1 = 0 by simp [agm_eq_ciSup, this]
  intro n
  induction n with
  | zero => simp [agmSequences]
  | succ n ih =>
    rw [agmSequences_succ']; rw [ih]; rw [zero_mul]; rw [sqrt_zero]

@[simp]
/--
lemma `agm_zero_right` / 引理 `agm_zero_right`

English:
lemma agm_zero_right
  statement: agm x 0 = 0
  proof: by
  rw [agm_comm]; rw [agm_zero_left]

中文:
引理 agm_zero_right
  结论: agm x 0 = 0
  证明: by
  rw [agm_comm]; rw [agm_zero_left]

Depends on / 依赖: agm_comm, agm_zero_left, isCorepresentable_comp_uliftFunctor_iff, isCorepresentable_comp_uliftFunctor_iff.mpr
-/
lemma agm_zero_right : agm x 0 = 0 := by
  rw [agm_comm]; rw [agm_zero_left]

/--
lemma `agm_pos` / 引理 `agm_pos`

English:
lemma agm_pos
  given: (hx : 0 < x) (hy : 0 < y)
  statement: 0 < agm x y
  proof: (lt_min hx hy).trans_le min_le_agm

中文:
引理 agm_pos
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: 0 < agm x y
  证明: (lt_min hx hy).trans_le min_le_agm

Depends on / 依赖: lt_min, min_le_agm, trans_le
-/
lemma agm_pos (hx : 0 < x) (hy : 0 < y) : 0 < agm x y := (lt_min hx hy).trans_le min_le_agm

/--
lemma `agm_eq_agm_agmSequences_fst_agmSequences_snd` / 引理 `agm_eq_agm_agmSequences_fst_agmSequences_snd`

English:
lemma agm_eq_agm_agmSequences_fst_agmSequences_snd
  given: (n : Nat)
  proof: by
  refine tendsto_nhds_unique ?_ tendsto_agmSequences_snd_agm
  have key := @tendsto_agmSequences_snd_agm x y
  rw [← tendsto_add_atTop_iff_nat (n + 1)] at key
  convert! key using 2 with m
  simp_rw [agmSequences, Prod.mk.eta, ← iterate_add_apply, add_right_comm]

中文:
引理 agm_eq_agm_agmSequences_fst_agmSequences_snd
  条件: (n : 自然数)
  证明: by
  refine tendsto_nhds_unique ?_ tendsto_agmSequences_snd_agm
  have key := @tendsto_agmSequences_snd_agm x y
  rw [← tendsto_add_atTop_iff_nat (n + 1)] at key
  convert! key using 2 with m
  simp_rw [agmSequences, Prod.mk.eta, ← iterate_add_apply, add_right_comm]

Depends on / 依赖: Prod.mk.eta, add_right_comm, agmSequences, convert, iterate_add_apply, simp_rw, tendsto_add_atTop_iff_nat, tendsto_agmSequences_snd_agm, tendsto_nhds_unique
-/
lemma agm_eq_agm_agmSequences_fst_agmSequences_snd (n : Nat) :
    agm x y = agm (agmSequences x y n).1 (agmSequences x y n).2 := by
  refine tendsto_nhds_unique ?_ tendsto_agmSequences_snd_agm
  have key := @tendsto_agmSequences_snd_agm x y
  rw [← tendsto_add_atTop_iff_nat (n + 1)] at key
  convert! key using 2 with m
  simp_rw [agmSequences, Prod.mk.eta, ← iterate_add_apply, add_right_comm]

/--
lemma `agm_eq_agm_gm_am` / 引理 `agm_eq_agm_gm_am`

English:
lemma agm_eq_agm_gm_am
  statement: agm x y = agm (sqrt (x * y)) ((x + y) / 2)
  proof: by
  simpa using agm_eq_agm_agmSequences_fst_agmSequences_snd 0

中文:
引理 agm_eq_agm_gm_am
  结论: agm x y = agm (sqrt (x * y)) ((x + y) / 2)
  证明: by
  simpa using agm_eq_agm_agmSequences_fst_agmSequences_snd 0

Depends on / 依赖: agm_eq_agm_agmSequences_fst_agmSequences_snd
-/
lemma agm_eq_agm_gm_am : agm x y = agm (sqrt (x * y)) ((x + y) / 2) := by
  simpa using agm_eq_agm_agmSequences_fst_agmSequences_snd 0

/--
lemma `agmSequences_fst_lt_agm_of_pos_of_ne` / 引理 `agmSequences_fst_lt_agm_of_pos_of_ne`

English:
lemma agmSequences_fst_lt_agm_of_pos_of_ne
  given: (hx : 0 < x) (hy : 0 < y) (hn : x != y) (n : Nat)
  proof: by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (?_ : p < sqrt (p * q)).trans_le (agmSequences_fst_le_agm 0)
  have ppos : 0 < p :=
    (show 0 < sqrt (x * y) by positivity).trans_le (agmSequences_fst_monotone zero_le)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 1 [← mul_self_sqrt p, sqrt_mul]
  gcongr

中文:
引理 agmSequences_fst_lt_agm_of_pos_of_ne
  条件: (hx : 0 < x) (hy : 0 < y) (hn : x != y) (n : 自然数)
  证明: by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (?_ : p < sqrt (p * q)).trans_le (agmSequences_fst_le_agm 0)
  have ppos : 0 < p :=
    (show 0 < sqrt (x * y) by positivity).trans_le (agmSequences_fst_monotone zero_le)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 1 [← mul_self_sqrt p, sqrt_mul]
  gcongr

Depends on / 依赖: agmSequences, agmSequences_fst_le_agm, agmSequences_fst_lt_snd_of_ne, agmSequences_fst_monotone, agm_eq_agm_agmSequences_fst_agmSequences_snd, mul_self_sqrt, nth_rw, sqrt_mul, trans_le, zero_le
-/
lemma agmSequences_fst_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x != y) (n : Nat) :
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

/--
lemma `agm_lt_agmSequences_snd_of_ne` / 引理 `agm_lt_agmSequences_snd_of_ne`

English:
lemma agm_lt_agmSequences_snd_of_ne
  given: (hn : x != y) (n : Nat)
  statement: agm x y < (agmSequences x y n).2
  proof: by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (agm_le_agmSequences_snd 0).trans_lt (?_ : (p + q) / 2 < q)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 2 [← add_halves q]
  rw [add_div]
  gcongr

中文:
引理 agm_lt_agmSequences_snd_of_ne
  条件: (hn : x != y) (n : 自然数)
  结论: agm x y < (agmSequences x y n).2
  证明: by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (agm_le_agmSequences_snd 0).trans_lt (?_ : (p + q) / 2 < q)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 2 [← add_halves q]
  rw [add_div]
  gcongr

Depends on / 依赖: add_div, add_halves, agmSequences, agmSequences_fst_lt_snd_of_ne, agm_eq_agm_agmSequences_fst_agmSequences_snd, agm_le_agmSequences_snd, nth_rw, trans_lt
-/
lemma agm_lt_agmSequences_snd_of_ne (hn : x != y) (n : Nat) : agm x y < (agmSequences x y n).2 := by
  rw [agm_eq_agm_agmSequences_fst_agmSequences_snd n]
  set p := (agmSequences x y n).1
  set q := (agmSequences x y n).2
  apply (agm_le_agmSequences_snd 0).trans_lt (?_ : (p + q) / 2 < q)
  have plq : p < q := agmSequences_fst_lt_snd_of_ne hn ..
  nth_rw 2 [← add_halves q]
  rw [add_div]
  gcongr

/--
lemma `min_lt_agm_of_pos_of_ne` / 引理 `min_lt_agm_of_pos_of_ne`

English:
lemma min_lt_agm_of_pos_of_ne
  given: (hx : 0 < x) (hy : 0 < y) (hn : x != y)
  statement: min x y < agm x y
  proof: by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, min_comm] using this hy hx hn.symm (hn.gt_or_lt.resolve_right h)
  rw [min_eq_left h.le]
  refine lt_of_le_of_lt ?_ (agmSequences_fst_lt_agm_of_pos_of_ne hx hy hn 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).1

中文:
引理 min_lt_agm_of_pos_of_ne
  条件: (hx : 0 < x) (hy : 0 < y) (hn : x != y)
  结论: 最小值 x y < agm x y
  证明: by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, min_comm] using this hy hx hn.symm (hn.gt_or_lt.resolve_right h)
  rw [min_eq_left h.le]
  refine lt_of_le_of_lt ?_ (agmSequences_fst_lt_agm_of_pos_of_ne hx hy hn 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).1

Depends on / 依赖: agmSequences_fst_lt_agm_of_pos_of_ne, agmSequences_zero, agm_comm, generalizing, gt_or_lt, h.le, hn.gt_or_lt.resolve_right, hn.symm, le_gm_and_am_le, lt_of_le_of_lt, min_comm, min_eq_left, resolve_right
-/
lemma min_lt_agm_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (hn : x != y) : min x y < agm x y := by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, min_comm] using this hy hx hn.symm (hn.gt_or_lt.resolve_right h)
  rw [min_eq_left h.le]
  refine lt_of_le_of_lt ?_ (agmSequences_fst_lt_agm_of_pos_of_ne hx hy hn 0)
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).1

/--
lemma `agm_lt_max_of_ne` / 引理 `agm_lt_max_of_ne`

English:
lemma agm_lt_max_of_ne
  given: (hn : x != y)
  statement: agm x y < max x y
  proof: by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, max_comm] using this hn.symm (hn.gt_or_lt.resolve_right h)
  rw [max_eq_right h.le]
  apply (agm_lt_agmSequences_snd_of_ne hn 0).trans_le
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).2

中文:
引理 agm_lt_max_of_ne
  条件: (hn : x != y)
  结论: agm x y < 最大值 x y
  证明: by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, max_comm] using this hn.symm (hn.gt_or_lt.resolve_right h)
  rw [max_eq_right h.le]
  apply (agm_lt_agmSequences_snd_of_ne hn 0).trans_le
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).2

Depends on / 依赖: agmSequences_zero, agm_comm, agm_lt_agmSequences_snd_of_ne, generalizing, gt_or_lt, h.le, hn.gt_or_lt.resolve_right, hn.symm, le_gm_and_am_le, max_comm, max_eq_right, resolve_right, trans_le
-/
lemma agm_lt_max_of_ne (hn : x != y) : agm x y < max x y := by
  wlog h : x < y generalizing x y
  · simpa [agm_comm, max_comm] using this hn.symm (hn.gt_or_lt.resolve_right h)
  rw [max_eq_right h.le]
  apply (agm_lt_agmSequences_snd_of_ne hn 0).trans_le
  rw [agmSequences_zero]
  exact (le_gm_and_am_le h.le).2

/--
lemma `agm_mul_distrib` / 引理 `agm_mul_distrib`

English:
lemma agm_mul_distrib
  given: {k : Real>=0}
  statement: agm (k * x) (k * y) = k * agm x y
  proof: by
  simp_rw [agm, mul_iInf]
  congr! with n
  induction n generalizing x y with
  | zero => simp [← mul_div_assoc, mul_add]
  | succ n ih =>
    rw [agmSequences_succ]; rw [← mul_add]; rw [mul_div_assoc]; rw [mul_mul_mul_comm]; rw [← sq]; rw [sqrt_mul]; rw [sqrt_sq]; rw [ih]; rw [agmSequences_succ]

中文:
引理 agm_mul_distrib
  条件: {k : 实数>=0}
  结论: agm (k * x) (k * y) = k * agm x y
  证明: by
  simp_rw [agm, mul_iInf]
  congr! with n
  induction n generalizing x y with
  | zero => simp [← mul_div_assoc, mul_add]
  | succ n ih =>
    rw [agmSequences_succ]; rw [← mul_add]; rw [mul_div_assoc]; rw [mul_mul_mul_comm]; rw [← sq]; rw [sqrt_mul]; rw [sqrt_sq]; rw [ih]; rw [agmSequences_succ]

Depends on / 依赖: agmSequences_succ, generalizing, mul_add, mul_div_assoc, mul_iInf, mul_mul_mul_comm, simp_rw, sqrt_mul, sqrt_sq
-/
lemma agm_mul_distrib {k : Real>=0} : agm (k * x) (k * y) = k * agm x y := by
  simp_rw [agm, mul_iInf]
  congr! with n
  induction n generalizing x y with
  | zero => simp [← mul_div_assoc, mul_add]
  | succ n ih =>
    rw [agmSequences_succ]; rw [← mul_add]; rw [mul_div_assoc]; rw [mul_mul_mul_comm]; rw [← sq]; rw [sqrt_mul]; rw [sqrt_sq]; rw [ih]; rw [agmSequences_succ]

end NNReal
