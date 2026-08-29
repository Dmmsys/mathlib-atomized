/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
public import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
public import Mathlib.Data.Rat.Floor

/-!
# Termination of Continued Fraction Computations (`GenContFract.of`)

## Summary
We show that the continued fraction for a value `v`, as defined in
`Mathlib/Algebra/ContinuedFractions/Basic.lean`, terminates if and only if `v` corresponds to a
rational number, that is `↑v = q` for some `q : ℚ`.

## Main Theorems

- `GenContFract.coe_of_rat_eq` shows that
  `GenContFract.of v = GenContFract.of q` for `v : α` given that `↑v = q` and `q : ℚ`.
- `GenContFract.terminates_iff_rat` shows that
  `GenContFract.of v` terminates if and only if `↑v = q` for some `q : ℚ`.

## Tags

rational, continued fraction, termination
-/

public section


namespace GenContFract

open GenContFract (of)

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K]

/-
We will have to constantly coerce along our structures in the following proofs using their provided
map functions.
-/
attribute [local simp] Pair.map IntFractPair.mapFr

section RatOfTerminates

/-!
### Terminating Continued Fractions Are Rational

We want to show that the computation of a continued fraction `GenContFract.of v`
terminates if and only if `v ∈ ℚ`. In this section, we show the implication from left to right.

We first show that every finite convergent corresponds to a rational number `q` and then use the
finite correctness proof (`of_correctness_of_terminates`) of `GenContFract.of` to show that
`v = ↑q`.
-/


variable (v : K) (n : Nat)

nonrec theorem exists_gcf_pair_rat_eq_of_nth_contsAux :
    exists conts : Pair Rat, (of v).contsAux n = (conts.map (↑) : Pair K) :=
  Nat.strong_induction_on n
    (by
      clear n
      let g := of v
      intro n IH
      rcases n with (_ | _ | n)
      -- n = 0
      · suffices exists gp : Pair Rat, Pair.mk (1 : K) 0 = gp.map (↑) by simpa [contsAux]
        use Pair.mk 1 0
        simp
      -- n = 1
      · suffices exists conts : Pair Rat, Pair.mk g.h 1 = conts.map (↑) by simpa [contsAux]
        use Pair.mk ⌊v⌋ 1
        simp [g]
      -- 2 ≤ n
· obtain ⟨pred_conts, pred_conts_eq⟩ := IH (n + 1) lt_add_one (n + 1)
        -- invoke the IH
        rcases s_ppred_nth_eq : g.s.get? n with gp_n | gp_n
        -- option.none
        · use pred_conts
          have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
            contsAux_stable_of_terminated (n + 1).le_succ s_ppred_nth_eq
          simp only [g, this, pred_conts_eq]
        -- option.some
        · -- invoke the IH a second time
          obtain ⟨ppred_conts, ppred_conts_eq⟩ :=
IH n lt_of_le_of_lt n.le_succ lt_add_one n + 1
          obtain ⟨a_eq_one, z, b_eq_z⟩ : gp_n.a = 1 ∧ exists z : Int, gp_n.b = (z : K) :=
            of_partNum_eq_one_and_exists_int_partDen_eq s_ppred_nth_eq
          -- finally, unfold the recurrence to obtain the required rational value.
          simp only [g, a_eq_one, b_eq_z,
            contsAux_recurrence s_ppred_nth_eq ppred_conts_eq pred_conts_eq]
          use nextConts 1 (z : Rat) ppred_conts pred_conts
          cases ppred_conts; cases pred_conts
          simp [nextConts, nextNum, nextDen])

/--
theorem `exists_gcf_pair_rat_eq_nth_conts` / 定理 `exists_gcf_pair_rat_eq_nth_conts`

English:
theorem exists_gcf_pair_rat_eq_nth_conts
  proof: by
rw [nth_cont_eq_succ_nth_contAux]; exact exists_gcf_pair_rat_eq_of_nth_contsAux v n + 1

中文:
定理 存在_gcf_pair_rat_eq_nth_conts
  证明: by
rw [nth_cont_eq_succ_nth_contAux]; exact exists_gcf_pair_rat_eq_of_nth_contsAux v n + 1

Depends on / 依赖: exists_gcf_pair_rat_eq_of_nth_contsAux, nth_cont_eq_succ_nth_contAux
-/
theorem exists_gcf_pair_rat_eq_nth_conts :
    exists conts : Pair Rat, (of v).conts n = (conts.map (↑) : Pair K) := by
rw [nth_cont_eq_succ_nth_contAux]; exact exists_gcf_pair_rat_eq_of_nth_contsAux v n + 1

/--
theorem `exists_rat_eq_nth_num` / 定理 `exists_rat_eq_nth_num`

English:
theorem exists_rat_eq_nth_num
  statement: exists q : Rat, (of v).nums n = (q : K)
  proof: by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
  use a
  simp [num_eq_conts_a, nth_cont_eq]

中文:
定理 存在_rat_eq_nth_num
  结论: 存在 q : 有理数, (of v).nums n = (q : K)
  证明: by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
  use a
  simp [num_eq_conts_a, nth_cont_eq]

Depends on / 依赖: exists_gcf_pair_rat_eq_nth_conts, nth_cont_eq, num_eq_conts_a
-/
theorem exists_rat_eq_nth_num : exists q : Rat, (of v).nums n = (q : K) := by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
  use a
  simp [num_eq_conts_a, nth_cont_eq]

/--
theorem `exists_rat_eq_nth_den` / 定理 `exists_rat_eq_nth_den`

English:
theorem exists_rat_eq_nth_den
  statement: exists q : Rat, (of v).dens n = (q : K)
  proof: by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
  use b
  simp [den_eq_conts_b, nth_cont_eq]

中文:
定理 存在_rat_eq_nth_den
  结论: 存在 q : 有理数, (of v).dens n = (q : K)
  证明: by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
  use b
  simp [den_eq_conts_b, nth_cont_eq]

Depends on / 依赖: den_eq_conts_b, exists_gcf_pair_rat_eq_nth_conts, nth_cont_eq
-/
theorem exists_rat_eq_nth_den : exists q : Rat, (of v).dens n = (q : K) := by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
  use b
  simp [den_eq_conts_b, nth_cont_eq]

/--
theorem `exists_rat_eq_nth_conv` / 定理 `exists_rat_eq_nth_conv`

English:
theorem exists_rat_eq_nth_conv
  statement: exists q : Rat, (of v).convs n = (q : K)
  proof: by
  rcases exists_rat_eq_nth_num v n with ⟨Aₙ, nth_num_eq⟩
  rcases exists_rat_eq_nth_den v n with ⟨Bₙ, nth_den_eq⟩
  use Aₙ / Bₙ
  simp [nth_num_eq, nth_den_eq, conv_eq_num_div_den]

中文:
定理 存在_rat_eq_nth_conv
  结论: 存在 q : 有理数, (of v).convs n = (q : K)
  证明: by
  rcases exists_rat_eq_nth_num v n with ⟨Aₙ, nth_num_eq⟩
  rcases exists_rat_eq_nth_den v n with ⟨Bₙ, nth_den_eq⟩
  use Aₙ / Bₙ
  simp [nth_num_eq, nth_den_eq, conv_eq_num_div_den]

Depends on / 依赖: conv_eq_num_div_den, exists_rat_eq_nth_den, exists_rat_eq_nth_num, nth_den_eq, nth_num_eq
-/
theorem exists_rat_eq_nth_conv : exists q : Rat, (of v).convs n = (q : K) := by
  rcases exists_rat_eq_nth_num v n with ⟨Aₙ, nth_num_eq⟩
  rcases exists_rat_eq_nth_den v n with ⟨Bₙ, nth_den_eq⟩
  use Aₙ / Bₙ
  simp [nth_num_eq, nth_den_eq, conv_eq_num_div_den]

variable {v}

/--
theorem `exists_rat_eq_of_terminates` / 定理 `exists_rat_eq_of_terminates`

English:
theorem exists_rat_eq_of_terminates
  given: (terminates : (of v).Terminates)
  statement: exists q : Rat, v = ↑q
  proof: by
  obtain ⟨n, v_eq_conv⟩ : exists n, v = (of v).convs n := of_correctness_of_terminates terminates
  obtain ⟨q, conv_eq_q⟩ : exists q : Rat, (of v).convs n = (↑q : K) := exists_rat_eq_nth_conv v n
  have : v = (↑q : K) := Eq.trans v_eq_conv conv_eq_q
  use q, this

中文:
定理 存在_rat_eq_of_terminates
  条件: (terminates : (of v).Terminates)
  结论: 存在 q : 有理数, v = ↑q
  证明: by
  obtain ⟨n, v_eq_conv⟩ : exists n, v = (of v).convs n := of_correctness_of_terminates terminates
  obtain ⟨q, conv_eq_q⟩ : exists q : Rat, (of v).convs n = (↑q : K) := exists_rat_eq_nth_conv v n
  have : v = (↑q : K) := Eq.trans v_eq_conv conv_eq_q
  use q, this

Depends on / 依赖: Eq.trans, conv_eq_q, exists_rat_eq_nth_conv, of_correctness_of_terminates, terminates, v_eq_conv
-/
theorem exists_rat_eq_of_terminates (terminates : (of v).Terminates) : exists q : Rat, v = ↑q := by
  obtain ⟨n, v_eq_conv⟩ : exists n, v = (of v).convs n := of_correctness_of_terminates terminates
  obtain ⟨q, conv_eq_q⟩ : exists q : Rat, (of v).convs n = (↑q : K) := exists_rat_eq_nth_conv v n
  have : v = (↑q : K) := Eq.trans v_eq_conv conv_eq_q
  use q, this

end RatOfTerminates

section RatTranslation

/-!
### Technical Translation Lemmas

Before we can show that the continued fraction of a rational number terminates, we have to prove
some technical translation lemmas. More precisely, in this section, we show that, given a rational
number `q : ℚ` and value `v : K` with `v = ↑q`, the continued fraction of `q` and `v` coincide.
In particular, we show that
```lean
    (↑(GenContFract.of q : GenContFract ℚ) : GenContFract K) = GenContFract.of v
```
in `GenContFract.coe_of_rat_eq`.

To do this, we proceed bottom-up, showing the correspondence between the basic functions involved in
the Computation first and then lift the results step-by-step.
-/


-- The lifting works for arbitrary linear ordered fields with a floor function.
variable [IsStrictOrderedRing K] {v : K} {q : Rat}

/-! First, we show the correspondence for the very basic functions in
`GenContFract.IntFractPair`. -/


namespace IntFractPair

/--
theorem `coe_of_rat_eq` / 定理 `coe_of_rat_eq`

English:
theorem coe_of_rat_eq
  given: (v_eq_q : v = (↑q : K))
  proof: by
  simp [IntFractPair.of, v_eq_q]

中文:
定理 coe_of_rat_eq
  条件: (v_eq_q : v = (↑q : K))
  证明: by
  simp [IntFractPair.of, v_eq_q]

Depends on / 依赖: IntFractPair, IntFractPair.of, v_eq_q
-/
theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    ((IntFractPair.of q).mapFr (↑) : IntFractPair K) = IntFractPair.of v := by
  simp [IntFractPair.of, v_eq_q]

/--
theorem `coe_stream_nth_rat_eq` / 定理 `coe_stream_nth_rat_eq`

English:
theorem coe_stream_nth_rat_eq
  given: (v_eq_q : v = (↑q : K)) (n : Nat)
  proof: by
  induction n with
  | zero =>
    simp only [IntFractPair.stream, Option.map_some, coe_of_rat_eq v_eq_q]
  | succ n IH =>
    rw [v_eq_q] at IH
    cases stream_q_nth_eq : IntFractPair.stream q n with
    | none => simp [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq]
    | some ifp_n =>


中文:
定理 coe_stream_nth_rat_eq
  条件: (v_eq_q : v = (↑q : K)) (n : 自然数)
  证明: by
  induction n with
  | zero =>
    simp only [IntFractPair.stream, Option.map_some, coe_of_rat_eq v_eq_q]
  | succ n IH =>
    rw [v_eq_q] at IH
    cases stream_q_nth_eq : IntFractPair.stream q n with
    | none => simp [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq]
    | some ifp_n =>


Depends on / 依赖: Decidable, Decidable.em, IH.symm, IntFractPair, IntFractPair.stream, Option.map_some, coe_of_fr, coe_of_rat_eq, fr_ne_zero, fr_zero, ifp_n, map_some, stream, stream_q_nth_eq, v_eq_q
-/
theorem coe_stream_nth_rat_eq (v_eq_q : v = (↑q : K)) (n : Nat) :
    ((IntFractPair.stream q n).map (mapFr (↑)) : Option <| IntFractPair K) =
      IntFractPair.stream v n := by
  induction n with
  | zero =>
    simp only [IntFractPair.stream, Option.map_some, coe_of_rat_eq v_eq_q]
  | succ n IH =>
    rw [v_eq_q] at IH
    cases stream_q_nth_eq : IntFractPair.stream q n with
    | none => simp [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq]
    | some ifp_n =>
      obtain ⟨b, fr⟩ := ifp_n
      rcases Decidable.em (fr = 0) with fr_zero | fr_ne_zero
      · simp [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_zero]
      · have : (fr : K)⁻¹ = ((fr⁻¹ : Rat) : K) := by norm_cast
        have coe_of_fr := coe_of_rat_eq this
        simpa [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_ne_zero]

/--
theorem `coe_stream'_rat_eq` / 定理 `coe_stream'_rat_eq`

English:
theorem coe_stream'_rat_eq
  given: (v_eq_q : v = (↑q : K))
  proof: by
  funext n; exact IntFractPair.coe_stream_nth_rat_eq v_eq_q n

中文:
定理 coe_stream'_rat_eq
  条件: (v_eq_q : v = (↑q : K))
  证明: by
  funext n; exact IntFractPair.coe_stream_nth_rat_eq v_eq_q n

Depends on / 依赖: IntFractPair, IntFractPair.coe_stream_nth_rat_eq, coe_stream_nth_rat_eq, v_eq_q
-/
theorem coe_stream'_rat_eq (v_eq_q : v = (↑q : K)) :
    ((IntFractPair.stream q).map (Option.map (mapFr (↑))) : Stream' <| Option <| IntFractPair K) =
      IntFractPair.stream v := by
  funext n; exact IntFractPair.coe_stream_nth_rat_eq v_eq_q n

end IntFractPair



/--
theorem `coe_of_h_rat_eq` / 定理 `coe_of_h_rat_eq`

English:
theorem coe_of_h_rat_eq
  given: (v_eq_q : v = (↑q : K))
  statement: (↑((of q).h : Rat) : K) = (of v).h
  proof: by
  simp_all

中文:
定理 coe_of_h_rat_eq
  条件: (v_eq_q : v = (↑q : K))
  结论: (↑((of q).h : 有理数) : K) = (of v).h
  证明: by
  simp_all
-/
theorem coe_of_h_rat_eq (v_eq_q : v = (↑q : K)) : (↑((of q).h : Rat) : K) = (of v).h := by
  simp_all

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_of_s_get?_rat_eq` / 定理 `coe_of_s_get?_rat_eq`

English:
theorem coe_of_s_get?_rat_eq
  given: (v_eq_q : v = (↑q : K)) (n : Nat)
  proof: by
  simp only [of, IntFractPair.seq1, Stream'.Seq.map_get?, Stream'.Seq.get?_tail]
  simp only [Stream'.Seq.get?]
  rw [← IntFractPair.coe_stream'_rat_eq v_eq_q]
  rcases succ_nth_stream_eq : IntFractPair.stream q (n + 1) with (_ | ⟨_, _⟩) <;>
    simp [Stream'.map, Stream'.get, succ_nth_stream_eq]

中文:
定理 coe_of_s_get?_rat_eq
  条件: (v_eq_q : v = (↑q : K)) (n : 自然数)
  证明: by
  simp only [of, IntFractPair.seq1, Stream'.Seq.map_get?, Stream'.Seq.get?_tail]
  simp only [Stream'.Seq.get?]
  rw [← IntFractPair.coe_stream'_rat_eq v_eq_q]
  rcases succ_nth_stream_eq : IntFractPair.stream q (n + 1) with (_ | ⟨_, _⟩) <;>
    simp [Stream'.map, Stream'.get, succ_nth_stream_eq]

Depends on / 依赖: IntFractPair, IntFractPair.coe_stream, IntFractPair.seq1, IntFractPair.stream, Seq.get, Seq.map_get, Stream, _rat_eq, _tail, coe_stream, map_get, stream, succ_nth_stream_eq, v_eq_q
-/
theorem coe_of_s_get?_rat_eq (v_eq_q : v = (↑q : K)) (n : Nat) :
    (((of q).s.get? n).map (Pair.map (↑)) : Option <| Pair K) = (of v).s.get? n := by
  simp only [of, IntFractPair.seq1, Stream'.Seq.map_get?, Stream'.Seq.get?_tail]
  simp only [Stream'.Seq.get?]
  rw [← IntFractPair.coe_stream'_rat_eq v_eq_q]
  rcases succ_nth_stream_eq : IntFractPair.stream q (n + 1) with (_ | ⟨_, _⟩) <;>
    simp [Stream'.map, Stream'.get, succ_nth_stream_eq]

/--
theorem `coe_of_s_rat_eq` / 定理 `coe_of_s_rat_eq`

English:
theorem coe_of_s_rat_eq
  given: (v_eq_q : v = (↑q : K))
  proof: by
  ext n; rw [← coe_of_s_get?_rat_eq v_eq_q]; rfl

中文:
定理 coe_of_s_rat_eq
  条件: (v_eq_q : v = (↑q : K))
  证明: by
  ext n; rw [← coe_of_s_get?_rat_eq v_eq_q]; rfl

Depends on / 依赖: _rat_eq, coe_of_s_get, v_eq_q
-/
theorem coe_of_s_rat_eq (v_eq_q : v = (↑q : K)) :
    ((of q).s.map (Pair.map ((↑))) : Stream'.Seq <| Pair K) = (of v).s := by
  ext n; rw [← coe_of_s_get?_rat_eq v_eq_q]; rfl

/--
theorem `coe_of_rat_eq` / 定理 `coe_of_rat_eq`

English:
theorem coe_of_rat_eq
  given: (v_eq_q : v = (↑q : K))
  proof: by
  rcases gcf_v_eq : of v with ⟨h, s⟩; subst v
  obtain rfl : ↑⌊(q : K)⌋ = h := by injection gcf_v_eq
  simp [coe_of_s_rat_eq rfl, gcf_v_eq]

中文:
定理 coe_of_rat_eq
  条件: (v_eq_q : v = (↑q : K))
  证明: by
  rcases gcf_v_eq : of v with ⟨h, s⟩; subst v
  obtain rfl : ↑⌊(q : K)⌋ = h := by injection gcf_v_eq
  simp [coe_of_s_rat_eq rfl, gcf_v_eq]

Depends on / 依赖: coe_of_s_rat_eq, gcf_v_eq, injection
-/
theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    (⟨(of q).h, (of q).s.map (Pair.map (↑))⟩ : GenContFract K) = of v := by
  rcases gcf_v_eq : of v with ⟨h, s⟩; subst v
  obtain rfl : ↑⌊(q : K)⌋ = h := by injection gcf_v_eq
  simp [coe_of_s_rat_eq rfl, gcf_v_eq]

/--
theorem `of_terminates_iff_of_rat_terminates` / 定理 `of_terminates_iff_of_rat_terminates`

English:
theorem of_terminates_iff_of_rat_terminates
  given: {v : K} {q : Rat} (v_eq_q : v = (q : K))
  proof: by
  refine exists_congr fun n => ?_
  rcases h : (of q).s.get? n <;> grind [Stream'.Seq.TerminatedAt, coe_of_s_get?_rat_eq v_eq_q n]

中文:
定理 of_terminates_iff_of_rat_terminates
  条件: {v : K} {q : 有理数} (v_eq_q : v = (q : K))
  证明: by
  refine exists_congr fun n => ?_
  rcases h : (of q).s.get? n <;> grind [Stream'.Seq.TerminatedAt, coe_of_s_get?_rat_eq v_eq_q n]

Depends on / 依赖: Seq.TerminatedAt, Stream, TerminatedAt, _rat_eq, coe_of_s_get, exists_congr, s.get, v_eq_q
-/
theorem of_terminates_iff_of_rat_terminates {v : K} {q : Rat} (v_eq_q : v = (q : K)) :
    (of v).Terminates ↔ (of q).Terminates := by
  refine exists_congr fun n => ?_
  rcases h : (of q).s.get? n <;> grind [Stream'.Seq.TerminatedAt, coe_of_s_get?_rat_eq v_eq_q n]

end RatTranslation

section TerminatesOfRat

/-!
### Continued Fractions of Rationals Terminate

Finally, we show that the continued fraction of a rational number terminates.

The crucial insight is that, given any `q : ℚ` with `0 < q < 1`, the numerator of `Int.fract q` is
smaller than the numerator of `q`. As the continued fraction computation recursively operates on
the fractional part of a value `v` and `0 ≤ Int.fract v < 1`, we infer that the numerator of the
fractional part in the computation decreases by at least one in each step. As `0 ≤ Int.fract v`,
this process must stop after finite number of steps, and the computation hence terminates.
-/


namespace IntFractPair

variable {q : Rat} {n : Nat}

/--
theorem `of_inv_fr_num_lt_num_of_pos` / 定理 `of_inv_fr_num_lt_num_of_pos`

English:
theorem of_inv_fr_num_lt_num_of_pos
  given: (q_pos : 0 < q)
  statement: (IntFractPair.of q⁻¹).fr.num < q.num
  proof: Rat.fract_inv_num_lt_num_of_pos q_pos

中文:
定理 of_inv_fr_num_lt_num_of_pos
  条件: (q_pos : 0 < q)
  结论: (整数FractPair.of q⁻¹).fr.num < q.num
  证明: Rat.fract_inv_num_lt_num_of_pos q_pos

Depends on / 依赖: Rat.fract_inv_num_lt_num_of_pos, fract_inv_num_lt_num_of_pos, q_pos
-/
theorem of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (IntFractPair.of q⁻¹).fr.num < q.num :=
  Rat.fract_inv_num_lt_num_of_pos q_pos

/--
theorem `stream_succ_nth_fr_num_lt_nth_fr_num_rat` / 定理 `stream_succ_nth_fr_num_lt_nth_fr_num_rat`

English:
theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat
  statement: {ifp_n ifp_succ_n : IntFractPair Rat}
  proof: by
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, IntFractPair.of_eq_ifp_succ_n⟩ :
    exists ifp_n',
      IntFractPair.stream q n = some ifp_n' ∧
        ifp_n'.fr != 0 ∧ IntFractPair.of ifp_n'.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq
  have : ifp_n = ifp_

中文:
定理 stream_succ_nth_fr_num_lt_nth_fr_num_rat
  结论: {ifp_n ifp_succ_n : 整数FractPair 有理数}
  证明: by
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, IntFractPair.of_eq_ifp_succ_n⟩ :
    exists ifp_n',
      IntFractPair.stream q n = some ifp_n' ∧
        ifp_n'.fr != 0 ∧ IntFractPair.of ifp_n'.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq
  have : ifp_n = ifp_

Depends on / 依赖: Eq.trans, IntFractPair, IntFractPair.of, IntFractPair.of_eq_ifp_succ_n, IntFractPair.stream, ifp_n, ifp_n.fr, ifp_n_fract_ne_zero, ifp_succ_n, injection, lt_of_le_of_ne, nth_stream_fr_nonneg_lt_one, of_eq_ifp_succ_n, stream, stream_nth_eq, stream_nth_eq.symm, stream_succ_nth_eq, succ_nth_stream_eq_some_iff, succ_nth_stream_eq_some_iff.mp, zero_le_ifp_n_fract
-/
theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : IntFractPair Rat}
    (stream_nth_eq : IntFractPair.stream q n = some ifp_n)
    (stream_succ_nth_eq : IntFractPair.stream q (n + 1) = some ifp_succ_n) :
    ifp_succ_n.fr.num < ifp_n.fr.num := by
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, IntFractPair.of_eq_ifp_succ_n⟩ :
    exists ifp_n',
      IntFractPair.stream q n = some ifp_n' ∧
        ifp_n'.fr != 0 ∧ IntFractPair.of ifp_n'.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq
  have : ifp_n = ifp_n' := by injection Eq.trans stream_nth_eq.symm stream_nth_eq'
  cases this
  rw [← IntFractPair.of_eq_ifp_succ_n]
  obtain ⟨zero_le_ifp_n_fract, _⟩ := nth_stream_fr_nonneg_lt_one stream_nth_eq
have : 0 < ifp_n.fr := lt_of_le_of_ne zero_le_ifp_n_fract ifp_n_fract_ne_zero.symm
  exact of_inv_fr_num_lt_num_of_pos this

/--
theorem `stream_nth_fr_num_le_fr_num_sub_n_rat` / 定理 `stream_nth_fr_num_le_fr_num_sub_n_rat`

English:
theorem stream_nth_fr_num_le_fr_num_sub_n_rat
  proof: by
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    have : IntFractPair.of q = ifp_zero := by injection stream_zero_eq
    simp [this.symm]
  | succ n IH =>
    intro ifp_succ_n stream_succ_nth_eq
    suffices ifp_succ_n.fr.num + 1 <= (IntFractPair.of q).fr.num - n by
      rw [I

中文:
定理 stream_nth_fr_num_le_fr_num_sub_n_rat
  证明: by
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    have : IntFractPair.of q = ifp_zero := by injection stream_zero_eq
    simp [this.symm]
  | succ n IH =>
    intro ifp_succ_n stream_succ_nth_eq
    suffices ifp_succ_n.fr.num + 1 <= (IntFractPair.of q).fr.num - n by
      rw [I

Depends on / 依赖: Int.natCast_succ, IntFractPair, IntFractPair.of, fr.num, ifp_n, ifp_n.fr.num, ifp_succ_n, ifp_succ_n.fr.num, ifp_zero, injection, le_sub_right_of_add_le, natCast_succ, solve_by_elim, stream_nth_eq, stream_succ_nth_eq, stream_succ_nth_fr_n, stream_zero_eq, sub_add_eq_sub_sub, succ_nth_stream_eq_some_iff, succ_nth_stream_eq_some_iff.mp
-/
theorem stream_nth_fr_num_le_fr_num_sub_n_rat :
    forall {ifp_n : IntFractPair Rat},
      IntFractPair.stream q n = some ifp_n -> ifp_n.fr.num <= (IntFractPair.of q).fr.num - n := by
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    have : IntFractPair.of q = ifp_zero := by injection stream_zero_eq
    simp [this.symm]
  | succ n IH =>
    intro ifp_succ_n stream_succ_nth_eq
    suffices ifp_succ_n.fr.num + 1 <= (IntFractPair.of q).fr.num - n by
      rw [Int.natCast_succ]; rw [sub_add_eq_sub_sub]
      solve_by_elim [le_sub_right_of_add_le]
    rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with ⟨ifp_n, stream_nth_eq, -⟩
    have : ifp_succ_n.fr.num < ifp_n.fr.num :=
      stream_succ_nth_fr_num_lt_nth_fr_num_rat stream_nth_eq stream_succ_nth_eq
    exact le_trans this (IH stream_nth_eq)

/--
theorem `exists_nth_stream_eq_none_of_rat` / 定理 `exists_nth_stream_eq_none_of_rat`

English:
theorem exists_nth_stream_eq_none_of_rat
  given: (q : Rat)
  statement: exists n : Nat, IntFractPair.stream q n = none
  proof: by
  let fract_q_num := (Int.fract q).num; let n := fract_q_num.natAbs + 1
  rcases stream_nth_eq : IntFractPair.stream q n with ifp | ifp
  · use n, stream_nth_eq
  · -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have 

中文:
定理 存在_nth_stream_eq_none_of_rat
  条件: (q : 有理数)
  结论: 存在 n : 自然数, 整数FractPair.stream q n = none
  证明: by
  let fract_q_num := (Int.fract q).num; let n := fract_q_num.natAbs + 1
  rcases stream_nth_eq : IntFractPair.stream q n with ifp | ifp
  · use n, stream_nth_eq
  · -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have 

Depends on / 依赖: Int.fract, IntFractPair, IntFractPair.stream, arrive, decreased, fract_q_num, fract_q_num.natAbs, fractional, natAbs, numerator, stream, stream_nth_eq
-/
theorem exists_nth_stream_eq_none_of_rat (q : Rat) : exists n : Nat, IntFractPair.stream q n = none := by
  let fract_q_num := (Int.fract q).num; let n := fract_q_num.natAbs + 1
  rcases stream_nth_eq : IntFractPair.stream q n with ifp | ifp
  · use n, stream_nth_eq
  · -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have ifp_fr_num_le_q_fr_num_sub_n : ifp.fr.num <= fract_q_num - n :=
      stream_nth_fr_num_le_fr_num_sub_n_rat stream_nth_eq
    have : fract_q_num - n = -1 := by
      have : 0 <= fract_q_num := Rat.num_nonneg.mpr (Int.fract_nonneg q)
      simp only [n, Nat.cast_add, Int.natAbs_of_nonneg this, Nat.cast_one,
        sub_add_eq_sub_sub_swap, sub_right_comm, sub_self, zero_sub]
    have : 0 <= ifp.fr := (nth_stream_fr_nonneg_lt_one stream_nth_eq).left
    have : 0 <= ifp.fr.num := Rat.num_nonneg.mpr this
    lia

end IntFractPair

/--
theorem `terminates_of_rat` / 定理 `terminates_of_rat`

English:
theorem terminates_of_rat
  given: (q : Rat)
  statement: (of q).Terminates
  proof: Exists.elim (IntFractPair.exists_nth_stream_eq_none_of_rat q) fun n stream_nth_eq_none =>
    Exists.intro n
      (have : IntFractPair.stream q (n + 1) = none := IntFractPair.stream_isSeq q stream_nth_eq_none
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)

中文:
定理 terminates_of_rat
  条件: (q : 有理数)
  结论: (of q).Terminates
  证明: Exists.elim (IntFractPair.exists_nth_stream_eq_none_of_rat q) fun n stream_nth_eq_none =>
    Exists.intro n
      (have : IntFractPair.stream q (n + 1) = none := IntFractPair.stream_isSeq q stream_nth_eq_none
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)

Depends on / 依赖: Exists, Exists.elim, Exists.intro, IntFractPair, IntFractPair.exists_nth_stream_eq_none_of_rat, IntFractPair.stream, IntFractPair.stream_isSeq, exists_nth_stream_eq_none_of_rat, of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr, stream, stream_isSeq, stream_nth_eq_none
-/
theorem terminates_of_rat (q : Rat) : (of q).Terminates :=
  Exists.elim (IntFractPair.exists_nth_stream_eq_none_of_rat q) fun n stream_nth_eq_none =>
    Exists.intro n
      (have : IntFractPair.stream q (n + 1) = none := IntFractPair.stream_isSeq q stream_nth_eq_none
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)

end TerminatesOfRat

/--
theorem `terminates_iff_rat` / 定理 `terminates_iff_rat`

English:
theorem terminates_iff_rat
  given: [IsStrictOrderedRing K] (v : K)
  proof: Iff.intro exists_rat_eq_of_terminates
    fun exists_q_eq_v : exists q : Rat, v = (↑q : K) =>
    Exists.elim exists_q_eq_v fun q => fun v_eq_q : v = ↑q =>
      have : (of q).Terminates := terminates_of_rat q
      (of_terminates_iff_of_rat_terminates v_eq_q).mpr this

中文:
定理 terminates_iff_rat
  条件: [是StrictOrdered环 K] (v : K)
  证明: Iff.intro exists_rat_eq_of_terminates
    fun exists_q_eq_v : exists q : Rat, v = (↑q : K) =>
    Exists.elim exists_q_eq_v fun q => fun v_eq_q : v = ↑q =>
      have : (of q).Terminates := terminates_of_rat q
      (of_terminates_iff_of_rat_terminates v_eq_q).mpr this

Depends on / 依赖: Exists, Exists.elim, Iff.intro, Terminates, exists_q_eq_v, exists_rat_eq_of_terminates, of_terminates_iff_of_rat_terminates, terminates_of_rat, v_eq_q
-/
theorem terminates_iff_rat [IsStrictOrderedRing K] (v : K) :
    (of v).Terminates ↔ exists q : Rat, v = (q : K) :=
  Iff.intro exists_rat_eq_of_terminates
    fun exists_q_eq_v : exists q : Rat, v = (↑q : K) =>
    Exists.elim exists_q_eq_v fun q => fun v_eq_q : v = ↑q =>
      have : (of q).Terminates := terminates_of_rat q
      (of_terminates_iff_of_rat_terminates v_eq_q).mpr this

end GenContFract
