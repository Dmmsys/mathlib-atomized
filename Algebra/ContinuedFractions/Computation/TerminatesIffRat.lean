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


variable (v : K) (n : ℕ)

nonrec theorem exists_gcf_pair_rat_eq_of_nth_contsAux :
    ∃ conts : Pair ℚ, (of v).contsAux n = (conts.map (↑) : Pair K) :=
  Nat.strong_induction_on n
    (by
      clear n
      let g := of v
      intro n IH
      rcases n with (_ | _ | n)
      -- n = 0
      · suffices ∃ gp : Pair ℚ, Pair.mk (1 : K) 0 = gp.map (↑) by simpa [contsAux]
        use Pair.mk 1 0
        simp
      -- n = 1
      · suffices ∃ conts : Pair ℚ, Pair.mk g.h 1 = conts.map (↑) by simpa [contsAux]
        use Pair.mk ⌊v⌋ 1
        simp [g]
      -- 2 ≤ n
      · obtain ⟨pred_conts, pred_conts_eq⟩ := IH (n + 1) <| lt_add_one (n + 1)
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
            IH n <| lt_of_le_of_lt n.le_succ <| lt_add_one <| n + 1
          obtain ⟨a_eq_one, z, b_eq_z⟩ : gp_n.a = 1 ∧ ∃ z : ℤ, gp_n.b = (z : K) :=
            of_partNum_eq_one_and_exists_int_partDen_eq s_ppred_nth_eq
          -- finally, unfold the recurrence to obtain the required rational value.
          simp only [g, a_eq_one, b_eq_z,
            contsAux_recurrence s_ppred_nth_eq ppred_conts_eq pred_conts_eq]
          use nextConts 1 (z : ℚ) ppred_conts pred_conts
          cases ppred_conts; cases pred_conts
          simp [nextConts, nextNum, nextDen])

/-
**GenContFract.exists_gcf_pair_rat_eq_nth_conts** 是 Mathlib 中的一个定理，位于命名空间 `GenCo
ntFract`。
形式化陈述：exists_gcf_pair_rat_eq_nth_conts : exists conts : Pair Rat, (of v).conts n
 = (conts.map (↑) : Pair K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.nth_cont_eq_succ_nth_contAux`：nth_cont_eq_succ_nth_contAux 
: g.conts n = g.contsAux (n + 1)
· 使用定理 `GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux`：∀ {K : Type u_1} [i
nst : Field K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] (v : K) (n : ℕ), 
  ∃ conts, (GenContFract.of v).contsAux n…
-/
theorem exists_gcf_pair_rat_eq_nth_conts :
    ∃ conts : Pair ℚ, (of v).conts n = (conts.map (↑) : Pair K) := by
  rw [nth_cont_eq_succ_nth_contAux]; exact exists_gcf_pair_rat_eq_of_nth_contsAux v <| n + 1
/-
**GenContFract.exists_rat_eq_nth_num** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_rat_eq_nth_num : exists q : Rat, (of v).nums n = (q : K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_gcf_pair_rat_eq_nth_conts`：exists_gcf_pair_rat_eq_nt
h_conts : exists conts : Pair Rat, (of v).conts n = (conts.map (↑) : Pair K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_rat_eq_nth_num : ∃ q : ℚ, (of v).nums n = (q : K) := by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
  use a
  simp [num_eq_conts_a, nth_cont_eq]
/-
**GenContFract.exists_rat_eq_nth_den** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_rat_eq_nth_den : exists q : Rat, (of v).dens n = (q : K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_gcf_pair_rat_eq_nth_conts`：exists_gcf_pair_rat_eq_nt
h_conts : exists conts : Pair Rat, (of v).conts n = (conts.map (↑) : Pair K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_rat_eq_nth_den : ∃ q : ℚ, (of v).dens n = (q : K) := by
  rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
  use b
  simp [den_eq_conts_b, nth_cont_eq]

/-- Every finite convergent corresponds to a rational number. -/
/-
**GenContFract.exists_rat_eq_nth_conv** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：exists_rat_eq_nth_conv : exists q : Rat, (of v).convs n = (q : K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_rat_eq_nth_num`：exists_rat_eq_nth_num : exists q : R
at, (of v).nums n = (q : K)
· 使用定理 `GenContFract.exists_rat_eq_nth_den`：exists_rat_eq_nth_den : exists q : R
at, (of v).dens n = (q : K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every finite convergent corresponds to a rational number.
-/
theorem exists_rat_eq_nth_conv : ∃ q : ℚ, (of v).convs n = (q : K) := by
  rcases exists_rat_eq_nth_num v n with ⟨Aₙ, nth_num_eq⟩
  rcases exists_rat_eq_nth_den v n with ⟨Bₙ, nth_den_eq⟩
  use Aₙ / Bₙ
  simp [nth_num_eq, nth_den_eq, conv_eq_num_div_den]

variable {v}

/-- Every terminating continued fraction corresponds to a rational number. -/
/-
**GenContFract.exists_rat_eq_of_terminates** 是 Mathlib 中的一个定理，位于命名空间 `GenContFra
ct`。
形式化陈述：exists_rat_eq_of_terminates (terminates : (of v).Terminates) : exists q : 
Rat, v = ↑q
参数：terminates : (of v).Terminates。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.of_correctness_of_terminates`：of_correctness_of_terminates 
(terminates : (of v).Terminates) : exists n : Nat, v = (of v).convs n
· 使用定理 `GenContFract.exists_rat_eq_nth_conv`：exists_rat_eq_nth_conv : exists q :
 Rat, (of v).convs n = (q : K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
Every terminating continued fraction corresponds to a rational number.
-/
theorem exists_rat_eq_of_terminates (terminates : (of v).Terminates) : ∃ q : ℚ, v = ↑q := by
  obtain ⟨n, v_eq_conv⟩ : ∃ n, v = (of v).convs n := of_correctness_of_terminates terminates
  obtain ⟨q, conv_eq_q⟩ : ∃ q : ℚ, (of v).convs n = (↑q : K) := exists_rat_eq_nth_conv v n
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
variable [IsStrictOrderedRing K] {v : K} {q : ℚ}

/-! First, we show the correspondence for the very basic functions in
`GenContFract.IntFractPair`. -/


namespace IntFractPair

/-
**GenContFract.IntFractPair.coe_of_rat_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFrac
t.IntFractPair`。
形式化陈述：coe_of_rat_eq (v_eq_q : v = (↑q : K)) : ((IntFractPair.of q).mapFr (↑) : I
ntFractPair K) = IntFractPair.of v
参数：v_eq_q : v = (↑q : K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_fract`：cast_fract (x : Rat) : (↑(fract x) : α) = fract (x : α)
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    ((IntFractPair.of q).mapFr (↑) : IntFractPair K) = IntFractPair.of v := by
  simp [IntFractPair.of, v_eq_q]
/-
**GenContFract.IntFractPair.coe_stream_nth_rat_eq** 是 Mathlib 中的一个定理，位于命名空间 `Gen
ContFract.IntFractPair`。
形式化陈述：coe_stream_nth_rat_eq (v_eq_q : v = (↑q : K)) (n : Nat) : ((IntFractPair.s
tream q n).map (mapFr (↑)) : Option <| IntFractPair K) = IntFractPair.stream v n
参数：v_eq_q : v = (↑q : K)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.IntFractPair.coe_of_rat_eq`：coe_of_rat_eq (v_eq_q : v = (↑q
 : K)) : ((IntFractPair.of q).mapFr (↑) : IntFractPair K) = IntFractPair.of v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem coe_stream_nth_rat_eq (v_eq_q : v = (↑q : K)) (n : ℕ) :
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
      · have : (fr : K)⁻¹ = ((fr⁻¹ : ℚ) : K) := by norm_cast
        have coe_of_fr := coe_of_rat_eq this
        simpa [IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_ne_zero]
/-
**GenContFract.IntFractPair.coe_stream'_rat_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract.IntFractPair`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : LinearOrder K] [inst_2 : Floor
Ring K] [IsStrictOrderedRing K] {v : K}   {q : ℚ},   v = ↑q →     Stream'.map (O
ption.map (GenContFract.IntFractPair.mapFr Rat.cast)) (GenContFract.IntFractPair
.stream q) =       GenContFract.IntFractPair.stream v
参数：Option.map (GenContFract.IntFractPair.mapFr Rat.cast)；GenContFract.IntFractPa
ir.stream q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GenContFract.IntFractPair.coe_stream_nth_rat_eq`：coe_stream_nth_rat_eq (
v_eq_q : v = (↑q : K)) (n : Nat) : ((IntFractPair.stream q n).map (mapFr (↑)) : 
Option <| IntFractPair K) = IntFractP…
-/
theorem coe_stream'_rat_eq (v_eq_q : v = (↑q : K)) :
    ((IntFractPair.stream q).map (Option.map (mapFr (↑))) : Stream' <| Option <| IntFractPair K) =
      IntFractPair.stream v := by
  funext n; exact IntFractPair.coe_stream_nth_rat_eq v_eq_q n

end IntFractPair

/-! Now we lift the coercion results to the continued fraction computation. -/


/-
**GenContFract.coe_of_h_rat_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：coe_of_h_rat_eq (v_eq_q : v = (↑q : K)) : (↑((of q).h : Rat) : K) = (of v)
.h
参数：v_eq_q : v = (↑q : K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Now we lift the coercion results to the continued fraction computation.
-/
theorem coe_of_h_rat_eq (v_eq_q : v = (↑q : K)) : (↑((of q).h : ℚ) : K) = (of v).h := by
  simp_all

set_option backward.isDefEq.respectTransparency false in
/-
**GenContFract.coe_of_s_get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：coe_of_s_get?_rat_eq (v_eq_q : v = (↑q : K)) (n : Nat) : (((of q).s.get? n
).map (Pair.map (↑)) : Option <| Pair K) = (of v).s.get? n
参数：v_eq_q : v = (↑q : K)；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of_s_get?_rat_eq (v_eq_q : v = (↑q : K)) (n : ℕ) :
    (((of q).s.get? n).map (Pair.map (↑)) : Option <| Pair K) = (of v).s.get? n := by
  simp only [of, IntFractPair.seq1, Stream'.Seq.map_get?, Stream'.Seq.get?_tail]
  simp only [Stream'.Seq.get?]
  rw [← IntFractPair.coe_stream'_rat_eq v_eq_q]
  rcases succ_nth_stream_eq : IntFractPair.stream q (n + 1) with (_ | ⟨_, _⟩) <;>
    simp [Stream'.map, Stream'.get, succ_nth_stream_eq]
/-
**GenContFract.coe_of_s_rat_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：coe_of_s_rat_eq (v_eq_q : v = (↑q : K)) : ((of q).s.map (Pair.map ((↑))) :
 Stream'.Seq <| Pair K) = (of v).s
参数：v_eq_q : v = (↑q : K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.ext`：∀ {α : Type u} {s t : Stream'.Seq α}, (∀ (n : ℕ), s.get
? n = t.get? n) → s = t
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenContFract.coe_of_s_get?_rat_eq`：∀ {K : Type u_1} [inst : Field K] [in
st_1 : LinearOrder K] [inst_2 : FloorRing K] [IsStrictOrderedRing K] {v : K}   {
q : ℚ},   v = ↑q →     …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_of_s_rat_eq (v_eq_q : v = (↑q : K)) :
    ((of q).s.map (Pair.map ((↑))) : Stream'.Seq <| Pair K) = (of v).s := by
  ext n; rw [← coe_of_s_get?_rat_eq v_eq_q]; rfl

/-- Given `(v : K), (q : ℚ), and v = q`, we have that `of q = of v` -/
/-
**GenContFract.coe_of_rat_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：coe_of_rat_eq (v_eq_q : v = (↑q : K)) : (⟨(of q).h, (of q).s.map (Pair.map
 (↑))⟩ : GenContFract K) = of v
参数：v_eq_q : v = (↑q : K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `GenContFract.coe_of_s_rat_eq`：coe_of_s_rat_eq (v_eq_q : v = (↑q : K)) : 
((of q).s.map (Pair.map ((↑))) : Stream'.Seq <| Pair K) = (of v).s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GenContFract.IntFractPair.stream_isSeq`：stream_isSeq (v : K) : (IntFract
Pair.stream v).IsSeq
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given `(v : K), (q : ℚ), and v = q`, we have that `of q = of v`
-/
theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    (⟨(of q).h, (of q).s.map (Pair.map (↑))⟩ : GenContFract K) = of v := by
  rcases gcf_v_eq : of v with ⟨h, s⟩; subst v
  obtain rfl : ↑⌊(q : K)⌋ = h := by injection gcf_v_eq
  simp [coe_of_s_rat_eq rfl, gcf_v_eq]
/-
**GenContFract.of_terminates_iff_of_rat_terminates** 是 Mathlib 中的一个定理，位于命名空间 `Ge
nContFract`。
形式化陈述：of_terminates_iff_of_rat_terminates {v : K} {q : Rat} (v_eq_q : v = (q : K
)) : (of v).Terminates ↔ (of q).Terminates
参数：v_eq_q : v = (q : K)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
-/
theorem of_terminates_iff_of_rat_terminates {v : K} {q : ℚ} (v_eq_q : v = (q : K)) :
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

variable {q : ℚ} {n : ℕ}

/-- Shows that for any `q : ℚ` with `0 < q < 1`, the numerator of the fractional part of
`IntFractPair.of q⁻¹` is smaller than the numerator of `q`.
-/
/-
**GenContFract.IntFractPair.of_inv_fr_num_lt_num_of_pos** 是 Mathlib 中的一个定理，位于命名空
间 `GenContFract.IntFractPair`。
形式化陈述：of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (IntFractPair.of q⁻¹).fr.num
 < q.num
参数：q_pos : 0 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.fract_inv_num_lt_num_of_pos`：fract_inv_num_lt_num_of_pos {q : Rat} (
q_pos : 0 < q) : (fract q⁻¹).num < q.num

--- 原说明 ---
Shows that for any `q : ℚ` with `0 < q < 1`, the numerator of the fractional par
t of
`IntFractPair.of q⁻¹` is smaller than the numerator of `q`.
-/
theorem of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (IntFractPair.of q⁻¹).fr.num < q.num :=
  Rat.fract_inv_num_lt_num_of_pos q_pos

/-- Shows that the sequence of numerators of the fractional parts of the stream is strictly
antitone. -/
/-
**GenContFract.IntFractPair.stream_succ_nth_fr_num_lt_nth_fr_num_rat** 是 Mathlib
 中的一个定理，位于命名空间 `GenContFract.IntFractPair`。
形式化陈述：stream_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : IntFractPair 
Rat} (stream_nth_eq : IntFractPair.stream q n = some ifp_n) (stream_succ_nth_eq 
: IntFractPair.stream q (n + 1) = some ifp_succ_n) : ifp_succ_n.fr.num < ifp_n.f
r.num
参数：stream_nth_eq : IntFractPair.stream q n = some ifp_n；stream_succ_nth_eq : Int
FractPair.stream q (n + 1) = some ifp_succ_n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one`：nth_stream_fr_non
neg_lt_one {ifp_n : IntFractPair K} (nth_stream_eq : IntFractPair.stream v n = s
ome ifp_n) : 0 <= ifp_n.fr ∧ ifp_n.fr < 1
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `GenContFract.IntFractPair.of_inv_fr_num_lt_num_of_pos`：of_inv_fr_num_lt_
num_of_pos (q_pos : 0 < q) : (IntFractPair.of q⁻¹).fr.num < q.num

--- 原说明 ---
Shows that the sequence of numerators of the fractional parts of the stream is s
trictly
antitone.
-/
theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : IntFractPair ℚ}
    (stream_nth_eq : IntFractPair.stream q n = some ifp_n)
    (stream_succ_nth_eq : IntFractPair.stream q (n + 1) = some ifp_succ_n) :
    ifp_succ_n.fr.num < ifp_n.fr.num := by
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, IntFractPair.of_eq_ifp_succ_n⟩ :
    ∃ ifp_n',
      IntFractPair.stream q n = some ifp_n' ∧
        ifp_n'.fr ≠ 0 ∧ IntFractPair.of ifp_n'.fr⁻¹ = ifp_succ_n :=
    succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq
  have : ifp_n = ifp_n' := by injection Eq.trans stream_nth_eq.symm stream_nth_eq'
  cases this
  rw [← IntFractPair.of_eq_ifp_succ_n]
  obtain ⟨zero_le_ifp_n_fract, _⟩ := nth_stream_fr_nonneg_lt_one stream_nth_eq
  have : 0 < ifp_n.fr := lt_of_le_of_ne zero_le_ifp_n_fract <| ifp_n_fract_ne_zero.symm
  exact of_inv_fr_num_lt_num_of_pos this
/-
**GenContFract.IntFractPair.stream_nth_fr_num_le_fr_num_sub_n_rat** 是 Mathlib 中的
一个定理，位于命名空间 `GenContFract.IntFractPair`。
形式化陈述：stream_nth_fr_num_le_fr_num_sub_n_rat : forall {ifp_n : IntFractPair Rat},
 IntFractPair.stream q n = some ifp_n -> ifp_n.fr.num <= (IntFractPair.of q).fr.
num - n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…
· 使用定理 `GenContFract.IntFractPair.stream_succ_nth_fr_num_lt_nth_fr_num_rat`：stre
am_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : IntFractPair Rat} (stre
am_nth_eq : IntFractPair.stream q n = some ifp_n) (strea…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
· 使用定理 `sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - (b + c) = a - b - c
· 使用定理 `le_sub_right_of_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE 
α] [AddRightMono α] {a b c : α}, a + b ≤ c → a ≤ c - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem stream_nth_fr_num_le_fr_num_sub_n_rat :
    ∀ {ifp_n : IntFractPair ℚ},
      IntFractPair.stream q n = some ifp_n → ifp_n.fr.num ≤ (IntFractPair.of q).fr.num - n := by
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    have : IntFractPair.of q = ifp_zero := by injection stream_zero_eq
    simp [this.symm]
  | succ n IH =>
    intro ifp_succ_n stream_succ_nth_eq
    suffices ifp_succ_n.fr.num + 1 ≤ (IntFractPair.of q).fr.num - n by
      rw [Int.natCast_succ, sub_add_eq_sub_sub]
      solve_by_elim [le_sub_right_of_add_le]
    rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with ⟨ifp_n, stream_nth_eq, -⟩
    have : ifp_succ_n.fr.num < ifp_n.fr.num :=
      stream_succ_nth_fr_num_lt_nth_fr_num_rat stream_nth_eq stream_succ_nth_eq
    exact le_trans this (IH stream_nth_eq)
/-
**GenContFract.IntFractPair.exists_nth_stream_eq_none_of_rat** 是 Mathlib 中的一个定理，
位于命名空间 `GenContFract.IntFractPair`。
形式化陈述：exists_nth_stream_eq_none_of_rat (q : Rat) : exists n : Nat, IntFractPair.
stream q n = none
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.IntFractPair.stream_nth_fr_num_le_fr_num_sub_n_rat`：stream_
nth_fr_num_le_fr_num_sub_n_rat : forall {ifp_n : IntFractPair Rat}, IntFractPair
.stream q n = some ifp_n -> ifp_n.fr.num <= (IntFract…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.num_nonneg`：∀ {q : ℚ}, 0 ≤ q.num ↔ 0 ≤ q
· 使用定理 `Int.fract_nonneg`：fract_nonneg (a : R) : 0 <= fract a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_add_eq_sub_sub_swap`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (
a b c : α), a - (b + c) = a - c - b
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `GenContFract.IntFractPair.nth_stream_fr_nonneg_lt_one`：nth_stream_fr_non
neg_lt_one {ifp_n : IntFractPair K} (nth_stream_eq : IntFractPair.stream v n = s
ome ifp_n) : 0 <= ifp_n.fr ∧ ifp_n.fr < 1
-/
theorem exists_nth_stream_eq_none_of_rat (q : ℚ) : ∃ n : ℕ, IntFractPair.stream q n = none := by
  let fract_q_num := (Int.fract q).num; let n := fract_q_num.natAbs + 1
  rcases stream_nth_eq : IntFractPair.stream q n with ifp | ifp
  · use n, stream_nth_eq
  · -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have ifp_fr_num_le_q_fr_num_sub_n : ifp.fr.num ≤ fract_q_num - n :=
      stream_nth_fr_num_le_fr_num_sub_n_rat stream_nth_eq
    have : fract_q_num - n = -1 := by
      have : 0 ≤ fract_q_num := Rat.num_nonneg.mpr (Int.fract_nonneg q)
      simp only [n, Nat.cast_add, Int.natAbs_of_nonneg this, Nat.cast_one,
        sub_add_eq_sub_sub_swap, sub_right_comm, sub_self, zero_sub]
    have : 0 ≤ ifp.fr := (nth_stream_fr_nonneg_lt_one stream_nth_eq).left
    have : 0 ≤ ifp.fr.num := Rat.num_nonneg.mpr this
    lia

end IntFractPair

/-- The continued fraction of a rational number terminates. -/
/-
**GenContFract.terminates_of_rat** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：terminates_of_rat (q : Rat) : (of q).Terminates
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `GenContFract.IntFractPair.exists_nth_stream_eq_none_of_rat`：exists_nth_s
tream_eq_none_of_rat (q : Rat) : exists n : Nat, IntFractPair.stream q n = none
· 使用定理 `GenContFract.IntFractPair.stream_isSeq`：stream_isSeq (v : K) : (IntFract
Pair.stream v).IsSeq
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none`
：of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none : (of v).TerminatedA
t n ↔ IntFractPair.stream v (n + 1) = none

--- 原说明 ---
The continued fraction of a rational number terminates.
-/
theorem terminates_of_rat (q : ℚ) : (of q).Terminates :=
  Exists.elim (IntFractPair.exists_nth_stream_eq_none_of_rat q) fun n stream_nth_eq_none =>
    Exists.intro n
      (have : IntFractPair.stream q (n + 1) = none := IntFractPair.stream_isSeq q stream_nth_eq_none
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)

end TerminatesOfRat

/-- The continued fraction `GenContFract.of v` terminates if and only if `v ∈ ℚ`. -/
/-
**GenContFract.terminates_iff_rat** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：terminates_iff_rat [IsStrictOrderedRing K] (v : K) : (of v).Terminates ↔ e
xists q : Rat, v = (q : K)
参数：v : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_rat_eq_of_terminates`：exists_rat_eq_of_terminates (t
erminates : (of v).Terminates) : exists q : Rat, v = ↑q
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `GenContFract.terminates_of_rat`：terminates_of_rat (q : Rat) : (of q).Ter
minates
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.of_terminates_iff_of_rat_terminates`：of_terminates_iff_of_r
at_terminates {v : K} {q : Rat} (v_eq_q : v = (q : K)) : (of v).Terminates ↔ (of
 q).Terminates

--- 原说明 ---
The continued fraction `GenContFract.of v` terminates if and only if `v ∈ ℚ`.
-/
theorem terminates_iff_rat [IsStrictOrderedRing K] (v : K) :
    (of v).Terminates ↔ ∃ q : ℚ, v = (q : K) :=
  Iff.intro exists_rat_eq_of_terminates
    fun exists_q_eq_v : ∃ q : ℚ, v = (↑q : K) =>
    Exists.elim exists_q_eq_v fun q => fun v_eq_q : v = ↑q =>
      have : (of q).Terminates := terminates_of_rat q
      (of_terminates_iff_of_rat_terminates v_eq_q).mpr this

end GenContFract

