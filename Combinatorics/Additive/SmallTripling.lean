/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring

/-!
# Small tripling implies small powers

This file shows that a set with small tripling has small powers, even in non-abelian groups.

## See also

In abelian groups, the Plünnecke-Ruzsa inequality is the stronger statement that small doubling
implies small powers. See `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean`.
-/

public section

open Fin MulOpposite
open List hiding tail
open scoped Pointwise

namespace Finset
variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : Real} {m : Nat}

@[to_additive]
/--
lemma `inductive_claim_mul` / 引理 `inductive_claim_mul`

English:
lemma inductive_claim_mul
  statement: (hm : 3 <= m)
  proof: by
  induction m, hm using Nat.le_induction with
  | base => simpa using h ε hε
  | succ m hm ih =>
    obtain _ | m := m
    · simp at hm
    have hm₀ : m != 0 := by simp at hm; positivity
    have hε₀ i : ε i != 0 := fun h => by simpa [h] using hε i
    obtain rfl | hA := A.eq_empty_or_nonempty
    · simp [hε₀]
    have hk : 0 <= k :=
      nonneg_of_mul_nonneg_left ((h 1 (by simp)).trans' (by positivity)) (by positivity)
    let π {n} (δ : Fin n -> Int) : Finset G := ((finRange _).map fun i => A ^ δ i).prod
    let V : Finset G := π ![-ε 1, -ε 0]
let W : Finset G := π tail tail ε
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
    calc
      (#A * #(π ε) : Real)
        = #A * #(V⁻¹ * W) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def, mul_assoc]
      _ <= #(A * V) * #(A * W) := by norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul ..
      _ = #(π ![1, -ε 1, -ε 0]) * #(π <| Fin.cons 1 <| tail <| tail ε) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def]
      _ <= (k * #A) * (k ^ (m - 1) * #A) := by
        gcongr
        · exact h ![1, -ε 1, -ε 0] fun i => by fin_cases i <;> simp [hε]
· exact ih (Fin.cons 1 <| tail <| tail ε) Fin.cons (by simp) (by simp [hε, Fin.tail])
      _ = #A * (k ^ m * #A) := by rw [← pow_sub_one_mul hm₀]; ring

@[to_additive]

中文:
引理 inductive_claim_mul
  结论: (hm : 3 <= m)
  证明: by
  induction m, hm using Nat.le_induction with
  | base => simpa using h ε hε
  | succ m hm ih =>
    obtain _ | m := m
    · simp at hm
    have hm₀ : m != 0 := by simp at hm; positivity
    have hε₀ i : ε i != 0 := fun h => by simpa [h] using hε i
    obtain rfl | hA := A.eq_empty_or_nonempty
    · simp [hε₀]
    have hk : 0 <= k :=
      nonneg_of_mul_nonneg_left ((h 1 (by simp)).trans' (by positivity)) (by positivity)
    let π {n} (δ : Fin n -> Int) : Finset G := ((finRange _).map fun i => A ^ δ i).prod
    let V : Finset G := π ![-ε 1, -ε 0]
let W : Finset G := π tail tail ε
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
    calc
      (#A * #(π ε) : Real)
        = #A * #(V⁻¹ * W) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def, mul_assoc]
      _ <= #(A * V) * #(A * W) := by norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul ..
      _ = #(π ![1, -ε 1, -ε 0]) * #(π <| Fin.cons 1 <| tail <| tail ε) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def]
      _ <= (k * #A) * (k ^ (m - 1) * #A) := by
        gcongr
        · exact h ![1, -ε 1, -ε 0] fun i => by fin_cases i <;> simp [hε]
· exact ih (Fin.cons 1 <| tail <| tail ε) Fin.cons (by simp) (by simp [hε, Fin.tail])
      _ = #A * (k ^ m * #A) := by rw [← pow_sub_one_mul hm₀]; ring

@[to_additive]
-/
private lemma inductive_claim_mul (hm : 3 <= m)
    (h : forall ε : Fin 3 -> Int, (forall i, |ε i| = 1) -> #((finRange 3).map fun i => A ^ ε i).prod <= k * #A)
    (ε : Fin m -> Int) (hε : forall i, |ε i| = 1) :
    #((finRange m).map fun i => A ^ ε i).prod <= k ^ (m - 2) * #A := by
  induction m, hm using Nat.le_induction with
  | base => simpa using h ε hε
  | succ m hm ih =>
    obtain _ | m := m
    · simp at hm
    have hm₀ : m != 0 := by simp at hm; positivity
    have hε₀ i : ε i != 0 := fun h => by simpa [h] using hε i
    obtain rfl | hA := A.eq_empty_or_nonempty
    · simp [hε₀]
    have hk : 0 <= k :=
      nonneg_of_mul_nonneg_left ((h 1 (by simp)).trans' (by positivity)) (by positivity)
    let π {n} (δ : Fin n -> Int) : Finset G := ((finRange _).map fun i => A ^ δ i).prod
    let V : Finset G := π ![-ε 1, -ε 0]
let W : Finset G := π tail tail ε
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
    calc
      (#A * #(π ε) : Real)
        = #A * #(V⁻¹ * W) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def, mul_assoc]
      _ <= #(A * V) * #(A * W) := by norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul ..
      _ = #(π ![1, -ε 1, -ε 0]) * #(π <| Fin.cons 1 <| tail <| tail ε) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def]
      _ <= (k * #A) * (k ^ (m - 1) * #A) := by
        gcongr
        · exact h ![1, -ε 1, -ε 0] fun i => by fin_cases i <;> simp [hε]
· exact ih (Fin.cons 1 <| tail <| tail ε) Fin.cons (by simp) (by simp [hε, Fin.tail])
      _ = #A * (k ^ m * #A) := by rw [← pow_sub_one_mul hm₀]; ring

@[to_additive]
/--
lemma `small_neg_pos_pos_mul` / 引理 `small_neg_pos_pos_mul`

English:
lemma small_neg_pos_pos_mul
  given: (hA : #(A ^ 3) <= K * #A)
  statement: #(A⁻¹ * A * A) <= K ^ 2 * #A
  proof: by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 <= K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
  calc
    (#A * #(A⁻¹ * A * A) : Real) = #A * #(A⁻¹ * (A * A)) := by rw [mul_assoc]
    _ <= #(A * A) * #(A * (A * A)) := by
      norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul A A (A * A)
    _ = #(A ^ 2) * #(A ^ 3) := by simp [pow_succ']
    _ <= (K * #A) * (K * #A) := by
      gcongr
      calc
        (#(A ^ 2) : Real) <= #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ <= K * #A := hA
    _ = #A * (K ^ 2 * #A) := by ring

@[to_additive]

中文:
引理 small_neg_pos_pos_mul
  条件: (hA : #(A ^ 3) <= K * #A)
  结论: #(A⁻¹ * A * A) <= K ^ 2 * #A
  证明: by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 <= K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
  calc
    (#A * #(A⁻¹ * A * A) : Real) = #A * #(A⁻¹ * (A * A)) := by rw [mul_assoc]
    _ <= #(A * A) * #(A * (A * A)) := by
      norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul A A (A * A)
    _ = #(A ^ 2) * #(A ^ 3) := by simp [pow_succ']
    _ <= (K * #A) * (K * #A) := by
      gcongr
      calc
        (#(A ^ 2) : Real) <= #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ <= K * #A := hA
    _ = #A * (K ^ 2 * #A) := by ring

@[to_additive]
-/
private lemma small_neg_pos_pos_mul (hA : #(A ^ 3) <= K * #A) : #(A⁻¹ * A * A) <= K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 <= K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
  calc
    (#A * #(A⁻¹ * A * A) : Real) = #A * #(A⁻¹ * (A * A)) := by rw [mul_assoc]
    _ <= #(A * A) * #(A * (A * A)) := by
      norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul A A (A * A)
    _ = #(A ^ 2) * #(A ^ 3) := by simp [pow_succ']
    _ <= (K * #A) * (K * #A) := by
      gcongr
      calc
        (#(A ^ 2) : Real) <= #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ <= K * #A := hA
    _ = #A * (K ^ 2 * #A) := by ring

@[to_additive]
/--
lemma `small_neg_neg_pos_mul` / 引理 `small_neg_neg_pos_mul`

English:
lemma small_neg_neg_pos_mul
  given: (hA : #(A ^ 3) <= K * #A)
  statement: #(A⁻¹ * A⁻¹ * A) <= K ^ 2 * #A
  proof: by
  rw [← card_inv]
  simpa [mul_assoc] using small_neg_pos_pos_mul (A := A) (K := K) (by simpa)

@[to_additive]

中文:
引理 small_neg_neg_pos_mul
  条件: (hA : #(A ^ 3) <= K * #A)
  结论: #(A⁻¹ * A⁻¹ * A) <= K ^ 2 * #A
  证明: by
  rw [← card_inv]
  simpa [mul_assoc] using small_neg_pos_pos_mul (A := A) (K := K) (by simpa)

@[to_additive]
-/
private lemma small_neg_neg_pos_mul (hA : #(A ^ 3) <= K * #A) : #(A⁻¹ * A⁻¹ * A) <= K ^ 2 * #A := by
  rw [← card_inv]
  simpa [mul_assoc] using small_neg_pos_pos_mul (A := A) (K := K) (by simpa)

@[to_additive]
/--
lemma `small_pos_neg_neg_mul` / 引理 `small_pos_neg_neg_mul`

English:
lemma small_pos_neg_neg_mul
  given: (hA : #(A ^ 3) <= K * #A)
  statement: #(A * A⁻¹ * A⁻¹) <= K ^ 2 * #A
  proof: by
  simpa using small_neg_pos_pos_mul (A := A⁻¹) (by simpa)

@[to_additive]

中文:
引理 small_pos_neg_neg_mul
  条件: (hA : #(A ^ 3) <= K * #A)
  结论: #(A * A⁻¹ * A⁻¹) <= K ^ 2 * #A
  证明: by
  simpa using small_neg_pos_pos_mul (A := A⁻¹) (by simpa)

@[to_additive]
-/
private lemma small_pos_neg_neg_mul (hA : #(A ^ 3) <= K * #A) : #(A * A⁻¹ * A⁻¹) <= K ^ 2 * #A := by
  simpa using small_neg_pos_pos_mul (A := A⁻¹) (by simpa)

@[to_additive]
/--
lemma `small_pos_pos_neg_mul` / 引理 `small_pos_pos_neg_mul`

English:
lemma small_pos_pos_neg_mul
  given: (hA : #(A ^ 3) <= K * #A)
  statement: #(A * A * A⁻¹) <= K ^ 2 * #A
  proof: by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_neg_mul (A := A) (K := K) (by simpa)

@[to_additive]

中文:
引理 small_pos_pos_neg_mul
  条件: (hA : #(A ^ 3) <= K * #A)
  结论: #(A * A * A⁻¹) <= K ^ 2 * #A
  证明: by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_neg_mul (A := A) (K := K) (by simpa)

@[to_additive]
-/
private lemma small_pos_pos_neg_mul (hA : #(A ^ 3) <= K * #A) : #(A * A * A⁻¹) <= K ^ 2 * #A := by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_neg_mul (A := A) (K := K) (by simpa)

@[to_additive]
/--
lemma `small_pos_neg_pos_mul` / 引理 `small_pos_neg_pos_mul`

English:
lemma small_pos_neg_pos_mul
  given: (hA : #(A ^ 3) <= K * #A)
  statement: #(A * A⁻¹ * A) <= K ^ 3 * #A
  proof: by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
  calc
    (#A * #(A * A⁻¹ * A) : Real) <= #(A * (A * A⁻¹)) * #(A * A) := by
      norm_cast; simpa using ruzsa_triangle_inequality_invMul_mul_mul (A * A⁻¹) A A
    _ = #(A * A * A⁻¹) * #(A ^ 2) := by simp [pow_succ, mul_assoc]
    _ <= (K ^ 2 * #A) * (K * #A) := by
      gcongr
      · exact small_pos_pos_neg_mul hA
      calc
        (#(A ^ 2) : Real) <= #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ <= K * #A := hA
    _ = #A * (K ^ 3 * #A) := by ring

@[to_additive]

中文:
引理 small_pos_neg_pos_mul
  条件: (hA : #(A ^ 3) <= K * #A)
  结论: #(A * A⁻¹ * A) <= K ^ 3 * #A
  证明: by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
  calc
    (#A * #(A * A⁻¹ * A) : Real) <= #(A * (A * A⁻¹)) * #(A * A) := by
      norm_cast; simpa using ruzsa_triangle_inequality_invMul_mul_mul (A * A⁻¹) A A
    _ = #(A * A * A⁻¹) * #(A ^ 2) := by simp [pow_succ, mul_assoc]
    _ <= (K ^ 2 * #A) * (K * #A) := by
      gcongr
      · exact small_pos_pos_neg_mul hA
      calc
        (#(A ^ 2) : Real) <= #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ <= K * #A := hA
    _ = #A * (K ^ 3 * #A) := by ring

@[to_additive]
-/
private lemma small_pos_neg_pos_mul (hA : #(A ^ 3) <= K * #A) : #(A * A⁻¹ * A) <= K ^ 3 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < #A)
  calc
    (#A * #(A * A⁻¹ * A) : Real) <= #(A * (A * A⁻¹)) * #(A * A) := by
      norm_cast; simpa using ruzsa_triangle_inequality_invMul_mul_mul (A * A⁻¹) A A
    _ = #(A * A * A⁻¹) * #(A ^ 2) := by simp [pow_succ, mul_assoc]
    _ <= (K ^ 2 * #A) * (K * #A) := by
      gcongr
      · exact small_pos_pos_neg_mul hA
      calc
        (#(A ^ 2) : Real) <= #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ <= K * #A := hA
    _ = #A * (K ^ 3 * #A) := by ring

@[to_additive]
/--
lemma `small_neg_pos_neg_mul` / 引理 `small_neg_pos_neg_mul`

English:
lemma small_neg_pos_neg_mul
  given: (hA : #(A ^ 3) <= K * #A)
  statement: #(A⁻¹ * A * A⁻¹) <= K ^ 3 * #A
  proof: by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_pos_mul (A := A) (K := K) (by simpa)

中文:
引理 small_neg_pos_neg_mul
  条件: (hA : #(A ^ 3) <= K * #A)
  结论: #(A⁻¹ * A * A⁻¹) <= K ^ 3 * #A
  证明: by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_pos_mul (A := A) (K := K) (by simpa)
-/
private lemma small_neg_pos_neg_mul (hA : #(A ^ 3) <= K * #A) : #(A⁻¹ * A * A⁻¹) <= K ^ 3 * #A := by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_pos_mul (A := A) (K := K) (by simpa)

/-- If `A` has small tripling, say with constant `K`, then `A` has small alternating powers, in the
sense that `|A^±1 * ... * A^±1|` is at most `|A|` times a constant exponential in the number of
terms in the product.

When `A` is symmetric (`A⁻¹ = A`), the base of the exponential can be lowered from `K ^ 3` to `K`,
where `K` is the tripling constant. See `Finset.small_pow_of_small_tripling`. -/
@[to_additive
/-- If `A` has small tripling, say with constant `K`, then `A` has small alternating powers, in the
sense that `|±A ± ... ± A|` is at most `|A|` times a constant exponential in the number of
terms in the product.

When `A` is symmetric (`-A = A`), the base of the exponential can be lowered from `K ^ 3` to `K`,
where `K` is the tripling constant. See `Finset.small_nsmul_of_small_tripling`. -/]
/--
lemma `small_alternating_pow_of_small_tripling` / 引理 `small_alternating_pow_of_small_tripling`

English:
lemma small_alternating_pow_of_small_tripling
  statement: (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (ε : Fin m -> Int)
  proof: by
  have hm₀ : m != 0 := by positivity
  have hε₀ i : ε i != 0 := fun h => by simpa [h] using hε i
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp [hm₀, hε₀]
  have hK₁ : 1 <= K :=
    one_le_of_le_mul_right₀ (by positivity)
      (hA.trans' <| by norm_cast; exact card_le_card_pow (by simp))
  rw [pow_mul]
  refine inductive_claim_mul hm (fun δ hδ => ?_) ε hε
  simp only [finRange_succ, Nat.reduceAdd, isValue, finRange_zero, map_nil, List.map_cons,
    succ_zero_eq_one, succ_one_eq_two, List.prod_cons, prod_nil, mul_one, ← mul_assoc]
  simp only [zero_le_one, abs_eq, Int.reduceNeg, forall_iff_succ, isValue, succ_zero_eq_one,
    succ_one_eq_two, IsEmpty.forall_iff, and_true] at hδ
  have : K ^ 2 <= K ^ 3 := by gcongr; simp
  obtain ⟨hδ₀ | hδ₀, hδ₁ | hδ₁, hδ₂ | hδ₂⟩ := hδ <;> simp [hδ₀, hδ₁, hδ₂]
  · simp [pow_succ] at hA
    nlinarith
  · nlinarith [small_pos_pos_neg_mul hA]
  · nlinarith [small_pos_neg_pos_mul hA]
  · nlinarith [small_pos_neg_neg_mul hA]
  · nlinarith [small_neg_pos_pos_mul hA]
  · nlinarith [small_neg_pos_neg_mul hA]
  · nlinarith [small_neg_neg_pos_mul hA]
  · simp [*, pow_succ', ← mul_inv_rev] at hA ⊢
    nlinarith

中文:
引理 small_alternating_pow_of_small_tripling
  结论: (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (ε : 有限集 m -> 整数)
  证明: by
  have hm₀ : m != 0 := by positivity
  have hε₀ i : ε i != 0 := fun h => by simpa [h] using hε i
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp [hm₀, hε₀]
  have hK₁ : 1 <= K :=
    one_le_of_le_mul_right₀ (by positivity)
      (hA.trans' <| by norm_cast; exact card_le_card_pow (by simp))
  rw [pow_mul]
  refine inductive_claim_mul hm (fun δ hδ => ?_) ε hε
  simp only [finRange_succ, Nat.reduceAdd, isValue, finRange_zero, map_nil, List.map_cons,
    succ_zero_eq_one, succ_one_eq_two, List.prod_cons, prod_nil, mul_one, ← mul_assoc]
  simp only [zero_le_one, abs_eq, Int.reduceNeg, forall_iff_succ, isValue, succ_zero_eq_one,
    succ_one_eq_two, IsEmpty.forall_iff, and_true] at hδ
  have : K ^ 2 <= K ^ 3 := by gcongr; simp
  obtain ⟨hδ₀ | hδ₀, hδ₁ | hδ₁, hδ₂ | hδ₂⟩ := hδ <;> simp [hδ₀, hδ₁, hδ₂]
  · simp [pow_succ] at hA
    nlinarith
  · nlinarith [small_pos_pos_neg_mul hA]
  · nlinarith [small_pos_neg_pos_mul hA]
  · nlinarith [small_pos_neg_neg_mul hA]
  · nlinarith [small_neg_pos_pos_mul hA]
  · nlinarith [small_neg_pos_neg_mul hA]
  · nlinarith [small_neg_neg_pos_mul hA]
  · simp [*, pow_succ', ← mul_inv_rev] at hA ⊢
    nlinarith

Depends on / 依赖: A.eq_empty_or_nonempty, List.map_cons, List.prod_cons, Nat.reduceAdd, card_le_card_pow, eq_empty_or_nonempty, finRange_succ, finRange_zero, hA.trans, inductive_claim_mul, isValue, map_cons, map_nil, mul_o, pow_mul, prod_cons, prod_nil, reduceAdd, succ_one_eq_two, succ_zero_eq_one
-/
lemma small_alternating_pow_of_small_tripling (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (ε : Fin m -> Int)
    (hε : forall i, |ε i| = 1) :
    #((finRange m).map fun i => A ^ ε i).prod <= K ^ (3 * (m - 2)) * #A := by
  have hm₀ : m != 0 := by positivity
  have hε₀ i : ε i != 0 := fun h => by simpa [h] using hε i
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp [hm₀, hε₀]
  have hK₁ : 1 <= K :=
    one_le_of_le_mul_right₀ (by positivity)
      (hA.trans' <| by norm_cast; exact card_le_card_pow (by simp))
  rw [pow_mul]
  refine inductive_claim_mul hm (fun δ hδ => ?_) ε hε
  simp only [finRange_succ, Nat.reduceAdd, isValue, finRange_zero, map_nil, List.map_cons,
    succ_zero_eq_one, succ_one_eq_two, List.prod_cons, prod_nil, mul_one, ← mul_assoc]
  simp only [zero_le_one, abs_eq, Int.reduceNeg, forall_iff_succ, isValue, succ_zero_eq_one,
    succ_one_eq_two, IsEmpty.forall_iff, and_true] at hδ
  have : K ^ 2 <= K ^ 3 := by gcongr; simp
  obtain ⟨hδ₀ | hδ₀, hδ₁ | hδ₁, hδ₂ | hδ₂⟩ := hδ <;> simp [hδ₀, hδ₁, hδ₂]
  · simp [pow_succ] at hA
    nlinarith
  · nlinarith [small_pos_pos_neg_mul hA]
  · nlinarith [small_pos_neg_pos_mul hA]
  · nlinarith [small_pos_neg_neg_mul hA]
  · nlinarith [small_neg_pos_pos_mul hA]
  · nlinarith [small_neg_pos_neg_mul hA]
  · nlinarith [small_neg_neg_pos_mul hA]
  · simp [*, pow_succ', ← mul_inv_rev] at hA ⊢
    nlinarith

/-- If `A` is symmetric (`A⁻¹ = A`) and has small tripling, then `A` has small powers,
in the sense that `|A ^ m|` is at most `|A|` times a constant exponential in `m`.

See also `Finset.small_alternating_pow_of_small_tripling` for a version with a weaker constant but
which encompasses non-symmetric sets. -/
@[to_additive
/-- If `A` is symmetric (`-A = A`) and has small tripling, then `A` has small powers,
in the sense that `|m • A|` is at most `|A|` times a constant exponential in `m`.

See also `Finset.small_alternating_nsmul_of_small_tripling` for a version with a weaker constant but
which encompasses non-symmetric sets. -/]
/--
lemma `small_pow_of_small_tripling` / 引理 `small_pow_of_small_tripling`

English:
lemma small_pow_of_small_tripling
  given: (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (hAsymm : A⁻¹ = A)
  proof: by
  have (ε : Int) (hε : |ε| = 1) : A ^ ε = A := by
    obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hε <;> simp [hAsymm]
  calc
    (#(A ^ m) : Real) = #((finRange m).map fun i => A ^ 1).prod := by simp
    _ <= K ^ (m - 2) * #A :=
      inductive_claim_mul hm (fun δ hδ => by simpa [this _ (hδ _), pow_succ'] using hA) _ (by simp)

中文:
引理 small_pow_of_small_tripling
  条件: (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (hAsymm : A⁻¹ = A)
  证明: by
  have (ε : Int) (hε : |ε| = 1) : A ^ ε = A := by
    obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hε <;> simp [hAsymm]
  calc
    (#(A ^ m) : Real) = #((finRange m).map fun i => A ^ 1).prod := by simp
    _ <= K ^ (m - 2) * #A :=
      inductive_claim_mul hm (fun δ hδ => by simpa [this _ (hδ _), pow_succ'] using hA) _ (by simp)

Depends on / 依赖: eq_or_eq_neg_of_abs_eq, finRange, hAsymm, inductive_claim_mul, pow_succ
-/
lemma small_pow_of_small_tripling (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (hAsymm : A⁻¹ = A) :
    #(A ^ m) <= K ^ (m - 2) * #A := by
  have (ε : Int) (hε : |ε| = 1) : A ^ ε = A := by
    obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hε <;> simp [hAsymm]
  calc
    (#(A ^ m) : Real) = #((finRange m).map fun i => A ^ 1).prod := by simp
    _ <= K ^ (m - 2) * #A :=
      inductive_claim_mul hm (fun δ hδ => by simpa [this _ (hδ _), pow_succ'] using hA) _ (by simp)

end Finset
