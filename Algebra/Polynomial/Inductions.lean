/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Damiano Testa, Jens Wagemaker
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Division
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/

@[expose] public section


noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : Nat}

section Semiring

variable [Semiring R] {p q : R[X]}

/--
Definition of `divX` / `divX` 的定义

English:
definition divX
  signature: (p : R[X])
  body: ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩

@[simp]

中文:
定义 divX
  签名: (p : R[X])
  定义体: ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.divOf, p.toFinsupp, toFinsupp
-/
def divX (p : R[X]) : R[X] :=
  ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩

@[simp]
/--
theorem `coeff_divX` / 定理 `coeff_divX`

English:
theorem coeff_divX
  statement: (divX p).coeff n = p.coeff (n + 1)
  proof: by
  rw [add_comm]; cases p; rfl

中文:
定理 coeff_divX
  结论: (divX p).coeff n = p.coeff (n + 1)
  证明: by
  rw [add_comm]; cases p; rfl

Depends on / 依赖: Semiring, SetLike, SubsemiringClass, add_comm, toSemiring
-/
theorem coeff_divX : (divX p).coeff n = p.coeff (n + 1) := by
  rw [add_comm]; cases p; rfl

/--
theorem `divX_mul_X_add` / 定理 `divX_mul_X_add`

English:
theorem divX_mul_X_add
  given: (p : R[X])
  statement: divX p * X + C (p.coeff 0) = p
  proof: ext by rintro ⟨_ | _⟩ <;> simp [coeff_C, coeff_mul_X]

@[simp]

中文:
定理 divX_mul_X_add
  条件: (p : R[X])
  结论: divX p * X + C (p.coeff 0) = p
  证明: ext by rintro ⟨_ | _⟩ <;> simp [coeff_C, coeff_mul_X]

@[simp]

Depends on / 依赖: coeff_C, coeff_mul_X
-/
theorem divX_mul_X_add (p : R[X]) : divX p * X + C (p.coeff 0) = p :=
ext by rintro ⟨_ | _⟩ <;> simp [coeff_C, coeff_mul_X]

@[simp]
/--
theorem `X_mul_divX_add` / 定理 `X_mul_divX_add`

English:
theorem X_mul_divX_add
  given: (p : R[X])
  statement: X * divX p + C (p.coeff 0) = p
  proof: ext by rintro ⟨_ | _⟩ <;> simp [coeff_C]

@[simp]

中文:
定理 X_mul_divX_add
  条件: (p : R[X])
  结论: X * divX p + C (p.coeff 0) = p
  证明: ext by rintro ⟨_ | _⟩ <;> simp [coeff_C]

@[simp]

Depends on / 依赖: coeff_C
-/
theorem X_mul_divX_add (p : R[X]) : X * divX p + C (p.coeff 0) = p :=
ext by rintro ⟨_ | _⟩ <;> simp [coeff_C]

@[simp]
/--
theorem `divX_C` / 定理 `divX_C`

English:
theorem divX_C
  given: (a : R)
  statement: divX (C a) = 0
  proof: ext fun n => by simp [coeff_divX]

中文:
定理 divX_C
  条件: (a : R)
  结论: divX (C a) = 0
  证明: ext fun n => by simp [coeff_divX]

Depends on / 依赖: coeff_divX
-/
theorem divX_C (a : R) : divX (C a) = 0 :=
  ext fun n => by simp [coeff_divX]

/--
theorem `divX_eq_zero_iff` / 定理 `divX_eq_zero_iff`

English:
theorem divX_eq_zero_iff
  statement: divX p = 0 ↔ p = C (p.coeff 0)
  proof: ⟨fun h => by simpa [eq_comm, h] using divX_mul_X_add p, fun h => by rw [h, divX_C]⟩

中文:
定理 divX_eq_zero_iff
  结论: divX p = 0 ↔ p = C (p.coeff 0)
  证明: ⟨fun h => by simpa [eq_comm, h] using divX_mul_X_add p, fun h => by rw [h, divX_C]⟩

Depends on / 依赖: divX_C, divX_mul_X_add, eq_comm
-/
theorem divX_eq_zero_iff : divX p = 0 ↔ p = C (p.coeff 0) :=
  ⟨fun h => by simpa [eq_comm, h] using divX_mul_X_add p, fun h => by rw [h, divX_C]⟩

/--
theorem `divX_add` / 定理 `divX_add`

English:
theorem divX_add
  statement: divX (p + q) = divX p + divX q
  proof: ext by simp

@[simp]

中文:
定理 divX_add
  结论: divX (p + q) = divX p + divX q
  证明: ext by simp

@[simp]

Depends on / 依赖: CanLift, Subsemiring
-/
theorem divX_add : divX (p + q) = divX p + divX q :=
ext by simp

@[simp]
/--
theorem `divX_zero` / 定理 `divX_zero`

English:
theorem divX_zero
  statement: divX (0 : R[X]) = 0
  proof: leadingCoeff_eq_zero.mp rfl

@[simp]

中文:
定理 divX_zero
  结论: divX (0 : R[X]) = 0
  证明: leadingCoeff_eq_zero.mp rfl

@[simp]

Depends on / 依赖: leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp
-/
theorem divX_zero : divX (0 : R[X]) = 0 := leadingCoeff_eq_zero.mp rfl

@[simp]
/--
theorem `divX_one` / 定理 `divX_one`

English:
theorem divX_one
  statement: divX (1 : R[X]) = 0
  proof: by
  ext
  simpa only [coeff_divX, coeff_zero] using! coeff_one

@[simp]

中文:
定理 divX_one
  结论: divX (1 : R[X]) = 0
  证明: by
  ext
  simpa only [coeff_divX, coeff_zero] using! coeff_one

@[simp]

Depends on / 依赖: coeff_divX, coeff_one, coeff_zero
-/
theorem divX_one : divX (1 : R[X]) = 0 := by
  ext
  simpa only [coeff_divX, coeff_zero] using! coeff_one

@[simp]
/--
theorem `divX_C_mul` / 定理 `divX_C_mul`

English:
theorem divX_C_mul
  statement: divX (C a * p) = C a * divX p
  proof: by
  ext
  simp

中文:
定理 divX_C_mul
  结论: divX (C a * p) = C a * divX p
  证明: by
  ext
  simp
-/
theorem divX_C_mul : divX (C a * p) = C a * divX p := by
  ext
  simp

/--
theorem `divX_X_pow` / 定理 `divX_X_pow`

English:
theorem divX_X_pow
  statement: divX (X ^ n : R[X]) = if (n = 0) then 0 else X ^ (n - 1)
  proof: by
  cases n
  · simp
  · ext n
    simp [coeff_X_pow]

中文:
定理 divX_X_pow
  结论: divX (X ^ n : R[X]) = if (n = 0) then 0 else X ^ (n - 1)
  证明: by
  cases n
  · simp
  · ext n
    simp [coeff_X_pow]

Depends on / 依赖: coeff_X_pow
-/
theorem divX_X_pow : divX (X ^ n : R[X]) = if (n = 0) then 0 else X ^ (n - 1) := by
  cases n
  · simp
  · ext n
    simp [coeff_X_pow]

/-- `divX` as an additive homomorphism. -/
noncomputable
/--
Definition of `divX_hom` / `divX_hom` 的定义

English:
definition divX_hom
  signature: : R[X] ->+ R[X]
  body: { toFun := divX
    map_zero' := divX_zero
    map_add' := fun _ _ => divX_add }

中文:
定义 divX_hom
  签名: : R[X] ->+ R[X]
  定义体: { toFun := divX
    map_zero' := divX_zero
    map_add' := fun _ _ => divX_add }

Depends on / 依赖: divX_add, divX_zero, map_add, map_zero
-/
def divX_hom : R[X] ->+ R[X] :=
  { toFun := divX
    map_zero' := divX_zero
    map_add' := fun _ _ => divX_add }

/--
theorem `divX_hom_toFun` / 定理 `divX_hom_toFun`

English:
theorem divX_hom_toFun
  statement: divX_hom p = divX p
  proof: rfl

中文:
定理 divX_hom_toFun
  结论: divX_hom p = divX p
  证明: rfl
-/
@[simp] theorem divX_hom_toFun : divX_hom p = divX p := rfl

/--
theorem `natDegree_divX_eq_natDegree_tsub_one` / 定理 `natDegree_divX_eq_natDegree_tsub_one`

English:
theorem natDegree_divX_eq_natDegree_tsub_one
  statement: p.divX.natDegree = p.natDegree - 1
  proof: by
  apply map_natDegree_eq_sub (φ := divX_hom)
  · intro f
    simpa [divX_hom, divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intro n c c0
    rw [← C_mul_X_pow_eq_monomial]; rw [divX_hom_toFun]; rw [divX_C_mul]; rw [divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0

中文:
定理 natDegree_divX_eq_natDegree_tsub_one
  结论: p.divX.natDegree = p.natDegree - 1
  证明: by
  apply map_natDegree_eq_sub (φ := divX_hom)
  · intro f
    simpa [divX_hom, divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intro n c c0
    rw [← C_mul_X_pow_eq_monomial]; rw [divX_hom_toFun]; rw [divX_C_mul]; rw [divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0

Depends on / 依赖: C_mul_X_pow_eq_monomial, divX_C_mul, divX_X_pow, divX_eq_zero_iff, divX_hom, divX_hom_toFun, eq_C_of_natDegree_eq_zero, map_natDegree_eq_sub, natDegree_C_mul_X_pow, split_ifs
-/
theorem natDegree_divX_eq_natDegree_tsub_one : p.divX.natDegree = p.natDegree - 1 := by
  apply map_natDegree_eq_sub (φ := divX_hom)
  · intro f
    simpa [divX_hom, divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intro n c c0
    rw [← C_mul_X_pow_eq_monomial]; rw [divX_hom_toFun]; rw [divX_C_mul]; rw [divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0

/--
theorem `natDegree_divX_le` / 定理 `natDegree_divX_le`

English:
theorem natDegree_divX_le
  statement: p.divX.natDegree <= p.natDegree
  proof: natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)

中文:
定理 natDegree_divX_le
  结论: p.divX.natDegree <= p.natDegree
  证明: natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)

Depends on / 依赖: Nat.pred_le, natDegree_divX_eq_natDegree_tsub_one, natDegree_divX_eq_natDegree_tsub_one.trans_le, pred_le, trans_le
-/
theorem natDegree_divX_le : p.divX.natDegree <= p.natDegree :=
  natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)

/--
theorem `divX_C_mul_X_pow` / 定理 `divX_C_mul_X_pow`

English:
theorem divX_C_mul_X_pow
  statement: divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n - 1)
  proof: by
  simp only [divX_C_mul, divX_X_pow, mul_ite, mul_zero]

中文:
定理 divX_C_mul_X_pow
  结论: divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n - 1)
  证明: by
  simp only [divX_C_mul, divX_X_pow, mul_ite, mul_zero]

Depends on / 依赖: divX_C_mul, divX_X_pow, mul_ite, mul_zero
-/
theorem divX_C_mul_X_pow : divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n - 1) := by
  simp only [divX_C_mul, divX_X_pow, mul_ite, mul_zero]

/--
theorem `degree_divX_lt` / 定理 `degree_divX_lt`

English:
theorem degree_divX_lt
  given: (hp0 : p != 0)
  statement: (divX p).degree < p.degree
  proof: by
  have := Nontrivial.of_polynomial_ne hp0
  calc
    degree (divX p) < (divX p * X + C (p.coeff 0)).degree :=
      if h : degree p <= 0 then by
        have h' : C (p.coeff 0) != 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h]; rw [divX_C]; rw [degree_zero]; rw [zero_mul]; rw [zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : divX p != 0 := by
          simpa [divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (divX p) * leadingCoeff X != 0 := by simpa
        have : degree (C (p.coeff 0)) < degree (divX p * X) :=
          calc
            degree (C (p.coeff 0)) <= 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (X : R[X]) := degree_X.symm
            _ <= degree (divX p * X) := by
              rw [← zero_add (degree X)]; rw [degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)

中文:
定理 degree_divX_lt
  条件: (hp0 : p != 0)
  结论: (divX p).degree < p.degree
  证明: by
  have := Nontrivial.of_polynomial_ne hp0
  calc
    degree (divX p) < (divX p * X + C (p.coeff 0)).degree :=
      if h : degree p <= 0 then by
        have h' : C (p.coeff 0) != 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h]; rw [divX_C]; rw [degree_zero]; rw [zero_mul]; rw [zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : divX p != 0 := by
          simpa [divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (divX p) * leadingCoeff X != 0 := by simpa
        have : degree (C (p.coeff 0)) < degree (divX p * X) :=
          calc
            degree (C (p.coeff 0)) <= 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (X : R[X]) := degree_X.symm
            _ <= degree (divX p * X) := by
              rw [← zero_add (degree X)]; rw [degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)

Depends on / 依赖: Ne.symm, Nontrivial, Nontrivial.of_polynomial_ne, bot_le, degree, degree_eq_bot, degree_le_zero_iff, degree_zero, divX_C, divX_eq_zero_iff, eq_C_of_degree_le_zero, leadingCoeff, lt_of_le_of_ne, not_le, of_polynomial_ne, p.coeff, zero_add, zero_mul
-/
theorem degree_divX_lt (hp0 : p != 0) : (divX p).degree < p.degree := by
  have := Nontrivial.of_polynomial_ne hp0
  calc
    degree (divX p) < (divX p * X + C (p.coeff 0)).degree :=
      if h : degree p <= 0 then by
        have h' : C (p.coeff 0) != 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h]; rw [divX_C]; rw [degree_zero]; rw [zero_mul]; rw [zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : divX p != 0 := by
          simpa [divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (divX p) * leadingCoeff X != 0 := by simpa
        have : degree (C (p.coeff 0)) < degree (divX p * X) :=
          calc
            degree (C (p.coeff 0)) <= 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (X : R[X]) := degree_X.symm
            _ <= degree (divX p * X) := by
              rw [← zero_add (degree X)]; rw [degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_elim]
/--
Definition of `recOnHorner` / `recOnHorner` 的定义

English:
definition recOnHorner
  signature: {M : R[X] -> Sort*} (p : R[X]) (M0 : M 0)
  body: letI := Classical.decEq R
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    rw [← divX_mul_X_add p] at *
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0]; rw [C_0]; rw [add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by p.degree

中文:
定义 recOnHorner
  签名: {M : R[X] -> 类型层*} (p : R[X]) (M0 : M 0)
  定义体: letI := Classical.decEq R
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    rw [← divX_mul_X_add p] at *
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0]; rw [C_0]; rw [add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by p.degree

Depends on / 依赖: Classical, Classical.decEq, add_zero, coeff_mul_X_zero, degree, degree_divX_lt, divX_mul_X_add, p.degre, recOnHorner, termination_by, zero_mul
-/
noncomputable def recOnHorner {M : R[X] -> Sort*} (p : R[X]) (M0 : M 0)
    (MC : forall p a, coeff p 0 = 0 -> a != 0 -> M p -> M (p + C a))
    (MX : forall p, p != 0 -> M p -> M (p * X)) : M p :=
  letI := Classical.decEq R
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    rw [← divX_mul_X_add p] at *
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0]; rw [C_0]; rw [add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by p.degree

/-- A property holds for all polynomials of positive `degree` with coefficients in a semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,

with appropriate restrictions on each term.

See `natDegree_ne_zero_induction_on` for a similar statement involving no explicit multiplication.
-/
@[elab_as_elim]
/--
theorem `degree_pos_induction_on` / 定理 `degree_pos_induction_on`

English:
theorem degree_pos_induction_on
  statement: {P : R[X] -> Prop} (p : R[X]) (h0 : 0 < degree p)
  proof: recOnHorner p (fun h => by rw [degree_zero] at h; exact absurd h (by decide))
    (fun p a heq0 _ ih h0 =>
      (have : 0 < degree p :=
        (lt_of_not_ge fun h =>
not_lt_of_ge (degree_C_le (a := a))
            by rwa [eq_C_of_degree_le_zero h, ← C_add, heq0, zero_add] at h0)
      hadd this (ih this)))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        exact hC fun h : coeff p 0 = 0 => by simp [h] at h0')
    h0

中文:
定理 degree_pos_induction_on
  结论: {P : R[X] -> 命题} (p : R[X]) (h0 : 0 < degree p)
  证明: recOnHorner p (fun h => by rw [degree_zero] at h; exact absurd h (by decide))
    (fun p a heq0 _ ih h0 =>
      (have : 0 < degree p :=
        (lt_of_not_ge fun h =>
not_lt_of_ge (degree_C_le (a := a))
            by rwa [eq_C_of_degree_le_zero h, ← C_add, heq0, zero_add] at h0)
      hadd this (ih this)))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        exact hC fun h : coeff p 0 = 0 => by simp [h] at h0')
    h0

Depends on / 依赖: C_add, absurd, degree, degree_C_le, degree_zero, eq_C_of_degree_le_zero, le_of_not_gt, lt_of_not_ge, not_lt_of_ge, recOnHorner, zero_add
-/
theorem degree_pos_induction_on {P : R[X] -> Prop} (p : R[X]) (h0 : 0 < degree p)
    (hC : forall {a}, a != 0 -> P (C a * X)) (hX : forall {p}, 0 < degree p -> P p -> P (p * X))
    (hadd : forall {p} {a}, 0 < degree p -> P p -> P (p + C a)) : P p :=
  recOnHorner p (fun h => by rw [degree_zero] at h; exact absurd h (by decide))
    (fun p a heq0 _ ih h0 =>
      (have : 0 < degree p :=
        (lt_of_not_ge fun h =>
not_lt_of_ge (degree_C_le (a := a))
            by rwa [eq_C_of_degree_le_zero h, ← C_add, heq0, zero_add] at h0)
      hadd this (ih this)))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        exact hC fun h : coeff p 0 = 0 => by simp [h] at h0')
    h0

/-- A property holds for all polynomials of non-zero `natDegree` with coefficients in a
semiring `R` if it holds for
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
* `p + q`, with `p, q ∈ R[X]`,
* monomials with nonzero coefficient and non-zero exponent,

with appropriate restrictions on each term.

Note that multiplication is "hidden" in the assumption on monomials, so there is no explicit
multiplication in the statement.
See `degree_pos_induction_on` for a similar statement involving more explicit multiplications.
-/
@[elab_as_elim]
/--
theorem `natDegree_ne_zero_induction_on` / 定理 `natDegree_ne_zero_induction_on`

English:
theorem natDegree_ne_zero_induction_on
  statement: {M : R[X] -> Prop} {f : R[X]} (f0 : f.natDegree != 0)
  proof: by
  suffices f.natDegree = 0 ∨ M f from Or.recOn this (fun h => (f0 h).elim) id
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
  · rintro p q (hp | hp) (hq | hq)
    · refine Or.inl ?_
      rw [eq_C_of_natDegree_eq_zero hp]; rw [eq_C_of_natDegree_eq_zero hq]; rw [← C_add]; rw [natDegree_C]
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hp]
      exact h_C_add hq
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hq]; rw [add_comm]
      exact h_C_add hp
    · exact Or.inr (h_add hp hq)
  · intro n a _
    by_cases a0 : a = 0
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
    · refine Or.inr ?_
      rw [C_mul_X_pow_eq_monomial]
      exact h_monomial a0 n.succ_ne_zero

中文:
定理 natDegree_ne_zero_induction_on
  结论: {M : R[X] -> 命题} {f : R[X]} (f0 : f.natDegree != 0)
  证明: by
  suffices f.natDegree = 0 ∨ M f from Or.recOn this (fun h => (f0 h).elim) id
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
  · rintro p q (hp | hp) (hq | hq)
    · refine Or.inl ?_
      rw [eq_C_of_natDegree_eq_zero hp]; rw [eq_C_of_natDegree_eq_zero hq]; rw [← C_add]; rw [natDegree_C]
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hp]
      exact h_C_add hq
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hq]; rw [add_comm]
      exact h_C_add hp
    · exact Or.inr (h_add hp hq)
  · intro n a _
    by_cases a0 : a = 0
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
    · refine Or.inr ?_
      rw [C_mul_X_pow_eq_monomial]
      exact h_monomial a0 n.succ_ne_zero

Depends on / 依赖: C_add, Or.inl, Or.inr, Or.recOn, Polynomial, Polynomial.induction_on, add_comm, eq_C_of_natDegree_eq_zero, f.natDegree, h_C_add, h_add, induction_on, natDegree, natDegree_C
-/
theorem natDegree_ne_zero_induction_on {M : R[X] -> Prop} {f : R[X]} (f0 : f.natDegree != 0)
    (h_C_add : forall {a p}, M p -> M (C a + p)) (h_add : forall {p q}, M p -> M q -> M (p + q))
    (h_monomial : forall {n : Nat} {a : R}, a != 0 -> n != 0 -> M (monomial n a)) : M f := by
  suffices f.natDegree = 0 ∨ M f from Or.recOn this (fun h => (f0 h).elim) id
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
  · rintro p q (hp | hp) (hq | hq)
    · refine Or.inl ?_
      rw [eq_C_of_natDegree_eq_zero hp]; rw [eq_C_of_natDegree_eq_zero hq]; rw [← C_add]; rw [natDegree_C]
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hp]
      exact h_C_add hq
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hq]; rw [add_comm]
      exact h_C_add hp
    · exact Or.inr (h_add hp hq)
  · intro n a _
    by_cases a0 : a = 0
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
    · refine Or.inr ?_
      rw [C_mul_X_pow_eq_monomial]
      exact h_monomial a0 n.succ_ne_zero

end Semiring

end Polynomial
