/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings. Assume that `K` is commutative. If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ R[X]` the "mathematical" expression `b ^ f.natDegree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/

@[expose] public section


open Polynomial Finset

open Polynomial

section DenomsClearable

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R ->+* K}
variable {a b : R} {bi : K}

-- TODO: use hypothesis (ub : IsUnit (i b)) to work with localizations.
/--
Definition of `DenomsClearable` / `DenomsClearable` 的定义

English:
definition DenomsClearable
  signature: (a b : R) (N : Nat) (f : R[X]) (i : R ->+* K)
  body: exists (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

中文:
定义 DenomsClearable
  签名: (a b : R) (N : 自然数) (f : R[X]) (i : R ->+* K)
  定义体: exists (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

Depends on / 依赖: f.map
-/
def DenomsClearable (a b : R) (N : Nat) (f : R[X]) (i : R ->+* K) : Prop :=
  exists (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

/--
theorem `denomsClearable_zero` / 定理 `denomsClearable_zero`

English:
theorem denomsClearable_zero
  given: (N : Nat) (a : R) (bu : bi * i b = 1)
  statement: DenomsClearable a b N 0 i
  proof: ⟨0, bi, bu, by
    simp only [eval_zero, map_zero, mul_zero, Polynomial.map_zero]⟩

中文:
定理 denomsClearable_zero
  条件: (N : 自然数) (a : R) (bu : bi * i b = 1)
  结论: DenomsClearable a b N 0 i
  证明: ⟨0, bi, bu, by
    simp only [eval_zero, map_zero, mul_zero, Polynomial.map_zero]⟩

Depends on / 依赖: Polynomial, Polynomial.map_zero, eval_zero, map_zero, mul_zero
-/
theorem denomsClearable_zero (N : Nat) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i :=
  ⟨0, bi, bu, by
    simp only [eval_zero, map_zero, mul_zero, Polynomial.map_zero]⟩

/--
theorem `denomsClearable_C_mul_X_pow` / 定理 `denomsClearable_C_mul_X_pow`

English:
theorem denomsClearable_C_mul_X_pow
  statement: {N : Nat} (a : R) (bu : bi * i b = 1) {n : Nat} (r : R)
  proof: by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial]; rw [map_monomial]; rw [← C_mul_X_pow_eq_monomial]; rw [eval_mul]; rw [eval_pow]; rw [eval_C]
  rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [eval_X]; rw [mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv

中文:
定理 denomsClearable_C_mul_X_pow
  结论: {N : 自然数} (a : R) (bu : bi * i b = 1) {n : 自然数} (r : R)
  证明: by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial]; rw [map_monomial]; rw [← C_mul_X_pow_eq_monomial]; rw [eval_mul]; rw [eval_pow]; rw [eval_C]
  rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [eval_X]; rw [mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv

Depends on / 依赖: C_mul_X_pow_eq_monomial, conv_lhs, eval_C, eval_X, eval_mul, eval_pow, map_monomial, map_mul, map_pow, mul_assoc, mul_comm, mul_left_comm, mul_one, mul_pow, pow_add, tsub_add_cancel_of_le
-/
theorem denomsClearable_C_mul_X_pow {N : Nat} (a : R) (bu : bi * i b = 1) {n : Nat} (r : R)
    (nN : n <= N) : DenomsClearable a b N (C r * X ^ n) i := by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial]; rw [map_monomial]; rw [← C_mul_X_pow_eq_monomial]; rw [eval_mul]; rw [eval_pow]; rw [eval_C]
  rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [map_pow]; rw [eval_X]; rw [mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv_lhs => rw [← mul_one (i a), ← bu]
  simp [mul_assoc, mul_comm, mul_left_comm, pow_add, mul_pow]

/--
theorem `DenomsClearable.add` / 定理 `DenomsClearable.add`

English:
theorem DenomsClearable.add
  given: {N : Nat} {f g : R[X]}
  proof: fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [map_add]; rw [Polynomial.map_add]; rw [eval_add]; rw [mul_add]; rw [Hf]; rw [Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

中文:
定理 DenomsClearable.add
  条件: {N : 自然数} {f g : R[X]}
  证明: fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [map_add]; rw [Polynomial.map_add]; rw [eval_add]; rw [mul_add]; rw [Hf]; rw [Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

Depends on / 依赖: MulSemiringAction, Polynomial, Polynomial.map_add, SetLike, eval_add, inv_unique, map_add, mul_add, mul_comm
-/
theorem DenomsClearable.add {N : Nat} {f g : R[X]} :
    DenomsClearable a b N f i -> DenomsClearable a b N g i -> DenomsClearable a b N (f + g) i :=
  fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [map_add]; rw [Polynomial.map_add]; rw [eval_add]; rw [mul_add]; rw [Hf]; rw [Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

/--
theorem `denomsClearable_of_natDegree_le` / 定理 `denomsClearable_of_natDegree_le`

English:
theorem denomsClearable_of_natDegree_le
  given: (N : Nat) (a : R) (bu : bi * i b = 1)
  proof: induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

中文:
定理 denomsClearable_of_natDegree_le
  条件: (N : 自然数) (a : R) (bu : bi * i b = 1)
  证明: induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

Depends on / 依赖: denomsClearable_C_mul_X_pow, denomsClearable_zero, df.add, induction_with_natDegree_le
-/
theorem denomsClearable_of_natDegree_le (N : Nat) (a : R) (bu : bi * i b = 1) :
    forall f : R[X], f.natDegree <= N -> DenomsClearable a b N f i :=
  induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

/--
theorem `denomsClearable_natDegree` / 定理 `denomsClearable_natDegree`

English:
theorem denomsClearable_natDegree
  given: (i : R ->+* K) (f : R[X]) (a : R) (bu : bi * i b = 1)
  proof: denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

中文:
定理 denomsClearable_natDegree
  条件: (i : R ->+* K) (f : R[X]) (a : R) (bu : bi * i b = 1)
  证明: denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

Depends on / 依赖: denomsClearable_of_natDegree_le, f.natDegree, le_rfl, natDegree
-/
theorem denomsClearable_natDegree (i : R ->+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i :=
  denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

end DenomsClearable

open RingHom

/--
theorem `one_le_pow_mul_abs_eval_div` / 定理 `one_le_pow_mul_abs_eval_div`

English:
theorem one_le_pow_mul_abs_eval_div
  statement: {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  proof: by
  obtain ⟨ev, bi, bu, hF⟩ :=
    denomsClearable_natDegree (b := b) (algebraMap Int K) f a
      (by
        rw [eq_intCast]; rw [one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu]; rw [eq_intCast]; r

中文:
定理 one_le_pow_mul_abs_eval_div
  结论: {K : 类型} [域 K] [线性序 K] [是StrictOrdered环 K]
  证明: by
  obtain ⟨ev, bi, bu, hF⟩ :=
    denomsClearable_natDegree (b := b) (algebraMap Int K) f a
      (by
        rw [eq_intCast]; rw [one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu]; rw [eq_intCast]; r

Depends on / 依赖: Int.cast_abs, Int.cast_le, Int.cast_ne_zero, Int.cast_one, Int.cast_pos.mpr, abs_mul, abs_of_pos, algebraMap, b0.ne.symm, cast_abs, cast_le, cast_ne_zero, cast_one, cast_pos, congr_arg, denomsClearable_natDegree, div_eq_mul_inv, eq_intCast, eq_one_div_of_mul_eq_one_left, one_div
-/
theorem one_le_pow_mul_abs_eval_div {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : Int[X]} {a b : Int}
    (b0 : 0 < b) (fab : eval ((a : K) / b) (f.map (algebraMap Int K)) != 0) :
    (1 : K) <= (b : K) ^ f.natDegree * |eval ((a : K) / b) (f.map (algebraMap Int K))| := by
  obtain ⟨ev, bi, bu, hF⟩ :=
    denomsClearable_natDegree (b := b) (algebraMap Int K) f a
      (by
        rw [eq_intCast]; rw [one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu]; rw [eq_intCast]; rw [eq_intCast]; rw [abs_mul] at Fa
  rw [abs_of_pos (pow_pos (Int.cast_pos.mpr b0) _ : 0 < (b : K) ^ _)]; rw [one_div]; rw [eq_intCast] at Fa
  rw [div_eq_mul_inv]; rw [← Fa]; rw [← Int.cast_abs]; rw [← Int.cast_one]; rw [Int.cast_le]
  refine Int.le_of_lt_add_one ((lt_add_iff_pos_left 1).mpr (abs_pos.mpr fun F0 => fab ?_))
  rw [eq_one_div_of_mul_eq_one_left bu]; rw [F0]; rw [one_div]; rw [eq_intCast]; rw [Int.cast_zero]; rw [zero_eq_mul] at hF
  rcases hF with hF | hF
  · exact (not_le.mpr b0 (le_of_eq (Int.cast_eq_zero.mp (eq_zero_of_pow_eq_zero hF)))).elim
  · rwa [div_eq_mul_inv]
