/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

Generalize linear independence to:
  * `IsCancelAdd` semirings
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

@[expose] public section

open Module Submodule
open scoped Function

variable (R : Type*)

namespace Polynomial

/--
Definition of `Sequence` / `Sequence` 的定义

English:
structure Sequence
  parameters: [Semiring R]
  axioms and operations (2):
    - elems' : Nat -> R[X]
    - degree_eq'((i : Nat)) : (elems' i).degree = i

中文:
结构 序列
  参数: [半环 R]
  公理与运算 (2 个):
    - elems' : 自然数 -> R[X]
    - degree_eq'((i : 自然数)) : (elems' i).degree = i
-/
structure Sequence [Semiring R] where
  /-- The `i`-th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : Nat -> R[X]
  /-- The `i`-th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : Nat) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/--
Instance `coeFun` / 实例 `coeFun`

English:
instance coeFun
  signature: [Semiring R]
  body: ⟨Sequence.elems'⟩

中文:
实例 coeFun
  签名: [半环 R]
  定义体: ⟨Sequence.elems'⟩

Depends on / 依赖: Sequence, Sequence.elems
-/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ => Nat -> R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

/-- `S i` has degree `i`. -/
@[simp]
/--
lemma `degree_eq` / 引理 `degree_eq`

English:
lemma degree_eq
  given: (i : Nat)
  statement: (S i).degree = i
  proof: S.degree_eq' i

中文:
引理 degree_eq
  条件: (i : 自然数)
  结论: (S i).degree = i
  证明: S.degree_eq' i

Depends on / 依赖: S.degree_eq, degree_eq
-/
lemma degree_eq (i : Nat) : (S i).degree = i := S.degree_eq' i

/-- `S i` has `natDegree` `i`. -/
@[simp]
/--
lemma `natDegree_eq` / 引理 `natDegree_eq`

English:
lemma natDegree_eq
  given: (i : Nat)
  statement: (S i).natDegree = i
  proof: natDegree_eq_of_degree_eq_some S.degree_eq i

中文:
引理 natDegree_eq
  条件: (i : 自然数)
  结论: (S i).natDegree = i
  证明: natDegree_eq_of_degree_eq_some S.degree_eq i

Depends on / 依赖: S.degree_eq, degree_eq, natDegree_eq_of_degree_eq_some
-/
lemma natDegree_eq (i : Nat) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some S.degree_eq i

/-- No polynomial in the sequence is zero. -/
@[simp]
/--
lemma `ne_zero` / 引理 `ne_zero`

English:
lemma ne_zero
  given: (i : Nat)
  statement: S i != 0
  proof: degree_ne_bot.mp by simp [S.degree_eq i]

中文:
引理 ne_zero
  条件: (i : 自然数)
  结论: S i != 0
  证明: degree_ne_bot.mp by simp [S.degree_eq i]

Depends on / 依赖: S.degree_eq, degree_eq, degree_ne_bot, degree_ne_bot.mp
-/
lemma ne_zero (i : Nat) : S i != 0 := degree_ne_bot.mp by simp [S.degree_eq i]

/--
lemma `degree_strictMono` / 引理 `degree_strictMono`

English:
lemma degree_strictMono
  statement: StrictMono degree ∘ S
  proof: fun _ _ => by simp

中文:
引理 degree_strictMono
  结论: 严格递增 degree ∘ S
  证明: fun _ _ => by simp
-/
lemma degree_strictMono : StrictMono degree ∘ S := fun _ _ => by simp

/--
lemma `natDegree_strictMono` / 引理 `natDegree_strictMono`

English:
lemma natDegree_strictMono
  statement: StrictMono natDegree ∘ S
  proof: fun _ _ => by simp

中文:
引理 natDegree_strictMono
  结论: 严格递增 natDegree ∘ S
  证明: fun _ _ => by simp
-/
lemma natDegree_strictMono : StrictMono natDegree ∘ S := fun _ _ => by simp

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/--
lemma `span_degreeLT` / 引理 `span_degreeLT`

English:
lemma span_degreeLT
  given: {m : Nat} (hCoeff : forall i < m, IsUnit (S i).leadingCoeff)
  proof: by
  apply span_eq_of_le
  · intro P hP
    obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hP
    rw [SetLike.mem_coe]; rw [Polynomial.mem_degreeLT]; rw [S.degree_eq i]; rw [Nat.cast_lt]
    exact Set.mem_Iio.mp hi
  intro P hP
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases! p_ne_zero : P = 0
    · simp [p_ne_zero]
    have hn : n < m := by
      rw [Polynomial.mem_degreeLT] at hP
      have := Polynomial.degree_eq_natDegree p_ne_zero
      aesop
    -- let u be the inverse of `S n`'s leading coefficient
obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp hCoeff n hn
    -- We'll show `P` is the difference of two terms in the span:
    -- a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    -- and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head in span R (S '' Set.Iio m) := by
      have in_span : S n in span R (S '' Set.Iio m) := subset_span ⟨n, by simp [hn], rfl⟩
      have smul_span := smul_mem (span R (S '' Set.Iio m)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
.mp apply sub_mem_iff_left _ head_mem_span
    -- so let's prove the tail has degree less than `n`
    suffices tail.degree < n by
      refine ih tail.natDegree ((natDegree_lt_iff_degree_lt tail_eq_zero).mpr this) ?_ rfl
      grw [(Nat.cast_lt (α := WithBot Nat)).mpr hn] at this
      rwa [Polynomial.mem_degreeLT]
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular, IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n hn).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same]; rw [S.degree_eq n]; rw [← hp]; rw [eq_comm]; rw [← degree_eq_natDegree p_ne_zero]; rw [hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree by
      grind [degree_eq_bot]
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree p_ne_zero]; rw [head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rw [coeff_smul]; rw [coeff_smul]; rw [coeff_natDegree]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [rightinv]; rw [mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt_left head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

中文:
引理 span_degreeLT
  条件: {m : 自然数} (hCoeff : 对任意 i < m, 是单位 (S i).leadingCoeff)
  证明: by
  apply span_eq_of_le
  · intro P hP
    obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hP
    rw [SetLike.mem_coe]; rw [Polynomial.mem_degreeLT]; rw [S.degree_eq i]; rw [Nat.cast_lt]
    exact Set.mem_Iio.mp hi
  intro P hP
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases! p_ne_zero : P = 0
    · simp [p_ne_zero]
    have hn : n < m := by
      rw [Polynomial.mem_degreeLT] at hP
      have := Polynomial.degree_eq_natDegree p_ne_zero
      aesop
    -- let u be the inverse of `S n`'s leading coefficient
obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp hCoeff n hn
    -- We'll show `P` is the difference of two terms in the span:
    -- a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    -- and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head in span R (S '' Set.Iio m) := by
      have in_span : S n in span R (S '' Set.Iio m) := subset_span ⟨n, by simp [hn], rfl⟩
      have smul_span := smul_mem (span R (S '' Set.Iio m)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
.mp apply sub_mem_iff_left _ head_mem_span
    -- so let's prove the tail has degree less than `n`
    suffices tail.degree < n by
      refine ih tail.natDegree ((natDegree_lt_iff_degree_lt tail_eq_zero).mpr this) ?_ rfl
      grw [(Nat.cast_lt (α := WithBot Nat)).mpr hn] at this
      rwa [Polynomial.mem_degreeLT]
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular, IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n hn).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same]; rw [S.degree_eq n]; rw [← hp]; rw [eq_comm]; rw [← degree_eq_natDegree p_ne_zero]; rw [hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree by
      grind [degree_eq_bot]
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree p_ne_zero]; rw [head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rw [coeff_smul]; rw [coeff_smul]; rw [coeff_natDegree]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [rightinv]; rw [mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt_left head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

Depends on / 依赖: Nat.cast_lt, Polynomial, Polynomial.mem_degreeLT, S.degree_eq, Set.mem_Iio.mp, Set.mem_image, SetLike, SetLike.mem_coe, cast_lt, degree_eq, mem_Iio, mem_coe, mem_degreeLT, mem_image, span_eq_of_le
-/
lemma span_degreeLT {m : Nat} (hCoeff : forall i < m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iio m) = degreeLT R m := by
  apply span_eq_of_le
  · intro P hP
    obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hP
    rw [SetLike.mem_coe]; rw [Polynomial.mem_degreeLT]; rw [S.degree_eq i]; rw [Nat.cast_lt]
    exact Set.mem_Iio.mp hi
  intro P hP
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases! p_ne_zero : P = 0
    · simp [p_ne_zero]
    have hn : n < m := by
      rw [Polynomial.mem_degreeLT] at hP
      have := Polynomial.degree_eq_natDegree p_ne_zero
      aesop
    -- let u be the inverse of `S n`'s leading coefficient
obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp hCoeff n hn
    -- We'll show `P` is the difference of two terms in the span:
    -- a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    -- and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head in span R (S '' Set.Iio m) := by
      have in_span : S n in span R (S '' Set.Iio m) := subset_span ⟨n, by simp [hn], rfl⟩
      have smul_span := smul_mem (span R (S '' Set.Iio m)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
.mp apply sub_mem_iff_left _ head_mem_span
    -- so let's prove the tail has degree less than `n`
    suffices tail.degree < n by
      refine ih tail.natDegree ((natDegree_lt_iff_degree_lt tail_eq_zero).mpr this) ?_ rfl
      grw [(Nat.cast_lt (α := WithBot Nat)).mpr hn] at this
      rwa [Polynomial.mem_degreeLT]
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular, IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n hn).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same]; rw [S.degree_eq n]; rw [← hp]; rw [eq_comm]; rw [← degree_eq_natDegree p_ne_zero]; rw [hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree by
      grind [degree_eq_bot]
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree p_ne_zero]; rw [head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rw [coeff_smul]; rw [coeff_smul]; rw [coeff_natDegree]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [rightinv]; rw [mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt_left head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

/--
lemma `span_degreeLE` / 引理 `span_degreeLE`

English:
lemma span_degreeLE
  given: {m : Nat} (hCoeff : forall i <= m, IsUnit (S i).leadingCoeff)
  proof: by
  rw [← Set.Iio_succ_eq_Iic]; rw [span_degreeLT _ (fun i hi => hCoeff i (Order.lt_succ_iff.mp hi))]
  simp [← Polynomial.degreeLT_succ_eq_degreeLE]

中文:
引理 span_degreeLE
  条件: {m : 自然数} (hCoeff : 对任意 i <= m, 是单位 (S i).leadingCoeff)
  证明: by
  rw [← Set.Iio_succ_eq_Iic]; rw [span_degreeLT _ (fun i hi => hCoeff i (Order.lt_succ_iff.mp hi))]
  simp [← Polynomial.degreeLT_succ_eq_degreeLE]

Depends on / 依赖: Iio_succ_eq_Iic, Order.lt_succ_iff.mp, Polynomial, Polynomial.degreeLT_succ_eq_degreeLE, Set.Iio_succ_eq_Iic, degreeLT_succ_eq_degreeLE, hCoeff, lt_succ_iff, span_degreeLT
-/
lemma span_degreeLE {m : Nat} (hCoeff : forall i <= m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iic m) = degreeLE R m := by
  rw [← Set.Iio_succ_eq_Iic]; rw [span_degreeLT _ (fun i hi => hCoeff i (Order.lt_succ_iff.mp hi))]
  simp [← Polynomial.degreeLT_succ_eq_degreeLE]

/--
lemma `span` / 引理 `span`

English:
lemma span
  given: (hCoeff : forall i, IsUnit (S i).leadingCoeff)
  statement: span R (Set.range S) = ⊤
  proof: by
  rw [eq_top_iff']
  intro P
  by_cases! p_ne_zero : P = 0
  · simp [p_ne_zero]
  suffices P in span R (S '' Set.Iio (P.natDegree + 1)) from (span_mono (by simp)) this
  rw [span_degreeLT _ (by grind)]; rw [Polynomial.mem_degreeLT]; rw [← natDegree_lt_iff_degree_lt p_ne_zero]
  simp

中文:
引理 span
  条件: (hCoeff : 对任意 i, 是单位 (S i).leadingCoeff)
  结论: span R (集合.range S) = ⊤
  证明: by
  rw [eq_top_iff']
  intro P
  by_cases! p_ne_zero : P = 0
  · simp [p_ne_zero]
  suffices P in span R (S '' Set.Iio (P.natDegree + 1)) from (span_mono (by simp)) this
  rw [span_degreeLT _ (by grind)]; rw [Polynomial.mem_degreeLT]; rw [← natDegree_lt_iff_degree_lt p_ne_zero]
  simp
-/
protected lemma span (hCoeff : forall i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ := by
  rw [eq_top_iff']
  intro P
  by_cases! p_ne_zero : P = 0
  · simp [p_ne_zero]
  suffices P in span R (S '' Set.Iio (P.natDegree + 1)) from (span_mono (by simp)) this
  rw [span_degreeLT _ (by grind)]; rw [Polynomial.mem_degreeLT]; rw [← natDegree_lt_iff_degree_lt p_ne_zero]
  simp

section IsDomain

variable [IsDomain R]

/--
lemma `linearIndependent` / 引理 `linearIndependent`

English:
lemma linearIndependent
  proof: linearIndependent_iff'.mpr fun s g eqzero i hi => by
  by_cases hsupzero : s.sup (fun i => (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i => (g i • S i).degree)
exact (smul_eq_zero_iff_left (S.ne_zero i)).mp degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i in s ∧ g i • S i != 0}.Pairwise (Ne on fun i => (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x != 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y != 0 := (smul_ne_zero_iff.mp hy).1
.right have rx : IsRightRegular (S x).leadingCoeff := IsRegular.of_ne_zero (by simp)
.right have ry : IsRightRegular (S y).leadingCoeff := IsRegular.of_ne_zero (by simp)
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : exists n, (s.sup fun i => (g i • S i).degree) = n := exists_eq'
.elim refine degree_ne_bot.mp ?_ eqzero
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
.trans_ne (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm exact hsum.trans hn

中文:
引理 linearIndependent
  证明: linearIndependent_iff'.mpr fun s g eqzero i hi => by
  by_cases hsupzero : s.sup (fun i => (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i => (g i • S i).degree)
exact (smul_eq_zero_iff_left (S.ne_zero i)).mp degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i in s ∧ g i • S i != 0}.Pairwise (Ne on fun i => (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x != 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y != 0 := (smul_ne_zero_iff.mp hy).1
.right have rx : IsRightRegular (S x).leadingCoeff := IsRegular.of_ne_zero (by simp)
.right have ry : IsRightRegular (S y).leadingCoeff := IsRegular.of_ne_zero (by simp)
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : exists n, (s.sup fun i => (g i • S i).degree) = n := exists_eq'
.elim refine degree_ne_bot.mp ?_ eqzero
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
.trans_ne (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm exact hsum.trans hn

Depends on / 依赖: Finset, Finset.le_sup, Pairwise, S.ne_zero, degree, degree_eq_bot, degree_eq_bot.mp, eq_bot_mono, eqzero, hpairwise, hsupzero, le_sup, linearIndependent_iff, ne_zero, s.sup, smul_eq_zero_iff_left, smul_ne_zero_iff, smul_ne_zero_iff.mp
-/
lemma linearIndependent :
LinearIndependent R S := linearIndependent_iff'.mpr fun s g eqzero i hi => by
  by_cases hsupzero : s.sup (fun i => (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i => (g i • S i).degree)
exact (smul_eq_zero_iff_left (S.ne_zero i)).mp degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i in s ∧ g i • S i != 0}.Pairwise (Ne on fun i => (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x != 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y != 0 := (smul_ne_zero_iff.mp hy).1
.right have rx : IsRightRegular (S x).leadingCoeff := IsRegular.of_ne_zero (by simp)
.right have ry : IsRightRegular (S y).leadingCoeff := IsRegular.of_ne_zero (by simp)
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : exists n, (s.sup fun i => (g i • S i).degree) = n := exists_eq'
.elim refine degree_ne_bot.mp ?_ eqzero
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
.trans_ne (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm exact hsum.trans hn

variable (hCoeff : forall i, IsUnit (S i).leadingCoeff)

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Basis Nat R R[X]
  body: Basis.mk S.linearIndependent eq_top_iff.mp S.span hCoeff

中文:
定义 basis
  签名: : 基 自然数 R R[X]
  定义体: Basis.mk S.linearIndependent eq_top_iff.mp S.span hCoeff

Depends on / 依赖: Basis.mk, S.linearIndependent, S.span, eq_top_iff, eq_top_iff.mp, hCoeff, linearIndependent
-/
noncomputable def basis : Basis Nat R R[X] :=
Basis.mk S.linearIndependent eq_top_iff.mp S.span hCoeff

/-- The `i`-th basis vector is the `i`-th polynomial in the sequence. -/
@[simp]
/--
lemma `basis_eq_self` / 引理 `basis_eq_self`

English:
lemma basis_eq_self
  given: (i : Nat)
  statement: S.basis hCoeff i = S i
  proof: Basis.mk_apply _ _ _

中文:
引理 basis_eq_self
  条件: (i : 自然数)
  结论: S.basis hCoeff i = S i
  证明: Basis.mk_apply _ _ _

Depends on / 依赖: Basis.mk_apply, mk_apply
-/
lemma basis_eq_self (i : Nat) : S.basis hCoeff i = S i := Basis.mk_apply _ _ _

/--
lemma `basis_degree_strictMono` / 引理 `basis_degree_strictMono`

English:
lemma basis_degree_strictMono
  statement: StrictMono degree ∘ (S.basis hCoeff)
  proof: fun _ _ => by simp

中文:
引理 basis_degree_strictMono
  结论: 严格递增 degree ∘ (S.basis hCoeff)
  证明: fun _ _ => by simp
-/
lemma basis_degree_strictMono : StrictMono degree ∘ (S.basis hCoeff) := fun _ _ => by simp

/--
lemma `basis_natDegree_strictMono` / 引理 `basis_natDegree_strictMono`

English:
lemma basis_natDegree_strictMono
  statement: StrictMono natDegree ∘ (S.basis hCoeff)
  proof: fun _ _ => by simp

中文:
引理 basis_natDegree_strictMono
  结论: 严格递增 natDegree ∘ (S.basis hCoeff)
  证明: fun _ _ => by simp
-/
lemma basis_natDegree_strictMono : StrictMono natDegree ∘ (S.basis hCoeff) := fun _ _ => by simp

end IsDomain

end Ring

end Sequence

end Polynomial
