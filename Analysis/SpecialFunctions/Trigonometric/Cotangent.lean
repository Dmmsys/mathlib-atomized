/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
In particular, we prove that
`π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n`
as well as the infinite sum representation of cotangent (also known as the Mittag-Leffler
expansion): `π * cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))`.
-/

public section

open Real Complex

open scoped UpperHalfPlane

local notation "Complex_Int" => integerComplement

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

/--
lemma `Complex.cot_eq_exp_ratio` / 引理 `Complex.cot_eq_exp_ratio`

English:
lemma Complex.cot_eq_exp_ratio
  given: (z : Complex)
  proof: by
  rw [Complex.cot]; rw [Complex.sin]; rw [Complex.cos]
  have h1 : exp (z * I) + exp (-z * I) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add]; rw [← Complex.exp_add]
    ring_nf
  have h2 : (exp (-z * I) - exp (z * I)) = exp (-(z * I)) * ((1 - exp (2 * I * z))) := by
    ring_nf
 

中文:
引理 Complex.cot_eq_exp_ratio
  条件: (z : Complex)
  证明: by
  rw [Complex.cot]; rw [Complex.sin]; rw [Complex.cos]
  have h1 : exp (z * I) + exp (-z * I) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add]; rw [← Complex.exp_add]
    ring_nf
  have h2 : (exp (-z * I) - exp (z * I)) = exp (-(z * I)) * ((1 - exp (2 * I * z))) := by
    ring_nf
 

Depends on / 依赖: Complex.cos, Complex.cot, Complex.exp_add, Complex.sin, exp_add, mul_add, mul_assoc, ring_nf
-/
lemma Complex.cot_eq_exp_ratio (z : Complex) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot]; rw [Complex.sin]; rw [Complex.cos]
  have h1 : exp (z * I) + exp (-z * I) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add]; rw [← Complex.exp_add]
    ring_nf
  have h2 : (exp (-z * I) - exp (z * I)) = exp (-(z * I)) * ((1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc]; rw [← Complex.exp_add]
    ring_nf
  rw [h1]; rw [h2]
  field

/--
lemma `Complex.cot_pi_eq_exp_ratio` / 引理 `Complex.cot_pi_eq_exp_ratio`

English:
lemma Complex.cot_pi_eq_exp_ratio
  given: (z : Complex)
  proof: by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

中文:
引理 Complex.cot_pi_eq_exp_ratio
  条件: (z : Complex)
  证明: by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

Depends on / 依赖: cot_eq_exp_ratio, ring_nf
-/
lemma Complex.cot_pi_eq_exp_ratio (z : Complex) :
    cot (π * z) = (Complex.exp (2 * π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z))) := by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

/--
theorem `pi_mul_cot_pi_q_exp` / 定理 `pi_mul_cot_pi_q_exp`

English:
theorem pi_mul_cot_pi_q_exp
  given: (z : ℍ)
  proof: by
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [cot_pi_eq_exp_ratio]; rw [h1]; rw

中文:
定理 pi_mul_cot_pi_q_exp
  条件: (z : ℍ)
  证明: by
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [cot_pi_eq_exp_ratio]; rw [h1]; rw

Depends on / 依赖: Complex.exp, UpperHalfPlane, UpperHalfPlane.norm_exp_two_pi_I_, UpperHalfPlane.norm_exp_two_pi_I_lt_one, add_comm, cot_pi_eq_exp_ratio, div_I, div_mul_eq_div_mul_one_div, geom_series_mul_one_add, mul_neg, neg_inj, neg_mul, norm_exp_two_pi_I_, norm_exp_two_pi_I_lt_one, one_div, tsum_geometric_of_norm_lt_one
-/
theorem pi_mul_cot_pi_q_exp (z : ℍ) :
    π * cot (π * z) = π * I - 2 * π * I * ∑' n : Nat, Complex.exp (2 * π * I * z) ^ n := by
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [cot_pi_eq_exp_ratio]; rw [h1]; rw [one_div]; rw [(tsum_geometric_of_norm_lt_one
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).symm]; rw [add_comm]; rw [geom_series_mul_one_add
      (Complex.exp (2 * π * I * (z : Complex))) (UpperHalfPlane.norm_exp_two_pi_I_lt_one _)]
  ring

section MittagLeffler

open Filter Function

open scoped Topology Nat Complex

variable {x : Complex} {Z : Set Complex}

/--
Definition of `sineTerm` / `sineTerm` 的定义

English:
abbreviation sineTerm
  signature: (x : Complex) (n : Nat)
  body: -x ^ 2 / (n + 1) ^ 2

中文:
缩写 sineTerm
  签名: (x : Complex) (n : 自然数)
  定义体: -x ^ 2 / (n + 1) ^ 2
-/
noncomputable abbrev sineTerm (x : Complex) (n : Nat) : Complex := -x ^ 2 / (n + 1) ^ 2

/--
lemma `sineTerm_ne_zero` / 引理 `sineTerm_ne_zero`

English:
lemma sineTerm_ne_zero
  given: {x : Complex} (hx : x in Complex_Int) (n : Nat)
  statement: 1 + sineTerm x n != 0
  proof: by
  simp only [sineTerm, ne_eq]
  rw [add_eq_zero_iff_eq_neg]; rw [neg_div']; rw [eq_div_iff]
  · have := (integerComplement_pow_two_ne_pow_two hx (n + 1 : Int))
    aesop
  · simp [Nat.cast_add_one_ne_zero n]

中文:
引理 sineTerm_ne_zero
  条件: {x : Complex} (hx : x in Complex_整数) (n : 自然数)
  结论: 1 + sineTerm x n != 0
  证明: by
  simp only [sineTerm, ne_eq]
  rw [add_eq_zero_iff_eq_neg]; rw [neg_div']; rw [eq_div_iff]
  · have := (integerComplement_pow_two_ne_pow_two hx (n + 1 : Int))
    aesop
  · simp [Nat.cast_add_one_ne_zero n]

Depends on / 依赖: Nat.cast_add_one_ne_zero, add_eq_zero_iff_eq_neg, cast_add_one_ne_zero, eq_div_iff, integerComplement_pow_two_ne_pow_two, ne_eq, neg_div, sineTerm
-/
lemma sineTerm_ne_zero {x : Complex} (hx : x in Complex_Int) (n : Nat) : 1 + sineTerm x n != 0 := by
  simp only [sineTerm, ne_eq]
  rw [add_eq_zero_iff_eq_neg]; rw [neg_div']; rw [eq_div_iff]
  · have := (integerComplement_pow_two_ne_pow_two hx (n + 1 : Int))
    aesop
  · simp [Nat.cast_add_one_ne_zero n]

/--
lemma `tendsto_euler_sin_prod'` / 引理 `tendsto_euler_sin_prod'`

English:
lemma tendsto_euler_sin_prod'
  given: (h0 : x != 0)
  proof: by
  rw [show (sin (π * x) / (π * x)) = sin (π * x) * (1 / (π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  exact fun n => by field_simp; rfl

中文:
引理 tendsto_euler_sin_prod'
  条件: (h0 : x != 0)
  证明: by
  rw [show (sin (π * x) / (π * x)) = sin (π * x) * (1 / (π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  exact fun n => by field_simp; rfl

Depends on / 依赖: Filter, Filter.Tendsto.mul_const, Tendsto, mul_const, tendsto_euler_sin_prod
-/
lemma tendsto_euler_sin_prod' (h0 : x != 0) :
    Tendsto (fun n : Nat => ∏ i in Finset.range n, (1 + sineTerm x i)) atTop
    (𝓝 (sin (π * x) / (π * x))) := by
  rw [show (sin (π * x) / (π * x)) = sin (π * x) * (1 / (π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  exact fun n => by field_simp; rfl

/--
lemma `multipliable_sineTerm` / 引理 `multipliable_sineTerm`

English:
lemma multipliable_sineTerm
  given: (x : Complex)
  statement: Multipliable fun i => (1 + sineTerm x i)
  proof: by
  apply multipliable_one_add_of_summable
  have := summable_pow_div_add (x ^ 2) 2 1 Nat.one_lt_two
  simpa [sineTerm] using this

中文:
引理 multipliable_sineTerm
  条件: (x : Complex)
  结论: Multipliable fun i => (1 + sineTerm x i)
  证明: by
  apply multipliable_one_add_of_summable
  have := summable_pow_div_add (x ^ 2) 2 1 Nat.one_lt_two
  simpa [sineTerm] using this

Depends on / 依赖: Nat.one_lt_two, multipliable_one_add_of_summable, one_lt_two, sineTerm, summable_pow_div_add
-/
lemma multipliable_sineTerm (x : Complex) : Multipliable fun i => (1 + sineTerm x i) := by
  apply multipliable_one_add_of_summable
  have := summable_pow_div_add (x ^ 2) 2 1 Nat.one_lt_two
  simpa [sineTerm] using this

/--
lemma `euler_sineTerm_tprod` / 引理 `euler_sineTerm_tprod`

English:
lemma euler_sineTerm_tprod
  given: (hx : x in Complex_Int)
  proof: by
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x)]; rw [Multipliable.hasProd_iff_tendsto_nat (multipliable_sineTerm x)]
  exact tendsto_euler_sin_prod' (integerComplement.ne_zero hx)

中文:
引理 euler_sineTerm_tprod
  条件: (hx : x in Complex_整数)
  证明: by
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x)]; rw [Multipliable.hasProd_iff_tendsto_nat (multipliable_sineTerm x)]
  exact tendsto_euler_sin_prod' (integerComplement.ne_zero hx)

Depends on / 依赖: Multipliable, Multipliable.hasProd_iff, Multipliable.hasProd_iff_tendsto_nat, hasProd_iff, hasProd_iff_tendsto_nat, integerComplement, integerComplement.ne_zero, multipliable_sineTerm, ne_zero, tendsto_euler_sin_prod
-/
lemma euler_sineTerm_tprod (hx : x in Complex_Int) :
    ∏' i : Nat, (1 + sineTerm x i) = Complex.sin (π * x) / (π * x) := by
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x)]; rw [Multipliable.hasProd_iff_tendsto_nat (multipliable_sineTerm x)]
  exact tendsto_euler_sin_prod' (integerComplement.ne_zero hx)

/--
lemma `sineTerm_bound_aux` / 引理 `sineTerm_bound_aux`

English:
lemma sineTerm_bound_aux
  given: (hZ : IsCompact Z)
  proof: by
  have hf : ContinuousOn (fun x : Complex => ‖-x ^ 2‖) Z := by
    fun_prop
  obtain ⟨s, hs⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  refine ⟨fun n : Nat => ‖(s : Complex) / (n + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (s : Complex) 2 1 (Nat.one_lt_two)
  · simp only [n

中文:
引理 sineTerm_bound_aux
  条件: (hZ : IsCompact Z)
  证明: by
  have hf : ContinuousOn (fun x : Complex => ‖-x ^ 2‖) Z := by
    fun_prop
  obtain ⟨s, hs⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  refine ⟨fun n : Nat => ‖(s : Complex) / (n + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (s : Complex) 2 1 (Nat.one_lt_two)
  · simp only [n
-/
private lemma sineTerm_bound_aux (hZ : IsCompact Z) :
    exists u : Nat -> Real, Summable u ∧ forall j z, z in Z -> ‖sineTerm z j‖ <= u j := by
  have hf : ContinuousOn (fun x : Complex => ‖-x ^ 2‖) Z := by
    fun_prop
  obtain ⟨s, hs⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  refine ⟨fun n : Nat => ‖(s : Complex) / (n + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (s : Complex) 2 1 (Nat.one_lt_two)
  · simp only [norm_neg, norm_pow, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, sineTerm, norm_div, norm_real, norm_eq_abs] at *
    intro n x hx
    gcongr
    apply le_trans (hs x hx) (le_abs_self s)

/--
lemma `multipliableUniformlyOn_euler_sin_prod_on_compact` / 引理 `multipliableUniformlyOn_euler_sin_prod_on_compact`

English:
lemma multipliableUniformlyOn_euler_sin_prod_on_compact
  given: (hZC : IsCompact Z)
  proof: by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop

中文:
引理 multipliableUniformlyOn_euler_sin_prod_on_compact
  条件: (hZC : IsCompact Z)
  证明: by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop

Depends on / 依赖: Summable, Summable.multipliableUniformlyOn_nat_one_add, filter_upwards, fun_prop, multipliableUniformlyOn_nat_one_add, sineTerm_bound_aux
-/
lemma multipliableUniformlyOn_euler_sin_prod_on_compact (hZC : IsCompact Z) :
    MultipliableUniformlyOn (fun n : Nat => fun z : Complex => (1 + sineTerm z n)) Z := by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop

/--
lemma `HasProdUniformlyOn_sineTerm_prod_on_compact` / 引理 `HasProdUniformlyOn_sineTerm_prod_on_compact`

English:
lemma HasProdUniformlyOn_sineTerm_prod_on_compact
  statement: (hZ2 : Z subseteq Complex_Int)
  proof: by
  apply (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn.congr_right
  exact fun x hx => euler_sineTerm_tprod (by aesop)

中文:
引理 HasProdUniformlyOn_sineTerm_prod_on_compact
  结论: (hZ2 : Z subseteq Complex_整数)
  证明: by
  apply (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn.congr_right
  exact fun x hx => euler_sineTerm_tprod (by aesop)

Depends on / 依赖: congr_right, euler_sineTerm_tprod, hasProdUniformlyOn, hasProdUniformlyOn.congr_right, multipliableUniformlyOn_euler_sin_prod_on_compact
-/
lemma HasProdUniformlyOn_sineTerm_prod_on_compact (hZ2 : Z subseteq Complex_Int)
    (hZC : IsCompact Z) :
    HasProdUniformlyOn (fun n : Nat => fun z : Complex => (1 + sineTerm z n))
    (fun x => (Complex.sin (↑π * x) / (↑π * x))) Z := by
  apply (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn.congr_right
  exact fun x hx => euler_sineTerm_tprod (by aesop)

/--
lemma `HasProdLocallyUniformlyOn_euler_sin_prod` / 引理 `HasProdLocallyUniformlyOn_euler_sin_prod`

English:
lemma HasProdLocallyUniformlyOn_euler_sin_prod
  proof: by
  apply hasProdLocallyUniformlyOn_of_forall_compact Complex.isOpen_compl_range_intCast
  exact fun _ hZ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZ hZC

中文:
引理 HasProdLocallyUniformlyOn_euler_sin_prod
  证明: by
  apply hasProdLocallyUniformlyOn_of_forall_compact Complex.isOpen_compl_range_intCast
  exact fun _ hZ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZ hZC

Depends on / 依赖: Complex.isOpen_compl_range_intCast, HasProdUniformlyOn_sineTerm_prod_on_compact, hasProdLocallyUniformlyOn_of_forall_compact, isOpen_compl_range_intCast
-/
lemma HasProdLocallyUniformlyOn_euler_sin_prod :
    HasProdLocallyUniformlyOn (fun n : Nat => fun z : Complex => (1 + sineTerm z n))
    (fun x => (Complex.sin (π * x) / (π * x))) Complex_Int := by
  apply hasProdLocallyUniformlyOn_of_forall_compact Complex.isOpen_compl_range_intCast
  exact fun _ hZ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZ hZC

/--
theorem `sin_pi_mul_ne_zero` / 定理 `sin_pi_mul_ne_zero`

English:
theorem sin_pi_mul_ne_zero
  given: (hx : x in Complex_Int)
  statement: Complex.sin (π * x) != 0
  proof: by
  apply Complex.sin_ne_zero_iff.2
  intro k
  nth_rw 2 [mul_comm]
  exact Injective.ne (mul_right_injective₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by aesop)

中文:
定理 sin_pi_mul_ne_zero
  条件: (hx : x in Complex_整数)
  结论: Complex.sin (π * x) != 0
  证明: by
  apply Complex.sin_ne_zero_iff.2
  intro k
  nth_rw 2 [mul_comm]
  exact Injective.ne (mul_right_injective₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by aesop)

Depends on / 依赖: Complex.sin_ne_zero_iff, Injective, Injective.ne, Real.pi_ne_zero, mul_comm, nth_rw, ofReal_ne_zero, ofReal_ne_zero.mpr, pi_ne_zero, sin_ne_zero_iff
-/
theorem sin_pi_mul_ne_zero (hx : x in Complex_Int) : Complex.sin (π * x) != 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k
  nth_rw 2 [mul_comm]
  exact Injective.ne (mul_right_injective₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by aesop)

/--
lemma `cot_pi_mul_contDiffWithinAt` / 引理 `cot_pi_mul_contDiffWithinAt`

English:
lemma cot_pi_mul_contDiffWithinAt
  given: (k : Nat∞) (hx : x in Complex_Int)
  proof: by
  simp_rw [Complex.cot, Complex.cos, Complex.sin]
  exact ContDiffWithinAt.div (by fun_prop) (by fun_prop) (sin_pi_mul_ne_zero hx)

中文:
引理 cot_pi_mul_contDiffWithinAt
  条件: (k : 自然数∞) (hx : x in Complex_整数)
  证明: by
  simp_rw [Complex.cot, Complex.cos, Complex.sin]
  exact ContDiffWithinAt.div (by fun_prop) (by fun_prop) (sin_pi_mul_ne_zero hx)

Depends on / 依赖: Complex.cos, Complex.cot, Complex.sin, ContDiffWithinAt, ContDiffWithinAt.div, fun_prop, simp_rw, sin_pi_mul_ne_zero
-/
lemma cot_pi_mul_contDiffWithinAt (k : Nat∞) (hx : x in Complex_Int) :
    ContDiffWithinAt Complex k (fun x => (↑π * x).cot) ℍₒ x := by
  simp_rw [Complex.cot, Complex.cos, Complex.sin]
  exact ContDiffWithinAt.div (by fun_prop) (by fun_prop) (sin_pi_mul_ne_zero hx)

/--
lemma `tendsto_logDeriv_euler_sin_div` / 引理 `tendsto_logDeriv_euler_sin_div`

English:
lemma tendsto_logDeriv_euler_sin_div
  given: (hx : x in Complex_Int)
  proof: by
  refine logDeriv_tendsto isOpen_compl_range_intCast hx
      HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange ?_ ?_
  · filter_upwards with n using by fun_prop
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨sin_pi_mul_ne_zero 

中文:
引理 tendsto_logDeriv_euler_sin_div
  条件: (hx : x in Complex_整数)
  证明: by
  refine logDeriv_tendsto isOpen_compl_range_intCast hx
      HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange ?_ ?_
  · filter_upwards with n using by fun_prop
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨sin_pi_mul_ne_zero 

Depends on / 依赖: HasProdLocallyUniformlyOn_euler_sin_prod, HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange, Real.pi_ne_zero, div_eq_zero_iff, filter_upwards, fun_prop, integerComplement, integerComplement.ne_zero, isOpen_compl_range_intCast, logDeriv_tendsto, mul_eq_zero, ne_eq, ne_zero, not_or, ofReal_eq_zero, pi_ne_zero, sin_pi_mul_ne_zero, tendstoLocallyUniformlyOn_finsetRange
-/
lemma tendsto_logDeriv_euler_sin_div (hx : x in Complex_Int) :
    Tendsto (fun n : Nat => logDeriv (fun z => ∏ j in Finset.range n, (1 + sineTerm z j)) x)
        atTop (𝓝 <| logDeriv (fun t => (Complex.sin (π * t) / (π * t))) x) := by
  refine logDeriv_tendsto isOpen_compl_range_intCast hx
      HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange ?_ ?_
  · filter_upwards with n using by fun_prop
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨sin_pi_mul_ne_zero hx, Real.pi_ne_zero, integerComplement.ne_zero hx⟩

/--
lemma `logDeriv_sin_div_eq_cot` / 引理 `logDeriv_sin_div_eq_cot`

English:
lemma logDeriv_sin_div_eq_cot
  given: (hz : x in Complex_Int)
  proof: by
  have : (fun t => (Complex.sin (π * t) / (π * t))) = fun z =>
    (Complex.sin ∘ fun t => π * t) z / (π * z) := by simp
  rw [this]; rw [logDeriv_div _ (by apply sin_pi_mul_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop)]; rw [logDeriv_comp

中文:
引理 logDeriv_sin_div_eq_cot
  条件: (hz : x in Complex_整数)
  证明: by
  have : (fun t => (Complex.sin (π * t) / (π * t))) = fun z =>
    (Complex.sin ∘ fun t => π * t) z / (π * z) := by simp
  rw [this]; rw [logDeriv_div _ (by apply sin_pi_mul_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop)]; rw [logDeriv_comp

Depends on / 依赖: Complex.differentiableAt_sin, Complex.logDeriv_sin, Complex.sin, DifferentiableAt, DifferentiableAt.comp, deriv_const_mul_id, differentiableAt_sin, fun_prop, logDeriv_comp, logDeriv_const_mul, logDeriv_div, logDeriv_id, logDeriv_sin, mul_eq_zero, ne_eq, not_or, ofReal_eq_zero, sin_pi_mul_ne_zero
-/
lemma logDeriv_sin_div_eq_cot (hz : x in Complex_Int) :
    logDeriv (fun t => (Complex.sin (π * t) / (π * t))) x = π * cot (π * x) - 1 / x := by
  have : (fun t => (Complex.sin (π * t) / (π * t))) = fun z =>
    (Complex.sin ∘ fun t => π * t) z / (π * z) := by simp
  rw [this]; rw [logDeriv_div _ (by apply sin_pi_mul_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop)]; rw [logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop)]; rw [Complex.logDeriv_sin]; rw [deriv_const_mul_id]; rw [logDeriv_const_mul]; rw [logDeriv_id']
  · ring
  · simp
  · simp only [ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨Real.pi_ne_zero, integerComplement.ne_zero hz⟩

/--
Definition of `cotTerm` / `cotTerm` 的定义

English:
abbreviation cotTerm
  signature: (x : Complex) (n : Nat)
  body: 1 / (x - (n + 1)) + 1 / (x + (n + 1))

中文:
缩写 cotTerm
  签名: (x : Complex) (n : 自然数)
  定义体: 1 / (x - (n + 1)) + 1 / (x + (n + 1))
-/
noncomputable abbrev cotTerm (x : Complex) (n : Nat) : Complex := 1 / (x - (n + 1)) + 1 / (x + (n + 1))

/--
lemma `logDeriv_sineTerm_eq_cotTerm` / 引理 `logDeriv_sineTerm_eq_cotTerm`

English:
lemma logDeriv_sineTerm_eq_cotTerm
  given: (hx : x in Complex_Int) (i : Nat)
  proof: by
  have h1 := integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : Complex) - (i + 1)) != 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(i + 1))
  have h3 : (i + 1) ^ 2 + - x ^ 2 != 0 := by
      have := (integerComplement_pow_two_ne_pow_two hx ((i + 1) : Int))


中文:
引理 logDeriv_sineTerm_eq_cotTerm
  条件: (hx : x in Complex_整数) (i : 自然数)
  证明: by
  have h1 := integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : Complex) - (i + 1)) != 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(i + 1))
  have h3 : (i + 1) ^ 2 + - x ^ 2 != 0 := by
      have := (integerComplement_pow_two_ne_pow_two hx ((i + 1) : Int))


Depends on / 依赖: Int.cast_add, Int.cast_natCast, Int.cast_one, cast_add, cast_natCast, cast_one, deriv.fun_neg, deriv_const_add, deriv_div_const, differentiableAt_fun_id, fun_neg, integerComplement_add_ne_zero, integerComplement_pow_two_ne_pow_two, logDeriv_apply, ne_eq, sineTerm, sub_eq_add_neg, sub_ne_zero
-/
lemma logDeriv_sineTerm_eq_cotTerm (hx : x in Complex_Int) (i : Nat) :
    logDeriv (fun (z : Complex) => 1 + sineTerm z i) x = cotTerm x i := by
  have h1 := integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : Complex) - (i + 1)) != 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(i + 1))
  have h3 : (i + 1) ^ 2 + - x ^ 2 != 0 := by
      have := (integerComplement_pow_two_ne_pow_two hx ((i + 1) : Int))
      rw [← sub_eq_add_neg]; rw [sub_ne_zero]
      aesop
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, ne_eq, sineTerm, logDeriv_apply,
    deriv_const_add', deriv_div_const, deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow,
    Nat.cast_ofNat, deriv_id'', cotTerm] at *
  field

/--
lemma `logDeriv_prod_sineTerm_eq_sum_cotTerm` / 引理 `logDeriv_prod_sineTerm_eq_sum_cotTerm`

English:
lemma logDeriv_prod_sineTerm_eq_sum_cotTerm
  given: (hx : x in Complex_Int) (n : Nat)
  proof: by
  rw [logDeriv_prod]
  · simp_rw [logDeriv_sineTerm_eq_cotTerm hx]
  · exact fun i _ => sineTerm_ne_zero hx i
  · fun_prop

中文:
引理 logDeriv_prod_sineTerm_eq_sum_cotTerm
  条件: (hx : x in Complex_整数) (n : 自然数)
  证明: by
  rw [logDeriv_prod]
  · simp_rw [logDeriv_sineTerm_eq_cotTerm hx]
  · exact fun i _ => sineTerm_ne_zero hx i
  · fun_prop

Depends on / 依赖: fun_prop, logDeriv_prod, logDeriv_sineTerm_eq_cotTerm, simp_rw, sineTerm_ne_zero
-/
lemma logDeriv_prod_sineTerm_eq_sum_cotTerm (hx : x in Complex_Int) (n : Nat) :
    logDeriv (fun (z : Complex) => ∏ j in Finset.range n, (1 + sineTerm z j)) x =
    ∑ j in Finset.range n, cotTerm x j := by
  rw [logDeriv_prod]
  · simp_rw [logDeriv_sineTerm_eq_cotTerm hx]
  · exact fun i _ => sineTerm_ne_zero hx i
  · fun_prop

/--
lemma `tendsto_logDeriv_euler_cot_sub` / 引理 `tendsto_logDeriv_euler_cot_sub`

English:
lemma tendsto_logDeriv_euler_cot_sub
  given: (hx : x in Complex_Int)
  proof: by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx

中文:
引理 tendsto_logDeriv_euler_cot_sub
  条件: (hx : x in Complex_整数)
  证明: by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx

Depends on / 依赖: logDeriv_prod_sineTerm_eq_sum_cotTerm, logDeriv_sin_div_eq_cot, simp_rw, tendsto_logDeriv_euler_sin_div
-/
lemma tendsto_logDeriv_euler_cot_sub (hx : x in Complex_Int) :
    Tendsto (fun n : Nat => ∑ j in Finset.range n, cotTerm x j) atTop
    (𝓝 <| π * cot (π * x) - 1 / x) := by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx

/--
lemma `cotTerm_identity` / 引理 `cotTerm_identity`

English:
lemma cotTerm_identity
  given: (hz : x in Complex_Int) (n : Nat)
  proof: by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : Int)
  · simpa using (integerComplement_add_ne_zero hz ((n : Int) + 1))

中文:
引理 cotTerm_identity
  条件: (hz : x in Complex_整数) (n : 自然数)
  证明: by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : Int)
  · simpa using (integerComplement_add_ne_zero hz ((n : Int) + 1))

Depends on / 依赖: cotTerm, integerComplement_add_ne_zero, one_div_add_one_div, sub_eq_add_neg
-/
lemma cotTerm_identity (hz : x in Complex_Int) (n : Nat) :
    cotTerm x n = 2 * x * (1 / ((x + (n + 1)) * (x - (n + 1)))) := by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : Int)
  · simpa using (integerComplement_add_ne_zero hz ((n : Int) + 1))

/--
lemma `summable_cotTerm` / 引理 `summable_cotTerm`

English:
lemma summable_cotTerm
  given: (hz : x in Complex_Int)
  statement: Summable fun n => cotTerm x n
  proof: by
  rw [funext fun n => cotTerm_identity hz n]
  apply Summable.mul_left
  suffices Summable fun i : Nat => (x - (↑i : Complex))⁻¹ * (x + (↑i : Complex))⁻¹ by
    rw [← summable_nat_add_iff 1] at this
    simpa using this
  suffices Summable fun i : Int => (x - (↑i : Complex))⁻¹ * (x + (↑i : Comple

中文:
引理 summable_cotTerm
  条件: (hz : x in Complex_整数)
  结论: Summable fun n => cotTerm x n
  证明: by
  rw [funext fun n => cotTerm_identity hz n]
  apply Summable.mul_left
  suffices Summable fun i : Nat => (x - (↑i : Complex))⁻¹ * (x + (↑i : Complex))⁻¹ by
    rw [← summable_nat_add_iff 1] at this
    simpa using this
  suffices Summable fun i : Int => (x - (↑i : Complex))⁻¹ * (x + (↑i : Comple

Depends on / 依赖: CharZero, CharZero.cast_injective, EisensteinSeries, EisensteinSeries.summable_linear_sub_mul_linear_add, Summable, Summable.mul_left, cast_injective, comp_injective, cotTerm_identity, mul_comm, mul_left, summable_linear_sub_mul_linear_add, summable_nat_add_iff, this.comp_injective
-/
lemma summable_cotTerm (hz : x in Complex_Int) : Summable fun n => cotTerm x n := by
  rw [funext fun n => cotTerm_identity hz n]
  apply Summable.mul_left
  suffices Summable fun i : Nat => (x - (↑i : Complex))⁻¹ * (x + (↑i : Complex))⁻¹ by
    rw [← summable_nat_add_iff 1] at this
    simpa using this
  suffices Summable fun i : Int => (x - (↑i : Complex))⁻¹ * (x + (↑i : Complex))⁻¹ by
    apply this.comp_injective CharZero.cast_injective
  apply (EisensteinSeries.summable_linear_sub_mul_linear_add x 1 1).congr
  simp [mul_comm]

@[deprecated (since := "2026-01-28")] alias Summable_cotTerm := summable_cotTerm

/--
lemma `cot_series_rep'` / 引理 `cot_series_rep'`

English:
lemma cot_series_rep'
  given: (hz : x in Complex_Int)
  statement: π * cot (π * x) - 1 / x =
  proof: by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

中文:
引理 cot_series_rep'
  条件: (hz : x in Complex_整数)
  结论: π * cot (π * x) - 1 / x =
  证明: by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

Depends on / 依赖: HasSum, HasSum.tsum_eq, Summable, Summable.hasSum_iff_tendsto_nat, hasSum_iff_tendsto_nat, summable_cotTerm, tendsto_logDeriv_euler_cot_sub, tsum_eq
-/
lemma cot_series_rep' (hz : x in Complex_Int) : π * cot (π * x) - 1 / x =
    ∑' n : Nat, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

/--
theorem `cot_series_rep` / 定理 `cot_series_rep`

English:
theorem cot_series_rep
  given: (hz : x in Complex_Int)
  proof: by
  have h0 := tsum_pnat_eq_tsum_succ (f := fun n => 1 / (x - n) + 1 / (x + n))
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [h0]; rw [← h1]
  ring

中文:
定理 cot_series_rep
  条件: (hz : x in Complex_整数)
  证明: by
  have h0 := tsum_pnat_eq_tsum_succ (f := fun n => 1 / (x - n) + 1 / (x + n))
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [h0]; rw [← h1]
  ring

Depends on / 依赖: Nat.cast_add, Nat.cast_one, cast_add, cast_one, cot_series_rep, one_div, tsum_pnat_eq_tsum_succ
-/
theorem cot_series_rep (hz : x in Complex_Int) :
    π * cot (π * x) = 1 / x + ∑' n : Nat+, (1 / (x - n) + 1 / (x + n)) := by
  have h0 := tsum_pnat_eq_tsum_succ (f := fun n => 1 / (x - n) + 1 / (x + n))
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [h0]; rw [← h1]
  ring

end MittagLeffler

section iteratedDeriv

open Set UpperHalfPlane

open scoped Nat

variable (k : Nat)

/--
lemma `contDiffOn_inv_linear` / 引理 `contDiffOn_inv_linear`

English:
lemma contDiffOn_inv_linear
  given: (d : Int)
  statement: ContDiffOn Complex k (fun z : Complex => 1 / (z + d)) Complex_Int
  proof: by
  simpa using ContDiffOn.fun_inv (by fun_prop) (fun x hx => integerComplement_add_ne_zero hx d)

中文:
引理 contDiffOn_inv_linear
  条件: (d : 整数)
  结论: ContDiffOn Complex k (fun z : Complex => 1 / (z + d)) Complex_整数
  证明: by
  simpa using ContDiffOn.fun_inv (by fun_prop) (fun x hx => integerComplement_add_ne_zero hx d)
-/
private lemma contDiffOn_inv_linear (d : Int) : ContDiffOn Complex k (fun z : Complex => 1 / (z + d)) Complex_Int := by
  simpa using ContDiffOn.fun_inv (by fun_prop) (fun x hx => integerComplement_add_ne_zero hx d)

/--
lemma `eqOn_iteratedDeriv_cotTerm` / 引理 `eqOn_iteratedDeriv_cotTerm`

English:
lemma eqOn_iteratedDeriv_cotTerm
  given: (d : Nat)
  proof: by
  intro z hz
  rw [← Pi.add_def]; rw [iteratedDeriv_add]
  · have h2 := iter_deriv_inv_linear_sub k 1 ((d + 1 : Complex))
    have h3 := iter_deriv_inv_linear k 1 (d + 1 : Complex)
    simp only [one_div, one_mul, one_pow, mul_one, Int.reduceNeg, iteratedDeriv_eq_iterate] at *
    rw [h2]; rw [h3

中文:
引理 eqOn_iteratedDeriv_cotTerm
  条件: (d : 自然数)
  证明: by
  intro z hz
  rw [← Pi.add_def]; rw [iteratedDeriv_add]
  · have h2 := iter_deriv_inv_linear_sub k 1 ((d + 1 : Complex))
    have h3 := iter_deriv_inv_linear k 1 (d + 1 : Complex)
    simp only [one_div, one_mul, one_pow, mul_one, Int.reduceNeg, iteratedDeriv_eq_iterate] at *
    rw [h2]; rw [h3

Depends on / 依赖: Int.reduceNeg, Pi.add_def, add_def, contDiffAt, contDiffOn_inv_linear, isOpen_compl_range_intCast, isOpen_compl_range_intCast.mem_, isOpen_compl_range_intCast.mem_nhds, iter_deriv_inv_linear, iter_deriv_inv_linear_sub, iteratedDeriv_add, iteratedDeriv_eq_iterate, mem_, mem_nhds, mul_one, one_div, one_mul, one_pow, reduceNeg, sub_eq_add_neg
-/
lemma eqOn_iteratedDeriv_cotTerm (d : Nat) :
    EqOn (iteratedDeriv k (fun z => cotTerm z d))
    (fun z => (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : Int) + (z - (d + 1)) ^ (-1 - k : Int)))
    Complex_Int := by
  intro z hz
  rw [← Pi.add_def]; rw [iteratedDeriv_add]
  · have h2 := iter_deriv_inv_linear_sub k 1 ((d + 1 : Complex))
    have h3 := iter_deriv_inv_linear k 1 (d + 1 : Complex)
    simp only [one_div, one_mul, one_pow, mul_one, Int.reduceNeg, iteratedDeriv_eq_iterate] at *
    rw [h2]; rw [h3]
    ring
  · simpa [sub_eq_add_neg] using (contDiffOn_inv_linear k (-(d + 1))).contDiffAt
      (isOpen_compl_range_intCast.mem_nhds hz)
  · simpa using (contDiffOn_inv_linear k (d + 1)).contDiffAt
      (isOpen_compl_range_intCast.mem_nhds hz)

/--
lemma `eqOn_iteratedDerivWithin_cotTerm_integerComplement` / 引理 `eqOn_iteratedDerivWithin_cotTerm_integerComplement`

English:
lemma eqOn_iteratedDerivWithin_cotTerm_integerComplement
  given: (d : Nat)
  proof: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast)
  exact eqOn_iteratedDeriv_cotTerm ..

中文:
引理 eqOn_iteratedDerivWithin_cotTerm_integerComplement
  条件: (d : 自然数)
  证明: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast)
  exact eqOn_iteratedDeriv_cotTerm ..

Depends on / 依赖: Complex.isOpen_compl_range_intCast, Set.EqOn.trans, eqOn_iteratedDeriv_cotTerm, isOpen_compl_range_intCast, iteratedDerivWithin_of_isOpen
-/
lemma eqOn_iteratedDerivWithin_cotTerm_integerComplement (d : Nat) :
    EqOn
      (iteratedDerivWithin k (fun z => cotTerm z d) Complex_Int)
      (fun z => (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : Int) + (z - (d + 1)) ^ (-1 - k : Int)))
      Complex_Int := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast)
  exact eqOn_iteratedDeriv_cotTerm ..

/--
lemma `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet` / 引理 `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet`

English:
lemma eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet
  given: (d : Nat)
  proof: by
  apply Set.EqOn.trans (upperHalfPlane_inter_integerComplement ▸
    iteratedDerivWithin_congr_right_of_isOpen (fun z => cotTerm z d) k
    isOpen_upperHalfPlaneSet (isOpen_compl_range_intCast))
  intro z hz
  simpa using! eqOn_iteratedDerivWithin_cotTerm_integerComplement k d
    (coe_mem_intege

中文:
引理 eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet
  条件: (d : 自然数)
  证明: by
  apply Set.EqOn.trans (upperHalfPlane_inter_integerComplement ▸
    iteratedDerivWithin_congr_right_of_isOpen (fun z => cotTerm z d) k
    isOpen_upperHalfPlaneSet (isOpen_compl_range_intCast))
  intro z hz
  simpa using! eqOn_iteratedDerivWithin_cotTerm_integerComplement k d
    (coe_mem_intege

Depends on / 依赖: Set.EqOn.trans, coe_mem_integerComplement, cotTerm, eqOn_iteratedDerivWithin_cotTerm_integerComplement, isOpen_compl_range_intCast, isOpen_upperHalfPlaneSet, iteratedDerivWithin_congr_right_of_isOpen, upperHalfPlane_inter_integerComplement
-/
lemma eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet (d : Nat) :
    EqOn
      (iteratedDerivWithin k (fun z => cotTerm z d) ℍₒ)
      (fun z => (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : Int) + (z - (d + 1)) ^ (-1 - k : Int)))
      ℍₒ := by
  apply Set.EqOn.trans (upperHalfPlane_inter_integerComplement ▸
    iteratedDerivWithin_congr_right_of_isOpen (fun z => cotTerm z d) k
    isOpen_upperHalfPlaneSet (isOpen_compl_range_intCast))
  intro z hz
  simpa using! eqOn_iteratedDerivWithin_cotTerm_integerComplement k d
    (coe_mem_integerComplement ⟨z, hz⟩)

open EisensteinSeries in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev cotTermUpperBound (A B : Real) (hB : 0 < B) (a : Nat)
  body: k ! * (2 * (r (⟨⟨A, B⟩, hB⟩) ^ (-1 - k : Int)) * ‖((a + 1) ^ (-1 - k : Int) : Real)‖)

中文:
缩写 noncomputable
  签名: abbrev cotTermUpperBound (A B : 实数) (hB : 0 < B) (a : 自然数)
  定义体: k ! * (2 * (r (⟨⟨A, B⟩, hB⟩) ^ (-1 - k : Int)) * ‖((a + 1) ^ (-1 - k : Int) : Real)‖)
-/
private noncomputable abbrev cotTermUpperBound (A B : Real) (hB : 0 < B) (a : Nat) :=
  k ! * (2 * (r (⟨⟨A, B⟩, hB⟩) ^ (-1 - k : Int)) * ‖((a + 1) ^ (-1 - k : Int) : Real)‖)

/--
lemma `summable_cotTermUpperBound` / 引理 `summable_cotTermUpperBound`

English:
lemma summable_cotTermUpperBound
  given: (A B : Real) (hB : 0 < B) {k : Nat} (hk : 1 <= k)
  proof: by
  simp_rw [← mul_assoc]
  apply Summable.mul_left
  conv => enter [1, n]; rw [show (-1 - k : Int) = -(1 + k :) by lia, zpow_neg, zpow_natCast];
          enter [1, 1, 1]; norm_cast
  rw [summable_norm_iff]; rw [summable_nat_add_iff (f := fun n : Nat => ((n : Real) ^ (1 + k))⁻¹)]
exact summable_na

中文:
引理 summable_cotTermUpperBound
  条件: (A B : 实数) (hB : 0 < B) {k : 自然数} (hk : 1 <= k)
  证明: by
  simp_rw [← mul_assoc]
  apply Summable.mul_left
  conv => enter [1, n]; rw [show (-1 - k : Int) = -(1 + k :) by lia, zpow_neg, zpow_natCast];
          enter [1, 1, 1]; norm_cast
  rw [summable_norm_iff]; rw [summable_nat_add_iff (f := fun n : Nat => ((n : Real) ^ (1 + k))⁻¹)]
exact summable_na
-/
private lemma summable_cotTermUpperBound (A B : Real) (hB : 0 < B) {k : Nat} (hk : 1 <= k) :
    Summable fun a : Nat => cotTermUpperBound k A B hB a := by
  simp_rw [← mul_assoc]
  apply Summable.mul_left
  conv => enter [1, n]; rw [show (-1 - k : Int) = -(1 + k :) by lia, zpow_neg, zpow_natCast];
          enter [1, 1, 1]; norm_cast
  rw [summable_norm_iff]; rw [summable_nat_add_iff (f := fun n : Nat => ((n : Real) ^ (1 + k))⁻¹)]
exact summable_nat_pow_inv.mpr by lia

open EisensteinSeries in
/--
lemma `iteratedDerivWithin_cotTerm_bounded_uniformly` / 引理 `iteratedDerivWithin_cotTerm_bounded_uniformly`

English:
lemma iteratedDerivWithin_cotTerm_bounded_uniformly
  proof: by
  rcases hKAB ha with ⟨a, haAB, rfl⟩
  simp only [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n a.im_pos, Complex.norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul, cotTermUpperBound,
    Int.reduceNeg, norm_zpow, Real.norm_eq_abs, two_mul, add_mul]
  gco

中文:
引理 iteratedDerivWithin_cotTerm_bounded_uniformly
  证明: by
  rcases hKAB ha with ⟨a, haAB, rfl⟩
  simp only [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n a.im_pos, Complex.norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul, cotTermUpperBound,
    Int.reduceNeg, norm_zpow, Real.norm_eq_abs, two_mul, add_mul]
  gco
-/
private lemma iteratedDerivWithin_cotTerm_bounded_uniformly
    {k : Nat} {K : Set Complex} (A B : Real) (hB : 0 < B)
    (hKAB : K subseteq (↑) '' verticalStrip A B) (n : Nat) {a : Complex} (ha : a in K) :
    ‖iteratedDerivWithin k (fun z => cotTerm z n) ℍₒ a‖ <= cotTermUpperBound k A B hB n := by
  rcases hKAB ha with ⟨a, haAB, rfl⟩
  simp only [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n a.im_pos, Complex.norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul, cotTermUpperBound,
    Int.reduceNeg, norm_zpow, Real.norm_eq_abs, two_mul, add_mul]
  gcongr
  have h1 := summand_bound_of_mem_verticalStrip (k := k + 1) (by positivity) ![1, n + 1] hB haAB
  have h2 := abs_norm_eq_max_natAbs_neg n ▸ summand_bound_of_mem_verticalStrip (k := k + 1)
    (by positivity) ![1, -(n + 1)] hB haAB
  apply norm_add_le_of_le
  · simpa (disch := positivity) [sub_eq_add_neg, ← Real.rpow_intCast, abs_norm_eq_max_natAbs,
      abs_of_nonneg] using h1
  · simpa (disch := positivity) [sub_eq_add_neg, ← Real.rpow_intCast, abs_norm_eq_max_natAbs,
      abs_of_nonneg] using h2

/--
lemma `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` / 引理 `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`

English:
lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm
  given: {k : Nat} (hk : 1 <= k)
  proof: by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  lift K to Set ℍ using hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact
    (isEmbedding_coe.isCompact_iff.mpr hKc)
  exact ⟨cotTermUpperBound k A B hB, summable_cotTermUpperBound A B

中文:
引理 summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm
  条件: {k : 自然数} (hk : 1 <= k)
  证明: by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  lift K to Set ℍ using hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact
    (isEmbedding_coe.isCompact_iff.mpr hKc)
  exact ⟨cotTermUpperBound k A B hB, summable_cotTermUpperBound A B

Depends on / 依赖: SummableLocallyUniformlyOn_of_locally_bounded, cotTermUpperBound, isCompact_iff, isEmbedding_coe, isEmbedding_coe.isCompact_iff.mpr, isOpen_upperHalfPlaneSet, iteratedDerivWithin_cotTerm_bounded_uniformly, subset_verticalStrip_of_isCompact, summable_cotTermUpperBound
-/
lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm {k : Nat} (hk : 1 <= k) :
    SummableLocallyUniformlyOn (fun n => iteratedDerivWithin k (fun z => cotTerm z n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  lift K to Set ℍ using hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact
    (isEmbedding_coe.isCompact_iff.mpr hKc)
  exact ⟨cotTermUpperBound k A B hB, summable_cotTermUpperBound A B hB hk,
iteratedDerivWithin_cotTerm_bounded_uniformly A B hB by gcongr⟩

/--
lemma `differentiableOn_iteratedDerivWithin_cotTerm` / 引理 `differentiableOn_iteratedDerivWithin_cotTerm`

English:
lemma differentiableOn_iteratedDerivWithin_cotTerm
  given: (n l : Nat)
  proof: by
  suffices DifferentiableOn Complex (fun z : Complex => (-1) ^ l * l ! * ((z + (n + 1)) ^ (-1 - l : Int) +
    (z - (n + 1)) ^ (-1 - l : Int))) ℍₒ by
    exact this.congr fun z hz => eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet l n hz
  apply DifferentiableOn.const_mul
apply DifferentiableO

中文:
引理 differentiableOn_iteratedDerivWithin_cotTerm
  条件: (n l : 自然数)
  证明: by
  suffices DifferentiableOn Complex (fun z : Complex => (-1) ^ l * l ! * ((z + (n + 1)) ^ (-1 - l : Int) +
    (z - (n + 1)) ^ (-1 - l : Int))) ℍₒ by
    exact this.congr fun z hz => eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet l n hz
  apply DifferentiableOn.const_mul
apply DifferentiableO

Depends on / 依赖: DifferentiableOn, DifferentiableOn.add, DifferentiableOn.const_mul, DifferentiableOn.zpow, UpperHalfPlane, UpperHalfPlane.ne_intCast, add_eq_zero_iff_neg_eq, const_mul, eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet, fun_prop, ne_intCast, sub_eq_zero, this.congr
-/
lemma differentiableOn_iteratedDerivWithin_cotTerm (n l : Nat) :
    DifferentiableOn Complex (iteratedDerivWithin l (fun z => cotTerm z n) ℍₒ) ℍₒ := by
  suffices DifferentiableOn Complex (fun z : Complex => (-1) ^ l * l ! * ((z + (n + 1)) ^ (-1 - l : Int) +
    (z - (n + 1)) ^ (-1 - l : Int))) ℍₒ by
    exact this.congr fun z hz => eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet l n hz
  apply DifferentiableOn.const_mul
apply DifferentiableOn.add <;> refine DifferentiableOn.zpow (by fun_prop) .inl fun x hx => ?_
  · simpa [add_eq_zero_iff_neg_eq'] using (UpperHalfPlane.ne_intCast (.mk x hx) (-(n + 1))).symm
  · simpa [sub_eq_zero] using (UpperHalfPlane.ne_intCast (.mk x hx) (n + 1))

/--
lemma `aux_summable_add` / 引理 `aux_summable_add`

English:
lemma aux_summable_add
  given: {k : Nat} (hk : 1 <= k) (x : Complex)
  proof: by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).1).congr
  simp [← zpow_neg, sub_eq_add_neg]

中文:
引理 aux_summable_add
  条件: {k : 自然数} (hk : 1 <= k) (x : Complex)
  证明: by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).1).congr
  simp [← zpow_neg, sub_eq_add_neg]
-/
private lemma aux_summable_add {k : Nat} (hk : 1 <= k) (x : Complex) :
  Summable fun (n : Nat) => (x + (n + 1)) ^ (-1 - k : Int) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).1).congr
  simp [← zpow_neg, sub_eq_add_neg]

/--
lemma `aux_summable_sub` / 引理 `aux_summable_sub`

English:
lemma aux_summable_sub
  given: {k : Nat} (hk : 1 <= k) (x : Complex)
  proof: by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).2).congr
  simp [← zpow_neg, sub_eq_add_neg]

中文:
引理 aux_summable_sub
  条件: {k : 自然数} (hk : 1 <= k) (x : Complex)
  证明: by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).2).congr
  simp [← zpow_neg, sub_eq_add_neg]
-/
private lemma aux_summable_sub {k : Nat} (hk : 1 <= k) (x : Complex) :
  Summable fun (n : Nat) => (x - (n + 1)) ^ (-1 - k : Int) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).2).congr
  simp [← zpow_neg, sub_eq_add_neg]

variable {z : Complex}

-- We have this auxiliary ugly version on the lhs so the rhs looks nicer.
/--
lemma `aux_iteratedDeriv_tsum_cotTerm` / 引理 `aux_iteratedDeriv_tsum_cotTerm`

English:
lemma aux_iteratedDeriv_tsum_cotTerm
  given: {k : Nat} (hk : 1 <= k) (hz : z in ℍₒ)
  proof: by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet hz
    (fun t ht => summable_cotTerm (coe_mem_integerComplement ⟨t]; rw [ht⟩))
    (fun l hl hl2 => summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm hl)
    (fun n l z hl hz => (differentiableOn_iteratedDerivWithin_cotTerm n l).diffe

中文:
引理 aux_iteratedDeriv_tsum_cotTerm
  条件: {k : 自然数} (hk : 1 <= k) (hz : z in ℍₒ)
  证明: by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet hz
    (fun t ht => summable_cotTerm (coe_mem_integerComplement ⟨t]; rw [ht⟩))
    (fun l hl hl2 => summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm hl)
    (fun n l z hl hz => (differentiableOn_iteratedDerivWithin_cotTerm n l).diffe
-/
private lemma aux_iteratedDeriv_tsum_cotTerm {k : Nat} (hk : 1 <= k) (hz : z in ℍₒ) :
    (-1) ^ k * (k !) * z ^ (-1 - k : Int) +
      iteratedDerivWithin k (fun z => ∑' n : Nat, cotTerm z n) ℍₒ z =
    (-1) ^ k * k ! * ∑' n : Int, (z + n) ^ (-1 - k : Int) := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet hz
    (fun t ht => summable_cotTerm (coe_mem_integerComplement ⟨t]; rw [ht⟩))
    (fun l hl hl2 => summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm hl)
    (fun n l z hl hz => (differentiableOn_iteratedDerivWithin_cotTerm n l).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz))]
  conv =>
    enter [1, 2, 1, n]
    rw [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n (by simp [hz])]
  rw [tsum_of_add_one_of_neg_add_one (by simpa using aux_summable_add hk z)
    (by simpa [sub_eq_add_neg] using aux_summable_sub hk z),
    tsum_mul_left, Summable.tsum_add (aux_summable_add hk z) (aux_summable_sub hk z)]
  push_cast
  ring_nf

/--
lemma `iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum` / 引理 `iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum`

English:
lemma iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum
  given: {k : Nat} (hk : 1 <= k) (hz : z in ℍₒ)
  proof: by
  simp only [← aux_iteratedDeriv_tsum_cotTerm hk hz, one_div, neg_mul, neg_add_cancel_left]
  refine iteratedDerivWithin_congr (fun z hz => ?_) hz
  simpa [cotTerm] using (cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))

中文:
引理 iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum
  条件: {k : 自然数} (hk : 1 <= k) (hz : z in ℍₒ)
  证明: by
  simp only [← aux_iteratedDeriv_tsum_cotTerm hk hz, one_div, neg_mul, neg_add_cancel_left]
  refine iteratedDerivWithin_congr (fun z hz => ?_) hz
  simpa [cotTerm] using (cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe_mem_integerComplement, aux_iteratedDeriv_tsum_cotTerm, coe_mem_integerComplement, cotTerm, cot_series_rep, iteratedDerivWithin_congr, neg_add_cancel_left, neg_mul, one_div
-/
lemma iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum {k : Nat} (hk : 1 <= k) (hz : z in ℍₒ) :
    iteratedDerivWithin k (fun x : Complex => π * cot (π * x) - 1 / x) ℍₒ z =
    -(-1) ^ k * k ! * (z ^ (-1 - k : Int)) + (-1) ^ k * k ! * ∑' n : Int, (z + n) ^ (-1 - k : Int) := by
  simp only [← aux_iteratedDeriv_tsum_cotTerm hk hz, one_div, neg_mul, neg_add_cancel_left]
  refine iteratedDerivWithin_congr (fun z hz => ?_) hz
  simpa [cotTerm] using (cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))

/--
lemma `iteratedDerivWithin_cot_pi_mul_sub_inv` / 引理 `iteratedDerivWithin_cot_pi_mul_sub_inv`

English:
lemma iteratedDerivWithin_cot_pi_mul_sub_inv
  given: {z : Complex} (hz : z in ℍₒ)
  proof: by
  simp_rw [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add hz isOpen_upperHalfPlaneSet.uniqueDiffOn]
  · simpa [iteratedDerivWithin_fun_neg] using! iteratedDerivWithin_one_div k
      isOpen_upperHalfPlaneSet hz
  · exact ContDiffWithinAt.mul (by fun_prop) (cot_pi_mul_contDiffWithinAt k
      (

中文:
引理 iteratedDerivWithin_cot_pi_mul_sub_inv
  条件: {z : Complex} (hz : z in ℍₒ)
  证明: by
  simp_rw [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add hz isOpen_upperHalfPlaneSet.uniqueDiffOn]
  · simpa [iteratedDerivWithin_fun_neg] using! iteratedDerivWithin_one_div k
      isOpen_upperHalfPlaneSet hz
  · exact ContDiffWithinAt.mul (by fun_prop) (cot_pi_mul_contDiffWithinAt k
      (
-/
private lemma iteratedDerivWithin_cot_pi_mul_sub_inv {z : Complex} (hz : z in ℍₒ) :
    iteratedDerivWithin k (fun x : Complex => π * cot (π * x) - 1 / x) ℍₒ z =
    (iteratedDerivWithin k (fun x : Complex => π * cot (π * x)) ℍₒ z) -
    (-1) ^ k * k ! * (z ^ (-1 - k : Int)) := by
  simp_rw [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add hz isOpen_upperHalfPlaneSet.uniqueDiffOn]
  · simpa [iteratedDerivWithin_fun_neg] using! iteratedDerivWithin_one_div k
      isOpen_upperHalfPlaneSet hz
  · exact ContDiffWithinAt.mul (by fun_prop) (cot_pi_mul_contDiffWithinAt k
      (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))
  · simp only [one_div]
    apply ContDiffWithinAt.neg
    exact ContDiffWithinAt.inv (by fun_prop) (ne_zero ⟨z, hz⟩)

/--
lemma `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow` / 引理 `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow`

English:
lemma iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow
  given: {k : Nat} (hk : 1 <= k) {z : Complex} (hz : z in ℍₒ)
  proof: by
  have h0 := iteratedDerivWithin_cot_pi_mul_sub_inv k hz
  rw [iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum hk hz]; rw [add_comm] at h0
  rw [← add_left_inj (-(-1) ^ k * k ! * z ^ (-1 - k : Int))]; rw [h0]
  ring

中文:
引理 iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow
  条件: {k : 自然数} (hk : 1 <= k) {z : Complex} (hz : z in ℍₒ)
  证明: by
  have h0 := iteratedDerivWithin_cot_pi_mul_sub_inv k hz
  rw [iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum hk hz]; rw [add_comm] at h0
  rw [← add_left_inj (-(-1) ^ k * k ! * z ^ (-1 - k : Int))]; rw [h0]
  ring

Depends on / 依赖: add_comm, add_left_inj, iteratedDerivWithin_cot_pi_mul_sub_inv, iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum
-/
lemma iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow {k : Nat} (hk : 1 <= k) {z : Complex} (hz : z in ℍₒ) :
    iteratedDerivWithin k (fun x : Complex => π * cot (π * x)) ℍₒ z =
    (-1) ^ k * k ! * ∑' n : Int, (z + n) ^ (-1 - k : Int) := by
  have h0 := iteratedDerivWithin_cot_pi_mul_sub_inv k hz
  rw [iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum hk hz]; rw [add_comm] at h0
  rw [← add_left_inj (-(-1) ^ k * k ! * z ^ (-1 - k : Int))]; rw [h0]
  ring

/--
theorem `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow` / 定理 `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`

English:
theorem iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
  statement: {k : Nat} (hk : 1 <= k) {z : Complex}
  proof: by
  convert! iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow hk hz with n
  rw [show (-1 - k : Int) = -(k + 1 :) by norm_cast; lia]; rw [zpow_neg_coe_of_pos _ (by lia)]; rw [one_div]

中文:
定理 iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
  结论: {k : 自然数} (hk : 1 <= k) {z : Complex}
  证明: by
  convert! iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow hk hz with n
  rw [show (-1 - k : Int) = -(k + 1 :) by norm_cast; lia]; rw [zpow_neg_coe_of_pos _ (by lia)]; rw [one_div]

Depends on / 依赖: convert, iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow, one_div, zpow_neg_coe_of_pos
-/
theorem iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow {k : Nat} (hk : 1 <= k) {z : Complex}
    (hz : z in ℍₒ) :
    iteratedDerivWithin k (fun x : Complex => π * cot (π * x)) ℍₒ z =
      (-1) ^ k * k ! * ∑' n : Int, 1 / (z + n) ^ (k + 1) := by
  convert! iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow hk hz with n
  rw [show (-1 - k : Int) = -(k + 1 :) by norm_cast; lia]; rw [zpow_neg_coe_of_pos _ (by lia)]; rw [one_div]

end iteratedDeriv
