/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
# Lemmas on infinite sums over the antidiagonal of the divisors function

This file contains lemmas about the antidiagonal of the divisors function. It defines the map from
`Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b` to `(a, b)`.

We then prove some identities about the infinite sums over this antidiagonal, such as
`∑' n : ℕ+, n ^ k * r ^ n / (1 - r ^ n) = ∑' n : ℕ+, σ k n * r ^ n`
which are used for Eisenstein series and their q-expansions. This is also a special case of
Lambert series.

-/

@[expose] public section

open Filter Complex ArithmeticFunction Nat Topology

/--
Definition of `divisorsAntidiagonalFactors` / `divisorsAntidiagonalFactors` 的定义

English:
definition divisorsAntidiagonalFactors
  signature: (n : Nat+)
  body: fun x =>
  ⟨⟨x.1.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal x.2)⟩,
    (⟨x.1.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩ : Nat+),
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩

中文:
定义 divisorsAntidiagonalFactors
  签名: (n : 自然数+)
  定义体: fun x =>
  ⟨⟨x.1.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal x.2)⟩,
    (⟨x.1.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩ : Nat+),
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩
-/
def divisorsAntidiagonalFactors (n : Nat+) : Nat.divisorsAntidiagonal n -> Nat+ × Nat+ := fun x =>
  ⟨⟨x.1.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal x.2)⟩,
    (⟨x.1.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩ : Nat+),
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩

/--
lemma `divisorsAntidiagonalFactors_eq` / 引理 `divisorsAntidiagonalFactors_eq`

English:
lemma divisorsAntidiagonalFactors_eq
  given: {n : Nat+} (x : Nat.divisorsAntidiagonal n)
  proof: by
  simp [divisorsAntidiagonalFactors, (Nat.mem_divisorsAntidiagonal.mp x.2).1]

中文:
引理 divisorsAntidiagonalFactors_eq
  条件: {n : 自然数+} (x : 自然数.divisorsAntidiagonal n)
  证明: by
  simp [divisorsAntidiagonalFactors, (Nat.mem_divisorsAntidiagonal.mp x.2).1]

Depends on / 依赖: Nat.mem_divisorsAntidiagonal.mp, divisorsAntidiagonalFactors, mem_divisorsAntidiagonal
-/
lemma divisorsAntidiagonalFactors_eq {n : Nat+} (x : Nat.divisorsAntidiagonal n) :
    (divisorsAntidiagonalFactors n x).1.1 * (divisorsAntidiagonalFactors n x).2.1 = n := by
  simp [divisorsAntidiagonalFactors, (Nat.mem_divisorsAntidiagonal.mp x.2).1]

/--
lemma `divisorsAntidiagonalFactors_one` / 引理 `divisorsAntidiagonalFactors_one`

English:
lemma divisorsAntidiagonalFactors_one
  given: (x : Nat.divisorsAntidiagonal 1)
  proof: by
  have h := Nat.mem_divisorsAntidiagonal.mp x.2
  simp only [mul_eq_one, ne_eq, one_ne_zero, not_false_eq_true, and_true] at h
  simp [divisorsAntidiagonalFactors, h.1, h.2]

中文:
引理 divisorsAntidiagonalFactors_one
  条件: (x : 自然数.divisorsAntidiagonal 1)
  证明: by
  have h := Nat.mem_divisorsAntidiagonal.mp x.2
  simp only [mul_eq_one, ne_eq, one_ne_zero, not_false_eq_true, and_true] at h
  simp [divisorsAntidiagonalFactors, h.1, h.2]

Depends on / 依赖: Nat.mem_divisorsAntidiagonal.mp, and_true, divisorsAntidiagonalFactors, mem_divisorsAntidiagonal, mul_eq_one, ne_eq, not_false_eq_true, one_ne_zero
-/
lemma divisorsAntidiagonalFactors_one (x : Nat.divisorsAntidiagonal 1) :
    (divisorsAntidiagonalFactors 1 x) = (1, 1) := by
  have h := Nat.mem_divisorsAntidiagonal.mp x.2
  simp only [mul_eq_one, ne_eq, one_ne_zero, not_false_eq_true, and_true] at h
  simp [divisorsAntidiagonalFactors, h.1, h.2]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sigmaAntidiagonalEquivProd` / `sigmaAntidiagonalEquivProd` 的定义

English:
definition sigmaAntidiagonalEquivProd
  signature: : (Σ n : Nat+, Nat.divisorsAntidiagonal n) ≃ Nat+ × Nat+ where
  body: divisorsAntidiagonalFactors x.1 x.2
  invFun x :=
    ⟨⟨x.1.val * x.2.val, mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by simp [Nat.mem_divisorsAntidiagonal]⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    ext <;> simp [divisorsAntidiagonalFactors, ← PNat.coe_injecti

中文:
定义 sigmaAntidiagonalEquivProd
  签名: : (Σ n : 自然数+, 自然数.divisorsAntidiagonal n) ≃ 自然数+ × 自然数+ where
  定义体: divisorsAntidiagonalFactors x.1 x.2
  invFun x :=
    ⟨⟨x.1.val * x.2.val, mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by simp [Nat.mem_divisorsAntidiagonal]⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    ext <;> simp [divisorsAntidiagonalFactors, ← PNat.coe_injecti

Depends on / 依赖: divisorsAntidiagonalFactors
-/
def sigmaAntidiagonalEquivProd : (Σ n : Nat+, Nat.divisorsAntidiagonal n) ≃ Nat+ × Nat+ where
  toFun x := divisorsAntidiagonalFactors x.1 x.2
  invFun x :=
    ⟨⟨x.1.val * x.2.val, mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by simp [Nat.mem_divisorsAntidiagonal]⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    ext <;> simp [divisorsAntidiagonalFactors, ← PNat.coe_injective.eq_iff, h.1]
  right_inv _ := rfl

/--
lemma `sigmaAntidiagonalEquivProd_symm_apply_fst` / 引理 `sigmaAntidiagonalEquivProd_symm_apply_fst`

English:
lemma sigmaAntidiagonalEquivProd_symm_apply_fst
  given: (x : Nat+ × Nat+)
  proof: rfl

中文:
引理 sigmaAntidiagonalEquivProd_symm_apply_fst
  条件: (x : 自然数+ × 自然数+)
  证明: rfl
-/
lemma sigmaAntidiagonalEquivProd_symm_apply_fst (x : Nat+ × Nat+) :
    (sigmaAntidiagonalEquivProd.symm x).1 = x.1.1 * x.2.1 := rfl

/--
lemma `sigmaAntidiagonalEquivProd_symm_apply_snd` / 引理 `sigmaAntidiagonalEquivProd_symm_apply_snd`

English:
lemma sigmaAntidiagonalEquivProd_symm_apply_snd
  given: (x : Nat+ × Nat+)
  proof: rfl

中文:
引理 sigmaAntidiagonalEquivProd_symm_apply_snd
  条件: (x : 自然数+ × 自然数+)
  证明: rfl
-/
lemma sigmaAntidiagonalEquivProd_symm_apply_snd (x : Nat+ × Nat+) :
    (sigmaAntidiagonalEquivProd.symm x).2 = (x.1.1, x.2.1) := rfl

section tsum

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormSMulClass Int 𝕜]

omit [NormSMulClass Int 𝕜] in
/--
lemma `summable_norm_pow_mul_geometric_div_one_sub` / 引理 `summable_norm_pow_mul_geometric_div_one_sub`

English:
lemma summable_norm_pow_mul_geometric_div_one_sub
  given: (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1)
  proof: by
  simp only [div_eq_mul_one_div (_ * _ ^ _)]
  apply Summable.mul_tendsto_const (c := 1 / (1 - 0))
    (by simpa using! summable_norm_pow_mul_geometric_of_norm_lt_one k hr)
  simpa only [Nat.cofinite_eq_atTop] using!
   tendsto_const_nhds.div ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).const

中文:
引理 summable_norm_pow_mul_geometric_div_one_sub
  条件: (k : 自然数) {r : 𝕜} (hr : ‖r‖ < 1)
  证明: by
  simp only [div_eq_mul_one_div (_ * _ ^ _)]
  apply Summable.mul_tendsto_const (c := 1 / (1 - 0))
    (by simpa using! summable_norm_pow_mul_geometric_of_norm_lt_one k hr)
  simpa only [Nat.cofinite_eq_atTop] using!
   tendsto_const_nhds.div ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).const

Depends on / 依赖: Nat.cofinite_eq_atTop, Summable, Summable.mul_tendsto_const, cofinite_eq_atTop, const_sub, div_eq_mul_one_div, mul_tendsto_const, summable_norm_pow_mul_geometric_of_norm_lt_one, tendsto_const_nhds, tendsto_const_nhds.div, tendsto_pow_atTop_nhds_zero_of_norm_lt_one
-/
lemma summable_norm_pow_mul_geometric_div_one_sub (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun n : Nat => n ^ k * r ^ n / (1 - r ^ n) := by
  simp only [div_eq_mul_one_div (_ * _ ^ _)]
  apply Summable.mul_tendsto_const (c := 1 / (1 - 0))
    (by simpa using! summable_norm_pow_mul_geometric_of_norm_lt_one k hr)
  simpa only [Nat.cofinite_eq_atTop] using!
   tendsto_const_nhds.div ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).const_sub 1) (by simp)

/--
lemma `summable_divisorsAntidiagonal_aux` / 引理 `summable_divisorsAntidiagonal_aux`

English:
lemma summable_divisorsAntidiagonal_aux
  given: (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1)
  proof: by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => by positivity)]
  constructor
  · exact fun n => (hasSum_fintype _).summable
  · simp only [norm_mul, norm_pow, tsum_fintype, Finset.univ_eq_attach]
    apply Summable.of_nonneg_of_le (f := fun c : Nat+ => ‖(c : 𝕜) ^ (k + 1) * r ^ 

中文:
引理 summable_divisorsAntidiagonal_aux
  条件: (k : 自然数) {r : 𝕜} (hr : ‖r‖ < 1)
  证明: by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => by positivity)]
  constructor
  · exact fun n => (hasSum_fintype _).summable
  · simp only [norm_mul, norm_pow, tsum_fintype, Finset.univ_eq_attach]
    apply Summable.of_nonneg_of_le (f := fun c : Nat+ => ‖(c : 𝕜) ^ (k + 1) * r ^ 
-/
private lemma summable_divisorsAntidiagonal_aux (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (n : Nat+) × {x // x in (n : Nat).divisorsAntidiagonal} =>
    (c.2.1.2) ^ k * (r ^ (c.2.1.1 * c.2.1.2)) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => by positivity)]
  constructor
  · exact fun n => (hasSum_fintype _).summable
  · simp only [norm_mul, norm_pow, tsum_fintype, Finset.univ_eq_attach]
    apply Summable.of_nonneg_of_le (f := fun c : Nat+ => ‖(c : 𝕜) ^ (k + 1) * r ^ (c : Nat)‖)
      (fun b => Finset.sum_nonneg (fun _ _ => mul_nonneg (by simp) (by simp))) (fun b => ?_)
      (by apply (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) hr).subtype)
    transitivity ∑ _ in (b : Nat).divisors, ‖(b : 𝕜)‖ ^ k * ‖r ^ (b : Nat)‖
    · rw [(b : Nat).divisorsAntidiagonal.sum_attach (fun x => ‖(x.2 : 𝕜)‖ ^ _ * _ ^ (x.1 * x.2)),
          sum_divisorsAntidiagonal ((fun x y => ‖(y : 𝕜)‖ ^ k * _ ^ (x * y)))]
      gcongr with i hi
      · simpa using! le_of_dvd b.2 (div_dvd_of_dvd (dvd_of_mem_divisors hi))
      · rw [norm_pow, mul_comm, Nat.div_mul_cancel (dvd_of_mem_divisors hi)]
    · simp only [norm_pow, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, add_comm k 1, pow_add,
        pow_one, norm_mul]
      gcongr
      simpa using! Nat.card_divisors_le_self b

/--
theorem `summable_prod_mul_pow` / 定理 `summable_prod_mul_pow`

English:
theorem summable_prod_mul_pow
  given: (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1)
  proof: by
  simpa [sigmaAntidiagonalEquivProd.summable_iff.symm] using! summable_divisorsAntidiagonal_aux k hr

中文:
定理 summable_prod_mul_pow
  条件: (k : 自然数) {r : 𝕜} (hr : ‖r‖ < 1)
  证明: by
  simpa [sigmaAntidiagonalEquivProd.summable_iff.symm] using! summable_divisorsAntidiagonal_aux k hr

Depends on / 依赖: sigmaAntidiagonalEquivProd, sigmaAntidiagonalEquivProd.summable_iff.symm, summable_divisorsAntidiagonal_aux, summable_iff
-/
theorem summable_prod_mul_pow (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (Nat+ × Nat+) => c.2 ^ k * (r ^ (c.1 * c.2 : Nat)) := by
  simpa [sigmaAntidiagonalEquivProd.summable_iff.symm] using! summable_divisorsAntidiagonal_aux k hr

-- access notation `σ`
open scoped sigma

/--
theorem `tsum_prod_pow_eq_tsum_sigma` / 定理 `tsum_prod_pow_eq_tsum_sigma`

English:
theorem tsum_prod_pow_eq_tsum_sigma
  given: (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1)
  proof: by
  suffices ∑' c : Nat+ × Nat+, c.2 ^ k * r ^ (c.1 * c.2 : Nat) =
    ∑' e : Nat+, σ k e * r ^ (e : Nat) by rwa [← (summable_prod_mul_pow k hr).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, s

中文:
定理 tsum_prod_pow_eq_tsum_sigma
  条件: (k : 自然数) {r : 𝕜} (hr : ‖r‖ < 1)
  证明: by
  suffices ∑' c : Nat+ × Nat+, c.2 ^ k * r ^ (c.1 * c.2 : Nat) =
    ∑' e : Nat+, σ k e * r ^ (e : Nat) by rwa [← (summable_prod_mul_pow k hr).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, s

Depends on / 依赖: Equiv.coe_fn_mk, Finset, Finset.sum_mul, PNat.mk_coe, Summable, Summable.tsum_sigma, cast_pow, cast_sum, coe_fn_mk, divisorsAntidiagonal, divisorsAntidiagonal.sum_attach, divisorsAntidiagonalFactors, mk_coe, sigmaAntidiagonalEquivProd, sigmaAntidiagonalEquivProd.tsum_eq, sigma_eq_sum_div, sum_attach, sum_mul, summable_divisorsAntidiagonal_aux, summable_prod_mul_pow
-/
theorem tsum_prod_pow_eq_tsum_sigma (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' d : Nat+, ∑' c : Nat+, c ^ k * r ^ (d * c : Nat) = ∑' e : Nat+, σ k e * r ^ (e : Nat) := by
  suffices ∑' c : Nat+ × Nat+, c.2 ^ k * r ^ (c.1 * c.2 : Nat) =
    ∑' e : Nat+, σ k e * r ^ (e : Nat) by rwa [← (summable_prod_mul_pow k hr).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, sigma_eq_sum_div, cast_sum,
    cast_pow, Summable.tsum_sigma (summable_divisorsAntidiagonal_aux k hr :)]
  refine tsum_congr fun n => ?_
  simpa [tsum_fintype, Finset.sum_mul,
    (n : Nat).divisorsAntidiagonal.sum_attach fun x : Nat × Nat => x.2 ^ k * r ^ (x.1 * x.2),
    sum_divisorsAntidiagonal fun x y => y ^ k * r ^ (x * y)]
      using Finset.sum_congr rfl fun i hi => by rw [Nat.mul_div_cancel' (dvd_of_mem_divisors hi)]

/--
lemma `tsum_pow_div_one_sub_eq_tsum_sigma` / 引理 `tsum_pow_div_one_sub_eq_tsum_sigma`

English:
lemma tsum_pow_div_one_sub_eq_tsum_sigma
  given: {r : 𝕜} (hr : ‖r‖ < 1) (k : Nat)
  proof: by
  have (m : Nat) [NeZero m] := tsum_geometric_of_norm_lt_one (ξ := r ^ m)
    (by simpa using pow_lt_one₀ (by simp) hr (NeZero.ne _))
  simp only [div_eq_mul_inv, ← this, ← tsum_mul_left, mul_assoc, ← _root_.pow_succ',
    ← fun (n : Nat) => tsum_pnat_eq_tsum_succ (f := fun m => n ^ k * (r ^ n) ^

中文:
引理 tsum_pow_div_one_sub_eq_tsum_sigma
  条件: {r : 𝕜} (hr : ‖r‖ < 1) (k : 自然数)
  证明: by
  have (m : Nat) [NeZero m] := tsum_geometric_of_norm_lt_one (ξ := r ^ m)
    (by simpa using pow_lt_one₀ (by simp) hr (NeZero.ne _))
  simp only [div_eq_mul_inv, ← this, ← tsum_mul_left, mul_assoc, ← _root_.pow_succ',
    ← fun (n : Nat) => tsum_pnat_eq_tsum_succ (f := fun m => n ^ k * (r ^ n) ^

Depends on / 依赖: NeZero, NeZero.ne, Summable, Summable.tsum_comm, _root_, _root_.pow_succ, b.val, c.val, div_eq_mul_inv, mul_assoc, mul_comm, pow_mul, pow_succ, prod_symm, summable_prod_mul_pow, tsum_comm, tsum_geometric_of_norm_lt_one, tsum_mul_left, tsum_pnat_eq_tsum_succ, tsum_prod_pow_eq_tsum_sigma
-/
lemma tsum_pow_div_one_sub_eq_tsum_sigma {r : 𝕜} (hr : ‖r‖ < 1) (k : Nat) :
    ∑' n : Nat+, n ^ k * r ^ (n : Nat) / (1 - r ^ (n : Nat)) = ∑' n : Nat+, σ k n * r ^ (n : Nat) := by
  have (m : Nat) [NeZero m] := tsum_geometric_of_norm_lt_one (ξ := r ^ m)
    (by simpa using pow_lt_one₀ (by simp) hr (NeZero.ne _))
  simp only [div_eq_mul_inv, ← this, ← tsum_mul_left, mul_assoc, ← _root_.pow_succ',
    ← fun (n : Nat) => tsum_pnat_eq_tsum_succ (f := fun m => n ^ k * (r ^ n) ^ m)]
  have h00 := tsum_prod_pow_eq_tsum_sigma k hr
  rw [Summable.tsum_comm (by apply (summable_prod_mul_pow k hr).prod_symm)] at h00
  rw [← h00]
exact tsum_congr₂ fun b c => by simp [mul_comm c.val b.val, pow_mul]

omit [CompleteSpace 𝕜] [NormSMulClass Int 𝕜] in
/--
lemma `tendsto_zero_geometric_tsum_pnat` / 引理 `tendsto_zero_geometric_tsum_pnat`

English:
lemma tendsto_zero_geometric_tsum_pnat
  given: {r : 𝕜} (hr : ‖r‖ < 1)
  proof: by
  have h1 (m : Nat+) : ‖r ^ (m : Nat)‖ < 1 := by
    rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne _)]
  have h2 (m : Nat+) : ∑' n : Nat+, r ^ (n * m : Nat) = (1 - r ^ (m : Nat))⁻¹ - 1 := by
    have := tsum_geometric_of_norm_lt_one (h1 m)
    rw [← tsum_zero_pnat_eq_tsum_nat

中文:
引理 tendsto_zero_geometric_tsum_pnat
  条件: {r : 𝕜} (hr : ‖r‖ < 1)
  证明: by
  have h1 (m : Nat+) : ‖r ^ (m : Nat)‖ < 1 := by
    rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne _)]
  have h2 (m : Nat+) : ∑' n : Nat+, r ^ (n * m : Nat) = (1 - r ^ (m : Nat))⁻¹ - 1 := by
    have := tsum_geometric_of_norm_lt_one (h1 m)
    rw [← tsum_zero_pnat_eq_tsum_nat

Depends on / 依赖: NeZero, NeZero.ne, add_sub_cancel_left, mul_comm, norm_nonneg, norm_pow, pow_lt_one_iff_of_nonneg, pow_mul, pow_zero, simp_rw, summable_geometric_of_norm_lt_one, tendsto_sub_const_iff, tsum_geometric_of_norm_lt_one, tsum_zero_pnat_eq_tsum_nat
-/
lemma tendsto_zero_geometric_tsum_pnat {r : 𝕜} (hr : ‖r‖ < 1) :
    Tendsto (fun m : Nat+ => ∑' n : Nat+, r ^ (n * m : Nat)) atTop (𝓝 0) := by
  have h1 (m : Nat+) : ‖r ^ (m : Nat)‖ < 1 := by
    rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne _)]
  have h2 (m : Nat+) : ∑' n : Nat+, r ^ (n * m : Nat) = (1 - r ^ (m : Nat))⁻¹ - 1 := by
    have := tsum_geometric_of_norm_lt_one (h1 m)
    rw [← tsum_zero_pnat_eq_tsum_nat (summable_geometric_of_norm_lt_one (h1 m) :)] at this
    simp_rw [← this, pow_zero, add_sub_cancel_left, mul_comm, pow_mul]
  rw [funext h2]; rw [(by simp : 𝓝 (0 : 𝕜) = 𝓝 ((1 - 0)⁻¹ - 1))]; rw [tendsto_sub_const_iff]; rw [tendsto_inv_iff₀ (by simp)]; rw [tendsto_const_sub_iff]
exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).comp tendsto_PNat_val_atTop_atTop

end tsum
