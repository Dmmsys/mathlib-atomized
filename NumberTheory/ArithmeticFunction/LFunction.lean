/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Construction of L-functions

This file constructs L-functions as formal Dirichlet series.

## Main definitions

* `ArithmeticFunction.ofPowerSeries q f`: L-function `f(q⁻ˢ)` obtained from a power series `f(T)`.
* `ArithmeticFunction.eulerProduct f`: the Euler product of a family `f i` of Dirichlet series.

## Implementation notes

We take the following route from polynomials to L-functions:
* Starting from a polynomial in `T`, `PowerSeries.invOfUnit` gives the reciporical power series.
* `ofPowerSeries` gives the local Euler factor as a formal Dirichlet series on powers of `q`.
* `eulerProduct` gives the L-function as the formal product of these local Euler factors.
* `LSeries` gives the L-function as an analytic function on the right half-plane of convergence.

For example, the Riemann zeta function `ζ(s)` corresponds to taking `1 - T` at each prime `p`.

For context, here is a diagram of the possible routes from polynomials to L-functions:
```
                   T=q⁻ˢ s ∈ ℂ
[polynomials in T] ----> [polynomials in q⁻ˢ] ----> [analytic function in s]
          | | |
          | (reciprocal) | (reciprocal) | (reciprocal)
          v T=q⁻ˢ V s ∈ ℂ V
[power series in T] ----> [power series in q⁻ˢ] ----> [analytic function in s] (the Euler factor)
          | | |
          | (product) | (product) | (product)
          v T=q⁻ˢ V s ∈ ℂ V
[multivariate power series] ----> [Dirichlet series] ----> [L-function in s] (the Euler product)
```
-/

@[expose] public section

namespace ArithmeticFunction

section PowerSeries

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofPowerSeries` / `ofPowerSeries` 的定义

English:
definition ofPowerSeries
  signature: (q : Nat)
  body: if hq : 1 < q then
    ⟨Function.extend (q ^ ·) (f.coeff ·) 0, by simp [Nat.ne_zero_of_lt hq]⟩ else
      algebraMap R (ArithmeticFunction R) f.constantCoeff
  map_zero' := by ext; split_ifs <;> simp [Function.extend]
  -- note that `ofPowerSeries.map_one'` relies on the junk value `f.constantCoeff`

中文:
定义 ofPowerSeries
  签名: (q : 自然数)
  定义体: if hq : 1 < q then
    ⟨Function.extend (q ^ ·) (f.coeff ·) 0, by simp [Nat.ne_zero_of_lt hq]⟩ else
      algebraMap R (ArithmeticFunction R) f.constantCoeff
  map_zero' := by ext; split_ifs <;> simp [Function.extend]
  -- note that `ofPowerSeries.map_one'` relies on the junk value `f.constantCoeff`
-/
noncomputable def ofPowerSeries (q : Nat) : PowerSeries R ->ₐ[R] ArithmeticFunction R where
  toFun f := if hq : 1 < q then
    ⟨Function.extend (q ^ ·) (f.coeff ·) 0, by simp [Nat.ne_zero_of_lt hq]⟩ else
      algebraMap R (ArithmeticFunction R) f.constantCoeff
  map_zero' := by ext; split_ifs <;> simp [Function.extend]
  -- note that `ofPowerSeries.map_one'` relies on the junk value `f.constantCoeff`.
  map_one' := by
    ext n
    split_ifs with hq
    · by_cases hn : exists k, q ^ k = n
      · obtain ⟨a, rfl⟩ := hn
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · simp [hn, one_apply_ne (fun H => hn ⟨0, H.symm⟩)]
    · simp
  map_add' f g := by
    ext n
    split_ifs with hq
    · by_cases h : exists a, q ^ a = n
      · obtain ⟨a, rfl⟩ := h
        simp [(Nat.pow_right_injective hq).extend_apply]
      · simp [h]
    · by_cases hn : n = 1 <;> simp [hn]
  map_mul' f g := by
    ext n
    split_ifs with hq
    · simp_rw [mul_apply, coe_mk]
      by_cases hn : exists a, q ^ a = n
      · obtain ⟨k, rfl⟩ := hn
        rw [(Nat.pow_right_injective hq).extend_apply]
        have hs : (Finset.antidiagonal k).map (.prodMap ⟨fun k => q ^ k, Nat.pow_right_injective hq⟩
            ⟨fun k => q ^ k, Nat.pow_right_injective hq⟩) subseteq (q ^ k).divisorsAntidiagonal :=
          Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow hq k
        rw [PowerSeries.coeff_mul k f g]; rw [← Finset.sum_subset hs]
        · simp [(Nat.pow_right_injective hq).extend_apply]
        · intro (a, b) hab h
          by_cases ha : exists i, q ^ i = a
          · by_cases hb : exists j, q ^ j = b
            · obtain ⟨i, rfl⟩ := ha
              obtain ⟨j, rfl⟩ := hb
              rw [Nat.mem_divisorsAntidiagonal]; rw [← pow_add]; rw [Nat.pow_right_inj hq] at hab
              simp_rw [Finset.mem_map, not_exists, not_and, Finset.mem_antidiagonal] at h
              simpa using h (i, j) hab.1
            · rwa [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
          · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
      · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply, Finset.sum_eq_zero]
        intro (a, b) hk
        obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hk
        by_cases ha : exists i, q ^ i = a
        · by_cases hb : exists j, q ^ j = b
          · obtain ⟨i, rfl⟩ := ha
            obtain ⟨j, rfl⟩ := hb
            rw [← pow_add] at hab
            exact (hn ⟨i + j, hab⟩).elim
          · rwa [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
        · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
    · simp
  commutes' x := by
    ext n
    split_ifs with hq
    · simp only [Algebra.algebraMap_eq_smul_one, coe_mk]
      by_cases hn : exists k, q ^ k = n
      · obtain ⟨k, rfl⟩ := hn
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply, smul_map, one_apply_ne, smul_zero]
        contrapose hn
        exact ⟨0, by simp [hn]⟩
    · simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ofPowerSeries_apply` / 定理 `ofPowerSeries_apply`

English:
theorem ofPowerSeries_apply
  given: {q : Nat} (hq : 1 < q) (f : PowerSeries R) (n : Nat)
  proof: by
  simp [ofPowerSeries, dif_pos hq]

中文:
定理 ofPowerSeries_apply
  条件: {q : 自然数} (hq : 1 < q) (f : PowerSeries R) (n : 自然数)
  证明: by
  simp [ofPowerSeries, dif_pos hq]

Depends on / 依赖: dif_pos, ofPowerSeries
-/
theorem ofPowerSeries_apply {q : Nat} (hq : 1 < q) (f : PowerSeries R) (n : Nat) :
    ofPowerSeries q f n = Function.extend (q ^ ·) (f.coeff ·) 0 n := by
  simp [ofPowerSeries, dif_pos hq]

/--
theorem `ofPowerSeries_apply_pow` / 定理 `ofPowerSeries_apply_pow`

English:
theorem ofPowerSeries_apply_pow
  given: {q : Nat} (hq : 1 < q) (f : PowerSeries R) (k : Nat)
  proof: by
  rw [ofPowerSeries_apply hq]; rw [(Nat.pow_right_injective hq).extend_apply]

中文:
定理 ofPowerSeries_apply_pow
  条件: {q : 自然数} (hq : 1 < q) (f : PowerSeries R) (k : 自然数)
  证明: by
  rw [ofPowerSeries_apply hq]; rw [(Nat.pow_right_injective hq).extend_apply]

Depends on / 依赖: Nat.pow_right_injective, extend_apply, ofPowerSeries_apply, pow_right_injective
-/
theorem ofPowerSeries_apply_pow {q : Nat} (hq : 1 < q) (f : PowerSeries R) (k : Nat) :
    ofPowerSeries q f (q ^ k) = f.coeff k := by
  rw [ofPowerSeries_apply hq]; rw [(Nat.pow_right_injective hq).extend_apply]

/--
theorem `ofPowerSeries_apply_zero` / 定理 `ofPowerSeries_apply_zero`

English:
theorem ofPowerSeries_apply_zero
  given: (q : Nat) (f : PowerSeries R)
  statement: ofPowerSeries q f 0 = 0
  proof: by
  simp

中文:
定理 ofPowerSeries_apply_zero
  条件: (q : 自然数) (f : PowerSeries R)
  结论: ofPowerSeries q f 0 = 0
  证明: by
  simp
-/
theorem ofPowerSeries_apply_zero (q : Nat) (f : PowerSeries R) : ofPowerSeries q f 0 = 0 := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
-- note that `ofPowerSeries_apply_one` relies on the junk value `f.constantCoeff`.
/--
theorem `ofPowerSeries_apply_one` / 定理 `ofPowerSeries_apply_one`

English:
theorem ofPowerSeries_apply_one
  given: (q : Nat) (f : PowerSeries R)
  proof: by
  by_cases hq : 1 < q
  · rw [← pow_zero q, ofPowerSeries_apply_pow hq, PowerSeries.coeff_zero_eq_constantCoeff]
  · simp [ofPowerSeries, dif_neg hq]

中文:
定理 ofPowerSeries_apply_one
  条件: (q : 自然数) (f : PowerSeries R)
  证明: by
  by_cases hq : 1 < q
  · rw [← pow_zero q, ofPowerSeries_apply_pow hq, PowerSeries.coeff_zero_eq_constantCoeff]
  · simp [ofPowerSeries, dif_neg hq]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_eq_constantCoeff, dif_neg, ofPowerSeries, ofPowerSeries_apply_pow, pow_zero
-/
theorem ofPowerSeries_apply_one (q : Nat) (f : PowerSeries R) :
    ofPowerSeries q f 1 = f.constantCoeff := by
  by_cases hq : 1 < q
  · rw [← pow_zero q, ofPowerSeries_apply_pow hq, PowerSeries.coeff_zero_eq_constantCoeff]
  · simp [ofPowerSeries, dif_neg hq]

end CommSemiring

section CommRing

variable [CommRing R]

/--
theorem `ofPowerSeries_pow` / 定理 `ofPowerSeries_pow`

English:
theorem ofPowerSeries_pow
  given: (q : Nat) {k : Nat} (hk : k != 0) (f : PowerSeries R)
  proof: by
  by_cases hq : 1 < q
  · ext n
    by_cases hn : exists i, q ^ i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [ofPowerSeries_apply_pow hq]; rw [PowerSeries.coeff_subst_X_pow hk]
      split_ifs with hn
      · obtain ⟨j, rfl⟩ := hn
        rw [pow_mul]; rw [ofPowerSeries_apply_pow (one_lt_pow' hq hk

中文:
定理 ofPowerSeries_pow
  条件: (q : 自然数) {k : 自然数} (hk : k != 0) (f : PowerSeries R)
  证明: by
  by_cases hq : 1 < q
  · ext n
    by_cases hn : exists i, q ^ i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [ofPowerSeries_apply_pow hq]; rw [PowerSeries.coeff_subst_X_pow hk]
      split_ifs with hn
      · obtain ⟨j, rfl⟩ := hn
        rw [pow_mul]; rw [ofPowerSeries_apply_pow (one_lt_pow' hq hk

Depends on / 依赖: Function, Function.extend_apply, Nat.pow_right_inj, Pi.zero_apply, PowerSeries, PowerSeries.coeff_subst_X_pow, coeff_subst_X_pow, dvd_def, eq_comm, extend_apply, ofPowerSeries_apply, ofPowerSeries_apply_pow, one_lt_pow, pow_mul, pow_right_inj, simp_rw, split_ifs, zero_apply
-/
theorem ofPowerSeries_pow (q : Nat) {k : Nat} (hk : k != 0) (f : PowerSeries R) :
    ofPowerSeries (q ^ k) f = ofPowerSeries q (f.subst (PowerSeries.X ^ k)) := by
  by_cases hq : 1 < q
  · ext n
    by_cases hn : exists i, q ^ i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [ofPowerSeries_apply_pow hq]; rw [PowerSeries.coeff_subst_X_pow hk]
      split_ifs with hn
      · obtain ⟨j, rfl⟩ := hn
        rw [pow_mul]; rw [ofPowerSeries_apply_pow (one_lt_pow' hq hk)]
        simp [hk]
      · rw [ofPowerSeries_apply (one_lt_pow' hq hk), Function.extend_apply', Pi.zero_apply]
        simp_rw [← pow_mul, Nat.pow_right_inj hq, eq_comm, ← dvd_def]
        exact hn
    · rwa [ofPowerSeries_apply hq, ofPowerSeries_apply (one_lt_pow' hq hk),
        Function.extend_apply', Function.extend_apply']
      contrapose! hn
      obtain ⟨i, rfl⟩ := hn
      exact ⟨k * i, pow_mul q k i⟩
  · simp [ofPowerSeries, hq, hk]

-- todo: generalize to `CommSemiring`
/--
theorem `isMultiplicative_ofPowerSeries_of_isPrimePow` / 定理 `isMultiplicative_ofPowerSeries_of_isPrimePow`

English:
theorem isMultiplicative_ofPowerSeries_of_isPrimePow
  proof: by
  refine ⟨(ofPowerSeries_apply_one q f).trans hf, fun {m n} hmn => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  rw [← Nat.prime_iff] at hp
  rw [ofPowerSeries_pow p hk.ne']
  by_cases hm : exists i, p ^ i = m
  · obtain ⟨i, rfl⟩ := hm
    by_cases hn : exists j, p ^ j = n
    · obtain ⟨j, rfl⟩ := hn


中文:
定理 isMultiplicative_ofPowerSeries_of_isPrimePow
  证明: by
  refine ⟨(ofPowerSeries_apply_one q f).trans hf, fun {m n} hmn => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  rw [← Nat.prime_iff] at hp
  rw [ofPowerSeries_pow p hk.ne']
  by_cases hm : exists i, p ^ i = m
  · obtain ⟨i, rfl⟩ := hm
    by_cases hn : exists j, p ^ j = n
    · obtain ⟨j, rfl⟩ := hn


Depends on / 依赖: Function, Function.extend_apply, Nat.prime_iff, Pi.zero_apply, extend_apply, hk.ne, hp.ne_one, hp.one_lt, ne_one, ofPowerSeries_apply, ofPowerSeries_apply_one, ofPowerSeries_pow, one_lt, prime_iff, simp_rw, zero_apply
-/
theorem isMultiplicative_ofPowerSeries_of_isPrimePow
    (q : Nat) (hq : IsPrimePow q) (f : PowerSeries R) (hf : f.constantCoeff = 1) :
    IsMultiplicative (ofPowerSeries q f) := by
  refine ⟨(ofPowerSeries_apply_one q f).trans hf, fun {m n} hmn => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  rw [← Nat.prime_iff] at hp
  rw [ofPowerSeries_pow p hk.ne']
  by_cases hm : exists i, p ^ i = m
  · obtain ⟨i, rfl⟩ := hm
    by_cases hn : exists j, p ^ j = n
    · obtain ⟨j, rfl⟩ := hn
      cases i
      · simp [hk.ne', hf]
      · cases j
        · simp [hk.ne', hf]
        · simp [hp.ne_one] at hmn
    · simp_rw [ofPowerSeries_apply hp.one_lt]
      rw [Function.extend_apply']; rw [Function.extend_apply' _ _ _ hn]; rw [Pi.zero_apply]; rw [Pi.zero_apply]; rw [mul_zero]
      contrapose! hn
      obtain ⟨j, hj⟩ := hn
      obtain ⟨v, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hj.symm)
      exact ⟨v, rfl⟩
  · simp_rw [ofPowerSeries_apply hp.one_lt]
    rw [Function.extend_apply']; rw [Function.extend_apply' _ _ _ hm]; rw [Pi.zero_apply]; rw [Pi.zero_apply]; rw [zero_mul]
    contrapose! hm
    obtain ⟨i, hi⟩ := hm
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨n, hi⟩
    exact ⟨j, rfl⟩

end CommRing

end PowerSeries

section EulerProduct

open Filter

variable {ι R : Type*} [CommSemiring R]

/-- A private uniform space instance on `ArithmeticFunction R` in order to define `eulerProduct` as
a `tprod`. If `R` is viewed as having the discrete topology, then the resulting topology on
`ArithmeticFunction R` is the topology of pointwise convergence (see `tendsto_iff`).

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance uniformSpace : UniformSpace (ArithmeticFunction R) :=
  letI : UniformSpace R := ⊥
  .comap ((↑) : ArithmeticFunction R -> (Nat -> R)) inferInstance

/--
theorem `tendsto_iff` / 定理 `tendsto_iff`

English:
theorem tendsto_iff
  proof: by
  let : UniformSpace R := ⊥
  have : Topology.IsInducing ((↑) : ArithmeticFunction R -> (Nat -> R)) := ⟨rfl⟩
  simp [this.tendsto_nhds_iff, tendsto_pi_nhds]

中文:
定理 tendsto_iff
  证明: by
  let : UniformSpace R := ⊥
  have : Topology.IsInducing ((↑) : ArithmeticFunction R -> (Nat -> R)) := ⟨rfl⟩
  simp [this.tendsto_nhds_iff, tendsto_pi_nhds]
-/
private theorem tendsto_iff
    {f : ι -> ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ forall n, forallᶠ i in F, f i n = g n := by
  let : UniformSpace R := ⊥
  have : Topology.IsInducing ((↑) : ArithmeticFunction R -> (Nat -> R)) := ⟨rfl⟩
  simp [this.tendsto_nhds_iff, tendsto_pi_nhds]

/-- The uniform space structure on arithmetic functions is complete.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : CompleteSpace (ArithmeticFunction R) := by
  let : UniformSpace R := ⊥
  apply IsUniformInducing.completeSpace ⟨rfl⟩
  apply IsClosed.isComplete
  have : Set.range ((↑) : ArithmeticFunction R -> (Nat -> R)) = {f | f 0 = 0} := by
    ext f
    exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩
  rw [ArithmeticFunction.range_coe]
  apply isClosed_setOfPred_map_zero

/--
Definition of `eulerProduct` / `eulerProduct` 的定义

English:
definition eulerProduct
  signature: (f : ι -> ArithmeticFunction R)
  body: ∏' i, f i

中文:
定义 eulerProduct
  签名: (f : ι -> ArithmeticFunction R)
  定义体: ∏' i, f i
-/
noncomputable def eulerProduct (f : ι -> ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

/--
theorem `tendsTo_eulerProduct_of_tendsTo` / 定理 `tendsTo_eulerProduct_of_tendsTo`

English:
theorem tendsTo_eulerProduct_of_tendsTo
  statement: (f : ι -> ArithmeticFunction R)
  proof: by
  let : UniformSpace R := ⊥
  have : IsUniformInducing ((↑) : ArithmeticFunction R -> (Nat -> R)) := ⟨rfl⟩
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, ← this.cauchy_map_iff,
    Filter.map_map, cauchy_map_iff', Pi

中文:
定理 tendsTo_eulerProduct_of_tendsTo
  结论: (f : ι -> ArithmeticFunction R)
  证明: by
  let : UniformSpace R := ⊥
  have : IsUniformInducing ((↑) : ArithmeticFunction R -> (Nat -> R)) := ⟨rfl⟩
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, ← this.cauchy_map_iff,
    Filter.map_map, cauchy_map_iff', Pi

Depends on / 依赖: ArithmeticFunction, CauchySeq, DiscreteUniformity, DiscreteUniformity.eq_principal_setRelId, Filter, Filter.map_map, Function, Function.comp_apply, IsUniformInducing, Multipliable, Pi.uniformity, SetRel, SetRel.mem_id, UniformSpace, cauchy_map_iff, classical, comp_apply, eq_principal_setRelId, eventually_atTop_prod_self, hasProd
-/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι -> ArithmeticFunction R)
    (hf : forall n, forallᶠ i in cofinite, f i n = (1 : ArithmeticFunction R) n) :
    forall n, forallᶠ s in atTop, (∏ i in s, f i) n = eulerProduct f n := by
  let : UniformSpace R := ⊥
  have : IsUniformInducing ((↑) : ArithmeticFunction R -> (Nat -> R)) := ⟨rfl⟩
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, ← this.cauchy_map_iff,
    Filter.map_map, cauchy_map_iff', Pi.uniformity, DiscreteUniformity.eq_principal_setRelId,
    tendsto_iInf, tendsto_comap_iff, tendsto_principal, Function.comp_apply, prod_atTop_atTop_eq,
    eventually_atTop_prod_self, SetRel.mem_id]
  intro n
  replace hf : forall k in Set.Iic n, forallᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk => hf k
  rw [← eventually_all_finite (Set.finite_Iic n)]; rw [eventually_iff_exists_mem] at hf
  obtain ⟨s, hs, hs'⟩ := hf
  let t := (mem_cofinite.mp hs).toFinset
  refine ⟨t, fun u v hu hv => ?_⟩
  rw [← Finset.prod_sdiff hu]; rw [← Finset.prod_sdiff hv]
  replace hu : forall i in u \ t, i in s := by
    intro i hi
    rw [Finset.mem_sdiff]; rw [Set.Finite.mem_toFinset]; rw [Set.notMem_compl_iff] at hi
    exact hi.2
  replace hv : forall i in v \ t, i in s := by
    intro i hi
    rw [Finset.mem_sdiff]; rw [Set.Finite.mem_toFinset]; rw [Set.notMem_compl_iff] at hi
    exact hi.2
  suffices forall k <= n, (∏ x in u \ t, f x) k = (∏ x in v \ t, f x) k by
    rw [mul_apply]; rw [mul_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [this k.1 (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hk))]
  suffices forall w, (forall i in w, i in s) -> forall k <= n, (∏ x in w, f x) k = (1 : ArithmeticFunction R) k by
    intro k hk
    rw [this (u \ t) hu k hk]; rw [this (v \ t) hv k hk]
  intro w hw
  induction w using Finset.induction_on
  case empty => simp
  case insert i w hi hw' =>
    intro k hk
    rw [← one_mul (1 : ArithmeticFunction R)]; rw [Finset.prod_insert hi]; rw [mul_apply]; rw [mul_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 := hs' i (hw i (Finset.mem_insert_self i w)) j.1
      ((Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    have h2 := hw' (fun i hi => hw i (Finset.mem_insert_of_mem hi)) j.2
      ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    rw [h1]; rw [h2]

/--
theorem `isMultiplicative_eulerProduct` / 定理 `isMultiplicative_eulerProduct`

English:
theorem isMultiplicative_eulerProduct
  statement: (f : ι -> ArithmeticFunction R)
  proof: by
  by_cases hf' : Multipliable f
  · have h (s : Finset ι) : (∏ b in s, f b).IsMultiplicative :=
      isMultiplicative_finsetProd f s fun i a => hf i
    have key := tendsto_iff.mp hf'.hasProd
    refine (forall_and.mp h).imp (fun h => ?_) fun h m n hmn => ?_
    · specialize key 1
      simp_rw 

中文:
定理 isMultiplicative_eulerProduct
  结论: (f : ι -> ArithmeticFunction R)
  证明: by
  by_cases hf' : Multipliable f
  · have h (s : Finset ι) : (∏ b in s, f b).IsMultiplicative :=
      isMultiplicative_finsetProd f s fun i a => hf i
    have key := tendsto_iff.mp hf'.hasProd
    refine (forall_and.mp h).imp (fun h => ?_) fun h m n hmn => ?_
    · specialize key 1
      simp_rw 

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, Finset, IsMultiplicative, Multipliable, eq_comm, eventually_const, eventually_const.mp, forall_and, forall_and.mp, hasProd, isMultiplicative_finsetProd, replace, simp_rw, specialize, tendsto_iff, tendsto_iff.mp
-/
theorem isMultiplicative_eulerProduct (f : ι -> ArithmeticFunction R)
    (hf : forall i, IsMultiplicative (f i)) : IsMultiplicative (eulerProduct f) := by
  by_cases hf' : Multipliable f
  · have h (s : Finset ι) : (∏ b in s, f b).IsMultiplicative :=
      isMultiplicative_finsetProd f s fun i a => hf i
    have key := tendsto_iff.mp hf'.hasProd
    refine (forall_and.mp h).imp (fun h => ?_) fun h m n hmn => ?_
    · specialize key 1
      simp_rw [h] at key
      rwa [eventually_const, eq_comm] at key
    · replace h s : (∏ b in s, f b) (m * n) = (∏ b in s, f b) m * (∏ b in s, f b) n := h s hmn
      have h2 := key (m * n)
      simp_rw [h] at h2
      exact eventually_const.mp (EventuallyEq.trans (.symm h2) (.mul (key m) (key n)))
  · rw [eulerProduct, tprod_eq_one_of_not_multipliable hf']
    exact isMultiplicative_one

/--
theorem `tendsTo_eulerProduct_ofPowerSeries` / 定理 `tendsTo_eulerProduct_ofPowerSeries`

English:
theorem tendsTo_eulerProduct_ofPowerSeries
  statement: (q : ι -> Nat) [hq : Northcott q]
  proof: by
  apply tendsTo_eulerProduct_of_tendsTo
  refine fun n => (tendsto_atTop.mp ((northcott_iff_tendsto q).mp hq) (n + 1)).mono fun i hi => ?_
  rcases n with rfl | rfl | n
  · simp
  · simp [hf]
  · have hqi : 1 < q i := by lia
    rw [ofPowerSeries_apply hqi]; rw [Function.extend_apply']; rw [Pi.ze

中文:
定理 tendsTo_eulerProduct_ofPowerSeries
  结论: (q : ι -> 自然数) [hq : Northcott q]
  证明: by
  apply tendsTo_eulerProduct_of_tendsTo
  refine fun n => (tendsto_atTop.mp ((northcott_iff_tendsto q).mp hq) (n + 1)).mono fun i hi => ?_
  rcases n with rfl | rfl | n
  · simp
  · simp [hf]
  · have hqi : 1 < q i := by lia
    rw [ofPowerSeries_apply hqi]; rw [Function.extend_apply']; rw [Pi.ze

Depends on / 依赖: Function, Function.extend_apply, Nat.le_pow, Pi.zero_apply, extend_apply, h.pos, le_pow, northcott_iff_tendsto, ofPowerSeries_apply, one_apply_ne, tendsTo_eulerProduct_of_tendsTo, tendsto_atTop, tendsto_atTop.mp, zero_apply
-/
theorem tendsTo_eulerProduct_ofPowerSeries (q : ι -> Nat) [hq : Northcott q]
    (f : ι -> PowerSeries R) (hf : forall i, (f i).constantCoeff = 1) (n : Nat) :
    forallᶠ s in atTop, (∏ i in s, ofPowerSeries (q i) (f i)) n =
      eulerProduct (fun i => ofPowerSeries (q i) (f i)) n := by
  apply tendsTo_eulerProduct_of_tendsTo
  refine fun n => (tendsto_atTop.mp ((northcott_iff_tendsto q).mp hq) (n + 1)).mono fun i hi => ?_
  rcases n with rfl | rfl | n
  · simp
  · simp [hf]
  · have hqi : 1 < q i := by lia
    rw [ofPowerSeries_apply hqi]; rw [Function.extend_apply']; rw [Pi.zero_apply]; rw [one_apply_ne (by lia)]
    rintro ⟨k, hk⟩
    have h : k != 0 := fun h => by simp_all
    grind [Nat.le_pow h.pos (a := q i)]

end EulerProduct

end ArithmeticFunction
