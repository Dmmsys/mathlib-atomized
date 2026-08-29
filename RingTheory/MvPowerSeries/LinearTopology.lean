/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.LinearTopology.basis`: the ideals of the ring of multivariate power series
  all coefficients the exponent of which is smaller than some bound vanish.

- `MvPowerSeries.LinearTopology.hasBasis_nhds_zero` :
  the two-sided ideals from `MvPowerSeries.LinearTopology.basis` form a basis
  of neighborhoods of `0` if the topology of `R` is (left and right) linear.

## Instances :

If `R` has a linear topology, then the product topology on `MvPowerSeries σ R`
is a linear topology.

This applies in particular when `R` has the discrete topology.

## Note

If we had an analogue of `PolynomialModule` for power series,
meaning that we could consider the `R⟦X⟧`-module `M⟦X⟧` when `M` is an `R`-module,
then one could prove that `M⟦X⟧` is linearly topologized over `R⟦X⟧`
whenever `M` is linearly topologized over `R`.
To recover the ring case, it would remain to show that the isomorphism between
`Rᵐᵒᵖ⟦X⟧` and `R⟦X⟧ᵐᵒᵖ` identifies their respective actions on `R⟦X⟧`.
(And likewise in the multivariate case.)

-/

@[expose] public section

namespace MvPowerSeries

namespace LinearTopology

open scoped Topology

open Set SetLike Filter

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: (σ : Type*) (R : Type*) [Ring R] (Jd : TwoSidedIdeal R × (σ ->₀ Nat))
  body: TwoSidedIdeal.mk' {f | forall e <= Jd.2, coeff e f in Jd.1}
    (by simp [coeff_zero])
    (fun hf hg e he => by rw [map_add]; exact add_mem (hf e he) (hg e he))
    (fun {f} hf e he => by simp only [map_neg, neg_mem, hf e he])
    (fun {f g} hg e he => by
      classical
      rw [coeff_mul]
      

中文:
定义 basis
  签名: (σ : 类型) (R : 类型) [Ring R] (Jd : TwoSidedIdeal R × (σ ->₀ 自然数))
  定义体: TwoSidedIdeal.mk' {f | forall e <= Jd.2, coeff e f in Jd.1}
    (by simp [coeff_zero])
    (fun hf hg e he => by rw [map_add]; exact add_mem (hf e he) (hg e he))
    (fun {f} hf e he => by simp only [map_neg, neg_mem, hf e he])
    (fun {f g} hg e he => by
      classical
      rw [coeff_mul]
      

Depends on / 依赖: Finset, Finset.HasAntidiagonal.antidiagonal.snd_le, HasAntidiagonal, TwoSidedIdea, TwoSidedIdeal, TwoSidedIdeal.mk, TwoSidedIdeal.mul_mem_left, add_mem, antidiagonal, classical, coeff_mul, coeff_zero, le_trans, map_add, map_neg, mul_mem_left, neg_mem, snd_le, sum_mem
-/
noncomputable def basis (σ : Type*) (R : Type*) [Ring R] (Jd : TwoSidedIdeal R × (σ ->₀ Nat)) :
    TwoSidedIdeal (MvPowerSeries σ R) :=
  TwoSidedIdeal.mk' {f | forall e <= Jd.2, coeff e f in Jd.1}
    (by simp [coeff_zero])
    (fun hf hg e he => by rw [map_add]; exact add_mem (hf e he) (hg e he))
    (fun {f} hf e he => by simp only [map_neg, neg_mem, hf e he])
    (fun {f g} hg e he => by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      exact TwoSidedIdeal.mul_mem_left _ _ _
        (hg _ (le_trans (Finset.HasAntidiagonal.antidiagonal.snd_le huv) he)))
    (fun {f g} hf e he => by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      exact TwoSidedIdeal.mul_mem_right _ _ _
        (hf _ (le_trans (Finset.HasAntidiagonal.antidiagonal.fst_le huv) he)))

variable {σ : Type*} {R : Type*} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_basis_iff` / 定理 `mem_basis_iff`

English:
theorem mem_basis_iff
  given: {f : MvPowerSeries σ R} {Jd : TwoSidedIdeal R × (σ ->₀ Nat)}
  proof: by
  simp [basis]

中文:
定理 mem_basis_iff
  条件: {f : MvPowerSeries σ R} {Jd : TwoSidedIdeal R × (σ ->₀ 自然数)}
  证明: by
  simp [basis]
-/
theorem mem_basis_iff {f : MvPowerSeries σ R} {Jd : TwoSidedIdeal R × (σ ->₀ Nat)} :
    f in basis σ R Jd ↔ forall e <= Jd.2, coeff e f in Jd.1 := by
  simp [basis]

/--
theorem `basis_le` / 定理 `basis_le`

English:
theorem basis_le
  given: {Jd Ke : TwoSidedIdeal R × (σ ->₀ Nat)} (hJK : Jd.1 <= Ke.1) (hed : Ke.2 <= Jd.2)
  proof: fun _ => forall_imp (fun _ h hue => hJK (h (le_trans hue hed)))

中文:
定理 basis_le
  条件: {Jd Ke : TwoSidedIdeal R × (σ ->₀ 自然数)} (hJK : Jd.1 <= Ke.1) (hed : Ke.2 <= Jd.2)
  证明: fun _ => forall_imp (fun _ h hue => hJK (h (le_trans hue hed)))

Depends on / 依赖: forall_imp, le_trans
-/
theorem basis_le {Jd Ke : TwoSidedIdeal R × (σ ->₀ Nat)} (hJK : Jd.1 <= Ke.1) (hed : Ke.2 <= Jd.2) :
    basis σ R Jd <= basis σ R Ke :=
  fun _ => forall_imp (fun _ h hue => hJK (h (le_trans hue hed)))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `basis_le_iff` / 定理 `basis_le_iff`

English:
theorem basis_le_iff
  given: {J K : TwoSidedIdeal R} {d e : σ ->₀ Nat} (hK : K != ⊤)
  proof: by
  classical
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', ofPred_subset_ofPred]
    intro h
    constructor
    · intro x hx
      have (d' : _) : coeff d' (C (σ := σ) x) in J := by
        rw [coeff_C]; split_ifs <;> [exact hx; exact J.zero_mem]
      simpa usi

中文:
定理 basis_le_iff
  条件: {J K : TwoSidedIdeal R} {d e : σ ->₀ 自然数} (hK : K != ⊤)
  证明: by
  classical
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', ofPred_subset_ofPred]
    intro h
    constructor
    · intro x hx
      have (d' : _) : coeff d' (C (σ := σ) x) in J := by
        rw [coeff_C]; split_ifs <;> [exact hx; exact J.zero_mem]
      simpa usi

Depends on / 依赖: J.zero_mem, TwoSidedIdeal, TwoSidedIdeal.coe_mk, TwoSidedIdeal.le_iff, classical, coe_mk, coeff_C, coeff_monomial, eq_top_iff, le_iff, monomial, ofPred_subset_ofPred, split_ifs, zero_le, zero_mem
-/
theorem basis_le_iff {J K : TwoSidedIdeal R} {d e : σ ->₀ Nat} (hK : K != ⊤) :
    basis σ R ⟨J, d⟩ <= basis σ R ⟨K, e⟩ ↔ J <= K ∧ e <= d := by
  classical
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', ofPred_subset_ofPred]
    intro h
    constructor
    · intro x hx
      have (d' : _) : coeff d' (C (σ := σ) x) in J := by
        rw [coeff_C]; split_ifs <;> [exact hx; exact J.zero_mem]
      simpa using h (C x) (fun _ _ => this _) _ zero_le
    · by_contra h'
      apply hK
      rw [eq_top_iff]
      intro x _
      have (d') (hd'_le : d' <= d) : coeff d' (monomial e x) in J := by
        rw [coeff_monomial]
        split_ifs with hd' <;> [exact (h' (hd' ▸ hd'_le)).elim; exact J.zero_mem]
      simpa using h (monomial e x) this _ le_rfl
  · rintro ⟨hJK, hed⟩
    exact basis_le hJK hed

variable [TopologicalSpace R]

-- We endow MvPowerSeries σ R with the product topology.
open WithPiTopology

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasBasis_nhds_zero` / 引理 `hasBasis_nhds_zero`

English:
lemma hasBasis_nhds_zero
  given: [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]
  proof: by
  classical
  rw [nhds_pi]
  refine IsLinearTopology.hasBasis_twoSidedIdeal.pi_self.to_hasBasis ?_ ?_
  · intro ⟨D, I⟩ ⟨hD, hI⟩
    refine ⟨⟨I, Finset.sup hD.toFinset id⟩, hI, fun f hf d hd => ?_⟩
    rw [SetLike.mem_coe]; rw [mem_basis_iff] at hf
convert! hf _ Finset.le_sup (hD.mem_toFinset.mpr 

中文:
引理 hasBasis_nhds_zero
  条件: [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]
  证明: by
  classical
  rw [nhds_pi]
  refine IsLinearTopology.hasBasis_twoSidedIdeal.pi_self.to_hasBasis ?_ ?_
  · intro ⟨D, I⟩ ⟨hD, hI⟩
    refine ⟨⟨I, Finset.sup hD.toFinset id⟩, hI, fun f hf d hd => ?_⟩
    rw [SetLike.mem_coe]; rw [mem_basis_iff] at hf
convert! hf _ Finset.le_sup (hD.mem_toFinset.mpr 

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup, IsLinearTopology, IsLinearTopology.hasBasis_twoSidedIdeal.pi_self.to_hasBasis, Set.pi, SetLike, SetLike.mem_coe, classical, coeff_apply, convert, finite_Iic, hD.mem_toFinset.mpr, hD.toFinset, hasBasis_twoSidedIdeal, le_sup, mem_basis_iff, mem_coe, mem_toFinset, nhds_pi
-/
lemma hasBasis_nhds_zero [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 0 : Filter (MvPowerSeries σ R)).HasBasis
      (fun Id : TwoSidedIdeal R × (σ ->₀ Nat) => (Id.1 : Set R) in 𝓝 0)
      (fun Id => basis _ _ Id) := by
  classical
  rw [nhds_pi]
  refine IsLinearTopology.hasBasis_twoSidedIdeal.pi_self.to_hasBasis ?_ ?_
  · intro ⟨D, I⟩ ⟨hD, hI⟩
    refine ⟨⟨I, Finset.sup hD.toFinset id⟩, hI, fun f hf d hd => ?_⟩
    rw [SetLike.mem_coe]; rw [mem_basis_iff] at hf
convert! hf _ Finset.le_sup (hD.mem_toFinset.mpr hd)
  · intro ⟨I, d⟩ hI
    refine ⟨⟨Iic d, I⟩, ⟨finite_Iic d, hI⟩, ?_⟩
    simpa [basis, coeff_apply, Iic, Set.pi] using! subset_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLinearTopology
  signature: R R] [IsLinearTopology Rᵐᵒᵖ R] :
  body: IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero TwoSidedIdeal.mul_mem_left

中文:
实例 [IsLinearTopology
  签名: R R] [IsLinearTopology Rᵐᵒᵖ R] :
  定义体: IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero TwoSidedIdeal.mul_mem_left

Depends on / 依赖: IsLinearTopology, IsLinearTopology.mk_of_hasBasis, TwoSidedIdeal, TwoSidedIdeal.mul_mem_left, hasBasis_nhds_zero, mk_of_hasBasis, mul_mem_left
-/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R) (MvPowerSeries σ R) :=
  IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero TwoSidedIdeal.mul_mem_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLinearTopology
  signature: R R] [IsLinearTopology Rᵐᵒᵖ R] :
  body: IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero (fun J _ _ hg => J.mul_mem_right _ _ hg)

中文:
实例 [IsLinearTopology
  签名: R R] [IsLinearTopology Rᵐᵒᵖ R] :
  定义体: IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero (fun J _ _ hg => J.mul_mem_right _ _ hg)

Depends on / 依赖: IsLinearTopology, IsLinearTopology.mk_of_hasBasis, J.mul_mem_right, hasBasis_nhds_zero, mk_of_hasBasis, mul_mem_right
-/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R)ᵐᵒᵖ (MvPowerSeries σ R) :=
  IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero (fun J _ _ hg => J.mul_mem_right _ _ hg)

/--
theorem `isTopologicallyNilpotent_of_constantCoeff` / 定理 `isTopologicallyNilpotent_of_constantCoeff`

English:
theorem isTopologicallyNilpotent_of_constantCoeff
  proof: by
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero,
    IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro d I hI
  replace hf := hf.eventually_mem hI
  simp_rw [eventually_atTop, SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem,
    map_pow, ← coeff_map, ← consta

中文:
定理 isTopologicallyNilpotent_of_constantCoeff
  证明: by
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero,
    IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro d I hI
  replace hf := hf.eventually_mem hI
  simp_rw [eventually_atTop, SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem,
    map_pow, ← coeff_map, ← consta

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, IsLinearTopology, IsLinearTopology.hasBasis_ideal.tendsto_right_iff, IsTopologicallyNilpotent, Quotient, SetLike, SetLike.mem_coe, coeff_eq_zero_of_constantCoeff_nilpotent, coeff_map, coeff_zero, constantCoeff_map, d.degree, degree, eq_zero_iff_mem, eventually_atTop, eventually_mem, hasBasis_ideal, hf.eventually_mem, le_rfl, map_pow
-/
theorem isTopologicallyNilpotent_of_constantCoeff
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R]
    {f : MvPowerSeries σ R} (hf : IsTopologicallyNilpotent (constantCoeff f)) :
    IsTopologicallyNilpotent f := by
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero,
    IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro d I hI
  replace hf := hf.eventually_mem hI
  simp_rw [eventually_atTop, SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem,
    map_pow, ← coeff_map, ← constantCoeff_map] at hf ⊢
  obtain ⟨N, hN⟩ := hf
  use N + d.degree
  intro n hn
  simpa only [map_pow] using coeff_eq_zero_of_constantCoeff_nilpotent (hN N le_rfl) hn

/--
theorem `isTopologicallyNilpotent_iff_constantCoeff` / 定理 `isTopologicallyNilpotent_iff_constantCoeff`

English:
theorem isTopologicallyNilpotent_iff_constantCoeff
  proof: by
  refine ⟨fun H => ?_, isTopologicallyNilpotent_of_constantCoeff⟩
  replace H : Tendsto (fun n => constantCoeff (f ^ n)) atTop (nhds 0) :=
.comp H .tendsto' 0 0 constantCoeff_zero continuous_constantCoeff R
  simpa only [map_pow] using! H

中文:
定理 isTopologicallyNilpotent_iff_constantCoeff
  证明: by
  refine ⟨fun H => ?_, isTopologicallyNilpotent_of_constantCoeff⟩
  replace H : Tendsto (fun n => constantCoeff (f ^ n)) atTop (nhds 0) :=
.comp H .tendsto' 0 0 constantCoeff_zero continuous_constantCoeff R
  simpa only [map_pow] using! H

Depends on / 依赖: Tendsto, constantCoeff, constantCoeff_zero, continuous_constantCoeff, isTopologicallyNilpotent_of_constantCoeff, map_pow, replace, tendsto
-/
theorem isTopologicallyNilpotent_iff_constantCoeff
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R] (f : MvPowerSeries σ R) :
    Tendsto (fun n : Nat => f ^ n) atTop (nhds 0) ↔
      IsTopologicallyNilpotent (constantCoeff f) := by
  refine ⟨fun H => ?_, isTopologicallyNilpotent_of_constantCoeff⟩
  replace H : Tendsto (fun n => constantCoeff (f ^ n)) atTop (nhds 0) :=
.comp H .tendsto' 0 0 constantCoeff_zero continuous_constantCoeff R
  simpa only [map_pow] using! H

end LinearTopology

end MvPowerSeries
