/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the set.
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/

public section


namespace MeasureTheory

open ENNReal Module MeasureTheory MeasureTheory.Measure Set Filter

open scoped Pointwise NNReal

variable {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

/--
theorem `exists_pair_mem_lattice_not_disjoint_vadd` / 定理 `exists_pair_mem_lattice_not_disjoint_vadd`

English:
theorem exists_pair_mem_lattice_not_disjoint_vadd
  statement: [AddGroup L] [Countable L] [AddAction L E]
  proof: by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_ri

中文:
定理 exists_pair_mem_lattice_not_disjoint_vadd
  结论: [AddGroup L] [Countable L] [AddAction L E]
  证明: by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_ri

Depends on / 依赖: Pairwise, Pairwise.mono, Set.iUnion_subset, Set.inter_subset_right, aedisjoint, contrapose, fund.measure_eq_tsum, fund.nullMeasurableSet, hS.vadd, hij.mono, iUnion_subset, inf_le_left, inter_subset_right, measure_eq_tsum, measure_mono, nullMeasurableSet, trans_le
-/
theorem exists_pair_mem_lattice_not_disjoint_vadd [AddGroup L] [Countable L] [AddAction L E]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    exists x y : L, x != y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_right)

/--
theorem `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` / 定理 `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`

English:
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
  statement: [NormedAddCommGroup E]
  proof: by
  have h_vol : μ F < μ ((2⁻¹ : Real) • s) := by
    rw [addHaar_smul_of_nonneg μ (by simp : 0 <= (2 : Real)⁻¹) s]; rw [← ENNReal.mul_lt_mul_iff_left (pow_ne_zero (finrank Real E) (two_ne_zero' _)) (by finiteness)]; rw [mul_right_comm]; rw [ofReal_pow (by simp : 0 <= (2 : Real)⁻¹)]; rw [ofReal_inv

中文:
定理 exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
  结论: [NormedAddCommGroup E]
  证明: by
  have h_vol : μ F < μ ((2⁻¹ : Real) • s) := by
    rw [addHaar_smul_of_nonneg μ (by simp : 0 <= (2 : Real)⁻¹) s]; rw [← ENNReal.mul_lt_mul_iff_left (pow_ne_zero (finrank Real E) (two_ne_zero' _)) (by finiteness)]; rw [mul_right_comm]; rw [ofReal_pow (by simp : 0 <= (2 : Real)⁻¹)]; rw [ofReal_inv

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, ENNReal.mul_lt_mul_iff_left, addHaar_smul_of_nonneg, exists_pair_mem_lattice_not_disjoint_vadd, finiteness, finrank, h_conv, h_conv.smul, h_vol, inv_mul_cancel, mul_lt_mul_iff_left, mul_pow, mul_right_comm, nullMeasurableSet, ofNat_ne_top, ofReal_inv_of_pos, ofReal_pow, pow_ne_zero, two_ne_zero
-/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommGroup E]
    [NormedSpace Real E] [BorelSpace E] [FiniteDimensional Real E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : forall x in s, -x in s) (h_conv : Convex Real s) (h : μ F * 2 ^ finrank Real E < μ s) :
    exists x != 0, ((x : L) : E) in s := by
  have h_vol : μ F < μ ((2⁻¹ : Real) • s) := by
    rw [addHaar_smul_of_nonneg μ (by simp : 0 <= (2 : Real)⁻¹) s]; rw [← ENNReal.mul_lt_mul_iff_left (pow_ne_zero (finrank Real E) (two_ne_zero' _)) (by finiteness)]; rw [mul_right_comm]; rw [ofReal_pow (by simp : 0 <= (2 : Real)⁻¹)]; rw [ofReal_inv_of_pos zero_lt_two]
    simpa [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  obtain ⟨x, y, hxy, h⟩ :=
    exists_pair_mem_lattice_not_disjoint_vadd fund ((h_conv.smul _).nullMeasurableSet _) h_vol
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := Set.not_disjoint_iff.mp h
  refine ⟨x - y, sub_ne_zero.2 hxy, ?_⟩
  rw [Set.mem_inv_smul_set_iff₀ (two_ne_zero' Real)] at hv hw
  simp_rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm _ w, ← sub_eq_sub_iff_add_eq_add, ←
    AddSubgroup.coe_sub] at hvw
  rw [← hvw]; rw [← inv_smul_smul₀ (two_ne_zero' Real) (_ - _)]; rw [smul_sub]; rw [sub_eq_add_neg]; rw [smul_add]
  refine h_conv hw (h_symm _ hv) ?_ ?_ ?_ <;> norm_num

/--
theorem `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` / 定理 `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`

English:
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
  statement: [NormedAddCommGroup E]
  proof: by
have h_mes : μ s != 0 := fun hμ => fund.measure_ne_zero (NeZero.ne μ) by simpa [hμ] using h
  have h_nemp : s.Nonempty := nonempty_of_measure_ne_zero h_mes
  let u : Nat -> Real>=0 := (exists_seq_strictAnti_tendsto 0).choose
  let K : ConvexBody E := ⟨s, h_conv, h_cpt, h_nemp⟩
  let S : Nat -> Co

中文:
定理 exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
  结论: [NormedAddCommGroup E]
  证明: by
have h_mes : μ s != 0 := fun hμ => fund.measure_ne_zero (NeZero.ne μ) by simpa [hμ] using h
  have h_nemp : s.Nonempty := nonempty_of_measure_ne_zero h_mes
  let u : Nat -> Real>=0 := (exists_seq_strictAnti_tendsto 0).choose
  let K : ConvexBody E := ⟨s, h_conv, h_cpt, h_nemp⟩
  let S : Nat -> Co

Depends on / 依赖: ConvexBody, NeZero, NeZero.ne, Nonempty, exists_seq_strictAnti_tendsto, fund.measure_ne_zero, h_conv, h_cpt, h_mes, h_nemp, measure_ne_zero, nonempty_of_measure_ne_zero, s.Nonempty
-/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure [NormedAddCommGroup E]
    [NormedSpace Real E] [BorelSpace E] [FiniteDimensional Real E] [Nontrivial E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] [DiscreteTopology L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : forall x in s, -x in s) (h_conv : Convex Real s) (h_cpt : IsCompact s)
    (h : μ F * 2 ^ finrank Real E <= μ s) :
    exists x != 0, ((x : L) : E) in s := by
have h_mes : μ s != 0 := fun hμ => fund.measure_ne_zero (NeZero.ne μ) by simpa [hμ] using h
  have h_nemp : s.Nonempty := nonempty_of_measure_ne_zero h_mes
  let u : Nat -> Real>=0 := (exists_seq_strictAnti_tendsto 0).choose
  let K : ConvexBody E := ⟨s, h_conv, h_cpt, h_nemp⟩
  let S : Nat -> ConvexBody E := fun n => (1 + u n) • K
  let Z : Nat -> Set E := fun n => (S n) inter (L \ {0})
  -- The convex bodies `S n` have volume strictly larger than `μ s` and thus we can apply
  -- `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` to them and obtain that
  -- `S n` contains a nonzero point of `L`. Since the intersection of the `S n` is equal to `s`,
  -- it follows that `s` contains a nonzero point of `L`.
  have h_zero : 0 in K := K.zero_mem_of_symmetric h_symm
  suffices Set.Nonempty (⋂ n, Z n) by
    simp_rw [Z, S, ConvexBody.coe_smul', NNReal.smul_def, ← Set.iInter_inter, NNReal.coe_add,
      NNReal.coe_one] at this
    rw [K.iInter_smul_eq_self h_zero] at this
    · obtain ⟨x, hx⟩ := this
      exact ⟨⟨x, by simp_all⟩, by aesop⟩
    · exact (exists_seq_strictAnti_tendsto (0 : Real>=0)).choose_spec.2.2
  have h_clos : IsClosed ((L : Set E) \ {0}) := by
    rsuffices ⟨U, hU⟩ : exists U : Set E, IsOpen U ∧ U inter L = {0}
    · rw [sdiff_eq_sdiff_iff_inf_eq_inf (z := U).mpr (by simp [Set.inter_comm .. ▸ hU.2, zero_mem])]
      exact AddSubgroup.isClosed_of_discrete.sdiff hU.1
    exact isOpen_inter_eq_singleton_of_mem_discrete ⟨inferInstance⟩ (zero_mem L)
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Z (fun n => ?_)
    (fun n => ?_) ((S 0).isCompact.inter_right h_clos) (fun n => (S n).isClosed.inter h_clos)
  · refine Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr ?_)
    refine ConvexBody.smul_le_of_le K h_zero ?_
    rw [add_le_add_iff_left]
exact le_of_lt (exists_seq_strictAnti_tendsto (0 : Real>=0)).choose_spec.1 (Nat.lt_add_one n)
  · suffices μ F * 2 ^ finrank Real E < μ (S n : Set E) by
      have h_symm' : forall x in S n, -x in S n := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨-y, h_symm _ hy, by simp⟩
      obtain ⟨x, hx_nz, hx_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        fund h_symm' (S n).convex this
      exact ⟨x, hx_mem, by simp_all⟩
    refine lt_of_le_of_lt h ?_
    rw [ConvexBody.coe_smul']; rw [NNReal.smul_def]; rw [addHaar_smul_of_nonneg _ (NNReal.coe_nonneg _)]
    rw [show μ s < _ ↔ 1 * μ s < _ by rw [one_mul]]
    dsimp [K]
    gcongr
    · exact h_cpt.measure_ne_top
    rw [ofReal_pow (by positivity)]
    refine one_lt_pow₀ ?_ (ne_of_gt finrank_pos)
    simp [u, (exists_seq_strictAnti_tendsto (0 : Real>=0)).choose_spec.2.1 n]

end MeasureTheory
