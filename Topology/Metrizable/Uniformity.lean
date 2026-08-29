/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Metrizable.Basic

/-!
# Metrizable uniform spaces

In this file we prove that a uniform space with countably generated uniformity filter is
pseudometrizable: there exists a `PseudoMetricSpace` structure that generates the same uniformity.
The proof follows [Sergey Melikhov, Metrizable uniform spaces][melikhov2011].

## Main definitions

* `PseudoMetricSpace.ofPreNNDist`: given a function `d : X → X → ℝ≥0` such that `d x x = 0` and
  `d x y = d y x` for all `x y : X`, constructs the maximal pseudometric space structure such that
  `NNDist x y ≤ d x y` for all `x y : X`.

* `UniformSpace.pseudoMetricSpace`: given a uniform space `X` with countably generated `𝓤 X`,
  constructs a `PseudoMetricSpace X` instance that is compatible with the uniform space structure.

* `UniformSpace.metricSpace`: given a T₀ uniform space `X` with countably generated `𝓤 X`,
  constructs a `MetricSpace X` instance that is compatible with the uniform space structure.

## Main statements

* `UniformSpace.metrizable_uniformity`: if `X` is a uniform space with countably generated `𝓤 X`,
  then there exists a `PseudoMetricSpace` structure that is compatible with this `UniformSpace`
  structure. Use `UniformSpace.pseudoMetricSpace` or `UniformSpace.metricSpace` instead.

* `UniformSpace.pseudoMetrizableSpace`: a uniform space with countably generated `𝓤 X` is
  pseudometrizable.

* `UniformSpace.metrizableSpace`: a T₀ uniform space with countably generated `𝓤 X` is
  metrizable. This is not an instance to avoid loops.

## Tags

metrizable space, uniform space
-/

@[expose] public section


open Set Function Metric List Filter
open scoped NNReal SetRel Uniformity

variable {X : Type*}

namespace PseudoMetricSpace

/-- The maximal pseudometric space structure on `X` such that `dist x y ≤ d x y` for all `x y`,
where `d : X → X → ℝ≥0` is a function such that `d x x = 0` and `d x y = d y x` for all `x`, `y`. -/
@[instance_reducible]
/--
Definition of `ofPreNNDist` / `ofPreNNDist` 的定义

English:
definition ofPreNNDist
  signature: (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
  body: ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : Real>=0)
dist_self x := NNReal.coe_eq_zero.2
nonpos_iff_eq_zero.1 (ciInf_le (OrderBot.bddBelow _) []).trans_eq by simp [dist_self]
  dist_comm x y :=
NNReal.coe_inj.2 by
      refine reverse_surjective.iInf_congr _ fun l => ?_
      rw [← sum_rever

中文:
定义 ofPreNNDist
  签名: (d : X -> X -> 实数>=0) (dist_self : 对任意 x, d x x = 0)
  定义体: ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : Real>=0)
dist_self x := NNReal.coe_eq_zero.2
nonpos_iff_eq_zero.1 (ciInf_le (OrderBot.bddBelow _) []).trans_eq by simp [dist_self]
  dist_comm x y :=
NNReal.coe_inj.2 by
      refine reverse_surjective.iInf_congr _ fun l => ?_
      rw [← sum_rever

Depends on / 依赖: zipWith
-/
noncomputable def ofPreNNDist (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
    (dist_comm : forall x y, d x y = d y x) : PseudoMetricSpace X where
  dist x y := ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : Real>=0)
dist_self x := NNReal.coe_eq_zero.2
nonpos_iff_eq_zero.1 (ciInf_le (OrderBot.bddBelow _) []).trans_eq by simp [dist_self]
  dist_comm x y :=
NNReal.coe_inj.2 by
      refine reverse_surjective.iInf_congr _ fun l => ?_
      rw [← sum_reverse]; rw [reverse_zipWith]; rw [reverse_append]; rw [reverse_reverse]; rw [reverse_singleton]; rw [singleton_append]; rw [reverse_cons]; rw [reverse_reverse]; rw [zipWith_comm_of_comm dist_comm]
      simp only [length, length_append]
  dist_triangle x y z := by
    rw [← NNReal.coe_add]; rw [NNReal.coe_le_coe]
    refine NNReal.le_iInf_add_iInf fun lxy lyz => ?_
    calc
      ⨅ l, (zipWith d (x::l) (l ++ [z])).sum <=
          (zipWith d (x::lxy ++ y::lyz) ((lxy ++ y::lyz) ++ [z])).sum :=
        ciInf_le (OrderBot.bddBelow _) (lxy ++ y::lyz)
      _ = (zipWith d (x::lxy) (lxy ++ [y])).sum + (zipWith d (y::lyz) (lyz ++ [z])).sum := by
        rw [← sum_append]; rw [← zipWith_append]; rw [cons_append]; rw [← @singleton_append _ y]; rw [append_assoc]; rw [append_assoc]; rw [append_assoc]
        rw [length_cons]; rw [length_append]; rw [length_singleton]

/--
theorem `dist_ofPreNNDist` / 定理 `dist_ofPreNNDist`

English:
theorem dist_ofPreNNDist
  statement: (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
  proof: rfl

中文:
定理 dist_ofPreNNDist
  结论: (d : X -> X -> 实数>=0) (dist_self : 对任意 x, d x x = 0)
  证明: rfl
-/
theorem dist_ofPreNNDist (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
    (dist_comm : forall x y, d x y = d y x) (x y : X) :
    @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x
        y =
      ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : Real>=0) :=
  rfl

/--
theorem `dist_ofPreNNDist_le` / 定理 `dist_ofPreNNDist_le`

English:
theorem dist_ofPreNNDist_le
  statement: (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
  proof: NNReal.coe_le_coe.2 (ciInf_le (OrderBot.bddBelow _) []).trans_eq by simp

中文:
定理 dist_ofPreNNDist_le
  结论: (d : X -> X -> 实数>=0) (dist_self : 对任意 x, d x x = 0)
  证明: NNReal.coe_le_coe.2 (ciInf_le (OrderBot.bddBelow _) []).trans_eq by simp

Depends on / 依赖: NNReal, NNReal.coe_le_coe, OrderBot, OrderBot.bddBelow, bddBelow, ciInf_le, coe_le_coe, trans_eq
-/
theorem dist_ofPreNNDist_le (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
    (dist_comm : forall x y, d x y = d y x) (x y : X) :
    @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x
        y <=
      d x y :=
NNReal.coe_le_coe.2 (ciInf_le (OrderBot.bddBelow _) []).trans_eq by simp

/--
theorem `le_two_mul_dist_ofPreNNDist` / 定理 `le_two_mul_dist_ofPreNNDist`

English:
theorem le_two_mul_dist_ofPreNNDist
  statement: (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
  proof: by
  /- We need to show that `d x y` is at most twice the sum `L` of `d xᵢ xᵢ₊₁` over a path
    `x₀=x, ..., xₙ=y`. We prove it by induction on the length `n` of the sequence. Find an edge that
    splits the path into two parts of almost equal length: both `d x₀ x₁ + ... + d xₖ₋₁ xₖ` and
    `d xₖ₊

中文:
定理 le_two_mul_dist_ofPreNNDist
  结论: (d : X -> X -> 实数>=0) (dist_self : 对任意 x, d x x = 0)
  证明: by
  /- We need to show that `d x y` is at most twice the sum `L` of `d xᵢ xᵢ₊₁` over a path
    `x₀=x, ..., xₙ=y`. We prove it by induction on the length `n` of the sequence. Find an edge that
    splits the path into two parts of almost equal length: both `d x₀ x₁ + ... + d xₖ₋₁ xₖ` and
    `d xₖ₊
-/
theorem le_two_mul_dist_ofPreNNDist (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
    (dist_comm : forall x y, d x y = d y x)
    (hd : forall x₁ x₂ x₃ x₄, d x₁ x₄ <= 2 * max (d x₁ x₂) (max (d x₂ x₃) (d x₃ x₄))) (x y : X) :
    ↑(d x y) <= 2 * @dist X
      (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x y := by
  /- We need to show that `d x y` is at most twice the sum `L` of `d xᵢ xᵢ₊₁` over a path
    `x₀=x, ..., xₙ=y`. We prove it by induction on the length `n` of the sequence. Find an edge that
    splits the path into two parts of almost equal length: both `d x₀ x₁ + ... + d xₖ₋₁ xₖ` and
    `d xₖ₊₁ xₖ₊₂ + ... + d xₙ₋₁ xₙ` are less than or equal to `L / 2`.
    Then `d x₀ xₖ ≤ L`, `d xₖ xₖ₊₁ ≤ L`, and `d xₖ₊₁ xₙ ≤ L`, thus `d x₀ xₙ ≤ 2 * L`. -/
  rw [dist_ofPreNNDist]; rw [← NNReal.coe_two]; rw [← NNReal.coe_mul]; rw [NNReal.mul_iInf]; rw [NNReal.coe_le_coe]
  refine le_ciInf fun l => ?_
  have : IsTrans X fun x y => d x y = 0 := by
    refine ⟨fun a b c hab hbc => ?_⟩
    rw [← nonpos_iff_eq_zero]
    simpa only [nonpos_iff_eq_zero, hab, hbc, dist_self c, max_self, mul_zero] using hd a b c c
  suffices forall n, length l = n -> d x y <= 2 * (zipWith d (x :: l) (l ++ [y])).sum by exact this _ rfl
  intro n hn
  induction n using Nat.strong_induction_on generalizing x y l with | h n ihn =>
  subst n
  set L := zipWith d (x::l) (l ++ [y])
  have hL_len : length L = length l + 1 := by simp [L]
  rcases eq_or_ne (d x y) 0 with hd₀ | hd₀
  · simp only [hd₀, zero_le]
  rsuffices ⟨z, z', hxz, hzz', hz'y⟩ : exists z z' : X, d x z <= L.sum ∧ d z z' <= L.sum ∧ d z' y <= L.sum
  · grw [hd x z z' y, max_le hxz (max_le hzz' hz'y)]
  set s : Set Nat := { m : Nat | 2 * (take m L).sum <= L.sum }
  have hs₀ : 0 in s := by simp [s]
  have hsne : s.Nonempty := ⟨0, hs₀⟩
  obtain ⟨M, hMl, hMs⟩ : exists M <= length l, IsGreatest s M := by
    have hs_ub : length l in upperBounds s := by
      intro m hm
      rw [← not_lt]; rw [Nat.lt_iff_add_one_le]; rw [← hL_len]
      intro hLm
      rw [mem_ofPred_eq]; rw [take_of_length_le hLm]; rw [two_mul]; rw [add_le_iff_nonpos_left]; rw [nonpos_iff_eq_zero]; rw [sum_eq_zero_iff]; rw [← forall_iff_forall_mem]; rw [forall_zipWith]; rw [← isChain_cons_append_singleton_iff_forall₂]
          at hm <;>
        [skip; simp]
      exact hd₀ (hm.rel_cons (mem_append.2 <| Or.inr <| mem_singleton_self _))
    have hs_bdd : BddAbove s := ⟨length l, hs_ub⟩
    exact ⟨sSup s, csSup_le hsne hs_ub, ⟨Nat.sSup_mem hsne hs_bdd, fun k => le_csSup hs_bdd⟩⟩
  have hM_lt : M < length L := by rwa [hL_len, Nat.lt_succ_iff]
  have hM_ltx : M < length (x::l) := lt_length_left_of_zipWith hM_lt
  have hM_lty : M < length (l ++ [y]) := lt_length_right_of_zipWith hM_lt
  refine ⟨(x::l)[M], (l ++ [y])[M], ?_, ?_, ?_⟩
  · cases M with
    | zero =>
      simp [dist_self]
    | succ M =>
      rw [Nat.succ_le_iff] at hMl
      have hMl' : length (take M l) = M := length_take.trans (min_eq_left hMl.le)
      refine (ihn _ hMl _ _ _ hMl').trans ?_
      convert! hMs.1.out
      rw [take_zipWith]; rw [take]; rw [take_add_one]; rw [getElem?_append_left hMl]; rw [getElem?_eq_getElem hMl]; rw [← Option.coe_def]; rw [Option.toList_some]; rw [take_append_of_le_length hMl.le]; rw [getElem_cons_succ]
  · exact single_le_sum (fun x _ => zero_le) _ (mem_iff_get.2 ⟨⟨M, hM_lt⟩, getElem_zipWith⟩)
  · rcases hMl.eq_or_lt with (rfl | hMl)
    · simp only [getElem_append_right le_rfl, getElem_singleton, dist_self, zero_le]
    rw [getElem_append_left hMl]
    have hlen : length (drop (M + 1) l) = length l - (M + 1) := length_drop
    have hlen_lt : length l - (M + 1) < length l := Nat.sub_lt_of_pos_le M.succ_pos hMl
    refine (ihn _ hlen_lt _ y _ hlen).trans ?_
    rw [cons_getElem_drop_succ]
    have hMs' : L.sum <= 2 * (L.take (M + 1)).sum :=
      not_lt.1 fun h => (hMs.2 h.le).not_gt M.lt_succ_self
    rw [← sum_take_add_sum_drop L (M + 1)]; rw [two_mul]; rw [add_le_add_iff_left]; rw [← add_le_add_iff_right]; rw [sum_take_add_sum_drop]; rw [← two_mul] at hMs'
    convert! hMs'
    rwa [drop_zipWith, drop, drop_append_of_le_length]

end PseudoMetricSpace

/--
theorem `UniformSpace.metrizable_uniformity` / 定理 `UniformSpace.metrizable_uniformity`

English:
theorem UniformSpace.metrizable_uniformity
  statement: (X : Type*) [UniformSpace X]
  proof: by
  classical
  /- Choose a fast decreasing antitone basis `U : ℕ → SetRel X X` of the uniformity filter `𝓤 X`.
    Define `d x y : ℝ≥0` to be `(1 / 2) ^ n`, where `n` is the minimal index of `U n` that
    separates `x` and `y`: `(x, y) ∉ U n`, or `0` if `x` is not separated from `y`. This functio

中文:
定理 UniformSpace.metrizable_uniformity
  结论: (X : 类型) [UniformSpace X]
  证明: by
  classical
  /- Choose a fast decreasing antitone basis `U : ℕ → SetRel X X` of the uniformity filter `𝓤 X`.
    Define `d x y : ℝ≥0` to be `(1 / 2) ^ n`, where `n` is the minimal index of `U n` that
    separates `x` and `y`: `(x, y) ∉ U n`, or `0` if `x` is not separated from `y`. This functio
-/
protected theorem UniformSpace.metrizable_uniformity (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] : exists I : PseudoMetricSpace X, I.toUniformSpace = ‹_› := by
  classical
  /- Choose a fast decreasing antitone basis `U : ℕ → SetRel X X` of the uniformity filter `𝓤 X`.
    Define `d x y : ℝ≥0` to be `(1 / 2) ^ n`, where `n` is the minimal index of `U n` that
    separates `x` and `y`: `(x, y) ∉ U n`, or `0` if `x` is not separated from `y`. This function
    satisfies the assumptions of `PseudoMetricSpace.ofPreNNDist` and
    `PseudoMetricSpace.le_two_mul_dist_ofPreNNDist`, hence the distance given by the former
    pseudometric space structure is Lipschitz equivalent to the `d`. Thus the uniformities generated
    by `d` and `dist` are equal. Since the former uniformity is equal to `𝓤 X`, the latter is equal
    to `𝓤 X` as well. -/
  obtain ⟨U, hU_symm, hU_comp, hB⟩ :
    exists U : Nat -> SetRel X X,
      (forall n, (U n).IsSymm) ∧
        (forall ⦃m n⦄, m < n -> U n ○ (U n ○ U n) subseteq U m) ∧ (𝓤 X).HasAntitoneBasis U := by
    rcases UniformSpace.has_seq_basis X with ⟨V, hB, hV_symm⟩
    rcases hB.subbasis_with_rel fun m =>
        hB.tendsto_smallSets.eventually
          (eventually_uniformity_iterate_comp_subset (hB.mem m) 2) with
      ⟨φ, -, hφ_comp, hφB⟩
    exact ⟨V ∘ φ, fun n => hV_symm _, hφ_comp, hφB⟩
  set d : X -> X -> Real>=0 := fun x y => if h : exists n, (x, y) ∉ U n then (1 / 2) ^ Nat.find h else 0
  have hd₀ : forall {x y}, d x y = 0 ↔ Inseparable x y := by
    intro x y
    refine Iff.trans ?_ hB.inseparable_iff_uniformity.symm
    simp only [d, true_imp_iff]
    split_ifs with h
    · simp [h, pow_eq_zero_iff']
    · simpa only [not_exists, Classical.not_not, eq_self_iff_true, true_iff] using h
  have hd_symm x y : d x y = d y x := by simp only [d, (U _).comm]
  have hr : (1 / 2 : Real>=0) in Ioo (0 : Real>=0) 1 := ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  let I := PseudoMetricSpace.ofPreNNDist d (fun x => hd₀.2 rfl) hd_symm
  have hdist_le : forall x y, dist x y <= d x y := PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hle_d : forall {x y : X} {n : Nat}, (1 / 2) ^ n <= d x y ↔ (x, y) ∉ U n := by
    intro x y n
    dsimp only [d]
    split_ifs with h
    · rw [(pow_right_strictAnti₀ hr.1 hr.2).le_iff_ge, Nat.find_le_iff]
      exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hB.antitone hmn hn), fun h => ⟨n, le_rfl, h⟩⟩
    · push Not at h
      simp only [h, not_true, (pow_pos hr.1 _).not_ge]
  have hd_le : forall x y, ↑(d x y) <= 2 * dist x y := by
    refine PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _ fun x₁ x₂ x₃ x₄ => ?_
    by_cases H : exists n, (x₁, x₄) ∉ U n
    · refine (dif_pos H).trans_le ?_
      rw [← div_le_iff₀' zero_lt_two]; rw [← mul_one_div (_ ^ _)]; rw [← pow_succ]
      simp only [le_max_iff, hle_d, ← not_and_or]
      rintro ⟨h₁₂, h₂₃, h₃₄⟩
      refine Nat.find_spec H (hU_comp (lt_add_one <| Nat.find H) ?_)
      exact ⟨x₂, h₁₂, x₃, h₂₃, h₃₄⟩
    · exact (dif_neg H).trans_le zero_le
  -- Porting note: without the next line, `uniformity_basis_dist_pow` ends up introducing some
  -- `Subtype.val` applications instead of `NNReal.toReal`.
  rw [mem_Ioo]; rw [← NNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hr
refine ⟨I, UniformSpace.ext (uniformity_basis_dist_pow hr.1 hr.2).ext hB.toHasBasis ?_ ?_⟩
  · refine fun n hn => ⟨n, hn, fun x hx => (hdist_le _ _).trans_lt ?_⟩
    rwa [← NNReal.coe_pow, NNReal.coe_lt_coe, ← not_le, hle_d, Classical.not_not]
  · refine fun n _ => ⟨n + 1, trivial, fun x hx => ?_⟩
    rw [mem_ofPred_eq] at hx
    contrapose! hx
    refine le_trans ?_ ((div_le_iff₀' zero_lt_two).2 (hd_le x.1 x.2))
    rwa [← NNReal.coe_two, ← NNReal.coe_div, ← NNReal.coe_pow, NNReal.coe_le_coe, pow_succ,
      mul_one_div, div_le_iff₀ zero_lt_two, div_mul_cancel₀ _ two_ne_zero, hle_d]

-- see note [reducible non-instances]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev UniformSpace.pseudoMetricSpace (X : Type*) [UniformSpace X]
  body: (UniformSpace.metrizable_uniformity X).choose.replaceUniformity
    congr_arg _ (UniformSpace.metrizable_uniformity X).choose_spec.symm

中文:
缩写 noncomputable
  签名: abbrev UniformSpace.pseudoMetricSpace (X : 类型) [UniformSpace X]
  定义体: (UniformSpace.metrizable_uniformity X).choose.replaceUniformity
    congr_arg _ (UniformSpace.metrizable_uniformity X).choose_spec.symm
-/
protected noncomputable abbrev UniformSpace.pseudoMetricSpace (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] : PseudoMetricSpace X :=
(UniformSpace.metrizable_uniformity X).choose.replaceUniformity
    congr_arg _ (UniformSpace.metrizable_uniformity X).choose_spec.symm

-- see note [reducible non-instances]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev UniformSpace.metricSpace (X : Type*) [UniformSpace X]
  body: @MetricSpace.ofT0PseudoMetricSpace X (UniformSpace.pseudoMetricSpace X) _

中文:
缩写 noncomputable
  签名: abbrev UniformSpace.metricSpace (X : 类型) [UniformSpace X]
  定义体: @MetricSpace.ofT0PseudoMetricSpace X (UniformSpace.pseudoMetricSpace X) _
-/
protected noncomputable abbrev UniformSpace.metricSpace (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] [T0Space X] : MetricSpace X :=
  @MetricSpace.ofT0PseudoMetricSpace X (UniformSpace.pseudoMetricSpace X) _

/--
theorem `UniformSpace.metrizableSpace` / 定理 `UniformSpace.metrizableSpace`

English:
theorem UniformSpace.metrizableSpace
  given: [UniformSpace X] [IsCountablyGenerated (𝓤 X)] [T0Space X]
  proof: inferInstance

中文:
定理 UniformSpace.metrizableSpace
  条件: [UniformSpace X] [IsCountablyGenerated (𝓤 X)] [T0Space X]
  证明: inferInstance
-/
theorem UniformSpace.metrizableSpace [UniformSpace X] [IsCountablyGenerated (𝓤 X)] [T0Space X] :
    TopologicalSpace.MetrizableSpace X := inferInstance

-- see note [reducible non-instances]
/--
Definition of `TopologicalSpace.pseudoMetrizableSpacePseudoMetric` / `TopologicalSpace.pseudoMetrizableSpacePseudoMetric` 的定义

English:
abbreviation TopologicalSpace.pseudoMetrizableSpacePseudoMetric
  signature: (X : Type*)
  body: letI := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  haveI := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  UniformSpace.pseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.PseudoMetrizableSpace] :
    t.pseudoMetrizableSpacePseudoMetric.toUniformS

中文:
缩写 TopologicalSpace.pseudoMetrizableSpacePseudoMetric
  签名: (X : 类型)
  定义体: letI := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  haveI := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  UniformSpace.pseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.PseudoMetrizableSpace] :
    t.pseudoMetrizableSpacePseudoMetric.toUniformS

Depends on / 依赖: TopologicalSpace, TopologicalSpace.pseudoMetrizableSpaceUniformity, TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated, UniformSpace, UniformSpace.pseudoMetricSpace, pseudoMetricSpace, pseudoMetrizableSpaceUniformity, pseudoMetrizableSpaceUniformity_countably_generated
-/
noncomputable abbrev TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X : Type*)
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  letI := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  haveI := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  UniformSpace.pseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.PseudoMetrizableSpace] :
    t.pseudoMetrizableSpacePseudoMetric.toUniformSpace = t.pseudoMetrizableSpaceUniformity := by
  with_reducible_and_instances rfl

/--
Definition of `TopologicalSpace.metrizableSpaceMetric` / `TopologicalSpace.metrizableSpaceMetric` 的定义

English:
abbreviation TopologicalSpace.metrizableSpaceMetric
  signature: (X : Type*) [TopologicalSpace X]
  body: letI := pseudoMetrizableSpacePseudoMetric X
  .ofT0PseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.MetrizableSpace] :
    t.metrizableSpaceMetric.toPseudoMetricSpace = t.pseudoMetrizableSpacePseudoMetric := by
  with_reducible_and_instances rfl

中文:
缩写 TopologicalSpace.metrizableSpaceMetric
  签名: (X : 类型) [TopologicalSpace X]
  定义体: letI := pseudoMetrizableSpacePseudoMetric X
  .ofT0PseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.MetrizableSpace] :
    t.metrizableSpaceMetric.toPseudoMetricSpace = t.pseudoMetrizableSpacePseudoMetric := by
  with_reducible_and_instances rfl

Depends on / 依赖: ofT0PseudoMetricSpace, pseudoMetrizableSpacePseudoMetric
-/
noncomputable abbrev TopologicalSpace.metrizableSpaceMetric (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] : MetricSpace X :=
  letI := pseudoMetrizableSpacePseudoMetric X
  .ofT0PseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.MetrizableSpace] :
    t.metrizableSpaceMetric.toPseudoMetricSpace = t.pseudoMetrizableSpacePseudoMetric := by
  with_reducible_and_instances rfl

variable {α : Type*}
open TopologicalSpace

instance (priority := 100) PseudoEMetricSpace.pseudoMetrizableSpace
    [PseudoEMetricSpace α] : PseudoMetrizableSpace α :=
  inferInstance

instance (priority := 100) EMetricSpace.metrizableSpace
    [EMetricSpace α] : MetrizableSpace α :=
  inferInstance
