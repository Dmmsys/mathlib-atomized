/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Positivity.Finset

/-!
# Direct sum of metric spaces

This files endows the direct sum `ι →₀ X` of `ι`-many copies of a metric space `X` with the
L^p metric.

## TODO

Allow the L^∞ metric too. Currently, there is no easy way to perform the proofs:
`match` on `ℝ≥0∞` exposes the underlying `Option` and `induction p using ENNReal.recTopCoe` in the
`EMetricSpace` instance chokes on the `PseudoEMetricSpace` one.
-/

open scoped ENNReal NNReal

public section

namespace Finsupp
variable {ι X : Type*} [Zero X] {p : Real>=0} [Fact (1 <= p)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoEMetricSpace
  signature: X] : PseudoEMetricSpace (WithLp p <| ι ->₀ X) where
  body: ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real)
  edist_self f := by
    have : 0 < p := zero_lt_one.trans_le Fact.out
    simp [sum, *]
  edist_comm f g := by
    simp only [sum, zipWith_apply, edist_comm]
    congr 2
    ext i
    simp [edist_comm]
  edi

中文:
实例 [PseudoEMetricSpace
  签名: X] : PseudoEMetricSpace (WithLp p <| ι ->₀ X) where
  定义体: ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real)
  edist_self f := by
    have : 0 < p := zero_lt_one.trans_le Fact.out
    simp [sum, *]
  edist_comm f g := by
    simp only [sum, zipWith_apply, edist_comm]
    congr 2
    ext i
    simp [edist_comm]
  edi

Depends on / 依赖: Fact.out, classical, edist_comm, edist_self, edist_triangle, f.ofLp.support, f.ofLp.zipWith, g.ofLp, g.ofLp.support, h.ofLp.support, sum_of_support_subset, support, support_zipWith, trans_le, zero_lt_one, zero_lt_one.trans_le, zipWith, zipWith_apply
-/
noncomputable instance [PseudoEMetricSpace X] : PseudoEMetricSpace (WithLp p <| ι ->₀ X) where
  edist f g :=
  ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real)
  edist_self f := by
    have : 0 < p := zero_lt_one.trans_le Fact.out
    simp [sum, *]
  edist_comm f g := by
    simp only [sum, zipWith_apply, edist_comm]
    congr 2
    ext i
    simp [edist_comm]
  edist_triangle f g h := by
    classical
    have : 0 < p := zero_lt_one.trans_le Fact.out
    let s := f.ofLp.support union g.ofLp.support union h.ofLp.support
    rw [sum_of_support_subset (s := s) _ (by grind [support_zipWith]) _ (by simp [*]),
      sum_of_support_subset (s := s) _ (by grind [support_zipWith]) _ (by simp [*]),
      sum_of_support_subset (s := s) _ (by grind [support_zipWith]) _ (by simp [*])]
    simp only [zipWith_apply, ← one_div]
    grw [← ENNReal.Lp_add_le _ _ _ (mod_cast Fact.out)]
    gcongr
    exact edist_triangle ..

/--
lemma `edist_def` / 引理 `edist_def`

English:
lemma edist_def
  statement: [PseudoEMetricSpace X] {p : Real>=0} [Fact (1 <= p)]
  proof: rfl

中文:
引理 edist_def
  结论: [PseudoEMetricSpace X] {p : 实数>=0} [Fact (1 <= p)]
  证明: rfl
-/
lemma edist_def [PseudoEMetricSpace X] {p : Real>=0} [Fact (1 <= p)]
    (f g : WithLp p <| ι ->₀ X) :
    edist f g =
      ((f.ofLp.zipWith edist (edist_self _) g.ofLp).sum fun _i r => r ^ (p : Real)) ^ (p⁻¹ : Real) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EMetricSpace
  signature: X] : EMetricSpace (WithLp p <| ι ->₀ X) where
  body: by simp_all [edist_def, sum, WithLp.ext_iff, DFunLike.ext_iff]

中文:
实例 [EMetricSpace
  签名: X] : EMetricSpace (WithLp p <| ι ->₀ X) where
  定义体: by simp_all [edist_def, sum, WithLp.ext_iff, DFunLike.ext_iff]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, WithLp, WithLp.ext_iff, edist_def, ext_iff
-/
noncomputable instance [EMetricSpace X] : EMetricSpace (WithLp p <| ι ->₀ X) where
  eq_of_edist_eq_zero {f g} hfg := by simp_all [edist_def, sum, WithLp.ext_iff, DFunLike.ext_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoMetricSpace
  signature: X] : PseudoMetricSpace (WithLp p <| ι ->₀ X)
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real))
    (fun f g => by dsimp [sum]; positivity) fun f g => by
      simp only [edist_def, sum, zipWith_apply, ← coe_nnreal_ennreal_nndist, NNReal.zero_l

中文:
实例 [PseudoMetricSpace
  签名: X] : PseudoMetricSpace (WithLp p <| ι ->₀ X)
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real))
    (fun f g => by dsimp [sum]; positivity) fun f g => by
      simp only [edist_def, sum, zipWith_apply, ← coe_nnreal_ennreal_nndist, NNReal.zero_l

Depends on / 依赖: ENNReal, ENNReal.coe_inj, ENNReal.coe_rpow_of_nonneg, ENNReal.ofNNReal_finsetSum, ENNReal.ofReal_coe_nnreal, NNReal, NNReal.coe_rpow, NNReal.coe_sum, NNReal.zero_le_coe, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, coe_inj, coe_nndist, coe_nnreal_ennreal_nndist, coe_rpow, coe_rpow_of_nonneg, coe_sum, dist_self, edist_def, f.ofLp.zipWith
-/
noncomputable instance [PseudoMetricSpace X] : PseudoMetricSpace (WithLp p <| ι ->₀ X) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real))
    (fun f g => by dsimp [sum]; positivity) fun f g => by
      simp only [edist_def, sum, zipWith_apply, ← coe_nnreal_ennreal_nndist, NNReal.zero_le_coe,
        ← ENNReal.coe_rpow_of_nonneg, ← ENNReal.ofNNReal_finsetSum, inv_nonneg, ← coe_nndist,
        ← NNReal.coe_rpow, ← NNReal.coe_sum, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inj]
      congr! 2
      ext i
      simp [← coe_nndist, ← coe_nnreal_ennreal_nndist]

/--
lemma `dist_def` / 引理 `dist_def`

English:
lemma dist_def
  given: [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X)
  proof: rfl

中文:
引理 dist_def
  条件: [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X)
  证明: rfl
-/
lemma dist_def [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X) :
    dist f g =
      ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun _i r => r ^ (p : Real)) ^ (p⁻¹ : Real) := rfl

/--
lemma `nndist_def` / 引理 `nndist_def`

English:
lemma nndist_def
  given: [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X)
  proof: by
  ext
  simp only [coe_nndist, dist_def, sum, zipWith_apply, NNReal.coe_sum, NNReal.coe_rpow]
  congr 2
  ext i
  simp [← coe_nndist]

中文:
引理 nndist_def
  条件: [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X)
  证明: by
  ext
  simp only [coe_nndist, dist_def, sum, zipWith_apply, NNReal.coe_sum, NNReal.coe_rpow]
  congr 2
  ext i
  simp [← coe_nndist]

Depends on / 依赖: NNReal, NNReal.coe_rpow, NNReal.coe_sum, coe_nndist, coe_rpow, coe_sum, dist_def, zipWith_apply
-/
lemma nndist_def [PseudoMetricSpace X] (f g : WithLp p <| ι ->₀ X) :
    nndist f g =
      ((f.ofLp.zipWith nndist (nndist_self _) g.ofLp).sum fun _i r => r ^ (p : Real)) ^ (p⁻¹ : Real) := by
  ext
  simp only [coe_nndist, dist_def, sum, zipWith_apply, NNReal.coe_sum, NNReal.coe_rpow]
  congr 2
  ext i
  simp [← coe_nndist]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: X] : MetricSpace (WithLp p <| ι ->₀ X)
  body: EMetricSpace.toMetricSpaceOfDist
    (fun f g => ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real))
    (fun f g => by dsimp [sum]; positivity) fun f g => by rw [edist_dist, dist_def]

中文:
实例 [MetricSpace
  签名: X] : MetricSpace (WithLp p <| ι ->₀ X)
  定义体: EMetricSpace.toMetricSpaceOfDist
    (fun f g => ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real))
    (fun f g => by dsimp [sum]; positivity) fun f g => by rw [edist_dist, dist_def]

Depends on / 依赖: EMetricSpace, EMetricSpace.toMetricSpaceOfDist, dist_def, dist_self, edist_dist, f.ofLp.zipWith, g.ofLp, toMetricSpaceOfDist, zipWith
-/
noncomputable instance [MetricSpace X] : MetricSpace (WithLp p <| ι ->₀ X) :=
  EMetricSpace.toMetricSpaceOfDist
    (fun f g => ((f.ofLp.zipWith dist (dist_self _) g.ofLp).sum fun i r => r ^ (p : Real)) ^ (p⁻¹ : Real))
    (fun f g => by dsimp [sum]; positivity) fun f g => by rw [edist_dist, dist_def]

end Finsupp
