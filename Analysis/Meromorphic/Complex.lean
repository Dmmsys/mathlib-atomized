/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma function is meromorphic
-/

public section

open Set Complex

/--
lemma `MeromorphicNFOn.Gamma` / 引理 `MeromorphicNFOn.Gamma`

English:
lemma MeromorphicNFOn.Gamma
  statement: MeromorphicNFOn Gamma univ
  proof: meromorphicNFOn_inv.mp AnalyticOnNhd.meromorphicNFOn
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

中文:
引理 MeromorphicNFOn.Gamma
  结论: MeromorphicNFOn Gamma univ
  证明: meromorphicNFOn_inv.mp AnalyticOnNhd.meromorphicNFOn
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.meromorphicNFOn, analyticOnNhd_univ_iff_differentiable, analyticOnNhd_univ_iff_differentiable.mpr, differentiable_one_div_Gamma, meromorphicNFOn, meromorphicNFOn_inv, meromorphicNFOn_inv.mp
-/
lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
meromorphicNFOn_inv.mp AnalyticOnNhd.meromorphicNFOn
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

-- TODO: restate `MeromorphicNFOn.Gamma` when `MeromorphicNF` is defined

/--
lemma `Meromorphic.Gamma` / 引理 `Meromorphic.Gamma`

English:
lemma Meromorphic.Gamma
  statement: Meromorphic Gamma
  proof: meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

中文:
引理 Meromorphic.Gamma
  结论: Meromorphic Gamma
  证明: meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

Depends on / 依赖: MeromorphicNFOn, MeromorphicNFOn.Gamma.meromorphicOn, meromorphicOn, meromorphicOn_univ, meromorphicOn_univ.mp
-/
lemma Meromorphic.Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

/--
lemma `MeromorphicOn.Gamma` / 引理 `MeromorphicOn.Gamma`

English:
lemma MeromorphicOn.Gamma
  given: {s}
  statement: MeromorphicOn Gamma s
  proof: Meromorphic.Gamma.meromorphicOn

中文:
引理 MeromorphicOn.Gamma
  条件: {s}
  结论: MeromorphicOn Gamma s
  证明: Meromorphic.Gamma.meromorphicOn

Depends on / 依赖: Meromorphic, Meromorphic.Gamma.meromorphicOn, meromorphicOn
-/
lemma MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s :=
  Meromorphic.Gamma.meromorphicOn
