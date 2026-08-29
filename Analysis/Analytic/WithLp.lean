/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Analyticity on `WithLp`
-/

public section

open WithLp

open scoped ENNReal

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (p : Real>=0∞) [Fact (1 <= p)]

/--
lemma `analyticOn_ofLp` / 引理 `analyticOn_ofLp`

English:
lemma analyticOn_ofLp
  given: (s : Set (WithLp p (E × F)))
  statement: AnalyticOn 𝕜 ofLp s
  proof: (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s

中文:
引理 analyticOn_ofLp
  条件: (s : 集合 (WithLp p (E × F)))
  结论: AnalyticOn 𝕜 ofLp s
  证明: (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s

Depends on / 依赖: analyticOn, prodContinuousLinearEquiv
-/
lemma analyticOn_ofLp (s : Set (WithLp p (E × F))) : AnalyticOn 𝕜 ofLp s :=
  (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s

/--
lemma `analyticOn_toLp` / 引理 `analyticOn_toLp`

English:
lemma analyticOn_toLp
  given: (s : Set (E × F))
  statement: AnalyticOn 𝕜 (toLp p) s
  proof: (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

中文:
引理 analyticOn_toLp
  条件: (s : 集合 (E × F))
  结论: AnalyticOn 𝕜 (toLp p) s
  证明: (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

Depends on / 依赖: analyticOn, prodContinuousLinearEquiv, symm.analyticOn
-/
lemma analyticOn_toLp (s : Set (E × F)) : AnalyticOn 𝕜 (toLp p) s :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

end WithLp

namespace PiLp

variable {𝕜 ι : Type*} [Fintype ι] {E : ι -> Type*} [NontriviallyNormedField 𝕜]
  [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)] (p : Real>=0∞) [Fact (1 <= p)]

/--
lemma `analyticOn_ofLp` / 引理 `analyticOn_ofLp`

English:
lemma analyticOn_ofLp
  given: (s : Set (PiLp p E))
  statement: AnalyticOn 𝕜 ofLp s
  proof: (continuousLinearEquiv p 𝕜 E).analyticOn s

中文:
引理 analyticOn_ofLp
  条件: (s : 集合 (PiLp p E))
  结论: AnalyticOn 𝕜 ofLp s
  证明: (continuousLinearEquiv p 𝕜 E).analyticOn s

Depends on / 依赖: analyticOn, continuousLinearEquiv
-/
lemma analyticOn_ofLp (s : Set (PiLp p E)) : AnalyticOn 𝕜 ofLp s :=
  (continuousLinearEquiv p 𝕜 E).analyticOn s

/--
lemma `analyticOn_toLp` / 引理 `analyticOn_toLp`

English:
lemma analyticOn_toLp
  given: (s : Set (Π i, E i))
  statement: AnalyticOn 𝕜 (toLp p) s
  proof: (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

中文:
引理 analyticOn_toLp
  条件: (s : 集合 (Π i, E i))
  结论: AnalyticOn 𝕜 (toLp p) s
  证明: (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

Depends on / 依赖: analyticOn, continuousLinearEquiv, symm.analyticOn
-/
lemma analyticOn_toLp (s : Set (Π i, E i)) : AnalyticOn 𝕜 (toLp p) s :=
  (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

end PiLp
