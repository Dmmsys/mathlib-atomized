/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Topology lemma for `ENat.toENNReal`

This file shows `ENat.toENNReal` is a closed embedding.
-/

public section

namespace ENat

@[continuity]
/--
theorem `continuous_toENNReal` / 定理 `continuous_toENNReal`

English:
theorem continuous_toENNReal
  statement: Continuous toENNReal
  proof: by
  refine OrderTopology.continuous_iff.mpr fun a => ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio

中文:
定理 continuous_toENNReal
  结论: Continuous toENN实数
  证明: by
  refine OrderTopology.continuous_iff.mpr fun a => ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio

Depends on / 依赖: OrderTopology, OrderTopology.continuous_iff.mpr, continuous_iff, isOpen_Iio, isOpen_Ioi
-/
theorem continuous_toENNReal : Continuous toENNReal := by
  refine OrderTopology.continuous_iff.mpr fun a => ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio

/--
theorem `isClosedEmbedding_toENNReal` / 定理 `isClosedEmbedding_toENNReal`

English:
theorem isClosedEmbedding_toENNReal
  statement: Topology.IsClosedEmbedding toENNReal
  proof: continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

中文:
定理 isClosedEmbedding_toENNReal
  结论: Topology.IsClosedEmbedding toENN实数
  证明: continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

Depends on / 依赖: continuous_toENNReal, continuous_toENNReal.isClosedEmbedding, injective, isClosedEmbedding, toENNReal_strictMono, toENNReal_strictMono.injective
-/
theorem isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal :=
  continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

end ENat
