/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Equip `ℂ` with the Borel sigma-algebra -/

public section


noncomputable section

instance (priority := 900) RCLike.measurableSpace {𝕜 : Type*} [RCLike 𝕜] : MeasurableSpace 𝕜 :=
  borel 𝕜

instance (priority := 900) RCLike.borelSpace {𝕜 : Type*} [RCLike 𝕜] : BorelSpace 𝕜 :=
  ⟨rfl⟩

/--
Instance `Complex.measurableSpace` / 实例 `Complex.measurableSpace`

English:
instance Complex.measurableSpace
  signature: : MeasurableSpace Complex
  body: borel Complex

中文:
实例 复形.measurableSpace
  签名: : 可测空间 复形
  定义体: borel Complex
-/
instance Complex.measurableSpace : MeasurableSpace Complex :=
  borel Complex

/--
Instance `Complex.borelSpace` / 实例 `Complex.borelSpace`

English:
instance Complex.borelSpace
  signature: : BorelSpace Complex
  body: ⟨rfl⟩

中文:
实例 复形.borelSpace
  签名: : Borel空间 复形
  定义体: ⟨rfl⟩
-/
instance Complex.borelSpace : BorelSpace Complex :=
  ⟨rfl⟩
