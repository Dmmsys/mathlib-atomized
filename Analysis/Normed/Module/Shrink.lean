/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Transfer normed algebraic structures from `α` to `Shrink α`
-/

public section

noncomputable section

namespace Shrink

universe v
variable {R 𝕜 α : Type*} [Small.{v} α] [Semiring R] [NormedField 𝕜]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedAddCommGroup
  signature: α] : SeminormedAddCommGroup (Shrink.{v} α)
  body: (equivShrink α).symm.seminormedAddCommGroup

中文:
实例 [SeminormedAddCommGroup
  签名: α] : SeminormedAddCommGroup (Shrink.{v} α)
  定义体: (equivShrink α).symm.seminormedAddCommGroup

Depends on / 依赖: equivShrink, seminormedAddCommGroup, symm.seminormedAddCommGroup
-/
instance [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.seminormedAddCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedAddCommGroup
  signature: α] : NormedAddCommGroup (Shrink.{v} α)
  body: (equivShrink α).symm.normedAddCommGroup

中文:
实例 [NormedAddCommGroup
  签名: α] : NormedAddCommGroup (Shrink.{v} α)
  定义体: (equivShrink α).symm.normedAddCommGroup
-/
instance [NormedAddCommGroup α] : NormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.normedAddCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedAddCommGroup
  signature: α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α)
  body: (equivShrink α).symm.normedSpace 𝕜

中文:
实例 [SeminormedAddCommGroup
  签名: α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α)
  定义体: (equivShrink α).symm.normedSpace 𝕜

Depends on / 依赖: equivShrink, normedSpace, symm.normedSpace
-/
instance [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α) :=
  (equivShrink α).symm.normedSpace 𝕜

end Shrink
