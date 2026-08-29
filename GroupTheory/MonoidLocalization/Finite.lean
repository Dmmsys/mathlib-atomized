/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Localization of a finitely generated submonoid

## TODO

If `Mathlib/GroupTheory/Finiteness.lean` wasn't so heavy, this could move earlier.
-/

public section

open Localization

variable {M : Type*} [CommMonoid M] {S : Submonoid M}

namespace Localization

/-- The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated. -/
@[to_additive /-- The localization of a finitely generated monoid at a finitely generated submonoid
is finitely generated. -/]
/--
lemma `fg` / 引理 `fg`

English:
lemma fg
  given: [Monoid.FG M] (hS : S.FG)
  statement: Monoid.FG Localization S
  proof: by
  rw [← Monoid.fg_iff_submonoid_fg] at hS; exact Monoid.fg_of_surjective mkHom mkHom_surjective

中文:
引理 fg
  条件: [幺半群.FG M] (hS : S.FG)
  结论: 幺半群.FG Localization S
  证明: by
  rw [← Monoid.fg_iff_submonoid_fg] at hS; exact Monoid.fg_of_surjective mkHom mkHom_surjective

Depends on / 依赖: Monoid, Monoid.fg_iff_submonoid_fg, Monoid.fg_of_surjective, fg_iff_submonoid_fg, fg_of_surjective, mkHom_surjective
-/
lemma fg [Monoid.FG M] (hS : S.FG) : Monoid.FG Localization S := by
  rw [← Monoid.fg_iff_submonoid_fg] at hS; exact Monoid.fg_of_surjective mkHom mkHom_surjective

end Localization

namespace Algebra.GrothendieckGroup

/-- The Grothendieck group of a finitely generated monoid is finitely generated. -/
@[to_additive /-- The Grothendieck group of a finitely generated monoid is finitely generated. -/]
/--
Instance `instFG` / 实例 `instFG`

English:
instance instFG
  signature: [Monoid.FG M]
  body: fg Monoid.FG.fg_top

中文:
实例 instFG
  签名: [幺半群.FG M]
  定义体: fg Monoid.FG.fg_top

Depends on / 依赖: Monoid, Monoid.FG.fg_top, fg_top
-/
instance instFG [Monoid.FG M] : Monoid.FG GrothendieckGroup M := fg Monoid.FG.fg_top

end Algebra.GrothendieckGroup
