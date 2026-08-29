/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.GroupTheory.OreLocalization.Cardinality

/-!

# Cardinality of localizations of commutative monoids

This file contains some results on cardinality of localizations.

-/

public section

universe u

open Cardinal

namespace Localization

variable {M : Type u} [CommMonoid M] (S : Submonoid M)

@[to_additive]
/--
theorem `cardinalMk_le` / 定理 `cardinalMk_le`

English:
theorem cardinalMk_le
  statement: #(Localization S) <= #M
  proof: OreLocalization.cardinalMk_le S

中文:
定理 cardinalMk_le
  结论: #(Localization S) <= #M
  证明: OreLocalization.cardinalMk_le S

Depends on / 依赖: OreLocalization, OreLocalization.cardinalMk_le, cardinalMk_le
-/
theorem cardinalMk_le : #(Localization S) <= #M :=
  OreLocalization.cardinalMk_le S

end Localization
