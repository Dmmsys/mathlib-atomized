/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.GroupTheory.OreLocalization.Cardinality
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Cardinality of Ore localizations of rings

This file contains some results on cardinality of Ore localizations of rings.
-/

public section

universe u

open Cardinal

namespace OreLocalization

variable {R : Type u} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S]

/--
theorem `cardinalMk` / 定理 `cardinalMk`

English:
theorem cardinalMk
  given: (hS : S <= nonZeroDivisorsLeft R)
  statement: #(OreLocalization S R) = #R
  proof: le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))

中文:
定理 cardinalMk
  条件: (hS : S <= nonZeroDivisorsLeft R)
  结论: #(OreLocalization S R) = #R
  证明: le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))

Depends on / 依赖: cardinalMk_le, le_antisymm, mk_le_of_injective, numeratorHom_inj
-/
theorem cardinalMk (hS : S <= nonZeroDivisorsLeft R) : #(OreLocalization S R) = #R :=
  le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))

end OreLocalization
