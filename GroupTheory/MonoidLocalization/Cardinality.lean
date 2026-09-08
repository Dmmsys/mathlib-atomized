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
/-
**Localization.cardinalMk_le** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：cardinalMk_le : #(Localization S) <= #M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.cardinalMk_le`：cardinalMk_le : #(OreLocalization S R) <=
 #R
-/
theorem cardinalMk_le : #(Localization S) ≤ #M :=
  OreLocalization.cardinalMk_le S

end Localization

