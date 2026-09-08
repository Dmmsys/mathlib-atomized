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

/-
**OreLocalization.cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：cardinalMk (hS : S <= nonZeroDivisorsLeft R) : #(OreLocalization S R) = #R
参数：hS : S <= nonZeroDivisorsLeft R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OreLocalization.cardinalMk_le`：cardinalMk_le : #(OreLocalization S R) <=
 #R
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `OreLocalization.numeratorHom_inj`：numeratorHom_inj (hS : S <= nonZeroDiv
isorsLeft R) : Function.Injective (numeratorHom : R -> R[S⁻¹])
-/
theorem cardinalMk (hS : S ≤ nonZeroDivisorsLeft R) : #(OreLocalization S R) = #R :=
  le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))

end OreLocalization

