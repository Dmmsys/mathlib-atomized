/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Transporting existence of specific limits across equivalences

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/

public section


open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/--
theorem `hasInitial_of_equivalence` / 定理 `hasInitial_of_equivalence`

English:
theorem hasInitial_of_equivalence
  given: (e : D ⥤ C) [e.IsEquivalence] [HasInitial C]
  statement: HasInitial D
  proof: Adjunction.hasColimitsOfShape_of_equivalence e

中文:
定理 hasInitial_of_equivalence
  条件: (e : D ⥤ C) [e.是等价] [HasInitial C]
  结论: HasInitial D
  证明: Adjunction.hasColimitsOfShape_of_equivalence e

Depends on / 依赖: Adjunction, Adjunction.hasColimitsOfShape_of_equivalence, hasColimitsOfShape_of_equivalence
-/
theorem hasInitial_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasInitial C] : HasInitial D :=
  Adjunction.hasColimitsOfShape_of_equivalence e

/--
theorem `Equivalence.hasInitial_iff` / 定理 `Equivalence.hasInitial_iff`

English:
theorem Equivalence.hasInitial_iff
  given: (e : C ≌ D)
  statement: HasInitial C ↔ HasInitial D
  proof: ⟨fun (_ : HasInitial C) => hasInitial_of_equivalence e.inverse,
    fun (_ : HasInitial D) => hasInitial_of_equivalence e.functor⟩

中文:
定理 等价.hasInitial_iff
  条件: (e : C ≌ D)
  结论: HasInitial C ↔ HasInitial D
  证明: ⟨fun (_ : HasInitial C) => hasInitial_of_equivalence e.inverse,
    fun (_ : HasInitial D) => hasInitial_of_equivalence e.functor⟩

Depends on / 依赖: HasInitial, e.functor, e.inverse, functor, hasInitial_of_equivalence, inverse
-/
theorem Equivalence.hasInitial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun (_ : HasInitial C) => hasInitial_of_equivalence e.inverse,
    fun (_ : HasInitial D) => hasInitial_of_equivalence e.functor⟩

/--
theorem `hasTerminal_of_equivalence` / 定理 `hasTerminal_of_equivalence`

English:
theorem hasTerminal_of_equivalence
  given: (e : D ⥤ C) [e.IsEquivalence] [HasTerminal C]
  statement: HasTerminal D
  proof: Adjunction.hasLimitsOfShape_of_equivalence e

中文:
定理 hasTerminal_of_equivalence
  条件: (e : D ⥤ C) [e.是等价] [有终止 C]
  结论: 有终止 D
  证明: Adjunction.hasLimitsOfShape_of_equivalence e

Depends on / 依赖: Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, hasLimitsOfShape_of_equivalence
-/
theorem hasTerminal_of_equivalence (e : D ⥤ C) [e.IsEquivalence] [HasTerminal C] : HasTerminal D :=
  Adjunction.hasLimitsOfShape_of_equivalence e

/--
theorem `Equivalence.hasTerminal_iff` / 定理 `Equivalence.hasTerminal_iff`

English:
theorem Equivalence.hasTerminal_iff
  given: (e : C ≌ D)
  statement: HasTerminal C ↔ HasTerminal D
  proof: ⟨fun (_ : HasTerminal C) => hasTerminal_of_equivalence e.inverse,
    fun (_ : HasTerminal D) => hasTerminal_of_equivalence e.functor⟩

中文:
定理 等价.hasTerminal_iff
  条件: (e : C ≌ D)
  结论: 有终止 C ↔ 有终止 D
  证明: ⟨fun (_ : HasTerminal C) => hasTerminal_of_equivalence e.inverse,
    fun (_ : HasTerminal D) => hasTerminal_of_equivalence e.functor⟩

Depends on / 依赖: HasTerminal, e.functor, e.inverse, functor, hasTerminal_of_equivalence, inverse
-/
theorem Equivalence.hasTerminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun (_ : HasTerminal C) => hasTerminal_of_equivalence e.inverse,
    fun (_ : HasTerminal D) => hasTerminal_of_equivalence e.functor⟩

end CategoryTheory
