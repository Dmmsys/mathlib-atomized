/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Fibrant and cofibrant objects in a model category

Once a category `C` has been endowed with a `CategoryWithCofibrations C`
instance, it is possible to define the property `IsCofibrant X` for
any `X : C` as an abbreviation for `Cofibration (initial.to X : ⊥_ C ⟶ X)`.
(Fibrant objects are defined similarly.)

-/

public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C]

section

variable [CategoryWithCofibrations C] [HasInitial C]

/--
Definition of `IsCofibrant` / `IsCofibrant` 的定义

English:
abbreviation IsCofibrant
  signature: (X : C)
  body: Cofibration (initial.to X)

中文:
缩写 IsCofibrant
  签名: (X : C)
  定义体: Cofibration (initial.to X)

Depends on / 依赖: Cofibration, initial, initial.to
-/
abbrev IsCofibrant (X : C) : Prop := Cofibration (initial.to X)

/--
lemma `isCofibrant_iff` / 引理 `isCofibrant_iff`

English:
lemma isCofibrant_iff
  given: (X : C)
  proof: Iff.rfl

中文:
引理 isCofibrant_iff
  条件: (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCofibrant_iff (X : C) :
    IsCofibrant X ↔ Cofibration (initial.to X) := Iff.rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isCofibrant_iff_of_isInitial` / 引理 `isCofibrant_iff_of_isInitial`

English:
lemma isCofibrant_iff_of_isInitial
  statement: [(cofibrations C).RespectsIso]
  proof: by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

中文:
引理 isCofibrant_iff_of_isInitial
  结论: [(cofibrations C).RespectsIso]
  证明: by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

Depends on / 依赖: Arrow.isoMk, IsInitial, IsInitial.uniqueUpToIso, Iso.refl, arrow_mk_iso_iff, cofibration_iff, cofibrations, initialIsInitial, uniqueUpToIso
-/
lemma isCofibrant_iff_of_isInitial [(cofibrations C).RespectsIso]
    {A X : C} (i : A ⟶ X) (hA : IsInitial A) :
    IsCofibrant X ↔ Cofibration i := by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

/--
lemma `isCofibrant_of_cofibration` / 引理 `isCofibrant_of_cofibration`

English:
lemma isCofibrant_of_cofibration
  statement: [(cofibrations C).IsStableUnderComposition]
  proof: by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

中文:
引理 isCofibrant_of_cofibration
  结论: [(cofibrations C).IsStableUnderComposition]
  证明: by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

Depends on / 依赖: Subsingleton, Subsingleton.elim, infer_instance, initial, initial.to, isCofibrant_iff
-/
lemma isCofibrant_of_cofibration [(cofibrations C).IsStableUnderComposition]
    {X Y : C} (i : X ⟶ Y) [Cofibration i] [hX : IsCofibrant X] :
    IsCofibrant Y := by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

section

variable (X Y : C) [(cofibrations C).IsStableUnderCobaseChange] [HasBinaryCoproduct X Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hY
  signature: : IsCofibrant Y] :
  body: by
  rw [isCofibrant_iff] at hY
  rw [cofibration_iff] at hY ⊢
  exact MorphismProperty.of_isPushout
    ((IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial).flip) hY

中文:
实例 [hY
  签名: : IsCofibrant Y] :
  定义体: by
  rw [isCofibrant_iff] at hY
  rw [cofibration_iff] at hY ⊢
  exact MorphismProperty.of_isPushout
    ((IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial).flip) hY

Depends on / 依赖: IsPushout, IsPushout.of_isColimit_binaryCofan_of_isInitial, MorphismProperty, MorphismProperty.of_isPushout, cofibration_iff, colimit, colimit.isColimit, initialIsInitial, isCofibrant_iff, isColimit, of_isColimit_binaryCofan_of_isInitial, of_isPushout
-/
instance [hY : IsCofibrant Y] :
    Cofibration (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hY
  rw [cofibration_iff] at hY ⊢
  exact MorphismProperty.of_isPushout
    ((IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial).flip) hY

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hX
  signature: : IsCofibrant X] : Cofibration (coprod.inr : Y ⟶ X ⨿ Y)
  body: by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact MorphismProperty.of_isPushout
    (IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial) hX

中文:
实例 [hX
  签名: : IsCofibrant X] : Cofibration (coprod.inr : Y ⟶ X ⨿ Y)
  定义体: by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact MorphismProperty.of_isPushout
    (IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial) hX

Depends on / 依赖: IsPushout, IsPushout.of_isColimit_binaryCofan_of_isInitial, MorphismProperty, MorphismProperty.of_isPushout, cofibration_iff, colimit, colimit.isColimit, initialIsInitial, isCofibrant_iff, isColimit, of_isColimit_binaryCofan_of_isInitial, of_isPushout
-/
instance [hX : IsCofibrant X] : Cofibration (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [isCofibrant_iff] at hX
  rw [cofibration_iff] at hX ⊢
  exact MorphismProperty.of_isPushout
    (IsPushout.of_isColimit_binaryCofan_of_isInitial
    (colimit.isColimit (pair X Y)) initialIsInitial) hX

end

end

section

variable [CategoryWithFibrations C] [HasTerminal C]

/--
Definition of `IsFibrant` / `IsFibrant` 的定义

English:
abbreviation IsFibrant
  signature: (X : C)
  body: Fibration (terminal.from X)

中文:
缩写 IsFibrant
  签名: (X : C)
  定义体: Fibration (terminal.from X)

Depends on / 依赖: Fibration, terminal, terminal.from
-/
abbrev IsFibrant (X : C) : Prop := Fibration (terminal.from X)

/--
lemma `isFibrant_iff` / 引理 `isFibrant_iff`

English:
lemma isFibrant_iff
  given: (X : C)
  proof: Iff.rfl

中文:
引理 isFibrant_iff
  条件: (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isFibrant_iff (X : C) :
    IsFibrant X ↔ Fibration (terminal.from X) := Iff.rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isFibrant_iff_of_isTerminal` / 引理 `isFibrant_iff_of_isTerminal`

English:
lemma isFibrant_iff_of_isTerminal
  statement: [(fibrations C).RespectsIso]
  proof: by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

中文:
引理 isFibrant_iff_of_isTerminal
  结论: [(fibrations C).RespectsIso]
  证明: by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

Depends on / 依赖: Arrow.isoMk, IsTerminal, IsTerminal.uniqueUpToIso, Iso.refl, arrow_mk_iso_iff, fibration_iff, fibrations, terminalIsTerminal, uniqueUpToIso
-/
lemma isFibrant_iff_of_isTerminal [(fibrations C).RespectsIso]
    {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) :
    IsFibrant X ↔ Fibration p := by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

/--
lemma `isFibrant_of_fibration` / 引理 `isFibrant_of_fibration`

English:
lemma isFibrant_of_fibration
  statement: [(fibrations C).IsStableUnderComposition]
  proof: by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

中文:
引理 isFibrant_of_fibration
  结论: [(fibrations C).IsStableUnderComposition]
  证明: by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

Depends on / 依赖: Subsingleton, Subsingleton.elim, infer_instance, isFibrant_iff, terminal, terminal.from
-/
lemma isFibrant_of_fibration [(fibrations C).IsStableUnderComposition]
    {X Y : C} (p : X ⟶ Y) [Fibration p] [hY : IsFibrant Y] :
    IsFibrant X := by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

section

variable (X Y : C) [(fibrations C).IsStableUnderBaseChange]
  [HasBinaryProduct X Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hY
  signature: : IsFibrant Y] :
  body: by
  rw [isFibrant_iff] at hY
  rw [fibration_iff] at hY ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal).flip hY

中文:
实例 [hY
  签名: : IsFibrant Y] :
  定义体: by
  rw [isFibrant_iff] at hY
  rw [fibration_iff] at hY ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal).flip hY

Depends on / 依赖: IsPullback, IsPullback.of_isLimit_binaryFan_of_isTerminal, MorphismProperty, MorphismProperty.of_isPullback, fibration_iff, isFibrant_iff, isLimit, limit.isLimit, of_isLimit_binaryFan_of_isTerminal, of_isPullback, terminalIsTerminal
-/
instance [hY : IsFibrant Y] :
    Fibration (prod.fst : X ⨯ Y ⟶ X) := by
  rw [isFibrant_iff] at hY
  rw [fibration_iff] at hY ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal).flip hY

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hX
  signature: : IsFibrant X] : Fibration (prod.snd : X ⨯ Y ⟶ Y)
  body: by
  rw [isFibrant_iff] at hX
  rw [fibration_iff] at hX ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal) hX

中文:
实例 [hX
  签名: : IsFibrant X] : Fibration (prod.snd : X ⨯ Y ⟶ Y)
  定义体: by
  rw [isFibrant_iff] at hX
  rw [fibration_iff] at hX ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal) hX

Depends on / 依赖: IsPullback, IsPullback.of_isLimit_binaryFan_of_isTerminal, MorphismProperty, MorphismProperty.of_isPullback, fibration_iff, isFibrant_iff, isLimit, limit.isLimit, of_isLimit_binaryFan_of_isTerminal, of_isPullback, terminalIsTerminal
-/
instance [hX : IsFibrant X] : Fibration (prod.snd : X ⨯ Y ⟶ Y) := by
  rw [isFibrant_iff] at hX
  rw [fibration_iff] at hX ⊢
  exact MorphismProperty.of_isPullback
    (IsPullback.of_isLimit_binaryFan_of_isTerminal
      (limit.isLimit (pair X Y)) terminalIsTerminal) hX

end

end

end HomotopicalAlgebra
