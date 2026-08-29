/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

@[expose] public section


noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable (C)

/--
Definition of `HasTerminal` / `HasTerminal` 的定义

English:
abbreviation HasTerminal
  body: HasLimitsOfShape (Discrete.{0} PEmpty) C

中文:
缩写 HasTerminal
  定义体: HasLimitsOfShape (Discrete.{0} PEmpty) C

Depends on / 依赖: Discrete, HasLimitsOfShape, PEmpty
-/
abbrev HasTerminal :=
  HasLimitsOfShape (Discrete.{0} PEmpty) C

/--
Definition of `HasInitial` / `HasInitial` 的定义

English:
abbreviation HasInitial
  body: HasColimitsOfShape (Discrete.{0} PEmpty) C

中文:
缩写 HasInitial
  定义体: HasColimitsOfShape (Discrete.{0} PEmpty) C

Depends on / 依赖: ContainsZero, Discrete, HasColimitsOfShape, HasZeroObject, Nonempty, P.ContainsZero, P.Nonempty, PEmpty
-/
abbrev HasInitial :=
  HasColimitsOfShape (Discrete.{0} PEmpty) C

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/--
theorem `hasTerminalChangeDiagram` / 定理 `hasTerminalChangeDiagram`

English:
theorem hasTerminalChangeDiagram
  given: (h : HasLimit F₁)
  statement: HasLimit F₂
  proof: ⟨⟨⟨⟨limit F₁, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

中文:
定理 hasTerminalChangeDiagram
  条件: (h : HasLimit F₁)
  结论: HasLimit F₂
  证明: ⟨⟨⟨⟨limit F₁, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

Depends on / 依赖: cat_disch, eqToIso, isLimit, isLimitChangeEmptyCone, limit.isLimit
-/
theorem hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

/--
theorem `hasTerminalChangeUniverse` / 定理 `hasTerminalChangeUniverse`

English:
theorem hasTerminalChangeUniverse
  given: [h : HasLimitsOfShape (Discrete.{w} PEmpty) C]
  proof: hasTerminalChangeDiagram C (h.1 (Functor.empty C))

中文:
定理 hasTerminalChangeUniverse
  条件: [h : HasLimitsOfShape (Discrete.{w} PEmpty) C]
  证明: hasTerminalChangeDiagram C (h.1 (Functor.empty C))

Depends on / 依赖: Functor, Functor.empty, hasTerminalChangeDiagram
-/
theorem hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
    HasLimitsOfShape (Discrete.{w'} PEmpty) C where
  has_limit _ := hasTerminalChangeDiagram C (h.1 (Functor.empty C))

/--
theorem `hasInitialChangeDiagram` / 定理 `hasInitialChangeDiagram`

English:
theorem hasInitialChangeDiagram
  given: (h : HasColimit F₁)
  statement: HasColimit F₂
  proof: ⟨⟨⟨⟨colimit F₁, by cat_disch, by simp⟩,
    isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩

中文:
定理 hasInitialChangeDiagram
  条件: (h : HasColimit F₁)
  结论: HasColimit F₂
  证明: ⟨⟨⟨⟨colimit F₁, by cat_disch, by simp⟩,
    isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩

Depends on / 依赖: cat_disch, colimit, colimit.isColimit, eqToIso, isColimit, isColimitChangeEmptyCocone
-/
theorem hasInitialChangeDiagram (h : HasColimit F₁) : HasColimit F₂ :=
  ⟨⟨⟨⟨colimit F₁, by cat_disch, by simp⟩,
    isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩

/--
theorem `hasInitialChangeUniverse` / 定理 `hasInitialChangeUniverse`

English:
theorem hasInitialChangeUniverse
  given: [h : HasColimitsOfShape (Discrete.{w} PEmpty) C]
  proof: hasInitialChangeDiagram C (h.1 (Functor.empty C))

中文:
定理 hasInitialChangeUniverse
  条件: [h : HasColimitsOfShape (Discrete.{w} PEmpty) C]
  证明: hasInitialChangeDiagram C (h.1 (Functor.empty C))

Depends on / 依赖: Functor, Functor.empty, hasInitialChangeDiagram
-/
theorem hasInitialChangeUniverse [h : HasColimitsOfShape (Discrete.{w} PEmpty) C] :
    HasColimitsOfShape (Discrete.{w'} PEmpty) C where
  has_colimit _ := hasInitialChangeDiagram C (h.1 (Functor.empty C))

end Univ

/--
Definition of `terminal` / `terminal` 的定义

English:
abbreviation terminal
  signature: [HasTerminal C]
  body: limit (Functor.empty.{0} C)

中文:
缩写 terminal
  签名: [HasTerminal C]
  定义体: limit (Functor.empty.{0} C)

Depends on / 依赖: Functor, Functor.empty
-/
abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{0} C)

/--
Definition of `initial` / `initial` 的定义

English:
abbreviation initial
  signature: [HasInitial C]
  body: colimit (Functor.empty.{0} C)

中文:
缩写 initial
  签名: [HasInitial C]
  定义体: colimit (Functor.empty.{0} C)

Depends on / 依赖: Functor, Functor.empty, colimit
-/
abbrev initial [HasInitial C] : C :=
  colimit (Functor.empty.{0} C)

/-- Notation for the terminal object in `C` -/
notation "⊤_ " C:20 => terminal C

/-- Notation for the initial object in `C` -/
notation "⊥_ " C:20 => initial C

section

variable {C}

/--
theorem `hasTerminal_of_unique` / 定理 `hasTerminal_of_unique`

English:
theorem hasTerminal_of_unique
  given: (X : C) [forall Y, Nonempty (Y ⟶ X)] [forall Y, Subsingleton (Y ⟶ X)]
  proof: .mk ⟨_, (isTerminalEquivUnique F X).invFun fun _ =>
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

中文:
定理 hasTerminal_of_unique
  条件: (X : C) [对任意 Y, Nonempty (Y ⟶ X)] [对任意 Y, Subsingleton (Y ⟶ X)]
  证明: .mk ⟨_, (isTerminalEquivUnique F X).invFun fun _ =>
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

Depends on / 依赖: invFun, isTerminalEquivUnique
-/
theorem hasTerminal_of_unique (X : C) [forall Y, Nonempty (Y ⟶ X)] [forall Y, Subsingleton (Y ⟶ X)] :
    HasTerminal C where
  has_limit F := .mk ⟨_, (isTerminalEquivUnique F X).invFun fun _ =>
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

/--
theorem `IsTerminal.hasTerminal` / 定理 `IsTerminal.hasTerminal`

English:
theorem IsTerminal.hasTerminal
  given: {X : C} (h : IsTerminal X)
  statement: HasTerminal C
  proof: { has_limit := fun F => HasLimit.mk ⟨⟨X, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

中文:
定理 IsTerminal.hasTerminal
  条件: {X : C} (h : IsTerminal X)
  结论: HasTerminal C
  证明: { has_limit := fun F => HasLimit.mk ⟨⟨X, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

Depends on / 依赖: HasLimit, HasLimit.mk, Iso.refl, cat_disch, has_limit, isLimitChangeEmptyCone
-/
theorem IsTerminal.hasTerminal {X : C} (h : IsTerminal X) : HasTerminal C :=
  { has_limit := fun F => HasLimit.mk ⟨⟨X, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

/--
theorem `hasInitial_of_unique` / 定理 `hasInitial_of_unique`

English:
theorem hasInitial_of_unique
  given: (X : C) [forall Y, Nonempty (X ⟶ Y)] [forall Y, Subsingleton (X ⟶ Y)]
  proof: .mk ⟨_, (isInitialEquivUnique F X).invFun fun _ =>
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

中文:
定理 hasInitial_of_unique
  条件: (X : C) [对任意 Y, Nonempty (X ⟶ Y)] [对任意 Y, Subsingleton (X ⟶ Y)]
  证明: .mk ⟨_, (isInitialEquivUnique F X).invFun fun _ =>
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

Depends on / 依赖: invFun, isInitialEquivUnique
-/
theorem hasInitial_of_unique (X : C) [forall Y, Nonempty (X ⟶ Y)] [forall Y, Subsingleton (X ⟶ Y)] :
    HasInitial C where
  has_colimit F := .mk ⟨_, (isInitialEquivUnique F X).invFun fun _ =>
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

/--
theorem `IsInitial.hasInitial` / 定理 `IsInitial.hasInitial`

English:
theorem IsInitial.hasInitial
  given: {X : C} (h : IsInitial X)
  statement: HasInitial C where
  proof: HasColimit.mk ⟨⟨X, by cat_disch, by simp⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩

中文:
定理 IsInitial.hasInitial
  条件: {X : C} (h : IsInitial X)
  结论: HasInitial C where
  证明: HasColimit.mk ⟨⟨X, by cat_disch, by simp⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩

Depends on / 依赖: HasColimit, HasColimit.mk, Iso.refl, cat_disch, isColimitChangeEmptyCocone
-/
theorem IsInitial.hasInitial {X : C} (h : IsInitial X) : HasInitial C where
  has_colimit F :=
    HasColimit.mk ⟨⟨X, by cat_disch, by simp⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩

/--
Definition of `terminal.from` / `terminal.from` 的定义

English:
abbreviation terminal.from
  signature: [HasTerminal C] (P : C)
  body: limit.lift (Functor.empty C) (asEmptyCone P)

中文:
缩写 terminal.from
  签名: [HasTerminal C] (P : C)
  定义体: limit.lift (Functor.empty C) (asEmptyCone P)

Depends on / 依赖: Functor, Functor.empty, asEmptyCone, limit.lift
-/
abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)

/--
Definition of `initial.to` / `initial.to` 的定义

English:
abbreviation initial.to
  signature: [HasInitial C] (P : C)
  body: colimit.desc (Functor.empty C) (asEmptyCocone P)

中文:
缩写 initial.to
  签名: [HasInitial C] (P : C)
  定义体: colimit.desc (Functor.empty C) (asEmptyCocone P)

Depends on / 依赖: Functor, Functor.empty, asEmptyCocone, colimit, colimit.desc
-/
abbrev initial.to [HasInitial C] (P : C) : ⊥_ C ⟶ P :=
  colimit.desc (Functor.empty C) (asEmptyCocone P)

/--
Definition of `terminalIsTerminal` / `terminalIsTerminal` 的定义

English:
definition terminalIsTerminal
  signature: [HasTerminal C]
  body: terminal.from _

中文:
定义 terminalIsTerminal
  签名: [HasTerminal C]
  定义体: terminal.from _

Depends on / 依赖: terminal, terminal.from
-/
def terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where
  lift _ := terminal.from _

/--
Definition of `initialIsInitial` / `initialIsInitial` 的定义

English:
definition initialIsInitial
  signature: [HasInitial C]
  body: initial.to _

中文:
定义 initialIsInitial
  签名: [HasInitial C]
  定义体: initial.to _

Depends on / 依赖: initial, initial.to
-/
def initialIsInitial [HasInitial C] : IsInitial (⊥_ C) where
  desc _ := initial.to _

/--
Instance `uniqueToTerminal` / 实例 `uniqueToTerminal`

English:
instance uniqueToTerminal
  signature: [HasTerminal C] (P : C)
  body: isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P

中文:
实例 uniqueToTerminal
  签名: [HasTerminal C] (P : C)
  定义体: isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P

Depends on / 依赖: isTerminalEquivUnique, terminalIsTerminal
-/
instance uniqueToTerminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C) :=
  isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P

/--
Instance `uniqueFromInitial` / 实例 `uniqueFromInitial`

English:
instance uniqueFromInitial
  signature: [HasInitial C] (P : C)
  body: isInitialEquivUnique _ (⊥_ C) initialIsInitial P

中文:
实例 uniqueFromInitial
  签名: [HasInitial C] (P : C)
  定义体: isInitialEquivUnique _ (⊥_ C) initialIsInitial P

Depends on / 依赖: initialIsInitial, isInitialEquivUnique
-/
instance uniqueFromInitial [HasInitial C] (P : C) : Unique (⊥_ C ⟶ P) :=
  isInitialEquivUnique _ (⊥_ C) initialIsInitial P

/--
theorem `terminal.hom_ext` / 定理 `terminal.hom_ext`

English:
theorem terminal.hom_ext
  given: [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C)
  statement: f = g
  proof: by ext ⟨⟨⟩⟩

中文:
定理 terminal.hom_ext
  条件: [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C)
  结论: f = g
  证明: by ext ⟨⟨⟩⟩
-/
@[ext] theorem terminal.hom_ext [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C) : f = g := by ext ⟨⟨⟩⟩

/--
theorem `initial.hom_ext` / 定理 `initial.hom_ext`

English:
theorem initial.hom_ext
  given: [HasInitial C] {P : C} (f g : ⊥_ C ⟶ P)
  statement: f = g
  proof: by ext ⟨⟨⟩⟩

@[reassoc (attr := simp)]

中文:
定理 initial.hom_ext
  条件: [HasInitial C] {P : C} (f g : ⊥_ C ⟶ P)
  结论: f = g
  证明: by ext ⟨⟨⟩⟩

@[reassoc (attr := simp)]
-/
@[ext] theorem initial.hom_ext [HasInitial C] {P : C} (f g : ⊥_ C ⟶ P) : f = g := by ext ⟨⟨⟩⟩

@[reassoc (attr := simp)]
/--
theorem `terminal.comp_from` / 定理 `terminal.comp_from`

English:
theorem terminal.comp_from
  given: [HasTerminal C] {P Q : C} (f : P ⟶ Q)
  proof: by
  simp [eq_iff_true_of_subsingleton]

中文:
定理 terminal.comp_from
  条件: [HasTerminal C] {P Q : C} (f : P ⟶ Q)
  证明: by
  simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem terminal.comp_from [HasTerminal C] {P Q : C} (f : P ⟶ Q) :
    f ≫ terminal.from Q = terminal.from P := by
  simp [eq_iff_true_of_subsingleton]

-- `initial.to_comp_assoc` does not need the `simp` attribute.
@[simp, reassoc]
/--
theorem `initial.to_comp` / 定理 `initial.to_comp`

English:
theorem initial.to_comp
  given: [HasInitial C] {P Q : C} (f : P ⟶ Q)
  statement: initial.to P ≫ f = initial.to Q
  proof: by
  simp [eq_iff_true_of_subsingleton]

中文:
定理 initial.to_comp
  条件: [HasInitial C] {P Q : C} (f : P ⟶ Q)
  结论: initial.to P ≫ f = initial.to Q
  证明: by
  simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem initial.to_comp [HasInitial C] {P Q : C} (f : P ⟶ Q) : initial.to P ≫ f = initial.to Q := by
  simp [eq_iff_true_of_subsingleton]

/-- The (unique) isomorphism between the chosen initial object and any other initial object. -/
@[simps!]
/--
Definition of `initialIsoIsInitial` / `initialIsoIsInitial` 的定义

English:
definition initialIsoIsInitial
  signature: [HasInitial C] {P : C} (t : IsInitial P)
  body: initialIsInitial.uniqueUpToIso t

中文:
定义 initialIsoIsInitial
  签名: [HasInitial C] {P : C} (t : IsInitial P)
  定义体: initialIsInitial.uniqueUpToIso t

Depends on / 依赖: initialIsInitial, initialIsInitial.uniqueUpToIso, uniqueUpToIso
-/
def initialIsoIsInitial [HasInitial C] {P : C} (t : IsInitial P) : ⊥_ C ≅ P :=
  initialIsInitial.uniqueUpToIso t

/-- The (unique) isomorphism between the chosen terminal object and any other terminal object. -/
@[simps!]
/--
Definition of `terminalIsoIsTerminal` / `terminalIsoIsTerminal` 的定义

English:
definition terminalIsoIsTerminal
  signature: [HasTerminal C] {P : C} (t : IsTerminal P)
  body: terminalIsTerminal.uniqueUpToIso t

中文:
定义 terminalIsoIsTerminal
  签名: [HasTerminal C] {P : C} (t : IsTerminal P)
  定义体: terminalIsTerminal.uniqueUpToIso t

Depends on / 依赖: terminalIsTerminal, terminalIsTerminal.uniqueUpToIso, uniqueUpToIso
-/
def terminalIsoIsTerminal [HasTerminal C] {P : C} (t : IsTerminal P) : ⊤_ C ≅ P :=
  terminalIsTerminal.uniqueUpToIso t

/--
Instance `terminal.isSplitMono_from` / 实例 `terminal.isSplitMono_from`

English:
instance terminal.isSplitMono_from
  signature: {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y)
  body: IsTerminal.isSplitMono_from terminalIsTerminal _

中文:
实例 terminal.isSplitMono_from
  签名: {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y)
  定义体: IsTerminal.isSplitMono_from terminalIsTerminal _

Depends on / 依赖: IsTerminal, IsTerminal.isSplitMono_from, isSplitMono_from, terminalIsTerminal
-/
instance terminal.isSplitMono_from {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y) : IsSplitMono f :=
  IsTerminal.isSplitMono_from terminalIsTerminal _

/--
Instance `initial.isSplitEpi_to` / 实例 `initial.isSplitEpi_to`

English:
instance initial.isSplitEpi_to
  signature: {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C)
  body: IsInitial.isSplitEpi_to initialIsInitial _

中文:
实例 initial.isSplitEpi_to
  签名: {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C)
  定义体: IsInitial.isSplitEpi_to initialIsInitial _

Depends on / 依赖: IsInitial, IsInitial.isSplitEpi_to, P.prop_of_iso, initialIsInitial, isSplitEpi_to, mapIso, prop_of_iso, shiftFunctor
-/
instance initial.isSplitEpi_to {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C) : IsSplitEpi f :=
  IsInitial.isSplitEpi_to initialIsInitial _

/--
Instance `hasInitial_op_of_hasTerminal` / 实例 `hasInitial_op_of_hasTerminal`

English:
instance hasInitial_op_of_hasTerminal
  signature: [HasTerminal C]
  body: (initialOpOfTerminal terminalIsTerminal).hasInitial

中文:
实例 hasInitial_op_of_hasTerminal
  签名: [HasTerminal C]
  定义体: (initialOpOfTerminal terminalIsTerminal).hasInitial

Depends on / 依赖: hasInitial, initialOpOfTerminal, terminalIsTerminal
-/
instance hasInitial_op_of_hasTerminal [HasTerminal C] : HasInitial Cᵒᵖ :=
  (initialOpOfTerminal terminalIsTerminal).hasInitial

/--
Instance `hasTerminal_op_of_hasInitial` / 实例 `hasTerminal_op_of_hasInitial`

English:
instance hasTerminal_op_of_hasInitial
  signature: [HasInitial C]
  body: (terminalOpOfInitial initialIsInitial).hasTerminal

中文:
实例 hasTerminal_op_of_hasInitial
  签名: [HasInitial C]
  定义体: (terminalOpOfInitial initialIsInitial).hasTerminal

Depends on / 依赖: hasTerminal, initialIsInitial, terminalOpOfInitial
-/
instance hasTerminal_op_of_hasInitial [HasInitial C] : HasTerminal Cᵒᵖ :=
  (terminalOpOfInitial initialIsInitial).hasTerminal

/--
theorem `hasTerminal_of_hasInitial_op` / 定理 `hasTerminal_of_hasInitial_op`

English:
theorem hasTerminal_of_hasInitial_op
  given: [HasInitial Cᵒᵖ]
  statement: HasTerminal C
  proof: (terminalUnopOfInitial initialIsInitial).hasTerminal

中文:
定理 hasTerminal_of_hasInitial_op
  条件: [HasInitial Cᵒᵖ]
  结论: HasTerminal C
  证明: (terminalUnopOfInitial initialIsInitial).hasTerminal

Depends on / 依赖: hasTerminal, initialIsInitial, terminalUnopOfInitial
-/
theorem hasTerminal_of_hasInitial_op [HasInitial Cᵒᵖ] : HasTerminal C :=
  (terminalUnopOfInitial initialIsInitial).hasTerminal

/--
theorem `hasInitial_of_hasTerminal_op` / 定理 `hasInitial_of_hasTerminal_op`

English:
theorem hasInitial_of_hasTerminal_op
  given: [HasTerminal Cᵒᵖ]
  statement: HasInitial C
  proof: (initialUnopOfTerminal terminalIsTerminal).hasInitial

中文:
定理 hasInitial_of_hasTerminal_op
  条件: [HasTerminal Cᵒᵖ]
  结论: HasInitial C
  证明: (initialUnopOfTerminal terminalIsTerminal).hasInitial

Depends on / 依赖: hasInitial, initialUnopOfTerminal, terminalIsTerminal
-/
theorem hasInitial_of_hasTerminal_op [HasTerminal Cᵒᵖ] : HasInitial C :=
  (initialUnopOfTerminal terminalIsTerminal).hasInitial

instance {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C] :
    HasLimit ((CategoryTheory.Functor.const J).obj (⊤_ C)) :=
  HasLimit.mk
    { cone :=
        { pt := ⊤_ C
          π := { app := fun _ => terminal.from _ } }
      isLimit := { lift := fun _ => terminal.from _ } }

/-- The limit of the constant `⊤_ C` functor is `⊤_ C`. -/
@[simps hom]
/--
Definition of `limitConstTerminal` / `limitConstTerminal` 的定义

English:
definition limitConstTerminal
  signature: {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C]
  body: terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { pt := ⊤_ C
        π := { app := fun _ => terminal.from _ } }

@[reassoc (attr := simp)]

中文:
定义 limitConstTerminal
  签名: {J : 类型} [Category* J] {C : 类型} [Category* C] [HasTerminal C]
  定义体: terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { pt := ⊤_ C
        π := { app := fun _ => terminal.from _ } }

@[reassoc (attr := simp)]

Depends on / 依赖: terminal, terminal.from
-/
def limitConstTerminal {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C] :
    limit ((CategoryTheory.Functor.const J).obj (⊤_ C)) ≅ ⊤_ C where
  hom := terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { pt := ⊤_ C
        π := { app := fun _ => terminal.from _ } }

@[reassoc (attr := simp)]
/--
theorem `limitConstTerminal_inv_π` / 定理 `limitConstTerminal_inv_π`

English:
theorem limitConstTerminal_inv_π
  statement: {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C]
  proof: by cat_disch

中文:
定理 limitConstTerminal_inv_π
  结论: {J : 类型} [Category* J] {C : 类型} [Category* C] [HasTerminal C]
  证明: by cat_disch

Depends on / 依赖: P.le_shift, cat_disch, le_shift
-/
theorem limitConstTerminal_inv_π {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C]
    {j : J} :
    limitConstTerminal.inv ≫ limit.π ((CategoryTheory.Functor.const J).obj (⊤_ C)) j =
      terminal.from _ := by cat_disch

instance {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C] :
    HasColimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) :=
  HasColimit.mk
    { cocone :=
        { pt := ⊥_ C
          ι := { app := fun _ => initial.to _ } }
      isColimit := { desc := fun _ => initial.to _ } }

/-- The colimit of the constant `⊥_ C` functor is `⊥_ C`. -/
@[simps inv]
/--
Definition of `colimitConstInitial` / `colimitConstInitial` 的定义

English:
definition colimitConstInitial
  signature: {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C]
  body: colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { pt := ⊥_ C
        ι := { app := fun _ => initial.to _ } }
  inv := initial.to _

@[reassoc (attr := simp)]

中文:
定义 colimitConstInitial
  签名: {J : 类型} [Category* J] {C : 类型} [Category* C] [HasInitial C]
  定义体: colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { pt := ⊥_ C
        ι := { app := fun _ => initial.to _ } }
  inv := initial.to _

@[reassoc (attr := simp)]

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.const, False.elim, Functor, colimit, colimit.desc, initial, initial.to
-/
def colimitConstInitial {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C] :
    colimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) ≅ ⊥_ C where
  hom :=
    colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { pt := ⊥_ C
        ι := { app := fun _ => initial.to _ } }
  inv := initial.to _

@[reassoc (attr := simp)]
/--
theorem `ι_colimitConstInitial_hom` / 定理 `ι_colimitConstInitial_hom`

English:
theorem ι_colimitConstInitial_hom
  statement: {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C]
  proof: by cat_disch

中文:
定理 ι_colimitConstInitial_hom
  结论: {J : 类型} [Category* J] {C : 类型} [Category* C] [HasInitial C]
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem ι_colimitConstInitial_hom {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C]
    {j : J} :
    colimit.ι ((CategoryTheory.Functor.const J).obj (⊥_ C)) j ≫ colimitConstInitial.hom =
      initial.to _ := by cat_disch

instance (priority := 100) initial.mono_from [HasInitial C] [InitialMonoClass C] (X : C)
    (f : ⊥_ C ⟶ X) : Mono f :=
  initialIsInitial.mono_from f

/--
theorem `InitialMonoClass.of_initial` / 定理 `InitialMonoClass.of_initial`

English:
theorem InitialMonoClass.of_initial
  given: [HasInitial C] (h : forall X : C, Mono (initial.to X))
  proof: InitialMonoClass.of_isInitial initialIsInitial h

中文:
定理 InitialMonoClass.of_initial
  条件: [HasInitial C] (h : 对任意 X : C, Mono (initial.to X))
  证明: InitialMonoClass.of_isInitial initialIsInitial h

Depends on / 依赖: InitialMonoClass, InitialMonoClass.of_isInitial, P.le_shift, initialIsInitial, le_shift, mapIso, of_isInitial, shiftFunctor
-/
theorem InitialMonoClass.of_initial [HasInitial C] (h : forall X : C, Mono (initial.to X)) :
    InitialMonoClass C :=
  InitialMonoClass.of_isInitial initialIsInitial h

/--
theorem `InitialMonoClass.of_terminal` / 定理 `InitialMonoClass.of_terminal`

English:
theorem InitialMonoClass.of_terminal
  given: [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C)))
  proof: InitialMonoClass.of_isTerminal initialIsInitial terminalIsTerminal h

中文:
定理 InitialMonoClass.of_terminal
  条件: [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C)))
  证明: InitialMonoClass.of_isTerminal initialIsInitial terminalIsTerminal h

Depends on / 依赖: InitialMonoClass, InitialMonoClass.of_isTerminal, P.le_shift, Q.le_shift, initialIsInitial, le_shift, of_isTerminal, terminalIsTerminal
-/
theorem InitialMonoClass.of_terminal [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C))) :
    InitialMonoClass C :=
  InitialMonoClass.of_isTerminal initialIsInitial terminalIsTerminal h

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/--
Definition of `terminalComparison` / `terminalComparison` 的定义

English:
definition terminalComparison
  signature: [HasTerminal C] [HasTerminal D]
  body: terminal.from _

中文:
定义 terminalComparison
  签名: [HasTerminal C] [HasTerminal D]
  定义体: terminal.from _

Depends on / 依赖: terminal, terminal.from
-/
def terminalComparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D :=
  terminal.from _

-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.
/--
Definition of `initialComparison` / `initialComparison` 的定义

English:
definition initialComparison
  signature: [HasInitial C] [HasInitial D]
  body: initial.to _

中文:
定义 initialComparison
  签名: [HasInitial C] [HasInitial D]
  定义体: initial.to _

Depends on / 依赖: initial, initial.to
-/
def initialComparison [HasInitial C] [HasInitial D] : ⊥_ D ⟶ G.obj (⊥_ C) :=
  initial.to _

end Comparison

variable {J : Type u} [Category.{v} J]

/--
Instance `hasLimit_of_domain_hasInitial` / 实例 `hasLimit_of_domain_hasInitial`

English:
instance hasLimit_of_domain_hasInitial
  signature: [HasInitial J] {F : J ⥤ C}
  body: HasLimit.mk { cone := _, isLimit := limitOfDiagramInitial (initialIsInitial) F }

中文:
实例 hasLimit_of_domain_hasInitial
  签名: [HasInitial J] {F : J ⥤ C}
  定义体: HasLimit.mk { cone := _, isLimit := limitOfDiagramInitial (initialIsInitial) F }

Depends on / 依赖: HasLimit, HasLimit.mk, initialIsInitial, isLimit, limitOfDiagramInitial
-/
instance hasLimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C} : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramInitial (initialIsInitial) F }

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/--
Definition of `limitOfInitial` / `limitOfInitial` 的定义

English:
abbreviation limitOfInitial
  signature: (F : J ⥤ C) [HasInitial J]
  body: IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)

中文:
缩写 limitOfInitial
  签名: (F : J ⥤ C) [HasInitial J]
  定义体: IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, initialIsInitial, isLimit, limit.isLimit, limitOfDiagramInitial
-/
abbrev limitOfInitial (F : J ⥤ C) [HasInitial J] : limit F ≅ F.obj (⊥_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)

/--
Instance `hasLimit_of_domain_hasTerminal` / 实例 `hasLimit_of_domain_hasTerminal`

English:
instance hasLimit_of_domain_hasTerminal
  signature: [HasTerminal J] {F : J ⥤ C}
  body: HasLimit.mk { cone := _, isLimit := limitOfDiagramTerminal (terminalIsTerminal) F }

中文:
实例 hasLimit_of_domain_hasTerminal
  签名: [HasTerminal J] {F : J ⥤ C}
  定义体: HasLimit.mk { cone := _, isLimit := limitOfDiagramTerminal (terminalIsTerminal) F }

Depends on / 依赖: HasLimit, HasLimit.mk, isLimit, limitOfDiagramTerminal, terminalIsTerminal
-/
instance hasLimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C}
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramTerminal (terminalIsTerminal) F }

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/--
Definition of `limitOfTerminal` / `limitOfTerminal` 的定义

English:
abbreviation limitOfTerminal
  signature: (F : J ⥤ C) [HasTerminal J] [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  body: IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)

中文:
缩写 limitOfTerminal
  签名: (F : J ⥤ C) [HasTerminal J] [对任意 (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  定义体: IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit, limitOfDiagramTerminal, terminalIsTerminal
-/
abbrev limitOfTerminal (F : J ⥤ C) [HasTerminal J] [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    limit F ≅ F.obj (⊤_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)

/--
Instance `hasColimit_of_domain_hasTerminal` / 实例 `hasColimit_of_domain_hasTerminal`

English:
instance hasColimit_of_domain_hasTerminal
  signature: [HasTerminal J] {F : J ⥤ C}
  body: HasColimit.mk { cocone := _, isColimit := colimitOfDiagramTerminal (terminalIsTerminal) F }

中文:
实例 hasColimit_of_domain_hasTerminal
  签名: [HasTerminal J] {F : J ⥤ C}
  定义体: HasColimit.mk { cocone := _, isColimit := colimitOfDiagramTerminal (terminalIsTerminal) F }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimitOfDiagramTerminal, isColimit, terminalIsTerminal
-/
instance hasColimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C} : HasColimit F :=
  HasColimit.mk { cocone := _, isColimit := colimitOfDiagramTerminal (terminalIsTerminal) F }

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/--
Definition of `colimitOfTerminal` / `colimitOfTerminal` 的定义

English:
abbreviation colimitOfTerminal
  signature: (F : J ⥤ C) [HasTerminal J]
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal terminalIsTerminal F)

中文:
缩写 colimitOfTerminal
  签名: (F : J ⥤ C) [HasTerminal J]
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal terminalIsTerminal F)

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitOfDiagramTerminal, isColimit, terminalIsTerminal
-/
abbrev colimitOfTerminal (F : J ⥤ C) [HasTerminal J] : colimit F ≅ F.obj (⊤_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal terminalIsTerminal F)

/--
Instance `hasColimit_of_domain_hasInitial` / 实例 `hasColimit_of_domain_hasInitial`

English:
instance hasColimit_of_domain_hasInitial
  signature: [HasInitial J] {F : J ⥤ C}
  body: HasColimit.mk { cocone := _, isColimit := colimitOfDiagramInitial (initialIsInitial) F }

中文:
实例 hasColimit_of_domain_hasInitial
  签名: [HasInitial J] {F : J ⥤ C}
  定义体: HasColimit.mk { cocone := _, isColimit := colimitOfDiagramInitial (initialIsInitial) F }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimitOfDiagramInitial, initialIsInitial, isColimit
-/
instance hasColimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C}
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasColimit F :=
  HasColimit.mk { cocone := _, isColimit := colimitOfDiagramInitial (initialIsInitial) F }

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/--
Definition of `colimitOfInitial` / `colimitOfInitial` 的定义

English:
abbreviation colimitOfInitial
  signature: (F : J ⥤ C) [HasInitial J] [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramInitial initialIsInitial _)

中文:
缩写 colimitOfInitial
  签名: (F : J ⥤ C) [HasInitial J] [对任意 (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramInitial initialIsInitial _)

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitOfDiagramInitial, initialIsInitial, isColimit
-/
abbrev colimitOfInitial (F : J ⥤ C) [HasInitial J] [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    colimit F ≅ F.obj (⊥_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramInitial initialIsInitial _)

/--
theorem `isIso_π_of_isInitial` / 定理 `isIso_π_of_isInitial`

English:
theorem isIso_π_of_isInitial
  given: {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F]
  proof: ⟨⟨limit.lift _ (coneOfDiagramInitial I F), ⟨by ext; simp, by simp⟩⟩⟩

中文:
定理 isIso_π_of_isInitial
  条件: {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F]
  证明: ⟨⟨limit.lift _ (coneOfDiagramInitial I F), ⟨by ext; simp, by simp⟩⟩⟩

Depends on / 依赖: coneOfDiagramInitial, limit.lift
-/
theorem isIso_π_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F] :
    IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramInitial I F), ⟨by ext; simp, by simp⟩⟩⟩

/--
Instance `isIso_π_initial` / 实例 `isIso_π_initial`

English:
instance isIso_π_initial
  signature: [HasInitial J] (F : J ⥤ C)
  body: isIso_π_of_isInitial initialIsInitial F

中文:
实例 isIso_π_initial
  签名: [HasInitial J] (F : J ⥤ C)
  定义体: isIso_π_of_isInitial initialIsInitial F

Depends on / 依赖: initialIsInitial
-/
instance isIso_π_initial [HasInitial J] (F : J ⥤ C) : IsIso (limit.π F (⊥_ J)) :=
  isIso_π_of_isInitial initialIsInitial F

/--
theorem `isIso_π_of_isTerminal` / 定理 `isIso_π_of_isTerminal`

English:
theorem isIso_π_of_isTerminal
  statement: {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
  proof: ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by ext; simp, by simp⟩⟩

中文:
定理 isIso_π_of_isTerminal
  结论: {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
  证明: ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by ext; simp, by simp⟩⟩

Depends on / 依赖: coneOfDiagramTerminal, limit.lift, mapIso, shiftFunctor, shiftFunctorAdd, symm.app
-/
theorem isIso_π_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by ext; simp, by simp⟩⟩

/--
Instance `isIso_π_terminal` / 实例 `isIso_π_terminal`

English:
instance isIso_π_terminal
  signature: [HasTerminal J] (F : J ⥤ C) [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  body: isIso_π_of_isTerminal terminalIsTerminal F

中文:
实例 isIso_π_terminal
  签名: [HasTerminal J] (F : J ⥤ C) [对任意 (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  定义体: isIso_π_of_isTerminal terminalIsTerminal F

Depends on / 依赖: terminalIsTerminal
-/
instance isIso_π_terminal [HasTerminal J] (F : J ⥤ C) [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (limit.π F (⊤_ J)) :=
  isIso_π_of_isTerminal terminalIsTerminal F

/--
theorem `isIso_ι_of_isTerminal` / 定理 `isIso_ι_of_isTerminal`

English:
theorem isIso_ι_of_isTerminal
  given: {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F]
  proof: ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F), ⟨by simp, by ext; simp⟩⟩⟩

中文:
定理 isIso_ι_of_isTerminal
  条件: {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F]
  证明: ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F), ⟨by simp, by ext; simp⟩⟩⟩

Depends on / 依赖: coconeOfDiagramTerminal, colimit, colimit.desc
-/
theorem isIso_ι_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F), ⟨by simp, by ext; simp⟩⟩⟩

/--
Instance `isIso_ι_terminal` / 实例 `isIso_ι_terminal`

English:
instance isIso_ι_terminal
  signature: [HasTerminal J] (F : J ⥤ C)
  body: isIso_ι_of_isTerminal terminalIsTerminal F

中文:
实例 isIso_ι_terminal
  签名: [HasTerminal J] (F : J ⥤ C)
  定义体: isIso_ι_of_isTerminal terminalIsTerminal F

Depends on / 依赖: terminalIsTerminal
-/
instance isIso_ι_terminal [HasTerminal J] (F : J ⥤ C) : IsIso (colimit.ι F (⊤_ J)) :=
  isIso_ι_of_isTerminal terminalIsTerminal F

/--
theorem `isIso_ι_of_isInitial` / 定理 `isIso_ι_of_isInitial`

English:
theorem isIso_ι_of_isInitial
  statement: {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
  proof: ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F), by
    refine ⟨?_, by ext; simp⟩
    simp only [colimit.ι_desc, coconeOfDiagramInitial_pt, coconeOfDiagramInitial_ι_app,
      Functor.const_obj_obj, IsInitial.to_self]
    grind
  ⟩⟩

中文:
定理 isIso_ι_of_isInitial
  结论: {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
  证明: ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F), by
    refine ⟨?_, by ext; simp⟩
    simp only [colimit.ι_desc, coconeOfDiagramInitial_pt, coconeOfDiagramInitial_ι_app,
      Functor.const_obj_obj, IsInitial.to_self]
    grind
  ⟩⟩

Depends on / 依赖: Functor, Functor.const_obj_obj, IsInitial, IsInitial.to_self, coconeOfDiagramInitial, coconeOfDiagramInitial_pt, colimit, colimit.desc, const_obj_obj, to_self
-/
theorem isIso_ι_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F), by
    refine ⟨?_, by ext; simp⟩
    simp only [colimit.ι_desc, coconeOfDiagramInitial_pt, coconeOfDiagramInitial_ι_app,
      Functor.const_obj_obj, IsInitial.to_self]
    grind
  ⟩⟩

/--
Instance `isIso_ι_initial` / 实例 `isIso_ι_initial`

English:
instance isIso_ι_initial
  signature: [HasInitial J] (F : J ⥤ C) [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  body: isIso_ι_of_isInitial initialIsInitial F

中文:
实例 isIso_ι_initial
  签名: [HasInitial J] (F : J ⥤ C) [对任意 (i j : J) (f : i ⟶ j), IsIso (F.map f)]
  定义体: isIso_ι_of_isInitial initialIsInitial F

Depends on / 依赖: initialIsInitial
-/
instance isIso_ι_initial [HasInitial J] (F : J ⥤ C) [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (colimit.ι F (⊥_ J)) :=
  isIso_ι_of_isInitial initialIsInitial F

end

end CategoryTheory.Limits
