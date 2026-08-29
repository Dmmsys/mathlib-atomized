/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally Cartesian closed category, every subobject lattice
  is Cartesian closed (equivalently, a Heyting algebra).

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

variable {C : Type u₁} [Category.{v₁} C] {A : C}

/--
Definition of `IsSubterminal` / `IsSubterminal` 的定义

English:
definition IsSubterminal
  signature: (A : C)
  body: forall ⦃Z : C⦄ (f g : Z ⟶ A), f = g

中文:
定义 IsSubterminal
  签名: (A : C)
  定义体: forall ⦃Z : C⦄ (f g : Z ⟶ A), f = g
-/
def IsSubterminal (A : C) : Prop :=
  forall ⦃Z : C⦄ (f g : Z ⟶ A), f = g

/--
theorem `IsSubterminal.def` / 定理 `IsSubterminal.def`

English:
theorem IsSubterminal.def
  statement: IsSubterminal A ↔ forall ⦃Z : C⦄ (f g : Z ⟶ A), f = g
  proof: Iff.rfl

中文:
定理 IsSubterminal.def
  结论: IsSubterminal A ↔ 对任意 ⦃Z : C⦄ (f g : Z ⟶ A), f = g
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem IsSubterminal.def : IsSubterminal A ↔ forall ⦃Z : C⦄ (f g : Z ⟶ A), f = g :=
  Iff.rfl

/--
theorem `IsSubterminal.mono_isTerminal_from` / 定理 `IsSubterminal.mono_isTerminal_from`

English:
theorem IsSubterminal.mono_isTerminal_from
  given: (hA : IsSubterminal A) {T : C} (hT : IsTerminal T)
  proof: { right_cancellation := fun _ _ _ => hA _ _ }

中文:
定理 IsSubterminal.mono_isTerminal_from
  条件: (hA : IsSubterminal A) {T : C} (hT : IsTerminal T)
  证明: { right_cancellation := fun _ _ _ => hA _ _ }

Depends on / 依赖: right_cancellation
-/
theorem IsSubterminal.mono_isTerminal_from (hA : IsSubterminal A) {T : C} (hT : IsTerminal T) :
    Mono (hT.from A) :=
  { right_cancellation := fun _ _ _ => hA _ _ }

/--
theorem `IsSubterminal.mono_terminal_from` / 定理 `IsSubterminal.mono_terminal_from`

English:
theorem IsSubterminal.mono_terminal_from
  given: [HasTerminal C] (hA : IsSubterminal A)
  proof: hA.mono_isTerminal_from terminalIsTerminal

中文:
定理 IsSubterminal.mono_terminal_from
  条件: [HasTerminal C] (hA : IsSubterminal A)
  证明: hA.mono_isTerminal_from terminalIsTerminal

Depends on / 依赖: hA.mono_isTerminal_from, mono_isTerminal_from, terminalIsTerminal
-/
theorem IsSubterminal.mono_terminal_from [HasTerminal C] (hA : IsSubterminal A) :
    Mono (terminal.from A) :=
  hA.mono_isTerminal_from terminalIsTerminal

/--
theorem `isSubterminal_of_mono_isTerminal_from` / 定理 `isSubterminal_of_mono_isTerminal_from`

English:
theorem isSubterminal_of_mono_isTerminal_from
  given: {T : C} (hT : IsTerminal T) [Mono (hT.from A)]
  proof: fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

中文:
定理 isSubterminal_of_mono_isTerminal_from
  条件: {T : C} (hT : IsTerminal T) [Mono (hT.from A)]
  证明: fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

Depends on / 依赖: cancel_mono, hT.from, hT.hom_ext, hom_ext
-/
theorem isSubterminal_of_mono_isTerminal_from {T : C} (hT : IsTerminal T) [Mono (hT.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

/--
theorem `isSubterminal_of_mono_terminal_from` / 定理 `isSubterminal_of_mono_terminal_from`

English:
theorem isSubterminal_of_mono_terminal_from
  given: [HasTerminal C] [Mono (terminal.from A)]
  proof: fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  subsingleton

中文:
定理 isSubterminal_of_mono_terminal_from
  条件: [HasTerminal C] [Mono (terminal.from A)]
  证明: fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  subsingleton

Depends on / 依赖: cancel_mono, subsingleton, terminal, terminal.from
-/
theorem isSubterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  subsingleton

/--
theorem `isSubterminal_of_isTerminal` / 定理 `isSubterminal_of_isTerminal`

English:
theorem isSubterminal_of_isTerminal
  given: {T : C} (hT : IsTerminal T)
  statement: IsSubterminal T
  proof: fun _ _ _ =>
  hT.hom_ext _ _

中文:
定理 isSubterminal_of_isTerminal
  条件: {T : C} (hT : IsTerminal T)
  结论: IsSubterminal T
  证明: fun _ _ _ =>
  hT.hom_ext _ _
-/
theorem isSubterminal_of_isTerminal {T : C} (hT : IsTerminal T) : IsSubterminal T := fun _ _ _ =>
  hT.hom_ext _ _

/--
theorem `isSubterminal_of_terminal` / 定理 `isSubterminal_of_terminal`

English:
theorem isSubterminal_of_terminal
  given: [HasTerminal C]
  statement: IsSubterminal (⊤_ C)
  proof: fun _ _ _ => by
  subsingleton

中文:
定理 isSubterminal_of_terminal
  条件: [HasTerminal C]
  结论: IsSubterminal (⊤_ C)
  证明: fun _ _ _ => by
  subsingleton

Depends on / 依赖: subsingleton
-/
theorem isSubterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C) := fun _ _ _ => by
  subsingleton

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsSubterminal.isIso_diag` / 定理 `IsSubterminal.isIso_diag`

English:
theorem IsSubterminal.isIso_diag
  given: (hA : IsSubterminal A) [HasBinaryProduct A A]
  statement: IsIso (diag A)
  proof: ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        cat_disch⟩⟩⟩

中文:
定理 IsSubterminal.isIso_diag
  条件: (hA : IsSubterminal A) [HasBinaryProduct A A]
  结论: IsIso (diag A)
  证明: ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        cat_disch⟩⟩⟩

Depends on / 依赖: IsSubterminal, IsSubterminal.def, Limits, Limits.prod.fst, cat_disch
-/
theorem IsSubterminal.isIso_diag (hA : IsSubterminal A) [HasBinaryProduct A A] : IsIso (diag A) :=
  ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        cat_disch⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSubterminal_of_isIso_diag` / 定理 `isSubterminal_of_isIso_diag`

English:
theorem isSubterminal_of_isIso_diag
  given: [HasBinaryProduct A A] [IsIso (diag A)]
  statement: IsSubterminal A
  proof: fun Z f g => by
  have : (Limits.prod.fst : A ⨯ A ⟶ _) = Limits.prod.snd := by simp [← cancel_epi (diag A)]
  rw [← prod.lift_fst f g]; rw [this]; rw [prod.lift_snd]

中文:
定理 isSubterminal_of_isIso_diag
  条件: [HasBinaryProduct A A] [IsIso (diag A)]
  结论: IsSubterminal A
  证明: fun Z f g => by
  have : (Limits.prod.fst : A ⨯ A ⟶ _) = Limits.prod.snd := by simp [← cancel_epi (diag A)]
  rw [← prod.lift_fst f g]; rw [this]; rw [prod.lift_snd]

Depends on / 依赖: Limits, Limits.prod.fst, Limits.prod.snd, cancel_epi, lift_fst, lift_snd, prod.lift_fst, prod.lift_snd
-/
theorem isSubterminal_of_isIso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSubterminal A :=
  fun Z f g => by
  have : (Limits.prod.fst : A ⨯ A ⟶ _) = Limits.prod.snd := by simp [← cancel_epi (diag A)]
  rw [← prod.lift_fst f g]; rw [this]; rw [prod.lift_snd]

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps!]
/--
Definition of `IsSubterminal.isoDiag` / `IsSubterminal.isoDiag` 的定义

English:
definition IsSubterminal.isoDiag
  signature: (hA : IsSubterminal A) [HasBinaryProduct A A]
  body: by
  letI := IsSubterminal.isIso_diag hA
  apply (asIso (diag A)).symm

中文:
定义 IsSubterminal.isoDiag
  签名: (hA : IsSubterminal A) [HasBinaryProduct A A]
  定义体: by
  letI := IsSubterminal.isIso_diag hA
  apply (asIso (diag A)).symm

Depends on / 依赖: IsSubterminal, IsSubterminal.isIso_diag, isIso_diag
-/
def IsSubterminal.isoDiag (hA : IsSubterminal A) [HasBinaryProduct A A] : A ⨯ A ≅ A := by
  letI := IsSubterminal.isIso_diag hA
  apply (asIso (diag A)).symm

variable (C)

/--
Definition of `Subterminals` / `Subterminals` 的定义

English:
definition Subterminals
  signature: (C : Type u₁) [Category.{v₁} C]
  body: ObjectProperty.FullSubcategory fun A : C => IsSubterminal A

中文:
定义 Subterminals
  签名: (C : 类型u₁) [Category.{v₁} C]
  定义体: ObjectProperty.FullSubcategory fun A : C => IsSubterminal A

Depends on / 依赖: FullSubcategory, IsSubterminal, ObjectProperty, ObjectProperty.FullSubcategory
-/
def Subterminals (C : Type u₁) [Category.{v₁} C] :=
  ObjectProperty.FullSubcategory fun A : C => IsSubterminal A

instance (C : Type u₁) [Category.{v₁} C] : Category (Subterminals C) :=
  ObjectProperty.FullSubcategory.category _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasTerminal
  signature: C] : Inhabited (Subterminals C)
  body: ⟨⟨⊤_ C, isSubterminal_of_terminal⟩⟩

中文:
实例 [HasTerminal
  签名: C] : Inhabited (Subterminals C)
  定义体: ⟨⟨⊤_ C, isSubterminal_of_terminal⟩⟩

Depends on / 依赖: isSubterminal_of_terminal
-/
instance [HasTerminal C] : Inhabited (Subterminals C) :=
  ⟨⟨⊤_ C, isSubterminal_of_terminal⟩⟩

/-- The inclusion of the subterminal objects into the original category. -/
@[simps!]
/--
Definition of `subterminalInclusion` / `subterminalInclusion` 的定义

English:
definition subterminalInclusion
  signature: : Subterminals C ⥤ C
  body: ObjectProperty.ι _

中文:
定义 subterminalInclusion
  签名: : Subterminals C ⥤ C
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
def subterminalInclusion : Subterminals C ⥤ C :=
  ObjectProperty.ι _

instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Full :=
  ObjectProperty.full_ι _

instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Faithful :=
  ObjectProperty.faithful_ι _

/--
Instance `subterminals_thin` / 实例 `subterminals_thin`

English:
instance subterminals_thin
  signature: (X Y : Subterminals C)
  body: ObjectProperty.hom_ext _ (Y.2 _ _)

中文:
实例 subterminals_thin
  签名: (X Y : Subterminals C)
  定义体: ObjectProperty.hom_ext _ (Y.2 _ _)

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, hom_ext
-/
instance subterminals_thin (X Y : Subterminals C) : Subsingleton (X ⟶ Y) where
  allEq _ _ := ObjectProperty.hom_ext _ (Y.2 _ _)

/--
The category of subterminal objects is equivalent to the category of monomorphisms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
@[simps]
/--
Definition of `subterminalsEquivMonoOverTerminal` / `subterminalsEquivMonoOverTerminal` 的定义

English:
definition subterminalsEquivMonoOverTerminal
  signature: [HasTerminal C]
  body: { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩
      map := fun f => MonoOver.homMk f.hom (by ext1 ⟨⟨⟩⟩) }
  inverse :=
    { obj := fun X =>
        ⟨X.obj.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          subsingleton⟩
      map := fun f => ObjectPropert

中文:
定义 subterminalsEquivMonoOverTerminal
  签名: [HasTerminal C]
  定义体: { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩
      map := fun f => MonoOver.homMk f.hom (by ext1 ⟨⟨⟩⟩) }
  inverse :=
    { obj := fun X =>
        ⟨X.obj.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          subsingleton⟩
      map := fun f => ObjectPropert

Depends on / 依赖: Iso.refl, MonoOver, MonoOver.homMk, MonoOver.isoMk, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.homMk, Over.mk, X.arrow, X.obj.left, cancel_mono, counitIso, f.hom, functor_unitIso_comp, inverse, mono_terminal_from, ofComponents, subsingleton, terminal
-/
def subterminalsEquivMonoOverTerminal [HasTerminal C] : Subterminals C ≌ MonoOver (⊤_ C) where
  functor :=
    { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩
      map := fun f => MonoOver.homMk f.hom (by ext1 ⟨⟨⟩⟩) }
  inverse :=
    { obj := fun X =>
        ⟨X.obj.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          subsingleton⟩
      map := fun f => ObjectProperty.homMk f.hom.1 }
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by subsingleton)
  counitIso := NatIso.ofComponents (fun X => MonoOver.isoMk (Iso.refl _)) (by subsingleton)
  functor_unitIso_comp := by subsingleton

@[simp]
/--
theorem `subterminals_to_monoOver_terminal_comp_forget` / 定理 `subterminals_to_monoOver_terminal_comp_forget`

English:
theorem subterminals_to_monoOver_terminal_comp_forget
  given: [HasTerminal C]
  proof: rfl

@[simp]

中文:
定理 subterminals_to_monoOver_terminal_comp_forget
  条件: [HasTerminal C]
  证明: rfl

@[simp]
-/
theorem subterminals_to_monoOver_terminal_comp_forget [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).functor ⋙ MonoOver.forget _ ⋙ Over.forget _ =
      subterminalInclusion C :=
  rfl

@[simp]
/--
theorem `monoOver_terminal_to_subterminals_comp` / 定理 `monoOver_terminal_to_subterminals_comp`

English:
theorem monoOver_terminal_to_subterminals_comp
  given: [HasTerminal C]
  proof: rfl

中文:
定理 monoOver_terminal_to_subterminals_comp
  条件: [HasTerminal C]
  证明: rfl
-/
theorem monoOver_terminal_to_subterminals_comp [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).inverse ⋙ subterminalInclusion C =
      MonoOver.forget _ ⋙ Over.forget _ :=
  rfl

end CategoryTheory
