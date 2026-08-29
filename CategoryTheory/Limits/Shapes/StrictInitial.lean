/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, i.e. given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`hasStrictInitialObjects_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `TopCat`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show Cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/

@[expose] public section


universe v u

namespace CategoryTheory

namespace Limits

open Category

variable (C : Type u) [Category.{v} C]

section StrictInitial

/--
Definition of `HasStrictInitialObjects` / `HasStrictInitialObjects` 的定义

English:
class HasStrictInitialObjects
  parameters: : Prop where
  axioms and operations (1):
    - out : forall {I A : C} (f : A ⟶ I), IsInitial I -> IsIso f

中文:
类 HasStrictInitialObjects
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 对任意 {I A : C} (f : A ⟶ I), IsInitial I -> IsIso f
-/
class HasStrictInitialObjects : Prop where
  out : forall {I A : C} (f : A ⟶ I), IsInitial I -> IsIso f

variable {C}

section

variable [HasStrictInitialObjects C] {I : C}

/--
theorem `IsInitial.isIso_to` / 定理 `IsInitial.isIso_to`

English:
theorem IsInitial.isIso_to
  given: (hI : IsInitial I) {A : C} (f : A ⟶ I)
  statement: IsIso f
  proof: HasStrictInitialObjects.out f hI

中文:
定理 IsInitial.isIso_to
  条件: (hI : IsInitial I) {A : C} (f : A ⟶ I)
  结论: IsIso f
  证明: HasStrictInitialObjects.out f hI

Depends on / 依赖: HasStrictInitialObjects, HasStrictInitialObjects.out
-/
theorem IsInitial.isIso_to (hI : IsInitial I) {A : C} (f : A ⟶ I) : IsIso f :=
  HasStrictInitialObjects.out f hI

/--
theorem `IsInitial.strict_hom_ext` / 定理 `IsInitial.strict_hom_ext`

English:
theorem IsInitial.strict_hom_ext
  given: (hI : IsInitial I) {A : C} (f g : A ⟶ I)
  statement: f = g
  proof: by
  have := hI.isIso_to f
  have := hI.isIso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

中文:
定理 IsInitial.strict_hom_ext
  条件: (hI : IsInitial I) {A : C} (f g : A ⟶ I)
  结论: f = g
  证明: by
  have := hI.isIso_to f
  have := hI.isIso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

Depends on / 依赖: eq_of_inv_eq_inv, hI.hom_ext, hI.isIso_to, hom_ext, isIso_to
-/
theorem IsInitial.strict_hom_ext (hI : IsInitial I) {A : C} (f g : A ⟶ I) : f = g := by
  have := hI.isIso_to f
  have := hI.isIso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

/--
theorem `IsInitial.subsingleton_to` / 定理 `IsInitial.subsingleton_to`

English:
theorem IsInitial.subsingleton_to
  given: (hI : IsInitial I) {A : C}
  statement: Subsingleton (A ⟶ I)
  proof: ⟨hI.strict_hom_ext⟩

中文:
定理 IsInitial.subsingleton_to
  条件: (hI : IsInitial I) {A : C}
  结论: Subsingleton (A ⟶ I)
  证明: ⟨hI.strict_hom_ext⟩

Depends on / 依赖: P.arbitrary, P.prop_arbitrary, arbitrary, hI.strict_hom_ext, prop_arbitrary, strict_hom_ext
-/
theorem IsInitial.subsingleton_to (hI : IsInitial I) {A : C} : Subsingleton (A ⟶ I) :=
  ⟨hI.strict_hom_ext⟩

/-- If `X ⟶ Y` with `Y` being a strict initial object, then `X` is also an initial object. -/
noncomputable
/--
Definition of `IsInitial.ofStrict` / `IsInitial.ofStrict` 的定义

English:
definition IsInitial.ofStrict
  signature: {X Y : C} (f : X ⟶ Y)
  body: letI := hY.isIso_to f
  hY.ofIso (asIso f).symm

中文:
定义 IsInitial.ofStrict
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: letI := hY.isIso_to f
  hY.ofIso (asIso f).symm

Depends on / 依赖: P.arbitrary.unop, P.prop_arbitrary, arbitrary, hY.isIso_to, hY.ofIso, isIso_to, prop_arbitrary
-/
def IsInitial.ofStrict {X Y : C} (f : X ⟶ Y)
    (hY : IsInitial Y) : IsInitial X :=
  letI := hY.isIso_to f
  hY.ofIso (asIso f).symm

instance (priority := 100) initial_mono_of_strict_initial_objects : InitialMonoClass C where
  isInitial_mono_from := fun _ hI => { right_cancellation := fun _ _ _ => hI.strict_hom_ext _ _ }

/-- If `I` is initial, then `X ⨯ I` is isomorphic to it. -/
@[simps! hom]
/--
Definition of `mulIsInitial` / `mulIsInitial` 的定义

English:
definition mulIsInitial
  signature: (X : C) [HasBinaryProduct X I] (hI : IsInitial I)
  body: by
  have := hI.isIso_to (prod.snd : X ⨯ I ⟶ I)
  exact asIso prod.snd

@[simp]

中文:
定义 mulIsInitial
  签名: (X : C) [HasBinaryProduct X I] (hI : IsInitial I)
  定义体: by
  have := hI.isIso_to (prod.snd : X ⨯ I ⟶ I)
  exact asIso prod.snd

@[simp]

Depends on / 依赖: hI.isIso_to, isIso_to, prod.snd
-/
noncomputable def mulIsInitial (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : X ⨯ I ≅ I := by
  have := hI.isIso_to (prod.snd : X ⨯ I ⟶ I)
  exact asIso prod.snd

@[simp]
/--
theorem `mulIsInitial_inv` / 定理 `mulIsInitial_inv`

English:
theorem mulIsInitial_inv
  given: (X : C) [HasBinaryProduct X I] (hI : IsInitial I)
  proof: hI.hom_ext _ _

中文:
定理 mulIsInitial_inv
  条件: (X : C) [HasBinaryProduct X I] (hI : IsInitial I)
  证明: hI.hom_ext _ _

Depends on / 依赖: hI.hom_ext, hom_ext
-/
theorem mulIsInitial_inv (X : C) [HasBinaryProduct X I] (hI : IsInitial I) :
    (mulIsInitial X hI).inv = hI.to _ :=
  hI.hom_ext _ _

/-- If `I` is initial, then `I ⨯ X` is isomorphic to it. -/
@[simps! hom]
/--
Definition of `isInitialMul` / `isInitialMul` 的定义

English:
definition isInitialMul
  signature: (X : C) [HasBinaryProduct I X] (hI : IsInitial I)
  body: by
  have := hI.isIso_to (prod.fst : I ⨯ X ⟶ I)
  exact asIso prod.fst

@[simp]

中文:
定义 isInitialMul
  签名: (X : C) [HasBinaryProduct I X] (hI : IsInitial I)
  定义体: by
  have := hI.isIso_to (prod.fst : I ⨯ X ⟶ I)
  exact asIso prod.fst

@[simp]

Depends on / 依赖: hI.isIso_to, isIso_to, prod.fst
-/
noncomputable def isInitialMul (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : I ⨯ X ≅ I := by
  have := hI.isIso_to (prod.fst : I ⨯ X ⟶ I)
  exact asIso prod.fst

@[simp]
/--
theorem `isInitialMul_inv` / 定理 `isInitialMul_inv`

English:
theorem isInitialMul_inv
  given: (X : C) [HasBinaryProduct I X] (hI : IsInitial I)
  proof: hI.hom_ext _ _

中文:
定理 isInitialMul_inv
  条件: (X : C) [HasBinaryProduct I X] (hI : IsInitial I)
  证明: hI.hom_ext _ _

Depends on / 依赖: hI.hom_ext, hom_ext
-/
theorem isInitialMul_inv (X : C) [HasBinaryProduct I X] (hI : IsInitial I) :
    (isInitialMul X hI).inv = hI.to _ :=
  hI.hom_ext _ _

variable [HasInitial C]

/--
Instance `initial_isIso_to` / 实例 `initial_isIso_to`

English:
instance initial_isIso_to
  signature: {A : C} (f : A ⟶ ⊥_ C)
  body: initialIsInitial.isIso_to _

@[ext]

中文:
实例 initial_isIso_to
  签名: {A : C} (f : A ⟶ ⊥_ C)
  定义体: initialIsInitial.isIso_to _

@[ext]

Depends on / 依赖: initialIsInitial, initialIsInitial.isIso_to, isIso_to
-/
instance initial_isIso_to {A : C} (f : A ⟶ ⊥_ C) : IsIso f :=
  initialIsInitial.isIso_to _

@[ext]
/--
theorem `initial.strict_hom_ext` / 定理 `initial.strict_hom_ext`

English:
theorem initial.strict_hom_ext
  given: {A : C} (f g : A ⟶ ⊥_ C)
  statement: f = g
  proof: initialIsInitial.strict_hom_ext _ _

中文:
定理 initial.strict_hom_ext
  条件: {A : C} (f g : A ⟶ ⊥_ C)
  结论: f = g
  证明: initialIsInitial.strict_hom_ext _ _

Depends on / 依赖: initialIsInitial, initialIsInitial.strict_hom_ext, strict_hom_ext
-/
theorem initial.strict_hom_ext {A : C} (f g : A ⟶ ⊥_ C) : f = g :=
  initialIsInitial.strict_hom_ext _ _

/--
theorem `initial.subsingleton_to` / 定理 `initial.subsingleton_to`

English:
theorem initial.subsingleton_to
  given: {A : C}
  statement: Subsingleton (A ⟶ ⊥_ C)
  proof: initialIsInitial.subsingleton_to

中文:
定理 initial.subsingleton_to
  条件: {A : C}
  结论: Subsingleton (A ⟶ ⊥_ C)
  证明: initialIsInitial.subsingleton_to

Depends on / 依赖: initialIsInitial, initialIsInitial.subsingleton_to, subsingleton_to
-/
theorem initial.subsingleton_to {A : C} : Subsingleton (A ⟶ ⊥_ C) :=
  initialIsInitial.subsingleton_to

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `X × Empty ≃ Empty` for types (or `n * 0 = 0`).
-/
@[simps! hom]
/--
Definition of `mulInitial` / `mulInitial` 的定义

English:
definition mulInitial
  signature: (X : C) [HasBinaryProduct X (⊥_ C)]
  body: mulIsInitial _ initialIsInitial

@[simp]

中文:
定义 mulInitial
  签名: (X : C) [HasBinaryProduct X (⊥_ C)]
  定义体: mulIsInitial _ initialIsInitial

@[simp]

Depends on / 依赖: initialIsInitial, mulIsInitial
-/
noncomputable def mulInitial (X : C) [HasBinaryProduct X (⊥_ C)] : X ⨯ ⊥_ C ≅ ⊥_ C :=
  mulIsInitial _ initialIsInitial

@[simp]
/--
theorem `mulInitial_inv` / 定理 `mulInitial_inv`

English:
theorem mulInitial_inv
  given: (X : C) [HasBinaryProduct X (⊥_ C)]
  statement: (mulInitial X).inv = initial.to _
  proof: Subsingleton.elim _ _

中文:
定理 mulInitial_inv
  条件: (X : C) [HasBinaryProduct X (⊥_ C)]
  结论: (mulInitial X).inv = initial.to _
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem mulInitial_inv (X : C) [HasBinaryProduct X (⊥_ C)] : (mulInitial X).inv = initial.to _ :=
  Subsingleton.elim _ _

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `Empty × X ≃ Empty` for types (or `0 * n = 0`).
-/
@[simps! hom]
/--
Definition of `initialMul` / `initialMul` 的定义

English:
definition initialMul
  signature: (X : C) [HasBinaryProduct (⊥_ C) X]
  body: isInitialMul _ initialIsInitial

@[simp]

中文:
定义 initialMul
  签名: (X : C) [HasBinaryProduct (⊥_ C) X]
  定义体: isInitialMul _ initialIsInitial

@[simp]

Depends on / 依赖: initialIsInitial, isInitialMul
-/
noncomputable def initialMul (X : C) [HasBinaryProduct (⊥_ C) X] : (⊥_ C) ⨯ X ≅ ⊥_ C :=
  isInitialMul _ initialIsInitial

@[simp]
/--
theorem `initialMul_inv` / 定理 `initialMul_inv`

English:
theorem initialMul_inv
  given: (X : C) [HasBinaryProduct (⊥_ C) X]
  statement: (initialMul X).inv = initial.to _
  proof: Subsingleton.elim _ _

中文:
定理 initialMul_inv
  条件: (X : C) [HasBinaryProduct (⊥_ C) X]
  结论: (initialMul X).inv = initial.to _
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem initialMul_inv (X : C) [HasBinaryProduct (⊥_ C) X] : (initialMul X).inv = initial.to _ :=
  Subsingleton.elim _ _

end

/--
theorem `hasStrictInitialObjects_of_initial_is_strict` / 定理 `hasStrictInitialObjects_of_initial_is_strict`

English:
theorem hasStrictInitialObjects_of_initial_is_strict
  statement: [HasInitial C]
  proof: { out := fun {I A} f hI =>
      haveI := h A (f ≫ hI.to _)
      ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by rw [← assoc, IsIso.hom_inv_id], hI.hom_ext _ _⟩⟩ }

中文:
定理 hasStrictInitialObjects_of_initial_is_strict
  结论: [HasInitial C]
  证明: { out := fun {I A} f hI =>
      haveI := h A (f ≫ hI.to _)
      ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by rw [← assoc, IsIso.hom_inv_id], hI.hom_ext _ _⟩⟩ }

Depends on / 依赖: IsIso.hom_inv_id, hI.hom_ext, hI.to, hom_ext, hom_inv_id
-/
theorem hasStrictInitialObjects_of_initial_is_strict [HasInitial C]
    (h : forall (A) (f : A ⟶ ⊥_ C), IsIso f) : HasStrictInitialObjects C :=
  { out := fun {I A} f hI =>
      haveI := h A (f ≫ hI.to _)
      ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by rw [← assoc, IsIso.hom_inv_id], hI.hom_ext _ _⟩⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Quiver.IsThin
  signature: C] : HasStrictInitialObjects C where
  body: by
    rw [isIso_iff_of_thin]
    exact ⟨hI.to _⟩

中文:
实例 [Quiver.IsThin
  签名: C] : HasStrictInitialObjects C where
  定义体: by
    rw [isIso_iff_of_thin]
    exact ⟨hI.to _⟩

Depends on / 依赖: hI.to, isIso_iff_of_thin
-/
instance [Quiver.IsThin C] : HasStrictInitialObjects C where
  out {I A} f hI := by
    rw [isIso_iff_of_thin]
    exact ⟨hI.to _⟩

end StrictInitial

section StrictTerminal

/--
Definition of `HasStrictTerminalObjects` / `HasStrictTerminalObjects` 的定义

English:
class HasStrictTerminalObjects
  parameters: : Prop where
  axioms and operations (1):
    - out : forall {I A : C} (f : I ⟶ A), IsTerminal I -> IsIso f

中文:
类 HasStrictTerminalObjects
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 对任意 {I A : C} (f : I ⟶ A), IsTerminal I -> IsIso f
-/
class HasStrictTerminalObjects : Prop where
  out : forall {I A : C} (f : I ⟶ A), IsTerminal I -> IsIso f

variable {C}

section

variable [HasStrictTerminalObjects C] {I : C}

/--
theorem `IsTerminal.isIso_from` / 定理 `IsTerminal.isIso_from`

English:
theorem IsTerminal.isIso_from
  given: (hI : IsTerminal I) {A : C} (f : I ⟶ A)
  statement: IsIso f
  proof: HasStrictTerminalObjects.out f hI

中文:
定理 IsTerminal.isIso_from
  条件: (hI : IsTerminal I) {A : C} (f : I ⟶ A)
  结论: IsIso f
  证明: HasStrictTerminalObjects.out f hI

Depends on / 依赖: HasStrictTerminalObjects, HasStrictTerminalObjects.out
-/
theorem IsTerminal.isIso_from (hI : IsTerminal I) {A : C} (f : I ⟶ A) : IsIso f :=
  HasStrictTerminalObjects.out f hI

/--
theorem `IsTerminal.strict_hom_ext` / 定理 `IsTerminal.strict_hom_ext`

English:
theorem IsTerminal.strict_hom_ext
  given: (hI : IsTerminal I) {A : C} (f g : I ⟶ A)
  statement: f = g
  proof: by
  have := hI.isIso_from f
  have := hI.isIso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

中文:
定理 IsTerminal.strict_hom_ext
  条件: (hI : IsTerminal I) {A : C} (f g : I ⟶ A)
  结论: f = g
  证明: by
  have := hI.isIso_from f
  have := hI.isIso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

Depends on / 依赖: P.prop_of_iso, e.symm.unop, eq_of_inv_eq_inv, hI.hom_ext, hI.isIso_from, hom_ext, isIso_from, prop_of_iso
-/
theorem IsTerminal.strict_hom_ext (hI : IsTerminal I) {A : C} (f g : I ⟶ A) : f = g := by
  have := hI.isIso_from f
  have := hI.isIso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

/-- If `X ⟶ Y` with `Y` being a strict terminal object, then `X` is also a terminal object. -/
noncomputable
/--
Definition of `IsTerminal.ofStrict` / `IsTerminal.ofStrict` 的定义

English:
definition IsTerminal.ofStrict
  signature: {X Y : C} (f : X ⟶ Y)
  body: letI := hY.isIso_from f
  hY.ofIso (asIso f)

中文:
定义 IsTerminal.ofStrict
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: letI := hY.isIso_from f
  hY.ofIso (asIso f)

Depends on / 依赖: P.prop_of_iso, e.symm.op, hY.isIso_from, hY.ofIso, isIso_from, prop_of_iso
-/
def IsTerminal.ofStrict {X Y : C} (f : X ⟶ Y)
    (hY : IsTerminal X) : IsTerminal Y :=
  letI := hY.isIso_from f
  hY.ofIso (asIso f)

/--
theorem `IsTerminal.subsingleton_to` / 定理 `IsTerminal.subsingleton_to`

English:
theorem IsTerminal.subsingleton_to
  given: (hI : IsTerminal I) {A : C}
  statement: Subsingleton (I ⟶ A)
  proof: ⟨hI.strict_hom_ext⟩

中文:
定理 IsTerminal.subsingleton_to
  条件: (hI : IsTerminal I) {A : C}
  结论: Subsingleton (I ⟶ A)
  证明: ⟨hI.strict_hom_ext⟩

Depends on / 依赖: hI.strict_hom_ext, strict_hom_ext
-/
theorem IsTerminal.subsingleton_to (hI : IsTerminal I) {A : C} : Subsingleton (I ⟶ A) :=
  ⟨hI.strict_hom_ext⟩

variable {J : Type v} [SmallCategory J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `limit_π_isIso_of_is_strict_terminal` / 定理 `limit_π_isIso_of_is_strict_terminal`

English:
theorem limit_π_isIso_of_is_strict_terminal
  statement: (F : J ⥤ C) [HasLimit F] (i : J)
  proof: by
  classical
    refine ⟨⟨limit.lift _ ⟨_, ⟨?_, ?_⟩⟩, ?_, ?_⟩⟩
    · exact fun j =>
        dite (j = i)
          (fun h => eqToHom (by cases h; rfl))
          fun h => (H _ h).from _
    · intro j k f
      split_ifs with h h_1 h_1
      · cases h
        cases h_1
        obtain rfl : f = 𝟙 _ 

中文:
定理 limit_π_isIso_of_is_strict_terminal
  结论: (F : J ⥤ C) [HasLimit F] (i : J)
  证明: by
  classical
    refine ⟨⟨limit.lift _ ⟨_, ⟨?_, ?_⟩⟩, ?_, ?_⟩⟩
    · exact fun j =>
        dite (j = i)
          (fun h => eqToHom (by cases h; rfl))
          fun h => (H _ h).from _
    · intro j k f
      split_ifs with h h_1 h_1
      · cases h
        cases h_1
        obtain rfl : f = 𝟙 _ 

Depends on / 依赖: F.map, IsIso.comp_inv_eq, Subsingleton, Subsingleton.elim, classical, comp_inv_eq, eqToHom, hom_ext, isIso_from, limit.lift, limit.lift_, split_ifs
-/
theorem limit_π_isIso_of_is_strict_terminal (F : J ⥤ C) [HasLimit F] (i : J)
    (H : forall (j) (_ : j != i), IsTerminal (F.obj j)) [Subsingleton (i ⟶ i)] : IsIso (limit.π F i) := by
  classical
    refine ⟨⟨limit.lift _ ⟨_, ⟨?_, ?_⟩⟩, ?_, ?_⟩⟩
    · exact fun j =>
        dite (j = i)
          (fun h => eqToHom (by cases h; rfl))
          fun h => (H _ h).from _
    · intro j k f
      split_ifs with h h_1 h_1
      · cases h
        cases h_1
        obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
        simp
      · cases h
        have : IsIso (F.map f) := (H _ h_1).isIso_from _
        rw [← IsIso.comp_inv_eq]
        apply (H _ h_1).hom_ext
      · cases h_1
        apply (H _ h).hom_ext
      · apply (H _ h).hom_ext
    · ext
      rw [assoc]; rw [limit.lift_π]
      dsimp only
      split_ifs with h
      · cases h
        rw [id_comp]; rw [eqToHom_refl]
        exact comp_id _
      · apply (H _ h).hom_ext
    · simp

variable [HasTerminal C]

/--
Instance `terminal_isIso_from` / 实例 `terminal_isIso_from`

English:
instance terminal_isIso_from
  signature: {A : C} (f : ⊤_ C ⟶ A)
  body: terminalIsTerminal.isIso_from _

@[ext]

中文:
实例 terminal_isIso_from
  签名: {A : C} (f : ⊤_ C ⟶ A)
  定义体: terminalIsTerminal.isIso_from _

@[ext]

Depends on / 依赖: isIso_from, terminalIsTerminal, terminalIsTerminal.isIso_from
-/
instance terminal_isIso_from {A : C} (f : ⊤_ C ⟶ A) : IsIso f :=
  terminalIsTerminal.isIso_from _

@[ext]
/--
theorem `terminal.strict_hom_ext` / 定理 `terminal.strict_hom_ext`

English:
theorem terminal.strict_hom_ext
  given: {A : C} (f g : ⊤_ C ⟶ A)
  statement: f = g
  proof: terminalIsTerminal.strict_hom_ext _ _

中文:
定理 terminal.strict_hom_ext
  条件: {A : C} (f g : ⊤_ C ⟶ A)
  结论: f = g
  证明: terminalIsTerminal.strict_hom_ext _ _

Depends on / 依赖: strict_hom_ext, terminalIsTerminal, terminalIsTerminal.strict_hom_ext
-/
theorem terminal.strict_hom_ext {A : C} (f g : ⊤_ C ⟶ A) : f = g :=
  terminalIsTerminal.strict_hom_ext _ _

/--
theorem `terminal.subsingleton_to` / 定理 `terminal.subsingleton_to`

English:
theorem terminal.subsingleton_to
  given: {A : C}
  statement: Subsingleton (⊤_ C ⟶ A)
  proof: terminalIsTerminal.subsingleton_to

中文:
定理 terminal.subsingleton_to
  条件: {A : C}
  结论: Subsingleton (⊤_ C ⟶ A)
  证明: terminalIsTerminal.subsingleton_to

Depends on / 依赖: subsingleton_to, terminalIsTerminal, terminalIsTerminal.subsingleton_to
-/
theorem terminal.subsingleton_to {A : C} : Subsingleton (⊤_ C ⟶ A) :=
  terminalIsTerminal.subsingleton_to

end

/--
theorem `hasStrictTerminalObjects_of_terminal_is_strict` / 定理 `hasStrictTerminalObjects_of_terminal_is_strict`

English:
theorem hasStrictTerminalObjects_of_terminal_is_strict
  given: (I : C) (h : forall (A) (f : I ⟶ A), IsIso f)
  proof: { out := fun {I' A} f hI' =>
      haveI := h A (hI'.from _ ≫ f)
      ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by rw [assoc, IsIso.inv_hom_id]⟩⟩ }

中文:
定理 hasStrictTerminalObjects_of_terminal_is_strict
  条件: (I : C) (h : 对任意 (A) (f : I ⟶ A), IsIso f)
  证明: { out := fun {I' A} f hI' =>
      haveI := h A (hI'.from _ ≫ f)
      ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by rw [assoc, IsIso.inv_hom_id]⟩⟩ }

Depends on / 依赖: IsIso.inv_hom_id, hom_ext, inv_hom_id
-/
theorem hasStrictTerminalObjects_of_terminal_is_strict (I : C) (h : forall (A) (f : I ⟶ A), IsIso f) :
    HasStrictTerminalObjects C :=
  { out := fun {I' A} f hI' =>
      haveI := h A (hI'.from _ ≫ f)
      ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by rw [assoc, IsIso.inv_hom_id]⟩⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Quiver.IsThin
  signature: C] : HasStrictTerminalObjects C where
  body: by
    rw [CategoryTheory.isIso_iff_of_thin]
    exact ⟨hI.from _⟩

中文:
实例 [Quiver.IsThin
  签名: C] : HasStrictTerminalObjects C where
  定义体: by
    rw [CategoryTheory.isIso_iff_of_thin]
    exact ⟨hI.from _⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.isIso_iff_of_thin, hI.from, isIso_iff_of_thin
-/
instance [Quiver.IsThin C] : HasStrictTerminalObjects C where
  out {I A} f hI := by
    rw [CategoryTheory.isIso_iff_of_thin]
    exact ⟨hI.from _⟩

end StrictTerminal

end Limits

end CategoryTheory
