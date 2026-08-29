/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.PUnit

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunctionOfStructuredArrowInitials` gives the left adjoint assuming the
appropriate initial objects exist, and `mkInitialOfLeftAdjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (G : D ⥤ C)

section OfInitials

variable [forall A, HasInitial (StructuredArrow A G)]

attribute [local simp] eq_iff_true_of_subsingleton in
/-- Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps]
/--
Definition of `leftAdjointOfStructuredArrowInitialsAux` / `leftAdjointOfStructuredArrowInitialsAux` 的定义

English:
definition leftAdjointOfStructuredArrowInitialsAux
  signature: (A : C) (B : D)
  body: (⊥_ StructuredArrow A G).hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g := by
    let B' : StructuredArrow A G := StructuredArrow.mk ((⊥_ StructuredArrow A G).hom ≫ G.map g)
    let g' : ⊥_ StructuredArrow A G ⟶ B' := StructuredArrow.homMk g rfl
    

中文:
定义 leftAdjointOfStructuredArrowInitialsAux
  签名: (A : C) (B : D)
  定义体: (⊥_ StructuredArrow A G).hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g := by
    let B' : StructuredArrow A G := StructuredArrow.mk ((⊥_ StructuredArrow A G).hom ≫ G.map g)
    let g' : ⊥_ StructuredArrow A G ⟶ B' := StructuredArrow.homMk g rfl
    

Depends on / 依赖: G.map, StructuredArrow
-/
def leftAdjointOfStructuredArrowInitialsAux (A : C) (B : D) :
    ((⊥_ StructuredArrow A G).right ⟶ B) ≃ (A ⟶ G.obj B) where
  toFun g := (⊥_ StructuredArrow A G).hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g := by
    let B' : StructuredArrow A G := StructuredArrow.mk ((⊥_ StructuredArrow A G).hom ≫ G.map g)
    let g' : ⊥_ StructuredArrow A G ⟶ B' := StructuredArrow.homMk g rfl
    have : initial.to _ = g' := by cat_disch
    change CommaMorphism.right (initial.to B') = _
    rw [this]
    rfl
  right_inv f := by
    let B' : StructuredArrow A G := StructuredArrow.mk f
    apply (CommaMorphism.w (initial.to B')).symm.trans (Category.id_comp _)

/--
Definition of `leftAdjointOfStructuredArrowInitials` / `leftAdjointOfStructuredArrowInitials` 的定义

English:
definition leftAdjointOfStructuredArrowInitials
  signature: : C ⥤ D
  body: Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp

中文:
定义 leftAdjointOfStructuredArrowInitials
  签名: : C ⥤ D
  定义体: Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp

Depends on / 依赖: Adjunction, Adjunction.leftAdjointOfEquiv, leftAdjointOfEquiv, leftAdjointOfStructuredArrowInitialsAux
-/
def leftAdjointOfStructuredArrowInitials : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp

/--
Definition of `adjunctionOfStructuredArrowInitials` / `adjunctionOfStructuredArrowInitials` 的定义

English:
definition adjunctionOfStructuredArrowInitials
  signature: : leftAdjointOfStructuredArrowInitials G ⊣ G
  body: Adjunction.adjunctionOfEquivLeft _ _

中文:
定义 adjunctionOfStructuredArrowInitials
  签名: : leftAdjointOfStructuredArrowInitials G ⊣ G
  定义体: Adjunction.adjunctionOfEquivLeft _ _

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivLeft, adjunctionOfEquivLeft
-/
def adjunctionOfStructuredArrowInitials : leftAdjointOfStructuredArrowInitials G ⊣ G :=
  Adjunction.adjunctionOfEquivLeft _ _

/--
lemma `isRightAdjointOfStructuredArrowInitials` / 引理 `isRightAdjointOfStructuredArrowInitials`

English:
lemma isRightAdjointOfStructuredArrowInitials
  statement: G.IsRightAdjoint where
  proof: ⟨_, ⟨adjunctionOfStructuredArrowInitials G⟩⟩

中文:
引理 isRightAdjointOfStructuredArrowInitials
  结论: G.IsRightAdjoint where
  证明: ⟨_, ⟨adjunctionOfStructuredArrowInitials G⟩⟩

Depends on / 依赖: adjunctionOfStructuredArrowInitials
-/
lemma isRightAdjointOfStructuredArrowInitials : G.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨adjunctionOfStructuredArrowInitials G⟩⟩

end OfInitials

section OfTerminals

variable [forall A, HasTerminal (CostructuredArrow G A)]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] eq_iff_true_of_subsingleton in
/-- Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps]
/--
Definition of `rightAdjointOfCostructuredArrowTerminalsAux` / `rightAdjointOfCostructuredArrowTerminalsAux` 的定义

English:
definition rightAdjointOfCostructuredArrowTerminalsAux
  signature: (B : D) (A : C)
  body: CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).hom
  left_inv := by cat_disch
  right_inv g := by
    let B' : CostructuredArrow G A :=
      CostructuredArrow.mk (G.map g ≫ (⊤_ CostructuredArrow G A).hom)
    let g' : B' ⟶ ⊤_ Costructu

中文:
定义 rightAdjointOfCostructuredArrowTerminalsAux
  签名: (B : D) (A : C)
  定义体: CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).hom
  left_inv := by cat_disch
  right_inv g := by
    let B' : CostructuredArrow G A :=
      CostructuredArrow.mk (G.map g ≫ (⊤_ CostructuredArrow G A).hom)
    let g' : B' ⟶ ⊤_ Costructu

Depends on / 依赖: CommaMorphism, CommaMorphism.left, CostructuredArrow, CostructuredArrow.mk, terminal, terminal.from
-/
def rightAdjointOfCostructuredArrowTerminalsAux (B : D) (A : C) :
    (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ CostructuredArrow G A).left) where
  toFun g := CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).hom
  left_inv := by cat_disch
  right_inv g := by
    let B' : CostructuredArrow G A :=
      CostructuredArrow.mk (G.map g ≫ (⊤_ CostructuredArrow G A).hom)
    let g' : B' ⟶ ⊤_ CostructuredArrow G A := CostructuredArrow.homMk g rfl
    have : terminal.from _ = g' := by cat_disch
    change CommaMorphism.left (terminal.from B') = _
    rw [this]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rightAdjointOfCostructuredArrowTerminals` / `rightAdjointOfCostructuredArrowTerminals` 的定义

English:
definition rightAdjointOfCostructuredArrowTerminals
  signature: : C ⥤ D
  body: Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G)
      fun B₁ B₂ A f g => by
    rw [← Equiv.eq_symm_apply]
    simp

中文:
定义 rightAdjointOfCostructuredArrowTerminals
  签名: : C ⥤ D
  定义体: Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G)
      fun B₁ B₂ A f g => by
    rw [← Equiv.eq_symm_apply]
    simp

Depends on / 依赖: Adjunction, Adjunction.rightAdjointOfEquiv, Equiv.eq_symm_apply, eq_symm_apply, rightAdjointOfCostructuredArrowTerminalsAux, rightAdjointOfEquiv
-/
def rightAdjointOfCostructuredArrowTerminals : C ⥤ D :=
  Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G)
      fun B₁ B₂ A f g => by
    rw [← Equiv.eq_symm_apply]
    simp

/--
Definition of `adjunctionOfCostructuredArrowTerminals` / `adjunctionOfCostructuredArrowTerminals` 的定义

English:
definition adjunctionOfCostructuredArrowTerminals
  signature: : G ⊣ rightAdjointOfCostructuredArrowTerminals G
  body: Adjunction.adjunctionOfEquivRight _ _

中文:
定义 adjunctionOfCostructuredArrowTerminals
  签名: : G ⊣ rightAdjointOfCostructuredArrowTerminals G
  定义体: Adjunction.adjunctionOfEquivRight _ _

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivRight, adjunctionOfEquivRight
-/
def adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArrowTerminals G :=
  Adjunction.adjunctionOfEquivRight _ _

/--
lemma `isLeftAdjoint_of_costructuredArrowTerminals` / 引理 `isLeftAdjoint_of_costructuredArrowTerminals`

English:
lemma isLeftAdjoint_of_costructuredArrowTerminals
  statement: G.IsLeftAdjoint where
  proof: ⟨rightAdjointOfCostructuredArrowTerminals G, ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

中文:
引理 isLeftAdjoint_of_costructuredArrowTerminals
  结论: G.IsLeftAdjoint where
  证明: ⟨rightAdjointOfCostructuredArrowTerminals G, ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivRight, adjunctionOfEquivRight, rightAdjointOfCostructuredArrowTerminals
-/
lemma isLeftAdjoint_of_costructuredArrowTerminals : G.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨rightAdjointOfCostructuredArrowTerminals G, ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

end OfTerminals

section

variable {F : C ⥤ D}

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkInitialOfLeftAdjoint` / `mkInitialOfLeftAdjoint` 的定义

English:
definition mkInitialOfLeftAdjoint
  signature: (h : F ⊣ G) (A : C)
  body: StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.hom)
  uniq s m _ := by
    apply StructuredArrow.ext
    simp [← StructuredArrow.w m]

中文:
定义 mkInitialOfLeftAdjoint
  签名: (h : F ⊣ G) (A : C)
  定义体: StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.hom)
  uniq s m _ := by
    apply StructuredArrow.ext
    simp [← StructuredArrow.w m]

Depends on / 依赖: B.pt.hom, StructuredArrow, StructuredArrow.homMk, h.homEquiv, homEquiv
-/
def mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (h.unit.app A) : StructuredArrow A G) where
  desc B := StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.hom)
  uniq s m _ := by
    apply StructuredArrow.ext
    simp [← StructuredArrow.w m]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkTerminalOfRightAdjoint` / `mkTerminalOfRightAdjoint` 的定义

English:
definition mkTerminalOfRightAdjoint
  signature: (h : F ⊣ G) (A : D)
  body: CostructuredArrow.homMk (h.homEquiv _ _ B.pt.hom)
  uniq s m _ := by
    apply CostructuredArrow.ext
    simp [← CostructuredArrow.w m]

中文:
定义 mkTerminalOfRightAdjoint
  签名: (h : F ⊣ G) (A : D)
  定义体: CostructuredArrow.homMk (h.homEquiv _ _ B.pt.hom)
  uniq s m _ := by
    apply CostructuredArrow.ext
    simp [← CostructuredArrow.w m]

Depends on / 依赖: B.pt.hom, CostructuredArrow, CostructuredArrow.homMk, h.homEquiv, homEquiv
-/
def mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) :
    IsTerminal (CostructuredArrow.mk (h.counit.app A) : CostructuredArrow F A) where
  lift B := CostructuredArrow.homMk (h.homEquiv _ _ B.pt.hom)
  uniq s m _ := by
    apply CostructuredArrow.ext
    simp [← CostructuredArrow.w m]

end

/--
theorem `isRightAdjoint_iff_hasInitial_structuredArrow` / 定理 `isRightAdjoint_iff_hasInitial_structuredArrow`

English:
theorem isRightAdjoint_iff_hasInitial_structuredArrow
  given: {G : D ⥤ C}
  proof: ⟨fun _ A => (mkInitialOfLeftAdjoint _ (Adjunction.ofIsRightAdjoint G) A).hasInitial,
    fun _ => isRightAdjointOfStructuredArrowInitials _⟩

中文:
定理 isRightAdjoint_iff_hasInitial_structuredArrow
  条件: {G : D ⥤ C}
  证明: ⟨fun _ A => (mkInitialOfLeftAdjoint _ (Adjunction.ofIsRightAdjoint G) A).hasInitial,
    fun _ => isRightAdjointOfStructuredArrowInitials _⟩

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, hasInitial, isRightAdjointOfStructuredArrowInitials, mkInitialOfLeftAdjoint, ofIsRightAdjoint
-/
theorem isRightAdjoint_iff_hasInitial_structuredArrow {G : D ⥤ C} :
    G.IsRightAdjoint ↔ forall A, HasInitial (StructuredArrow A G) :=
  ⟨fun _ A => (mkInitialOfLeftAdjoint _ (Adjunction.ofIsRightAdjoint G) A).hasInitial,
    fun _ => isRightAdjointOfStructuredArrowInitials _⟩

/--
theorem `isLeftAdjoint_iff_hasTerminal_costructuredArrow` / 定理 `isLeftAdjoint_iff_hasTerminal_costructuredArrow`

English:
theorem isLeftAdjoint_iff_hasTerminal_costructuredArrow
  given: {F : C ⥤ D}
  proof: ⟨fun _ A => (mkTerminalOfRightAdjoint _ (Adjunction.ofIsLeftAdjoint F) A).hasTerminal,
    fun _ => isLeftAdjoint_of_costructuredArrowTerminals _⟩

中文:
定理 isLeftAdjoint_iff_hasTerminal_costructuredArrow
  条件: {F : C ⥤ D}
  证明: ⟨fun _ A => (mkTerminalOfRightAdjoint _ (Adjunction.ofIsLeftAdjoint F) A).hasTerminal,
    fun _ => isLeftAdjoint_of_costructuredArrowTerminals _⟩

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, hasTerminal, isLeftAdjoint_of_costructuredArrowTerminals, mkTerminalOfRightAdjoint, ofIsLeftAdjoint
-/
theorem isLeftAdjoint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} :
    F.IsLeftAdjoint ↔ forall A, HasTerminal (CostructuredArrow F A) :=
  ⟨fun _ A => (mkTerminalOfRightAdjoint _ (Adjunction.ofIsLeftAdjoint F) A).hasTerminal,
    fun _ => isLeftAdjoint_of_costructuredArrowTerminals _⟩

end CategoryTheory
