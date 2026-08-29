/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `CategoryTheory.Pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(Opens X)ᵒᵖ`),
we produce a functor `CategoryTheory.Pairwise ι ⥤ α` in the obvious way,
and show that `iSup U` provides a colimit cocone over this functor.
-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

/--
Inductive type `Pairwise` / 归纳类型 `Pairwise`

English:
inductive Pairwise
  parameters: (ι : Type v)
  constructors (2):
    - single: ι -> Pairwise ι
    - pair: ι -> ι -> Pairwise ι

中文:
归纳类型 两两
  参数: (ι : 类型v)
  构造子 (2 个):
    - single: ι -> 两两 ι
    - pair: ι -> ι -> 两两 ι
-/
inductive Pairwise (ι : Type v)
  | single : ι -> Pairwise ι
  | pair : ι -> ι -> Pairwise ι
  deriving Fintype, DecidableEq

variable {ι : Type v}

namespace Pairwise

/--
Instance `pairwiseInhabited` / 实例 `pairwiseInhabited`

English:
instance pairwiseInhabited
  signature: [Inhabited ι]
  body: ⟨single default⟩

中文:
实例 pairwiseInhabited
  签名: [可居 ι]
  定义体: ⟨single default⟩

Depends on / 依赖: single
-/
instance pairwiseInhabited [Inhabited ι] : Inhabited (Pairwise ι) :=
  ⟨single default⟩

/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : Pairwise ι -> Pairwise ι -> Type v
  constructors (4):
    - id_single: forall i, Hom (single i) (single i)
    - id_pair: forall i j, Hom (pair i j) (pair i j)
    - left: forall i j, Hom (pair i j) (single i)
    - right: forall i j, Hom (pair i j) (single j)

中文:
归纳类型 态射
  参数: : 两两 ι -> 两两 ι -> 类型v
  构造子 (4 个):
    - id_single: 对任意 i, 态射 (single i) (single i)
    - id_pair: 对任意 i j, 态射 (pair i j) (pair i j)
    - left: 对任意 i j, 态射 (pair i j) (single i)
    - right: 对任意 i j, 态射 (pair i j) (single j)
-/
inductive Hom : Pairwise ι -> Pairwise ι -> Type v
  | id_single : forall i, Hom (single i) (single i)
  | id_pair : forall i j, Hom (pair i j) (pair i j)
  | left : forall i j, Hom (pair i j) (single i)
  | right : forall i j, Hom (pair i j) (single j)
  deriving DecidableEq

-- False positive?
attribute [nolint unusedArguments] instDecidableEqHom.decEq

open Hom

/--
Instance `homInhabited` / 实例 `homInhabited`

English:
instance homInhabited
  signature: [Inhabited ι]
  body: ⟨id_single default⟩

中文:
实例 homInhabited
  签名: [可居 ι]
  定义体: ⟨id_single default⟩

Depends on / 依赖: id_single
-/
instance homInhabited [Inhabited ι] : Inhabited (Hom (single (default : ι)) (single default)) :=
  ⟨id_single default⟩

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : forall o : Pairwise ι, Hom o o

中文:
定义 id
  签名: : 对任意 o : 两两 ι, 态射 o o
-/
def id : forall o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : forall {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃

中文:
定义 comp
  签名: : 对任意 {o₁ o₂ o₃ : 两两 ι} (_ : 态射 o₁ o₂) (_ : 态射 o₂ o₃), 态射 o₁ o₃
-/
def comp : forall {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
  | _, _, _, id_single _, g => g
  | _, _, _, id_pair _ _, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (Pairwise ι)
  body: Hom
  id := id
  comp := @comp _

中文:
实例 :
  签名: CategoryStruct (两两 ι)
  定义体: Hom
  id := id
  comp := @comp _
-/
instance : CategoryStruct (Pairwise ι) where
  Hom := Hom
  id := id
  comp := @comp _

section

open Lean Elab Tactic in
/-- A helper tactic for `cat_disch` and `CategoryTheory.Pairwise`. -/
meta def pairwiseCases : TacticM Unit := do
  evalTactic (← `(tactic| casesm* (_ : Pairwise _) ⟶ (_ : Pairwise _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] pairwiseCases in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Pairwise ι)

中文:
实例 :
  签名: 范畴 (两两 ι)
-/
instance : Category (Pairwise ι) where

end

instance {i j : Pairwise ι} [DecidableEq ι] : DecidableEq (i ⟶ j) :=
  inferInstanceAs (DecidableEq (Pairwise.Hom i j))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: ι] [DecidableEq ι] : FinCategory (Pairwise ι) where

中文:
实例 [有限类型
  签名: ι] [DecidableEq ι] : 有限范畴 (两两 ι) where
-/
instance [Fintype ι] [DecidableEq ι] : FinCategory (Pairwise ι) where
  fintypeHom
  | .single i, .single j => ⟨if h : i = j then {eqToHom (h ▸ rfl)} else ∅, by rintro ⟨⟩; cat_disch⟩
  | .single i, .pair j k => ⟨∅, by rintro ⟨⟩⟩
  | .pair i j, .single k =>
    ⟨(if h : i = k then {Hom.left i j ≫ eqToHom (h ▸ rfl)} else ∅) union
      (if h : j = k then {Hom.right i j ≫ eqToHom (h ▸ rfl)} else ∅),
        by rintro ⟨⟩ <;> cat_disch⟩
  | .pair i j, .pair k l =>
    ⟨if h : i = k ∧ j = l then {eqToHom (h.1 ▸ h.2 ▸ rfl)} else ∅, by rintro ⟨⟩; cat_disch⟩

variable {α : Type u} (U : ι -> α)

section

variable [SemilatticeInf α]

/-- Auxiliary definition for `diagram`. -/
@[simp]
/--
Definition of `diagramObj` / `diagramObj` 的定义

English:
definition diagramObj
  signature: : Pairwise ι -> α

中文:
定义 diagramObj
  签名: : 两两 ι -> α
-/
def diagramObj : Pairwise ι -> α
  | single i => U i
  | pair i j => U i ⊓ U j

/-- Auxiliary definition for `diagram`. -/
@[simp]
/--
Definition of `diagramMap` / `diagramMap` 的定义

English:
definition diagramMap
  signature: : forall {o₁ o₂ : Pairwise ι} (_ : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂

中文:
定义 diagramMap
  签名: : 对任意 {o₁ o₂ : 两两 ι} (_ : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂
-/
def diagramMap : forall {o₁ o₂ : Pairwise ι} (_ : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => homOfLE inf_le_left
  | _, _, right _ _ => homOfLE inf_le_right

/-- Given a function `U : ι → α` for `[SemilatticeInf α]`, we obtain a functor
`CategoryTheory.Pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
@[simps]
/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: : Pairwise ι ⥤ α where
  body: diagramObj U
  map := diagramMap U

中文:
定义 diagram
  签名: : 两两 ι ⥤ α where
  定义体: diagramObj U
  map := diagramMap U

Depends on / 依赖: diagramObj
-/
def diagram : Pairwise ι ⥤ α where
  obj := diagramObj U
  map := diagramMap U

end

section

-- `CompleteLattice` is not really needed, as we only ever use `inf`,
-- but the appropriate structure has not been defined.
variable [CompleteLattice α]

/--
Definition of `coconeιApp` / `coconeιApp` 的定义

English:
definition coconeιApp
  signature: : forall o : Pairwise ι, diagramObj U o ⟶ iSup U

中文:
定义 coconeιApp
  签名: : 对任意 o : 两两 ι, diagramObj U o ⟶ iSup U
-/
def coconeιApp : forall o : Pairwise ι, diagramObj U o ⟶ iSup U
  | single i => homOfLE (le_iSup U i)
  | pair i _ => homOfLE inf_le_left ≫ homOfLE (le_iSup U i)

/-- Given a function `U : ι → α` for `[CompleteLattice α]`,
`iSup U` provides a cocone over `diagram U`.
-/
@[simps]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone (diagram U) where
  body: iSup U
  ι := { app := coconeιApp U }

中文:
定义 cocone
  签名: : 余锥 (diagram U) where
  定义体: iSup U
  ι := { app := coconeιApp U }
-/
def cocone : Cocone (diagram U) where
  pt := iSup U
  ι := { app := coconeιApp U }

/--
Definition of `coconeIsColimit` / `coconeIsColimit` 的定义

English:
definition coconeIsColimit
  signature: : IsColimit (cocone U) where
  body: homOfLE
    (by
      apply sSup_le
      rintro _ ⟨j, rfl⟩
      exact (s.ι.app (single j)).le)

中文:
定义 coconeIsColimit
  签名: : 是余极限 (cocone U) where
  定义体: homOfLE
    (by
      apply sSup_le
      rintro _ ⟨j, rfl⟩
      exact (s.ι.app (single j)).le)

Depends on / 依赖: homOfLE
-/
def coconeIsColimit : IsColimit (cocone U) where
  desc s := homOfLE
    (by
      apply sSup_le
      rintro _ ⟨j, rfl⟩
      exact (s.ι.app (single j)).le)

end

end Pairwise

end CategoryTheory
