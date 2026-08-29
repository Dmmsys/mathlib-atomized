/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Transport rigid structures over a monoidal equivalence.
-/

@[expose] public section


namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- Given candidate data for an exact pairing,
which is sent by a faithful monoidal functor to an exact pairing,
the equations holds automatically. -/
@[instance_reducible]
/--
Definition of `ExactPairing.ofFaithful` / `ExactPairing.ofFaithful` 的定义

English:
definition ExactPairing.ofFaithful
  signature: [F.Faithful] {X Y : C} (eval : Y otimes X ⟶ 𝟙_ C)
  body: eval
  coevaluation' := coeval
  evaluation_coevaluation' :=
F.map_injective by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' :=
F.map_injective by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]

中文:
定义 ExactPairing.ofFaithful
  签名: [F.忠实] {X Y : C} (eval : Y otimes X ⟶ 𝟙_ C)
  定义体: eval
  coevaluation' := coeval
  evaluation_coevaluation' :=
F.map_injective by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' :=
F.map_injective by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
-/
def ExactPairing.ofFaithful [F.Faithful] {X Y : C} (eval : Y otimes X ⟶ 𝟙_ C)
    (coeval : 𝟙_ C ⟶ X otimes Y) [ExactPairing (F.obj X) (F.obj Y)]
    (map_eval : F.map eval = (δ F _ _) ≫ ε_ _ _ ≫ ε F)
    (map_coeval : F.map coeval = (η F) ≫ η_ _ _ ≫ μ F _ _) : ExactPairing X Y where
  evaluation' := eval
  coevaluation' := coeval
  evaluation_coevaluation' :=
F.map_injective by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' :=
F.map_injective by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]

/-- Given a pair of objects which are sent by a fully faithful functor to a pair of objects
with an exact pairing, we get an exact pairing.
-/
@[instance_reducible]
/--
Definition of `ExactPairing.ofFullyFaithful` / `ExactPairing.ofFullyFaithful` 的定义

English:
definition ExactPairing.ofFullyFaithful
  signature: [F.Full] [F.Faithful] (X Y : C)
  body: .ofFaithful F (F.preimage (δ F _ _ ≫ ε_ _ _ ≫ (ε F)))
    (F.preimage (η F ≫ η_ _ _ ≫ μ F _ _)) (by simp) (by simp)

中文:
定义 ExactPairing.ofFullyFaithful
  签名: [F.满] [F.忠实] (X Y : C)
  定义体: .ofFaithful F (F.preimage (δ F _ _ ≫ ε_ _ _ ≫ (ε F)))
    (F.preimage (η F ≫ η_ _ _ ≫ μ F _ _)) (by simp) (by simp)

Depends on / 依赖: F.preimage, ofFaithful, preimage
-/
noncomputable def ExactPairing.ofFullyFaithful [F.Full] [F.Faithful] (X Y : C)
    [ExactPairing (F.obj X) (F.obj Y)] : ExactPairing X Y :=
  .ofFaithful F (F.preimage (δ F _ _ ≫ ε_ _ _ ≫ (ε F)))
    (F.preimage (η F ≫ η_ _ _ ≫ μ F _ _)) (by simp) (by simp)

variable {F}
variable {G : D ⥤ C} (adj : F ⊣ G) [F.IsEquivalence]

noncomputable section

/-- Pull back a left dual along an equivalence. -/
@[instance_reducible]
/--
Definition of `hasLeftDualOfEquivalence` / `hasLeftDualOfEquivalence` 的定义

English:
definition hasLeftDualOfEquivalence
  signature: (X : C) [HasLeftDual (F.obj X)]
  body: G.obj (ᘁ(F.obj X))
  exact := by
    letI := exactPairingCongrLeft (X := F.obj (G.obj ᘁ(F.obj X)))
      (X' := ᘁ(F.obj X)) (Y := F.obj X) (adj.toEquivalence.counitIso.app ᘁ(F.obj X))
    apply ExactPairing.ofFullyFaithful F

中文:
定义 hasLeftDualOfEquivalence
  签名: (X : C) [有LeftDual (F.obj X)]
  定义体: G.obj (ᘁ(F.obj X))
  exact := by
    letI := exactPairingCongrLeft (X := F.obj (G.obj ᘁ(F.obj X)))
      (X' := ᘁ(F.obj X)) (Y := F.obj X) (adj.toEquivalence.counitIso.app ᘁ(F.obj X))
    apply ExactPairing.ofFullyFaithful F

Depends on / 依赖: F.obj, G.obj
-/
def hasLeftDualOfEquivalence (X : C) [HasLeftDual (F.obj X)] :
    HasLeftDual X where
  leftDual := G.obj (ᘁ(F.obj X))
  exact := by
    letI := exactPairingCongrLeft (X := F.obj (G.obj ᘁ(F.obj X)))
      (X' := ᘁ(F.obj X)) (Y := F.obj X) (adj.toEquivalence.counitIso.app ᘁ(F.obj X))
    apply ExactPairing.ofFullyFaithful F

/-- Pull back a right dual along an equivalence. -/
@[instance_reducible]
/--
Definition of `hasRightDualOfEquivalence` / `hasRightDualOfEquivalence` 的定义

English:
definition hasRightDualOfEquivalence
  signature: (X : C) [HasRightDual (F.obj X)]
  body: G.obj ((F.obj X)ᘁ)
  exact := by
    letI := exactPairingCongrRight (X := F.obj X) (Y := F.obj (G.obj (F.obj X)ᘁ))
      (Y' := (F.obj X)ᘁ) (adj.toEquivalence.counitIso.app (F.obj X)ᘁ)
    apply ExactPairing.ofFullyFaithful F

中文:
定义 hasRightDualOfEquivalence
  签名: (X : C) [有RightDual (F.obj X)]
  定义体: G.obj ((F.obj X)ᘁ)
  exact := by
    letI := exactPairingCongrRight (X := F.obj X) (Y := F.obj (G.obj (F.obj X)ᘁ))
      (Y' := (F.obj X)ᘁ) (adj.toEquivalence.counitIso.app (F.obj X)ᘁ)
    apply ExactPairing.ofFullyFaithful F

Depends on / 依赖: F.obj, G.obj
-/
def hasRightDualOfEquivalence (X : C) [HasRightDual (F.obj X)] :
    HasRightDual X where
  rightDual := G.obj ((F.obj X)ᘁ)
  exact := by
    letI := exactPairingCongrRight (X := F.obj X) (Y := F.obj (G.obj (F.obj X)ᘁ))
      (Y' := (F.obj X)ᘁ) (adj.toEquivalence.counitIso.app (F.obj X)ᘁ)
    apply ExactPairing.ofFullyFaithful F

/-- Pull back a left rigid structure along an equivalence. -/
@[instance_reducible]
/--
Definition of `leftRigidCategoryOfEquivalence` / `leftRigidCategoryOfEquivalence` 的定义

English:
definition leftRigidCategoryOfEquivalence
  signature: [LeftRigidCategory D]
  body: hasLeftDualOfEquivalence adj X

中文:
定义 leftRigidCategoryOfEquivalence
  签名: [LeftRigid范畴 D]
  定义体: hasLeftDualOfEquivalence adj X

Depends on / 依赖: hasLeftDualOfEquivalence
-/
def leftRigidCategoryOfEquivalence [LeftRigidCategory D] :
    LeftRigidCategory C where leftDual X := hasLeftDualOfEquivalence adj X

/-- Pull back a right rigid structure along an equivalence. -/
@[instance_reducible]
/--
Definition of `rightRigidCategoryOfEquivalence` / `rightRigidCategoryOfEquivalence` 的定义

English:
definition rightRigidCategoryOfEquivalence
  signature: [RightRigidCategory D]
  body: hasRightDualOfEquivalence adj X

中文:
定义 rightRigidCategoryOfEquivalence
  签名: [RightRigid范畴 D]
  定义体: hasRightDualOfEquivalence adj X

Depends on / 依赖: hasRightDualOfEquivalence
-/
def rightRigidCategoryOfEquivalence [RightRigidCategory D] :
    RightRigidCategory C where rightDual X := hasRightDualOfEquivalence adj X

/-- Pull back a rigid structure along an equivalence. -/
@[instance_reducible]
/--
Definition of `rigidCategoryOfEquivalence` / `rigidCategoryOfEquivalence` 的定义

English:
definition rigidCategoryOfEquivalence
  signature: [RigidCategory D]
  body: hasLeftDualOfEquivalence adj X
  rightDual X := hasRightDualOfEquivalence adj X

中文:
定义 rigidCategoryOfEquivalence
  签名: [Rigid范畴 D]
  定义体: hasLeftDualOfEquivalence adj X
  rightDual X := hasRightDualOfEquivalence adj X

Depends on / 依赖: hasLeftDualOfEquivalence
-/
def rigidCategoryOfEquivalence [RigidCategory D] : RigidCategory C where
  leftDual X := hasLeftDualOfEquivalence adj X
  rightDual X := hasRightDualOfEquivalence adj X

end

end CategoryTheory
