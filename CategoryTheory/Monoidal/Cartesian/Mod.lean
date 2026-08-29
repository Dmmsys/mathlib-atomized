/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Module objects in cartesian monoidal categories

In this file we study module objects in a cartesian monoidal category `C` action on
itself by `⊗`.

In particular, for a monoid object `M : C` action on `X : C`, we equip `Z ⟶ X` with a `M ⟶ X` action
for every `Z : C`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local simp] leftUnitor_hom

/--
Definition of `ModObj.trivialAction` / `ModObj.trivialAction` 的定义

English:
definition ModObj.trivialAction
  signature: (M : C) [MonObj M] (X : C)
  body: snd M X

中文:
定义 ModObj.trivialAction
  签名: (M : C) [MonObj M] (X : C)
  定义体: snd M X
-/
@[reducible] def ModObj.trivialAction (M : C) [MonObj M] (X : C) :
    ModObj M X where
  smul := snd M X

attribute [local instance] ModObj.trivialAction in
/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
/--
Definition of `Mod.trivialAction` / `Mod.trivialAction` 的定义

English:
definition Mod.trivialAction
  signature: (M : Mon C) (X : C)
  body: X

@[deprecated (since := "2026-04-21")]
alias Mod_.trivialAction := Mod.trivialAction

中文:
定义 取模.trivialAction
  签名: (M : 幺半群 C) (X : C)
  定义体: X

@[deprecated (since := "2026-04-21")]
alias Mod_.trivialAction := Mod.trivialAction
-/
def Mod.trivialAction (M : Mon C) (X : C) : Mod C M.X where
  X := X

@[deprecated (since := "2026-04-21")]
alias Mod_.trivialAction := Mod.trivialAction

variable {M : C} [MonObj M] {X : C} [ModObj M X]

namespace Hom

/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal scalar multiplication. -/
@[to_additive (attr := simps! -isSimp)
/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal additive action. -/]
instance (Y : C) : SMul (Y ⟶ M) (Y ⟶ X) where
  smul m x := lift m x ≫ γ[M, X]

/-- If `M` is a monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/
@[to_additive /-- If `M` is an additive monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: (Z : C)
  body: by simp [one_def, smul_def, ← lift_whiskerRight]
  mul_smul m n x := by simp [mul_def, smul_def, ← lift_whiskerRight]

中文:
实例 mulAction
  签名: (Z : C)
  定义体: by simp [one_def, smul_def, ← lift_whiskerRight]
  mul_smul m n x := by simp [mul_def, smul_def, ← lift_whiskerRight]

Depends on / 依赖: lift_whiskerRight, mul_def, mul_smul, one_def, smul_def
-/
instance mulAction (Z : C) : MulAction (Z ⟶ M) (Z ⟶ X) where
  one_smul x := by simp [one_def, smul_def, ← lift_whiskerRight]
  mul_smul m n x := by simp [mul_def, smul_def, ← lift_whiskerRight]

end Hom

variable {Y : C} [ModObj M Y]

/--
lemma `ModObj.comp_smul` / 引理 `ModObj.comp_smul`

English:
lemma ModObj.comp_smul
  given: {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ M) (x : Z ⟶ X)
  proof: by
  rw [Hom.smul_def]; rw [Hom.smul_def]; rw [comp_lift_assoc]

@[to_additive (attr := reassoc (attr := simp))]

中文:
引理 ModObj.comp_smul
  条件: {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ M) (x : Z ⟶ X)
  证明: by
  rw [Hom.smul_def]; rw [Hom.smul_def]; rw [comp_lift_assoc]

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: Hom.smul_def, comp_lift_assoc, smul_def
-/
lemma ModObj.comp_smul {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ M) (x : Z ⟶ X) :
    g ≫ (m • x) = (g ≫ m) • (g ≫ x) := by
  rw [Hom.smul_def]; rw [Hom.smul_def]; rw [comp_lift_assoc]

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `IsModHom.map_smul` / 引理 `IsModHom.map_smul`

English:
lemma IsModHom.map_smul
  given: (f : X ⟶ Y) [IsModHom M f] {Z : C} (m : Z ⟶ M) (x : Z ⟶ X)
  proof: by
  simp [Hom.smul_def, Category.assoc, IsModHom.smul_hom]

中文:
引理 是取模态射.map_smul
  条件: (f : X ⟶ Y) [是取模态射 M f] {Z : C} (m : Z ⟶ M) (x : Z ⟶ X)
  证明: by
  simp [Hom.smul_def, Category.assoc, IsModHom.smul_hom]

Depends on / 依赖: Category, Category.assoc, Hom.smul_def, IsModHom, IsModHom.smul_hom, smul_def, smul_hom
-/
lemma IsModHom.map_smul (f : X ⟶ Y) [IsModHom M f] {Z : C} (m : Z ⟶ M) (x : Z ⟶ X) :
    (m • x) ≫ f = m • x ≫ f := by
  simp [Hom.smul_def, Category.assoc, IsModHom.smul_hom]

/-- An `M`-equivariant morphism induces an equivariant function on hom types. -/
@[to_additive (attr := simps)
/-- A `φ`-equivariant morphism induces an equivariant morphism on hom types. -/]
/--
Definition of `IsModHom.mulActionHom` / `IsModHom.mulActionHom` 的定义

English:
definition IsModHom.mulActionHom
  signature: (f : X ⟶ Y) [IsModHom M f] (Z : C)
  body: (· ≫ f)
  map_smul' := map_smul f

中文:
定义 是取模态射.mulActionHom
  签名: (f : X ⟶ Y) [是取模态射 M f] (Z : C)
  定义体: (· ≫ f)
  map_smul' := map_smul f
-/
def IsModHom.mulActionHom (f : X ⟶ Y) [IsModHom M f] (Z : C) :
    MulActionHom (id (α := Z ⟶ M)) (Z ⟶ X) (Z ⟶ Y) where
  toFun := (· ≫ f)
  map_smul' := map_smul f

namespace ModObj

variable (M X) in
/--
Definition of `leftSMul` / `leftSMul` 的定义

English:
definition leftSMul
  signature: : M otimes X ⟶ X otimes X
  body: lift γ[M, X] (snd _ _)

@[reassoc (attr := simp)]

中文:
定义 leftSMul
  签名: : M otimes X ⟶ X otimes X
  定义体: lift γ[M, X] (snd _ _)

@[reassoc (attr := simp)]
-/
def leftSMul : M otimes X ⟶ X otimes X :=
  lift γ[M, X] (snd _ _)

@[reassoc (attr := simp)]
/--
lemma `leftSMul_fst` / 引理 `leftSMul_fst`

English:
lemma leftSMul_fst
  statement: leftSMul M X ≫ fst _ _ = γ[M, X]
  proof: by
  simp [leftSMul]

@[reassoc (attr := simp)]

中文:
引理 leftSMul_fst
  结论: leftSMul M X ≫ fst _ _ = γ[M, X]
  证明: by
  simp [leftSMul]

@[reassoc (attr := simp)]

Depends on / 依赖: leftSMul
-/
lemma leftSMul_fst : leftSMul M X ≫ fst _ _ = γ[M, X] := by
  simp [leftSMul]

@[reassoc (attr := simp)]
/--
lemma `leftSMul_snd` / 引理 `leftSMul_snd`

English:
lemma leftSMul_snd
  statement: leftSMul M X ≫ snd _ _ = snd _ _
  proof: by
  simp [leftSMul]

@[reassoc]

中文:
引理 leftSMul_snd
  结论: leftSMul M X ≫ snd _ _ = snd _ _
  证明: by
  simp [leftSMul]

@[reassoc]

Depends on / 依赖: leftSMul
-/
lemma leftSMul_snd : leftSMul M X ≫ snd _ _ = snd _ _ := by
  simp [leftSMul]

@[reassoc]
/--
lemma `lift_leftSMul` / 引理 `lift_leftSMul`

English:
lemma lift_leftSMul
  given: (Z : C) (x : Z ⟶ X) (m : Z ⟶ M)
  statement: lift m x ≫ leftSMul M X = lift (m • x) x
  proof: by
  ext <;> simp [Hom.smul_def]

中文:
引理 lift_leftSMul
  条件: (Z : C) (x : Z ⟶ X) (m : Z ⟶ M)
  结论: lift m x ≫ leftSMul M X = lift (m • x) x
  证明: by
  ext <;> simp [Hom.smul_def]

Depends on / 依赖: Hom.smul_def, smul_def
-/
lemma lift_leftSMul (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) : lift m x ≫ leftSMul M X = lift (m • x) x := by
  ext <;> simp [Hom.smul_def]

/--
lemma `lift_leftSMul_eq_lift_iff` / 引理 `lift_leftSMul_eq_lift_iff`

English:
lemma lift_leftSMul_eq_lift_iff
  given: (Z : C) (x y : Z ⟶ X) (m : Z ⟶ M)
  proof: by
  simp [Hom.smul_def, leftSMul, CartesianMonoidalCategory.hom_ext_iff]

中文:
引理 lift_leftSMul_eq_lift_iff
  条件: (Z : C) (x y : Z ⟶ X) (m : Z ⟶ M)
  证明: by
  simp [Hom.smul_def, leftSMul, CartesianMonoidalCategory.hom_ext_iff]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.hom_ext_iff, Hom.smul_def, hom_ext_iff, leftSMul, smul_def
-/
lemma lift_leftSMul_eq_lift_iff (Z : C) (x y : Z ⟶ X) (m : Z ⟶ M) :
    lift m x ≫ leftSMul M X = lift y x ↔ m • x = y := by
  simp [Hom.smul_def, leftSMul, CartesianMonoidalCategory.hom_ext_iff]

open CartesianMonoidalCategory in
/--
lemma `isIso_leftSMul_iff` / 引理 `isIso_leftSMul_iff`

English:
lemma isIso_leftSMul_iff
  proof: by
  have H (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) :
      lift m x ≫ leftSMul M X = lift (m • x) x := by
    ext <;> simp [Hom.smul_def]
  have h (Z : C) (f g : Z ⟶ X) (m : Z ⟶ M) (x : Z ⟶ X) :
      lift m x ≫ leftSMul M X = lift f g ↔ x = g ∧ m • x = f := by
    simp [← lift_leftSMul_eq_lift_iff, Cartes

中文:
引理 isIso_leftSMul_iff
  证明: by
  have H (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) :
      lift m x ≫ leftSMul M X = lift (m • x) x := by
    ext <;> simp [Hom.smul_def]
  have h (Z : C) (f g : Z ⟶ X) (m : Z ⟶ M) (x : Z ⟶ X) :
      lift m x ≫ leftSMul M X = lift f g ↔ x = g ∧ m • x = f := by
    simp [← lift_leftSMul_eq_lift_iff, Cartes

Depends on / 依赖: Bijective, CartesianMonoidalCategory, CartesianMonoidalCategory.hom_ext_iff, Function, Function.Bijective.of_comp_iff, Function.bijective_iff_existsUnique, Hom.smul_def, bijective, bijective_iff_existsUnique, hom_ext_iff, isIso_iff_yoneda_map_bijective, leftSMul, liftEquiv, liftEquiv.bijective, liftEquiv.surjective.f, lift_leftSMul_eq_lift_iff, of_comp_iff, smul_def, surjective
-/
lemma isIso_leftSMul_iff :
    IsIso (leftSMul M X) ↔ forall (Z : C) (x y : Z ⟶ X), exists! (m : Z ⟶ M), m • x = y := by
  have H (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) :
      lift m x ≫ leftSMul M X = lift (m • x) x := by
    ext <;> simp [Hom.smul_def]
  have h (Z : C) (f g : Z ⟶ X) (m : Z ⟶ M) (x : Z ⟶ X) :
      lift m x ≫ leftSMul M X = lift f g ↔ x = g ∧ m • x = f := by
    simp [← lift_leftSMul_eq_lift_iff, CartesianMonoidalCategory.hom_ext_iff]
    grind
  rw [isIso_iff_yoneda_map_bijective]
  congr! with Z
  rw [← Function.Bijective.of_comp_iff _ liftEquiv.bijective]; rw [Function.bijective_iff_existsUnique]
  simp only [liftEquiv.surjective.forall, liftEquiv_apply, Prod.forall, Function.comp_apply, h]
  rw [forall_comm]
  congr! 2 with f g
  exact Equiv.existsUnique_subtype_congr ⟨fun a => ⟨a.val.fst, by grind⟩,
    fun a => ⟨⟨a.val, f⟩, by grind⟩, by cat_disch, by cat_disch⟩

end ModObj

end CategoryTheory
