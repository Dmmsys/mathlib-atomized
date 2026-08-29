/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.GroupTheory.EckmannHilton
public import Mathlib.Tactic.CategoryTheory.Reassoc
/-!
# Constructing a semiadditive structure from binary biproducts

We show that any category with zero morphisms and binary biproducts is enriched over the category
of commutative monoids.

-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.SemiadditiveOfBinaryBiproducts

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

section

variable (X Y : C)

/-- `f +ₗ g` is the composite `X ⟶ Y ⊞ Y ⟶ Y`, where the first map is `(f, g)` and the second map
is `(𝟙 𝟙)`. -/
@[simp]
/--
Definition of `leftAdd` / `leftAdd` 的定义

English:
definition leftAdd
  signature: (f g : X ⟶ Y)
  body: biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)

中文:
定义 leftAdd
  签名: (f g : X ⟶ Y)
  定义体: biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)

Depends on / 依赖: biprod, biprod.desc, biprod.lift
-/
def leftAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)

/-- `f +ᵣ g` is the composite `X ⟶ X ⊞ X ⟶ Y`, where the first map is `(𝟙, 𝟙)` and the second map
is `(f g)`. -/
@[simp]
/--
Definition of `rightAdd` / `rightAdd` 的定义

English:
definition rightAdd
  signature: (f g : X ⟶ Y)
  body: biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g

local infixr:65 " +ₗ " => leftAdd X Y

local infixr:65 " +ᵣ " => rightAdd X Y

中文:
定义 rightAdd
  签名: (f g : X ⟶ Y)
  定义体: biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g

local infixr:65 " +ₗ " => leftAdd X Y

local infixr:65 " +ᵣ " => rightAdd X Y

Depends on / 依赖: biprod, biprod.desc, biprod.lift
-/
def rightAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g

local infixr:65 " +ₗ " => leftAdd X Y

local infixr:65 " +ᵣ " => rightAdd X Y

/--
theorem `isUnital_leftAdd` / 定理 `isUnital_leftAdd`

English:
theorem isUnital_leftAdd
  statement: EckmannHilton.IsUnital (· +ₗ ·) 0
  proof: by
  have hr : forall f : X ⟶ Y, biprod.lift (0 : X ⟶ Y) f = f ≫ biprod.inr := by
    intro f
    ext
    · simp
    · simp [Category.assoc]
  have hl : forall f : X ⟶ Y, biprod.lift f (0 : X ⟶ Y) = f ≫ biprod.inl := by
    intro f
    ext
    · simp
    · simp [biprod.lift_snd, Category.assoc, comp

中文:
定理 isUnital_leftAdd
  结论: EckmannHilton.是Unital (· +ₗ ·) 0
  证明: by
  have hr : forall f : X ⟶ Y, biprod.lift (0 : X ⟶ Y) f = f ≫ biprod.inr := by
    intro f
    ext
    · simp
    · simp [Category.assoc]
  have hl : forall f : X ⟶ Y, biprod.lift f (0 : X ⟶ Y) = f ≫ biprod.inl := by
    intro f
    ext
    · simp
    · simp [biprod.lift_snd, Category.assoc, comp

Depends on / 依赖: Category, Category.assoc, Category.comp_id, biprod, biprod.inl, biprod.inl_desc, biprod.inr, biprod.inr_desc, biprod.lift, biprod.lift_snd, comp_id, comp_zero, inl_desc, inr_desc, leftAdd, left_id, lift_snd, right_id
-/
theorem isUnital_leftAdd : EckmannHilton.IsUnital (· +ₗ ·) 0 := by
  have hr : forall f : X ⟶ Y, biprod.lift (0 : X ⟶ Y) f = f ≫ biprod.inr := by
    intro f
    ext
    · simp
    · simp [Category.assoc]
  have hl : forall f : X ⟶ Y, biprod.lift f (0 : X ⟶ Y) = f ≫ biprod.inl := by
    intro f
    ext
    · simp
    · simp [biprod.lift_snd, Category.assoc, comp_zero]
  exact {
    left_id := fun f => by simp [hr f, leftAdd, Category.assoc, Category.comp_id, biprod.inr_desc],
    right_id := fun f => by simp [hl f, leftAdd, Category.assoc, Category.comp_id, biprod.inl_desc]
  }

/--
theorem `isUnital_rightAdd` / 定理 `isUnital_rightAdd`

English:
theorem isUnital_rightAdd
  statement: EckmannHilton.IsUnital (· +ᵣ ·) 0
  proof: by
  have h₂ : forall f : X ⟶ Y, biprod.desc (0 : X ⟶ Y) f = biprod.snd ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_snd_assoc]
  have h₁ : forall f : X ⟶ Y, biprod.desc f (0 : X ⟶ Y) = biprod.fst ≫ f := by
    intro f
    ext
    · simp
    · simp only

中文:
定理 isUnital_rightAdd
  结论: EckmannHilton.是Unital (· +ᵣ ·) 0
  证明: by
  have h₂ : forall f : X ⟶ Y, biprod.desc (0 : X ⟶ Y) f = biprod.snd ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_snd_assoc]
  have h₁ : forall f : X ⟶ Y, biprod.desc f (0 : X ⟶ Y) = biprod.fst ≫ f := by
    intro f
    ext
    · simp
    · simp only

Depends on / 依赖: BinaryBicone, BinaryBicone.inr_fst_assoc, BinaryBicone.inr_snd_assoc, Category, Category.id_co, Category.id_comp, biprod, biprod.desc, biprod.fst, biprod.inr_desc, biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.snd, id_co, id_comp, inr_desc, inr_fst_assoc, inr_snd_assoc, left_id, lift_fst_assoc
-/
theorem isUnital_rightAdd : EckmannHilton.IsUnital (· +ᵣ ·) 0 := by
  have h₂ : forall f : X ⟶ Y, biprod.desc (0 : X ⟶ Y) f = biprod.snd ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_snd_assoc]
  have h₁ : forall f : X ⟶ Y, biprod.desc f (0 : X ⟶ Y) = biprod.fst ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_fst_assoc, zero_comp]
  exact {
    left_id := fun f => by simp [h₂ f, rightAdd, biprod.lift_snd_assoc, Category.id_comp],
    right_id := fun f => by simp [h₁ f, rightAdd, biprod.lift_fst_assoc, Category.id_comp]
  }

/--
theorem `distrib` / 定理 `distrib`

English:
theorem distrib
  given: (f g h k : X ⟶ Y)
  statement: (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k
  proof: by
  let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift (biprod.desc f g) (biprod.desc h k)
  have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by ext <;> simp [diag]
  have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by ext <;> simp [diag]
  have h₁ : biprod.lift (f +ᵣ g) (h +ᵣ k) = biprod.lift (𝟙 X) (𝟙 X) ≫

中文:
定理 distrib
  条件: (f g h k : X ⟶ Y)
  结论: (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k
  证明: by
  let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift (biprod.desc f g) (biprod.desc h k)
  have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by ext <;> simp [diag]
  have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by ext <;> simp [diag]
  have h₁ : biprod.lift (f +ᵣ g) (h +ᵣ k) = biprod.lift (𝟙 X) (𝟙 X) ≫

Depends on / 依赖: Category, Category.assoc, biprod, biprod.desc, biprod.inl, biprod.inr, biprod.lift, cat_disch, leftAdd, reassoc_of
-/
theorem distrib (f g h k : X ⟶ Y) : (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k := by
  let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift (biprod.desc f g) (biprod.desc h k)
  have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by ext <;> simp [diag]
  have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by ext <;> simp [diag]
  have h₁ : biprod.lift (f +ᵣ g) (h +ᵣ k) = biprod.lift (𝟙 X) (𝟙 X) ≫ diag := by
    ext <;> cat_disch
  have h₂ : diag ≫ biprod.desc (𝟙 Y) (𝟙 Y) = biprod.desc (f +ₗ h) (g +ₗ k) := by
    ext <;> simp [reassoc_of% hd₁, reassoc_of% hd₂]
  rw [leftAdd]; rw [h₁]; rw [Category.assoc]; rw [h₂]; rw [rightAdd]

/-- In a category with binary biproducts, the morphisms form a commutative monoid. -/
@[instance_reducible]
/--
Definition of `addCommMonoidHomOfHasBinaryBiproducts` / `addCommMonoidHomOfHasBinaryBiproducts` 的定义

English:
definition addCommMonoidHomOfHasBinaryBiproducts
  signature: : AddCommMonoid (X ⟶ Y) where
  body: (· +ᵣ ·)
  add_assoc :=
    (EckmannHilton.mul_assoc (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).assoc
  zero_add := (isUnital_rightAdd X Y).left_id
  add_zero := (isUnital_rightAdd X Y).right_id
  add_comm :=
    (EckmannHilton.mul_comm (isUnital_leftAdd X Y) (isUnital_rightAdd X 

中文:
定义 addCommMonoidHomOfHasBinaryBiproducts
  签名: : 加法交换幺半群 (X ⟶ Y) where
  定义体: (· +ᵣ ·)
  add_assoc :=
    (EckmannHilton.mul_assoc (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).assoc
  zero_add := (isUnital_rightAdd X Y).left_id
  add_zero := (isUnital_rightAdd X Y).right_id
  add_comm :=
    (EckmannHilton.mul_comm (isUnital_leftAdd X Y) (isUnital_rightAdd X 
-/
def addCommMonoidHomOfHasBinaryBiproducts : AddCommMonoid (X ⟶ Y) where
  add := (· +ᵣ ·)
  add_assoc :=
    (EckmannHilton.mul_assoc (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).assoc
  zero_add := (isUnital_rightAdd X Y).left_id
  add_zero := (isUnital_rightAdd X Y).right_id
  add_comm :=
    (EckmannHilton.mul_comm (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).comm
  nsmul := letI : Add (X ⟶ Y) := ⟨(· +ᵣ ·)⟩; nsmulRec

end

section

variable {X Y Z : C}

attribute [local instance] addCommMonoidHomOfHasBinaryBiproducts

/--
theorem `add_eq_right_addition` / 定理 `add_eq_right_addition`

English:
theorem add_eq_right_addition
  given: (f g : X ⟶ Y)
  statement: f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g
  proof: rfl

中文:
定理 add_eq_right_addition
  条件: (f g : X ⟶ Y)
  结论: f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g
  证明: rfl
-/
theorem add_eq_right_addition (f g : X ⟶ Y) : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g :=
  rfl

/--
theorem `add_eq_left_addition` / 定理 `add_eq_left_addition`

English:
theorem add_eq_left_addition
  given: (f g : X ⟶ Y)
  statement: f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)
  proof: congr_fun₂ (EckmannHilton.mul (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).symm f
    g

中文:
定理 add_eq_left_addition
  条件: (f g : X ⟶ Y)
  结论: f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)
  证明: congr_fun₂ (EckmannHilton.mul (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).symm f
    g

Depends on / 依赖: EckmannHilton, EckmannHilton.mul, distrib, isUnital_leftAdd, isUnital_rightAdd
-/
theorem add_eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) :=
  congr_fun₂ (EckmannHilton.mul (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).symm f
    g

/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  given: (f g : X ⟶ Y) (h : Y ⟶ Z)
  statement: (f + g) ≫ h = f ≫ h + g ≫ h
  proof: by
  simp only [add_eq_right_addition, Category.assoc]
  congr
  ext <;> simp

中文:
定理 add_comp
  条件: (f g : X ⟶ Y) (h : Y ⟶ Z)
  结论: (f + g) ≫ h = f ≫ h + g ≫ h
  证明: by
  simp only [add_eq_right_addition, Category.assoc]
  congr
  ext <;> simp

Depends on / 依赖: Category, Category.assoc, add_eq_right_addition
-/
theorem add_comp (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  simp only [add_eq_right_addition, Category.assoc]
  congr
  ext <;> simp

/--
theorem `comp_add` / 定理 `comp_add`

English:
theorem comp_add
  given: (f : X ⟶ Y) (g h : Y ⟶ Z)
  statement: f ≫ (g + h) = f ≫ g + f ≫ h
  proof: by
  simp only [add_eq_left_addition, ← Category.assoc]
  congr
  ext <;> simp

中文:
定理 comp_add
  条件: (f : X ⟶ Y) (g h : Y ⟶ Z)
  结论: f ≫ (g + h) = f ≫ g + f ≫ h
  证明: by
  simp only [add_eq_left_addition, ← Category.assoc]
  congr
  ext <;> simp

Depends on / 依赖: Category, Category.assoc, add_eq_left_addition
-/
theorem comp_add (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  simp only [add_eq_left_addition, ← Category.assoc]
  congr
  ext <;> simp

end

end CategoryTheory.SemiadditiveOfBinaryBiproducts
