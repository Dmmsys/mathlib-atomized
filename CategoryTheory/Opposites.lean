/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# Opposite categories

We provide a category instance on `Cᵒᵖ`.
The morphisms `X ⟶ Y` are defined to be the morphisms `unop Y ⟶ unop X` in `C`.

Here `Cᵒᵖ` is an irreducible typeclass synonym for `C`
(it is the same one used in the algebra library).

We also provide various mechanisms for constructing opposite morphisms, functors,
and natural transformations.

Unfortunately, because we do not have a definitional equality `op (op X) = X`,
there are quite a few variations that are needed in practice.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
open Opposite

variable {C : Type u₁}

section Quiver

variable [Quiver.{v₁} C]

@[to_dual self]
/--
theorem `Quiver.Hom.op_inj` / 定理 `Quiver.Hom.op_inj`

English:
theorem Quiver.Hom.op_inj
  given: {X Y : C}
  proof: fun _ _ H =>
  congr_arg Quiver.Hom.unop H

@[to_dual self]

中文:
定理 Quiver.Hom.op_inj
  条件: {X Y : C}
  证明: fun _ _ H =>
  congr_arg Quiver.Hom.unop H

@[to_dual self]
-/
theorem Quiver.Hom.op_inj {X Y : C} :
    Function.Injective (Quiver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X)) := fun _ _ H =>
  congr_arg Quiver.Hom.unop H

@[to_dual self]
/--
theorem `Quiver.Hom.unop_inj` / 定理 `Quiver.Hom.unop_inj`

English:
theorem Quiver.Hom.unop_inj
  given: {X Y : Cᵒᵖ}
  proof: fun _ _ H => congr_arg Quiver.Hom.op H

@[simp, to_dual self]

中文:
定理 Quiver.Hom.unop_inj
  条件: {X Y : Cᵒᵖ}
  证明: fun _ _ H => congr_arg Quiver.Hom.op H

@[simp, to_dual self]

Depends on / 依赖: Quiver, Quiver.Hom.op, congr_arg
-/
theorem Quiver.Hom.unop_inj {X Y : Cᵒᵖ} :
    Function.Injective (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X)) :=
  fun _ _ H => congr_arg Quiver.Hom.op H

@[simp, to_dual self]
/--
theorem `Quiver.Hom.unop_op` / 定理 `Quiver.Hom.unop_op`

English:
theorem Quiver.Hom.unop_op
  given: {X Y : C} (f : X ⟶ Y)
  statement: f.op.unop = f
  proof: rfl

@[simp, to_dual self]

中文:
定理 Quiver.Hom.unop_op
  条件: {X Y : C} (f : X ⟶ Y)
  结论: f.op.unop = f
  证明: rfl

@[simp, to_dual self]
-/
theorem Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl

@[simp, to_dual self]
/--
theorem `Quiver.Hom.unop_op'` / 定理 `Quiver.Hom.unop_op'`

English:
theorem Quiver.Hom.unop_op'
  given: {X Y : Cᵒᵖ} {x}
  proof: rfl

@[simp, to_dual self]

中文:
定理 Quiver.Hom.unop_op'
  条件: {X Y : Cᵒᵖ} {x}
  证明: rfl

@[simp, to_dual self]
-/
theorem Quiver.Hom.unop_op' {X Y : Cᵒᵖ} {x} :
    @Quiver.Hom.unop C _ X Y no_index (Opposite.op (unop := x)) = x := rfl

@[simp, to_dual self]
/--
theorem `Quiver.Hom.op_unop` / 定理 `Quiver.Hom.op_unop`

English:
theorem Quiver.Hom.op_unop
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  statement: f.unop.op = f
  proof: rfl

@[simp, to_dual self]

中文:
定理 Quiver.Hom.op_unop
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  结论: f.unop.op = f
  证明: rfl

@[simp, to_dual self]
-/
theorem Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f :=
  rfl

@[simp, to_dual self]
/--
theorem `Quiver.Hom.unop_mk` / 定理 `Quiver.Hom.unop_mk`

English:
theorem Quiver.Hom.unop_mk
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  statement: Quiver.Hom.unop { unop := f } = f
  proof: rfl

中文:
定理 Quiver.Hom.unop_mk
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  结论: Quiver.Hom.unop { unop := f } = f
  证明: rfl
-/
theorem Quiver.Hom.unop_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) : Quiver.Hom.unop { unop := f } = f :=
  rfl

end Quiver

namespace CategoryTheory

section

variable [CategoryStruct.{v₁} C]

/--
Instance `CategoryStruct.opposite` / 实例 `CategoryStruct.opposite`

English:
instance CategoryStruct.opposite
  signature: : CategoryStruct.{v₁} Cᵒᵖ where
  body: (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op

@[simp]

中文:
实例 CategoryStruct.opposite
  签名: : CategoryStruct.{v₁} Cᵒᵖ where
  定义体: (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op

@[simp]

Depends on / 依赖: f.unop, g.unop
-/
instance CategoryStruct.opposite : CategoryStruct.{v₁} Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op

@[simp]
/--
theorem `unop_id` / 定理 `unop_id`

English:
theorem unop_id
  given: {X : Cᵒᵖ}
  statement: (𝟙 X).unop = 𝟙 (unop X)
  proof: rfl

@[simp]

中文:
定理 unop_id
  条件: {X : Cᵒᵖ}
  结论: (𝟙 X).unop = 𝟙 (unop X)
  证明: rfl

@[simp]
-/
theorem unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) :=
  rfl

@[simp]
/--
theorem `op_id_unop` / 定理 `op_id_unop`

English:
theorem op_id_unop
  given: {X : Cᵒᵖ}
  statement: (𝟙 (unop X)).op = 𝟙 X
  proof: rfl

@[simp, grind _=_, to_dual self]

中文:
定理 op_id_unop
  条件: {X : Cᵒᵖ}
  结论: (𝟙 (unop X)).op = 𝟙 X
  证明: rfl

@[simp, grind _=_, to_dual self]
-/
theorem op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X :=
  rfl

@[simp, grind _=_, to_dual self]
/--
theorem `op_comp` / 定理 `op_comp`

English:
theorem op_comp
  given: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g).op = g.op ≫ f.op
  proof: rfl

@[simp]

中文:
定理 op_comp
  条件: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g).op = g.op ≫ f.op
  证明: rfl

@[simp]
-/
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op :=
  rfl

@[simp]
/--
theorem `op_id` / 定理 `op_id`

English:
theorem op_id
  given: {X : C}
  statement: (𝟙 X).op = 𝟙 (op X)
  proof: rfl

@[simp, to_dual self]

中文:
定理 op_id
  条件: {X : C}
  结论: (𝟙 X).op = 𝟙 (op X)
  证明: rfl

@[simp, to_dual self]
-/
theorem op_id {X : C} : (𝟙 X).op = 𝟙 (op X) :=
  rfl

@[simp, to_dual self]
/--
theorem `unop_comp` / 定理 `unop_comp`

English:
theorem unop_comp
  given: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g).unop = g.unop ≫ f.unop
  proof: rfl

@[simp]

中文:
定理 unop_comp
  条件: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g).unop = g.unop ≫ f.unop
  证明: rfl

@[simp]
-/
theorem unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ f.unop :=
  rfl

@[simp]
/--
theorem `unop_id_op` / 定理 `unop_id_op`

English:
theorem unop_id_op
  given: {X : C}
  statement: (𝟙 (op X)).unop = 𝟙 X
  proof: rfl

中文:
定理 unop_id_op
  条件: {X : C}
  结论: (𝟙 (op X)).unop = 𝟙 X
  证明: rfl
-/
theorem unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X :=
  rfl

-- This lemma is needed to prove `Category.opposite` below.
@[to_dual self]
/--
theorem `op_comp_unop` / 定理 `op_comp_unop`

English:
theorem op_comp_unop
  given: {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (g.unop ≫ f.unop).op = f ≫ g
  proof: rfl

中文:
定理 op_comp_unop
  条件: {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (g.unop ≫ f.unop).op = f ≫ g
  证明: rfl
-/
theorem op_comp_unop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) : (g.unop ≫ f.unop).op = f ≫ g :=
  rfl

end

open CategoryTheory.Functor

variable [Category.{v₁} C]

/-- The opposite category. -/
@[stacks 001M]
/--
Instance `Category.opposite` / 实例 `Category.opposite`

English:
instance Category.opposite
  signature: : Category.{v₁} Cᵒᵖ where
  body: CategoryStruct.opposite
  comp_id f := by rw [← op_comp_unop, unop_id, id_comp, Quiver.Hom.op_unop]
  id_comp f := by rw [← op_comp_unop, unop_id, comp_id, Quiver.Hom.op_unop]
  assoc f g h := by simp only [← op_comp_unop, Quiver.Hom.unop_op, assoc]

中文:
实例 Category.opposite
  签名: : Category.{v₁} Cᵒᵖ where
  定义体: CategoryStruct.opposite
  comp_id f := by rw [← op_comp_unop, unop_id, id_comp, Quiver.Hom.op_unop]
  id_comp f := by rw [← op_comp_unop, unop_id, comp_id, Quiver.Hom.op_unop]
  assoc f g h := by simp only [← op_comp_unop, Quiver.Hom.unop_op, assoc]

Depends on / 依赖: CategoryStruct, CategoryStruct.opposite, opposite
-/
instance Category.opposite : Category.{v₁} Cᵒᵖ where
  __ := CategoryStruct.opposite
  comp_id f := by rw [← op_comp_unop, unop_id, id_comp, Quiver.Hom.op_unop]
  id_comp f := by rw [← op_comp_unop, unop_id, comp_id, Quiver.Hom.op_unop]
  assoc f g h := by simp only [← op_comp_unop, Quiver.Hom.unop_op, assoc]

-- Note: these need to be proven manually as the original lemmas are only stated in terms
-- of `CategoryStruct`s!
@[to_dual none]
/--
theorem `op_comp_assoc` / 定理 `op_comp_assoc`

English:
theorem op_comp_assoc
  given: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'}
  proof: by
  simp only [op_comp, Category.assoc]

@[to_dual none]

中文:
定理 op_comp_assoc
  条件: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'}
  证明: by
  simp only [op_comp, Category.assoc]

@[to_dual none]

Depends on / 依赖: Category, Category.assoc, op_comp
-/
theorem op_comp_assoc {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'} :
    (f ≫ g).op ≫ h = g.op ≫ f.op ≫ h := by
  simp only [op_comp, Category.assoc]

@[to_dual none]
/--
theorem `unop_comp_assoc` / 定理 `unop_comp_assoc`

English:
theorem unop_comp_assoc
  given: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : C} {h : unop X ⟶ Z'}
  proof: by
  simp only [unop_comp, Category.assoc]

中文:
定理 unop_comp_assoc
  条件: {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : C} {h : unop X ⟶ Z'}
  证明: by
  simp only [unop_comp, Category.assoc]

Depends on / 依赖: Category, Category.assoc, unop_comp
-/
theorem unop_comp_assoc {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : C} {h : unop X ⟶ Z'} :
    (f ≫ g).unop ≫ h = g.unop ≫ f.unop ≫ h := by
  simp only [unop_comp, Category.assoc]

section

variable (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[implicit_reducible, simps]
/--
Definition of `unopUnop` / `unopUnop` 的定义

English:
definition unopUnop
  signature: : Cᵒᵖᵒᵖ ⥤ C where
  body: unop (unop X)
  map f := f.unop.unop

中文:
定义 unopUnop
  签名: : Cᵒᵖᵒᵖ ⥤ C where
  定义体: unop (unop X)
  map f := f.unop.unop
-/
def unopUnop : Cᵒᵖᵒᵖ ⥤ C where
  obj X := unop (unop X)
  map f := f.unop.unop

/-- The functor from a category to its double-opposite. -/
@[implicit_reducible, simps]
/--
Definition of `opOp` / `opOp` 的定义

English:
definition opOp
  signature: : C ⥤ Cᵒᵖᵒᵖ where
  body: op (op X)
  map f := f.op.op

中文:
定义 opOp
  签名: : C ⥤ Cᵒᵖᵒᵖ where
  定义体: op (op X)
  map f := f.op.op
-/
def opOp : C ⥤ Cᵒᵖᵒᵖ where
  obj X := op (op X)
  map f := f.op.op

/-- The double opposite category is equivalent to the original. -/
@[simps]
/--
Definition of `opOpEquivalence` / `opOpEquivalence` 的定义

English:
definition opOpEquivalence
  signature: : Cᵒᵖᵒᵖ ≌ C where
  body: unopUnop C
  inverse := opOp C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (opOp C ⋙ unopUnop C)

中文:
定义 opOpEquivalence
  签名: : Cᵒᵖᵒᵖ ≌ C where
  定义体: unopUnop C
  inverse := opOp C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (opOp C ⋙ unopUnop C)

Depends on / 依赖: unopUnop
-/
def opOpEquivalence : Cᵒᵖᵒᵖ ≌ C where
  functor := unopUnop C
  inverse := opOp C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (opOp C ⋙ unopUnop C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opOp C).IsEquivalence
  body: (opOpEquivalence C).isEquivalence_inverse

中文:
实例 :
  签名: (opOp C).IsEquivalence
  定义体: (opOpEquivalence C).isEquivalence_inverse

Depends on / 依赖: isEquivalence_inverse, opOpEquivalence
-/
instance : (opOp C).IsEquivalence :=
  (opOpEquivalence C).isEquivalence_inverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unopUnop C).IsEquivalence
  body: (opOpEquivalence C).isEquivalence_functor

中文:
实例 :
  签名: (unopUnop C).IsEquivalence
  定义体: (opOpEquivalence C).isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, opOpEquivalence
-/
instance : (unopUnop C).IsEquivalence :=
  (opOpEquivalence C).isEquivalence_functor

end

/-- If `f` is an isomorphism, so is `f.op` -/
@[to_dual self]
/--
Instance `isIso_op` / 实例 `isIso_op`

English:
instance isIso_op
  signature: {X Y : C} (f : X ⟶ Y) [IsIso f]
  body: ⟨⟨(inv f).op, ⟨Quiver.Hom.unop_inj (by simp), Quiver.Hom.unop_inj (by simp)⟩⟩⟩

中文:
实例 isIso_op
  签名: {X Y : C} (f : X ⟶ Y) [IsIso f]
  定义体: ⟨⟨(inv f).op, ⟨Quiver.Hom.unop_inj (by simp), Quiver.Hom.unop_inj (by simp)⟩⟩⟩

Depends on / 依赖: Quiver, Quiver.Hom.unop_inj, unop_inj
-/
instance isIso_op {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.op :=
  ⟨⟨(inv f).op, ⟨Quiver.Hom.unop_inj (by simp), Quiver.Hom.unop_inj (by simp)⟩⟩⟩

/-- If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
@[to_dual self]
/--
theorem `isIso_of_op` / 定理 `isIso_of_op`

English:
theorem isIso_of_op
  given: {X Y : C} (f : X ⟶ Y) [IsIso f.op]
  statement: IsIso f
  proof: ⟨⟨(inv f.op).unop, ⟨Quiver.Hom.op_inj (by simp), Quiver.Hom.op_inj (by simp)⟩⟩⟩

@[to_dual self]

中文:
定理 isIso_of_op
  条件: {X Y : C} (f : X ⟶ Y) [IsIso f.op]
  结论: IsIso f
  证明: ⟨⟨(inv f.op).unop, ⟨Quiver.Hom.op_inj (by simp), Quiver.Hom.op_inj (by simp)⟩⟩⟩

@[to_dual self]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, f.op, op_inj
-/
theorem isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.op] : IsIso f :=
  ⟨⟨(inv f.op).unop, ⟨Quiver.Hom.op_inj (by simp), Quiver.Hom.op_inj (by simp)⟩⟩⟩

@[to_dual self]
/--
theorem `isIso_op_iff` / 定理 `isIso_op_iff`

English:
theorem isIso_op_iff
  given: {X Y : C} (f : X ⟶ Y)
  statement: IsIso f.op ↔ IsIso f
  proof: ⟨fun _ => isIso_of_op _, fun _ => inferInstance⟩

@[to_dual self]

中文:
定理 isIso_op_iff
  条件: {X Y : C} (f : X ⟶ Y)
  结论: IsIso f.op ↔ IsIso f
  证明: ⟨fun _ => isIso_of_op _, fun _ => inferInstance⟩

@[to_dual self]

Depends on / 依赖: isIso_of_op
-/
theorem isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso f.op ↔ IsIso f :=
  ⟨fun _ => isIso_of_op _, fun _ => inferInstance⟩

@[to_dual self]
/--
theorem `isIso_unop_iff` / 定理 `isIso_unop_iff`

English:
theorem isIso_unop_iff
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  statement: IsIso f.unop ↔ IsIso f
  proof: by
  rw [← isIso_op_iff f.unop]; rw [Quiver.Hom.op_unop]

@[to_dual self]

中文:
定理 isIso_unop_iff
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  结论: IsIso f.unop ↔ IsIso f
  证明: by
  rw [← isIso_op_iff f.unop]; rw [Quiver.Hom.op_unop]

@[to_dual self]

Depends on / 依赖: Quiver, Quiver.Hom.op_unop, f.unop, isIso_op_iff, op_unop
-/
theorem isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso f.unop ↔ IsIso f := by
  rw [← isIso_op_iff f.unop]; rw [Quiver.Hom.op_unop]

@[to_dual self]
/--
Instance `isIso_unop` / 实例 `isIso_unop`

English:
instance isIso_unop
  signature: {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f]
  body: (isIso_unop_iff _).2 inferInstance

@[simp, push ←, to_dual self]

中文:
实例 isIso_unop
  签名: {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f]
  定义体: (isIso_unop_iff _).2 inferInstance

@[simp, push ←, to_dual self]

Depends on / 依赖: isIso_unop_iff
-/
instance isIso_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unop :=
  (isIso_unop_iff _).2 inferInstance

@[simp, push ←, to_dual self]
/--
theorem `op_inv` / 定理 `op_inv`

English:
theorem op_inv
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: (inv f).op = inv f.op
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← op_comp]; rw [IsIso.inv_hom_id]; rw [op_id]

@[simp, push ←, to_dual self]

中文:
定理 op_inv
  条件: {X Y : C} (f : X ⟶ Y) [IsIso f]
  结论: (inv f).op = inv f.op
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← op_comp]; rw [IsIso.inv_hom_id]; rw [op_id]

@[simp, push ←, to_dual self]

Depends on / 依赖: IsIso.eq_inv_of_hom_inv_id, IsIso.inv_hom_id, eq_inv_of_hom_inv_id, inv_hom_id, op_comp, op_id
-/
theorem op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).op = inv f.op := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← op_comp]; rw [IsIso.inv_hom_id]; rw [op_id]

@[simp, push ←, to_dual self]
/--
theorem `unop_inv` / 定理 `unop_inv`

English:
theorem unop_inv
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f]
  statement: (inv f).unop = inv f.unop
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← unop_comp]; rw [IsIso.inv_hom_id]; rw [unop_id]

中文:
定理 unop_inv
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f]
  结论: (inv f).unop = inv f.unop
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← unop_comp]; rw [IsIso.inv_hom_id]; rw [unop_id]

Depends on / 依赖: IsIso.eq_inv_of_hom_inv_id, IsIso.inv_hom_id, eq_inv_of_hom_inv_id, inv_hom_id, unop_comp, unop_id
-/
theorem unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (inv f).unop = inv f.unop := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← unop_comp]; rw [IsIso.inv_hom_id]; rw [unop_id]

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D]

/-- The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these. -/
@[simps, implicit_reducible]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (F : C ⥤ D)
  body: op (F.obj (unop X))
  map f := (F.map f.unop).op

中文:
定义 op
  签名: (F : C ⥤ D)
  定义体: op (F.obj (unop X))
  map f := (F.map f.unop).op
-/
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj X := op (F.obj (unop X))
  map f := (F.map f.unop).op

/-- Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps, implicit_reducible]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  body: unop (F.obj (op X))
  map f := (F.map f.op).unop

中文:
定义 unop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  定义体: unop (F.obj (op X))
  map f := (F.map f.op).unop
-/
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj X := unop (F.obj (op X))
  map f := (F.map f.op).unop

/-- The isomorphism between `F.op.unop` and `F`. -/
@[simps!]
/--
Definition of `opUnopIso` / `opUnopIso` 的定义

English:
definition opUnopIso
  signature: (F : C ⥤ D)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 opUnopIso
  签名: (F : C ⥤ D)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def opUnopIso (F : C ⥤ D) : F.op.unop ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The isomorphism between `F.unop.op` and `F`. -/
@[simps!]
/--
Definition of `unopOpIso` / `unopOpIso` 的定义

English:
definition unopOpIso
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 unopOpIso
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def unopOpIso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

variable (C D)

/-- Taking the opposite of a functor is functorial.
-/
@[implicit_reducible, simps]
/--
Definition of `opHom` / `opHom` 的定义

English:
definition opHom
  signature: : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  body: (unop F).op
  map α :=
    { app := fun X => (α.unop.app (unop X)).op
      naturality := fun _ _ f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }

中文:
定义 opHom
  签名: : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  定义体: (unop F).op
  map α :=
    { app := fun X => (α.unop.app (unop X)).op
      naturality := fun _ _ f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }
-/
def opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  obj F := (unop F).op
  map α :=
    { app := fun X => (α.unop.app (unop X)).op
      naturality := fun _ _ f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }

/-- Take the "unopposite" of a functor is functorial.
-/
@[implicit_reducible, simps]
/--
Definition of `opInv` / `opInv` 的定义

English:
definition opInv
  signature: : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  body: op F.unop
  map α :=
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop
naturality := fun _ _ f => Quiver.Hom.op_inj (α.naturality f.op).symm }

中文:
定义 opInv
  签名: : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  定义体: op F.unop
  map α :=
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop
naturality := fun _ _ f => Quiver.Hom.op_inj (α.naturality f.op).symm }

Depends on / 依赖: F.unop
-/
def opInv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  obj F := op F.unop
  map α :=
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop
naturality := fun _ _ f => Quiver.Hom.op_inj (α.naturality f.op).symm }

variable {C D}

section Compositions

variable {E : Type*} [Category* E]

/-- Compatibility of `Functor.op` with respect to functor composition. -/
@[simps!]
/--
Definition of `opComp` / `opComp` 的定义

English:
definition opComp
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: Iso.refl _

中文:
定义 opComp
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def opComp (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op ≅ F.op ⋙ G.op := Iso.refl _

/-- Compatibility of `Functor.unop` with respect to functor composition. -/
@[simps!]
/--
Definition of `unopComp` / `unopComp` 的定义

English:
definition unopComp
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ)
  body: Iso.refl _

中文:
定义 unopComp
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def unopComp (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ) : (F ⋙ G).unop ≅ F.unop ⋙ G.unop := Iso.refl _

variable (C) in
/-- `Functor.op` transforms identity functors to identity functors. -/
@[simps!]
/--
Definition of `opId` / `opId` 的定义

English:
definition opId
  signature: : (𝟭 C).op ≅ 𝟭 (Cᵒᵖ)
  body: Iso.refl _

中文:
定义 opId
  签名: : (𝟭 C).op ≅ 𝟭 (Cᵒᵖ)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def opId : (𝟭 C).op ≅ 𝟭 (Cᵒᵖ) := Iso.refl _

variable (C) in
/-- `Functor.unop` transforms identity functors to identity functors. -/
@[simps!]
/--
Definition of `unopId` / `unopId` 的定义

English:
definition unopId
  signature: : (𝟭 Cᵒᵖ).unop ≅ 𝟭 C
  body: Iso.refl _

中文:
定义 unopId
  签名: : (𝟭 Cᵒᵖ).unop ≅ 𝟭 C
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def unopId : (𝟭 Cᵒᵖ).unop ≅ 𝟭 C := Iso.refl _

end Compositions

/--
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[implicit_reducible, simps]
/--
Definition of `leftOp` / `leftOp` 的定义

English:
definition leftOp
  signature: (F : C ⥤ Dᵒᵖ)
  body: unop (F.obj (unop X))
  map f := (F.map f.unop).unop

中文:
定义 leftOp
  签名: (F : C ⥤ Dᵒᵖ)
  定义体: unop (F.obj (unop X))
  map f := (F.map f.unop).unop
-/
protected def leftOp (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D where
  obj X := unop (F.obj (unop X))
  map f := (F.map f.unop).unop

/--
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[implicit_reducible, simps]
/--
Definition of `rightOp` / `rightOp` 的定义

English:
definition rightOp
  signature: (F : Cᵒᵖ ⥤ D)
  body: op (F.obj (op X))
  map f := (F.map f.op).op

中文:
定义 rightOp
  签名: (F : Cᵒᵖ ⥤ D)
  定义体: op (F.obj (op X))
  map f := (F.map f.op).op
-/
protected def rightOp (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj X := op (F.obj (op X))
  map f := (F.map f.op).op

/--
lemma `rightOp_map_unop` / 引理 `rightOp_map_unop`

English:
lemma rightOp_map_unop
  given: {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y)
  proof: rfl

中文:
引理 rightOp_map_unop
  条件: {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y)
  证明: rfl
-/
lemma rightOp_map_unop {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y) :
    (F.rightOp.map f).unop = F.map f.op := rfl

instance {F : C ⥤ D} [Full F] : Full F.op where
  map_surjective f := ⟨(F.preimage f.unop).op, by simp⟩

instance {F : C ⥤ D} [Faithful F] : Faithful F.op where
map_injective h := Quiver.Hom.unop_inj by simpa using map_injective F (Quiver.Hom.op_inj h)

/--
Definition of `FullyFaithful.op` / `FullyFaithful.op` 的定义

English:
definition FullyFaithful.op
  signature: {F : C ⥤ D} (hF : F.FullyFaithful)
  body: .op hF.preimage f.unop

中文:
定义 FullyFaithful.op
  签名: {F : C ⥤ D} (hF : F.FullyFaithful)
  定义体: .op hF.preimage f.unop
-/
protected def FullyFaithful.op {F : C ⥤ D} (hF : F.FullyFaithful) : F.op.FullyFaithful where
preimage {X Y} f := .op hF.preimage f.unop

/--
Definition of `FullyFaithful.unop` / `FullyFaithful.unop` 的定义

English:
definition FullyFaithful.unop
  signature: {F : Cᵒᵖ ⥤ Dᵒᵖ} (hF : F.FullyFaithful)
  body: (hF.preimage f.op).unop

中文:
定义 FullyFaithful.unop
  签名: {F : Cᵒᵖ ⥤ Dᵒᵖ} (hF : F.FullyFaithful)
  定义体: (hF.preimage f.op).unop
-/
protected def FullyFaithful.unop {F : Cᵒᵖ ⥤ Dᵒᵖ} (hF : F.FullyFaithful) :
    F.unop.FullyFaithful where
  preimage {X Y} f := (hF.preimage f.op).unop

/--
Instance `rightOp_faithful` / 实例 `rightOp_faithful`

English:
instance rightOp_faithful
  signature: {F : Cᵒᵖ ⥤ D} [Faithful F]
  body: Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

中文:
实例 rightOp_faithful
  签名: {F : Cᵒᵖ ⥤ D} [Faithful F]
  定义体: Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, map_injective, op_inj
-/
instance rightOp_faithful {F : Cᵒᵖ ⥤ D} [Faithful F] : Faithful F.rightOp where
  map_injective h := Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

/--
Instance `leftOp_faithful` / 实例 `leftOp_faithful`

English:
instance leftOp_faithful
  signature: {F : C ⥤ Dᵒᵖ} [Faithful F]
  body: Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))

中文:
实例 leftOp_faithful
  签名: {F : C ⥤ Dᵒᵖ} [Faithful F]
  定义体: Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))

Depends on / 依赖: Quiver, Quiver.Hom.unop_inj, map_injective, unop_inj
-/
instance leftOp_faithful {F : C ⥤ Dᵒᵖ} [Faithful F] : Faithful F.leftOp where
  map_injective h := Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))

/--
Instance `rightOp_full` / 实例 `rightOp_full`

English:
instance rightOp_full
  signature: {F : Cᵒᵖ ⥤ D} [Full F]
  body: ⟨(F.preimage f.unop).unop, by simp⟩

中文:
实例 rightOp_full
  签名: {F : Cᵒᵖ ⥤ D} [Full F]
  定义体: ⟨(F.preimage f.unop).unop, by simp⟩

Depends on / 依赖: F.preimage, f.unop, preimage
-/
instance rightOp_full {F : Cᵒᵖ ⥤ D} [Full F] : Full F.rightOp where
  map_surjective f := ⟨(F.preimage f.unop).unop, by simp⟩

/--
Instance `leftOp_full` / 实例 `leftOp_full`

English:
instance leftOp_full
  signature: {F : C ⥤ Dᵒᵖ} [Full F]
  body: ⟨(F.preimage f.op).op, by simp⟩

中文:
实例 leftOp_full
  签名: {F : C ⥤ Dᵒᵖ} [Full F]
  定义体: ⟨(F.preimage f.op).op, by simp⟩

Depends on / 依赖: F.preimage, f.op, preimage
-/
instance leftOp_full {F : C ⥤ Dᵒᵖ} [Full F] : Full F.leftOp where
  map_surjective f := ⟨(F.preimage f.op).op, by simp⟩

/--
Definition of `FullyFaithful.leftOp` / `FullyFaithful.leftOp` 的定义

English:
definition FullyFaithful.leftOp
  signature: {F : C ⥤ Dᵒᵖ} (hF : F.FullyFaithful)
  body: .op hF.preimage f.op

中文:
定义 FullyFaithful.leftOp
  签名: {F : C ⥤ Dᵒᵖ} (hF : F.FullyFaithful)
  定义体: .op hF.preimage f.op
-/
protected def FullyFaithful.leftOp {F : C ⥤ Dᵒᵖ} (hF : F.FullyFaithful) :
    F.leftOp.FullyFaithful where
preimage {X Y} f := .op hF.preimage f.op

/--
Definition of `FullyFaithful.rightOp` / `FullyFaithful.rightOp` 的定义

English:
definition FullyFaithful.rightOp
  signature: {F : Cᵒᵖ ⥤ D} (hF : F.FullyFaithful)
  body: .unop hF.preimage f.unop

中文:
定义 FullyFaithful.rightOp
  签名: {F : Cᵒᵖ ⥤ D} (hF : F.FullyFaithful)
  定义体: .unop hF.preimage f.unop
-/
protected def FullyFaithful.rightOp {F : Cᵒᵖ ⥤ D} (hF : F.FullyFaithful) :
    F.rightOp.FullyFaithful where
preimage {X Y} f := .unop hF.preimage f.unop

/-- Compatibility of `Functor.rightOp` with respect to functor composition. -/
@[simps!]
/--
Definition of `rightOpComp` / `rightOpComp` 的定义

English:
definition rightOpComp
  signature: {E : Type*} [Category* E] (F : Cᵒᵖ ⥤ D) (G : D ⥤ E)
  body: Iso.refl _

中文:
定义 rightOpComp
  签名: {E : 类型} [Category* E] (F : Cᵒᵖ ⥤ D) (G : D ⥤ E)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def rightOpComp {E : Type*} [Category* E] (F : Cᵒᵖ ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).rightOp ≅ F.rightOp ⋙ G.op :=
  Iso.refl _

/-- Compatibility of `Functor.leftOp` with respect to functor composition. -/
@[simps!]
/--
Definition of `leftOpComp` / `leftOpComp` 的定义

English:
definition leftOpComp
  signature: {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ Eᵒᵖ)
  body: Iso.refl _

中文:
定义 leftOpComp
  签名: {E : 类型} [Category* E] (F : C ⥤ D) (G : D ⥤ Eᵒᵖ)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def leftOpComp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ Eᵒᵖ) :
    (F ⋙ G).leftOp ≅ F.op ⋙ G.leftOp :=
  Iso.refl _

section
variable (C)

/-- `Functor.rightOp` sends identity functors to the canonical isomorphism `opOp`. -/
@[simps!]
/--
Definition of `rightOpId` / `rightOpId` 的定义

English:
definition rightOpId
  signature: : (𝟭 Cᵒᵖ).rightOp ≅ opOp C
  body: Iso.refl _

中文:
定义 rightOpId
  签名: : (𝟭 Cᵒᵖ).rightOp ≅ opOp C
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def rightOpId : (𝟭 Cᵒᵖ).rightOp ≅ opOp C := Iso.refl _

/-- `Functor.leftOp` sends identity functors to the canonical isomorphism `unopUnop`. -/
@[simps!]
/--
Definition of `leftOpId` / `leftOpId` 的定义

English:
definition leftOpId
  signature: : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C
  body: Iso.refl _

中文:
定义 leftOpId
  签名: : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def leftOpId : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C := Iso.refl _

end

/-- The isomorphism between `F.leftOp.rightOp` and `F`. -/
@[simps!]
/--
Definition of `leftOpRightOpIso` / `leftOpRightOpIso` 的定义

English:
definition leftOpRightOpIso
  signature: (F : C ⥤ Dᵒᵖ)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 leftOpRightOpIso
  签名: (F : C ⥤ Dᵒᵖ)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def leftOpRightOpIso (F : C ⥤ Dᵒᵖ) : F.leftOp.rightOp ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The isomorphism between `F.rightOp.leftOp` and `F`. -/
@[simps!]
/--
Definition of `rightOpLeftOpIso` / `rightOpLeftOpIso` 的定义

English:
definition rightOpLeftOpIso
  signature: (F : Cᵒᵖ ⥤ D)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 rightOpLeftOpIso
  签名: (F : Cᵒᵖ ⥤ D)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def rightOpLeftOpIso (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/--
theorem `rightOp_leftOp_eq` / 定理 `rightOp_leftOp_eq`

English:
theorem rightOp_leftOp_eq
  given: (F : Cᵒᵖ ⥤ D)
  statement: F.rightOp.leftOp = F
  proof: by
  cases F
  rfl

中文:
定理 rightOp_leftOp_eq
  条件: (F : Cᵒᵖ ⥤ D)
  结论: F.rightOp.leftOp = F
  证明: by
  cases F
  rfl
-/
theorem rightOp_leftOp_eq (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp = F := by
  cases F
  rfl

end

end Functor

namespace NatTrans

variable {D : Type u₂} [Category.{v₂} D]

section

variable {F G : C ⥤ D}

/-- The opposite of a natural transformation. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (α : F ⟶ G)
  body: (α.app (unop X)).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]

中文:
定义 op
  签名: (α : F ⟶ G)
  定义体: (α.app (unop X)).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
-/
protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app X := (α.app (unop X)).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
/--
theorem `op_id` / 定理 `op_id`

English:
theorem op_id
  given: (F : C ⥤ D)
  statement: NatTrans.op (𝟙 F) = 𝟙 F.op
  proof: rfl

@[simp, to_dual self, reassoc]

中文:
定理 op_id
  条件: (F : C ⥤ D)
  结论: 自然数Trans.op (𝟙 F) = 𝟙 F.op
  证明: rfl

@[simp, to_dual self, reassoc]
-/
theorem op_id (F : C ⥤ D) : NatTrans.op (𝟙 F) = 𝟙 F.op :=
  rfl

@[simp, to_dual self, reassoc]
/--
theorem `op_comp` / 定理 `op_comp`

English:
theorem op_comp
  given: {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
  proof: rfl

@[to_dual none, reassoc]

中文:
定理 op_comp
  条件: {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
  证明: rfl

@[to_dual none, reassoc]
-/
theorem op_comp {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.op (α ≫ β) = NatTrans.op β ≫ NatTrans.op α :=
  rfl

@[to_dual none, reassoc]
/--
lemma `op_whiskerRight` / 引理 `op_whiskerRight`

English:
lemma op_whiskerRight
  given: {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G)
  proof: by
  cat_disch

@[to_dual none, reassoc]

中文:
引理 op_whiskerRight
  条件: {E : 类型} [Category* E] {H : D ⥤ E} (α : F ⟶ G)
  证明: by
  cat_disch

@[to_dual none, reassoc]

Depends on / 依赖: cat_disch
-/
lemma op_whiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G) :
    NatTrans.op (whiskerRight α H) =
    (Functor.opComp _ _).hom ≫ whiskerRight (NatTrans.op α) H.op ≫ (Functor.opComp _ _).inv := by
  cat_disch

@[to_dual none, reassoc]
/--
lemma `op_whiskerLeft` / 引理 `op_whiskerLeft`

English:
lemma op_whiskerLeft
  given: {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G)
  proof: by
  cat_disch

中文:
引理 op_whiskerLeft
  条件: {E : 类型} [Category* E] {H : E ⥤ C} (α : F ⟶ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma op_whiskerLeft {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G) :
    NatTrans.op (whiskerLeft H α) =
    (Functor.opComp _ _).hom ≫ whiskerLeft H.op (NatTrans.op α) ≫ (Functor.opComp _ _).inv := by
  cat_disch

/-- The "unopposite" of a natural transformation. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G)
  body: (α.app (op X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]

中文:
定义 unop
  签名: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G)
  定义体: (α.app (op X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
-/
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop where
  app X := (α.app (op X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
/--
theorem `unop_id` / 定理 `unop_id`

English:
theorem unop_id
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  statement: NatTrans.unop (𝟙 F) = 𝟙 F.unop
  proof: rfl

@[simp, to_dual self, reassoc]

中文:
定理 unop_id
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  结论: 自然数Trans.unop (𝟙 F) = 𝟙 F.unop
  证明: rfl

@[simp, to_dual self, reassoc]
-/
theorem unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.unop (𝟙 F) = 𝟙 F.unop :=
  rfl

@[simp, to_dual self, reassoc]
/--
theorem `unop_comp` / 定理 `unop_comp`

English:
theorem unop_comp
  given: {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (β : G ⟶ H)
  proof: rfl

@[to_dual none, reassoc]

中文:
定理 unop_comp
  条件: {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (β : G ⟶ H)
  证明: rfl

@[to_dual none, reassoc]
-/
theorem unop_comp {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.unop (α ≫ β) = NatTrans.unop β ≫ NatTrans.unop α :=
  rfl

@[to_dual none, reassoc]
/--
lemma `unop_whiskerRight` / 引理 `unop_whiskerRight`

English:
lemma unop_whiskerRight
  given: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ⟶ G)
  proof: by
  cat_disch

@[to_dual none, reassoc]

中文:
引理 unop_whiskerRight
  条件: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : 类型} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ⟶ G)
  证明: by
  cat_disch

@[to_dual none, reassoc]

Depends on / 依赖: cat_disch
-/
lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ⟶ G) :
    NatTrans.unop (whiskerRight α H) =
    (Functor.unopComp _ _).hom ≫ whiskerRight (NatTrans.unop α) H.unop ≫
      (Functor.unopComp _ _).inv := by
  cat_disch

@[to_dual none, reassoc]
/--
lemma `unop_whiskerLeft` / 引理 `unop_whiskerLeft`

English:
lemma unop_whiskerLeft
  given: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ⟶ G)
  proof: by
  cat_disch

中文:
引理 unop_whiskerLeft
  条件: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : 类型} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ⟶ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ⟶ G) :
    NatTrans.unop (whiskerLeft H α) =
    (Functor.unopComp _ _).hom ≫ whiskerLeft H.unop (NatTrans.unop α) ≫
      (Functor.unopComp _ _).inv := by
  cat_disch

/-- Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `removeOp` / `removeOp` 的定义

English:
definition removeOp
  signature: (α : F.op ⟶ G.op)
  body: (α.app (op X)).unop
  naturality X Y f :=
Quiver.Hom.op_inj by simpa only [Functor.op_map] using! (α.naturality f.op).symm

@[simp]

中文:
定义 removeOp
  签名: (α : F.op ⟶ G.op)
  定义体: (α.app (op X)).unop
  naturality X Y f :=
Quiver.Hom.op_inj by simpa only [Functor.op_map] using! (α.naturality f.op).symm

@[simp]
-/
protected def removeOp (α : F.op ⟶ G.op) : G ⟶ F where
  app X := (α.app (op X)).unop
  naturality X Y f :=
Quiver.Hom.op_inj by simpa only [Functor.op_map] using! (α.naturality f.op).symm

@[simp]
/--
theorem `removeOp_id` / 定理 `removeOp_id`

English:
theorem removeOp_id
  given: (F : C ⥤ D)
  statement: NatTrans.removeOp (𝟙 F.op) = 𝟙 F
  proof: rfl

中文:
定理 removeOp_id
  条件: (F : C ⥤ D)
  结论: 自然数Trans.removeOp (𝟙 F.op) = 𝟙 F
  证明: rfl
-/
theorem removeOp_id (F : C ⥤ D) : NatTrans.removeOp (𝟙 F.op) = 𝟙 F :=
  rfl

/-- Given a natural transformation `α : F.unop ⟶ G.unop`, we can take the opposite of each
component obtaining a natural transformation `G ⟶ F`. -/
@[implicit_reducible, simps, to_dual self]
/--
Definition of `removeUnop` / `removeUnop` 的定义

English:
definition removeUnop
  signature: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop)
  body: (α.app (unop X)).op
  naturality X Y f :=
Quiver.Hom.unop_inj by simpa only [Functor.unop_map] using! (α.naturality f.unop).symm

@[simp]

中文:
定义 removeUnop
  签名: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop)
  定义体: (α.app (unop X)).op
  naturality X Y f :=
Quiver.Hom.unop_inj by simpa only [Functor.unop_map] using! (α.naturality f.unop).symm

@[simp]
-/
protected def removeUnop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop) : G ⟶ F where
  app X := (α.app (unop X)).op
  naturality X Y f :=
Quiver.Hom.unop_inj by simpa only [Functor.unop_map] using! (α.naturality f.unop).symm

@[simp]
/--
theorem `removeUnop_id` / 定理 `removeUnop_id`

English:
theorem removeUnop_id
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  statement: NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F
  proof: rfl

中文:
定理 removeUnop_id
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  结论: 自然数Trans.removeUnop (𝟙 F.unop) = 𝟙 F
  证明: rfl
-/
theorem removeUnop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F :=
  rfl

end

section

variable {F G H : C ⥤ Dᵒᵖ}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.leftOp ⟶ F.leftOp`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `leftOp` / `leftOp` 的定义

English:
definition leftOp
  signature: (α : F ⟶ G)
  body: (α.app (unop X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]

中文:
定义 leftOp
  签名: (α : F ⟶ G)
  定义体: (α.app (unop X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
-/
protected def leftOp (α : F ⟶ G) : G.leftOp ⟶ F.leftOp where
  app X := (α.app (unop X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
/--
theorem `leftOp_id` / 定理 `leftOp_id`

English:
theorem leftOp_id
  statement: NatTrans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp
  proof: rfl

@[simp, to_dual self]

中文:
定理 leftOp_id
  结论: 自然数Trans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp
  证明: rfl

@[simp, to_dual self]
-/
theorem leftOp_id : NatTrans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp :=
  rfl

@[simp, to_dual self]
/--
theorem `leftOp_comp` / 定理 `leftOp_comp`

English:
theorem leftOp_comp
  given: (α : F ⟶ G) (β : G ⟶ H)
  statement: NatTrans.leftOp (α ≫ β) =
  proof: rfl

@[to_dual none, reassoc]

中文:
定理 leftOp_comp
  条件: (α : F ⟶ G) (β : G ⟶ H)
  结论: 自然数Trans.leftOp (α ≫ β) =
  证明: rfl

@[to_dual none, reassoc]
-/
theorem leftOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.leftOp (α ≫ β) =
    NatTrans.leftOp β ≫ NatTrans.leftOp α :=
  rfl

@[to_dual none, reassoc]
/--
lemma `leftOpWhiskerRight` / 引理 `leftOpWhiskerRight`

English:
lemma leftOpWhiskerRight
  given: {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G)
  proof: by
  cat_disch

中文:
引理 leftOpWhiskerRight
  条件: {E : 类型} [Category* E] {H : E ⥤ C} (α : F ⟶ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma leftOpWhiskerRight {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G) :
    (whiskerLeft H α).leftOp = (Functor.leftOpComp H G).hom ≫ whiskerLeft _ α.leftOp ≫
      (Functor.leftOpComp H F).inv := by
  cat_disch

/-- Given a natural transformation `α : F.leftOp ⟶ G.leftOp`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `removeLeftOp` / `removeLeftOp` 的定义

English:
definition removeLeftOp
  signature: (α : F.leftOp ⟶ G.leftOp)
  body: (α.app (op X)).op
  naturality X Y f :=
Quiver.Hom.unop_inj by simpa only [Functor.leftOp_map] using! (α.naturality f.op).symm

@[simp]

中文:
定义 removeLeftOp
  签名: (α : F.leftOp ⟶ G.leftOp)
  定义体: (α.app (op X)).op
  naturality X Y f :=
Quiver.Hom.unop_inj by simpa only [Functor.leftOp_map] using! (α.naturality f.op).symm

@[simp]
-/
protected def removeLeftOp (α : F.leftOp ⟶ G.leftOp) : G ⟶ F where
  app X := (α.app (op X)).op
  naturality X Y f :=
Quiver.Hom.unop_inj by simpa only [Functor.leftOp_map] using! (α.naturality f.op).symm

@[simp]
/--
theorem `removeLeftOp_id` / 定理 `removeLeftOp_id`

English:
theorem removeLeftOp_id
  statement: NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F
  proof: rfl

中文:
定理 removeLeftOp_id
  结论: 自然数Trans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F
  证明: rfl
-/
theorem removeLeftOp_id : NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F :=
  rfl

end

section

variable {F G H : Cᵒᵖ ⥤ D}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.rightOp ⟶ F.rightOp`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `rightOp` / `rightOp` 的定义

English:
definition rightOp
  signature: (α : F ⟶ G)
  body: (α.app _).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]

中文:
定义 rightOp
  签名: (α : F ⟶ G)
  定义体: (α.app _).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
-/
protected def rightOp (α : F ⟶ G) : G.rightOp ⟶ F.rightOp where
  app _ := (α.app _).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
/--
theorem `rightOp_id` / 定理 `rightOp_id`

English:
theorem rightOp_id
  statement: NatTrans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp
  proof: rfl

@[simp, to_dual self]

中文:
定理 rightOp_id
  结论: 自然数Trans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp
  证明: rfl

@[simp, to_dual self]
-/
theorem rightOp_id : NatTrans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp :=
  rfl

@[simp, to_dual self]
/--
theorem `rightOp_comp` / 定理 `rightOp_comp`

English:
theorem rightOp_comp
  given: (α : F ⟶ G) (β : G ⟶ H)
  statement: NatTrans.rightOp (α ≫ β) =
  proof: rfl

@[to_dual none, reassoc]

中文:
定理 rightOp_comp
  条件: (α : F ⟶ G) (β : G ⟶ H)
  结论: 自然数Trans.rightOp (α ≫ β) =
  证明: rfl

@[to_dual none, reassoc]
-/
theorem rightOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.rightOp (α ≫ β) =
    NatTrans.rightOp β ≫ NatTrans.rightOp α :=
  rfl

@[to_dual none, reassoc]
/--
lemma `rightOpWhiskerRight` / 引理 `rightOpWhiskerRight`

English:
lemma rightOpWhiskerRight
  given: {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G)
  proof: by
  cat_disch

中文:
引理 rightOpWhiskerRight
  条件: {E : 类型} [Category* E] {H : D ⥤ E} (α : F ⟶ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma rightOpWhiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G) :
    (whiskerRight α H).rightOp = (Functor.rightOpComp G H).hom ≫ whiskerRight α.rightOp H.op ≫
      (Functor.rightOpComp F H).inv := by
  cat_disch

/-- Given a natural transformation `α : F.rightOp ⟶ G.rightOp`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/--
Definition of `removeRightOp` / `removeRightOp` 的定义

English:
definition removeRightOp
  signature: (α : F.rightOp ⟶ G.rightOp)
  body: (α.app X.unop).unop
  naturality X Y f :=
Quiver.Hom.op_inj by simpa only [Functor.rightOp_map] using! (α.naturality f.unop).symm

@[simp]

中文:
定义 removeRightOp
  签名: (α : F.rightOp ⟶ G.rightOp)
  定义体: (α.app X.unop).unop
  naturality X Y f :=
Quiver.Hom.op_inj by simpa only [Functor.rightOp_map] using! (α.naturality f.unop).symm

@[simp]
-/
protected def removeRightOp (α : F.rightOp ⟶ G.rightOp) : G ⟶ F where
  app X := (α.app X.unop).unop
  naturality X Y f :=
Quiver.Hom.op_inj by simpa only [Functor.rightOp_map] using! (α.naturality f.unop).symm

@[simp]
/--
theorem `removeRightOp_id` / 定理 `removeRightOp_id`

English:
theorem removeRightOp_id
  statement: NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F
  proof: rfl

中文:
定理 removeRightOp_id
  结论: 自然数Trans.removeRightOp (𝟙 F.rightOp) = 𝟙 F
  证明: rfl
-/
theorem removeRightOp_id : NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F :=
  rfl

end

end NatTrans

namespace Iso

variable {X Y : C}

/-- The opposite isomorphism.
-/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (α : X ≅ Y)
  body: α.hom.op
  inv := α.inv.op
  hom_inv_id := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id := Quiver.Hom.unop_inj α.hom_inv_id

中文:
定义 op
  签名: (α : X ≅ Y)
  定义体: α.hom.op
  inv := α.inv.op
  hom_inv_id := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id := Quiver.Hom.unop_inj α.hom_inv_id
-/
protected def op (α : X ≅ Y) : op Y ≅ op X where
  hom := α.hom.op
  inv := α.inv.op
  hom_inv_id := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id := Quiver.Hom.unop_inj α.hom_inv_id

/-- The isomorphism obtained from an isomorphism in the opposite category. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {X Y : Cᵒᵖ} (f : X ≅ Y)
  body: f.hom.unop
  inv := f.inv.unop
  hom_inv_id := by simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id := by simp only [← unop_comp, f.hom_inv_id, unop_id]

@[simp]

中文:
定义 unop
  签名: {X Y : Cᵒᵖ} (f : X ≅ Y)
  定义体: f.hom.unop
  inv := f.inv.unop
  hom_inv_id := by simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id := by simp only [← unop_comp, f.hom_inv_id, unop_id]

@[simp]

Depends on / 依赖: f.hom.unop
-/
def unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where
  hom := f.hom.unop
  inv := f.inv.unop
  hom_inv_id := by simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id := by simp only [← unop_comp, f.hom_inv_id, unop_id]

@[simp]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: {X Y : Cᵒᵖ} (f : X ≅ Y)
  statement: f.unop.op = f
  proof: by (ext; rfl)

@[simp]

中文:
定理 unop_op
  条件: {X Y : Cᵒᵖ} (f : X ≅ Y)
  结论: f.unop.op = f
  证明: by (ext; rfl)

@[simp]
-/
theorem unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f := by (ext; rfl)

@[simp]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: {X Y : C} (f : X ≅ Y)
  statement: f.op.unop = f
  proof: by (ext; rfl)

中文:
定理 op_unop
  条件: {X Y : C} (f : X ≅ Y)
  结论: f.op.unop = f
  证明: by (ext; rfl)
-/
theorem op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f := by (ext; rfl)

variable (X) in
@[simp]
/--
theorem `op_refl` / 定理 `op_refl`

English:
theorem op_refl
  statement: Iso.op (Iso.refl X) = Iso.refl (op X)
  proof: rfl

@[simp]

中文:
定理 op_refl
  结论: Iso.op (Iso.refl X) = Iso.refl (op X)
  证明: rfl

@[simp]
-/
theorem op_refl : Iso.op (Iso.refl X) = Iso.refl (op X) := rfl

@[simp]
/--
theorem `op_trans` / 定理 `op_trans`

English:
theorem op_trans
  given: {Z : C} (α : X ≅ Y) (β : Y ≅ Z)
  proof: rfl

@[simp]

中文:
定理 op_trans
  条件: {Z : C} (α : X ≅ Y) (β : Y ≅ Z)
  证明: rfl

@[simp]
-/
theorem op_trans {Z : C} (α : X ≅ Y) (β : Y ≅ Z) :
    Iso.op (α ≪≫ β) = Iso.op β ≪≫ Iso.op α :=
  rfl

@[simp]
/--
theorem `op_symm` / 定理 `op_symm`

English:
theorem op_symm
  given: (α : X ≅ Y)
  statement: Iso.op α.symm = (Iso.op α).symm
  proof: rfl

@[simp]

中文:
定理 op_symm
  条件: (α : X ≅ Y)
  结论: Iso.op α.symm = (Iso.op α).symm
  证明: rfl

@[simp]
-/
theorem op_symm (α : X ≅ Y) : Iso.op α.symm = (Iso.op α).symm := rfl

@[simp]
/--
theorem `unop_refl` / 定理 `unop_refl`

English:
theorem unop_refl
  given: (X : Cᵒᵖ)
  statement: Iso.unop (Iso.refl X) = Iso.refl X.unop
  proof: rfl

@[simp]

中文:
定理 unop_refl
  条件: (X : Cᵒᵖ)
  结论: Iso.unop (Iso.refl X) = Iso.refl X.unop
  证明: rfl

@[simp]
-/
theorem unop_refl (X : Cᵒᵖ) : Iso.unop (Iso.refl X) = Iso.refl X.unop := rfl

@[simp]
/--
theorem `unop_trans` / 定理 `unop_trans`

English:
theorem unop_trans
  given: {X Y Z : Cᵒᵖ} (α : X ≅ Y) (β : Y ≅ Z)
  proof: rfl

@[simp]

中文:
定理 unop_trans
  条件: {X Y Z : Cᵒᵖ} (α : X ≅ Y) (β : Y ≅ Z)
  证明: rfl

@[simp]
-/
theorem unop_trans {X Y Z : Cᵒᵖ} (α : X ≅ Y) (β : Y ≅ Z) :
    Iso.unop (α ≪≫ β) = Iso.unop β ≪≫ Iso.unop α :=
  rfl

@[simp]
/--
theorem `unop_symm` / 定理 `unop_symm`

English:
theorem unop_symm
  given: {X Y : Cᵒᵖ} (α : X ≅ Y)
  statement: Iso.unop α.symm = (Iso.unop α).symm
  proof: rfl

中文:
定理 unop_symm
  条件: {X Y : Cᵒᵖ} (α : X ≅ Y)
  结论: Iso.unop α.symm = (Iso.unop α).symm
  证明: rfl
-/
theorem unop_symm {X Y : Cᵒᵖ} (α : X ≅ Y) : Iso.unop α.symm = (Iso.unop α).symm := rfl

section

variable {D : Type*} [Category* D] {F G : C ⥤ Dᵒᵖ} (e : F ≅ G) (X : C)

@[reassoc +to_dual (attr := simp)]
/--
lemma `unop_hom_inv_id_app` / 引理 `unop_hom_inv_id_app`

English:
lemma unop_hom_inv_id_app
  statement: (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _
  proof: by
  rw [← unop_comp]; rw [inv_hom_id_app]; rw [unop_id]

@[reassoc +to_dual (attr := simp)]

中文:
引理 unop_hom_inv_id_app
  结论: (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _
  证明: by
  rw [← unop_comp]; rw [inv_hom_id_app]; rw [unop_id]

@[reassoc +to_dual (attr := simp)]

Depends on / 依赖: inv_hom_id_app, unop_comp, unop_id
-/
lemma unop_hom_inv_id_app : (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _ := by
  rw [← unop_comp]; rw [inv_hom_id_app]; rw [unop_id]

@[reassoc +to_dual (attr := simp)]
/--
lemma `unop_inv_hom_id_app` / 引理 `unop_inv_hom_id_app`

English:
lemma unop_inv_hom_id_app
  statement: (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _
  proof: by
  rw [← unop_comp]; rw [hom_inv_id_app]; rw [unop_id]

中文:
引理 unop_inv_hom_id_app
  结论: (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _
  证明: by
  rw [← unop_comp]; rw [hom_inv_id_app]; rw [unop_id]

Depends on / 依赖: hom_inv_id_app, unop_comp, unop_id
-/
lemma unop_inv_hom_id_app : (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _ := by
  rw [← unop_comp]; rw [hom_inv_id_app]; rw [unop_id]

end

end Iso

namespace NatIso

variable {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (α : F ≅ G)
  body: NatTrans.op α.hom
  inv := NatTrans.op α.inv
  hom_inv_id := by ext; dsimp; rw [← op_comp]; rw [α.inv_hom_id_app]; rfl
  inv_hom_id := by ext; dsimp; rw [← op_comp]; rw [α.hom_inv_id_app]; rfl

@[simp]

中文:
定义 op
  签名: (α : F ≅ G)
  定义体: NatTrans.op α.hom
  inv := NatTrans.op α.inv
  hom_inv_id := by ext; dsimp; rw [← op_comp]; rw [α.inv_hom_id_app]; rfl
  inv_hom_id := by ext; dsimp; rw [← op_comp]; rw [α.hom_inv_id_app]; rfl

@[simp]
-/
protected def op (α : F ≅ G) : G.op ≅ F.op where
  hom := NatTrans.op α.hom
  inv := NatTrans.op α.inv
  hom_inv_id := by ext; dsimp; rw [← op_comp]; rw [α.inv_hom_id_app]; rfl
  inv_hom_id := by ext; dsimp; rw [← op_comp]; rw [α.hom_inv_id_app]; rfl

@[simp]
/--
theorem `op_refl` / 定理 `op_refl`

English:
theorem op_refl
  statement: NatIso.op (Iso.refl F) = Iso.refl F.op
  proof: rfl

@[simp]

中文:
定理 op_refl
  结论: 自然数Iso.op (Iso.refl F) = Iso.refl F.op
  证明: rfl

@[simp]
-/
theorem op_refl : NatIso.op (Iso.refl F) = Iso.refl F.op := rfl

@[simp]
/--
theorem `op_trans` / 定理 `op_trans`

English:
theorem op_trans
  given: {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H)
  proof: rfl

@[simp]

中文:
定理 op_trans
  条件: {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H)
  证明: rfl

@[simp]
-/
theorem op_trans {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) :
    NatIso.op (α ≪≫ β) = NatIso.op β ≪≫ NatIso.op α :=
  rfl

@[simp]
/--
theorem `op_symm` / 定理 `op_symm`

English:
theorem op_symm
  given: (α : F ≅ G)
  statement: NatIso.op α.symm = (NatIso.op α).symm
  proof: rfl

中文:
定理 op_symm
  条件: (α : F ≅ G)
  结论: 自然数Iso.op α.symm = (自然数Iso.op α).symm
  证明: rfl
-/
theorem op_symm (α : F ≅ G) : NatIso.op α.symm = (NatIso.op α).symm := rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps]
/--
Definition of `removeOp` / `removeOp` 的定义

English:
definition removeOp
  signature: (α : F.op ≅ G.op)
  body: NatTrans.removeOp α.hom
  inv := NatTrans.removeOp α.inv

中文:
定义 removeOp
  签名: (α : F.op ≅ G.op)
  定义体: NatTrans.removeOp α.hom
  inv := NatTrans.removeOp α.inv
-/
protected def removeOp (α : F.op ≅ G.op) : G ≅ F where
  hom := NatTrans.removeOp α.hom
  inv := NatTrans.removeOp α.inv

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G)
  body: NatTrans.unop α.hom
  inv := NatTrans.unop α.inv

@[simp]

中文:
定义 unop
  签名: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G)
  定义体: NatTrans.unop α.hom
  inv := NatTrans.unop α.inv

@[simp]
-/
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop where
  hom := NatTrans.unop α.hom
  inv := NatTrans.unop α.inv

@[simp]
/--
theorem `unop_refl` / 定理 `unop_refl`

English:
theorem unop_refl
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  statement: NatIso.unop (Iso.refl F) = Iso.refl F.unop
  proof: rfl

@[simp]

中文:
定理 unop_refl
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ)
  结论: 自然数Iso.unop (Iso.refl F) = Iso.refl F.unop
  证明: rfl

@[simp]
-/
theorem unop_refl (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatIso.unop (Iso.refl F) = Iso.refl F.unop := rfl

@[simp]
/--
theorem `unop_trans` / 定理 `unop_trans`

English:
theorem unop_trans
  given: {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) (β : G ≅ H)
  proof: rfl

@[simp]

中文:
定理 unop_trans
  条件: {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) (β : G ≅ H)
  证明: rfl

@[simp]
-/
theorem unop_trans {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) (β : G ≅ H) :
    NatIso.unop (α ≪≫ β) = NatIso.unop β ≪≫ NatIso.unop α :=
  rfl

@[simp]
/--
theorem `unop_symm` / 定理 `unop_symm`

English:
theorem unop_symm
  given: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G)
  statement: NatIso.unop α.symm = (NatIso.unop α).symm
  proof: rfl

中文:
定理 unop_symm
  条件: {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G)
  结论: 自然数Iso.unop α.symm = (自然数Iso.unop α).symm
  证明: rfl
-/
theorem unop_symm {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : NatIso.unop α.symm = (NatIso.unop α).symm := rfl

/--
lemma `op_isoWhiskerRight` / 引理 `op_isoWhiskerRight`

English:
lemma op_isoWhiskerRight
  given: {E : Type*} [Category* E] {H : D ⥤ E} (α : F ≅ G)
  proof: by
  cat_disch

中文:
引理 op_isoWhiskerRight
  条件: {E : 类型} [Category* E] {H : D ⥤ E} (α : F ≅ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma op_isoWhiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ≅ G) :
    NatIso.op (isoWhiskerRight α H) =
    (Functor.opComp _ _) ≪≫ isoWhiskerRight (NatIso.op α) H.op ≪≫ (Functor.opComp _ _).symm := by
  cat_disch

/--
lemma `op_isoWhiskerLeft` / 引理 `op_isoWhiskerLeft`

English:
lemma op_isoWhiskerLeft
  given: {E : Type*} [Category* E] {H : E ⥤ C} (α : F ≅ G)
  proof: by
  cat_disch

中文:
引理 op_isoWhiskerLeft
  条件: {E : 类型} [Category* E] {H : E ⥤ C} (α : F ≅ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma op_isoWhiskerLeft {E : Type*} [Category* E] {H : E ⥤ C} (α : F ≅ G) :
    NatIso.op (isoWhiskerLeft H α) =
    (Functor.opComp _ _) ≪≫ isoWhiskerLeft H.op (NatIso.op α) ≪≫ (Functor.opComp _ _).symm := by
  cat_disch

/--
lemma `unop_whiskerRight` / 引理 `unop_whiskerRight`

English:
lemma unop_whiskerRight
  given: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ≅ G)
  proof: by
  cat_disch

中文:
引理 unop_whiskerRight
  条件: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : 类型} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ≅ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerRight α H) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerRight (NatIso.unop α) H.unop ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch

/--
lemma `unop_whiskerLeft` / 引理 `unop_whiskerLeft`

English:
lemma unop_whiskerLeft
  given: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ≅ G)
  proof: by
  cat_disch

中文:
引理 unop_whiskerLeft
  条件: {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : 类型} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ≅ G)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerLeft H α) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerLeft H.unop (NatIso.unop α) ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch

/--
lemma `op_leftUnitor` / 引理 `op_leftUnitor`

English:
lemma op_leftUnitor
  proof: by
  cat_disch

中文:
引理 op_leftUnitor
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma op_leftUnitor :
    NatIso.op F.leftUnitor =
    F.op.leftUnitor.symm ≪≫
      isoWhiskerRight (Functor.opId C).symm F.op ≪≫
      (Functor.opComp _ _).symm := by
  cat_disch

/--
lemma `op_rightUnitor` / 引理 `op_rightUnitor`

English:
lemma op_rightUnitor
  proof: by
  cat_disch

中文:
引理 op_rightUnitor
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma op_rightUnitor :
    NatIso.op F.rightUnitor =
    F.op.rightUnitor.symm ≪≫
      isoWhiskerLeft F.op (Functor.opId D).symm ≪≫
      (Functor.opComp _ _).symm := by
  cat_disch

/--
lemma `op_associator` / 引理 `op_associator`

English:
lemma op_associator
  statement: {E E' : Type*} [Category* E] [Category* E']
  proof: by
  cat_disch

中文:
引理 op_associator
  结论: {E E' : 类型} [Category* E] [Category* E']
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma op_associator {E E' : Type*} [Category* E] [Category* E']
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} :
    NatIso.op (Functor.associator F G H) =
      Functor.opComp _ _ ≪≫ isoWhiskerLeft F.op (Functor.opComp _ _) ≪≫
        (Functor.associator F.op G.op H.op).symm ≪≫
        isoWhiskerRight (Functor.opComp _ _).symm H.op ≪≫ (Functor.opComp _ _).symm := by
  cat_disch

/--
lemma `unop_leftUnitor` / 引理 `unop_leftUnitor`

English:
lemma unop_leftUnitor
  given: {F : Cᵒᵖ ⥤ Dᵒᵖ}
  proof: by
  cat_disch

中文:
引理 unop_leftUnitor
  条件: {F : Cᵒᵖ ⥤ Dᵒᵖ}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma unop_leftUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} :
    NatIso.unop F.leftUnitor =
    F.unop.leftUnitor.symm ≪≫
      isoWhiskerRight (Functor.unopId C).symm F.unop ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch

/--
lemma `unop_rightUnitor` / 引理 `unop_rightUnitor`

English:
lemma unop_rightUnitor
  given: {F : Cᵒᵖ ⥤ Dᵒᵖ}
  proof: by
  cat_disch

中文:
引理 unop_rightUnitor
  条件: {F : Cᵒᵖ ⥤ Dᵒᵖ}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma unop_rightUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} :
    NatIso.unop F.rightUnitor =
    F.unop.rightUnitor.symm ≪≫
      isoWhiskerLeft F.unop (Functor.unopId D).symm ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch

/--
lemma `unop_associator` / 引理 `unop_associator`

English:
lemma unop_associator
  statement: {E E' : Type*} [Category* E] [Category* E']
  proof: by
  cat_disch

中文:
引理 unop_associator
  结论: {E E' : 类型} [Category* E] [Category* E']
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma unop_associator {E E' : Type*} [Category* E] [Category* E']
    {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Eᵒᵖ} {H : Eᵒᵖ ⥤ E'ᵒᵖ} :
    NatIso.unop (Functor.associator F G H) =
      Functor.unopComp _ _ ≪≫ isoWhiskerLeft F.unop (Functor.unopComp _ _) ≪≫
        (Functor.associator F.unop G.unop H.unop).symm ≪≫
        isoWhiskerRight (Functor.unopComp _ _).symm H.unop ≪≫ (Functor.unopComp _ _).symm := by
  cat_disch

end NatIso

section

variable {D : Type*} [Category* D] {F G : C ⥤ D}

instance (α : F ⟶ G) [IsIso α] :
    IsIso (NatTrans.op α) :=
  (NatIso.op (asIso α)).isIso_hom

@[push]
/--
lemma `inv_op` / 引理 `inv_op`

English:
lemma inv_op
  given: (α : F ⟶ G) [IsIso α]
  proof: IsIso.inv_eq_of_hom_inv_id (by simp [← NatTrans.op_comp])

中文:
引理 inv_op
  条件: (α : F ⟶ G) [IsIso α]
  证明: IsIso.inv_eq_of_hom_inv_id (by simp [← NatTrans.op_comp])

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, NatTrans, NatTrans.op_comp, inv_eq_of_hom_inv_id, op_comp
-/
lemma inv_op (α : F ⟶ G) [IsIso α] :
    inv (NatTrans.op α) = NatTrans.op (inv α) :=
  IsIso.inv_eq_of_hom_inv_id (by simp [← NatTrans.op_comp])

end

namespace Equivalence

variable {D : Type u₂} [Category.{v₂} D]

/-- An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (e : C ≌ D)
  body: e.functor.op
  inverse := e.inverse.op
  unitIso := (NatIso.op e.unitIso).symm
  counitIso := (NatIso.op e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.unop_inj
    simp

中文:
定义 op
  签名: (e : C ≌ D)
  定义体: e.functor.op
  inverse := e.inverse.op
  unitIso := (NatIso.op e.unitIso).symm
  counitIso := (NatIso.op e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.unop_inj
    simp

Depends on / 依赖: e.functor.op, functor
-/
def op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ where
  functor := e.functor.op
  inverse := e.inverse.op
  unitIso := (NatIso.op e.unitIso).symm
  counitIso := (NatIso.op e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.unop_inj
    simp

/-- An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (e : Cᵒᵖ ≌ Dᵒᵖ)
  body: e.functor.unop
  inverse := e.inverse.unop
  unitIso := (NatIso.unop e.unitIso).symm
  counitIso := (NatIso.unop e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.op_inj
    simp

中文:
定义 unop
  签名: (e : Cᵒᵖ ≌ Dᵒᵖ)
  定义体: e.functor.unop
  inverse := e.inverse.unop
  unitIso := (NatIso.unop e.unitIso).symm
  counitIso := (NatIso.unop e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.op_inj
    simp

Depends on / 依赖: e.functor.unop, functor
-/
def unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D where
  functor := e.functor.unop
  inverse := e.inverse.unop
  unitIso := (NatIso.unop e.unitIso).symm
  counitIso := (NatIso.unop e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.op_inj
    simp

/--
Definition of `leftOp` / `leftOp` 的定义

English:
definition leftOp
  signature: (e : C ≌ Dᵒᵖ)
  body: e.op.trans (opOpEquivalence D)

中文:
定义 leftOp
  签名: (e : C ≌ Dᵒᵖ)
  定义体: e.op.trans (opOpEquivalence D)
-/
@[simps!] def leftOp (e : C ≌ Dᵒᵖ) : Cᵒᵖ ≌ D := e.op.trans (opOpEquivalence D)

/--
Definition of `rightOp` / `rightOp` 的定义

English:
definition rightOp
  signature: (e : Cᵒᵖ ≌ D)
  body: (opOpEquivalence C).symm.trans e.op

中文:
定义 rightOp
  签名: (e : Cᵒᵖ ≌ D)
  定义体: (opOpEquivalence C).symm.trans e.op
-/
@[simps!] def rightOp (e : Cᵒᵖ ≌ D) : C ≌ Dᵒᵖ := (opOpEquivalence C).symm.trans e.op

end Equivalence

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def opEquiv' (A : C) (B : Cᵒᵖ) : (Opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
  opEquiv _ _

def opEquiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ Opposite.op B) ≃ (B ⟶ A.unop) :=
  opEquiv _ _

def opEquiv''' (A B : C) : (Opposite.op A ⟶ Opposite.op B) ≃ (B ⟶ A) :=
  opEquiv _ _
```
-/
@[to_dual self, simps (attr := to_dual self)]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: (A B : Cᵒᵖ)
  body: f.unop
  invFun g := g.op

@[to_dual self]

中文:
定义 opEquiv
  签名: (A B : Cᵒᵖ)
  定义体: f.unop
  invFun g := g.op

@[to_dual self]

Depends on / 依赖: f.unop
-/
def opEquiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) where
  toFun f := f.unop
  invFun g := g.op

@[to_dual self]
/--
Instance `subsingleton_of_unop` / 实例 `subsingleton_of_unop`

English:
instance subsingleton_of_unop
  signature: (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)]
  body: (opEquiv A B).subsingleton

@[to_dual self]

中文:
实例 subsingleton_of_unop
  签名: (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)]
  定义体: (opEquiv A B).subsingleton

@[to_dual self]

Depends on / 依赖: opEquiv, subsingleton
-/
instance subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B) :=
  (opEquiv A B).subsingleton

@[to_dual self]
/--
Instance `decidableEqOfUnop` / 实例 `decidableEqOfUnop`

English:
instance decidableEqOfUnop
  signature: (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)]
  body: (opEquiv A B).decidableEq

中文:
实例 decidableEqOfUnop
  签名: (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)]
  定义体: (opEquiv A B).decidableEq

Depends on / 依赖: decidableEq, opEquiv
-/
instance decidableEqOfUnop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableEq (A ⟶ B) :=
  (opEquiv A B).decidableEq

/-- The equivalence between isomorphisms of the form `A ≅ B` and `B.unop ≅ A.unop`.

Note this is definitionally the same as the other three variants:
* `(Opposite.op A ≅ B) ≃ (B.unop ≅ A)`
* `(A ≅ Opposite.op B) ≃ (B ≅ A.unop)`
* `(Opposite.op A ≅ Opposite.op B) ≃ (B ≅ A)`
-/
@[simps]
/--
Definition of `isoOpEquiv` / `isoOpEquiv` 的定义

English:
definition isoOpEquiv
  signature: (A B : Cᵒᵖ)
  body: f.unop
  invFun g := g.op

中文:
定义 isoOpEquiv
  签名: (A B : Cᵒᵖ)
  定义体: f.unop
  invFun g := g.op

Depends on / 依赖: f.unop
-/
def isoOpEquiv (A B : Cᵒᵖ) : (A ≅ B) ≃ (B.unop ≅ A.unop) where
  toFun f := f.unop
  invFun g := g.op

namespace Functor

variable (C)
variable (D : Type u₂) [Category.{v₂} D]

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of functor categories induced by `op` and `unop`.
-/
@[simps]
/--
Definition of `opUnopEquiv` / `opUnopEquiv` 的定义

English:
definition opUnopEquiv
  signature: : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  body: opHom _ _
  inverse := opInv _ _
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.opUnopIso.op)
      (by
        intro F G f
        dsimp [opUnopIso]
        rw [show f = f.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents f

中文:
定义 opUnopEquiv
  签名: : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  定义体: opHom _ _
  inverse := opInv _ _
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.opUnopIso.op)
      (by
        intro F G f
        dsimp [opUnopIso]
        rw [show f = f.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents f
-/
def opUnopEquiv : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  functor := opHom _ _
  inverse := opInv _ _
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.opUnopIso.op)
      (by
        intro F G f
        dsimp [opUnopIso]
        rw [show f = f.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents fun F => F.unopOpIso

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of functor categories induced by `leftOp` and `rightOp`.
-/
@[simps!]
/--
Definition of `leftOpRightOpEquiv` / `leftOpRightOpEquiv` 的定义

English:
definition leftOpRightOpEquiv
  signature: : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  body: { obj := fun F => F.unop.rightOp
      map := fun η => NatTrans.rightOp η.unop }
  inverse :=
    { obj := fun F => op F.leftOp
      map := fun η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp
        rw [show 

中文:
定义 leftOpRightOpEquiv
  签名: : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  定义体: { obj := fun F => F.unop.rightOp
      map := fun η => NatTrans.rightOp η.unop }
  inverse :=
    { obj := fun F => op F.leftOp
      map := fun η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp
        rw [show 

Depends on / 依赖: F.leftOp, F.leftOpRightOpIso, F.unop.rightOp, F.unop.rightOpLeftOpIso.op, NatIso, NatIso.ofComponents, NatTrans, NatTrans.rightOp, cat_disch, counitIso, inverse, leftOp, leftOp.op, leftOpRightOpIso, ofComponents, op_comp, rightOp, rightOpLeftOpIso, unitIso, unop.op
-/
def leftOpRightOpEquiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  functor :=
    { obj := fun F => F.unop.rightOp
      map := fun η => NatTrans.rightOp η.unop }
  inverse :=
    { obj := fun F => op F.leftOp
      map := fun η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp
        rw [show η = η.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents fun F => F.leftOpRightOpIso

instance {F : C ⥤ D} [EssSurj F] : EssSurj F.op where
  mem_essImage X := ⟨op _, ⟨(F.objObjPreimageIso X.unop).op.symm⟩⟩

instance {F : Cᵒᵖ ⥤ D} [EssSurj F] : EssSurj F.rightOp where
  mem_essImage X := ⟨_, ⟨(F.objObjPreimageIso X.unop).op.symm⟩⟩

instance {F : C ⥤ Dᵒᵖ} [EssSurj F] : EssSurj F.leftOp where
  mem_essImage X := ⟨op _, ⟨(F.objObjPreimageIso (op X)).unop.symm⟩⟩

instance {F : C ⥤ D} [IsEquivalence F] : IsEquivalence F.op where

instance {F : Cᵒᵖ ⥤ D} [IsEquivalence F] : IsEquivalence F.rightOp where

instance {F : C ⥤ Dᵒᵖ} [IsEquivalence F] : IsEquivalence F.leftOp where

end Functor

end CategoryTheory
