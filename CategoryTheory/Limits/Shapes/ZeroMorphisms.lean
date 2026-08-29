/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe w v v' u u'

open CategoryTheory

open CategoryTheory.Category

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/--
Definition of `HasZeroMorphisms` / `HasZeroMorphisms` 的定义

English:
class HasZeroMorphisms
  parameters: where
  axioms and operations (3):
    - [zero : forall X Y : C, Zero (X ⟶ Y)]
    - comp_zero : forall {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)  [default: by cat_disch]
    - zero_comp : forall (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)  [default: by cat_disch]

中文:
类 HasZeroMorphisms
  参数: where
  公理与运算 (3 个):
    - [zero : 对任意 X Y : C, Zero (X ⟶ Y)]
    - comp_zero : 对任意 {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)  [默认: by cat_disch]
    - zero_comp : 对任意 (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : forall X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : forall {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by cat_disch
  /-- `0` composed with `f` is `0` -/
  zero_comp : forall (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by cat_disch

attribute [instance_reducible, instance] HasZeroMorphisms.zero

variable {C}

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  given: [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C}
  proof: HasZeroMorphisms.comp_zero f Z

@[simp]

中文:
定理 comp_zero
  条件: [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C}
  证明: HasZeroMorphisms.comp_zero f Z

@[simp]

Depends on / 依赖: HasZeroMorphisms, HasZeroMorphisms.comp_zero, comp_zero
-/
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z}
  proof: HasZeroMorphisms.zero_comp X f

中文:
定理 zero_comp
  条件: [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z}
  证明: HasZeroMorphisms.zero_comp X f

Depends on / 依赖: HasZeroMorphisms, HasZeroMorphisms.zero_comp, zero_comp
-/
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f

/--
Instance `hasZeroMorphismsPEmpty` / 实例 `hasZeroMorphismsPEmpty`

English:
instance hasZeroMorphismsPEmpty
  signature: : HasZeroMorphisms (Discrete PEmpty) where
  body: by cat_disch

中文:
实例 hasZeroMorphismsPEmpty
  签名: : HasZeroMorphisms (Discrete PEmpty) where
  定义体: by cat_disch

Depends on / 依赖: cat_disch
-/
instance hasZeroMorphismsPEmpty : HasZeroMorphisms (Discrete PEmpty) where
  zero := by cat_disch

/--
Instance `hasZeroMorphismsPUnit` / 实例 `hasZeroMorphismsPUnit`

English:
instance hasZeroMorphismsPUnit
  signature: : HasZeroMorphisms (Discrete PUnit) where
  body: by repeat (constructor)

中文:
实例 hasZeroMorphismsPUnit
  签名: : HasZeroMorphisms (Discrete PUnit) where
  定义体: by repeat (constructor)

Depends on / 依赖: repeat
-/
instance hasZeroMorphismsPUnit : HasZeroMorphisms (Discrete PUnit) where
  zero X Y := by repeat (constructor)

namespace HasZeroMorphisms

/--
theorem `ext_aux` / 定理 `ext_aux`

English:
theorem ext_aux
  statement: (I J : HasZeroMorphisms C)
  proof: by
  have : I.zero = J.zero := by
    funext X Y
    specialize w X Y
    apply congrArg Zero.mk w
  cases I; cases J
  congr
  · apply proof_irrel_heq
  · apply proof_irrel_heq

中文:
定理 ext_aux
  结论: (I J : HasZeroMorphisms C)
  证明: by
  have : I.zero = J.zero := by
    funext X Y
    specialize w X Y
    apply congrArg Zero.mk w
  cases I; cases J
  congr
  · apply proof_irrel_heq
  · apply proof_irrel_heq
-/
private theorem ext_aux (I J : HasZeroMorphisms C)
    (w : forall X Y : C, (I.zero X Y).zero = (J.zero X Y).zero) : I = J := by
  have : I.zero = J.zero := by
    funext X Y
    specialize w X Y
    apply congrArg Zero.mk w
  cases I; cases J
  congr
  · apply proof_irrel_heq
  · apply proof_irrel_heq

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (I J : HasZeroMorphisms C)
  statement: I = J
  proof: by
  apply ext_aux
  intro X Y
  have : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (I.zero X Y).zero := by
    apply I.zero_comp X (J.zero Y Y).zero
  have that : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (J.zero X Y).zero := by
    apply J.comp_zero (I.zero X Y).zero Y
  rw [← this]; rw [← that]

中文:
定理 ext
  条件: (I J : HasZeroMorphisms C)
  结论: I = J
  证明: by
  apply ext_aux
  intro X Y
  have : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (I.zero X Y).zero := by
    apply I.zero_comp X (J.zero Y Y).zero
  have that : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (J.zero X Y).zero := by
    apply J.comp_zero (I.zero X Y).zero Y
  rw [← this]; rw [← that]

Depends on / 依赖: I.zero, I.zero_comp, J.comp_zero, J.zero, comp_zero, ext_aux, zero_comp
-/
theorem ext (I J : HasZeroMorphisms C) : I = J := by
  apply ext_aux
  intro X Y
  have : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (I.zero X Y).zero := by
    apply I.zero_comp X (J.zero Y Y).zero
  have that : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (J.zero X Y).zero := by
    apply J.comp_zero (I.zero X Y).zero Y
  rw [← this]; rw [← that]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (HasZeroMorphisms C)
  body: ⟨ext⟩

中文:
实例 :
  签名: Subsingleton (HasZeroMorphisms C)
  定义体: ⟨ext⟩
-/
instance : Subsingleton (HasZeroMorphisms C) :=
  ⟨ext⟩

end HasZeroMorphisms

open Opposite HasZeroMorphisms

/--
Instance `hasZeroMorphismsOpposite` / 实例 `hasZeroMorphismsOpposite`

English:
instance hasZeroMorphismsOpposite
  signature: [HasZeroMorphisms C]
  body: ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X {Y Z} (f : Y ⟶ Z) :=
    congrArg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))

中文:
实例 hasZeroMorphismsOpposite
  签名: [HasZeroMorphisms C]
  定义体: ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X {Y Z} (f : Y ⟶ Z) :=
    congrArg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))
-/
instance hasZeroMorphismsOpposite [HasZeroMorphisms C] : HasZeroMorphisms Cᵒᵖ where
  zero X Y := ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X {Y Z} (f : Y ⟶ Z) :=
    congrArg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))

section

variable [HasZeroMorphisms C]

/--
lemma `op_zero` / 引理 `op_zero`

English:
lemma op_zero
  given: (X Y : C)
  statement: (0 : X ⟶ Y).op = 0
  proof: rfl

中文:
引理 op_zero
  条件: (X Y : C)
  结论: (0 : X ⟶ Y).op = 0
  证明: rfl
-/
@[simp] lemma op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 := rfl

/--
lemma `unop_zero` / 引理 `unop_zero`

English:
lemma unop_zero
  given: (X Y : Cᵒᵖ)
  statement: (0 : X ⟶ Y).unop = 0
  proof: rfl

中文:
引理 unop_zero
  条件: (X Y : Cᵒᵖ)
  结论: (0 : X ⟶ Y).unop = 0
  证明: rfl
-/
@[simp] lemma unop_zero (X Y : Cᵒᵖ) : (0 : X ⟶ Y).unop = 0 := rfl

/--
theorem `zero_of_comp_mono` / 定理 `zero_of_comp_mono`

English:
theorem zero_of_comp_mono
  given: {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0)
  statement: f = 0
  proof: by
  rw [← zero_comp]; rw [cancel_mono] at h
  exact h

中文:
定理 zero_of_comp_mono
  条件: {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0)
  结论: f = 0
  证明: by
  rw [← zero_comp]; rw [cancel_mono] at h
  exact h

Depends on / 依赖: cancel_mono, zero_comp
-/
theorem zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0 := by
  rw [← zero_comp]; rw [cancel_mono] at h
  exact h

/--
theorem `zero_of_epi_comp` / 定理 `zero_of_epi_comp`

English:
theorem zero_of_epi_comp
  given: {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0)
  statement: g = 0
  proof: by
  rw [← comp_zero]; rw [cancel_epi] at h
  exact h

中文:
定理 zero_of_epi_comp
  条件: {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0)
  结论: g = 0
  证明: by
  rw [← comp_zero]; rw [cancel_epi] at h
  exact h

Depends on / 依赖: cancel_epi, comp_zero
-/
theorem zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0 := by
  rw [← comp_zero]; rw [cancel_epi] at h
  exact h

/--
lemma `comp_eq_zero_iff_of_epi` / 引理 `comp_eq_zero_iff_of_epi`

English:
lemma comp_eq_zero_iff_of_epi
  given: {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f]
  proof: ⟨zero_of_epi_comp _, by simp +contextual⟩

中文:
引理 comp_eq_zero_iff_of_epi
  条件: {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f]
  证明: ⟨zero_of_epi_comp _, by simp +contextual⟩

Depends on / 依赖: contextual, zero_of_epi_comp
-/
lemma comp_eq_zero_iff_of_epi {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] :
    f ≫ g = 0 ↔ g = 0 :=
  ⟨zero_of_epi_comp _, by simp +contextual⟩

/--
theorem `eq_zero_of_image_eq_zero` / 定理 `eq_zero_of_image_eq_zero`

English:
theorem eq_zero_of_image_eq_zero
  given: {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0)
  proof: by rw [← image.fac f, w, HasZeroMorphisms.comp_zero]

中文:
定理 eq_zero_of_image_eq_zero
  条件: {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0)
  证明: by rw [← image.fac f, w, HasZeroMorphisms.comp_zero]

Depends on / 依赖: HasZeroMorphisms, HasZeroMorphisms.comp_zero, IsMonoidal, NatTrans, NatTrans.IsMonoidal.tensor, NatTrans.IsMonoidal.unit, comp_zero, image.fac, tensor
-/
theorem eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) :
    f = 0 := by rw [← image.fac f, w, HasZeroMorphisms.comp_zero]

/--
theorem `nonzero_image_of_nonzero` / 定理 `nonzero_image_of_nonzero`

English:
theorem nonzero_image_of_nonzero
  given: {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f != 0)
  statement: image.ι f != 0
  proof: fun h => w (eq_zero_of_image_eq_zero h)

中文:
定理 nonzero_image_of_nonzero
  条件: {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f != 0)
  结论: image.ι f != 0
  证明: fun h => w (eq_zero_of_image_eq_zero h)

Depends on / 依赖: eq_zero_of_image_eq_zero
-/
theorem nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f != 0) : image.ι f != 0 :=
  fun h => w (eq_zero_of_image_eq_zero h)

end

section

variable [HasZeroMorphisms D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (C ⥤ D)
  body: ⟨{ app := fun _ => 0 }⟩
  comp_zero := fun η H => by
    ext X; dsimp; apply comp_zero
  zero_comp := fun F {G H} η => by
    ext X; dsimp; apply zero_comp

@[simp]

中文:
实例 :
  签名: HasZeroMorphisms (C ⥤ D)
  定义体: ⟨{ app := fun _ => 0 }⟩
  comp_zero := fun η H => by
    ext X; dsimp; apply comp_zero
  zero_comp := fun F {G H} η => by
    ext X; dsimp; apply zero_comp

@[simp]
-/
instance : HasZeroMorphisms (C ⥤ D) where
  zero F G := ⟨{ app := fun _ => 0 }⟩
  comp_zero := fun η H => by
    ext X; dsimp; apply comp_zero
  zero_comp := fun F {G H} η => by
    ext X; dsimp; apply zero_comp

@[simp]
/--
theorem `zero_app` / 定理 `zero_app`

English:
theorem zero_app
  given: (F G : C ⥤ D) (j : C)
  statement: (0 : F ⟶ G).app j = 0
  proof: rfl

中文:
定理 zero_app
  条件: (F G : C ⥤ D) (j : C)
  结论: (0 : F ⟶ G).app j = 0
  证明: rfl
-/
theorem zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 := rfl

end

namespace IsZero

variable [HasZeroMorphisms C]

/--
theorem `eq_zero_of_src` / 定理 `eq_zero_of_src`

English:
theorem eq_zero_of_src
  given: {X Y : C} (o : IsZero X) (f : X ⟶ Y)
  statement: f = 0
  proof: o.eq_of_src _ _

中文:
定理 eq_zero_of_src
  条件: {X Y : C} (o : IsZero X) (f : X ⟶ Y)
  结论: f = 0
  证明: o.eq_of_src _ _

Depends on / 依赖: eq_of_src, o.eq_of_src
-/
theorem eq_zero_of_src {X Y : C} (o : IsZero X) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_src _ _

/--
theorem `eq_zero_of_tgt` / 定理 `eq_zero_of_tgt`

English:
theorem eq_zero_of_tgt
  given: {X Y : C} (o : IsZero Y) (f : X ⟶ Y)
  statement: f = 0
  proof: o.eq_of_tgt _ _

中文:
定理 eq_zero_of_tgt
  条件: {X Y : C} (o : IsZero Y) (f : X ⟶ Y)
  结论: f = 0
  证明: o.eq_of_tgt _ _

Depends on / 依赖: PreservesZeroMorphisms, eq_of_tgt, o.eq_of_tgt, preservesZeroMorphisms_of_additive
-/
theorem eq_zero_of_tgt {X Y : C} (o : IsZero Y) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_tgt _ _

/--
theorem `iff_id_eq_zero` / 定理 `iff_id_eq_zero`

English:
theorem iff_id_eq_zero
  given: (X : C)
  statement: IsZero X ↔ 𝟙 X = 0
  proof: ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← id_comp f]; rw [← id_comp (0 : X ⟶ Y)]; rw [h]; rw [zero_comp]; rw [zero_comp]; simp only⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← comp_id f]; rw [← comp_id (0 : Y ⟶ X)]; rw [h]; rw [comp_zero]; rw [comp_zero]

中文:
定理 iff_id_eq_zero
  条件: (X : C)
  结论: IsZero X ↔ 𝟙 X = 0
  证明: ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← id_comp f]; rw [← id_comp (0 : X ⟶ Y)]; rw [h]; rw [zero_comp]; rw [zero_comp]; simp only⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← comp_id f]; rw [← comp_id (0 : Y ⟶ X)]; rw [h]; rw [comp_zero]; rw [comp_zero]

Depends on / 依赖: comp_id, comp_zero, eq_of_src, h.eq_of_src, id_comp, zero_comp
-/
theorem iff_id_eq_zero (X : C) : IsZero X ↔ 𝟙 X = 0 :=
  ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← id_comp f]; rw [← id_comp (0 : X ⟶ Y)]; rw [h]; rw [zero_comp]; rw [zero_comp]; simp only⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← comp_id f]; rw [← comp_id (0 : Y ⟶ X)]; rw [h]; rw [comp_zero]; rw [comp_zero]; simp only ⟩⟩⟩⟩

/--
theorem `of_mono_zero` / 定理 `of_mono_zero`

English:
theorem of_mono_zero
  given: (X Y : C) [Mono (0 : X ⟶ Y)]
  statement: IsZero X
  proof: (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))

中文:
定理 of_mono_zero
  条件: (X Y : C) [Mono (0 : X ⟶ Y)]
  结论: IsZero X
  证明: (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))

Depends on / 依赖: cancel_mono, iff_id_eq_zero
-/
theorem of_mono_zero (X Y : C) [Mono (0 : X ⟶ Y)] : IsZero X :=
  (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))

/--
theorem `of_epi_zero` / 定理 `of_epi_zero`

English:
theorem of_epi_zero
  given: (X Y : C) [Epi (0 : X ⟶ Y)]
  statement: IsZero Y
  proof: (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))

中文:
定理 of_epi_zero
  条件: (X Y : C) [Epi (0 : X ⟶ Y)]
  结论: IsZero Y
  证明: (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))

Depends on / 依赖: cancel_epi, iff_id_eq_zero
-/
theorem of_epi_zero (X Y : C) [Epi (0 : X ⟶ Y)] : IsZero Y :=
  (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))

/--
theorem `of_mono_eq_zero` / 定理 `of_mono_eq_zero`

English:
theorem of_mono_eq_zero
  given: {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0)
  statement: IsZero X
  proof: by
  subst h
  apply of_mono_zero X Y

中文:
定理 of_mono_eq_zero
  条件: {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0)
  结论: IsZero X
  证明: by
  subst h
  apply of_mono_zero X Y

Depends on / 依赖: of_mono_zero
-/
theorem of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0) : IsZero X := by
  subst h
  apply of_mono_zero X Y

/--
theorem `of_epi_eq_zero` / 定理 `of_epi_eq_zero`

English:
theorem of_epi_eq_zero
  given: {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0)
  statement: IsZero Y
  proof: by
  subst h
  apply of_epi_zero X Y

中文:
定理 of_epi_eq_zero
  条件: {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0)
  结论: IsZero Y
  证明: by
  subst h
  apply of_epi_zero X Y

Depends on / 依赖: of_epi_zero
-/
theorem of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y := by
  subst h
  apply of_epi_zero X Y

/--
theorem `iff_isSplitMono_eq_zero` / 定理 `iff_isSplitMono_eq_zero`

English:
theorem iff_isSplitMono_eq_zero
  given: {X Y : C} (f : X ⟶ Y) [IsSplitMono f]
  statement: IsZero X ↔ f = 0
  proof: by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.id_comp f]; rw [h]; rw [zero_comp]
  · intro h
    rw [← IsSplitMono.id f]
    simp only [h, zero_comp]

中文:
定理 iff_isSplitMono_eq_zero
  条件: {X Y : C} (f : X ⟶ Y) [IsSplitMono f]
  结论: IsZero X ↔ f = 0
  证明: by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.id_comp f]; rw [h]; rw [zero_comp]
  · intro h
    rw [← IsSplitMono.id f]
    simp only [h, zero_comp]

Depends on / 依赖: Category, Category.id_comp, IsSplitMono, IsSplitMono.id, id_comp, iff_id_eq_zero, zero_comp
-/
theorem iff_isSplitMono_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.id_comp f]; rw [h]; rw [zero_comp]
  · intro h
    rw [← IsSplitMono.id f]
    simp only [h, zero_comp]

/--
theorem `iff_isSplitEpi_eq_zero` / 定理 `iff_isSplitEpi_eq_zero`

English:
theorem iff_isSplitEpi_eq_zero
  given: {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]
  statement: IsZero Y ↔ f = 0
  proof: by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.comp_id f]; rw [h]; rw [comp_zero]
  · intro h
    rw [← IsSplitEpi.id f]
    simp [h]

中文:
定理 iff_isSplitEpi_eq_zero
  条件: {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]
  结论: IsZero Y ↔ f = 0
  证明: by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.comp_id f]; rw [h]; rw [comp_zero]
  · intro h
    rw [← IsSplitEpi.id f]
    simp [h]

Depends on / 依赖: Category, Category.comp_id, IsSplitEpi, IsSplitEpi.id, comp_id, comp_zero, iff_id_eq_zero
-/
theorem iff_isSplitEpi_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.comp_id f]; rw [h]; rw [comp_zero]
  · intro h
    rw [← IsSplitEpi.id f]
    simp [h]

/--
theorem `of_mono` / 定理 `of_mono`

English:
theorem of_mono
  given: {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y)
  statement: IsZero X
  proof: by
  obtain rfl := i.eq_zero_of_tgt f
  exact IsZero.of_mono_zero X Y

中文:
定理 of_mono
  条件: {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y)
  结论: IsZero X
  证明: by
  obtain rfl := i.eq_zero_of_tgt f
  exact IsZero.of_mono_zero X Y

Depends on / 依赖: IsZero, IsZero.of_mono_zero, eq_zero_of_tgt, i.eq_zero_of_tgt, of_mono_zero
-/
theorem of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y) : IsZero X := by
  obtain rfl := i.eq_zero_of_tgt f
  exact IsZero.of_mono_zero X Y

/--
theorem `of_epi` / 定理 `of_epi`

English:
theorem of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X)
  statement: IsZero Y
  proof: by
  obtain rfl := i.eq_zero_of_src f
  exact IsZero.of_epi_zero X Y

中文:
定理 of_epi
  条件: {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X)
  结论: IsZero Y
  证明: by
  obtain rfl := i.eq_zero_of_src f
  exact IsZero.of_epi_zero X Y

Depends on / 依赖: IsZero, IsZero.of_epi_zero, eq_zero_of_src, i.eq_zero_of_src, of_epi_zero
-/
theorem of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X) : IsZero Y := by
  obtain rfl := i.eq_zero_of_src f
  exact IsZero.of_epi_zero X Y

end IsZero

/-- A category with a zero object has zero morphisms.

It is rarely a good idea to use this. Many categories that have a zero object have zero
morphisms for some other reason, for example from additivity. Library code that uses
`zeroMorphismsOfZeroObject` will then be incompatible with these categories because
the `HasZeroMorphisms` instances will not be definitionally equal. For this reason library
code should generally ask for an instance of `HasZeroMorphisms` separately, even if it already
asks for an instance of `HasZeroObject`. -/
@[instance_reducible]
/--
Definition of `IsZero.hasZeroMorphisms` / `IsZero.hasZeroMorphisms` 的定义

English:
definition IsZero.hasZeroMorphisms
  signature: {O : C} (hO : IsZero O)
  body: { zero := hO.from_ X ≫ hO.to_ Y }
  zero_comp X {Y Z} f := by
    change (hO.from_ X ≫ hO.to_ Y) ≫ f = hO.from_ X ≫ hO.to_ Z
    rw [Category.assoc]
    congr
    apply hO.eq_of_src
  comp_zero {X Y} f Z := by
    change f ≫ (hO.from_ Y ≫ hO.to_ Z) = hO.from_ X ≫ hO.to_ Z
    rw [← Category.assoc]
 

中文:
定义 IsZero.hasZeroMorphisms
  签名: {O : C} (hO : IsZero O)
  定义体: { zero := hO.from_ X ≫ hO.to_ Y }
  zero_comp X {Y Z} f := by
    change (hO.from_ X ≫ hO.to_ Y) ≫ f = hO.from_ X ≫ hO.to_ Z
    rw [Category.assoc]
    congr
    apply hO.eq_of_src
  comp_zero {X Y} f Z := by
    change f ≫ (hO.from_ Y ≫ hO.to_ Z) = hO.from_ X ≫ hO.to_ Z
    rw [← Category.assoc]
 

Depends on / 依赖: from_, hO.from_, hO.to_
-/
def IsZero.hasZeroMorphisms {O : C} (hO : IsZero O) : HasZeroMorphisms C where
  zero X Y := { zero := hO.from_ X ≫ hO.to_ Y }
  zero_comp X {Y Z} f := by
    change (hO.from_ X ≫ hO.to_ Y) ≫ f = hO.from_ X ≫ hO.to_ Z
    rw [Category.assoc]
    congr
    apply hO.eq_of_src
  comp_zero {X Y} f Z := by
    change f ≫ (hO.from_ Y ≫ hO.to_ Z) = hO.from_ X ≫ hO.to_ Z
    rw [← Category.assoc]
    congr
    apply hO.eq_of_tgt

namespace HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- A category with a zero object has zero morphisms.

It is rarely a good idea to use this. Many categories that have a zero object have zero
morphisms for some other reason, for example from additivity. Library code that uses
`zeroMorphismsOfZeroObject` will then be incompatible with these categories because
the `HasZeroMorphisms` instances will not be definitionally equal. For this reason library
code should generally ask for an instance of `HasZeroMorphisms` separately, even if it already
asks for an instance of `HasZeroObject`. -/
@[instance_reducible]
/--
Definition of `zeroMorphismsOfZeroObject` / `zeroMorphismsOfZeroObject` 的定义

English:
definition zeroMorphismsOfZeroObject
  signature: : HasZeroMorphisms C where
  body: { zero := (default : X ⟶ 0) ≫ default }
  zero_comp X {Y Z} f := by
    change ((default : X ⟶ 0) ≫ default) ≫ f = (default : X ⟶ 0) ≫ default
    rw [Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]
  comp_zero {X Y} f Z := by
    change f ≫ (default : Y ⟶ 0) ≫ default = (defau

中文:
定义 zeroMorphismsOfZeroObject
  签名: : HasZeroMorphisms C where
  定义体: { zero := (default : X ⟶ 0) ≫ default }
  zero_comp X {Y Z} f := by
    change ((default : X ⟶ 0) ≫ default) ≫ f = (default : X ⟶ 0) ≫ default
    rw [Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]
  comp_zero {X Y} f Z := by
    change f ≫ (default : Y ⟶ 0) ≫ default = (defau
-/
def zeroMorphismsOfZeroObject : HasZeroMorphisms C where
  zero X _ := { zero := (default : X ⟶ 0) ≫ default }
  zero_comp X {Y Z} f := by
    change ((default : X ⟶ 0) ≫ default) ≫ f = (default : X ⟶ 0) ≫ default
    rw [Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]
  comp_zero {X Y} f Z := by
    change f ≫ (default : Y ⟶ 0) ≫ default = (default : X ⟶ 0) ≫ default
    rw [← Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

@[simp]
/--
theorem `zeroIsoIsInitial_hom` / 定理 `zeroIsoIsInitial_hom`

English:
theorem zeroIsoIsInitial_hom
  given: {X : C} (t : IsInitial X)
  statement: (zeroIsoIsInitial t).hom = 0
  proof: by ext

@[simp]

中文:
定理 zeroIsoIsInitial_hom
  条件: {X : C} (t : IsInitial X)
  结论: (zeroIsoIsInitial t).hom = 0
  证明: by ext

@[simp]

Depends on / 依赖: Functor, Functor.postcompose, infer_instance
-/
theorem zeroIsoIsInitial_hom {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).hom = 0 := by ext

@[simp]
/--
theorem `zeroIsoIsInitial_inv` / 定理 `zeroIsoIsInitial_inv`

English:
theorem zeroIsoIsInitial_inv
  given: {X : C} (t : IsInitial X)
  statement: (zeroIsoIsInitial t).inv = 0
  proof: by ext

@[simp]

中文:
定理 zeroIsoIsInitial_inv
  条件: {X : C} (t : IsInitial X)
  结论: (zeroIsoIsInitial t).inv = 0
  证明: by ext

@[simp]
-/
theorem zeroIsoIsInitial_inv {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).inv = 0 := by ext

@[simp]
/--
theorem `zeroIsoIsTerminal_hom` / 定理 `zeroIsoIsTerminal_hom`

English:
theorem zeroIsoIsTerminal_hom
  given: {X : C} (t : IsTerminal X)
  statement: (zeroIsoIsTerminal t).hom = 0
  proof: by ext

@[simp]

中文:
定理 zeroIsoIsTerminal_hom
  条件: {X : C} (t : IsTerminal X)
  结论: (zeroIsoIsTerminal t).hom = 0
  证明: by ext

@[simp]

Depends on / 依赖: Additive, preservesFiniteBiproductsOfAdditive
-/
theorem zeroIsoIsTerminal_hom {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).hom = 0 := by ext

@[simp]
/--
theorem `zeroIsoIsTerminal_inv` / 定理 `zeroIsoIsTerminal_inv`

English:
theorem zeroIsoIsTerminal_inv
  given: {X : C} (t : IsTerminal X)
  statement: (zeroIsoIsTerminal t).inv = 0
  proof: by ext

@[simp]

中文:
定理 zeroIsoIsTerminal_inv
  条件: {X : C} (t : IsTerminal X)
  结论: (zeroIsoIsTerminal t).inv = 0
  证明: by ext

@[simp]

Depends on / 依赖: Additive, preservesFiniteCoproductsOfAdditive
-/
theorem zeroIsoIsTerminal_inv {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).inv = 0 := by ext

@[simp]
/--
theorem `zeroIsoInitial_hom` / 定理 `zeroIsoInitial_hom`

English:
theorem zeroIsoInitial_hom
  given: [HasInitial C]
  statement: zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C)
  proof: by ext

@[simp]

中文:
定理 zeroIsoInitial_hom
  条件: [HasInitial C]
  结论: zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C)
  证明: by ext

@[simp]

Depends on / 依赖: Additive, preservesFiniteProductsOfAdditive
-/
theorem zeroIsoInitial_hom [HasInitial C] : zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C) := by ext

@[simp]
/--
theorem `zeroIsoInitial_inv` / 定理 `zeroIsoInitial_inv`

English:
theorem zeroIsoInitial_inv
  given: [HasInitial C]
  statement: zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0)
  proof: by ext

@[simp]

中文:
定理 zeroIsoInitial_inv
  条件: [HasInitial C]
  结论: zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0)
  证明: by ext

@[simp]
-/
theorem zeroIsoInitial_inv [HasInitial C] : zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0) := by ext

@[simp]
/--
theorem `zeroIsoTerminal_hom` / 定理 `zeroIsoTerminal_hom`

English:
theorem zeroIsoTerminal_hom
  given: [HasTerminal C]
  statement: zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C)
  proof: by ext

@[simp]

中文:
定理 zeroIsoTerminal_hom
  条件: [HasTerminal C]
  结论: zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C)
  证明: by ext

@[simp]
-/
theorem zeroIsoTerminal_hom [HasTerminal C] : zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C) := by ext

@[simp]
/--
theorem `zeroIsoTerminal_inv` / 定理 `zeroIsoTerminal_inv`

English:
theorem zeroIsoTerminal_inv
  given: [HasTerminal C]
  statement: zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0)
  proof: by ext

中文:
定理 zeroIsoTerminal_inv
  条件: [HasTerminal C]
  结论: zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0)
  证明: by ext
-/
theorem zeroIsoTerminal_inv [HasTerminal C] : zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0) := by ext

end HasZeroMorphisms

open ZeroObject

instance {B : Type*} [Category* B] : HasZeroObject (B ⥤ C) :=
  (((CategoryTheory.Functor.const B).obj (0 : C)).isZero fun _ => isZero_zero _).hasZeroObject

end HasZeroObject

open ZeroObject

variable {D}

@[simp]
/--
theorem `IsZero.map` / 定理 `IsZero.map`

English:
theorem IsZero.map
  statement: [HasZeroObject D] [HasZeroMorphisms D] {F : C ⥤ D} (hF : IsZero F) {X Y : C}
  proof: (hF.obj _).eq_of_src _ _

@[simp]

中文:
定理 IsZero.map
  结论: [HasZeroObject D] [HasZeroMorphisms D] {F : C ⥤ D} (hF : IsZero F) {X Y : C}
  证明: (hF.obj _).eq_of_src _ _

@[simp]

Depends on / 依赖: eq_of_src, hF.obj
-/
theorem IsZero.map [HasZeroObject D] [HasZeroMorphisms D] {F : C ⥤ D} (hF : IsZero F) {X Y : C}
    (f : X ⟶ Y) : F.map f = 0 :=
  (hF.obj _).eq_of_src _ _

@[simp]
/--
theorem `_root_.CategoryTheory.Functor.zero_obj` / 定理 `_root_.CategoryTheory.Functor.zero_obj`

English:
theorem _root_.CategoryTheory.Functor.zero_obj
  given: [HasZeroObject D] (X : C)
  proof: (isZero_zero _).obj _

@[simp]

中文:
定理 _root_.CategoryTheory.Functor.zero_obj
  条件: [HasZeroObject D] (X : C)
  证明: (isZero_zero _).obj _

@[simp]

Depends on / 依赖: isZero_zero
-/
theorem _root_.CategoryTheory.Functor.zero_obj [HasZeroObject D] (X : C) :
    IsZero ((0 : C ⥤ D).obj X) :=
  (isZero_zero _).obj _

@[simp]
/--
theorem `_root_.CategoryTheory.zero_map` / 定理 `_root_.CategoryTheory.zero_map`

English:
theorem _root_.CategoryTheory.zero_map
  statement: [HasZeroObject D] [HasZeroMorphisms D] {X Y : C}
  proof: (isZero_zero _).map _

中文:
定理 _root_.CategoryTheory.zero_map
  结论: [HasZeroObject D] [HasZeroMorphisms D] {X Y : C}
  证明: (isZero_zero _).map _

Depends on / 依赖: isZero_zero
-/
theorem _root_.CategoryTheory.zero_map [HasZeroObject D] [HasZeroMorphisms D] {X Y : C}
    (f : X ⟶ Y) : (0 : C ⥤ D).map f = 0 :=
  (isZero_zero _).map _

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

@[simp]
/--
theorem `id_zero` / 定理 `id_zero`

English:
theorem id_zero
  statement: 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
  proof: by apply HasZeroObject.from_zero_ext

中文:
定理 id_zero
  结论: 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
  证明: by apply HasZeroObject.from_zero_ext

Depends on / 依赖: HasZeroObject, HasZeroObject.from_zero_ext, from_zero_ext
-/
theorem id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0) := by apply HasZeroObject.from_zero_ext

-- This can't be a `simp` lemma because the left-hand side would be a metavariable.
/--
theorem `zero_of_to_zero` / 定理 `zero_of_to_zero`

English:
theorem zero_of_to_zero
  given: {X : C} (f : X ⟶ 0)
  statement: f = 0
  proof: by ext

中文:
定理 zero_of_to_zero
  条件: {X : C} (f : X ⟶ 0)
  结论: f = 0
  证明: by ext

Depends on / 依赖: F.property, property
-/
theorem zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 := by ext

/--
theorem `zero_of_target_iso_zero` / 定理 `zero_of_target_iso_zero`

English:
theorem zero_of_target_iso_zero
  given: {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0)
  statement: f = 0
  proof: by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [Iso.hom_inv_id, id_comp, comp_id]
  simpa using h

中文:
定理 zero_of_target_iso_zero
  条件: {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0)
  结论: f = 0
  证明: by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [Iso.hom_inv_id, id_comp, comp_id]
  simpa using h

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id, i.hom, i.inv, id_comp
-/
theorem zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 := by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [Iso.hom_inv_id, id_comp, comp_id]
  simpa using h

/--
theorem `zero_of_from_zero` / 定理 `zero_of_from_zero`

English:
theorem zero_of_from_zero
  given: {X : C} (f : 0 ⟶ X)
  statement: f = 0
  proof: by ext

中文:
定理 zero_of_from_zero
  条件: {X : C} (f : 0 ⟶ X)
  结论: f = 0
  证明: by ext
-/
theorem zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 := by ext

/--
theorem `zero_of_source_iso_zero` / 定理 `zero_of_source_iso_zero`

English:
theorem zero_of_source_iso_zero
  given: {X Y : C} (f : X ⟶ Y) (i : X ≅ 0)
  statement: f = 0
  proof: by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [Iso.hom_inv_id_assoc, id_comp]
  simpa using h

中文:
定理 zero_of_source_iso_zero
  条件: {X Y : C} (f : X ⟶ Y) (i : X ≅ 0)
  结论: f = 0
  证明: by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [Iso.hom_inv_id_assoc, id_comp]
  simpa using h

Depends on / 依赖: Iso.hom_inv_id_assoc, hom_inv_id_assoc, i.hom, i.inv, id_comp
-/
theorem zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 := by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [Iso.hom_inv_id_assoc, id_comp]
  simpa using h

/--
theorem `zero_of_source_iso_zero'` / 定理 `zero_of_source_iso_zero'`

English:
theorem zero_of_source_iso_zero'
  given: {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0)
  statement: f = 0
  proof: zero_of_source_iso_zero f (Nonempty.some i)

中文:
定理 zero_of_source_iso_zero'
  条件: {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0)
  结论: f = 0
  证明: zero_of_source_iso_zero f (Nonempty.some i)

Depends on / 依赖: Nonempty, Nonempty.some, zero_of_source_iso_zero
-/
theorem zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0) : f = 0 :=
  zero_of_source_iso_zero f (Nonempty.some i)

/--
theorem `zero_of_target_iso_zero'` / 定理 `zero_of_target_iso_zero'`

English:
theorem zero_of_target_iso_zero'
  given: {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0)
  statement: f = 0
  proof: zero_of_target_iso_zero f (Nonempty.some i)

中文:
定理 zero_of_target_iso_zero'
  条件: {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0)
  结论: f = 0
  证明: zero_of_target_iso_zero f (Nonempty.some i)

Depends on / 依赖: Nonempty, Nonempty.some, zero_of_target_iso_zero
-/
theorem zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0) : f = 0 :=
  zero_of_target_iso_zero f (Nonempty.some i)

/--
theorem `mono_of_source_iso_zero` / 定理 `mono_of_source_iso_zero`

English:
theorem mono_of_source_iso_zero
  given: {X Y : C} (f : X ⟶ Y) (i : X ≅ 0)
  statement: Mono f
  proof: ⟨fun {Z} g h _ => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩

中文:
定理 mono_of_source_iso_zero
  条件: {X Y : C} (f : X ⟶ Y) (i : X ≅ 0)
  结论: Mono f
  证明: ⟨fun {Z} g h _ => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩

Depends on / 依赖: zero_of_target_iso_zero
-/
theorem mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : Mono f :=
  ⟨fun {Z} g h _ => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩

/--
theorem `epi_of_target_iso_zero` / 定理 `epi_of_target_iso_zero`

English:
theorem epi_of_target_iso_zero
  given: {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0)
  statement: Epi f
  proof: ⟨fun {Z} g h _ => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

中文:
定理 epi_of_target_iso_zero
  条件: {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0)
  结论: Epi f
  证明: ⟨fun {Z} g h _ => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

Depends on / 依赖: zero_of_source_iso_zero
-/
theorem epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f :=
  ⟨fun {Z} g h _ => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

/--
Definition of `idZeroEquivIsoZero` / `idZeroEquivIsoZero` 的定义

English:
definition idZeroEquivIsoZero
  signature: (X : C)
  body: { hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by cat_disch
  right_inv := by cat_disch

@[simp]

中文:
定义 idZeroEquivIsoZero
  签名: (X : C)
  定义体: { hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by cat_disch
  right_inv := by cat_disch

@[simp]

Depends on / 依赖: cat_disch, invFun, left_inv, right_inv, zero_of_target_iso_zero
-/
def idZeroEquivIsoZero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0) where
  toFun h :=
    { hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by cat_disch
  right_inv := by cat_disch

@[simp]
/--
theorem `idZeroEquivIsoZero_apply_hom` / 定理 `idZeroEquivIsoZero_apply_hom`

English:
theorem idZeroEquivIsoZero_apply_hom
  given: (X : C) (h : 𝟙 X = 0)
  statement: ((idZeroEquivIsoZero X) h).hom = 0
  proof: rfl

@[simp]

中文:
定理 idZeroEquivIsoZero_apply_hom
  条件: (X : C) (h : 𝟙 X = 0)
  结论: ((idZeroEquivIsoZero X) h).hom = 0
  证明: rfl

@[simp]
-/
theorem idZeroEquivIsoZero_apply_hom (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).hom = 0 :=
  rfl

@[simp]
/--
theorem `idZeroEquivIsoZero_apply_inv` / 定理 `idZeroEquivIsoZero_apply_inv`

English:
theorem idZeroEquivIsoZero_apply_inv
  given: (X : C) (h : 𝟙 X = 0)
  statement: ((idZeroEquivIsoZero X) h).inv = 0
  proof: rfl

中文:
定理 idZeroEquivIsoZero_apply_inv
  条件: (X : C) (h : 𝟙 X = 0)
  结论: ((idZeroEquivIsoZero X) h).inv = 0
  证明: rfl
-/
theorem idZeroEquivIsoZero_apply_inv (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).inv = 0 :=
  rfl

/-- If `0 : X ⟶ Y` is a monomorphism, then `X ≅ 0`. -/
@[simps]
/--
Definition of `isoZeroOfMonoZero` / `isoZeroOfMonoZero` 的定义

English:
definition isoZeroOfMonoZero
  signature: {X Y : C} (_ : Mono (0 : X ⟶ Y))
  body: 0
  inv := 0
  hom_inv_id := (cancel_mono (0 : X ⟶ Y)).mp (by simp)

中文:
定义 isoZeroOfMonoZero
  签名: {X Y : C} (_ : Mono (0 : X ⟶ Y))
  定义体: 0
  inv := 0
  hom_inv_id := (cancel_mono (0 : X ⟶ Y)).mp (by simp)
-/
def isoZeroOfMonoZero {X Y : C} (_ : Mono (0 : X ⟶ Y)) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_mono (0 : X ⟶ Y)).mp (by simp)

/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
/--
Definition of `isoZeroOfEpiZero` / `isoZeroOfEpiZero` 的定义

English:
definition isoZeroOfEpiZero
  signature: {X Y : C} (_ : Epi (0 : X ⟶ Y))
  body: 0
  inv := 0
  hom_inv_id := (cancel_epi (0 : X ⟶ Y)).mp (by simp)

中文:
定义 isoZeroOfEpiZero
  签名: {X Y : C} (_ : Epi (0 : X ⟶ Y))
  定义体: 0
  inv := 0
  hom_inv_id := (cancel_epi (0 : X ⟶ Y)).mp (by simp)
-/
def isoZeroOfEpiZero {X Y : C} (_ : Epi (0 : X ⟶ Y)) : Y ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_epi (0 : X ⟶ Y)).mp (by simp)

/--
Definition of `isoZeroOfMonoEqZero` / `isoZeroOfMonoEqZero` 的定义

English:
definition isoZeroOfMonoEqZero
  signature: {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0)
  body: by
  subst h
  apply isoZeroOfMonoZero (Y := Y) ‹_›

中文:
定义 isoZeroOfMonoEqZero
  签名: {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0)
  定义体: by
  subst h
  apply isoZeroOfMonoZero (Y := Y) ‹_›

Depends on / 依赖: isoZeroOfMonoZero
-/
def isoZeroOfMonoEqZero {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0) : X ≅ 0 := by
  subst h
  apply isoZeroOfMonoZero (Y := Y) ‹_›

/--
Definition of `isoZeroOfEpiEqZero` / `isoZeroOfEpiEqZero` 的定义

English:
definition isoZeroOfEpiEqZero
  signature: {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0)
  body: by
  subst h
  apply isoZeroOfEpiZero (X := X) ‹_›

中文:
定义 isoZeroOfEpiEqZero
  签名: {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0)
  定义体: by
  subst h
  apply isoZeroOfEpiZero (X := X) ‹_›

Depends on / 依赖: isoZeroOfEpiZero
-/
def isoZeroOfEpiEqZero {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0) : Y ≅ 0 := by
  subst h
  apply isoZeroOfEpiZero (X := X) ‹_›

/--
Definition of `isoOfIsIsomorphicZero` / `isoOfIsIsomorphicZero` 的定义

English:
definition isoOfIsIsomorphicZero
  signature: {X : C} (P : IsIsomorphic X 0)
  body: 0
  inv := 0
  hom_inv_id := by
    have P := P.some
    rw [← P.hom_inv_id]; rw [← Category.id_comp P.inv]
    apply Eq.symm
    simp only [id_comp, Iso.hom_inv_id, comp_zero]
    apply (idZeroEquivIsoZero X).invFun P
  inv_hom_id := by simp

中文:
定义 isoOfIsIsomorphicZero
  签名: {X : C} (P : IsIsomorphic X 0)
  定义体: 0
  inv := 0
  hom_inv_id := by
    have P := P.some
    rw [← P.hom_inv_id]; rw [← Category.id_comp P.inv]
    apply Eq.symm
    simp only [id_comp, Iso.hom_inv_id, comp_zero]
    apply (idZeroEquivIsoZero X).invFun P
  inv_hom_id := by simp
-/
def isoOfIsIsomorphicZero {X : C} (P : IsIsomorphic X 0) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by
    have P := P.some
    rw [← P.hom_inv_id]; rw [← Category.id_comp P.inv]
    apply Eq.symm
    simp only [id_comp, Iso.hom_inv_id, comp_zero]
    apply (idZeroEquivIsoZero X).invFun P
  inv_hom_id := by simp

end

section IsIso

variable [HasZeroMorphisms C]

/--
Definition of `isIsoZeroEquiv` / `isIsoZeroEquiv` 的定义

English:
definition isIsoZeroEquiv
  signature: (X Y : C)
  body: by
    intro i
    rw [← IsIso.hom_inv_id (0 : X ⟶ Y)]
    rw [← IsIso.inv_hom_id (0 : X ⟶ Y)]
    simp only [comp_zero, and_self, zero_comp]
  invFun h := ⟨⟨(0 : Y ⟶ X), by cat_disch⟩⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 isIsoZeroEquiv
  签名: (X Y : C)
  定义体: by
    intro i
    rw [← IsIso.hom_inv_id (0 : X ⟶ Y)]
    rw [← IsIso.inv_hom_id (0 : X ⟶ Y)]
    simp only [comp_zero, and_self, zero_comp]
  invFun h := ⟨⟨(0 : Y ⟶ X), by cat_disch⟩⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: IsIso.hom_inv_id, IsIso.inv_hom_id, and_self, cat_disch, comp_zero, hom_inv_id, invFun, inv_hom_id, left_inv, right_inv, zero_comp
-/
def isIsoZeroEquiv (X Y : C) : IsIso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0 where
  toFun := by
    intro i
    rw [← IsIso.hom_inv_id (0 : X ⟶ Y)]
    rw [← IsIso.inv_hom_id (0 : X ⟶ Y)]
    simp only [comp_zero, and_self, zero_comp]
  invFun h := ⟨⟨(0 : Y ⟶ X), by cat_disch⟩⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

/--
Definition of `isIsoZeroSelfEquiv` / `isIsoZeroSelfEquiv` 的定义

English:
definition isIsoZeroSelfEquiv
  signature: (X : C)
  body: by simpa using isIsoZeroEquiv X X

中文:
定义 isIsoZeroSelfEquiv
  签名: (X : C)
  定义体: by simpa using isIsoZeroEquiv X X

Depends on / 依赖: isIsoZeroEquiv
-/
def isIsoZeroSelfEquiv (X : C) : IsIso (0 : X ⟶ X) ≃ 𝟙 X = 0 := by simpa using isIsoZeroEquiv X X

variable [HasZeroObject C]

open ZeroObject

/--
Definition of `isIsoZeroEquivIsoZero` / `isIsoZeroEquivIsoZero` 的定义

English:
definition isIsoZeroEquivIsoZero
  signature: (X Y : C)
  body: by
  -- This is lame, because `Prod` can't cope with `Prop`, so we can't use `Equiv.prodCongr`.
  refine (isIsoZeroEquiv X Y).trans ?_
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X).symm eX
    · exact (idZeroEquivIsoZero Y).symm eY
  · rintro ⟨hX, hY⟩


中文:
定义 isIsoZeroEquivIsoZero
  签名: (X Y : C)
  定义体: by
  -- This is lame, because `Prod` can't cope with `Prop`, so we can't use `Equiv.prodCongr`.
  refine (isIsoZeroEquiv X Y).trans ?_
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X).symm eX
    · exact (idZeroEquivIsoZero Y).symm eY
  · rintro ⟨hX, hY⟩

-/
def isIsoZeroEquivIsoZero (X Y : C) : IsIso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0) := by
  -- This is lame, because `Prod` can't cope with `Prop`, so we can't use `Equiv.prodCongr`.
  refine (isIsoZeroEquiv X Y).trans ?_
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X).symm eX
    · exact (idZeroEquivIsoZero Y).symm eY
  · rintro ⟨hX, hY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X) hX
    · exact (idZeroEquivIsoZero Y) hY
  · cat_disch
  · cat_disch

/--
lemma `isIsoZero_iff_source_target_isZero` / 引理 `isIsoZero_iff_source_target_isZero`

English:
lemma isIsoZero_iff_source_target_isZero
  given: (X Y : C)
  statement: IsIso (0 : X ⟶ Y) ↔ IsZero X ∧ IsZero Y
  proof: by
  constructor
  · intro h
    let h' := isIsoZeroEquivIsoZero _ _ h
    exact ⟨(isZero_zero _).of_iso h'.1, (isZero_zero _).of_iso h'.2⟩
  · intro ⟨hX, hY⟩
    exact (isIsoZeroEquivIsoZero _ _).symm ⟨hX.isoZero, hY.isoZero⟩

中文:
引理 isIsoZero_iff_source_target_isZero
  条件: (X Y : C)
  结论: IsIso (0 : X ⟶ Y) ↔ IsZero X ∧ IsZero Y
  证明: by
  constructor
  · intro h
    let h' := isIsoZeroEquivIsoZero _ _ h
    exact ⟨(isZero_zero _).of_iso h'.1, (isZero_zero _).of_iso h'.2⟩
  · intro ⟨hX, hY⟩
    exact (isIsoZeroEquivIsoZero _ _).symm ⟨hX.isoZero, hY.isoZero⟩

Depends on / 依赖: hX.isoZero, hY.isoZero, isIsoZeroEquivIsoZero, isZero_zero, isoZero, of_iso
-/
lemma isIsoZero_iff_source_target_isZero (X Y : C) : IsIso (0 : X ⟶ Y) ↔ IsZero X ∧ IsZero Y := by
  constructor
  · intro h
    let h' := isIsoZeroEquivIsoZero _ _ h
    exact ⟨(isZero_zero _).of_iso h'.1, (isZero_zero _).of_iso h'.2⟩
  · intro ⟨hX, hY⟩
    exact (isIsoZeroEquivIsoZero _ _).symm ⟨hX.isoZero, hY.isoZero⟩

/--
theorem `isIso_of_source_target_iso_zero` / 定理 `isIso_of_source_target_iso_zero`

English:
theorem isIso_of_source_target_iso_zero
  given: {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0)
  proof: by
  rw [zero_of_source_iso_zero f i]
  exact (isIsoZeroEquivIsoZero _ _).invFun ⟨i, j⟩

中文:
定理 isIso_of_source_target_iso_zero
  条件: {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0)
  证明: by
  rw [zero_of_source_iso_zero f i]
  exact (isIsoZeroEquivIsoZero _ _).invFun ⟨i, j⟩

Depends on / 依赖: invFun, isIsoZeroEquivIsoZero, zero_of_source_iso_zero
-/
theorem isIso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) :
    IsIso f := by
  rw [zero_of_source_iso_zero f i]
  exact (isIsoZeroEquivIsoZero _ _).invFun ⟨i, j⟩

/--
Definition of `isIsoZeroSelfEquivIsoZero` / `isIsoZeroSelfEquivIsoZero` 的定义

English:
definition isIsoZeroSelfEquivIsoZero
  signature: (X : C)
  body: (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv

中文:
定义 isIsoZeroSelfEquivIsoZero
  签名: (X : C)
  定义体: (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv

Depends on / 依赖: isIsoZeroEquivIsoZero, subsingletonProdSelfEquiv
-/
def isIsoZeroSelfEquivIsoZero (X : C) : IsIso (0 : X ⟶ X) ≃ (X ≅ 0) :=
  (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv

end IsIso

/--
theorem `hasZeroObject_of_hasInitial_object` / 定理 `hasZeroObject_of_hasInitial_object`

English:
theorem hasZeroObject_of_hasInitial_object
  given: [HasZeroMorphisms C] [HasInitial C]
  proof: by
  refine ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ 0 := by congr!; subsingleton
    _ = 0 := HasZeroMorphisms.comp_zero _ _

中文:
定理 hasZeroObject_of_hasInitial_object
  条件: [HasZeroMorphisms C] [HasInitial C]
  证明: by
  refine ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ 0 := by congr!; subsingleton
    _ = 0 := HasZeroMorphisms.comp_zero _ _

Depends on / 依赖: Category, Category.comp_id, HasZeroMorphisms, HasZeroMorphisms.comp_zero, cat_disch, comp_id, comp_zero, subsingleton
-/
theorem hasZeroObject_of_hasInitial_object [HasZeroMorphisms C] [HasInitial C] :
    HasZeroObject C := by
  refine ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ 0 := by congr!; subsingleton
    _ = 0 := HasZeroMorphisms.comp_zero _ _

/--
theorem `hasZeroObject_of_hasTerminal_object` / 定理 `hasZeroObject_of_hasTerminal_object`

English:
theorem hasZeroObject_of_hasTerminal_object
  given: [HasZeroMorphisms C] [HasTerminal C]
  proof: by
  refine ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = 0 ≫ f := by congr!; subsingleton
    _ = 0 := zero_comp

中文:
定理 hasZeroObject_of_hasTerminal_object
  条件: [HasZeroMorphisms C] [HasTerminal C]
  证明: by
  refine ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = 0 ≫ f := by congr!; subsingleton
    _ = 0 := zero_comp

Depends on / 依赖: Category, Category.id_comp, cat_disch, id_comp, subsingleton, zero_comp
-/
theorem hasZeroObject_of_hasTerminal_object [HasZeroMorphisms C] [HasTerminal C] :
    HasZeroObject C := by
  refine ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = 0 ≫ f := by congr!; subsingleton
    _ = 0 := zero_comp

section Image

variable [HasZeroMorphisms C]

/--
theorem `image_ι_comp_eq_zero` / 定理 `image_ι_comp_eq_zero`

English:
theorem image_ι_comp_eq_zero
  statement: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
  proof: zero_of_epi_comp (factorThruImage f) by simp [h]

中文:
定理 image_ι_comp_eq_zero
  结论: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
  证明: zero_of_epi_comp (factorThruImage f) by simp [h]

Depends on / 依赖: factorThruImage, zero_of_epi_comp
-/
theorem image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
    [Epi (factorThruImage f)] (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
zero_of_epi_comp (factorThruImage f) by simp [h]

/--
theorem `comp_factorThruImage_eq_zero` / 定理 `comp_factorThruImage_eq_zero`

English:
theorem comp_factorThruImage_eq_zero
  statement: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
  proof: zero_of_comp_mono (image.ι g) by simp [h]

中文:
定理 comp_factorThruImage_eq_zero
  结论: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
  证明: zero_of_comp_mono (image.ι g) by simp [h]

Depends on / 依赖: AddCommGroup, zero_of_comp_mono
-/
theorem comp_factorThruImage_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
    (h : f ≫ g = 0) : f ≫ factorThruImage g = 0 :=
zero_of_comp_mono (image.ι g) by simp [h]

variable [HasZeroObject C]

open ZeroObject

/-- The zero morphism has a `MonoFactorisation` through the zero object.
-/
@[simps]
/--
Definition of `monoFactorisationZero` / `monoFactorisationZero` 的定义

English:
definition monoFactorisationZero
  signature: (X Y : C)
  body: 0
  m := 0
  e := 0

中文:
定义 monoFactorisationZero
  签名: (X Y : C)
  定义体: 0
  m := 0
  e := 0
-/
def monoFactorisationZero (X Y : C) : MonoFactorisation (0 : X ⟶ Y) where
  I := 0
  m := 0
  e := 0

/--
Definition of `imageFactorisationZero` / `imageFactorisationZero` 的定义

English:
definition imageFactorisationZero
  signature: (X Y : C)
  body: monoFactorisationZero X Y
  isImage := { lift := fun _ => 0 }

中文:
定义 imageFactorisationZero
  签名: (X Y : C)
  定义体: monoFactorisationZero X Y
  isImage := { lift := fun _ => 0 }

Depends on / 依赖: monoFactorisationZero
-/
def imageFactorisationZero (X Y : C) : ImageFactorisation (0 : X ⟶ Y) where
  F := monoFactorisationZero X Y
  isImage := { lift := fun _ => 0 }

/--
Instance `hasImage_zero` / 实例 `hasImage_zero`

English:
instance hasImage_zero
  signature: {X Y : C}
  body: HasImage.mk imageFactorisationZero _ _

中文:
实例 hasImage_zero
  签名: {X Y : C}
  定义体: HasImage.mk imageFactorisationZero _ _

Depends on / 依赖: HasImage, HasImage.mk, imageFactorisationZero
-/
instance hasImage_zero {X Y : C} : HasImage (0 : X ⟶ Y) :=
HasImage.mk imageFactorisationZero _ _

/--
Definition of `imageZero` / `imageZero` 的定义

English:
definition imageZero
  signature: {X Y : C}
  body: IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).isImage

中文:
定义 imageZero
  签名: {X Y : C}
  定义体: IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).isImage

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, imageFactorisationZero, isImage, isoExt
-/
def imageZero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
  IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).isImage

/--
Definition of `imageZero'` / `imageZero'` 的定义

English:
definition imageZero'
  signature: {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f]
  body: image.eqToIso h ≪≫ imageZero

中文:
定义 imageZero'
  签名: {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f]
  定义体: image.eqToIso h ≪≫ imageZero

Depends on / 依赖: eqToIso, image.eqToIso, imageZero
-/
def imageZero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] : image f ≅ 0 :=
  image.eqToIso h ≪≫ imageZero

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `image.ι_zero` / 定理 `image.ι_zero`

English:
theorem image.ι_zero
  given: {X Y : C} [HasImage (0 : X ⟶ Y)]
  statement: image.ι (0 : X ⟶ Y) = 0
  proof: by
  rw [← image.lift_fac (monoFactorisationZero X Y)]
  simp

中文:
定理 image.ι_zero
  条件: {X Y : C} [HasImage (0 : X ⟶ Y)]
  结论: image.ι (0 : X ⟶ Y) = 0
  证明: by
  rw [← image.lift_fac (monoFactorisationZero X Y)]
  simp

Depends on / 依赖: image.lift_fac, lift_fac, monoFactorisationZero
-/
theorem image.ι_zero {X Y : C} [HasImage (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 := by
  rw [← image.lift_fac (monoFactorisationZero X Y)]
  simp

/-- If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
/--
theorem `image.ι_zero'` / 定理 `image.ι_zero'`

English:
theorem image.ι_zero'
  given: [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f]
  proof: by
  rw [image.eq_fac h]
  simp

中文:
定理 image.ι_zero'
  条件: [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f]
  证明: by
  rw [image.eq_fac h]
  simp

Depends on / 依赖: eq_fac, image.eq_fac
-/
theorem image.ι_zero' [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] :
    image.ι f = 0 := by
  rw [image.eq_fac h]
  simp

end Image

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isSplitMono_sigma_ι` / 实例 `isSplitMono_sigma_ι`

English:
instance isSplitMono_sigma_ι
  signature: {β : Type u'} [HasZeroMorphisms C] (f : β -> C)
  body: by
  classical exact IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }

中文:
实例 isSplitMono_sigma_ι
  签名: {β : 类型u'} [HasZeroMorphisms C] (f : β -> C)
  定义体: by
  classical exact IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, Pi.single, Sigma.desc, classical, retraction, single
-/
instance isSplitMono_sigma_ι {β : Type u'} [HasZeroMorphisms C] (f : β -> C)
    [HasColimit (Discrete.functor f)] (b : β) : IsSplitMono (Sigma.ι f b) := by
  classical exact IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isSplitEpi_pi_π` / 实例 `isSplitEpi_pi_π`

English:
instance isSplitEpi_pi_π
  signature: {β : Type u'} [HasZeroMorphisms C] (f : β -> C)
  body: by
  classical exact IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }

中文:
实例 isSplitEpi_pi_π
  签名: {β : 类型u'} [HasZeroMorphisms C] (f : β -> C)
  定义体: by
  classical exact IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, Pi.lift, Pi.single, classical, section_, single
-/
instance isSplitEpi_pi_π {β : Type u'} [HasZeroMorphisms C] (f : β -> C)
    [HasLimit (Discrete.functor f)] (b : β) : IsSplitEpi (Pi.π f b) := by
  classical exact IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isSplitMono_coprod_inl` / 实例 `isSplitMono_coprod_inl`

English:
instance isSplitMono_coprod_inl
  signature: [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)]
  body: IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }

中文:
实例 isSplitMono_coprod_inl
  签名: [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)]
  定义体: IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, coprod, coprod.desc, retraction
-/
instance isSplitMono_coprod_inl [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inl : X ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isSplitMono_coprod_inr` / 实例 `isSplitMono_coprod_inr`

English:
instance isSplitMono_coprod_inr
  signature: [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)]
  body: IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }

中文:
实例 isSplitMono_coprod_inr
  签名: [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)]
  定义体: IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, coprod, coprod.desc, retraction
-/
instance isSplitMono_coprod_inr [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isSplitEpi_prod_fst` / 实例 `isSplitEpi_prod_fst`

English:
instance isSplitEpi_prod_fst
  signature: [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)]
  body: IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }

中文:
实例 isSplitEpi_prod_fst
  签名: [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)]
  定义体: IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, prod.lift, section_
-/
instance isSplitEpi_prod_fst [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.fst : X ⨯ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isSplitEpi_prod_snd` / 实例 `isSplitEpi_prod_snd`

English:
instance isSplitEpi_prod_snd
  signature: [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)]
  body: IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }

中文:
实例 isSplitEpi_prod_snd
  签名: [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)]
  定义体: IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, prod.lift, section_
-/
instance isSplitEpi_prod_snd [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.snd : X ⨯ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }


section

variable [HasZeroMorphisms C] [HasZeroObject C] {F : D ⥤ C}

/--
Definition of `IsLimit.ofIsZero` / `IsLimit.ofIsZero` 的定义

English:
definition IsLimit.ofIsZero
  signature: (c : Cone F) (hF : IsZero F) (hc : IsZero c.pt)
  body: 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_tgt _ _
  uniq _ _ _ := hc.eq_of_tgt _ _

中文:
定义 IsLimit.ofIsZero
  签名: (c : Cone F) (hF : IsZero F) (hc : IsZero c.pt)
  定义体: 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_tgt _ _
  uniq _ _ _ := hc.eq_of_tgt _ _
-/
def IsLimit.ofIsZero (c : Cone F) (hF : IsZero F) (hc : IsZero c.pt) : IsLimit c where
  lift _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_tgt _ _
  uniq _ _ _ := hc.eq_of_tgt _ _

/--
Definition of `IsColimit.ofIsZero` / `IsColimit.ofIsZero` 的定义

English:
definition IsColimit.ofIsZero
  signature: (c : Cocone F) (hF : IsZero F) (hc : IsZero c.pt)
  body: 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_src _ _
  uniq _ _ _ := hc.eq_of_src _ _

中文:
定义 IsColimit.ofIsZero
  签名: (c : Cocone F) (hF : IsZero F) (hc : IsZero c.pt)
  定义体: 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_src _ _
  uniq _ _ _ := hc.eq_of_src _ _
-/
def IsColimit.ofIsZero (c : Cocone F) (hF : IsZero F) (hc : IsZero c.pt) : IsColimit c where
  desc _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_src _ _
  uniq _ _ _ := hc.eq_of_src _ _

/--
lemma `IsLimit.isZero_pt` / 引理 `IsLimit.isZero_pt`

English:
lemma IsLimit.isZero_pt
  given: {c : Cone F} (hc : IsLimit c) (hF : IsZero F)
  statement: IsZero c.pt
  proof: (isZero_zero C).of_iso (IsLimit.conePointUniqueUpToIso hc
    (IsLimit.ofIsZero (Cone.mk 0 0) hF (isZero_zero C)))

中文:
引理 IsLimit.isZero_pt
  条件: {c : Cone F} (hc : IsLimit c) (hF : IsZero F)
  结论: IsZero c.pt
  证明: (isZero_zero C).of_iso (IsLimit.conePointUniqueUpToIso hc
    (IsLimit.ofIsZero (Cone.mk 0 0) hF (isZero_zero C)))

Depends on / 依赖: Cone.mk, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.ofIsZero, cancel_epi, comp_neg, conePointUniqueUpToIso, isZero_zero, neg_comp, neg_inj, ofIsZero, of_iso
-/
lemma IsLimit.isZero_pt {c : Cone F} (hc : IsLimit c) (hF : IsZero F) : IsZero c.pt :=
  (isZero_zero C).of_iso (IsLimit.conePointUniqueUpToIso hc
    (IsLimit.ofIsZero (Cone.mk 0 0) hF (isZero_zero C)))

/--
lemma `IsColimit.isZero_pt` / 引理 `IsColimit.isZero_pt`

English:
lemma IsColimit.isZero_pt
  given: {c : Cocone F} (hc : IsColimit c) (hF : IsZero F)
  statement: IsZero c.pt
  proof: (isZero_zero C).of_iso (IsColimit.coconePointUniqueUpToIso hc
    (IsColimit.ofIsZero (Cocone.mk 0 0) hF (isZero_zero C)))

中文:
引理 IsColimit.isZero_pt
  条件: {c : Cocone F} (hc : IsColimit c) (hF : IsZero F)
  结论: IsZero c.pt
  证明: (isZero_zero C).of_iso (IsColimit.coconePointUniqueUpToIso hc
    (IsColimit.ofIsZero (Cocone.mk 0 0) hF (isZero_zero C)))

Depends on / 依赖: Cocone, Cocone.mk, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.ofIsZero, cancel_mono, coconePointUniqueUpToIso, comp_neg, isZero_zero, neg_comp, neg_inj, ofIsZero, of_iso
-/
lemma IsColimit.isZero_pt {c : Cocone F} (hc : IsColimit c) (hF : IsZero F) : IsZero c.pt :=
  (isZero_zero C).of_iso (IsColimit.coconePointUniqueUpToIso hc
    (IsColimit.ofIsZero (Cocone.mk 0 0) hF (isZero_zero C)))

/-- Given a functor `F : D ⥤ C`, zero morphisms on `C` induce zero morphisms on
`D` by taking preimages. -/
@[reducible]
/--
Definition of `_root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms` / `_root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms` 的定义

English:
definition _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms
  signature: (hF : F.FullyFaithful)
  body: ⟨hF.preimage 0⟩
  comp_zero f _ := by
    apply hF.map_injective
    change F.map (f ≫ (hF.preimage _)) = F.map (hF.preimage _)
    simp
  zero_comp _ _ _ f := by
    apply hF.map_injective
    change F.map ((hF.preimage _) ≫ f) = F.map (hF.preimage _)
    simp

omit [HasZeroObject C] in

中文:
定义 _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms
  签名: (hF : F.FullyFaithful)
  定义体: ⟨hF.preimage 0⟩
  comp_zero f _ := by
    apply hF.map_injective
    change F.map (f ≫ (hF.preimage _)) = F.map (hF.preimage _)
    simp
  zero_comp _ _ _ f := by
    apply hF.map_injective
    change F.map ((hF.preimage _) ≫ f) = F.map (hF.preimage _)
    simp

omit [HasZeroObject C] in

Depends on / 依赖: HasZeroMorphisms, hF.preimage, preadditiveHasZeroMorphisms, preimage
-/
def _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms (hF : F.FullyFaithful) :
    HasZeroMorphisms D where
  zero X Y := ⟨hF.preimage 0⟩
  comp_zero f _ := by
    apply hF.map_injective
    change F.map (f ≫ (hF.preimage _)) = F.map (hF.preimage _)
    simp
  zero_comp _ _ _ f := by
    apply hF.map_injective
    change F.map ((hF.preimage _) ≫ f) = F.map (hF.preimage _)
    simp

omit [HasZeroObject C] in
/--
lemma `_root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def` / 引理 `_root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def`

English:
lemma _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def
  statement: (hF : F.FullyFaithful)
  proof: hF.hasZeroMorphisms
    (0 : X ⟶ Y) = hF.preimage 0 := rfl

中文:
引理 _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def
  结论: (hF : F.FullyFaithful)
  证明: hF.hasZeroMorphisms
    (0 : X ⟶ Y) = hF.preimage 0 := rfl

Depends on / 依赖: End.monoid, HasZeroMorphisms, HasZeroMorphisms.comp_zero, HasZeroMorphisms.zero_comp, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, comp_add, comp_zero, hF.hasZeroMorphisms, hasZeroMorphisms, left_distrib, monoid, mul_zero, right_distrib, zero_comp, zero_mul
-/
lemma _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def (hF : F.FullyFaithful)
    (X Y : D) : letI : HasZeroMorphisms D := hF.hasZeroMorphisms
    (0 : X ⟶ Y) = hF.preimage 0 := rfl

end

section

variable [HasZeroMorphisms C]

/--
lemma `IsTerminal.isZero` / 引理 `IsTerminal.isZero`

English:
lemma IsTerminal.isZero
  given: {X : C} (hX : IsTerminal X)
  statement: IsZero X
  proof: by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

中文:
引理 IsTerminal.isZero
  条件: {X : C} (hX : IsTerminal X)
  结论: IsZero X
  证明: by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

Depends on / 依赖: AddCommGroup, IsZero, IsZero.iff_id_eq_zero, Semiring, hX.hom_ext, hom_ext, iff_id_eq_zero, neg_add_cancel
-/
lemma IsTerminal.isZero {X : C} (hX : IsTerminal X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

/--
lemma `IsInitial.isZero` / 引理 `IsInitial.isZero`

English:
lemma IsInitial.isZero
  given: {X : C} (hX : IsInitial X)
  statement: IsZero X
  proof: by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

中文:
引理 IsInitial.isZero
  条件: {X : C} (hX : IsInitial X)
  结论: IsZero X
  证明: by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, hX.hom_ext, hom_ext, iff_id_eq_zero
-/
lemma IsInitial.isZero {X : C} (hX : IsInitial X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

end

section PiIota

variable [HasZeroMorphisms C] {β : Type w} [DecidableEq β] (f : β -> C) [HasProduct f]

/--
Definition of `Pi.ι` / `Pi.ι` 的定义

English:
definition Pi.ι
  signature: (b : β)
  body: Pi.lift (Function.update (fun _ => 0) b (𝟙 _))

中文:
定义 Pi.ι
  签名: (b : β)
  定义体: Pi.lift (Function.update (fun _ => 0) b (𝟙 _))

Depends on / 依赖: Function, Function.update, Pi.lift, update
-/
def Pi.ι (b : β) : f b ⟶ ∏ᶜ f :=
  Pi.lift (Function.update (fun _ => 0) b (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
/--
lemma `Pi.ι_π_eq_id` / 引理 `Pi.ι_π_eq_id`

English:
lemma Pi.ι_π_eq_id
  given: (b : β)
  statement: Pi.ι f b ≫ Pi.π f b = 𝟙 _
  proof: by
  simp [Pi.ι]

中文:
引理 Pi.ι_π_eq_id
  条件: (b : β)
  结论: Pi.ι f b ≫ Pi.π f b = 𝟙 _
  证明: by
  simp [Pi.ι]
-/
lemma Pi.ι_π_eq_id (b : β) : Pi.ι f b ≫ Pi.π f b = 𝟙 _ := by
  simp [Pi.ι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, grind =]
/--
lemma `Pi.ι_π_of_ne` / 引理 `Pi.ι_π_of_ne`

English:
lemma Pi.ι_π_of_ne
  given: {b c : β} (h : b != c)
  statement: Pi.ι f b ≫ Pi.π f c = 0
  proof: by
  simp [Pi.ι, Function.update_of_ne h.symm]

@[reassoc]

中文:
引理 Pi.ι_π_of_ne
  条件: {b c : β} (h : b != c)
  结论: Pi.ι f b ≫ Pi.π f c = 0
  证明: by
  simp [Pi.ι, Function.update_of_ne h.symm]

@[reassoc]

Depends on / 依赖: Function, Function.update_of_ne, h.symm, update_of_ne
-/
lemma Pi.ι_π_of_ne {b c : β} (h : b != c) : Pi.ι f b ≫ Pi.π f c = 0 := by
  simp [Pi.ι, Function.update_of_ne h.symm]

@[reassoc]
/--
lemma `Pi.ι_π` / 引理 `Pi.ι_π`

English:
lemma Pi.ι_π
  given: (b c : β)
  proof: by
  grind [CategoryTheory.eqToHom_refl]

中文:
引理 Pi.ι_π
  条件: (b c : β)
  证明: by
  grind [CategoryTheory.eqToHom_refl]

Depends on / 依赖: CategoryTheory, CategoryTheory.eqToHom_refl, eqToHom_refl
-/
lemma Pi.ι_π (b c : β) :
    Pi.ι f b ≫ Pi.π f c = if h : b = c then eqToHom (congrArg f h) else 0 := by
  grind [CategoryTheory.eqToHom_refl]

instance (b : β) : Mono (Pi.ι f b) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ Pi.π f b) e

end PiIota

section SigmaPi

variable [HasZeroMorphisms C] {β : Type w} [DecidableEq β] (f : β -> C) [HasCoproduct f]

/--
Definition of `Sigma.π` / `Sigma.π` 的定义

English:
definition Sigma.π
  signature: (b : β)
  body: Limits.Sigma.desc (Function.update (fun _ => 0) b (𝟙 _))

中文:
定义 Sigma.π
  签名: (b : β)
  定义体: Limits.Sigma.desc (Function.update (fun _ => 0) b (𝟙 _))

Depends on / 依赖: Function, Function.update, Limits, Limits.Sigma.desc, update
-/
def Sigma.π (b : β) : ∐ f ⟶ f b :=
  Limits.Sigma.desc (Function.update (fun _ => 0) b (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
/--
lemma `Sigma.ι_π_eq_id` / 引理 `Sigma.ι_π_eq_id`

English:
lemma Sigma.ι_π_eq_id
  given: (b : β)
  statement: Sigma.ι f b ≫ Sigma.π f b = 𝟙 _
  proof: by
  simp [Sigma.π]

中文:
引理 Sigma.ι_π_eq_id
  条件: (b : β)
  结论: Sigma.ι f b ≫ Sigma.π f b = 𝟙 _
  证明: by
  simp [Sigma.π]
-/
lemma Sigma.ι_π_eq_id (b : β) : Sigma.ι f b ≫ Sigma.π f b = 𝟙 _ := by
  simp [Sigma.π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, grind =]
/--
lemma `Sigma.ι_π_of_ne` / 引理 `Sigma.ι_π_of_ne`

English:
lemma Sigma.ι_π_of_ne
  given: {b c : β} (h : b != c)
  statement: Sigma.ι f b ≫ Sigma.π f c = 0
  proof: by
  simp [Sigma.π, Function.update_of_ne h]

@[reassoc]

中文:
引理 Sigma.ι_π_of_ne
  条件: {b c : β} (h : b != c)
  结论: Sigma.ι f b ≫ Sigma.π f c = 0
  证明: by
  simp [Sigma.π, Function.update_of_ne h]

@[reassoc]

Depends on / 依赖: Function, Function.update_of_ne, update_of_ne
-/
lemma Sigma.ι_π_of_ne {b c : β} (h : b != c) : Sigma.ι f b ≫ Sigma.π f c = 0 := by
  simp [Sigma.π, Function.update_of_ne h]

@[reassoc]
/--
theorem `Sigma.ι_π` / 定理 `Sigma.ι_π`

English:
theorem Sigma.ι_π
  given: (b c : β)
  proof: by
  grind [CategoryTheory.eqToHom_refl]

中文:
定理 Sigma.ι_π
  条件: (b c : β)
  证明: by
  grind [CategoryTheory.eqToHom_refl]

Depends on / 依赖: CategoryTheory, CategoryTheory.eqToHom_refl, eqToHom_refl
-/
theorem Sigma.ι_π (b c : β) :
    Sigma.ι f b ≫ Sigma.π f c = if h : b = c then eqToHom (congrArg f h) else 0 := by
  grind [CategoryTheory.eqToHom_refl]

instance (b : β) : Epi (Sigma.π f b) where
  left_cancellation _ _ e := by simpa using congrArg (Sigma.ι f b ≫ ·) e

end SigmaPi

section ProdInlInr

variable [HasZeroMorphisms C] (X Y : C) [HasBinaryProduct X Y]

/--
Definition of `prod.inl` / `prod.inl` 的定义

English:
definition prod.inl
  signature: : X ⟶ X ⨯ Y
  body: prod.lift (𝟙 _) 0

中文:
定义 prod.inl
  签名: : X ⟶ X ⨯ Y
  定义体: prod.lift (𝟙 _) 0

Depends on / 依赖: prod.lift
-/
def prod.inl : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 _) 0

/--
Definition of `prod.inr` / `prod.inr` 的定义

English:
definition prod.inr
  signature: : Y ⟶ X ⨯ Y
  body: prod.lift 0 (𝟙 _)

中文:
定义 prod.inr
  签名: : Y ⟶ X ⨯ Y
  定义体: prod.lift 0 (𝟙 _)

Depends on / 依赖: prod.lift
-/
def prod.inr : Y ⟶ X ⨯ Y :=
  prod.lift 0 (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prod.inl_fst` / 引理 `prod.inl_fst`

English:
lemma prod.inl_fst
  statement: prod.inl X Y ≫ prod.fst = 𝟙 X
  proof: by
  simp [prod.inl]

中文:
引理 prod.inl_fst
  结论: prod.inl X Y ≫ prod.fst = 𝟙 X
  证明: by
  simp [prod.inl]

Depends on / 依赖: prod.inl
-/
lemma prod.inl_fst : prod.inl X Y ≫ prod.fst = 𝟙 X := by
  simp [prod.inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prod.inl_snd` / 引理 `prod.inl_snd`

English:
lemma prod.inl_snd
  statement: prod.inl X Y ≫ prod.snd = 0
  proof: by
  simp [prod.inl]

中文:
引理 prod.inl_snd
  结论: prod.inl X Y ≫ prod.snd = 0
  证明: by
  simp [prod.inl]

Depends on / 依赖: prod.inl
-/
lemma prod.inl_snd : prod.inl X Y ≫ prod.snd = 0 := by
  simp [prod.inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prod.inr_fst` / 引理 `prod.inr_fst`

English:
lemma prod.inr_fst
  statement: prod.inr X Y ≫ prod.fst = 0
  proof: by
  simp [prod.inr]

中文:
引理 prod.inr_fst
  结论: prod.inr X Y ≫ prod.fst = 0
  证明: by
  simp [prod.inr]

Depends on / 依赖: prod.inr
-/
lemma prod.inr_fst : prod.inr X Y ≫ prod.fst = 0 := by
  simp [prod.inr]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `prod.inr_snd` / 引理 `prod.inr_snd`

English:
lemma prod.inr_snd
  statement: prod.inr X Y ≫ prod.snd = 𝟙 Y
  proof: by
  simp [prod.inr]

中文:
引理 prod.inr_snd
  结论: prod.inr X Y ≫ prod.snd = 𝟙 Y
  证明: by
  simp [prod.inr]

Depends on / 依赖: prod.inr
-/
lemma prod.inr_snd : prod.inr X Y ≫ prod.snd = 𝟙 Y := by
  simp [prod.inr]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (prod.inl X Y)
  body: by simpa using congrArg (· ≫ prod.fst) e

中文:
实例 :
  签名: Mono (prod.inl X Y)
  定义体: by simpa using congrArg (· ≫ prod.fst) e

Depends on / 依赖: prod.fst
-/
instance : Mono (prod.inl X Y) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ prod.fst) e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (prod.inr X Y)
  body: by simpa using congrArg (· ≫ prod.snd) e

中文:
实例 :
  签名: Mono (prod.inr X Y)
  定义体: by simpa using congrArg (· ≫ prod.snd) e

Depends on / 依赖: prod.snd
-/
instance : Mono (prod.inr X Y) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ prod.snd) e

end ProdInlInr

section CoprodFstSnd

variable [HasZeroMorphisms C] (X Y : C) [HasBinaryCoproduct X Y]

/--
Definition of `coprod.fst` / `coprod.fst` 的定义

English:
definition coprod.fst
  signature: : X ⨿ Y ⟶ X
  body: coprod.desc (𝟙 _) 0

中文:
定义 coprod.fst
  签名: : X ⨿ Y ⟶ X
  定义体: coprod.desc (𝟙 _) 0

Depends on / 依赖: coprod, coprod.desc
-/
def coprod.fst : X ⨿ Y ⟶ X :=
  coprod.desc (𝟙 _) 0

/--
Definition of `coprod.snd` / `coprod.snd` 的定义

English:
definition coprod.snd
  signature: : X ⨿ Y ⟶ Y
  body: coprod.desc 0 (𝟙 _)

中文:
定义 coprod.snd
  签名: : X ⨿ Y ⟶ Y
  定义体: coprod.desc 0 (𝟙 _)

Depends on / 依赖: coprod, coprod.desc
-/
def coprod.snd : X ⨿ Y ⟶ Y :=
  coprod.desc 0 (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `coprod.inl_fst` / 引理 `coprod.inl_fst`

English:
lemma coprod.inl_fst
  statement: coprod.inl ≫ coprod.fst X Y = 𝟙 X
  proof: by
  simp [coprod.fst]

中文:
引理 coprod.inl_fst
  结论: coprod.inl ≫ coprod.fst X Y = 𝟙 X
  证明: by
  simp [coprod.fst]

Depends on / 依赖: coprod, coprod.fst
-/
lemma coprod.inl_fst : coprod.inl ≫ coprod.fst X Y = 𝟙 X := by
  simp [coprod.fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `coprod.inr_fst` / 引理 `coprod.inr_fst`

English:
lemma coprod.inr_fst
  statement: coprod.inr ≫ coprod.fst X Y = 0
  proof: by
  simp [coprod.fst]

中文:
引理 coprod.inr_fst
  结论: coprod.inr ≫ coprod.fst X Y = 0
  证明: by
  simp [coprod.fst]

Depends on / 依赖: coprod, coprod.fst
-/
lemma coprod.inr_fst : coprod.inr ≫ coprod.fst X Y = 0 := by
  simp [coprod.fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `coprod.inl_snd` / 引理 `coprod.inl_snd`

English:
lemma coprod.inl_snd
  statement: coprod.inl ≫ coprod.snd X Y = 0
  proof: by
  simp [coprod.snd]

中文:
引理 coprod.inl_snd
  结论: coprod.inl ≫ coprod.snd X Y = 0
  证明: by
  simp [coprod.snd]

Depends on / 依赖: coprod, coprod.snd
-/
lemma coprod.inl_snd : coprod.inl ≫ coprod.snd X Y = 0 := by
  simp [coprod.snd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `coprod.inr_snd` / 引理 `coprod.inr_snd`

English:
lemma coprod.inr_snd
  statement: coprod.inr ≫ coprod.snd X Y = 𝟙 Y
  proof: by
  simp [coprod.snd]

中文:
引理 coprod.inr_snd
  结论: coprod.inr ≫ coprod.snd X Y = 𝟙 Y
  证明: by
  simp [coprod.snd]

Depends on / 依赖: coprod, coprod.snd
-/
lemma coprod.inr_snd : coprod.inr ≫ coprod.snd X Y = 𝟙 Y := by
  simp [coprod.snd]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (coprod.fst X Y)
  body: by simpa using congrArg (coprod.inl ≫ ·) e

中文:
实例 :
  签名: Epi (coprod.fst X Y)
  定义体: by simpa using congrArg (coprod.inl ≫ ·) e

Depends on / 依赖: coprod, coprod.inl
-/
instance : Epi (coprod.fst X Y) where
  left_cancellation _ _ e := by simpa using congrArg (coprod.inl ≫ ·) e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (coprod.snd X Y)
  body: by simpa using congrArg (coprod.inr ≫ ·) e

中文:
实例 :
  签名: Epi (coprod.snd X Y)
  定义体: by simpa using congrArg (coprod.inr ≫ ·) e

Depends on / 依赖: coprod, coprod.inr
-/
instance : Epi (coprod.snd X Y) where
  left_cancellation _ _ e := by simpa using congrArg (coprod.inr ≫ ·) e

end CoprodFstSnd

end Limits

namespace ObjectProperty

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (P : ObjectProperty C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms P.FullSubcategory
  body: { zero := P.homMk 0 }
  __ := P.fullyFaithfulι.hasZeroMorphisms

@[simp]

中文:
实例 :
  签名: HasZeroMorphisms P.FullSubcategory
  定义体: { zero := P.homMk 0 }
  __ := P.fullyFaithfulι.hasZeroMorphisms

@[simp]

Depends on / 依赖: P.homMk
-/
instance : HasZeroMorphisms P.FullSubcategory where
  -- Note: Add zero field explicitly for a better transparency of definitional properties
  zero _ _ := { zero := P.homMk 0 }
  __ := P.fullyFaithfulι.hasZeroMorphisms

@[simp]
/--
lemma `homMk_zero` / 引理 `homMk_zero`

English:
lemma homMk_zero
  given: (X Y : P.FullSubcategory)
  proof: rfl

@[simp]

中文:
引理 homMk_zero
  条件: (X Y : P.FullSubcategory)
  证明: rfl

@[simp]
-/
lemma homMk_zero (X Y : P.FullSubcategory) :
    P.homMk (0 : X.obj ⟶ Y.obj) = 0 := rfl

@[simp]
/--
lemma `zero_hom` / 引理 `zero_hom`

English:
lemma zero_hom
  given: (X Y : P.FullSubcategory)
  proof: rfl

中文:
引理 zero_hom
  条件: (X Y : P.FullSubcategory)
  证明: rfl
-/
lemma zero_hom (X Y : P.FullSubcategory) :
    (0 : X ⟶ Y).hom = 0 := rfl

end ObjectProperty

end CategoryTheory
