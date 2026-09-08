/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopPair

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

The data for a homology theory is bundled in a structure `HomologyPretheory` consisting of functors
`Hₚ i : TopPair ⥤ C` and `H i : TopCat ⥤ C` which represent the `i`th relative and regular homology,
respectively, (indexed by a `ComplexShape`) and a proof that they agree on `TopCat`. They also
require boundary morphisms `δ i j :  Hₚ i ⟶ proj₂ ⋙ H j` for the long exact sequence of
topological pairs. These are nonzero only if `c.Rel i j`.

We introduce a typeclass `IsHomotopyInvariant` for the first axiom.
-/

@[expose] public section

open CategoryTheory TopPair ObjectProperty

universe u

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
/-
**TopPair.HomologyPretheory** 是 Mathlib 中的一个结构，位于命名空间 `TopPair`。
形式化陈述：HomologyPretheory (C : Type*) [Category* C] [Limits.HasZeroMorphisms C] {ι
 : Type*} (c : ComplexShape ι) where /-- The relative homology functor of a `Hom
ologyPretheory`. -/ Hₚ (i : ι) : TopPair.{u} ⥤ C /-- The regular homology functo
r of a `HomologyPretheory`. -/ H (i : ι) : TopCat.{u} ⥤ C /-- `Hₚ` and `H` agree
 on `TopCat`. -/ iso (i : ι) : H i ≅ incl ⋙ Hₚ i /-- The boundary natural transf
ormation of a `HomologyPretheory`. -/ δ (i j : ι) : Hₚ i ⟶ proj₂ ⋙ H j /-- The b
oundary map is only nonzer
参数：C : Type*；c : ComplexShape ι；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
-/
structure HomologyPretheory
    (C : Type*) [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- `Hₚ` and `H` agree on `TopCat`. -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : Hₚ i ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
/-
**TopPair.HomologyPretheory.Hom** 是 Mathlib 中的一个结构，位于命名空间 `TopPair.HomologyPreth
eory`。
形式化陈述：Hom (HP HP' : HomologyPretheory.{u} C c) where /-- The natural transformat
ion of relative homology functors in a morphism of `HomologyPretheory`s. -/ homₚ
 (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i /-- The natural transformation of homology functor
s in a morphism of `HomologyPretheory`s. -/ hom (i : ι) : HP.H i ⟶ HP'.H i
参数：HP HP' : HomologyPretheory.{u} C c；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the category `HomologyPretheory`.
-/
structure Hom (HP HP' : HomologyPretheory.{u} C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `HomologyPretheory`s. -/
  homₚ (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- The natural transformation of homology functors in a morphism of
  `HomologyPretheory`s. -/
  hom (i : ι) : HP.H i ⟶ HP'.H i := (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv
  /-- `homₚ` and `hom` need to be compatible with `HomologyPretheory.iso`. -/
  iso_comm (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom := by cat_disch
  /-- `homₚ` needs to be compatible with the boundary maps. -/
  w (i j : ι) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j := by cat_disch

attribute [reassoc (attr := simp)] Hom.iso_comm
attribute [reassoc (attr := local simp)] Hom.w

@[simps]
/-
**TopPair.HomologyPretheory.** 是 Mathlib 中的一个实例，位于命名空间 `TopPair.HomologyPretheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (HomologyPretheory.{u} C c) where
  Hom := HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

variable {HP HP' : HomologyPretheory.{u} C c}

-- TODO: generate this with `@[to_app]`
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**TopPair.HomologyPretheory.Hom.iso_comm_app** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.
HomologyPretheory.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} {
HP HP' : TopPair.HomologyPretheory C c} (f : HP ⟶ HP') (i : ι) (X : TopCat),   C
ategoryTheory.CategoryStruct.comp ((HP.iso i).hom.app X) ((f.homₚ i).app (TopPai
r.ofTopCat X)) =     CategoryTheory.CategoryStruct.comp ((f.hom i).app X) ((HP'.
iso i).hom.app X)
参数：f : HP ⟶ HP'；i : ι；X : TopCat；(HP.iso i).hom.app X；(f.homₚ i).app (TopPair.of
TopCat X)；(f.hom i).app X；(HP'.iso i).hom.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopPair.HomologyPretheory.Hom.iso_comm`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma Hom.iso_comm_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) = (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

-- TODO: generate this with `@[to_app]`
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**TopPair.HomologyPretheory.Hom.w_app** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.Homolog
yPretheory.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {ι : Type u_2} {c : ComplexShape ι} {
HP HP' : TopPair.HomologyPretheory C c} (f : HP ⟶ HP') (i j : ι) (X : TopPair), 
  CategoryTheory.CategoryStruct.comp ((HP.δ i j).app X) ((f.hom j).app X.left) =
     CategoryTheory.CategoryStruct.comp ((f.homₚ i).app X) ((HP'.δ i j).app X)
参数：f : HP ⟶ HP'；i j : ι；X : TopPair；(HP.δ i j).app X；(f.hom j).app X.left；(f.hom
ₚ i).app X；(HP'.δ i j).app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopPair.HomologyPretheory.Hom.w`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {ι
 : Type u_2} {c : Com…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma Hom.w_app (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u}) :
    (HP.δ i j).app X ≫ (f.hom j).app X.left = (f.homₚ i).app X ≫ (HP'.δ i j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
/-
**TopPair.HomologyPretheory.iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `TopPair.HomologyP
retheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iso_homₚ_inv_hom (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

-- TODO: generate this with `@[to_app]`
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**TopPair.HomologyPretheory.iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `TopPair.HomologyP
retheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma iso_homₚ_inv_hom_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) ≫ (HP'.iso i).inv.app X = (f.hom i).app X :=
  congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
/-
**TopPair.HomologyPretheory.inv_hom_iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `TopPair.H
omologyPretheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_hom_iso_homₚ (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
/-
**TopPair.HomologyPretheory.inv_hom_iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `TopPair.H
omologyPretheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_hom_iso_homₚ_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X = (f.homₚ i).app (ofTopCat X) :=
  congr($(inv_hom_iso_homₚ _ _).app _)

/-- The forgetful functor that sends a `HomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
/-
**TopPair.HomologyPretheory.h** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.HomologyPretheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor that sends a `HomologyPretheory` to it's relative homology
 functor `Hₚ`.
-/
protected def hₚFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopPair.{u} ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i
/-
**TopPair.HomologyPretheory.** 是 Mathlib 中的一个实例，位于命名空间 `TopPair.HomologyPretheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.homₚ i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hₚFunctor i).map f))

/-- The forgetful functor that sends a `HomologyPretheory` to it's homology functor `H`. -/
@[simps]
/-
**TopPair.HomologyPretheory.hFunctor** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Homology
Pretheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {ι : Type u_2} →       
  {c : ComplexShape ι} →           ι → CategoryTheory.Functor (TopPair.HomologyP
retheory C c) (CategoryTheory.Functor TopCat C)
参数：TopPair.HomologyPretheory C c；CategoryTheory.Functor TopCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor that sends a `HomologyPretheory` to it's homology functor 
`H`.
-/
protected def hFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopCat.{u} ⥤ C where
  obj HP := HP.H i
  map f := f.hom i
/-
**TopPair.HomologyPretheory.** 是 Mathlib 中的一个实例，位于命名空间 `TopPair.HomologyPretheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.hom i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hFunctor i).map f))

variable (HP HP' : HomologyPretheory.{u} C c)

/-- A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps to
the same map in homology -/
/-
**TopPair.HomologyPretheory.IsHomotopyInvariant** 是 Mathlib 中的一个类，位于命名空间 `TopPai
r.HomologyPretheory`。
形式化陈述：IsHomotopyInvariant (HP : HomologyPretheory.{u} C c) where map_eq_of_homot
opy (HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι) : (HP.Hₚ i
).map f = (HP.Hₚ i).map g
参数：HP : HomologyPretheory.{u} C c；HP；F : Homotopy f g；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes h
omotopic maps to
the same map in homology
-/
class IsHomotopyInvariant (HP : HomologyPretheory.{u} C c) where
  map_eq_of_homotopy (HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι) :
    (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

export IsHomotopyInvariant (map_eq_of_homotopy)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsHomotopyInvariant` as `ObjectProperty`. -/
/-
**TopPair.HomologyPretheory.isHomotopyInvariant** 是 Mathlib 中的一个缩写定义，位于命名空间 `Top
Pair.HomologyPretheory`。
形式化陈述：isHomotopyInvariant : ObjectProperty (HomologyPretheory.{u} C c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HomologyPretheory.IsHomotopyInvariant` as `ObjectProperty`.
-/
abbrev isHomotopyInvariant : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsHomotopyInvariant

@[simp]
/-
**TopPair.HomologyPretheory.isHomotopyInvariant_iff** 是 Mathlib 中的一个引理，位于命名空间 `T
opPair.HomologyPretheory`。
形式化陈述：isHomotopyInvariant_iff : isHomotopyInvariant C c HP ↔ IsHomotopyInvariant
 HP
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isHomotopyInvariant_iff : isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP := .rfl
/-
**TopPair.HomologyPretheory.** 是 Mathlib 中的一个实例，位于命名空间 `TopPair.HomologyPretheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ ↦ by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

end HomologyPretheory

end TopPair

