/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Subcategories of comma categories defined by morphism properties

Given functors `L : A ⥤ T` and `R : B ⥤ T` and morphism properties `P`, `Q` and `W`
on `T`, `A` and `B` respectively, we define the subcategory `P.Comma L R Q W` of
`Comma L R` where

- objects are objects of `Comma L R` with the structural morphism satisfying `P`, and
- morphisms are morphisms of `Comma L R` where the left morphism satisfies `Q` and the
  right morphism satisfies `W`.

For an object `X : T`, this specializes to `P.Over Q X` which is the subcategory of `Over X`
where the structural morphism satisfies `P` and where the horizontal morphisms satisfy `Q`.
Common examples of the latter are e.g. the category of schemes étale (finite, affine, etc.)
over a base `X`. Here `Q = ⊤`.

## Implementation details

- We provide the general constructor `P.Comma L R Q W` to obtain `Over X` and `Under X` as
  special cases of the more general setup.

- Most results are developed only in the case where `Q = ⊤` and `W = ⊤`, but the definition
  is setup in the general case to allow for a later generalization if needed.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

section Comma

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {T : Type*} [Category* T]
  (L : A ⥤ T) (R : B ⥤ T)

/-
**CategoryTheory.MorphismProperty.costructuredArrow_iso_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：costructuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso] {L : A 
⥤ T} {X : T} {f g : CostructuredArrow L X} (e : f ≅ g) : P f.hom ↔ P g.hom
参数：P : MorphismProperty T；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comma_iso_iff`：comma_iso_iff (P : Morphi
smProperty C) [P.RespectsIso] {A B : Type*} [Category* A] [Category* B] {L : A ⥤
 C} {R : B ⥤ C} {f g : Comma L R} (…
-/
lemma costructuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : CostructuredArrow L X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e
/-
**CategoryTheory.MorphismProperty.structuredArrow_iso_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：structuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso] {L : A ⥤ 
T} {X : T} {f g : StructuredArrow X L} (e : f ≅ g) : P f.hom ↔ P g.hom
参数：P : MorphismProperty T；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comma_iso_iff`：comma_iso_iff (P : Morphi
smProperty C) [P.RespectsIso] {A B : Type*} [Category* A] [Category* B] {L : A ⥤
 C} {R : B ⥤ C} {f g : Comma L R} (…
-/
lemma structuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : StructuredArrow X L} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e
/-
**CategoryTheory.MorphismProperty.over_iso_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：over_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over 
X} (e : f ≅ g) : P f.hom ↔ P g.hom
参数：P : MorphismProperty T；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comma_iso_iff`：comma_iso_iff (P : Morphi
smProperty C) [P.RespectsIso] {A B : Type*} [Category* A] [Category* B] {L : A ⥤
 C} {R : B ⥤ C} {f g : Comma L R} (…
-/
lemma over_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e
/-
**CategoryTheory.MorphismProperty.under_iso_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：under_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Unde
r X} (e : f ≅ g) : P f.hom ↔ P g.hom
参数：P : MorphismProperty T；e : f ≅ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comma_iso_iff`：comma_iso_iff (P : Morphi
smProperty C) [P.RespectsIso] {A B : Type*} [Category* A] [Category* B] {L : A ⥤
 C} {R : B ⥤ C} {f g : Comma L R} (…
-/
lemma under_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Under X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

section

variable {W : MorphismProperty T} {X : T}

/-- The object property on `Comma L R` induced by a morphism property. -/
/-
**CategoryTheory.MorphismProperty.commaObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：commaObj (W : MorphismProperty T) : ObjectProperty (Comma L R)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property on `Comma L R` induced by a morphism property.
-/
def commaObj (W : MorphismProperty T) : ObjectProperty (Comma L R) :=
  fun f ↦ W f.hom
/-
**CategoryTheory.MorphismProperty.commaObj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} B] {T : Type u_3} [inst_2 : C
ategoryTheory.Category.{v_3, u_3} T]   (L : CategoryTheory.Functor A T) (R : Cat
egoryTheory.Functor B T) {W : CategoryTheory.MorphismProperty T}   (Y : Category
Theory.Comma L R), CategoryTheory.MorphismProperty.commaObj L R W Y ↔ W Y.hom
参数：L : CategoryTheory.Functor A T；R : CategoryTheory.Functor B T；Y : CategoryThe
ory.Comma L R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma commaObj_iff (Y : Comma L R) : W.commaObj L R Y ↔ W Y.hom := .rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : (W.commaObj L R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    rwa [commaObj_iff, ← W.cancel_left_of_respectsIso (L.map e.hom.left), e.hom.w,
      W.cancel_right_of_respectsIso]

/-- The object property on `CostructuredArrow L X` induced by a morphism property. -/
/-
**CategoryTheory.MorphismProperty.costructuredArrowObj** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：costructuredArrowObj (W : MorphismProperty T) : ObjectProperty (Costructur
edArrow L X)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property on `CostructuredArrow L X` induced by a morphism property.
-/
def costructuredArrowObj (W : MorphismProperty T) : ObjectProperty (CostructuredArrow L X) :=
  fun f ↦ W f.hom
/-
**CategoryTheory.MorphismProperty.costructuredArrowObj_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {T : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} T] (L : CategoryTheory.Functo
r A T)   {W : CategoryTheory.MorphismProperty T} {X : T} (Y : CategoryTheory.Cos
tructuredArrow L X),   CategoryTheory.MorphismProperty.costructuredArrowObj L W 
Y ↔ W Y.hom
参数：L : CategoryTheory.Functor A T；Y : CategoryTheory.CostructuredArrow L X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma costructuredArrowObj_iff (Y : CostructuredArrow L X) :
    W.costructuredArrowObj L Y ↔ W Y.hom := .rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : (W.costructuredArrowObj L (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

/-- The object property on `StructuredArrow X R` induced by a morphism property. -/
/-
**CategoryTheory.MorphismProperty.structuredArrowObj** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：structuredArrowObj (W : MorphismProperty T) : ObjectProperty (StructuredAr
row X R)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property on `StructuredArrow X R` induced by a morphism property.
-/
def structuredArrowObj (W : MorphismProperty T) : ObjectProperty (StructuredArrow X R) :=
  fun f ↦ W f.hom
/-
**CategoryTheory.MorphismProperty.structuredArrowObj_iff** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：∀ {B : Type u_2} [inst : CategoryTheory.Category.{v_2, u_2} B] {T : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_3, u_3} T] (R : CategoryTheory.Functo
r B T)   {W : CategoryTheory.MorphismProperty T} {X : T} (Y : CategoryTheory.Str
ucturedArrow X R),   CategoryTheory.MorphismProperty.structuredArrowObj R W Y ↔ 
W Y.hom
参数：R : CategoryTheory.Functor B T；Y : CategoryTheory.StructuredArrow X R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma structuredArrowObj_iff (Y : StructuredArrow X R) :
    W.structuredArrowObj R Y ↔ W Y.hom := .rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : (W.structuredArrowObj L (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

/-- The morphism property on `Over X` induced by a morphism property on `C`. -/
/-
**CategoryTheory.MorphismProperty.over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MorphismProperty`。
形式化陈述：over (W : MorphismProperty T) {X : T} : MorphismProperty (Over X)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property on `Over X` induced by a morphism property on `C`.
-/
def over (W : MorphismProperty T) {X : T} : MorphismProperty (Over X) := fun _ _ f ↦ W f.left
/-
**CategoryTheory.MorphismProperty.over_eq_inverseImage** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：over_eq_inverseImage (W : MorphismProperty T) (X : T) : W.over = W.inverse
Image (Over.forget X)
参数：W : MorphismProperty T；X : T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma over_eq_inverseImage (W : MorphismProperty T) (X : T) :
    W.over = W.inverseImage (Over.forget X) := rfl
/-
**CategoryTheory.MorphismProperty.over_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：∀ {T : Type u_3} [inst : CategoryTheory.Category.{v_3, u_3} T] {W : Catego
ryTheory.MorphismProperty T} {X : T}   {Y Z : CategoryTheory.Over X} (f : Y ⟶ Z)
, W.over f ↔ W (CategoryTheory.Over.Hom.left f)
参数：f : Y ⟶ Z；CategoryTheory.Over.Hom.left f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma over_iff {Y Z : Over X} (f : Y ⟶ Z) : W.over f ↔ W f.left := .rfl

/-- The morphism property on `Under X` induced by a morphism property on `C`. -/
/-
**CategoryTheory.MorphismProperty.under** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：under (W : MorphismProperty T) {X : T} : MorphismProperty (Under X)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property on `Under X` induced by a morphism property on `C`.
-/
def under (W : MorphismProperty T) {X : T} : MorphismProperty (Under X) := fun _ _ f ↦ W f.right
/-
**CategoryTheory.MorphismProperty.under_eq_inverseImage** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：under_eq_inverseImage (W : MorphismProperty T) (X : T) : W.under = W.inver
seImage (Under.forget X)
参数：W : MorphismProperty T；X : T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma under_eq_inverseImage (W : MorphismProperty T) (X : T) :
    W.under = W.inverseImage (Under.forget X) := rfl
/-
**CategoryTheory.MorphismProperty.under_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：∀ {T : Type u_3} [inst : CategoryTheory.Category.{v_3, u_3} T] {W : Catego
ryTheory.MorphismProperty T} {X : T}   {Y Z : CategoryTheory.Under X} (f : Y ⟶ Z
), W.under f ↔ W (CategoryTheory.Under.Hom.right f)
参数：f : Y ⟶ Z；CategoryTheory.Under.Hom.right f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma under_iff {Y Z : Under X} (f : Y ⟶ Z) : W.under f ↔ W f.right := .rfl

/-- The object property on `Over X` induced by a morphism property. -/
/-
**CategoryTheory.MorphismProperty.overObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：overObj (W : MorphismProperty T) {X : T} : ObjectProperty (Over X)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property on `Over X` induced by a morphism property.
-/
def overObj (W : MorphismProperty T) {X : T} : ObjectProperty (Over X) := fun f ↦ W f.hom
/-
**CategoryTheory.MorphismProperty.overObj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：∀ {T : Type u_3} [inst : CategoryTheory.Category.{v_3, u_3} T] {W : Catego
ryTheory.MorphismProperty T} {X : T}   (Y : CategoryTheory.Over X), W.overObj Y 
↔ W Y.hom
参数：Y : CategoryTheory.Over X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma overObj_iff (Y : Over X) : W.overObj Y ↔ W Y.hom := .rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : (W.overObj (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

/-- The object property on `Under X` induced by a morphism property. -/
/-
**CategoryTheory.MorphismProperty.underObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：underObj (W : MorphismProperty T) {X : T} : ObjectProperty (Under X)
参数：W : MorphismProperty T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property on `Under X` induced by a morphism property.
-/
def underObj (W : MorphismProperty T) {X : T} : ObjectProperty (Under X) := fun f ↦ W f.hom
/-
**CategoryTheory.MorphismProperty.underObj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：∀ {T : Type u_3} [inst : CategoryTheory.Category.{v_3, u_3} T] {W : Catego
ryTheory.MorphismProperty T} {X : T}   (Y : CategoryTheory.Under X), W.underObj 
Y ↔ W Y.hom
参数：Y : CategoryTheory.Under X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma underObj_iff (Y : Under X) : W.underObj Y ↔ W Y.hom := .rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : (W.underObj (X := X)).IsClosedUnderIsomorphisms :=
  inferInstanceAs <| (W.commaObj _ _).IsClosedUnderIsomorphisms

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_op_overObj** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_op_overObj (W : MorphismProperty T) {X : T} : W.overObj.op.in
verseImage (Under.opEquivOpOver X).functor = W.op.underObj
参数：W : MorphismProperty T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_op_overObj (W : MorphismProperty T) {X : T} :
    W.overObj.op.inverseImage (Under.opEquivOpOver X).functor = W.op.underObj := rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.inverseImage_op_underObj** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：inverseImage_op_underObj (W : MorphismProperty T) {X : T} : W.underObj.op.
inverseImage (Over.opEquivOpUnder X).functor = W.op.overObj
参数：W : MorphismProperty T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_op_underObj (W : MorphismProperty T) {X : T} :
    W.underObj.op.inverseImage (Over.opEquivOpUnder X).functor = W.op.overObj := rfl

end

variable (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)

/-- `P.Comma L R Q W` is the subcategory of `Comma L R` consisting of
objects `X : Comma L R` where `X.hom` satisfies `P`. The morphisms are given by
morphisms in `Comma L R` where the left one satisfies `Q` and the right one satisfies `W`. -/
@[ext]
/-
**CategoryTheory.MorphismProperty.Comma** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：{A : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} A] →     {B 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} B] →         {T
 : Type u_3} →           [inst_2 : CategoryTheory.Category.{v_3, u_3} T] →      
       CategoryTheory.Functor A T →               CategoryTheory.Functor B T →  
               CategoryTheory.MorphismProperty T →                   CategoryThe
ory.MorphismProperty A → CategoryTheory.MorphismProperty B → Type (max (max u_1 
u_2) v_3)
参数：max (max u_1 u_2) v_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.Comma L R Q W` is the subcategory of `Comma L R` consisting of
objects `X : Comma L R` where `X.hom` satisfies `P`. The morphisms are given by
morphisms in `Comma L R` where the left one satisfies `Q` and the right one sati
sfies `W`.
-/
protected structure Comma (Q : MorphismProperty A) (W : MorphismProperty B) extends Comma L R where
  prop : P toComma.hom

namespace Comma

variable {L R P Q W}

/-- A morphism in `P.Comma L R Q W` is a morphism in `Comma L R` where the left
hom satisfies `Q` and the right one satisfies `W`. -/
@[ext]
/-
**CategoryTheory.MorphismProperty.Comma.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.MorphismProperty.Comma`。
形式化陈述：{A : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} A] →     {B 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} B] →         {T
 : Type u_3} →           [inst_2 : CategoryTheory.Category.{v_3, u_3} T] →      
       {L : CategoryTheory.Functor A T} →               {R : CategoryTheory.Func
tor B T} →                 {P : CategoryTheory.MorphismProperty T} →            
       {Q : CategoryTheory.MorphismProperty A} →                     {W : Catego
ryTheory.MorphismProperty B} →                       CategoryTheory.MorphismProp
erty.Comma L R P Q W →                         CategoryTheory.MorphismProperty.C
omma L R P Q W → Type (max v_1 v_2)
参数：max v_1 v_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `P.Comma L R Q W` is a morphism in `Comma L R` where the left
hom satisfies `Q` and the right one satisfies `W`.
-/
structure Hom (X Y : P.Comma L R Q W) extends CommaMorphism X.toComma Y.toComma where
  prop_hom_left : Q toCommaMorphism.left
  prop_hom_right : W toCommaMorphism.right

/-- The underlying morphism of objects in `Comma L R`. -/
/-
**CategoryTheory.MorphismProperty.Comma.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty.Comma.Hom`。
形式化陈述：{A : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} A] →     {B 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} B] →         {T
 : Type u_3} →           [inst_2 : CategoryTheory.Category.{v_3, u_3} T] →      
       {L : CategoryTheory.Functor A T} →               {R : CategoryTheory.Func
tor B T} →                 {P : CategoryTheory.MorphismProperty T} →            
       {Q : CategoryTheory.MorphismProperty A} →                     {W : Catego
ryTheory.MorphismProperty B} →                       {X Y : CategoryTheory.Morph
ismProperty.Comma L R P Q W} → X.Hom Y → (X.toComma ⟶ Y.toComma)
参数：X.toComma ⟶ Y.toComma。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying morphism of objects in `Comma L R`.
-/
abbrev Hom.hom {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : X.toComma ⟶ Y.toComma :=
  f.toCommaMorphism

@[simp]
/-
**CategoryTheory.MorphismProperty.Comma.Hom.hom_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Comma.Hom`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} B] {T : Type u_3} [inst_2 : C
ategoryTheory.Category.{v_3, u_3} T]   {L : CategoryTheory.Functor A T} {R : Cat
egoryTheory.Functor B T} {P : CategoryTheory.MorphismProperty T}   {Q : Category
Theory.MorphismProperty A} {W : CategoryTheory.MorphismProperty B}   {X Y : Cate
goryTheory.MorphismProperty.Comma L R P Q W} (f : CategoryTheory.CommaMorphism X
.toComma Y.toComma)   (hf : Q f.left) (hg : W f.right), { toCommaMorphism := f, 
prop_hom_left := hf, prop_hom_right := hg }.hom = f
参数：f : CategoryTheory.CommaMorphism X.toComma Y.toComma；hf : Q f.left；hg : W f.r
ight。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.hom_mk {X Y : P.Comma L R Q W} (f : CommaMorphism X.toComma Y.toComma) (hf) (hg) :
    Comma.Hom.hom ⟨f, hf, hg⟩ = f := rfl
/-
**CategoryTheory.MorphismProperty.Comma.Hom.hom_left** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty.Comma.Hom`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} B] {T : Type u_3} [inst_2 : C
ategoryTheory.Category.{v_3, u_3} T]   {L : CategoryTheory.Functor A T} {R : Cat
egoryTheory.Functor B T} {P : CategoryTheory.MorphismProperty T}   {Q : Category
Theory.MorphismProperty A} {W : CategoryTheory.MorphismProperty B}   {X Y : Cate
goryTheory.MorphismProperty.Comma L R P Q W} (f : X.Hom Y), f.hom.left = f.left
参数：f : X.Hom Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.hom_left {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : f.hom.left = f.left := rfl
/-
**CategoryTheory.MorphismProperty.Comma.Hom.hom_right** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.Comma.Hom`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} B] {T : Type u_3} [inst_2 : C
ategoryTheory.Category.{v_3, u_3} T]   {L : CategoryTheory.Functor A T} {R : Cat
egoryTheory.Functor B T} {P : CategoryTheory.MorphismProperty T}   {Q : Category
Theory.MorphismProperty A} {W : CategoryTheory.MorphismProperty B}   {X Y : Cate
goryTheory.MorphismProperty.Comma L R P Q W} (f : X.Hom Y), f.hom.right = f.righ
t
参数：f : X.Hom Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.hom_right {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : f.hom.right = f.right := rfl

/-- See Note [custom simps projection] -/
/-
**CategoryTheory.MorphismProperty.Comma.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.MorphismProperty.Comma.Hom.Simps`。
形式化陈述：{A : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} A] →     {B 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} B] →         {T
 : Type u_3} →           [inst_2 : CategoryTheory.Category.{v_3, u_3} T] →      
       {L : CategoryTheory.Functor A T} →               {R : CategoryTheory.Func
tor B T} →                 {P : CategoryTheory.MorphismProperty T} →            
       {Q : CategoryTheory.MorphismProperty A} →                     {W : Catego
ryTheory.MorphismProperty B} →                       {X Y : CategoryTheory.Morph
ismProperty.Comma L R P Q W} → X.Hom Y → (X.toComma ⟶ Y.toComma)
参数：X.toComma ⟶ Y.toComma。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Hom.Simps.hom {X Y : P.Comma L R Q W} (f : X.Hom Y) :
    X.toComma ⟶ Y.toComma :=
  f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism → hom)

/-- The identity morphism of an object in `P.Comma L R Q W`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.Comma.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty.Comma`。
形式化陈述：id [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W) : C
omma.Hom X X where left
参数：X : P.Comma L R Q W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of an object in `P.Comma L R Q W`.
-/
def id [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W) : Comma.Hom X X where
  left := 𝟙 X.left
  right := 𝟙 X.right
  prop_hom_left := Q.id_mem X.toComma.left
  prop_hom_right := W.id_mem X.toComma.right

/-- Composition of morphisms in `P.Comma L R Q W`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.Comma.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.MorphismProperty.Comma.Hom`。
形式化陈述：{A : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} A] →     {B 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} B] →         {T
 : Type u_3} →           [inst_2 : CategoryTheory.Category.{v_3, u_3} T] →      
       {L : CategoryTheory.Functor A T} →               {R : CategoryTheory.Func
tor B T} →                 {P : CategoryTheory.MorphismProperty T} →            
       {Q : CategoryTheory.MorphismProperty A} →                     {W : Catego
ryTheory.MorphismProperty B} →                       [Q.IsStableUnderComposition
] →                         [W.IsStableUnderComposition] →                      
     {X Y Z : CategoryTheory.MorphismProperty.Comma L R P Q W} → X.Hom Y → Y.Hom
 Z → X.Hom Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in `P.Comma L R Q W`.
-/
def Hom.comp [Q.IsStableUnderComposition] [W.IsStableUnderComposition] {X Y Z : P.Comma L R Q W}
    (f : Comma.Hom X Y) (g : Comma.Hom Y Z) :
    Comma.Hom X Z where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  prop_hom_left := Q.comp_mem _ _ f.prop_hom_left g.prop_hom_left
  prop_hom_right := W.comp_mem _ _ f.prop_hom_right g.prop_hom_right

variable [Q.IsMultiplicative] [W.IsMultiplicative]

variable (L R P Q W) in
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (P.Comma L R Q W) where
  Hom X Y := X.Hom Y
  id X := X.id
  comp f g := f.comp g
/-
**CategoryTheory.MorphismProperty.Comma.toCommaMorphism_eq_hom** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：toCommaMorphism_eq_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) : f.toCommaMorp
hism = f.hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCommaMorphism_eq_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) : f.toCommaMorphism = f.hom := rfl

/-- Alternative `ext` lemma for `Comma.Hom`. -/
@[ext]
/-
**CategoryTheory.MorphismProperty.Comma.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty.Comma.Hom`。
形式化陈述：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} B] {T : Type u_3} [inst_2 : C
ategoryTheory.Category.{v_3, u_3} T]   {L : CategoryTheory.Functor A T} {R : Cat
egoryTheory.Functor B T} {P : CategoryTheory.MorphismProperty T}   {Q : Category
Theory.MorphismProperty A} {W : CategoryTheory.MorphismProperty B} [inst_3 : Q.I
sMultiplicative]   [inst_4 : W.IsMultiplicative] {X Y : CategoryTheory.MorphismP
roperty.Comma L R P Q W} {f g : X ⟶ Y},   CategoryTheory.MorphismProperty.Comma.
Hom.hom f = CategoryTheory.MorphismProperty.Comma.Hom.hom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.ext`：∀ {A : Type u_1} {inst : 
CategoryTheory.Category.{v_1, u_1} A} {B : Type u_2}   {inst_1 : CategoryTheory.
Category.{v_2, u_2} B} {T : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Alternative `ext` lemma for `Comma.Hom`.
-/
lemma Hom.ext' {X Y : P.Comma L R Q W} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g := Comma.Hom.ext
  (congrArg CommaMorphism.left h)
  (congrArg CommaMorphism.right h)

@[simp]
/-
**CategoryTheory.MorphismProperty.Comma.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty.Comma`。
形式化陈述：id_hom (X : P.Comma L R Q W) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma
参数：X : P.Comma L R Q W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (X : P.Comma L R Q W) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma := rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.Comma.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty.Comma`。
形式化陈述：comp_hom {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom =
 f.hom ≫ g.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[reassoc]
/-
**CategoryTheory.MorphismProperty.Comma.comp_left** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty.Comma`。
形式化陈述：comp_left {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).left
 = f.left ≫ g.left
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_left {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

@[reassoc]
/-
**CategoryTheory.MorphismProperty.Comma.comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Comma`。
形式化陈述：comp_right {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).rig
ht = f.right ≫ g.right
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_right {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

/-- If `i` is an isomorphism in `Comma L R`, it is also a morphism in `P.Comma L R Q W`. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Comma.homFromCommaOfIsIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W
} (i : X.toComma ⟶ Y.toComma) [IsIso i] : X ⟶ Y where __
参数：i : X.toComma ⟶ Y.toComma。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i` is an isomorphism in `Comma L R`, it is also a morphism in `P.Comma L R Q
 W`.
-/
def homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ⟶ Y.toComma) [IsIso i] :
    X ⟶ Y where
  __ := i
  prop_hom_left := Q.of_isIso i.left
  prop_hom_right := W.of_isIso i.right
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (i : X.toComma ⟶ Y.toComma)
    [IsIso i] : IsIso (homFromCommaOfIsIso i) := by
  constructor
  use homFromCommaOfIsIso (inv i)
  constructor <;> ext : 1 <;> simp

/-- Any isomorphism between objects of `P.Comma L R Q W` in `Comma L R` is also an isomorphism
in `P.Comma L R Q W`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.Comma.isoFromComma** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.Comma`。
形式化陈述：isoFromComma [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (i : 
X.toComma ≅ Y.toComma) : X ≅ Y where hom
参数：i : X.toComma ≅ Y.toComma。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any isomorphism between objects of `P.Comma L R Q W` in `Comma L R` is also an i
somorphism
in `P.Comma L R Q W`.
-/
def isoFromComma [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ≅ Y.toComma) : X ≅ Y where
  hom := homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

/-- Constructor for isomorphisms in `P.Comma L R Q W` from isomorphisms of the left and right
components and naturality in the forward direction. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Comma`。
形式化陈述：isoMk [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left 
≅ Y.left) (r : X.right ≅ Y.right) (h : L.map l.hom ≫ Y.hom = X.hom ≫ R.map r.hom
参数：l : X.left ≅ Y.left；r : X.right ≅ Y.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `P.Comma L R Q W` from isomorphisms of the left 
and right
components and naturality in the forward direction.
-/
def isoMk [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left ≅ Y.left)
    (r : X.right ≅ Y.right) (h : L.map l.hom ≫ Y.hom = X.hom ≫ R.map r.hom := by cat_disch) :
    X ≅ Y :=
  isoFromComma (CategoryTheory.Comma.isoMk l r h)

variable (L R P Q W)

/-- The forgetful functor. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.Comma.forget** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty.Comma`。
形式化陈述：forget : P.Comma L R Q W ⥤ Comma L R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor.
-/
def forget : P.Comma L R Q W ⥤ Comma L R where
  obj X := X.toComma
  map f := f.hom
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget L R P Q W).Faithful where
  map_injective := Comma.Hom.ext'

variable {L R P Q W}
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : IsIso f.hom :=
  (forget L R P Q W).map_isIso f
/-
**CategoryTheory.MorphismProperty.Comma.hom_homFromCommaOfIsIso** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：hom_homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R
 Q W} (i : X ⟶ Y) [IsIso i.hom] : homFromCommaOfIsIso i.hom = i
参数：i : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X ⟶ Y) [IsIso i.hom] :
    homFromCommaOfIsIso i.hom = i :=
  rfl
/-
**CategoryTheory.MorphismProperty.Comma.inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty.Comma`。
形式化陈述：inv_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv 
f.hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `CategoryTheory.MorphismProperty.Comma.instIsIsoCommaHom`：∀ {A : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.Comma.comp_hom`：comp_hom {X Y Z : P.Comm
a L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.MorphismProperty.Comma.id_hom`：id_hom (X : P.Comma L R Q 
W) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma
-/
lemma inv_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_hom, IsIso.hom_inv_id, id_hom]

variable (L R P Q W)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.RespectsIso] [W.RespectsIso] : (forget L R P Q W).ReflectsIsomorphisms where
  reflects f hf := by
    simp only [forget_obj, forget_map] at hf
    rw [← hom_homFromCommaOfIsIso f]
    infer_instance

/-- The forgetful functor from the full subcategory of `Comma L R` defined by `P` is
fully faithful. -/
/-
**CategoryTheory.MorphismProperty.Comma.forgetFullyFaithful** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：forgetFullyFaithful : (forget L R P ⊤ ⊤).FullyFaithful where preimage {X Y
} f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `trivial`：True

--- 原说明 ---
The forgetful functor from the full subcategory of `Comma L R` defined by `P` is
fully faithful.
-/
def forgetFullyFaithful : (forget L R P ⊤ ⊤).FullyFaithful where
  preimage {X Y} f := ⟨f, trivial, trivial⟩
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget L R P ⊤ ⊤).Full :=
  Functor.FullyFaithful.full (forgetFullyFaithful L R P)

section

variable {L R}

@[simp]
/-
**CategoryTheory.MorphismProperty.Comma.eqToHom_left** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty.Comma`。
形式化陈述：eqToHom_left {X Y : P.Comma L R Q W} (h : X = Y) : (eqToHom h).left = eqTo
Hom (by rw [h])
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_left {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.Comma.eqToHom_right** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty.Comma`。
形式化陈述：eqToHom_right {X Y : P.Comma L R Q W} (h : X = Y) : (eqToHom h).right = eq
ToHom (by rw [h])
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_right {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  rfl

end

section

variable {P P' : MorphismProperty T} {Q Q' : MorphismProperty A} {W W' : MorphismProperty B}
  (hP : P ≤ P') (hQ : Q ≤ Q') (hW : W ≤ W')

variable [Q.IsMultiplicative] [Q'.IsMultiplicative] [W.IsMultiplicative] [W'.IsMultiplicative]

/-- Weaken the conditions on all components. -/
/-
**CategoryTheory.MorphismProperty.Comma.changeProp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Comma`。
形式化陈述：changeProp : P.Comma L R Q W ⥤ P'.Comma L R Q' W' where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weaken the conditions on all components.
-/
def changeProp : P.Comma L R Q W ⥤ P'.Comma L R Q' W' where
  obj X := ⟨X.toComma, hP _ X.2⟩
  map f := ⟨f.toCommaMorphism, hQ _ f.2, hW _ f.3⟩

/-- Weakening the condition on the structure morphisms is fully faithful. -/
/-
**CategoryTheory.MorphismProperty.Comma.fullyFaithfulChangeProp** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：fullyFaithfulChangeProp : (changeProp (Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weakening the condition on the structure morphisms is fully faithful.
-/
def fullyFaithfulChangeProp :
    (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, f.2, f.3⟩
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (changeProp L R hP hQ hW).Faithful where
  map_injective {X Y} f g h := by ext : 1; exact congr($(h).hom)
/-
**CategoryTheory.MorphismProperty.Comma.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Comma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).Full :=
  (fullyFaithfulChangeProp ..).full

end

section Functoriality

variable {L R P Q W}
variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/-- Lift a functor `F : C ⥤ Comma L R` to the subcategory `P.Comma L R Q W` under
suitable assumptions on `F`. -/
@[simps obj_toComma map_hom]
/-
**CategoryTheory.MorphismProperty.Comma.lift** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty.Comma`。
形式化陈述：lift {C : Type*} [Category* C] (F : C ⥤ Comma L R) (hP : forall X, P (F.ob
j X).hom) (hQ : forall {X Y} (f : X ⟶ Y), Q (F.map f).left) (hW : forall {X Y} (
f : X ⟶ Y), W (F.map f).right) : C ⥤ P.Comma L R Q W where obj X
参数：F : C ⥤ Comma L R；hP : forall X, P (F.obj X).hom；hQ : forall {X Y} (f : X ⟶ Y
), Q (F.map f).left；hW : forall {X Y} (f : X ⟶ Y), W (F.map f).right。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a functor `F : C ⥤ Comma L R` to the subcategory `P.Comma L R Q W` under
suitable assumptions on `F`.
-/
def lift {C : Type*} [Category* C] (F : C ⥤ Comma L R)
    (hP : ∀ X, P (F.obj X).hom)
    (hQ : ∀ {X Y} (f : X ⟶ Y), Q (F.map f).left)
    (hW : ∀ {X Y} (f : X ⟶ Y), W (F.map f).right) :
    C ⥤ P.Comma L R Q W where
  obj X :=
    { __ := F.obj X
      prop := hP X }
  map {X Y} f :=
    { __ := F.map f
      prop_hom_left := hQ f
      prop_hom_right := hW f }

variable (R) in
/-- A natural transformation `L₁ ⟶ L₂` induces a functor `P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W`. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapLeft** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty.Comma`。
形式化陈述：mapLeft (l : L₁ ⟶ L₂) (hl : forall X : P.Comma L₂ R Q W, P (l.app X.left ≫
 X.hom)) : P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W
参数：l : L₁ ⟶ L₂；hl : forall X : P.Comma L₂ R Q W, P (l.app X.left ≫ X.hom)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_left`：∀ {A : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_right`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} B] {T : Type u_…

--- 原说明 ---
A natural transformation `L₁ ⟶ L₂` induces a functor `P.Comma L₂ R Q W ⥤ P.Comma
 L₁ R Q W`.
-/
def mapLeft (l : L₁ ⟶ L₂) (hl : ∀ X : P.Comma L₂ R Q W, P (l.app X.left ≫ X.hom)) :
    P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapLeft R l) hl
    (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

set_option backward.isDefEq.respectTransparency.types false in
variable (L R) in
/-- The functor `P.Comma L R Q W ⥤ P.Comma L R Q W` induced by the identity natural transformation
on `L` is naturally isomorphic to the identity functor. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapLeftId** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MorphismProperty.Comma`。
形式化陈述：mapLeftId [Q.RespectsIso] [W.RespectsIso] : mapLeft (P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `P.Comma L R Q W ⥤ P.Comma L R Q W` induced by the identity natural 
transformation
on `L` is naturally isomorphic to the identity functor.
-/
def mapLeftId [Q.RespectsIso] [W.RespectsIso] :
    mapLeft (P := P) (Q := Q) (W := W) R (𝟙 L) (fun X ↦ by simpa using X.prop) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- The functor `P.Comma L₁ R Q W ⥤ P.Comma L₃ R Q W` induced by the composition of two natural
transformations `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the
two functors induced by these natural transformations. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapLeftComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.Comma`。
形式化陈述：mapLeftComp [Q.RespectsIso] [W.RespectsIso] (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) (
hl : forall (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom)) (hl' : forall (X :
 P.Comma L₃ R Q W), P (l'.app X.left ≫ X.hom)) (hll' : forall (X : P.Comma L₃ R 
Q W), P ((l ≫ l').app X.left ≫ X.hom)) : mapLeft (P
参数：l : L₁ ⟶ L₂；l' : L₂ ⟶ L₃；hl : forall (X : P.Comma L₂ R Q W), P (l.app X.left 
≫ X.hom)；hl' : forall (X : P.Comma L₃ R Q W), P (l'.app X.left ≫ X.hom)；hll' : f
orall (X : P.Comma L₃ R Q W), P ((l ≫ l').app X.left ≫ X.hom)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `P.Comma L₁ R Q W ⥤ P.Comma L₃ R Q W` induced by the composition of 
two natural
transformations `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the 
composition of the
two functors induced by these natural transformations.
-/
def mapLeftComp [Q.RespectsIso] [W.RespectsIso] (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
    (hl : ∀ (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom))
    (hl' : ∀ (X : P.Comma L₃ R Q W), P (l'.app X.left ≫ X.hom))
    (hll' : ∀ (X : P.Comma L₃ R Q W), P ((l ≫ l').app X.left ≫ X.hom)) :
    mapLeft (P := P) (Q := Q) (W := W) R (l ≫ l') hll' ≅
      mapLeft R l' hl' ⋙ mapLeft R l hl :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- Two equal natural transformations `L₁ ⟶ L₂` yield naturally isomorphic functors
`P.Comma L₁ R Q W ⥤ P.Comma L₂ R Q W`. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapLeftEq** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MorphismProperty.Comma`。
形式化陈述：mapLeftEq [Q.RespectsIso] [W.RespectsIso] (l l' : L₁ ⟶ L₂) (h : l = l') (h
l : forall (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom)) : mapLeft R l hl ≅ 
mapLeft R l' (h ▸ hl)
参数：l l' : L₁ ⟶ L₂；h : l = l'；hl : forall (X : P.Comma L₂ R Q W), P (l.app X.left
 ≫ X.hom)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two equal natural transformations `L₁ ⟶ L₂` yield naturally isomorphic functors
`P.Comma L₁ R Q W ⥤ P.Comma L₂ R Q W`.
-/
def mapLeftEq [Q.RespectsIso] [W.RespectsIso] (l l' : L₁ ⟶ L₂) (h : l = l')
    (hl : ∀ (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom)) :
    mapLeft R l hl ≅ mapLeft R l' (h ▸ hl) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- A natural isomorphism `L₁ ≅ L₂` induces an equivalence of categories
`P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W`. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Comma`。
形式化陈述：mapLeftIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso] (e : L₁ ≅ L₂) :
 P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W where functor
参数：e : L₁ ≅ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism `L₁ ≅ L₂` induces an equivalence of categories
`P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W`.
-/
def mapLeftIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
      (e : L₁ ≅ L₂) :
    P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W where
  functor := Comma.mapLeft R e.inv (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapLeft R e.hom (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapLeftId _ _).symm ≪≫
    mapLeftEq _ _ _ e.hom_inv_id.symm (fun X ↦ by simpa using X.prop) ≪≫
    mapLeftComp _ _ _
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  counitIso :=
    (mapLeftComp _ _ _
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)).symm ≪≫
    mapLeftEq _ _ _ e.inv_hom_id
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop) ≪≫
    mapLeftId _ _

variable (L) in
/-- A natural transformation `R₁ ⟶ R₂` induces a functor `P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W`. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapRight** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.MorphismProperty.Comma`。
形式化陈述：mapRight (r : R₁ ⟶ R₂) (hr : forall X : P.Comma L R₁ Q W, P (X.hom ≫ r.app
 X.right)) : P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W
参数：r : R₁ ⟶ R₂；hr : forall X : P.Comma L R₁ Q W, P (X.hom ≫ r.app X.right)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_left`：∀ {A : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.prop_hom_right`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} B] {T : Type u_…

--- 原说明 ---
A natural transformation `R₁ ⟶ R₂` induces a functor `P.Comma L R₁ Q W ⥤ P.Comma
 L R₂ Q W`.
-/
def mapRight (r : R₁ ⟶ R₂) (hr : ∀ X : P.Comma L R₁ Q W, P (X.hom ≫ r.app X.right)) :
    P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapRight L r) hr
    (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

set_option backward.isDefEq.respectTransparency.types false in
variable (L R) in
/-- The functor `P.Comma L R Q W ⥤ P.Comma L R Q W` induced by the identity natural transformation
on `R` is naturally isomorphic to the identity functor. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapRightId** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Comma`。
形式化陈述：mapRightId [Q.RespectsIso] [W.RespectsIso] : mapRight (P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `P.Comma L R Q W ⥤ P.Comma L R Q W` induced by the identity natural 
transformation
on `R` is naturally isomorphic to the identity functor.
-/
def mapRightId [Q.RespectsIso] [W.RespectsIso] :
    mapRight (P := P) (Q := Q) (W := W) L (𝟙 R) (fun X ↦ by simpa using X.prop) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (L) in
/-- The functor `P.Comma L R₁ Q W ⥤ P.Comma L R₃ Q W` induced by the composition of the natural
transformations `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the
functors induced by these natural transformations. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapRightComp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty.Comma`。
形式化陈述：mapRightComp [Q.RespectsIso] [W.RespectsIso] (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) 
(hr : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right)) (hr' : forall (X
 : P.Comma L R₂ Q W), P (X.hom ≫ r'.app X.right)) (hrr' : forall (X : P.Comma L 
R₁ Q W), P (X.hom ≫ (r ≫ r').app X.right)) : mapRight (P
参数：r : R₁ ⟶ R₂；r' : R₂ ⟶ R₃；hr : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app
 X.right)；hr' : forall (X : P.Comma L R₂ Q W), P (X.hom ≫ r'.app X.right)；hrr' :
 forall (X : P.Comma L R₁ Q W), P (X.hom ≫ (r ≫ r').app X.right)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `P.Comma L R₁ Q W ⥤ P.Comma L R₃ Q W` induced by the composition of 
the natural
transformations `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the 
composition of the
functors induced by these natural transformations.
-/
def mapRightComp [Q.RespectsIso] [W.RespectsIso] (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃)
    (hr : ∀ (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right))
    (hr' : ∀ (X : P.Comma L R₂ Q W), P (X.hom ≫ r'.app X.right))
    (hrr' : ∀ (X : P.Comma L R₁ Q W), P (X.hom ≫ (r ≫ r').app X.right)) :
    mapRight (P := P) (Q := Q) (W := W) L (r ≫ r') hrr' ≅
      mapRight L r hr ⋙ mapRight L r' hr' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (L) in
/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
`P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W`. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapRightEq** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Comma`。
形式化陈述：mapRightEq [Q.RespectsIso] [W.RespectsIso] (r r' : R₁ ⟶ R₂) (h : r = r') (
hr : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right)) : mapRight L r hr
 ≅ mapRight L r' (h ▸ hr)
参数：r r' : R₁ ⟶ R₂；h : r = r'；hr : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ r.ap
p X.right)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
`P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W`.
-/
def mapRightEq [Q.RespectsIso] [W.RespectsIso] (r r' : R₁ ⟶ R₂) (h : r = r')
    (hr : ∀ (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right)) :
    mapRight L r hr ≅ mapRight L r' (h ▸ hr) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (L) in
/-- A natural isomorphism `R₁ ≅ R₂` induces an equivalence of categories
`P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W`. -/
@[simps!]
/-
**CategoryTheory.MorphismProperty.Comma.mapRightIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.Comma`。
形式化陈述：mapRightIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso] (e : R₁ ≅ R₂) 
: P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W where functor
参数：e : R₁ ≅ R₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism `R₁ ≅ R₂` induces an equivalence of categories
`P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W`.
-/
def mapRightIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
      (e : R₁ ≅ R₂) :
    P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W where
  functor := Comma.mapRight L e.hom (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapRight L e.inv (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapRightId _ _).symm ≪≫
    mapRightEq _ _ _ e.hom_inv_id.symm (fun X ↦ by simpa using X.prop) ≪≫
    mapRightComp _ _ _
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  counitIso :=
    (mapRightComp _ _ _
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)).symm ≪≫
    mapRightEq _ _ _ e.inv_hom_id
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop) ≪≫
    mapRightId _ _

end Functoriality

end Comma

end Comma

section Arrow

variable {T : Type*} [Category* T]
  (P Q W : MorphismProperty T) [Q.IsMultiplicative] [W.IsMultiplicative]

/-- Given a morphism property `P` on a category `T`, this is the
subcategory of `Arrow T` defined by `P` where morphisms satisfy `Q` and `W` on the left and right,
respectively. -/
/-
**CategoryTheory.MorphismProperty.Arrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     Cat
egoryTheory.MorphismProperty T →       CategoryTheory.MorphismProperty T → Categ
oryTheory.MorphismProperty T → Type (max v_1 u_1)
参数：max v_1 u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `P` on a category `T`, this is the
subcategory of `Arrow T` defined by `P` where morphisms satisfy `Q` and `W` on t
he left and right,
respectively.
-/
protected abbrev Arrow : Type _ := P.Comma (𝟭 T) (𝟭 T) Q W

/-- The forgetful functor from the full subcategory of `Arrow T` defined by `P` to `Arrow T`. -/
/-
**CategoryTheory.MorphismProperty.Arrow.forget** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty.Arrow`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q W : CategoryTheory.MorphismProperty T) →       [inst_1 : Q.IsMultiplicative] →
         [inst_2 : W.IsMultiplicative] → CategoryTheory.Functor (P.Arrow Q W) (C
ategoryTheory.Arrow T)
参数：P Q W : CategoryTheory.MorphismProperty T；P.Arrow Q W；CategoryTheory.Arrow T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the full subcategory of `Arrow T` defined by `P` to `
Arrow T`.
-/
protected abbrev Arrow.forget : P.Arrow Q W ⥤ Arrow T := Comma.forget (𝟭 T) (𝟭 T) P Q W
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Arrow.forget P Q W).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Arrow.forget P ⊤ ⊤).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

/-- Occasionally useful for rewriting in the backwards direction. -/
/-
**CategoryTheory.MorphismProperty.Arrow.forget_comp_leftFunc_map** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MorphismProperty.Arrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q W : Ca
tegoryTheory.MorphismProperty T)   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {A B : P.Arrow Q W} (f : A ⟶ B),   ((CategoryTheory.MorphismPrope
rty.Arrow.forget P Q W).comp CategoryTheory.Arrow.leftFunc).map f = f.left
参数：P Q W : CategoryTheory.MorphismProperty T；f : A ⟶ B；(CategoryTheory.MorphismP
roperty.Arrow.forget P Q W).comp CategoryTheory.Arrow.leftFunc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Occasionally useful for rewriting in the backwards direction.
-/
lemma Arrow.forget_comp_leftFunc_map {A B : P.Arrow Q W} (f : A ⟶ B) :
    (MorphismProperty.Arrow.forget P Q W ⋙ CategoryTheory.Arrow.leftFunc).map f = f.left := rfl

/-- Occasionally useful for rewriting in the backwards direction. -/
/-
**CategoryTheory.MorphismProperty.Arrow.forget_comp_rightFunc_map** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.MorphismProperty.Arrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q W : Ca
tegoryTheory.MorphismProperty T)   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {A B : P.Arrow Q W} (f : A ⟶ B),   ((CategoryTheory.MorphismPrope
rty.Arrow.forget P Q W).comp CategoryTheory.Arrow.rightFunc).map f = f.right
参数：P Q W : CategoryTheory.MorphismProperty T；f : A ⟶ B；(CategoryTheory.MorphismP
roperty.Arrow.forget P Q W).comp CategoryTheory.Arrow.rightFunc。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Occasionally useful for rewriting in the backwards direction.
-/
lemma Arrow.forget_comp_rightFunc_map {A B : P.Arrow Q W} (f : A ⟶ B) :
    (MorphismProperty.Arrow.forget P Q W ⋙ CategoryTheory.Arrow.rightFunc).map f = f.right := rfl

variable {P Q W}

/-- Construct a morphism in `P.Arrow Q W` from a morphism in `Arrow T`. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Arrow.Hom.mk** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty.Arrow.Hom`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q W : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →
         [inst_2 : W.IsMultiplicative] →           {A B : P.Arrow Q W} →        
     (f :                 (CategoryTheory.MorphismProperty.Arrow.forget P Q W).o
bj A ⟶                   (CategoryTheory.MorphismProperty.Arrow.forget P Q W).ob
j B) →               Q (CategoryTheory.Arrow.Hom.left f) → W (CategoryTheory.Arr
ow.Hom.right f) → (A ⟶ B)
参数：f :                 (CategoryTheory.MorphismProperty.Arrow.forget P Q W).obj 
A ⟶                   (CategoryTheory.MorphismProperty.Arrow.forget P Q W).obj B
；CategoryTheory.Arrow.Hom.left f；CategoryTheory.Arrow.Hom.right f；A ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism in `P.Arrow Q W` from a morphism in `Arrow T`.
-/
def Arrow.Hom.mk {A B : P.Arrow Q W} (f : (Arrow.forget _ _ _).obj A ⟶ (Arrow.forget _ _ _).obj B)
    (hfl : Q f.left) (hfr : W f.right) : A ⟶ B where
  __ := f
  prop_hom_left := hfl
  prop_hom_right := hfr

/-- Make an object of `P.Arrow Q X` from a morphism `f : A ⟶ B` and a proof of `P f`. -/
@[simps hom left]
/-
**CategoryTheory.MorphismProperty.Arrow.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty.Arrow`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q W : CategoryTheory.MorphismProperty T} → {A B : T} → (f : A ⟶ B) → P f → P.Arr
ow Q W
参数：f : A ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an object of `P.Arrow Q X` from a morphism `f : A ⟶ B` and a proof of `P f`
.
-/
protected def Arrow.mk {A B : T} (f : A ⟶ B) (hf : P f) : P.Arrow Q W where
  left := A
  right := B
  hom := f
  prop := hf

/-- Make a morphism in `P.Arrow Q X` from morphisms in `T` with compatibilities. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Arrow.homMk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Arrow`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q W : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →
         [inst_2 : W.IsMultiplicative] →           {A B : P.Arrow Q W} →        
     (f : A.left ⟶ B.left) →               (g : A.right ⟶ B.right) →            
     autoParam (CategoryTheory.CategoryStruct.comp f B.hom = CategoryTheory.Cate
goryStruct.comp A.hom g)                     CategoryTheory.MorphismProperty.Arr
ow.homMk._auto_1 →                   autoParam (Q f) CategoryTheory.MorphismProp
erty.Arrow.homMk._auto_3 →                     autoParam (W g) CategoryTheory.Mo
rphismProperty.Arrow.homMk._auto_5 → (A ⟶ B)
参数：f : A.left ⟶ B.left；g : A.right ⟶ B.right；CategoryTheory.CategoryStruct.comp 
f B.hom = CategoryTheory.CategoryStruct.comp A.hom g；Q f；W g；A ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a morphism in `P.Arrow Q X` from morphisms in `T` with compatibilities.
-/
protected def Arrow.homMk {A B : P.Arrow Q W} (f : A.left ⟶ B.left) (g : A.right ⟶ B.right)
    (w : f ≫ B.hom = A.hom ≫ g := by cat_disch)
    (hf : Q f := by trivial) (hg : W g := by trivial) : A ⟶ B where
  __ := CategoryTheory.Arrow.homMk f g w
  prop_hom_left := hf
  prop_hom_right := hg

/-- Make an isomorphism in `P.Arrow Q X` from isomorphisms in `T` with compatibilities. -/
@[simps! hom_left inv_left]
/-
**CategoryTheory.MorphismProperty.Arrow.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Arrow`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q W : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →
         [inst_2 : W.IsMultiplicative] →           [Q.RespectsIso] →            
 [W.RespectsIso] →               {A B : P.Arrow Q W} →                 (f : A.le
ft ≅ B.left) →                   (g : A.right ≅ B.right) →                     a
utoParam                         (CategoryTheory.CategoryStruct.comp f.hom B.hom
 =                           CategoryTheory.CategoryStruct.comp A.hom g.hom)    
                     CategoryTheory.MorphismProperty.Arrow.isoMk._auto_1 →      
                 (A ≅ B)
参数：f : A.left ≅ B.left；g : A.right ≅ B.right；CategoryTheory.CategoryStruct.comp 
f.hom B.hom =                           CategoryTheory.CategoryStruct.comp A.hom
 g.hom；A ≅ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an isomorphism in `P.Arrow Q X` from isomorphisms in `T` with compatibiliti
es.
-/
protected def Arrow.isoMk [Q.RespectsIso] [W.RespectsIso] {A B : P.Arrow Q W}
    (f : A.left ≅ B.left) (g : A.right ≅ B.right)
    (w : f.hom ≫ B.hom = A.hom ≫ g.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk f g

@[ext]
/-
**CategoryTheory.MorphismProperty.Arrow.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MorphismProperty.Arrow.Hom`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q W : Ca
tegoryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {A B : P.Arrow Q W} {f g : A ⟶ B},   f.left = g.left → f.right = 
g.right → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.ext'`：∀ {A : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory
.Category.{v_2, u_2} B] {T : Type u_…
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
-/
lemma Arrow.Hom.ext {A B : P.Arrow Q W} {f g : A ⟶ B}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  ext
  · exact hl
  · exact hr

@[reassoc]
/-
**CategoryTheory.MorphismProperty.Arrow.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MorphismProperty.Arrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q W : Ca
tegoryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {A B : P.Arrow Q W} (f : A ⟶ B),   CategoryTheory.CategoryStruct.
comp f.left B.hom = CategoryTheory.CategoryStruct.comp A.hom f.right
参数：f : A ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
lemma Arrow.w {A B : P.Arrow Q W} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom ≫ f.right := f.w

section

variable {P' Q' W' : MorphismProperty T} [Q'.IsMultiplicative] [W'.IsMultiplicative]
    (hPP' : P ≤ P') (hQQ' : Q ≤ Q')

/-- The natural inclusion induced by implications of morphism properties. -/
/-
**CategoryTheory.MorphismProperty.Arrow.changeProp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.Arrow`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q W : CategoryTheory.MorphismProperty T} →       [inst_1 : Q.IsMultiplicative] →
         [inst_2 : W.IsMultiplicative] →           {P' Q' W' : CategoryTheory.Mo
rphismProperty T} →             [inst_3 : Q'.IsMultiplicative] →               [
inst_4 : W'.IsMultiplicative] →                 P ≤ P' → Q ≤ Q' → W ≤ W' → Categ
oryTheory.Functor (P.Arrow Q W) (P'.Arrow Q' W')
参数：P.Arrow Q W；P'.Arrow Q' W'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion induced by implications of morphism properties.
-/
abbrev Arrow.changeProp (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (hWW' : W ≤ W') :
    P.Arrow Q W ⥤ P'.Arrow Q' W' :=
  Comma.changeProp _ _ hPP' hQQ' hWW'

-- `simps` on `Arrow.changeProp` fails to create this lemma
@[simp]
/-
**CategoryTheory.MorphismProperty.Arrow.changeProp_obj_left** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MorphismProperty.Arrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q W : Ca
tegoryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {P' Q' W' : CategoryTheory.MorphismProperty T}   [inst_3 : Q'.IsM
ultiplicative] [inst_4 : W'.IsMultiplicative] (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (h
WW' : W ≤ W')   (Y : P.Arrow Q W), ((CategoryTheory.MorphismProperty.Arrow.chang
eProp hPP' hQQ' hWW').obj Y).left = Y.left
参数：hPP' : P ≤ P'；hQQ' : Q ≤ Q'；hWW' : W ≤ W'；Y : P.Arrow Q W；(CategoryTheory.Mor
phismProperty.Arrow.changeProp hPP' hQQ' hWW').obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.changeProp_obj_left (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (hWW' : W ≤ W') (Y : P.Arrow Q W) :
    ((changeProp hPP' hQQ' hWW').obj Y).left = Y.left := rfl

-- `simps` on `Arrow.changeProp` fails to create this lemma
@[simp]
/-
**CategoryTheory.MorphismProperty.Arrow.changeProp_obj_right** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MorphismProperty.Arrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q W : Ca
tegoryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {P' Q' W' : CategoryTheory.MorphismProperty T}   [inst_3 : Q'.IsM
ultiplicative] [inst_4 : W'.IsMultiplicative] (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (h
WW' : W ≤ W')   (Y : P.Arrow Q W), ((CategoryTheory.MorphismProperty.Arrow.chang
eProp hPP' hQQ' hWW').obj Y).right = Y.right
参数：hPP' : P ≤ P'；hQQ' : Q ≤ Q'；hWW' : W ≤ W'；Y : P.Arrow Q W；(CategoryTheory.Mor
phismProperty.Arrow.changeProp hPP' hQQ' hWW').obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.changeProp_obj_right (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (hWW' : W ≤ W') (Y : P.Arrow Q W) :
    ((changeProp hPP' hQQ' hWW').obj Y).right = Y.right := rfl

-- `simps` on `Arrow.changeProp` fails to create this lemma
@[simp]
/-
**CategoryTheory.MorphismProperty.Arrow.changeProp_obj_hom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.Arrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q W : Ca
tegoryTheory.MorphismProperty T}   [inst_1 : Q.IsMultiplicative] [inst_2 : W.IsM
ultiplicative] {P' Q' W' : CategoryTheory.MorphismProperty T}   [inst_3 : Q'.IsM
ultiplicative] [inst_4 : W'.IsMultiplicative] (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (h
WW' : W ≤ W')   (Y : P.Arrow Q W), ((CategoryTheory.MorphismProperty.Arrow.chang
eProp hPP' hQQ' hWW').obj Y).hom = Y.hom
参数：hPP' : P ≤ P'；hQQ' : Q ≤ Q'；hWW' : W ≤ W'；Y : P.Arrow Q W；(CategoryTheory.Mor
phismProperty.Arrow.changeProp hPP' hQQ' hWW').obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Arrow.changeProp_obj_hom (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (hWW' : W ≤ W') (Y : P.Arrow Q W) :
    ((changeProp hPP' hQQ' hWW').obj Y).hom = Y.hom := rfl

end

end Arrow

section Over

variable {T : Type*} [Category* T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

/-- Given a morphism property `P` on a category `T` and an object `X : T`, this is the
subcategory of `Over X` defined by `P` where morphisms satisfy `Q`. -/
/-
**CategoryTheory.MorphismProperty.Over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MorphismProperty`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     Cat
egoryTheory.MorphismProperty T → CategoryTheory.MorphismProperty T → T → Type (m
ax v_1 u_1)
参数：max v_1 u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `P` on a category `T` and an object `X : T`, this is t
he
subcategory of `Over X` defined by `P` where morphisms satisfy `Q`.
-/
protected abbrev Over : Type _ :=
  P.Comma (Functor.id T) (Functor.fromPUnit.{0} X) Q ⊤

/-- The forgetful functor from the full subcategory of `Over X` defined by `P` to `Over X`. -/
/-
**CategoryTheory.MorphismProperty.Over.forget** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q : CategoryTheory.MorphismProperty T) →       (X : T) → [inst_1 : Q.IsMultiplic
ative] → CategoryTheory.Functor (P.Over Q X) (CategoryTheory.Over X)
参数：P Q : CategoryTheory.MorphismProperty T；X : T；P.Over Q X；CategoryTheory.Over 
X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the full subcategory of `Over X` defined by `P` to `O
ver X`.
-/
protected abbrev Over.forget : P.Over Q X ⥤ Over X :=
  Comma.forget (Functor.id T) (Functor.fromPUnit.{0} X) P Q ⊤
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Over.forget P Q X).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Over.forget P ⊤ X).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

/-- Occasionally useful for rewriting in the backwards direction. -/
/-
**CategoryTheory.MorphismProperty.Over.forget_comp_forget_map** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : Cate
goryTheory.MorphismProperty T) (X : T)   [inst_1 : Q.IsMultiplicative] {A B : P.
Over Q X} (f : A ⟶ B),   ((CategoryTheory.MorphismProperty.Over.forget P Q X).co
mp (CategoryTheory.Over.forget X)).map f = f.left
参数：P Q : CategoryTheory.MorphismProperty T；X : T；f : A ⟶ B；(CategoryTheory.Morph
ismProperty.Over.forget P Q X).comp (CategoryTheory.Over.forget X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Occasionally useful for rewriting in the backwards direction.
-/
lemma Over.forget_comp_forget_map {A B : P.Over Q X} (f : A ⟶ B) :
    (MorphismProperty.Over.forget P Q X ⋙ CategoryTheory.Over.forget X).map f = f.left := rfl

variable {P Q X}

/-- Construct a morphism in `P.Over Q X` from a morphism in `Over X`. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Over.Hom.mk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Over.Hom`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       {X : T} →         [inst_1 : Q.IsM
ultiplicative] →           {A B : P.Over Q X} →             (f :                
 (CategoryTheory.MorphismProperty.Over.forget P Q X).obj A ⟶                   (
CategoryTheory.MorphismProperty.Over.forget P Q X).obj B) →               Q (Cat
egoryTheory.Over.Hom.left f) → (A ⟶ B)
参数：f :                 (CategoryTheory.MorphismProperty.Over.forget P Q X).obj A
 ⟶                   (CategoryTheory.MorphismProperty.Over.forget P Q X).obj B；C
ategoryTheory.Over.Hom.left f；A ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Construct a morphism in `P.Over Q X` from a morphism in `Over X`.
-/
def Over.Hom.mk {A B : P.Over Q X}
    (f : (Over.forget _ _ _).obj A ⟶ (Over.forget _ _ _).obj B) (hf : Q f.left) : A ⟶ B where
  __ := f
  prop_hom_left := hf
  prop_hom_right := trivial

variable (Q) in
/-- Make an object of `P.Over Q X` from a morphism `f : A ⟶ X` and a proof of `P f`. -/
@[simps hom left]
/-
**CategoryTheory.MorphismProperty.Over.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) → {X A : T} → (f : A ⟶ X) → P f → P.Over Q X
参数：Q : CategoryTheory.MorphismProperty T；f : A ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an object of `P.Over Q X` from a morphism `f : A ⟶ X` and a proof of `P f`.
-/
protected def Over.mk {A : T} (f : A ⟶ X) (hf : P f) : P.Over Q X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

/-- Make a morphism in `P.Over Q X` from a morphism in `T` with compatibilities. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Over.homMk** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       {X : T} →         [inst_1 : Q.IsM
ultiplicative] →           {A B : P.Over Q X} →             (f : A.left ⟶ B.left
) →               autoParam (CategoryTheory.CategoryStruct.comp f B.hom = A.hom)
                   CategoryTheory.MorphismProperty.Over.homMk._auto_1 →         
        autoParam (Q f) CategoryTheory.MorphismProperty.Over.homMk._auto_3 → (A 
⟶ B)
参数：f : A.left ⟶ B.left；CategoryTheory.CategoryStruct.comp f B.hom = A.hom；Q f；A 
⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Make a morphism in `P.Over Q X` from a morphism in `T` with compatibilities.
-/
protected def Over.homMk {A B : P.Over Q X} (f : A.left ⟶ B.left)
    (w : f ≫ B.hom = A.hom := by cat_disch) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Over.homMk f w
  prop_hom_left := hf
  prop_hom_right := trivial

/-- Make an isomorphism in `P.Over Q X` from an isomorphism in `T` with compatibilities. -/
@[simps! hom_left inv_left]
/-
**CategoryTheory.MorphismProperty.Over.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       {X : T} →         [inst_1 : Q.IsM
ultiplicative] →           [Q.RespectsIso] →             {A B : P.Over Q X} →   
            (f : A.left ≅ B.left) →                 autoParam (CategoryTheory.Ca
tegoryStruct.comp f.hom B.hom = A.hom)                     CategoryTheory.Morphi
smProperty.Over.isoMk._auto_1 →                   (A ≅ B)
参数：f : A.left ≅ B.left；CategoryTheory.CategoryStruct.comp f.hom B.hom = A.hom；A 
≅ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an isomorphism in `P.Over Q X` from an isomorphism in `T` with compatibilit
ies.
-/
protected def Over.isoMk [Q.RespectsIso] {A B : P.Over Q X} (f : A.left ≅ B.left)
    (w : f.hom ≫ B.hom = A.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk f (Discrete.eqToIso' rfl)

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/-
**CategoryTheory.MorphismProperty.Over.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MorphismProperty.Over.Hom`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T} {X : T}   [inst_1 : Q.IsMultiplicative] {A B : P.
Over Q X} {f g : A ⟶ B}, f.left = g.left → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.ext'`：∀ {A : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory
.Category.{v_2, u_2} B] {T : Type u_…
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Over.Hom.ext {A B : P.Over Q X} {f g : A ⟶ B} (h : f.left = g.left) : f = g := by
  ext
  · exact h
  · simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.MorphismProperty.Over.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T} {X : T}   [inst_1 : Q.IsMultiplicative] {A B : P.
Over Q X} (f : A ⟶ B), CategoryTheory.CategoryStruct.comp f.left B.hom = A.hom
参数：f : A ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Over.w {A B : P.Over Q X} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom := by
  simp

section

variable {P' Q' : MorphismProperty T} [Q'.IsMultiplicative] (hPP' : P ≤ P') (hQQ' : Q ≤ Q')

variable (X) in
/-- The natural inclusion induced by implications of morphism properties. -/
/-
**CategoryTheory.MorphismProperty.Over.changeProp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MorphismProperty.Over`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       (X : T) →         [inst_1 : Q.IsM
ultiplicative] →           {P' Q' : CategoryTheory.MorphismProperty T} →        
     [inst_2 : Q'.IsMultiplicative] → P ≤ P' → Q ≤ Q' → CategoryTheory.Functor (
P.Over Q X) (P'.Over Q' X)
参数：X : T；P.Over Q X；P'.Over Q' X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion induced by implications of morphism properties.
-/
abbrev Over.changeProp (hPP' : P ≤ P') (hQQ' : Q ≤ Q') :
    P.Over Q X ⥤ P'.Over Q' X :=
  Comma.changeProp _ _ hPP' hQQ' le_rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.Over.changeProp_obj_left** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T} {X : T}   [inst_1 : Q.IsMultiplicative] {P' Q' : 
CategoryTheory.MorphismProperty T} [inst_2 : Q'.IsMultiplicative]   (hPP' : P ≤ 
P') (hQQ' : Q ≤ Q') (Y : P.Over Q X),   ((CategoryTheory.MorphismProperty.Over.c
hangeProp X hPP' hQQ').obj Y).left = Y.left
参数：hPP' : P ≤ P'；hQQ' : Q ≤ Q'；Y : P.Over Q X；(CategoryTheory.MorphismProperty.O
ver.changeProp X hPP' hQQ').obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
-/
lemma Over.changeProp_obj_left (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (Y : P.Over Q X) :
    ((changeProp X hPP' hQQ').obj Y).left = Y.left := rfl

@[simp]
/-
**CategoryTheory.MorphismProperty.Over.changeProp_obj_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T} {X : T}   [inst_1 : Q.IsMultiplicative] {P' Q' : 
CategoryTheory.MorphismProperty T} [inst_2 : Q'.IsMultiplicative]   (hPP' : P ≤ 
P') (hQQ' : Q ≤ Q') (Y : P.Over Q X),   ((CategoryTheory.MorphismProperty.Over.c
hangeProp X hPP' hQQ').obj Y).hom = Y.hom
参数：hPP' : P ≤ P'；hQQ' : Q ≤ Q'；Y : P.Over Q X；(CategoryTheory.MorphismProperty.O
ver.changeProp X hPP' hQQ').obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
-/
lemma Over.changeProp_obj_hom (hPP' : P ≤ P') (hQQ' : Q ≤ Q') (Y : P.Over Q X) :
    ((changeProp X hPP' hQQ').obj Y).hom = Y.hom := rfl

end

end Over

section Under

variable {T : Type*} [Category* T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

/-- Given a morphism property `P` on a category `T` and an object `X : T`, this is the
subcategory of `Under X` defined by `P` where morphisms satisfy `Q`. -/
/-
**CategoryTheory.MorphismProperty.Under** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     Cat
egoryTheory.MorphismProperty T → CategoryTheory.MorphismProperty T → T → Type (m
ax v_1 u_1)
参数：max v_1 u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `P` on a category `T` and an object `X : T`, this is t
he
subcategory of `Under X` defined by `P` where morphisms satisfy `Q`.
-/
protected abbrev Under : Type _ :=
  P.Comma (Functor.fromPUnit.{0} X) (Functor.id T) ⊤ Q

/-- The forgetful functor from the full subcategory of `Under X` defined by `P` to `Under X`. -/
/-
**CategoryTheory.MorphismProperty.Under.forget** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     (P 
Q : CategoryTheory.MorphismProperty T) →       (X : T) → [inst_1 : Q.IsMultiplic
ative] → CategoryTheory.Functor (P.Under Q X) (CategoryTheory.Under X)
参数：P Q : CategoryTheory.MorphismProperty T；X : T；P.Under Q X；CategoryTheory.Unde
r X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the full subcategory of `Under X` defined by `P` to `
Under X`.
-/
protected abbrev Under.forget : P.Under Q X ⥤ Under X :=
  Comma.forget (Functor.fromPUnit.{0} X) (Functor.id T) P ⊤ Q
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Under.forget P Q X).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Under.forget P ⊤ X).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

/-- Occasionally useful for rewriting in the backwards direction. -/
/-
**CategoryTheory.MorphismProperty.Under.forget_comp_forget_map** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty.Under`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : Cate
goryTheory.MorphismProperty T) (X : T)   [inst_1 : Q.IsMultiplicative] {A B : P.
Under Q X} (f : A ⟶ B),   ((CategoryTheory.MorphismProperty.Under.forget P Q X).
comp (CategoryTheory.Under.forget X)).map f = f.right
参数：P Q : CategoryTheory.MorphismProperty T；X : T；f : A ⟶ B；(CategoryTheory.Morph
ismProperty.Under.forget P Q X).comp (CategoryTheory.Under.forget X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Occasionally useful for rewriting in the backwards direction.
-/
lemma Under.forget_comp_forget_map {A B : P.Under Q X} (f : A ⟶ B) :
    (MorphismProperty.Under.forget P Q X ⋙ CategoryTheory.Under.forget X).map f = f.right := rfl

variable {P Q X}

/-- Construct a morphism in `P.Under Q X` from a morphism in `Under X`. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Under.Hom.mk** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty.Under.Hom`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       {X : T} →         [inst_1 : Q.IsM
ultiplicative] →           {A B : P.Under Q X} →             (f :               
  (CategoryTheory.MorphismProperty.Under.forget P Q X).obj A ⟶                  
 (CategoryTheory.MorphismProperty.Under.forget P Q X).obj B) →               Q (
CategoryTheory.Under.Hom.right f) → (A ⟶ B)
参数：f :                 (CategoryTheory.MorphismProperty.Under.forget P Q X).obj 
A ⟶                   (CategoryTheory.MorphismProperty.Under.forget P Q X).obj B
；CategoryTheory.Under.Hom.right f；A ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Construct a morphism in `P.Under Q X` from a morphism in `Under X`.
-/
def Under.Hom.mk {A B : P.Under Q X}
    (f : (Under.forget _ _ _).obj A ⟶ (Under.forget _ _ _).obj B) (hf : Q f.right) : A ⟶ B where
  __ := f
  prop_hom_left := trivial
  prop_hom_right := hf

variable (Q) in
/-- Make an object of `P.Under Q X` from a morphism `f : A ⟶ X` and a proof of `P f`. -/
@[simps hom left]
/-
**CategoryTheory.MorphismProperty.Under.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
: CategoryTheory.MorphismProperty T} →       (Q : CategoryTheory.MorphismPropert
y T) → {X A : T} → (f : X ⟶ A) → P f → P.Under Q X
参数：Q : CategoryTheory.MorphismProperty T；f : X ⟶ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an object of `P.Under Q X` from a morphism `f : A ⟶ X` and a proof of `P f`
.
-/
protected def Under.mk {A : T} (f : X ⟶ A) (hf : P f) : P.Under Q X where
  left := ⟨⟨⟩⟩
  right := A
  hom := f
  prop := hf

/-- Make a morphism in `P.Under Q X` from a morphism in `T` with compatibilities. -/
@[simps hom]
/-
**CategoryTheory.MorphismProperty.Under.homMk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       {X : T} →         [inst_1 : Q.IsM
ultiplicative] →           {A B : P.Under Q X} →             (f : A.right ⟶ B.ri
ght) →               autoParam (CategoryTheory.CategoryStruct.comp A.hom f = B.h
om)                   CategoryTheory.MorphismProperty.Under.homMk._auto_1 →     
            autoParam (Q f) CategoryTheory.MorphismProperty.Under.homMk._auto_3 
→ (A ⟶ B)
参数：f : A.right ⟶ B.right；CategoryTheory.CategoryStruct.comp A.hom f = B.hom；Q f；
A ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Make a morphism in `P.Under Q X` from a morphism in `T` with compatibilities.
-/
protected def Under.homMk {A B : P.Under Q X} (f : A.right ⟶ B.right)
    (w : A.hom ≫ f = B.hom := by cat_disch) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Under.homMk f w
  prop_hom_left := trivial
  prop_hom_right := hf

/-- Make an isomorphism in `P.Under Q X` from an isomorphism in `T` with compatibilities. -/
@[simps! hom_right inv_right]
/-
**CategoryTheory.MorphismProperty.Under.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty.Under`。
形式化陈述：{T : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} T] →     {P 
Q : CategoryTheory.MorphismProperty T} →       {X : T} →         [inst_1 : Q.IsM
ultiplicative] →           [Q.RespectsIso] →             {A B : P.Under Q X} →  
             (f : A.right ≅ B.right) →                 autoParam (CategoryTheory
.CategoryStruct.comp A.hom f.hom = B.hom)                     CategoryTheory.Mor
phismProperty.Under.isoMk._auto_1 →                   (A ≅ B)
参数：f : A.right ≅ B.right；CategoryTheory.CategoryStruct.comp A.hom f.hom = B.hom；
A ≅ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an isomorphism in `P.Under Q X` from an isomorphism in `T` with compatibili
ties.
-/
protected def Under.isoMk [Q.RespectsIso] {A B : P.Under Q X} (f : A.right ≅ B.right)
    (w : A.hom ≫ f.hom = B.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk (Discrete.eqToIso' rfl) f

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/-
**CategoryTheory.MorphismProperty.Under.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MorphismProperty.Under.Hom`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T} {X : T}   [inst_1 : Q.IsMultiplicative] {A B : P.
Under Q X} {f g : A ⟶ B}, f.right = g.right → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.ext'`：∀ {A : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory
.Category.{v_2, u_2} B] {T : Type u_…
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Under.Hom.ext {A B : P.Under Q X} {f g : A ⟶ B} (h : f.right = g.right) : f = g := by
  ext
  · simp
  · exact h

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.MorphismProperty.Under.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MorphismProperty.Under`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {P Q : Cate
goryTheory.MorphismProperty T} {X : T}   [inst_1 : Q.IsMultiplicative] {A B : P.
Under Q X} (f : A ⟶ B),   CategoryTheory.CategoryStruct.comp A.hom f.right = B.h
om
参数：f : A ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Under.w {A B : P.Under Q X} (f : A ⟶ B) :
    A.hom ≫ f.right = B.hom := by
  simp

end Under

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

/-- Given a morphism property `P` on a category `C` and an object `X : C`, this is the
subcategory of `CostructuredArrow F X` defined by `P` where morphisms satisfy `Q`. -/
/-
**CategoryTheory.MorphismProperty.CostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{u
_3, u_1} C] →       [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →         Ca
tegoryTheory.MorphismProperty D →           CategoryTheory.MorphismProperty C → 
CategoryTheory.Functor C D → D → Type (max u_1 u_4)
参数：max u_1 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `P` on a category `C` and an object `X : C`, this is t
he
subcategory of `CostructuredArrow F X` defined by `P` where morphisms satisfy `Q
`.
-/
protected abbrev CostructuredArrow (P : MorphismProperty D) (Q : MorphismProperty C)
    (F : C ⥤ D) (X : D) :=
  P.Comma F (Functor.fromPUnit.{0} X) Q ⊤

section CostructuredArrow

variable {P F X} in
/-- Construct an object of `P.CostructuredArrow Q F X` from a morphism `F.obj A ⟶ X`. -/
@[simps left hom]
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.mk** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.MorphismProperty.CostructuredArrow`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{u
_3, u_1} C] →       [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →         {P
 : CategoryTheory.MorphismProperty D} →           (Q : CategoryTheory.MorphismPr
operty C) →             {F : CategoryTheory.Functor C D} → {X : D} → {A : C} → (
f : F.obj A ⟶ X) → P f → P.CostructuredArrow Q F X
参数：Q : CategoryTheory.MorphismProperty C；f : F.obj A ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of `P.CostructuredArrow Q F X` from a morphism `F.obj A ⟶ X`
.
-/
protected def CostructuredArrow.mk {A : C} (f : F.obj A ⟶ X) (hf : P f) :
    P.CostructuredArrow Q F X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

variable {P Q F X} in
/-- Construct a morphism in `P.CostructuredArrow Q F X` by giving a morphism on the underlying
objects of `C`. -/
@[simps left]
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.homMk** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MorphismProperty.CostructuredArrow`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{u
_3, u_1} C] →       [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →         {P
 : CategoryTheory.MorphismProperty D} →           {Q : CategoryTheory.MorphismPr
operty C} →             [inst_2 : Q.IsMultiplicative] →               {F : Categ
oryTheory.Functor C D} →                 {X : D} →                   {A B : P.Co
structuredArrow Q F X} →                     (f : A.left ⟶ B.left) →            
           Q f →                         autoParam (CategoryTheory.CategoryStruc
t.comp (F.map f) B.hom = A.hom)                             CategoryTheory.Morph
ismProperty.CostructuredArrow.homMk._auto_1 →                           (A ⟶ B)
参数：f : A.left ⟶ B.left；CategoryTheory.CategoryStruct.comp (F.map f) B.hom = A.ho
m；A ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Construct a morphism in `P.CostructuredArrow Q F X` by giving a morphism on the 
underlying
objects of `C`.
-/
def CostructuredArrow.homMk {A B : P.CostructuredArrow Q F X} (f : A.left ⟶ B.left) (hf : Q f)
    (w : F.map f ≫ B.hom = A.hom := by cat_disch) :
    A ⟶ B where
  left := f
  right := eqToHom (Subsingleton.elim _ _)
  prop_hom_left := hf
  prop_hom_right := trivial

set_option backward.isDefEq.respectTransparency.types false in
variable {P Q F X} in
@[ext]
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.Hom.ext** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MorphismProperty.CostructuredArrow.Hom`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{u_3, u_1}
 C]   [inst_1 : CategoryTheory.Category.{u_4, u_2} D] {P : CategoryTheory.Morphi
smProperty D}   {Q : CategoryTheory.MorphismProperty C} [inst_2 : Q.IsMultiplica
tive] {F : CategoryTheory.Functor C D} {X : D}   {A B : P.CostructuredArrow Q F 
X} {f g : A ⟶ B}, f.left = g.left → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.Comma.Hom.ext'`：∀ {A : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory
.Category.{v_2, u_2} B] {T : Type u_…
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CostructuredArrow.Hom.ext {A B : P.CostructuredArrow Q F X} {f g : A ⟶ B}
    (h : f.left = g.left) : f = g := by
  ext <;> simp [h]

variable {P Q F X} in
/-- Construct an isomorphism in `P.CostructuredArrow Q F X` by giving the isomorphism
on the underlying objects of `C`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.isoMk** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MorphismProperty.CostructuredArrow`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{u
_3, u_1} C] →       [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →         {P
 : CategoryTheory.MorphismProperty D} →           {Q : CategoryTheory.MorphismPr
operty C} →             [inst_2 : Q.IsMultiplicative] →               {F : Categ
oryTheory.Functor C D} →                 {X : D} →                   {A B : P.Co
structuredArrow Q F X} →                     (f : A.left ≅ B.left) →            
           Q f.hom →                         Q f.inv →                          
 autoParam (CategoryTheory.CategoryStruct.comp (F.map f.hom) B.hom = A.hom)     
                          CategoryTheory.MorphismProperty.CostructuredArrow.isoM
k._auto_1 →                             (A ≅ B)
参数：f : A.left ≅ B.left；CategoryTheory.CategoryStruct.comp (F.map f.hom) B.hom = 
A.hom；A ≅ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in `P.CostructuredArrow Q F X` by giving the isomorphis
m
on the underlying objects of `C`.
-/
def CostructuredArrow.isoMk {A B : P.CostructuredArrow Q F X} (f : A.left ≅ B.left) (hf : Q f.hom)
    (hf' : Q f.inv)
    (w : F.map f.hom ≫ B.hom = A.hom := by cat_disch) :
    A ≅ B where
  hom := MorphismProperty.CostructuredArrow.homMk _ hf
  inv := MorphismProperty.CostructuredArrow.homMk _ hf' (by simp [← w])

/-- The forgetful functor from the subcategory `P.CostructuredArrow Q F X`. -/
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.forget** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.MorphismProperty.CostructuredArrow`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{u
_3, u_1} C] →       [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →         (P
 : CategoryTheory.MorphismProperty D) →           (Q : CategoryTheory.MorphismPr
operty C) →             [inst_2 : Q.IsMultiplicative] →               (F : Categ
oryTheory.Functor C D) →                 (X : D) → CategoryTheory.Functor (P.Cos
tructuredArrow Q F X) (CategoryTheory.CostructuredArrow F X)
参数：P : CategoryTheory.MorphismProperty D；Q : CategoryTheory.MorphismProperty C；F
 : CategoryTheory.Functor C D；X : D；P.CostructuredArrow Q F X；CategoryTheory.Cos
tructuredArrow F X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the subcategory `P.CostructuredArrow Q F X`.
-/
protected abbrev CostructuredArrow.forget :
    P.CostructuredArrow Q F X ⥤ CostructuredArrow F X :=
  Comma.forget _ _ _ _ _

/-- Reinterpreting an `F`-costructured arrow `F.obj A ⟶ X` as an arrow over `X`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.toOver** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.MorphismProperty.CostructuredArrow`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{u
_3, u_1} C] →       [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →         (P
 : CategoryTheory.MorphismProperty D) →           (F : CategoryTheory.Functor C 
D) → (X : D) → CategoryTheory.Functor (P.CostructuredArrow ⊤ F X) (P.Over ⊤ X)
参数：P : CategoryTheory.MorphismProperty D；F : CategoryTheory.Functor C D；X : D；P.
CostructuredArrow ⊤ F X；P.Over ⊤ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Reinterpreting an `F`-costructured arrow `F.obj A ⟶ X` as an arrow over `X`.
-/
protected def CostructuredArrow.toOver : P.CostructuredArrow ⊤ F X ⥤ P.Over ⊤ X where
  obj A := Over.mk _ A.hom A.prop
  map f := Over.homMk (F.map f.left) _
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : (CostructuredArrow.toOver P F X).Faithful := by
  constructor
  intro A B f g hfg
  ext
  exact F.map_injective congr($(hfg).left)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Full] : (CostructuredArrow.toOver P F X).Full := by
  constructor
  intro A B f
  refine ⟨CostructuredArrow.homMk (F.preimage f.left) trivial ?_, ?_⟩
  · simpa using f.w
  · ext; simp

end CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MorphismProperty.HasFactorization.over** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.HasFactorization`。
形式化陈述：∀ {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_3} C] (W₁ W₂ : Ca
tegoryTheory.MorphismProperty C)   [W₁.HasFactorization W₂] (S : C), W₁.over.Has
Factorization W₂.over
参数：W₁ W₂ : CategoryTheory.MorphismProperty C；S : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.M
orphismProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
-/
instance HasFactorization.over
    {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.HasFactorization W₂] (S : C) :
    (W₁.over (X := S)).HasFactorization W₂.over where
  nonempty_mapFactorizationData {X Y} f := by
    let hf := W₁.factorizationData W₂ f.left
    exact ⟨{
      Z := .mk (hf.p ≫ Y.hom)
      i := CategoryTheory.Over.homMk hf.i
      p := CategoryTheory.Over.homMk hf.p
      hi := hf.hi
      hp := hf.hp
    }⟩

end CategoryTheory.MorphismProperty

