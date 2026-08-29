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

/--
lemma `costructuredArrow_iso_iff` / 引理 `costructuredArrow_iso_iff`

English:
lemma costructuredArrow_iso_iff
  statement: (P : MorphismProperty T) [P.RespectsIso]
  proof: P.comma_iso_iff e

中文:
引理 costructuredArrow_iso_iff
  结论: (P : MorphismProperty T) [P.RespectsIso]
  证明: P.comma_iso_iff e

Depends on / 依赖: P.comma_iso_iff, comma_iso_iff
-/
lemma costructuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : CostructuredArrow L X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

/--
lemma `structuredArrow_iso_iff` / 引理 `structuredArrow_iso_iff`

English:
lemma structuredArrow_iso_iff
  statement: (P : MorphismProperty T) [P.RespectsIso]
  proof: P.comma_iso_iff e

中文:
引理 structuredArrow_iso_iff
  结论: (P : MorphismProperty T) [P.RespectsIso]
  证明: P.comma_iso_iff e

Depends on / 依赖: P.comma_iso_iff, comma_iso_iff
-/
lemma structuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : StructuredArrow X L} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

/--
lemma `over_iso_iff` / 引理 `over_iso_iff`

English:
lemma over_iso_iff
  given: (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g)
  proof: P.comma_iso_iff e

中文:
引理 over_iso_iff
  条件: (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g)
  证明: P.comma_iso_iff e

Depends on / 依赖: P.comma_iso_iff, comma_iso_iff
-/
lemma over_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

/--
lemma `under_iso_iff` / 引理 `under_iso_iff`

English:
lemma under_iso_iff
  given: (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Under X} (e : f ≅ g)
  proof: P.comma_iso_iff e

中文:
引理 under_iso_iff
  条件: (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Under X} (e : f ≅ g)
  证明: P.comma_iso_iff e

Depends on / 依赖: P.comma_iso_iff, comma_iso_iff
-/
lemma under_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Under X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

section

variable {W : MorphismProperty T} {X : T}

/--
Definition of `commaObj` / `commaObj` 的定义

English:
definition commaObj
  signature: (W : MorphismProperty T)
  body: fun f => W f.hom

中文:
定义 commaObj
  签名: (W : MorphismProperty T)
  定义体: fun f => W f.hom

Depends on / 依赖: f.hom
-/
def commaObj (W : MorphismProperty T) : ObjectProperty (Comma L R) :=
  fun f => W f.hom

/--
lemma `commaObj_iff` / 引理 `commaObj_iff`

English:
lemma commaObj_iff
  given: (Y : Comma L R)
  statement: W.commaObj L R Y ↔ W Y.hom
  proof: .rfl

中文:
引理 commaObj_iff
  条件: (Y : 交换a L R)
  结论: W.commaObj L R Y ↔ W Y.hom
  证明: .rfl
-/
@[simp] lemma commaObj_iff (Y : Comma L R) : W.commaObj L R Y ↔ W Y.hom := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : (W.commaObj L R).IsClosedUnderIsomorphisms where
  body: by
    rwa [commaObj_iff, ← W.cancel_left_of_respectsIso (L.map e.hom.left), e.hom.w,
      W.cancel_right_of_respectsIso]

中文:
实例 [W.RespectsIso]
  签名: : (W.commaObj L R).在同构下封闭 where
  定义体: by
    rwa [commaObj_iff, ← W.cancel_left_of_respectsIso (L.map e.hom.left), e.hom.w,
      W.cancel_right_of_respectsIso]

Depends on / 依赖: L.map, W.cancel_left_of_respectsIso, W.cancel_right_of_respectsIso, cancel_left_of_respectsIso, cancel_right_of_respectsIso, commaObj_iff, e.hom.left, e.hom.w
-/
instance [W.RespectsIso] : (W.commaObj L R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    rwa [commaObj_iff, ← W.cancel_left_of_respectsIso (L.map e.hom.left), e.hom.w,
      W.cancel_right_of_respectsIso]

/--
Definition of `costructuredArrowObj` / `costructuredArrowObj` 的定义

English:
definition costructuredArrowObj
  signature: (W : MorphismProperty T)
  body: fun f => W f.hom

中文:
定义 costructuredArrowObj
  签名: (W : MorphismProperty T)
  定义体: fun f => W f.hom

Depends on / 依赖: f.hom
-/
def costructuredArrowObj (W : MorphismProperty T) : ObjectProperty (CostructuredArrow L X) :=
  fun f => W f.hom

/--
lemma `costructuredArrowObj_iff` / 引理 `costructuredArrowObj_iff`

English:
lemma costructuredArrowObj_iff
  given: (Y : CostructuredArrow L X)
  proof: .rfl

中文:
引理 costructuredArrowObj_iff
  条件: (Y : CostructuredArrow L X)
  证明: .rfl
-/
@[simp] lemma costructuredArrowObj_iff (Y : CostructuredArrow L X) :
    W.costructuredArrowObj L Y ↔ W Y.hom := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : (W.costructuredArrowObj L (X := X)).IsClosedUnderIsomorphisms
  body: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

中文:
实例 [W.RespectsIso]
  签名: : (W.costructuredArrowObj L (X := X)).在同构下封闭
  定义体: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
instance [W.RespectsIso] : (W.costructuredArrowObj L (X := X)).IsClosedUnderIsomorphisms :=
inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

/--
Definition of `structuredArrowObj` / `structuredArrowObj` 的定义

English:
definition structuredArrowObj
  signature: (W : MorphismProperty T)
  body: fun f => W f.hom

中文:
定义 structuredArrowObj
  签名: (W : MorphismProperty T)
  定义体: fun f => W f.hom

Depends on / 依赖: f.hom
-/
def structuredArrowObj (W : MorphismProperty T) : ObjectProperty (StructuredArrow X R) :=
  fun f => W f.hom

/--
lemma `structuredArrowObj_iff` / 引理 `structuredArrowObj_iff`

English:
lemma structuredArrowObj_iff
  given: (Y : StructuredArrow X R)
  proof: .rfl

中文:
引理 structuredArrowObj_iff
  条件: (Y : 结构化箭头 X R)
  证明: .rfl
-/
@[simp] lemma structuredArrowObj_iff (Y : StructuredArrow X R) :
    W.structuredArrowObj R Y ↔ W Y.hom := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : (W.structuredArrowObj L (X := X)).IsClosedUnderIsomorphisms
  body: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

中文:
实例 [W.RespectsIso]
  签名: : (W.structuredArrowObj L (X := X)).在同构下封闭
  定义体: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
instance [W.RespectsIso] : (W.structuredArrowObj L (X := X)).IsClosedUnderIsomorphisms :=
inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

/--
Definition of `over` / `over` 的定义

English:
definition over
  signature: (W : MorphismProperty T) {X : T}
  body: fun _ _ f => W f.left

中文:
定义 over
  签名: (W : MorphismProperty T) {X : T}
  定义体: fun _ _ f => W f.left

Depends on / 依赖: f.left
-/
def over (W : MorphismProperty T) {X : T} : MorphismProperty (Over X) := fun _ _ f => W f.left

/--
lemma `over_eq_inverseImage` / 引理 `over_eq_inverseImage`

English:
lemma over_eq_inverseImage
  given: (W : MorphismProperty T) (X : T)
  proof: rfl

中文:
引理 over_eq_inverseImage
  条件: (W : MorphismProperty T) (X : T)
  证明: rfl
-/
lemma over_eq_inverseImage (W : MorphismProperty T) (X : T) :
    W.over = W.inverseImage (Over.forget X) := rfl

/--
lemma `over_iff` / 引理 `over_iff`

English:
lemma over_iff
  given: {Y Z : Over X} (f : Y ⟶ Z)
  statement: W.over f ↔ W f.left
  proof: .rfl

中文:
引理 over_iff
  条件: {Y Z : Over X} (f : Y ⟶ Z)
  结论: W.over f ↔ W f.left
  证明: .rfl
-/
@[simp] lemma over_iff {Y Z : Over X} (f : Y ⟶ Z) : W.over f ↔ W f.left := .rfl

/--
Definition of `under` / `under` 的定义

English:
definition under
  signature: (W : MorphismProperty T) {X : T}
  body: fun _ _ f => W f.right

中文:
定义 under
  签名: (W : MorphismProperty T) {X : T}
  定义体: fun _ _ f => W f.right

Depends on / 依赖: f.right
-/
def under (W : MorphismProperty T) {X : T} : MorphismProperty (Under X) := fun _ _ f => W f.right

/--
lemma `under_eq_inverseImage` / 引理 `under_eq_inverseImage`

English:
lemma under_eq_inverseImage
  given: (W : MorphismProperty T) (X : T)
  proof: rfl

中文:
引理 under_eq_inverseImage
  条件: (W : MorphismProperty T) (X : T)
  证明: rfl
-/
lemma under_eq_inverseImage (W : MorphismProperty T) (X : T) :
    W.under = W.inverseImage (Under.forget X) := rfl

/--
lemma `under_iff` / 引理 `under_iff`

English:
lemma under_iff
  given: {Y Z : Under X} (f : Y ⟶ Z)
  statement: W.under f ↔ W f.right
  proof: .rfl

中文:
引理 under_iff
  条件: {Y Z : Under X} (f : Y ⟶ Z)
  结论: W.under f ↔ W f.right
  证明: .rfl
-/
@[simp] lemma under_iff {Y Z : Under X} (f : Y ⟶ Z) : W.under f ↔ W f.right := .rfl

/--
Definition of `overObj` / `overObj` 的定义

English:
definition overObj
  signature: (W : MorphismProperty T) {X : T}
  body: fun f => W f.hom

中文:
定义 overObj
  签名: (W : MorphismProperty T) {X : T}
  定义体: fun f => W f.hom

Depends on / 依赖: f.hom
-/
def overObj (W : MorphismProperty T) {X : T} : ObjectProperty (Over X) := fun f => W f.hom

/--
lemma `overObj_iff` / 引理 `overObj_iff`

English:
lemma overObj_iff
  given: (Y : Over X)
  statement: W.overObj Y ↔ W Y.hom
  proof: .rfl

中文:
引理 overObj_iff
  条件: (Y : Over X)
  结论: W.overObj Y ↔ W Y.hom
  证明: .rfl
-/
@[simp] lemma overObj_iff (Y : Over X) : W.overObj Y ↔ W Y.hom := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : (W.overObj (X := X)).IsClosedUnderIsomorphisms
  body: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

中文:
实例 [W.RespectsIso]
  签名: : (W.overObj (X := X)).在同构下封闭
  定义体: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
instance [W.RespectsIso] : (W.overObj (X := X)).IsClosedUnderIsomorphisms :=
inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

/--
Definition of `underObj` / `underObj` 的定义

English:
definition underObj
  signature: (W : MorphismProperty T) {X : T}
  body: fun f => W f.hom

中文:
定义 underObj
  签名: (W : MorphismProperty T) {X : T}
  定义体: fun f => W f.hom

Depends on / 依赖: f.hom
-/
def underObj (W : MorphismProperty T) {X : T} : ObjectProperty (Under X) := fun f => W f.hom

/--
lemma `underObj_iff` / 引理 `underObj_iff`

English:
lemma underObj_iff
  given: (Y : Under X)
  statement: W.underObj Y ↔ W Y.hom
  proof: .rfl

中文:
引理 underObj_iff
  条件: (Y : Under X)
  结论: W.underObj Y ↔ W Y.hom
  证明: .rfl
-/
@[simp] lemma underObj_iff (Y : Under X) : W.underObj Y ↔ W Y.hom := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : (W.underObj (X := X)).IsClosedUnderIsomorphisms
  body: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

@[simp]

中文:
实例 [W.RespectsIso]
  签名: : (W.underObj (X := X)).在同构下封闭
  定义体: inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

@[simp]

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
instance [W.RespectsIso] : (W.underObj (X := X)).IsClosedUnderIsomorphisms :=
inferInstanceAs (W.commaObj _ _).IsClosedUnderIsomorphisms

@[simp]
/--
lemma `inverseImage_op_overObj` / 引理 `inverseImage_op_overObj`

English:
lemma inverseImage_op_overObj
  given: (W : MorphismProperty T) {X : T}
  proof: rfl

@[simp]

中文:
引理 inverseImage_op_overObj
  条件: (W : MorphismProperty T) {X : T}
  证明: rfl

@[simp]
-/
lemma inverseImage_op_overObj (W : MorphismProperty T) {X : T} :
    W.overObj.op.inverseImage (Under.opEquivOpOver X).functor = W.op.underObj := rfl

@[simp]
/--
lemma `inverseImage_op_underObj` / 引理 `inverseImage_op_underObj`

English:
lemma inverseImage_op_underObj
  given: (W : MorphismProperty T) {X : T}
  proof: rfl

中文:
引理 inverseImage_op_underObj
  条件: (W : MorphismProperty T) {X : T}
  证明: rfl
-/
lemma inverseImage_op_underObj (W : MorphismProperty T) {X : T} :
    W.underObj.op.inverseImage (Over.opEquivOpUnder X).functor = W.op.overObj := rfl

end

variable (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)

/-- `P.Comma L R Q W` is the subcategory of `Comma L R` consisting of
objects `X : Comma L R` where `X.hom` satisfies `P`. The morphisms are given by
morphisms in `Comma L R` where the left one satisfies `Q` and the right one satisfies `W`. -/
@[ext]
/--
Definition of `Comma` / `Comma` 的定义

English:
structure Comma
  parameters: (Q : MorphismProperty A) (W : MorphismProperty B)
  extends: Comma L R
  axioms and operations (1):
    - prop : P toComma.hom

中文:
结构 交换a
  参数: (Q : MorphismProperty A) (W : MorphismProperty B)
  继承: 交换a L R
  公理与运算 (1 个):
    - prop : P toComma.hom
-/
protected structure Comma (Q : MorphismProperty A) (W : MorphismProperty B) extends Comma L R where
  prop : P toComma.hom

namespace Comma

variable {L R P Q W}

/-- A morphism in `P.Comma L R Q W` is a morphism in `Comma L R` where the left
hom satisfies `Q` and the right one satisfies `W`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : P.Comma L R Q W)
  extends: CommaMorphism X.toComma Y.toComma
  axioms and operations (2):
    - prop_hom_left : Q toCommaMorphism.left
    - prop_hom_right : W toCommaMorphism.right

中文:
结构 态射
  参数: (X Y : P.交换a L R Q W)
  继承: 交换a态射 X.toComma Y.toComma
  公理与运算 (2 个):
    - prop_hom_left : Q toCommaMorphism.left
    - prop_hom_right : W toCommaMorphism.right
-/
structure Hom (X Y : P.Comma L R Q W) extends CommaMorphism X.toComma Y.toComma where
  prop_hom_left : Q toCommaMorphism.left
  prop_hom_right : W toCommaMorphism.right

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : P.Comma L R Q W} (f : Comma.Hom X Y)
  body: f.toCommaMorphism

@[simp]

中文:
缩写 态射.hom
  签名: {X Y : P.交换a L R Q W} (f : 交换a.态射 X Y)
  定义体: f.toCommaMorphism

@[simp]
-/
abbrev Hom.hom {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : X.toComma ⟶ Y.toComma :=
  f.toCommaMorphism

@[simp]
/--
lemma `Hom.hom_mk` / 引理 `Hom.hom_mk`

English:
lemma Hom.hom_mk
  given: {X Y : P.Comma L R Q W} (f : CommaMorphism X.toComma Y.toComma) (hf) (hg)
  proof: rfl

中文:
引理 态射.hom_mk
  条件: {X Y : P.交换a L R Q W} (f : 交换a态射 X.toComma Y.toComma) (hf) (hg)
  证明: rfl
-/
lemma Hom.hom_mk {X Y : P.Comma L R Q W} (f : CommaMorphism X.toComma Y.toComma) (hf) (hg) :
    Comma.Hom.hom ⟨f, hf, hg⟩ = f := rfl

/--
lemma `Hom.hom_left` / 引理 `Hom.hom_left`

English:
lemma Hom.hom_left
  given: {X Y : P.Comma L R Q W} (f : Comma.Hom X Y)
  statement: f.hom.left = f.left
  proof: rfl

中文:
引理 态射.hom_left
  条件: {X Y : P.交换a L R Q W} (f : 交换a.态射 X Y)
  结论: f.hom.left = f.left
  证明: rfl
-/
lemma Hom.hom_left {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : f.hom.left = f.left := rfl

/--
lemma `Hom.hom_right` / 引理 `Hom.hom_right`

English:
lemma Hom.hom_right
  given: {X Y : P.Comma L R Q W} (f : Comma.Hom X Y)
  statement: f.hom.right = f.right
  proof: rfl

中文:
引理 态射.hom_right
  条件: {X Y : P.交换a L R Q W} (f : 交换a.态射 X Y)
  结论: f.hom.right = f.right
  证明: rfl
-/
lemma Hom.hom_right {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : f.hom.right = f.right := rfl

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: {X Y : P.Comma L R Q W} (f : X.Hom Y)
  body: f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism -> hom)

中文:
定义 态射.Simps.hom
  签名: {X Y : P.交换a L R Q W} (f : X.态射 Y)
  定义体: f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism -> hom)
-/
def Hom.Simps.hom {X Y : P.Comma L R Q W} (f : X.Hom Y) :
    X.toComma ⟶ Y.toComma :=
  f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism -> hom)

/-- The identity morphism of an object in `P.Comma L R Q W`. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W)
  body: 𝟙 X.left
  right := 𝟙 X.right
  prop_hom_left := Q.id_mem X.toComma.left
  prop_hom_right := W.id_mem X.toComma.right

中文:
定义 id
  签名: [Q.余ntainsIdentities] [W.余ntainsIdentities] (X : P.交换a L R Q W)
  定义体: 𝟙 X.left
  right := 𝟙 X.right
  prop_hom_left := Q.id_mem X.toComma.left
  prop_hom_right := W.id_mem X.toComma.right

Depends on / 依赖: X.left
-/
def id [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W) : Comma.Hom X X where
  left := 𝟙 X.left
  right := 𝟙 X.right
  prop_hom_left := Q.id_mem X.toComma.left
  prop_hom_right := W.id_mem X.toComma.right

/-- Composition of morphisms in `P.Comma L R Q W`. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: [Q.IsStableUnderComposition] [W.IsStableUnderComposition] {X Y Z : P.Comma L R Q W}
  body: f.left ≫ g.left
  right := f.right ≫ g.right
  prop_hom_left := Q.comp_mem _ _ f.prop_hom_left g.prop_hom_left
  prop_hom_right := W.comp_mem _ _ f.prop_hom_right g.prop_hom_right

中文:
定义 态射.comp
  签名: [Q.是StableUnderComposition] [W.是StableUnderComposition] {X Y Z : P.交换a L R Q W}
  定义体: f.left ≫ g.left
  right := f.right ≫ g.right
  prop_hom_left := Q.comp_mem _ _ f.prop_hom_left g.prop_hom_left
  prop_hom_right := W.comp_mem _ _ f.prop_hom_right g.prop_hom_right
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (P.Comma L R Q W)
  body: X.Hom Y
  id X := X.id
  comp f g := f.comp g

中文:
实例 :
  签名: 范畴 (P.交换a L R Q W)
  定义体: X.Hom Y
  id X := X.id
  comp f g := f.comp g

Depends on / 依赖: X.Hom
-/
instance : Category (P.Comma L R Q W) where
  Hom X Y := X.Hom Y
  id X := X.id
  comp f g := f.comp g

/--
lemma `toCommaMorphism_eq_hom` / 引理 `toCommaMorphism_eq_hom`

English:
lemma toCommaMorphism_eq_hom
  given: {X Y : P.Comma L R Q W} (f : X ⟶ Y)
  statement: f.toCommaMorphism = f.hom
  proof: rfl

中文:
引理 toCommaMorphism_eq_hom
  条件: {X Y : P.交换a L R Q W} (f : X ⟶ Y)
  结论: f.toCommaMorphism = f.hom
  证明: rfl

Depends on / 依赖: isIso_hom, uniqueUpToIso
-/
lemma toCommaMorphism_eq_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) : f.toCommaMorphism = f.hom := rfl

/-- Alternative `ext` lemma for `Comma.Hom`. -/
@[ext]
/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  given: {X Y : P.Comma L R Q W} {f g : X ⟶ Y} (h : f.hom = g.hom)
  proof: Comma.Hom.ext
  (congrArg CommaMorphism.left h)
  (congrArg CommaMorphism.right h)

@[simp]

中文:
引理 态射.ext'
  条件: {X Y : P.交换a L R Q W} {f g : X ⟶ Y} (h : f.hom = g.hom)
  证明: Comma.Hom.ext
  (congrArg CommaMorphism.left h)
  (congrArg CommaMorphism.right h)

@[simp]
-/
lemma Hom.ext' {X Y : P.Comma L R Q W} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g := Comma.Hom.ext
  (congrArg CommaMorphism.left h)
  (congrArg CommaMorphism.right h)

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (X : P.Comma L R Q W)
  statement: (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma
  proof: rfl

@[simp]

中文:
引理 id_hom
  条件: (X : P.交换a L R Q W)
  结论: (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma
  证明: rfl

@[simp]
-/
lemma id_hom (X : P.Comma L R Q W) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma := rfl

@[simp]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[reassoc]

中文:
引理 comp_hom
  条件: {X Y Z : P.交换a L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[reassoc]
-/
lemma comp_hom {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[reassoc]
/--
lemma `comp_left` / 引理 `comp_left`

English:
lemma comp_left
  given: {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[reassoc]

中文:
引理 comp_left
  条件: {X Y Z : P.交换a L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[reassoc]
-/
lemma comp_left {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

@[reassoc]
/--
lemma `comp_right` / 引理 `comp_right`

English:
lemma comp_right
  given: {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 comp_right
  条件: {X Y Z : P.交换a L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma comp_right {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

/-- If `i` is an isomorphism in `Comma L R`, it is also a morphism in `P.Comma L R Q W`. -/
@[simps hom]
/--
Definition of `homFromCommaOfIsIso` / `homFromCommaOfIsIso` 的定义

English:
definition homFromCommaOfIsIso
  signature: [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
  body: i
  prop_hom_left := Q.of_isIso i.left
  prop_hom_right := W.of_isIso i.right

中文:
定义 homFromCommaOfIsIso
  签名: [Q.RespectsIso] [W.RespectsIso] {X Y : P.交换a L R Q W}
  定义体: i
  prop_hom_left := Q.of_isIso i.left
  prop_hom_right := W.of_isIso i.right
-/
def homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ⟶ Y.toComma) [IsIso i] :
    X ⟶ Y where
  __ := i
  prop_hom_left := Q.of_isIso i.left
  prop_hom_right := W.of_isIso i.right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.RespectsIso]
  signature: [W.RespectsIso] {X Y : P.Comma L R Q W} (i : X.toComma ⟶ Y.toComma)
  body: by
  constructor
  use homFromCommaOfIsIso (inv i)
  constructor <;> ext : 1 <;> simp

中文:
实例 [Q.RespectsIso]
  签名: [W.RespectsIso] {X Y : P.交换a L R Q W} (i : X.toComma ⟶ Y.toComma)
  定义体: by
  constructor
  use homFromCommaOfIsIso (inv i)
  constructor <;> ext : 1 <;> simp

Depends on / 依赖: homFromCommaOfIsIso
-/
instance [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (i : X.toComma ⟶ Y.toComma)
    [IsIso i] : IsIso (homFromCommaOfIsIso i) := by
  constructor
  use homFromCommaOfIsIso (inv i)
  constructor <;> ext : 1 <;> simp

/-- Any isomorphism between objects of `P.Comma L R Q W` in `Comma L R` is also an isomorphism
in `P.Comma L R Q W`. -/
@[simps]
/--
Definition of `isoFromComma` / `isoFromComma` 的定义

English:
definition isoFromComma
  signature: [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
  body: homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

中文:
定义 isoFromComma
  签名: [Q.RespectsIso] [W.RespectsIso] {X Y : P.交换a L R Q W}
  定义体: homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

Depends on / 依赖: homFromCommaOfIsIso, i.hom
-/
def isoFromComma [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ≅ Y.toComma) : X ≅ Y where
  hom := homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

/-- Constructor for isomorphisms in `P.Comma L R Q W` from isomorphisms of the left and right
components and naturality in the forward direction. -/
@[simps!]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left ≅ Y.left)
  body: isoFromComma (CategoryTheory.Comma.isoMk l r h)

中文:
定义 isoMk
  签名: [Q.RespectsIso] [W.RespectsIso] {X Y : P.交换a L R Q W} (l : X.left ≅ Y.left)
  定义体: isoFromComma (CategoryTheory.Comma.isoMk l r h)

Depends on / 依赖: CategoryTheory, CategoryTheory.Comma.isoMk, cat_disch, isoFromComma
-/
def isoMk [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left ≅ Y.left)
    (r : X.right ≅ Y.right) (h : L.map l.hom ≫ Y.hom = X.hom ≫ R.map r.hom := by cat_disch) :
    X ≅ Y :=
  isoFromComma (CategoryTheory.Comma.isoMk l r h)

variable (L R P Q W)

/-- The forgetful functor. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : P.Comma L R Q W ⥤ Comma L R where
  body: X.toComma
  map f := f.hom

中文:
定义 forget
  签名: : P.交换a L R Q W ⥤ 交换a L R where
  定义体: X.toComma
  map f := f.hom

Depends on / 依赖: X.toComma, toComma
-/
def forget : P.Comma L R Q W ⥤ Comma L R where
  obj X := X.toComma
  map f := f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget L R P Q W).Faithful
  body: Comma.Hom.ext'

中文:
实例 :
  签名: (forget L R P Q W).忠实
  定义体: Comma.Hom.ext'

Depends on / 依赖: Comma.Hom.ext
-/
instance : (forget L R P Q W).Faithful where
  map_injective := Comma.Hom.ext'

variable {L R P Q W}

instance {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : IsIso f.hom :=
  (forget L R P Q W).map_isIso f

/--
lemma `hom_homFromCommaOfIsIso` / 引理 `hom_homFromCommaOfIsIso`

English:
lemma hom_homFromCommaOfIsIso
  statement: [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
  proof: rfl

中文:
引理 hom_homFromCommaOfIsIso
  结论: [Q.RespectsIso] [W.RespectsIso] {X Y : P.交换a L R Q W}
  证明: rfl
-/
lemma hom_homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X ⟶ Y) [IsIso i.hom] :
    homFromCommaOfIsIso i.hom = i :=
  rfl

/--
lemma `inv_hom` / 引理 `inv_hom`

English:
lemma inv_hom
  given: {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f]
  statement: (inv f).hom = inv f.hom
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_hom]; rw [IsIso.hom_inv_id]; rw [id_hom]

中文:
引理 inv_hom
  条件: {X Y : P.交换a L R Q W} (f : X ⟶ Y) [是同构 f]
  结论: (inv f).hom = inv f.hom
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_hom]; rw [IsIso.hom_inv_id]; rw [id_hom]

Depends on / 依赖: IsIso.eq_inv_of_hom_inv_id, IsIso.hom_inv_id, comp_hom, eq_inv_of_hom_inv_id, hom_inv_id, id_hom
-/
lemma inv_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_hom]; rw [IsIso.hom_inv_id]; rw [id_hom]

variable (L R P Q W)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.RespectsIso]
  signature: [W.RespectsIso]
  body: by
    simp only [forget_obj, forget_map] at hf
    rw [← hom_homFromCommaOfIsIso f]
    infer_instance

中文:
实例 [Q.RespectsIso]
  签名: [W.RespectsIso]
  定义体: by
    simp only [forget_obj, forget_map] at hf
    rw [← hom_homFromCommaOfIsIso f]
    infer_instance

Depends on / 依赖: forget_map, forget_obj, hom_homFromCommaOfIsIso, infer_instance
-/
instance [Q.RespectsIso] [W.RespectsIso] : (forget L R P Q W).ReflectsIsomorphisms where
  reflects f hf := by
    simp only [forget_obj, forget_map] at hf
    rw [← hom_homFromCommaOfIsIso f]
    infer_instance

/--
Definition of `forgetFullyFaithful` / `forgetFullyFaithful` 的定义

English:
definition forgetFullyFaithful
  signature: : (forget L R P ⊤ ⊤).FullyFaithful where
  body: ⟨f, trivial, trivial⟩

中文:
定义 forgetFullyFaithful
  签名: : (forget L R P ⊤ ⊤).满忠实 where
  定义体: ⟨f, trivial, trivial⟩
-/
def forgetFullyFaithful : (forget L R P ⊤ ⊤).FullyFaithful where
  preimage {X Y} f := ⟨f, trivial, trivial⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget L R P ⊤ ⊤).Full
  body: Functor.FullyFaithful.full (forgetFullyFaithful L R P)

中文:
实例 :
  签名: (forget L R P ⊤ ⊤).满
  定义体: Functor.FullyFaithful.full (forgetFullyFaithful L R P)

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.full, forgetFullyFaithful
-/
instance : (forget L R P ⊤ ⊤).Full :=
  Functor.FullyFaithful.full (forgetFullyFaithful L R P)

section

variable {L R}

@[simp]
/--
lemma `eqToHom_left` / 引理 `eqToHom_left`

English:
lemma eqToHom_left
  given: {X Y : P.Comma L R Q W} (h : X = Y)
  proof: by
  subst h
  rfl

@[simp]

中文:
引理 eqToHom_left
  条件: {X Y : P.交换a L R Q W} (h : X = Y)
  证明: by
  subst h
  rfl

@[simp]
-/
lemma eqToHom_left {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp]
/--
lemma `eqToHom_right` / 引理 `eqToHom_right`

English:
lemma eqToHom_right
  given: {X Y : P.Comma L R Q W} (h : X = Y)
  proof: by
  subst h
  rfl

中文:
引理 eqToHom_right
  条件: {X Y : P.交换a L R Q W} (h : X = Y)
  证明: by
  subst h
  rfl
-/
lemma eqToHom_right {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  rfl

end

section

variable {P P' : MorphismProperty T} {Q Q' : MorphismProperty A} {W W' : MorphismProperty B}
  (hP : P <= P') (hQ : Q <= Q') (hW : W <= W')

variable [Q.IsMultiplicative] [Q'.IsMultiplicative] [W.IsMultiplicative] [W'.IsMultiplicative]

/--
Definition of `changeProp` / `changeProp` 的定义

English:
definition changeProp
  signature: : P.Comma L R Q W ⥤ P'.Comma L R Q' W' where
  body: ⟨X.toComma, hP _ X.2⟩
  map f := ⟨f.toCommaMorphism, hQ _ f.2, hW _ f.3⟩

中文:
定义 changeProp
  签名: : P.交换a L R Q W ⥤ P'.交换a L R Q' W' where
  定义体: ⟨X.toComma, hP _ X.2⟩
  map f := ⟨f.toCommaMorphism, hQ _ f.2, hW _ f.3⟩

Depends on / 依赖: X.toComma, toComma
-/
def changeProp : P.Comma L R Q W ⥤ P'.Comma L R Q' W' where
  obj X := ⟨X.toComma, hP _ X.2⟩
  map f := ⟨f.toCommaMorphism, hQ _ f.2, hW _ f.3⟩

/--
Definition of `fullyFaithfulChangeProp` / `fullyFaithfulChangeProp` 的定义

English:
definition fullyFaithfulChangeProp
  signature: :
  body: ⟨f.toCommaMorphism, f.2, f.3⟩

中文:
定义 fullyFaithfulChangeProp
  签名: :
  定义体: ⟨f.toCommaMorphism, f.2, f.3⟩

Depends on / 依赖: FullyFaithful, le_rfl
-/
def fullyFaithfulChangeProp :
    (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, f.2, f.3⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (changeProp L R hP hQ hW).Faithful
  body: by ext : 1; exact congr($(h).hom)

中文:
实例 :
  签名: (changeProp L R hP hQ hW).忠实
  定义体: by ext : 1; exact congr($(h).hom)
-/
instance : (changeProp L R hP hQ hW).Faithful where
  map_injective {X Y} f g h := by ext : 1; exact congr($(h).hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).Full
  body: (fullyFaithfulChangeProp ..).full

中文:
实例 :
  签名: (changeProp (Q := Q) (W := W) L R hP le_rfl le_rfl).满
  定义体: (fullyFaithfulChangeProp ..).full

Depends on / 依赖: le_rfl
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
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {C : Type*} [Category* C] (F : C ⥤ Comma L R)
  body: { __ := F.obj X
      prop := hP X }
  map {X Y} f :=
    { __ := F.map f
      prop_hom_left := hQ f
      prop_hom_right := hW f }

中文:
定义 lift
  签名: {C : 类型} [范畴* C] (F : C ⥤ 交换a L R)
  定义体: { __ := F.obj X
      prop := hP X }
  map {X Y} f :=
    { __ := F.map f
      prop_hom_left := hQ f
      prop_hom_right := hW f }

Depends on / 依赖: F.map, F.obj, prop_hom_left, prop_hom_right
-/
def lift {C : Type*} [Category* C] (F : C ⥤ Comma L R)
    (hP : forall X, P (F.obj X).hom)
    (hQ : forall {X Y} (f : X ⟶ Y), Q (F.map f).left)
    (hW : forall {X Y} (f : X ⟶ Y), W (F.map f).right) :
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
/--
Definition of `mapLeft` / `mapLeft` 的定义

English:
definition mapLeft
  signature: (l : L₁ ⟶ L₂) (hl : forall X : P.Comma L₂ R Q W, P (l.app X.left ≫ X.hom))
  body: lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapLeft R l) hl
    (fun f => f.prop_hom_left) (fun f => f.prop_hom_right)

中文:
定义 mapLeft
  签名: (l : L₁ ⟶ L₂) (hl : 对任意 X : P.交换a L₂ R Q W, P (l.app X.left ≫ X.hom))
  定义体: lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapLeft R l) hl
    (fun f => f.prop_hom_left) (fun f => f.prop_hom_right)

Depends on / 依赖: CategoryTheory, CategoryTheory.Comma.mapLeft, f.prop_hom_left, f.prop_hom_right, forget, mapLeft, prop_hom_left, prop_hom_right
-/
def mapLeft (l : L₁ ⟶ L₂) (hl : forall X : P.Comma L₂ R Q W, P (l.app X.left ≫ X.hom)) :
    P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapLeft R l) hl
    (fun f => f.prop_hom_left) (fun f => f.prop_hom_right)

set_option backward.isDefEq.respectTransparency.types false in
variable (L R) in
/-- The functor `P.Comma L R Q W ⥤ P.Comma L R Q W` induced by the identity natural transformation
on `L` is naturally isomorphic to the identity functor. -/
@[simps!]
/--
Definition of `mapLeftId` / `mapLeftId` 的定义

English:
definition mapLeftId
  signature: [Q.RespectsIso] [W.RespectsIso]
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapLeftId
  签名: [Q.RespectsIso] [W.RespectsIso]
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: X.prop
-/
def mapLeftId [Q.RespectsIso] [W.RespectsIso] :
    mapLeft (P := P) (Q := Q) (W := W) R (𝟙 L) (fun X => by simpa using X.prop) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- The functor `P.Comma L₁ R Q W ⥤ P.Comma L₃ R Q W` induced by the composition of two natural
transformations `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the
two functors induced by these natural transformations. -/
@[simps!]
/--
Definition of `mapLeftComp` / `mapLeftComp` 的定义

English:
definition mapLeftComp
  signature: [Q.RespectsIso] [W.RespectsIso] (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapLeftComp
  签名: [Q.RespectsIso] [W.RespectsIso] (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
-/
def mapLeftComp [Q.RespectsIso] [W.RespectsIso] (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
    (hl : forall (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom))
    (hl' : forall (X : P.Comma L₃ R Q W), P (l'.app X.left ≫ X.hom))
    (hll' : forall (X : P.Comma L₃ R Q W), P ((l ≫ l').app X.left ≫ X.hom)) :
    mapLeft (P := P) (Q := Q) (W := W) R (l ≫ l') hll' ≅
      mapLeft R l' hl' ⋙ mapLeft R l hl :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- Two equal natural transformations `L₁ ⟶ L₂` yield naturally isomorphic functors
`P.Comma L₁ R Q W ⥤ P.Comma L₂ R Q W`. -/
@[simps!]
/--
Definition of `mapLeftEq` / `mapLeftEq` 的定义

English:
definition mapLeftEq
  signature: [Q.RespectsIso] [W.RespectsIso] (l l' : L₁ ⟶ L₂) (h : l = l')
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapLeftEq
  签名: [Q.RespectsIso] [W.RespectsIso] (l l' : L₁ ⟶ L₂) (h : l = l')
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapLeftEq [Q.RespectsIso] [W.RespectsIso] (l l' : L₁ ⟶ L₂) (h : l = l')
    (hl : forall (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom)) :
    mapLeft R l hl ≅ mapLeft R l' (h ▸ hl) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- A natural isomorphism `L₁ ≅ L₂` induces an equivalence of categories
`P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W`. -/
@[simps!]
/--
Definition of `mapLeftIso` / `mapLeftIso` 的定义

English:
definition mapLeftIso
  signature: [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
  body: Comma.mapLeft R e.inv (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapLeft R e.hom (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapLeftId _ _).symm ≪≫
    mapLeftEq _ _ _ e.hom_inv_id.symm (fun X => by simpa using X.prop) ≪≫
    mapLeftComp _ 

中文:
定义 mapLeftIso
  签名: [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
  定义体: Comma.mapLeft R e.inv (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapLeft R e.hom (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapLeftId _ _).symm ≪≫
    mapLeftEq _ _ _ e.hom_inv_id.symm (fun X => by simpa using X.prop) ≪≫
    mapLeftComp _ 

Depends on / 依赖: Comma.mapLeft, P.cancel_left_of_respectsIso, X.prop, cancel_left_of_respectsIso, e.inv, mapLeft
-/
def mapLeftIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
      (e : L₁ ≅ L₂) :
    P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W where
  functor := Comma.mapLeft R e.inv (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapLeft R e.hom (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapLeftId _ _).symm ≪≫
    mapLeftEq _ _ _ e.hom_inv_id.symm (fun X => by simpa using X.prop) ≪≫
    mapLeftComp _ _ _
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  counitIso :=
    (mapLeftComp _ _ _
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop)).symm ≪≫
    mapLeftEq _ _ _ e.inv_hom_id
      (fun X => (P.cancel_left_of_respectsIso _ _).mpr X.prop) ≪≫
    mapLeftId _ _

variable (L) in
/-- A natural transformation `R₁ ⟶ R₂` induces a functor `P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W`. -/
@[simps!]
/--
Definition of `mapRight` / `mapRight` 的定义

English:
definition mapRight
  signature: (r : R₁ ⟶ R₂) (hr : forall X : P.Comma L R₁ Q W, P (X.hom ≫ r.app X.right))
  body: lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapRight L r) hr
    (fun f => f.prop_hom_left) (fun f => f.prop_hom_right)

中文:
定义 mapRight
  签名: (r : R₁ ⟶ R₂) (hr : 对任意 X : P.交换a L R₁ Q W, P (X.hom ≫ r.app X.right))
  定义体: lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapRight L r) hr
    (fun f => f.prop_hom_left) (fun f => f.prop_hom_right)

Depends on / 依赖: CategoryTheory, CategoryTheory.Comma.mapRight, f.prop_hom_left, f.prop_hom_right, forget, mapRight, prop_hom_left, prop_hom_right
-/
def mapRight (r : R₁ ⟶ R₂) (hr : forall X : P.Comma L R₁ Q W, P (X.hom ≫ r.app X.right)) :
    P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapRight L r) hr
    (fun f => f.prop_hom_left) (fun f => f.prop_hom_right)

set_option backward.isDefEq.respectTransparency.types false in
variable (L R) in
/-- The functor `P.Comma L R Q W ⥤ P.Comma L R Q W` induced by the identity natural transformation
on `R` is naturally isomorphic to the identity functor. -/
@[simps!]
/--
Definition of `mapRightId` / `mapRightId` 的定义

English:
definition mapRightId
  signature: [Q.RespectsIso] [W.RespectsIso]
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapRightId
  签名: [Q.RespectsIso] [W.RespectsIso]
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: X.prop
-/
def mapRightId [Q.RespectsIso] [W.RespectsIso] :
    mapRight (P := P) (Q := Q) (W := W) L (𝟙 R) (fun X => by simpa using X.prop) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (L) in
/-- The functor `P.Comma L R₁ Q W ⥤ P.Comma L R₃ Q W` induced by the composition of the natural
transformations `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the
functors induced by these natural transformations. -/
@[simps!]
/--
Definition of `mapRightComp` / `mapRightComp` 的定义

English:
definition mapRightComp
  signature: [Q.RespectsIso] [W.RespectsIso] (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃)
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapRightComp
  签名: [Q.RespectsIso] [W.RespectsIso] (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃)
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))
-/
def mapRightComp [Q.RespectsIso] [W.RespectsIso] (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃)
    (hr : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right))
    (hr' : forall (X : P.Comma L R₂ Q W), P (X.hom ≫ r'.app X.right))
    (hrr' : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ (r ≫ r').app X.right)) :
    mapRight (P := P) (Q := Q) (W := W) L (r ≫ r') hrr' ≅
      mapRight L r hr ⋙ mapRight L r' hr' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (L) in
/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
`P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W`. -/
@[simps!]
/--
Definition of `mapRightEq` / `mapRightEq` 的定义

English:
definition mapRightEq
  signature: [Q.RespectsIso] [W.RespectsIso] (r r' : R₁ ⟶ R₂) (h : r = r')
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapRightEq
  签名: [Q.RespectsIso] [W.RespectsIso] (r r' : R₁ ⟶ R₂) (h : r = r')
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapRightEq [Q.RespectsIso] [W.RespectsIso] (r r' : R₁ ⟶ R₂) (h : r = r')
    (hr : forall (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right)) :
    mapRight L r hr ≅ mapRight L r' (h ▸ hr) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
variable (L) in
/-- A natural isomorphism `R₁ ≅ R₂` induces an equivalence of categories
`P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W`. -/
@[simps!]
/--
Definition of `mapRightIso` / `mapRightIso` 的定义

English:
definition mapRightIso
  signature: [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
  body: Comma.mapRight L e.hom (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapRight L e.inv (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapRightId _ _).symm ≪≫
    mapRightEq _ _ _ e.hom_inv_id.symm (fun X => by simpa using X.prop) ≪≫
    mapRight

中文:
定义 mapRightIso
  签名: [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
  定义体: Comma.mapRight L e.hom (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapRight L e.inv (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapRightId _ _).symm ≪≫
    mapRightEq _ _ _ e.hom_inv_id.symm (fun X => by simpa using X.prop) ≪≫
    mapRight

Depends on / 依赖: Comma.mapRight, P.cancel_right_of_respectsIso, X.prop, cancel_right_of_respectsIso, e.hom, mapRight
-/
def mapRightIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
      (e : R₁ ≅ R₂) :
    P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W where
  functor := Comma.mapRight L e.hom (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapRight L e.inv (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapRightId _ _).symm ≪≫
    mapRightEq _ _ _ e.hom_inv_id.symm (fun X => by simpa using X.prop) ≪≫
    mapRightComp _ _ _
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  counitIso :=
    (mapRightComp _ _ _
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop)).symm ≪≫
    mapRightEq _ _ _ e.inv_hom_id
      (fun X => (P.cancel_right_of_respectsIso _ _).mpr X.prop) ≪≫
    mapRightId _ _

end Functoriality

end Comma

end Comma

section Arrow

variable {T : Type*} [Category* T]
  (P Q W : MorphismProperty T) [Q.IsMultiplicative] [W.IsMultiplicative]

/--
Definition of `Arrow` / `Arrow` 的定义

English:
abbreviation Arrow
  signature: : Type _
  body: P.Comma (𝟭 T) (𝟭 T) Q W

中文:
缩写 箭头
  签名: : 类型 _
  定义体: P.Comma (𝟭 T) (𝟭 T) Q W
-/
protected abbrev Arrow : Type _ := P.Comma (𝟭 T) (𝟭 T) Q W

/--
Definition of `Arrow.forget` / `Arrow.forget` 的定义

English:
abbreviation Arrow.forget
  signature: : P.Arrow Q W ⥤ Arrow T
  body: Comma.forget (𝟭 T) (𝟭 T) P Q W

中文:
缩写 箭头.forget
  签名: : P.箭头 Q W ⥤ 箭头 T
  定义体: Comma.forget (𝟭 T) (𝟭 T) P Q W
-/
protected abbrev Arrow.forget : P.Arrow Q W ⥤ Arrow T := Comma.forget (𝟭 T) (𝟭 T) P Q W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Arrow.forget P Q W).Faithful
  body: inferInstanceAs (Comma.forget _ _ _ _ _).Faithful

中文:
实例 :
  签名: (箭头.forget P Q W).忠实
  定义体: inferInstanceAs (Comma.forget _ _ _ _ _).Faithful

Depends on / 依赖: Comma.forget, Faithful, forget
-/
instance : (Arrow.forget P Q W).Faithful := inferInstanceAs (Comma.forget _ _ _ _ _).Faithful
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Arrow.forget P ⊤ ⊤).Full
  body: inferInstanceAs (Comma.forget _ _ _ _ _).Full

中文:
实例 :
  签名: (箭头.forget P ⊤ ⊤).满
  定义体: inferInstanceAs (Comma.forget _ _ _ _ _).Full

Depends on / 依赖: Comma.forget, forget
-/
instance : (Arrow.forget P ⊤ ⊤).Full := inferInstanceAs (Comma.forget _ _ _ _ _).Full

/--
lemma `Arrow.forget_comp_leftFunc_map` / 引理 `Arrow.forget_comp_leftFunc_map`

English:
lemma Arrow.forget_comp_leftFunc_map
  given: {A B : P.Arrow Q W} (f : A ⟶ B)
  proof: rfl

中文:
引理 箭头.forget_comp_leftFunc_map
  条件: {A B : P.箭头 Q W} (f : A ⟶ B)
  证明: rfl
-/
lemma Arrow.forget_comp_leftFunc_map {A B : P.Arrow Q W} (f : A ⟶ B) :
    (MorphismProperty.Arrow.forget P Q W ⋙ CategoryTheory.Arrow.leftFunc).map f = f.left := rfl

/--
lemma `Arrow.forget_comp_rightFunc_map` / 引理 `Arrow.forget_comp_rightFunc_map`

English:
lemma Arrow.forget_comp_rightFunc_map
  given: {A B : P.Arrow Q W} (f : A ⟶ B)
  proof: rfl

中文:
引理 箭头.forget_comp_rightFunc_map
  条件: {A B : P.箭头 Q W} (f : A ⟶ B)
  证明: rfl
-/
lemma Arrow.forget_comp_rightFunc_map {A B : P.Arrow Q W} (f : A ⟶ B) :
    (MorphismProperty.Arrow.forget P Q W ⋙ CategoryTheory.Arrow.rightFunc).map f = f.right := rfl

variable {P Q W}

/-- Construct a morphism in `P.Arrow Q W` from a morphism in `Arrow T`. -/
@[simps hom]
/--
Definition of `Arrow.Hom.mk` / `Arrow.Hom.mk` 的定义

English:
definition Arrow.Hom.mk
  signature: {A B : P.Arrow Q W} (f : (Arrow.forget _ _ _).obj A ⟶ (Arrow.forget _ _ _).obj B)
  body: f
  prop_hom_left := hfl
  prop_hom_right := hfr

中文:
定义 箭头.态射.mk
  签名: {A B : P.箭头 Q W} (f : (箭头.forget _ _ _).obj A ⟶ (箭头.forget _ _ _).obj B)
  定义体: f
  prop_hom_left := hfl
  prop_hom_right := hfr
-/
def Arrow.Hom.mk {A B : P.Arrow Q W} (f : (Arrow.forget _ _ _).obj A ⟶ (Arrow.forget _ _ _).obj B)
    (hfl : Q f.left) (hfr : W f.right) : A ⟶ B where
  __ := f
  prop_hom_left := hfl
  prop_hom_right := hfr

/-- Make an object of `P.Arrow Q X` from a morphism `f : A ⟶ B` and a proof of `P f`. -/
@[simps hom left]
/--
Definition of `Arrow.mk` / `Arrow.mk` 的定义

English:
definition Arrow.mk
  signature: {A B : T} (f : A ⟶ B) (hf : P f)
  body: A
  right := B
  hom := f
  prop := hf

中文:
定义 箭头.mk
  签名: {A B : T} (f : A ⟶ B) (hf : P f)
  定义体: A
  right := B
  hom := f
  prop := hf
-/
protected def Arrow.mk {A B : T} (f : A ⟶ B) (hf : P f) : P.Arrow Q W where
  left := A
  right := B
  hom := f
  prop := hf

/-- Make a morphism in `P.Arrow Q X` from morphisms in `T` with compatibilities. -/
@[simps hom]
/--
Definition of `Arrow.homMk` / `Arrow.homMk` 的定义

English:
definition Arrow.homMk
  signature: {A B : P.Arrow Q W} (f : A.left ⟶ B.left) (g : A.right ⟶ B.right)
  body: CategoryTheory.Arrow.homMk f g w
  prop_hom_left := hf
  prop_hom_right := hg

中文:
定义 箭头.homMk
  签名: {A B : P.箭头 Q W} (f : A.left ⟶ B.left) (g : A.right ⟶ B.right)
  定义体: CategoryTheory.Arrow.homMk f g w
  prop_hom_left := hf
  prop_hom_right := hg
-/
protected def Arrow.homMk {A B : P.Arrow Q W} (f : A.left ⟶ B.left) (g : A.right ⟶ B.right)
    (w : f ≫ B.hom = A.hom ≫ g := by cat_disch)
    (hf : Q f := by trivial) (hg : W g := by trivial) : A ⟶ B where
  __ := CategoryTheory.Arrow.homMk f g w
  prop_hom_left := hf
  prop_hom_right := hg

/-- Make an isomorphism in `P.Arrow Q X` from isomorphisms in `T` with compatibilities. -/
@[simps! hom_left inv_left]
/--
Definition of `Arrow.isoMk` / `Arrow.isoMk` 的定义

English:
definition Arrow.isoMk
  signature: [Q.RespectsIso] [W.RespectsIso] {A B : P.Arrow Q W}
  body: Comma.isoMk f g

@[ext]

中文:
定义 箭头.isoMk
  签名: [Q.RespectsIso] [W.RespectsIso] {A B : P.箭头 Q W}
  定义体: Comma.isoMk f g

@[ext]
-/
protected def Arrow.isoMk [Q.RespectsIso] [W.RespectsIso] {A B : P.Arrow Q W}
    (f : A.left ≅ B.left) (g : A.right ≅ B.right)
    (w : f.hom ≫ B.hom = A.hom ≫ g.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk f g

@[ext]
/--
lemma `Arrow.Hom.ext` / 引理 `Arrow.Hom.ext`

English:
lemma Arrow.Hom.ext
  statement: {A B : P.Arrow Q W} {f g : A ⟶ B}
  proof: by
  ext
  · exact hl
  · exact hr

@[reassoc]

中文:
引理 箭头.态射.ext
  结论: {A B : P.箭头 Q W} {f g : A ⟶ B}
  证明: by
  ext
  · exact hl
  · exact hr

@[reassoc]
-/
lemma Arrow.Hom.ext {A B : P.Arrow Q W} {f g : A ⟶ B}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  ext
  · exact hl
  · exact hr

@[reassoc]
/--
lemma `Arrow.w` / 引理 `Arrow.w`

English:
lemma Arrow.w
  given: {A B : P.Arrow Q W} (f : A ⟶ B)
  proof: f.w

中文:
引理 箭头.w
  条件: {A B : P.箭头 Q W} (f : A ⟶ B)
  证明: f.w
-/
lemma Arrow.w {A B : P.Arrow Q W} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom ≫ f.right := f.w

section

variable {P' Q' W' : MorphismProperty T} [Q'.IsMultiplicative] [W'.IsMultiplicative]
    (hPP' : P <= P') (hQQ' : Q <= Q')

/--
Definition of `Arrow.changeProp` / `Arrow.changeProp` 的定义

English:
abbreviation Arrow.changeProp
  signature: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W')
  body: Comma.changeProp _ _ hPP' hQQ' hWW'

中文:
缩写 箭头.changeProp
  签名: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W')
  定义体: Comma.changeProp _ _ hPP' hQQ' hWW'

Depends on / 依赖: Comma.changeProp, changeProp
-/
abbrev Arrow.changeProp (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') :
    P.Arrow Q W ⥤ P'.Arrow Q' W' :=
  Comma.changeProp _ _ hPP' hQQ' hWW'

-- `simps` on `Arrow.changeProp` fails to create this lemma
@[simp]
/--
lemma `Arrow.changeProp_obj_left` / 引理 `Arrow.changeProp_obj_left`

English:
lemma Arrow.changeProp_obj_left
  given: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.Arrow Q W)
  proof: rfl

中文:
引理 箭头.changeProp_obj_left
  条件: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.箭头 Q W)
  证明: rfl
-/
lemma Arrow.changeProp_obj_left (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.Arrow Q W) :
    ((changeProp hPP' hQQ' hWW').obj Y).left = Y.left := rfl

-- `simps` on `Arrow.changeProp` fails to create this lemma
@[simp]
/--
lemma `Arrow.changeProp_obj_right` / 引理 `Arrow.changeProp_obj_right`

English:
lemma Arrow.changeProp_obj_right
  given: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.Arrow Q W)
  proof: rfl

中文:
引理 箭头.changeProp_obj_right
  条件: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.箭头 Q W)
  证明: rfl
-/
lemma Arrow.changeProp_obj_right (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.Arrow Q W) :
    ((changeProp hPP' hQQ' hWW').obj Y).right = Y.right := rfl

-- `simps` on `Arrow.changeProp` fails to create this lemma
@[simp]
/--
lemma `Arrow.changeProp_obj_hom` / 引理 `Arrow.changeProp_obj_hom`

English:
lemma Arrow.changeProp_obj_hom
  given: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.Arrow Q W)
  proof: rfl

中文:
引理 箭头.changeProp_obj_hom
  条件: (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.箭头 Q W)
  证明: rfl
-/
lemma Arrow.changeProp_obj_hom (hPP' : P <= P') (hQQ' : Q <= Q') (hWW' : W <= W') (Y : P.Arrow Q W) :
    ((changeProp hPP' hQQ' hWW').obj Y).hom = Y.hom := rfl

end

end Arrow

section Over

variable {T : Type*} [Category* T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

/--
Definition of `Over` / `Over` 的定义

English:
abbreviation Over
  signature: : Type _
  body: P.Comma (Functor.id T) (Functor.fromPUnit.{0} X) Q ⊤

中文:
缩写 Over
  签名: : 类型 _
  定义体: P.Comma (Functor.id T) (Functor.fromPUnit.{0} X) Q ⊤
-/
protected abbrev Over : Type _ :=
  P.Comma (Functor.id T) (Functor.fromPUnit.{0} X) Q ⊤

/--
Definition of `Over.forget` / `Over.forget` 的定义

English:
abbreviation Over.forget
  signature: : P.Over Q X ⥤ Over X
  body: Comma.forget (Functor.id T) (Functor.fromPUnit.{0} X) P Q ⊤

中文:
缩写 Over.forget
  签名: : P.Over Q X ⥤ Over X
  定义体: Comma.forget (Functor.id T) (Functor.fromPUnit.{0} X) P Q ⊤
-/
protected abbrev Over.forget : P.Over Q X ⥤ Over X :=
  Comma.forget (Functor.id T) (Functor.fromPUnit.{0} X) P Q ⊤

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Over.forget P Q X).Faithful
  body: inferInstanceAs (Comma.forget _ _ _ _ _).Faithful

中文:
实例 :
  签名: (Over.forget P Q X).忠实
  定义体: inferInstanceAs (Comma.forget _ _ _ _ _).Faithful

Depends on / 依赖: Comma.forget, Faithful, forget
-/
instance : (Over.forget P Q X).Faithful := inferInstanceAs (Comma.forget _ _ _ _ _).Faithful
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Over.forget P ⊤ X).Full
  body: inferInstanceAs (Comma.forget _ _ _ _ _).Full

中文:
实例 :
  签名: (Over.forget P ⊤ X).满
  定义体: inferInstanceAs (Comma.forget _ _ _ _ _).Full

Depends on / 依赖: Comma.forget, forget
-/
instance : (Over.forget P ⊤ X).Full := inferInstanceAs (Comma.forget _ _ _ _ _).Full

/--
lemma `Over.forget_comp_forget_map` / 引理 `Over.forget_comp_forget_map`

English:
lemma Over.forget_comp_forget_map
  given: {A B : P.Over Q X} (f : A ⟶ B)
  proof: rfl

中文:
引理 Over.forget_comp_forget_map
  条件: {A B : P.Over Q X} (f : A ⟶ B)
  证明: rfl
-/
lemma Over.forget_comp_forget_map {A B : P.Over Q X} (f : A ⟶ B) :
    (MorphismProperty.Over.forget P Q X ⋙ CategoryTheory.Over.forget X).map f = f.left := rfl

variable {P Q X}

/-- Construct a morphism in `P.Over Q X` from a morphism in `Over X`. -/
@[simps hom]
/--
Definition of `Over.Hom.mk` / `Over.Hom.mk` 的定义

English:
definition Over.Hom.mk
  signature: {A B : P.Over Q X}
  body: f
  prop_hom_left := hf
  prop_hom_right := trivial

中文:
定义 Over.态射.mk
  签名: {A B : P.Over Q X}
  定义体: f
  prop_hom_left := hf
  prop_hom_right := trivial
-/
def Over.Hom.mk {A B : P.Over Q X}
    (f : (Over.forget _ _ _).obj A ⟶ (Over.forget _ _ _).obj B) (hf : Q f.left) : A ⟶ B where
  __ := f
  prop_hom_left := hf
  prop_hom_right := trivial

variable (Q) in
/-- Make an object of `P.Over Q X` from a morphism `f : A ⟶ X` and a proof of `P f`. -/
@[simps hom left]
/--
Definition of `Over.mk` / `Over.mk` 的定义

English:
definition Over.mk
  signature: {A : T} (f : A ⟶ X) (hf : P f)
  body: A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

中文:
定义 Over.mk
  签名: {A : T} (f : A ⟶ X) (hf : P f)
  定义体: A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf
-/
protected def Over.mk {A : T} (f : A ⟶ X) (hf : P f) : P.Over Q X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

/-- Make a morphism in `P.Over Q X` from a morphism in `T` with compatibilities. -/
@[simps hom]
/--
Definition of `Over.homMk` / `Over.homMk` 的定义

English:
definition Over.homMk
  signature: {A B : P.Over Q X} (f : A.left ⟶ B.left)
  body: CategoryTheory.Over.homMk f w
  prop_hom_left := hf
  prop_hom_right := trivial

中文:
定义 Over.homMk
  签名: {A B : P.Over Q X} (f : A.left ⟶ B.left)
  定义体: CategoryTheory.Over.homMk f w
  prop_hom_left := hf
  prop_hom_right := trivial
-/
protected def Over.homMk {A B : P.Over Q X} (f : A.left ⟶ B.left)
    (w : f ≫ B.hom = A.hom := by cat_disch) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Over.homMk f w
  prop_hom_left := hf
  prop_hom_right := trivial

/-- Make an isomorphism in `P.Over Q X` from an isomorphism in `T` with compatibilities. -/
@[simps! hom_left inv_left]
/--
Definition of `Over.isoMk` / `Over.isoMk` 的定义

English:
definition Over.isoMk
  signature: [Q.RespectsIso] {A B : P.Over Q X} (f : A.left ≅ B.left)
  body: Comma.isoMk f (Discrete.eqToIso' rfl)

中文:
定义 Over.isoMk
  签名: [Q.RespectsIso] {A B : P.Over Q X} (f : A.left ≅ B.left)
  定义体: Comma.isoMk f (Discrete.eqToIso' rfl)
-/
protected def Over.isoMk [Q.RespectsIso] {A B : P.Over Q X} (f : A.left ≅ B.left)
    (w : f.hom ≫ B.hom = A.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk f (Discrete.eqToIso' rfl)

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/--
lemma `Over.Hom.ext` / 引理 `Over.Hom.ext`

English:
lemma Over.Hom.ext
  given: {A B : P.Over Q X} {f g : A ⟶ B} (h : f.left = g.left)
  statement: f = g
  proof: by
  ext
  · exact h
  · simp

中文:
引理 Over.态射.ext
  条件: {A B : P.Over Q X} {f g : A ⟶ B} (h : f.left = g.left)
  结论: f = g
  证明: by
  ext
  · exact h
  · simp
-/
lemma Over.Hom.ext {A B : P.Over Q X} {f g : A ⟶ B} (h : f.left = g.left) : f = g := by
  ext
  · exact h
  · simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Over.w` / 引理 `Over.w`

English:
lemma Over.w
  given: {A B : P.Over Q X} (f : A ⟶ B)
  proof: by
  simp

中文:
引理 Over.w
  条件: {A B : P.Over Q X} (f : A ⟶ B)
  证明: by
  simp
-/
lemma Over.w {A B : P.Over Q X} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom := by
  simp

section

variable {P' Q' : MorphismProperty T} [Q'.IsMultiplicative] (hPP' : P <= P') (hQQ' : Q <= Q')

variable (X) in
/--
Definition of `Over.changeProp` / `Over.changeProp` 的定义

English:
abbreviation Over.changeProp
  signature: (hPP' : P <= P') (hQQ' : Q <= Q')
  body: Comma.changeProp _ _ hPP' hQQ' le_rfl

@[simp]

中文:
缩写 Over.changeProp
  签名: (hPP' : P <= P') (hQQ' : Q <= Q')
  定义体: Comma.changeProp _ _ hPP' hQQ' le_rfl

@[simp]

Depends on / 依赖: Comma.changeProp, changeProp, le_rfl
-/
abbrev Over.changeProp (hPP' : P <= P') (hQQ' : Q <= Q') :
    P.Over Q X ⥤ P'.Over Q' X :=
  Comma.changeProp _ _ hPP' hQQ' le_rfl

@[simp]
/--
lemma `Over.changeProp_obj_left` / 引理 `Over.changeProp_obj_left`

English:
lemma Over.changeProp_obj_left
  given: (hPP' : P <= P') (hQQ' : Q <= Q') (Y : P.Over Q X)
  proof: rfl

@[simp]

中文:
引理 Over.changeProp_obj_left
  条件: (hPP' : P <= P') (hQQ' : Q <= Q') (Y : P.Over Q X)
  证明: rfl

@[simp]
-/
lemma Over.changeProp_obj_left (hPP' : P <= P') (hQQ' : Q <= Q') (Y : P.Over Q X) :
    ((changeProp X hPP' hQQ').obj Y).left = Y.left := rfl

@[simp]
/--
lemma `Over.changeProp_obj_hom` / 引理 `Over.changeProp_obj_hom`

English:
lemma Over.changeProp_obj_hom
  given: (hPP' : P <= P') (hQQ' : Q <= Q') (Y : P.Over Q X)
  proof: rfl

中文:
引理 Over.changeProp_obj_hom
  条件: (hPP' : P <= P') (hQQ' : Q <= Q') (Y : P.Over Q X)
  证明: rfl
-/
lemma Over.changeProp_obj_hom (hPP' : P <= P') (hQQ' : Q <= Q') (Y : P.Over Q X) :
    ((changeProp X hPP' hQQ').obj Y).hom = Y.hom := rfl

end

end Over

section Under

variable {T : Type*} [Category* T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

/--
Definition of `Under` / `Under` 的定义

English:
abbreviation Under
  signature: : Type _
  body: P.Comma (Functor.fromPUnit.{0} X) (Functor.id T) ⊤ Q

中文:
缩写 Under
  签名: : 类型 _
  定义体: P.Comma (Functor.fromPUnit.{0} X) (Functor.id T) ⊤ Q
-/
protected abbrev Under : Type _ :=
  P.Comma (Functor.fromPUnit.{0} X) (Functor.id T) ⊤ Q

/--
Definition of `Under.forget` / `Under.forget` 的定义

English:
abbreviation Under.forget
  signature: : P.Under Q X ⥤ Under X
  body: Comma.forget (Functor.fromPUnit.{0} X) (Functor.id T) P ⊤ Q

中文:
缩写 Under.forget
  签名: : P.Under Q X ⥤ Under X
  定义体: Comma.forget (Functor.fromPUnit.{0} X) (Functor.id T) P ⊤ Q
-/
protected abbrev Under.forget : P.Under Q X ⥤ Under X :=
  Comma.forget (Functor.fromPUnit.{0} X) (Functor.id T) P ⊤ Q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Under.forget P Q X).Faithful
  body: inferInstanceAs (Comma.forget _ _ _ _ _).Faithful

中文:
实例 :
  签名: (Under.forget P Q X).忠实
  定义体: inferInstanceAs (Comma.forget _ _ _ _ _).Faithful

Depends on / 依赖: Comma.forget, Faithful, forget
-/
instance : (Under.forget P Q X).Faithful := inferInstanceAs (Comma.forget _ _ _ _ _).Faithful
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Under.forget P ⊤ X).Full
  body: inferInstanceAs (Comma.forget _ _ _ _ _).Full

中文:
实例 :
  签名: (Under.forget P ⊤ X).满
  定义体: inferInstanceAs (Comma.forget _ _ _ _ _).Full

Depends on / 依赖: Comma.forget, forget
-/
instance : (Under.forget P ⊤ X).Full := inferInstanceAs (Comma.forget _ _ _ _ _).Full

/--
lemma `Under.forget_comp_forget_map` / 引理 `Under.forget_comp_forget_map`

English:
lemma Under.forget_comp_forget_map
  given: {A B : P.Under Q X} (f : A ⟶ B)
  proof: rfl

中文:
引理 Under.forget_comp_forget_map
  条件: {A B : P.Under Q X} (f : A ⟶ B)
  证明: rfl
-/
lemma Under.forget_comp_forget_map {A B : P.Under Q X} (f : A ⟶ B) :
    (MorphismProperty.Under.forget P Q X ⋙ CategoryTheory.Under.forget X).map f = f.right := rfl

variable {P Q X}

/-- Construct a morphism in `P.Under Q X` from a morphism in `Under X`. -/
@[simps hom]
/--
Definition of `Under.Hom.mk` / `Under.Hom.mk` 的定义

English:
definition Under.Hom.mk
  signature: {A B : P.Under Q X}
  body: f
  prop_hom_left := trivial
  prop_hom_right := hf

中文:
定义 Under.态射.mk
  签名: {A B : P.Under Q X}
  定义体: f
  prop_hom_left := trivial
  prop_hom_right := hf
-/
def Under.Hom.mk {A B : P.Under Q X}
    (f : (Under.forget _ _ _).obj A ⟶ (Under.forget _ _ _).obj B) (hf : Q f.right) : A ⟶ B where
  __ := f
  prop_hom_left := trivial
  prop_hom_right := hf

variable (Q) in
/-- Make an object of `P.Under Q X` from a morphism `f : A ⟶ X` and a proof of `P f`. -/
@[simps hom left]
/--
Definition of `Under.mk` / `Under.mk` 的定义

English:
definition Under.mk
  signature: {A : T} (f : X ⟶ A) (hf : P f)
  body: ⟨⟨⟩⟩
  right := A
  hom := f
  prop := hf

中文:
定义 Under.mk
  签名: {A : T} (f : X ⟶ A) (hf : P f)
  定义体: ⟨⟨⟩⟩
  right := A
  hom := f
  prop := hf
-/
protected def Under.mk {A : T} (f : X ⟶ A) (hf : P f) : P.Under Q X where
  left := ⟨⟨⟩⟩
  right := A
  hom := f
  prop := hf

/-- Make a morphism in `P.Under Q X` from a morphism in `T` with compatibilities. -/
@[simps hom]
/--
Definition of `Under.homMk` / `Under.homMk` 的定义

English:
definition Under.homMk
  signature: {A B : P.Under Q X} (f : A.right ⟶ B.right)
  body: CategoryTheory.Under.homMk f w
  prop_hom_left := trivial
  prop_hom_right := hf

中文:
定义 Under.homMk
  签名: {A B : P.Under Q X} (f : A.right ⟶ B.right)
  定义体: CategoryTheory.Under.homMk f w
  prop_hom_left := trivial
  prop_hom_right := hf
-/
protected def Under.homMk {A B : P.Under Q X} (f : A.right ⟶ B.right)
    (w : A.hom ≫ f = B.hom := by cat_disch) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Under.homMk f w
  prop_hom_left := trivial
  prop_hom_right := hf

/-- Make an isomorphism in `P.Under Q X` from an isomorphism in `T` with compatibilities. -/
@[simps! hom_right inv_right]
/--
Definition of `Under.isoMk` / `Under.isoMk` 的定义

English:
definition Under.isoMk
  signature: [Q.RespectsIso] {A B : P.Under Q X} (f : A.right ≅ B.right)
  body: Comma.isoMk (Discrete.eqToIso' rfl) f

中文:
定义 Under.isoMk
  签名: [Q.RespectsIso] {A B : P.Under Q X} (f : A.right ≅ B.right)
  定义体: Comma.isoMk (Discrete.eqToIso' rfl) f
-/
protected def Under.isoMk [Q.RespectsIso] {A B : P.Under Q X} (f : A.right ≅ B.right)
    (w : A.hom ≫ f.hom = B.hom := by cat_disch) : A ≅ B :=
  Comma.isoMk (Discrete.eqToIso' rfl) f

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/--
lemma `Under.Hom.ext` / 引理 `Under.Hom.ext`

English:
lemma Under.Hom.ext
  given: {A B : P.Under Q X} {f g : A ⟶ B} (h : f.right = g.right)
  statement: f = g
  proof: by
  ext
  · simp
  · exact h

中文:
引理 Under.态射.ext
  条件: {A B : P.Under Q X} {f g : A ⟶ B} (h : f.right = g.right)
  结论: f = g
  证明: by
  ext
  · simp
  · exact h
-/
lemma Under.Hom.ext {A B : P.Under Q X} {f g : A ⟶ B} (h : f.right = g.right) : f = g := by
  ext
  · simp
  · exact h

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `Under.w` / 引理 `Under.w`

English:
lemma Under.w
  given: {A B : P.Under Q X} (f : A ⟶ B)
  proof: by
  simp

中文:
引理 Under.w
  条件: {A B : P.Under Q X} (f : A ⟶ B)
  证明: by
  simp
-/
lemma Under.w {A B : P.Under Q X} (f : A ⟶ B) :
    A.hom ≫ f.right = B.hom := by
  simp

end Under

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

/--
Definition of `CostructuredArrow` / `CostructuredArrow` 的定义

English:
abbreviation CostructuredArrow
  signature: (P : MorphismProperty D) (Q : MorphismProperty C)
  body: P.Comma F (Functor.fromPUnit.{0} X) Q ⊤

中文:
缩写 CostructuredArrow
  签名: (P : MorphismProperty D) (Q : MorphismProperty C)
  定义体: P.Comma F (Functor.fromPUnit.{0} X) Q ⊤
-/
protected abbrev CostructuredArrow (P : MorphismProperty D) (Q : MorphismProperty C)
    (F : C ⥤ D) (X : D) :=
  P.Comma F (Functor.fromPUnit.{0} X) Q ⊤

section CostructuredArrow

variable {P F X} in
/-- Construct an object of `P.CostructuredArrow Q F X` from a morphism `F.obj A ⟶ X`. -/
@[simps left hom]
/--
Definition of `CostructuredArrow.mk` / `CostructuredArrow.mk` 的定义

English:
definition CostructuredArrow.mk
  signature: {A : C} (f : F.obj A ⟶ X) (hf : P f)
  body: A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

中文:
定义 CostructuredArrow.mk
  签名: {A : C} (f : F.obj A ⟶ X) (hf : P f)
  定义体: A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf
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
/--
Definition of `CostructuredArrow.homMk` / `CostructuredArrow.homMk` 的定义

English:
definition CostructuredArrow.homMk
  signature: {A B : P.CostructuredArrow Q F X} (f : A.left ⟶ B.left) (hf : Q f)
  body: f
  right := eqToHom (Subsingleton.elim _ _)
  prop_hom_left := hf
  prop_hom_right := trivial

中文:
定义 CostructuredArrow.homMk
  签名: {A B : P.CostructuredArrow Q F X} (f : A.left ⟶ B.left) (hf : Q f)
  定义体: f
  right := eqToHom (Subsingleton.elim _ _)
  prop_hom_left := hf
  prop_hom_right := trivial

Depends on / 依赖: Subsingleton, Subsingleton.elim, cat_disch, eqToHom, prop_hom_left, prop_hom_right
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
/--
lemma `CostructuredArrow.Hom.ext` / 引理 `CostructuredArrow.Hom.ext`

English:
lemma CostructuredArrow.Hom.ext
  statement: {A B : P.CostructuredArrow Q F X} {f g : A ⟶ B}
  proof: by
  ext <;> simp [h]

中文:
引理 CostructuredArrow.态射.ext
  结论: {A B : P.CostructuredArrow Q F X} {f g : A ⟶ B}
  证明: by
  ext <;> simp [h]
-/
lemma CostructuredArrow.Hom.ext {A B : P.CostructuredArrow Q F X} {f g : A ⟶ B}
    (h : f.left = g.left) : f = g := by
  ext <;> simp [h]

variable {P Q F X} in
/-- Construct an isomorphism in `P.CostructuredArrow Q F X` by giving the isomorphism
on the underlying objects of `C`. -/
@[simps]
/--
Definition of `CostructuredArrow.isoMk` / `CostructuredArrow.isoMk` 的定义

English:
definition CostructuredArrow.isoMk
  signature: {A B : P.CostructuredArrow Q F X} (f : A.left ≅ B.left) (hf : Q f.hom)
  body: MorphismProperty.CostructuredArrow.homMk _ hf
  inv := MorphismProperty.CostructuredArrow.homMk _ hf' (by simp [← w])

中文:
定义 CostructuredArrow.isoMk
  签名: {A B : P.CostructuredArrow Q F X} (f : A.left ≅ B.left) (hf : Q f.hom)
  定义体: MorphismProperty.CostructuredArrow.homMk _ hf
  inv := MorphismProperty.CostructuredArrow.homMk _ hf' (by simp [← w])

Depends on / 依赖: CostructuredArrow, MorphismProperty, MorphismProperty.CostructuredArrow.homMk, cat_disch
-/
def CostructuredArrow.isoMk {A B : P.CostructuredArrow Q F X} (f : A.left ≅ B.left) (hf : Q f.hom)
    (hf' : Q f.inv)
    (w : F.map f.hom ≫ B.hom = A.hom := by cat_disch) :
    A ≅ B where
  hom := MorphismProperty.CostructuredArrow.homMk _ hf
  inv := MorphismProperty.CostructuredArrow.homMk _ hf' (by simp [← w])

/--
Definition of `CostructuredArrow.forget` / `CostructuredArrow.forget` 的定义

English:
abbreviation CostructuredArrow.forget
  signature: :
  body: Comma.forget _ _ _ _ _

中文:
缩写 CostructuredArrow.forget
  签名: :
  定义体: Comma.forget _ _ _ _ _
-/
protected abbrev CostructuredArrow.forget :
    P.CostructuredArrow Q F X ⥤ CostructuredArrow F X :=
  Comma.forget _ _ _ _ _

/-- Reinterpreting an `F`-costructured arrow `F.obj A ⟶ X` as an arrow over `X`. -/
@[simps]
/--
Definition of `CostructuredArrow.toOver` / `CostructuredArrow.toOver` 的定义

English:
definition CostructuredArrow.toOver
  signature: : P.CostructuredArrow ⊤ F X ⥤ P.Over ⊤ X where
  body: Over.mk _ A.hom A.prop
  map f := Over.homMk (F.map f.left) _

中文:
定义 CostructuredArrow.toOver
  签名: : P.CostructuredArrow ⊤ F X ⥤ P.Over ⊤ X where
  定义体: Over.mk _ A.hom A.prop
  map f := Over.homMk (F.map f.left) _
-/
protected def CostructuredArrow.toOver : P.CostructuredArrow ⊤ F X ⥤ P.Over ⊤ X where
  obj A := Over.mk _ A.hom A.prop
  map f := Over.homMk (F.map f.left) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : (CostructuredArrow.toOver P F X).Faithful
  body: by
  constructor
  intro A B f g hfg
  ext
  exact F.map_injective congr($(hfg).left)

中文:
实例 [F.忠实]
  签名: : (CostructuredArrow.toOver P F X).忠实
  定义体: by
  constructor
  intro A B f g hfg
  ext
  exact F.map_injective congr($(hfg).left)

Depends on / 依赖: F.map_injective, map_injective
-/
instance [F.Faithful] : (CostructuredArrow.toOver P F X).Faithful := by
  constructor
  intro A B f g hfg
  ext
  exact F.map_injective congr($(hfg).left)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Full]
  signature: : (CostructuredArrow.toOver P F X).Full
  body: by
  constructor
  intro A B f
  refine ⟨CostructuredArrow.homMk (F.preimage f.left) trivial ?_, ?_⟩
  · simpa using f.w
  · ext; simp

中文:
实例 [F.满]
  签名: : (CostructuredArrow.toOver P F X).满
  定义体: by
  constructor
  intro A B f
  refine ⟨CostructuredArrow.homMk (F.preimage f.left) trivial ?_, ?_⟩
  · simpa using f.w
  · ext; simp

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, F.preimage, f.left, preimage
-/
instance [F.Full] : (CostructuredArrow.toOver P F X).Full := by
  constructor
  intro A B f
  refine ⟨CostructuredArrow.homMk (F.preimage f.left) trivial ?_, ?_⟩
  · simpa using f.w
  · ext; simp

end CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `HasFactorization.over` / 实例 `HasFactorization.over`

English:
instance HasFactorization.over
  body: by
    let hf := W₁.factorizationData W₂ f.left
    exact ⟨{
      Z := .mk (hf.p ≫ Y.hom)
      i := CategoryTheory.Over.homMk hf.i
      p := CategoryTheory.Over.homMk hf.p
      hi := hf.hi
      hp := hf.hp
    }⟩

中文:
实例 有分解.over
  定义体: by
    let hf := W₁.factorizationData W₂ f.left
    exact ⟨{
      Z := .mk (hf.p ≫ Y.hom)
      i := CategoryTheory.Over.homMk hf.i
      p := CategoryTheory.Over.homMk hf.p
      hi := hf.hi
      hp := hf.hp
    }⟩

Depends on / 依赖: HasFactorization
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
