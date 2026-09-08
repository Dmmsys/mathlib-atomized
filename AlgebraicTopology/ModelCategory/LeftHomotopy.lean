/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Left homotopies in model categories

We introduce the types `Precylinder.LeftHomotopy` and `Cylinder.LeftHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)cylinder of `X`.
Given two morphisms `f` and `g`, we introduce the relation `LeftHomotopyRel f g`
asserting the existence of a cylinder object `P` and
a left homotopy `P.LeftHomotopy f g`, and we define the quotient
type `LeftHomotopyClass X Y`. We show that if `X` is a cofibrant
object in a model category, then `LeftHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace Precylinder

variable {X : C} (P : Precylinder X) {Y : C}

/-- Given a precylinder `P` for `X`, two maps `f` and `g` in `X ⟶ Y` are
homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`. -/
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy** 是 Mathlib 中的一个结构，位于命名空间 `Homotop
icalAlgebra.Precylinder`。
形式化陈述：LeftHomotopy (f g : X ⟶ Y) where /-- a morphism from the (pre)cylinder obj
ect to the target -/ h : P.I ⟶ Y h₀ : P.i₀ ≫ h = f
参数：f g : X ⟶ Y；pre。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a precylinder `P` for `X`, two maps `f` and `g` in `X ⟶ Y` are
homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`.
-/
structure LeftHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the (pre)cylinder object to the target -/
  h : P.I ⟶ Y
  h₀ : P.i₀ ≫ h = f := by cat_disch
  h₁ : P.i₁ ≫ h = g := by cat_disch

namespace LeftHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

/-- `f : X ⟶ Y` is left homotopic to itself relative to any precylinder. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：refl (f : X ⟶ Y) : P.LeftHomotopy f f where h
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X ⟶ Y` is left homotopic to itself relative to any precylinder.
-/
def refl (f : X ⟶ Y) : P.LeftHomotopy f f where
  h := P.π ≫ f

variable {P}

set_option backward.defeqAttrib.useBackward true in
/-- If `f` and `g` are homotopic relative to a precylinder `P`, then `g` and `f`
are homotopic relative to `P.symm` -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f wher
e h
参数：h : P.LeftHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are homotopic relative to a precylinder `P`, then `g` and `f`
are homotopic relative to `P.symm`
-/
def symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f where
  h := h.h

set_option backward.isDefEq.respectTransparency false in
/-- If `f₀` is homotopic to `f₁` relative to a precylinder `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `H
omotopicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：trans {f₀ f₁ f₂ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) {P' : Precylinder X} (
h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] : (P.trans P').LeftHomotopy 
f₀ f₂ where h
参数：h : P.LeftHomotopy f₀ f₁；h' : P'.LeftHomotopy f₁ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f₀` is homotopic to `f₁` relative to a precylinder `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`.
-/
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.LeftHomotopy f₀ f₁) {P' : Precylinder X}
    (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] :
    (P.trans P').LeftHomotopy f₀ f₂ where
  h := pushout.desc h.h h'.h (by simp)

/-- Left homotopies are compatible with postcomposition. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.postcomp** 是 Mathlib 中的一个定义，位于命名空间
 `HomotopicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) : P.Le
ftHomotopy (f ≫ p) (g ≫ p) where h
参数：h : P.LeftHomotopy f g；p : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopies are compatible with postcomposition.
-/
def postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) where
  h := h.h ≫ p

set_option backward.defeqAttrib.useBackward true in
/-- Left homotopies in a full subcategory identify to left homotopies in the
ambient category. -/
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.fullSubcategoryEquiv** 是 Mathlib 中
的一个定义，位于命名空间 `HomotopicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：fullSubcategoryEquiv {P : ObjectProperty C} {X Y : P.FullSubcategory} {Q :
 Precylinder X} {f g : X ⟶ Y} : Q.LeftHomotopy f g ≃ (Q.map P.ι).LeftHomotopy f.
hom g.hom where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopies in a full subcategory identify to left homotopies in the
ambient category.
-/
noncomputable def fullSubcategoryEquiv {P : ObjectProperty C} {X Y : P.FullSubcategory}
    {Q : Precylinder X} {f g : X ⟶ Y} :
    Q.LeftHomotopy f g ≃ (Q.map P.ι).LeftHomotopy f.hom g.hom where
  toFun h :=
    { h := h.h.hom
      h₀ := by
        dsimp
        simp only [← h.h₀, ObjectProperty.FullSubcategory.comp_hom]
      h₁ := by
        dsimp
        simp only [← h.h₁, ObjectProperty.FullSubcategory.comp_hom] }
  invFun h :=
    { h := P.homMk h.h
      h₀ := by ext; exact h.h₀
      h₁ := by ext; exact h.h₁ }

end LeftHomotopy

end Precylinder

namespace Cylinder

variable {X Y : C}

/-- Given a cylinder `P` for `X`, two maps `f` and `g` in `X ⟶ Y`
are homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`. -/
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopi
calAlgebra.Cylinder`。
形式化陈述：LeftHomotopy [CategoryWithWeakEquivalences C] (P : Cylinder X) (f g : X ⟶ 
Y) : Type v
参数：P : Cylinder X；f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cylinder `P` for `X`, two maps `f` and `g` in `X ⟶ Y`
are homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`.
-/
abbrev LeftHomotopy [CategoryWithWeakEquivalences C] (P : Cylinder X) (f g : X ⟶ Y) : Type v :=
  P.toPrecylinder.LeftHomotopy f g

namespace LeftHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : Cylinder X)

/-- `f : X ⟶ Y` is left homotopic to itself relative to any cylinder. -/
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.refl** 是 Mathlib 中的一个缩写定义，位于命名空间 `Hom
otopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：refl (f : X ⟶ Y) : P.LeftHomotopy f f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X ⟶ Y` is left homotopic to itself relative to any cylinder.
-/
abbrev refl (f : X ⟶ Y) : P.LeftHomotopy f f := Precylinder.LeftHomotopy.refl _ f

variable {P} in
/-- If `f` and `g` are homotopic relative to a cylinder `P`, then `g` and `f`
are homotopic relative to `P.symm`. -/
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.symm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Hom
otopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f
参数：h : P.LeftHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are homotopic relative to a cylinder `P`, then `g` and `f`
are homotopic relative to `P.symm`.
-/
abbrev symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f :=
  Precylinder.LeftHomotopy.symm h

variable {P} in
/-- Left homotopies are compatible with postcomposition. -/
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.postcomp** 是 Mathlib 中的一个缩写定义，位于命名空间 
`HomotopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) : P.Le
ftHomotopy (f ≫ p) (g ≫ p)
参数：h : P.LeftHomotopy f g；p : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopies are compatible with postcomposition.
-/
abbrev postcomp {f g : X ⟶ Y} (h : P.LeftHomotopy f g) {Z : C} (p : Y ⟶ Z) :
    P.LeftHomotopy (f ≫ p) (g ≫ p) :=
  Precylinder.LeftHomotopy.postcomp h p
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.weakEquivalence_iff** 是 Mathlib 中的一个引
理，位于命名空间 `HomotopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty] [(weak
Equivalences C).ContainsIdentities] {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) :
 WeakEquivalence f₀ ↔ WeakEquivalence f₁
参数：weakEquivalences C；weakEquivalences C；h : P.LeftHomotopy f₀ f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [(weakEquivalences C).ContainsIdentities]
    {f₀ f₁ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  induction h
  grind [weakEquivalence_precomp_iff]

end

section

variable [ModelCategory C] {P : Cylinder X}

/-- If `f₀ : X ⟶ Y` is homotopic to `f₁` relative to a cylinder `P`,
and `f₁` is homotopic to `f₂` relative to a good cylinder `P'`,
then `f₀` is homotopic to `f₂` relative to the cylinder `P.trans P'`
when `X` is cofibrant. -/
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.trans** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ho
motopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：trans [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y} (h : P.LeftHomotopy f₀ f₁) {P' : 
Cylinder X} [P'.IsGood] (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] : (
P.trans P').LeftHomotopy f₀ f₂
参数：h : P.LeftHomotopy f₀ f₁；h' : P'.LeftHomotopy f₁ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f₀ : X ⟶ Y` is homotopic to `f₁` relative to a cylinder `P`,
and `f₁` is homotopic to `f₂` relative to a good cylinder `P'`,
then `f₀` is homotopic to `f₂` relative to the cylinder `P.trans P'`
when `X` is cofibrant.
-/
noncomputable abbrev trans [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.LeftHomotopy f₀ f₁) {P' : Cylinder X} [P'.IsGood]
    (h' : P'.LeftHomotopy f₁ f₂) [HasPushout P.i₁ P'.i₀] :
    (P.trans P').LeftHomotopy f₀ f₂ :=
  Precylinder.LeftHomotopy.trans h h'
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.exists_good_cylinder** 是 Mathlib 中的一个
引理，位于命名空间 `HomotopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：exists_good_cylinder {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : exists (P' :
 Cylinder X), P'.IsGood ∧ Nonempty (P'.LeftHomotopy f g)
参数：h : P.LeftHomotopy f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.cofibrations C).…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.M
orphismProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.Precylinder.inl_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₀_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.Precylinder.inr_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₁_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceCompOfIsStableUnderCompositionWeak
Equivalences`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : 
C} (f : X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithWeak…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalencePCofibrationsTrivialFibrations`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.Cylinder.weakEquivalence_π`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakEqu
ivalences C]   {A : C} (self : Homo…
· 使用定理 `HomotopicalAlgebra.cofibration_iff`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Catego
ryWithCofibrations C],  …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用引理 `HomotopicalAlgebra.Precylinder.inl_i`：inl_i : coprod.inl ≫ P.i = P.i₀
· 使用引理 `HomotopicalAlgebra.Precylinder.inr_i`：inr_i : coprod.inr ≫ P.i = P.i₁
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₁`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
-/
lemma exists_good_cylinder {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    ∃ (P' : Cylinder X), P'.IsGood ∧ Nonempty (P'.LeftHomotopy f g) := by
  let d := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.i
  exact
   ⟨{ I := d.Z
      i₀ := coprod.inl ≫ d.i
      i₁ := coprod.inr ≫ d.i
      π := d.p ≫ P.π }, ⟨by
        rw [cofibration_iff]
        convert! d.hi
        aesop⟩, ⟨{ h := d.p ≫ h.h }⟩⟩

/-- The covering homotopy theorem: if `p : E ⟶ B` is a fibration,
`l₀ : A ⟶ E` is a morphism, if there is a left homotopy `h` between
the composition `f₀ := l₀ ≫ p` and a morphism `f₁ : A ⟶ B`,
then there exists a morphism `l₁ : A ⟶ E` and a left homotopy `h'` from
`l₀` to `l₁` which is compatible with `h` (in particular, `l₁ ≫ p = f₁`). -/
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.covering_homotopy** 是 Mathlib 中的一个引理，
位于命名空间 `HomotopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：covering_homotopy {A E B : C} {P : Cylinder A} {f₀ f₁ : A ⟶ B} [IsCofibran
t A] [P.IsGood] (h : P.LeftHomotopy f₀ f₁) (p : E ⟶ B) [Fibration p] (l₀ : A ⟶ E
) (hl₀ : l₀ ≫ p = f₀
参数：h : P.LeftHomotopy f₀ f₁；p : E ⟶ B；l₀ : A ⟶ E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.Cylinder.instCofibrationI₀`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlgebra.CategoryW
ithWeakEquivalences C] (P : Homotop…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeCofibrations`：∀ (C : Type u) [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithW
eakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemCofibratio
nsTrivialFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.cofibrations 
C…
· 使用定理 `HomotopicalAlgebra.instIsStableUnderCobaseChangeCofibrations`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Cate
goryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.Cylinder.instWeakEquivalenceI₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlgebra.Categ
oryWithWeakEquivalences C] (P : Homotop…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeWeakEquivalencesOfIsWeakFactoriza
tionSystemTrivialCofibrationsFibrationsOfIsStableUnderRetractsOfIsStableUnderCom
position`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Hom
otopicalAlgebra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemTrivialCof
ibrationsFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.trivialCofibr
a…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm3a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.weakEquivalences…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…

--- 原说明 ---
The covering homotopy theorem: if `p : E ⟶ B` is a fibration,
`l₀ : A ⟶ E` is a morphism, if there is a left homotopy `h` between
the composition `f₀ := l₀ ≫ p` and a morphism `f₁ : A ⟶ B`,
then there exists a morphism `l₁ : A ⟶ E` and a left homotopy `h'` from
`l₀` to `l₁` which is compatible with `h` (in particular, `l₁ ≫ p = f₁`).
-/
lemma covering_homotopy {A E B : C} {P : Cylinder A} {f₀ f₁ : A ⟶ B}
    [IsCofibrant A] [P.IsGood]
    (h : P.LeftHomotopy f₀ f₁) (p : E ⟶ B) [Fibration p]
    (l₀ : A ⟶ E) (hl₀ : l₀ ≫ p = f₀ := by cat_disch) :
    ∃ (l₁ : A ⟶ E) (h' : P.LeftHomotopy l₀ l₁), h'.h ≫ p = h.h :=
  have sq : CommSq l₀ P.i₀ p h.h := { }
  ⟨P.i₁ ≫ sq.lift, { h := sq.lift }, by simp⟩

end

end LeftHomotopy

end Cylinder

/-- The left homotopy relation on morphisms in a category with weak equivalences. -/
/-
**HomotopicalAlgebra.LeftHomotopyRel** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgeb
ra`。
形式化陈述：LeftHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homotopy relation on morphisms in a category with weak equivalences.
-/
def LeftHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C :=
  fun X _ f g ↦ ∃ (P : Cylinder X), Nonempty (P.LeftHomotopy f g)
/-
**HomotopicalAlgebra.Cylinder.LeftHomotopy.leftHomotopyRel** 是 Mathlib 中的一个定理，位于
命名空间 `HomotopicalAlgebra.Cylinder.LeftHomotopy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.CategoryWithWeakEquivalences C]   {X Y : C} {f g : X ⟶ Y} {P : Homot
opicalAlgebra.Cylinder X} (h : P.LeftHomotopy f g),   HomotopicalAlgebra.LeftHom
otopyRel f g
参数：h : P.LeftHomotopy f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cylinder.LeftHomotopy.leftHomotopyRel [CategoryWithWeakEquivalences C]
    {X Y : C} {f g : X ⟶ Y}
    {P : Cylinder X} (h : P.LeftHomotopy f g) :
    LeftHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace LeftHomotopyRel

variable (C) in
/-
**HomotopicalAlgebra.LeftHomotopyRel.factorsThroughLocalization** 是 Mathlib 中的一个
引理，位于命名空间 `HomotopicalAlgebra.LeftHomotopyRel`。
形式化陈述：factorsThroughLocalization [CategoryWithWeakEquivalences C] : LeftHomotopy
Rel.FactorsThroughLocalization (weakEquivalences C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.areEqualizedByLocalization_iff`：areEqualizedByLocalizatio
n_iff [L.IsLocalization W] : AreEqualizedByLocalization W f g ↔ L.map f = L.map 
g
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用定理 `HomotopicalAlgebra.Cylinder.weakEquivalence_π`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakEqu
ivalences C]   {A : C} (self : Homo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₀_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₁_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₁`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
-/
lemma factorsThroughLocalization [CategoryWithWeakEquivalences C] :
    LeftHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.i₀ = L.map P.i₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.π (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_mono (L.map P.π), ← L.map_comp, P.i₀_π, P.i₁_π]

variable {X Y : C}
/-
**HomotopicalAlgebra.LeftHomotopyRel.refl** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra.LeftHomotopyRel`。
形式化陈述：refl [ModelCategory C] (f : X ⟶ Y) : LeftHomotopyRel f f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.Cylinder.instNonempty`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory C] {A : C}
,   Nonempty (HomotopicalAlgeb…
-/
lemma refl [ModelCategory C] (f : X ⟶ Y) : LeftHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨Cylinder.LeftHomotopy.refl _ _⟩⟩
/-
**HomotopicalAlgebra.LeftHomotopyRel.postcomp** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.LeftHomotopyRel`。
形式化陈述：postcomp [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyR
el f g) {Z : C} (p : Y ⟶ Z) : LeftHomotopyRel (f ≫ p) (g ≫ p)
参数：h : LeftHomotopyRel f g；p : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.Cylinder.LeftHomotopy.leftHomotopyRel`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Category
WithWeakEquivalences C]   {X Y : C} {f g : X ⟶…
-/
lemma postcomp [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) {Z : C} (p : Y ⟶ Z) :
    LeftHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.postcomp p).leftHomotopyRel
/-
**HomotopicalAlgebra.LeftHomotopyRel.exists_good_cylinder** 是 Mathlib 中的一个引理，位于命
名空间 `HomotopicalAlgebra.LeftHomotopyRel`。
形式化陈述：exists_good_cylinder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel 
f g) : exists (P : Cylinder X), P.IsGood ∧ Nonempty (P.LeftHomotopy f g)
参数：h : LeftHomotopyRel f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `HomotopicalAlgebra.Cylinder.LeftHomotopy.exists_good_cylinder`：exists_go
od_cylinder {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : exists (P' : Cylinder X), P
'.IsGood ∧ Nonempty (P'.LeftHomotopy f g)
-/
lemma exists_good_cylinder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    ∃ (P : Cylinder X), P.IsGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_cylinder
/-
**HomotopicalAlgebra.LeftHomotopyRel.exists_very_good_cylinder** 是 Mathlib 中的一个引
理，位于命名空间 `HomotopicalAlgebra.LeftHomotopyRel`。
形式化陈述：exists_very_good_cylinder [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h
 : LeftHomotopyRel f g) : exists (P : Cylinder X), P.IsVeryGood ∧ Nonempty (P.Le
ftHomotopy f g)
参数：h : LeftHomotopyRel f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.exists_good_cylinder`：exists_good_cyl
inder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : exists (P : Cy
linder X), P.IsGood ∧ Nonempty (P.LeftHomotop…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.trivialCofibrati…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₀_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.Precylinder.i₁_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用引理 `HomotopicalAlgebra.weakEquivalence_of_precomp_of_fac`：weakEquivalence_of
_precomp_of_fac (fac : f ≫ g = fg) [WeakEquivalence f] [WeakEquivalence fg] : We
akEquivalence g
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceITrivialCofibrationsFibrations`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.Cylinder.weakEquivalence_π`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakEqu
ivalences C]   {A : C} (self : Homo…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomotopicalAlgebra.Precylinder.inl_i`：inl_i : coprod.inl ≫ P.i = P.i₀
· 使用定理 `HomotopicalAlgebra.Precylinder.inl_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用引理 `HomotopicalAlgebra.Precylinder.inr_i`：inr_i : coprod.inr ≫ P.i = P.i₁
· 使用定理 `HomotopicalAlgebra.Precylinder.inr_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.instCofibrationCompOfIsStableUnderCompositionCofibrat
ions`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithCofi…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeCofibrations`：∀ (C : Type u) [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithW
eakEquivalences C]   [inst_2 : Homotopica…
（共 40 条，此处仅展示前 30 条）
-/
lemma exists_very_good_cylinder [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y]
    (h : LeftHomotopyRel f g) :
    ∃ (P : Cylinder X), P.IsVeryGood ∧ Nonempty (P.LeftHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
  let fac := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.π
  let P' : Cylinder X :=
    { I := fac.Z
      i₀ := P.i₀ ≫ fac.i
      i₁ := P.i₁ ≫ fac.i
      π := fac.p
      weakEquivalence_π := weakEquivalence_of_precomp_of_fac fac.fac }
  have : Cofibration P'.i := by
    rw [show P'.i = P.i ≫ fac.i by cat_disch]
    infer_instance
  have sq : CommSq h.h fac.i (terminal.from _) (terminal.from _) := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩ ⟩
/-
**HomotopicalAlgebra.LeftHomotopyRel.symm** 是 Mathlib 中的一个引理，位于命名空间 `Homotopical
Algebra.LeftHomotopyRel`。
形式化陈述：symm [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel f
 g) : LeftHomotopyRel g f
参数：h : LeftHomotopyRel f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.Cylinder.LeftHomotopy.leftHomotopyRel`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Category
WithWeakEquivalences C]   {X Y : C} {f g : X ⟶…
-/
lemma symm [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : LeftHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.leftHomotopyRel
/-
**HomotopicalAlgebra.LeftHomotopyRel.trans** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra.LeftHomotopyRel`。
形式化陈述：trans [ModelCategory C] {f₀ f₁ f₂ : X ⟶ Y} [IsCofibrant X] (h : LeftHomoto
pyRel f₀ f₁) (h' : LeftHomotopyRel f₁ f₂) : LeftHomotopyRel f₀ f₂
参数：h : LeftHomotopyRel f₀ f₁；h' : LeftHomotopyRel f₁ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.exists_good_cylinder`：exists_good_cyl
inder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : exists (P : Cy
linder X), P.IsGood ∧ Nonempty (P.LeftHomotop…
· 使用定理 `HomotopicalAlgebra.Cylinder.LeftHomotopy.leftHomotopyRel`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Category
WithWeakEquivalences C]   {X Y : C} {f g : X ⟶…
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
-/
lemma trans [ModelCategory C]
    {f₀ f₁ f₂ : X ⟶ Y} [IsCofibrant X] (h : LeftHomotopyRel f₀ f₁)
    (h' : LeftHomotopyRel f₁ f₂) : LeftHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_cylinder
  exact (h.trans h').leftHomotopyRel
/-
**HomotopicalAlgebra.LeftHomotopyRel.equivalence** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra.LeftHomotopyRel`。
形式化陈述：equivalence [ModelCategory C] (X Y : C) [IsCofibrant X] : _root_.Equivalen
ce (LeftHomotopyRel (X
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.refl`：refl [ModelCategory C] (f : X ⟶
 Y) : LeftHomotopyRel f f
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.symm`：symm [CategoryWithWeakEquivalen
ces C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : LeftHomotopyRel g f
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.trans`：trans [ModelCategory C] {f₀ f₁
 f₂ : X ⟶ Y} [IsCofibrant X] (h : LeftHomotopyRel f₀ f₁) (h' : LeftHomotopyRel f
₁ f₂) : LeftHomotopyRel f₀ f₂
-/
lemma equivalence [ModelCategory C] (X Y : C) [IsCofibrant X] :
    _root_.Equivalence (LeftHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.LeftHomotopyRel.precomp** 是 Mathlib 中的一个引理，位于命名空间 `Homotopi
calAlgebra.LeftHomotopyRel`。
形式化陈述：precomp [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel
 f g) {Z : C} (i : Z ⟶ X) : LeftHomotopyRel (i ≫ f) (i ≫ g)
参数：h : LeftHomotopyRel f g；i : Z ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.exists_very_good_cylinder`：exists_ver
y_good_cylinder [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyR
el f g) : exists (P : Cylinder X), P.IsVeryGood ∧ …
· 使用引理 `HomotopicalAlgebra.Cylinder.exists_very_good`：exists_very_good : exists 
(P : Cylinder A), P.IsVeryGood
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₀_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₁_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `HomotopicalAlgebra.Precylinder.inl_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₀_π_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A) {Z
 : C}   (h : A ⟶ Z), CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.Precylinder.inr_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₁_π_assoc`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A) {Z
 : C}   (h : A ⟶ Z), CategoryTh…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.Cylinder.IsGood.cofibration_i`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Catego
ryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `HomotopicalAlgebra.Cylinder.IsVeryGood.toIsGood`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Categor
yWithWeakEquivalences C} {P : Homotop…
· 使用定理 `HomotopicalAlgebra.Cylinder.IsVeryGood.fibration_π`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Cate
goryWithWeakEquivalences C} {P : Homotop…
（共 39 条，此处仅展示前 30 条）
-/
lemma precomp [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyRel f g)
    {Z : C} (i : Z ⟶ X) : LeftHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  obtain ⟨Q, _⟩ := Cylinder.exists_very_good Z
  have sq : CommSq (coprod.desc (i ≫ P.i₀) (i ≫ P.i₁)) Q.i P.π (Q.π ≫ i) := ⟨by aesop_cat⟩
  exact ⟨Q,
   ⟨{ h := sq.lift ≫ h.h
      h₀ := by
        have := coprod.inl ≫= sq.fac_left
        simp only [Q.inl_i_assoc, coprod.inl_desc] at this
        simp [reassoc_of% this]
      h₁ := by
        have := coprod.inr ≫= sq.fac_left
        simp only [Q.inr_i_assoc, coprod.inr_desc] at this
        simp [reassoc_of% this] }⟩⟩

end LeftHomotopyRel

variable (X Y Z : C)

/-- In a category with weak equivalences, this is the quotient of the type
of morphisms `X ⟶ Y` by the equivalence relation generated by left homotopies. -/
/-
**HomotopicalAlgebra.LeftHomotopyClass** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlg
ebra`。
形式化陈述：LeftHomotopyClass [CategoryWithWeakEquivalences C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with weak equivalences, this is the quotient of the type
of morphisms `X ⟶ Y` by the equivalence relation generated by left homotopies.
-/
def LeftHomotopyClass [CategoryWithWeakEquivalences C] :=
  _root_.Quot (LeftHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

/-- Given `f : X ⟶ Y`, this is the class of `f` in the quotient `LeftHomotopyClass X Y`. -/
/-
**HomotopicalAlgebra.LeftHomotopyClass.mk** 是 Mathlib 中的一个定义，位于命名空间 `Homotopical
Algebra.LeftHomotopyClass`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       [inst_1 : HomotopicalAlgebra.CategoryWithWeakEquivalences C] → (X ⟶ Y) 
→ HomotopicalAlgebra.LeftHomotopyClass X Y
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X ⟶ Y`, this is the class of `f` in the quotient `LeftHomotopyClass X
 Y`.
-/
def LeftHomotopyClass.mk [CategoryWithWeakEquivalences C] :
    (X ⟶ Y) → LeftHomotopyClass X Y := Quot.mk _
/-
**HomotopicalAlgebra.LeftHomotopyClass.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `
HomotopicalAlgebra.LeftHomotopyClass`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : HomotopicalAlgebra.CategoryWithWeakEquivalences C],   Function.Surjective H
omotopicalAlgebra.LeftHomotopyClass.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
lemma LeftHomotopyClass.mk_surjective [CategoryWithWeakEquivalences C] :
    Function.Surjective (mk : (X ⟶ Y) → _) :=
  Quot.mk_surjective

namespace LeftHomotopyClass

/-
**HomotopicalAlgebra.LeftHomotopyClass.sound** 是 Mathlib 中的一个引理，位于命名空间 `Homotopi
calAlgebra.LeftHomotopyClass`。
形式化陈述：sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel 
f g) : mk f = mk g
参数：h : LeftHomotopyRel f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    mk f = mk g := Quot.sound h

/-- The postcomposition map `LeftHomotopyClass X Y → (Y ⟶ Z) → LeftHomotopyClass X Z`. -/
/-
**HomotopicalAlgebra.LeftHomotopyClass.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `Homot
opicalAlgebra.LeftHomotopyClass`。
形式化陈述：postcomp [CategoryWithWeakEquivalences C] : LeftHomotopyClass X Y -> (Y ⟶ 
Z) -> LeftHomotopyClass X Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The postcomposition map `LeftHomotopyClass X Y → (Y ⟶ Z) → LeftHomotopyClass X Z
`.
-/
def postcomp [CategoryWithWeakEquivalences C] :
    LeftHomotopyClass X Y → (Y ⟶ Z) → LeftHomotopyClass X Z :=
  fun f g ↦ Quot.lift (fun f ↦ mk (f ≫ g)) (fun _ _ h ↦ sound (h.postcomp g)) f

@[simp]
/-
**HomotopicalAlgebra.LeftHomotopyClass.postcomp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ho
motopicalAlgebra.LeftHomotopyClass`。
形式化陈述：postcomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) : (mk
 f).postcomp g = mk (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma postcomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk f).postcomp g = mk (f ≫ g) := rfl
/-
**HomotopicalAlgebra.LeftHomotopyClass.mk_eq_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopicalAlgebra.LeftHomotopyClass`。
形式化陈述：mk_eq_mk_iff [ModelCategory C] [IsCofibrant X] (f g : X ⟶ Y) : mk f = mk g
 ↔ LeftHomotopyRel f g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equivalence.eqvGen_iff`：Equivalence.eqvGen_iff (h : Equivalence r) : Eqv
Gen r a b ↔ r a b
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.equivalence`：equivalence [ModelCatego
ry C] (X Y : C) [IsCofibrant X] : _root_.Equivalence (LeftHomotopyRel (X
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
-/
lemma mk_eq_mk_iff [ModelCategory C] [IsCofibrant X] (f g : X ⟶ Y) :
    mk f = mk g ↔ LeftHomotopyRel f g := by
  rw [← (LeftHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

end LeftHomotopyClass

end HomotopicalAlgebra

