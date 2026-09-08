/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Right homotopies in model categories

We introduce the types `PrepathObject.RightHomotopy` and `PathObject.RightHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)path object of `Y`.
Given two morphisms `f` and `g`, we introduce the relation `RightHomotopyRel f g`
asserting the existence of a path object `P` and
a right homotopy `P.RightHomotopy f g`, and we define the quotient
type `RightHomotopyClass X Y`. We show that if `Y` is a fibrant
object in a model category, then `RightHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

(This file dualizes the definitions in `Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean`.)

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace PrepathObject

variable {Y : C} (P : PrepathObject Y) {X : C}

/-- Given a pre-path object `P` for `Y`, two maps `f` and `g` in `X ⟶ Y` are
homotopic relative to `P` when there is a morphism `h : X ⟶ P.P`
such that `h ≫ P.p₀ = f` and `h ≫ P.p₁ = g`. -/
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy** 是 Mathlib 中的一个结构，位于命名空间 `Homo
topicalAlgebra.PrepathObject`。
形式化陈述：RightHomotopy (f g : X ⟶ Y) where /-- a morphism from the source to the pr
e-path object -/ h : X ⟶ P.P h₀ : h ≫ P.p₀ = f
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pre-path object `P` for `Y`, two maps `f` and `g` in `X ⟶ Y` are
homotopic relative to `P` when there is a morphism `h : X ⟶ P.P`
such that `h ≫ P.p₀ = f` and `h ≫ P.p₁ = g`.
-/
structure RightHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the source to the pre-path object -/
  h : X ⟶ P.P
  h₀ : h ≫ P.p₀ = f := by cat_disch
  h₁ : h ≫ P.p₁ = g := by cat_disch

namespace RightHomotopy

attribute [reassoc (attr := simp)] h₀ h₁

/-- `f : X ⟶ Y` is right homotopic to itself relative to any pre-path object. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 
`HomotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：refl (f : X ⟶ Y) : P.RightHomotopy f f where h
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X ⟶ Y` is right homotopic to itself relative to any pre-path object.
-/
def refl (f : X ⟶ Y) : P.RightHomotopy f f where
  h := f ≫ P.ι

variable {P}

set_option backward.defeqAttrib.useBackward true in
/-- If `f` and `g` are homotopic relative to a pre-path object `P`, then `g` and `f`
are homotopic relative to `P.symm` -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 
`HomotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f wh
ere h
参数：h : P.RightHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are homotopic relative to a pre-path object `P`, then `g` and `f`
are homotopic relative to `P.symm`
-/
def symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f where
  h := h.h

set_option backward.isDefEq.respectTransparency false in
/-- If `f₀` is homotopic to `f₁` relative to a pre-path object `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.trans** 是 Mathlib 中的一个定义，位于命名空间
 `HomotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：trans {f₀ f₁ f₂ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) {P' : PrepathObject Y
} (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] : (P.trans P').RightHom
otopy f₀ f₂ where h
参数：h : P.RightHomotopy f₀ f₁；h' : P'.RightHomotopy f₁ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f₀` is homotopic to `f₁` relative to a pre-path object `P`,
and `f₁` is homotopic to `f₂` relative to `P'`, then
`f₀` is homotopic to `f₂` relative to `P.trans P'`.
-/
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.RightHomotopy f₀ f₁) {P' : PrepathObject Y}
    (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] :
    (P.trans P').RightHomotopy f₀ f₂ where
  h := pullback.lift h.h h'.h (by simp)

/-- Right homotopies are compatible with precomposition. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.precomp** 是 Mathlib 中的一个定义，位于命名
空间 `HomotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) : P.Ri
ghtHomotopy (i ≫ f) (i ≫ g) where h
参数：h : P.RightHomotopy f g；i : Z ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopies are compatible with precomposition.
-/
def precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) where
  h := i ≫ h.h

set_option backward.defeqAttrib.useBackward true in
/-- Right homotopies in a full subcategory identify to right homotopies in the
ambient category. -/
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.fullSubcategoryEquiv** 是 Mathli
b 中的一个定义，位于命名空间 `HomotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：fullSubcategoryEquiv {P : ObjectProperty C} {X Y : P.FullSubcategory} {Q :
 PrepathObject Y} {f g : X ⟶ Y} : Q.RightHomotopy f g ≃ (Q.map P.ι).RightHomotop
y f.hom g.hom where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopies in a full subcategory identify to right homotopies in the
ambient category.
-/
noncomputable def fullSubcategoryEquiv {P : ObjectProperty C} {X Y : P.FullSubcategory}
    {Q : PrepathObject Y} {f g : X ⟶ Y} :
    Q.RightHomotopy f g ≃ (Q.map P.ι).RightHomotopy f.hom g.hom where
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

end RightHomotopy

end PrepathObject

namespace PathObject

variable {X Y : C}

/-- Given a path object `P` for `X`, two maps `f` and `g` in `X ⟶ Y`
are homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`. -/
/-
**HomotopicalAlgebra.PathObject.RightHomotopy** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homot
opicalAlgebra.PathObject`。
形式化陈述：RightHomotopy [CategoryWithWeakEquivalences C] (P : PathObject Y) (f g : X
 ⟶ Y) : Type v
参数：P : PathObject Y；f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a path object `P` for `X`, two maps `f` and `g` in `X ⟶ Y`
are homotopic relative to `P` when there is a morphism `h : P.I ⟶ Y`
such that `P.i₀ ≫ h = f` and `P.i₁ ≫ h = g`.
-/
abbrev RightHomotopy [CategoryWithWeakEquivalences C] (P : PathObject Y) (f g : X ⟶ Y) : Type v :=
  P.toPrepathObject.RightHomotopy f g

namespace RightHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : PathObject Y)

/-- `f : X ⟶ Y` is right homotopic to itself relative to any path object. -/
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.refl** 是 Mathlib 中的一个缩写定义，位于命名空间 `
HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：refl (f : X ⟶ Y) : P.RightHomotopy f f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X ⟶ Y` is right homotopic to itself relative to any path object.
-/
abbrev refl (f : X ⟶ Y) : P.RightHomotopy f f := PrepathObject.RightHomotopy.refl _ f

variable {P} in
/-- If `f` and `g` are homotopic relative to a path object `P`, then `g` and `f`
are homotopic relative to `P.symm`. -/
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.symm** 是 Mathlib 中的一个缩写定义，位于命名空间 `
HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f
参数：h : P.RightHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are homotopic relative to a path object `P`, then `g` and `f`
are homotopic relative to `P.symm`.
-/
abbrev symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f :=
  PrepathObject.RightHomotopy.symm h

variable {P} in
/-- Right homotopies are compatible with precomposition. -/
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.precomp** 是 Mathlib 中的一个缩写定义，位于命名空
间 `HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) : P.Ri
ghtHomotopy (i ≫ f) (i ≫ g)
参数：h : P.RightHomotopy f g；i : Z ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopies are compatible with precomposition.
-/
abbrev precomp {f g : X ⟶ Y} (h : P.RightHomotopy f g) {Z : C} (i : Z ⟶ X) :
    P.RightHomotopy (i ≫ f) (i ≫ g) :=
  PrepathObject.RightHomotopy.precomp h i
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.weakEquivalence_iff** 是 Mathlib 中的
一个引理，位于命名空间 `HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty] [(weak
Equivalences C).ContainsIdentities] {f₀ f₁ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) 
: WeakEquivalence f₀ ↔ WeakEquivalence f₁
参数：weakEquivalences C；weakEquivalences C；h : P.RightHomotopy f₀ f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma weakEquivalence_iff [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [(weakEquivalences C).ContainsIdentities]
    {f₀ f₁ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) :
    WeakEquivalence f₀ ↔ WeakEquivalence f₁ := by
  induction h
  grind [weakEquivalence_postcomp_iff]

end

section

variable [ModelCategory C] {P : PathObject Y}

/-- If `f₀ : X ⟶ Y` is homotopic to `f₁` relative to a path object `P`,
and `f₁` is homotopic to `f₂` relative to a good path object `P'`,
then `f₀` is homotopic to `f₂` relative to the path object `P.trans P'`
when `Y` is fibrant. -/
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.trans** 是 Mathlib 中的一个缩写定义，位于命名空间 
`HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：trans [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y} (h : P.RightHomotopy f₀ f₁) {P' : P
athObject Y} [P'.IsGood] (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] 
: (P.trans P').RightHomotopy f₀ f₂
参数：h : P.RightHomotopy f₀ f₁；h' : P'.RightHomotopy f₁ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f₀ : X ⟶ Y` is homotopic to `f₁` relative to a path object `P`,
and `f₁` is homotopic to `f₂` relative to a good path object `P'`,
then `f₀` is homotopic to `f₂` relative to the path object `P.trans P'`
when `Y` is fibrant.
-/
noncomputable abbrev trans [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y}
    (h : P.RightHomotopy f₀ f₁) {P' : PathObject Y} [P'.IsGood]
    (h' : P'.RightHomotopy f₁ f₂) [HasPullback P.p₁ P'.p₀] :
    (P.trans P').RightHomotopy f₀ f₂ :=
  PrepathObject.RightHomotopy.trans h h'
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.exists_good_pathObject** 是 Mathlib
 中的一个引理，位于命名空间 `HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：exists_good_pathObject {f g : X ⟶ Y} (h : P.RightHomotopy f g) : exists (P
' : PathObject Y), P'.IsGood ∧ Nonempty (P'.RightHomotopy f g)
参数：h : P.RightHomotopy f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
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
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.M
orphismProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_fst`：p_fst : P.p ≫ prod.fst = P.p₀
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₀`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_snd`：p_snd : P.p ≫ prod.snd = P.p₁
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₁`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceCompOfIsStableUnderCompositionWeak
Equivalences`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : 
C} (f : X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithWeak…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `HomotopicalAlgebra.PathObject.weakEquivalence_ι`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakE
quivalences C]   {A : C} (self : Homo…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceITrivialCofibrationsFibrations`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.fibration_iff`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Category
WithFibrations C],   H…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₁`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
-/
lemma exists_good_pathObject {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    ∃ (P' : PathObject Y), P'.IsGood ∧ Nonempty (P'.RightHomotopy f g) := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) P.p
  exact
   ⟨{ P := d.Z
      p₀ := d.p ≫ prod.fst
      p₁ := d.p ≫ prod.snd
      ι := P.ι ≫ d.i }, ⟨by
        rw [fibration_iff]
        convert! d.hp
        aesop⟩, ⟨{ h := h.h ≫ d.i }⟩⟩

/-- The homotopy extension theorem: if `p : A ⟶ X` is a cofibration,
`l₀ : X ⟶ B` is a morphism, if there is a right homotopy `h` between
the composition `f₀ := i ≫ l₀` and a morphism `f₁ : A ⟶ B`,
then there exists a morphism `l₁ : X ⟶ B` and a right homotopy `h'` from
`l₀` to `l₁` which is compatible with `h` (in particular, `i ≫ l₁ = f₁`). -/
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.homotopy_extension** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：homotopy_extension {A B X : C} {P : PathObject B} {f₀ f₁ : A ⟶ B} [IsFibra
nt B] [P.IsGood] (h : P.RightHomotopy f₀ f₁) (i : A ⟶ X) [Cofibration i] (l₀ : X
 ⟶ B) (hl₀ : i ≫ l₀ = f₀
参数：h : P.RightHomotopy f₀ f₁；i : A ⟶ X；l₀ : X ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.PathObject.instFibrationP₀`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlgebra.CategoryW
ithWeakEquivalences C] (P : Homotop…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeFibrations`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWea
kEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemTrivialCof
ibrationsFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.trivialCofibr
a…
· 使用定理 `HomotopicalAlgebra.instIsStableUnderBaseChangeFibrations`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Category
WithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.PathObject.instWeakEquivalenceP₀`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlgebra.Cat
egoryWithWeakEquivalences C] (P : Homotop…
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
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm3a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.weakEquivalences…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f

--- 原说明 ---
The homotopy extension theorem: if `p : A ⟶ X` is a cofibration,
`l₀ : X ⟶ B` is a morphism, if there is a right homotopy `h` between
the composition `f₀ := i ≫ l₀` and a morphism `f₁ : A ⟶ B`,
then there exists a morphism `l₁ : X ⟶ B` and a right homotopy `h'` from
`l₀` to `l₁` which is compatible with `h` (in particular, `i ≫ l₁ = f₁`).
-/
lemma homotopy_extension {A B X : C} {P : PathObject B} {f₀ f₁ : A ⟶ B}
    [IsFibrant B] [P.IsGood]
    (h : P.RightHomotopy f₀ f₁) (i : A ⟶ X) [Cofibration i]
    (l₀ : X ⟶ B) (hl₀ : i ≫ l₀ = f₀ := by cat_disch) :
    ∃ (l₁ : X ⟶ B) (h' : P.RightHomotopy l₀ l₁), i ≫ h'.h = h.h :=
  have sq : CommSq h.h i P.p₀ l₀ := { }
  ⟨sq.lift ≫ P.p₁, { h := sq.lift }, by simp⟩

end

end RightHomotopy

end PathObject

/-- The right homotopy relation on morphisms in a category with weak equivalences. -/
/-
**HomotopicalAlgebra.RightHomotopyRel** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：RightHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homotopy relation on morphisms in a category with weak equivalences.
-/
def RightHomotopyRel [CategoryWithWeakEquivalences C] : HomRel C :=
  fun _ Y f g ↦ ∃ (P : PathObject Y), Nonempty (P.RightHomotopy f g)
/-
**HomotopicalAlgebra.PathObject.RightHomotopy.rightHomotopyRel** 是 Mathlib 中的一个定
理，位于命名空间 `HomotopicalAlgebra.PathObject.RightHomotopy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.CategoryWithWeakEquivalences C]   {X Y : C} {f g : X ⟶ Y} {P : Homot
opicalAlgebra.PathObject Y} (h : P.RightHomotopy f g),   HomotopicalAlgebra.Righ
tHomotopyRel f g
参数：h : P.RightHomotopy f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma PathObject.RightHomotopy.rightHomotopyRel [CategoryWithWeakEquivalences C]
    {X Y : C} {f g : X ⟶ Y}
    {P : PathObject Y} (h : P.RightHomotopy f g) :
    RightHomotopyRel f g :=
  ⟨_, ⟨h⟩⟩

namespace RightHomotopyRel

variable (C) in
/-
**HomotopicalAlgebra.RightHomotopyRel.factorsThroughLocalization** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopicalAlgebra.RightHomotopyRel`。
形式化陈述：factorsThroughLocalization [CategoryWithWeakEquivalences C] : RightHomotop
yRel.FactorsThroughLocalization (weakEquivalences C)
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
· 使用定理 `HomotopicalAlgebra.PathObject.weakEquivalence_ι`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakE
quivalences C]   {A : C} (self : Homo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₀`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₁`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₁`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
-/
lemma factorsThroughLocalization [CategoryWithWeakEquivalences C] :
    RightHomotopyRel.FactorsThroughLocalization (weakEquivalences C) := by
  rintro X Y f g ⟨P, ⟨h⟩⟩
  let L := (weakEquivalences C).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map P.p₀ = L.map P.p₁ by
    simp only [← h.h₀, ← h.h₁, L.map_comp, this]
  have := Localization.inverts L (weakEquivalences C) P.ι (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp [← cancel_epi (L.map P.ι), ← L.map_comp]

variable {X Y : C}
/-
**HomotopicalAlgebra.RightHomotopyRel.refl** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra.RightHomotopyRel`。
形式化陈述：refl [ModelCategory C] (f : X ⟶ Y) : RightHomotopyRel f f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.PathObject.instNonempty`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory C] {A : 
C},   Nonempty (HomotopicalAlgeb…
-/
lemma refl [ModelCategory C] (f : X ⟶ Y) : RightHomotopyRel f f :=
  ⟨Classical.arbitrary _, ⟨PathObject.RightHomotopy.refl _ _⟩⟩
/-
**HomotopicalAlgebra.RightHomotopyRel.precomp** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.RightHomotopyRel`。
形式化陈述：precomp [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyR
el f g) {Z : C} (i : Z ⟶ X) : RightHomotopyRel (i ≫ f) (i ≫ g)
参数：h : RightHomotopyRel f g；i : Z ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.PathObject.RightHomotopy.rightHomotopyRel`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Cate
goryWithWeakEquivalences C]   {X Y : C} {f g : X ⟶…
-/
lemma precomp [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : RightHomotopyRel f g) {Z : C} (i : Z ⟶ X) :
    RightHomotopyRel (i ≫ f) (i ≫ g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact (h.precomp i).rightHomotopyRel
/-
**HomotopicalAlgebra.RightHomotopyRel.exists_good_pathObject** 是 Mathlib 中的一个引理，
位于命名空间 `HomotopicalAlgebra.RightHomotopyRel`。
形式化陈述：exists_good_pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyR
el f g) : exists (P : PathObject Y), P.IsGood ∧ Nonempty (P.RightHomotopy f g)
参数：h : RightHomotopyRel f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `HomotopicalAlgebra.PathObject.RightHomotopy.exists_good_pathObject`：exis
ts_good_pathObject {f g : X ⟶ Y} (h : P.RightHomotopy f g) : exists (P' : PathOb
ject Y), P'.IsGood ∧ Nonempty (P'.RightHomotopy f g)
-/
lemma exists_good_pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    ∃ (P : PathObject Y), P.IsGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.exists_good_pathObject
/-
**HomotopicalAlgebra.RightHomotopyRel.exists_very_good_pathObject** 是 Mathlib 中的
一个引理，位于命名空间 `HomotopicalAlgebra.RightHomotopyRel`。
形式化陈述：exists_very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X
] (h : RightHomotopyRel f g) : exists (P : PathObject Y), P.IsVeryGood ∧ Nonempt
y (P.RightHomotopy f g)
参数：h : RightHomotopyRel f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_good_pathObject`：exists_good_
pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) : exists (
P : PathObject Y), P.IsGood ∧ Nonempty (P.RightH…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.cofibrations C).…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.M
orphismProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₀`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₁`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用引理 `HomotopicalAlgebra.weakEquivalence_of_postcomp_of_fac`：weakEquivalence_o
f_postcomp_of_fac (fac : f ≫ g = fg) [WeakEquivalence g] [hfg : WeakEquivalence 
fg] : WeakEquivalence f
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalencePCofibrationsTrivialFibrations`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.PathObject.weakEquivalence_ι`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakE
quivalences C]   {A : C} (self : Homo…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_fst`：p_fst : P.p ≫ prod.fst = P.p₀
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_snd`：p_snd : P.p ≫ prod.snd = P.p₁
· 使用定理 `HomotopicalAlgebra.instFibrationCompOfIsStableUnderCompositionFibrations
`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ 
Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithFibr…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeFibrations`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWea
kEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemTrivialCof
ibrationsFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.trivialCofibr
a…
（共 39 条，此处仅展示前 30 条）
-/
lemma exists_very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X]
    (h : RightHomotopyRel f g) :
    ∃ (P : PathObject Y), P.IsVeryGood ∧ Nonempty (P.RightHomotopy f g) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
  let fac := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C) P.ι
  let P' : PathObject Y :=
    { P := fac.Z
      p₀ := fac.p ≫ P.p₀
      p₁ := fac.p ≫ P.p₁
      ι := fac.i
      weakEquivalence_ι := weakEquivalence_of_postcomp_of_fac fac.fac }
  have : Fibration P'.p := by
    rw [show P'.p = fac.p ≫ P.p by cat_disch]
    infer_instance
  have sq : CommSq (initial.to _) (initial.to _) fac.p h.h := { }
  exact ⟨P', { }, ⟨{ h := sq.lift }⟩⟩
/-
**HomotopicalAlgebra.RightHomotopyRel.symm** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra.RightHomotopyRel`。
形式化陈述：symm [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyRel 
f g) : RightHomotopyRel g f
参数：h : RightHomotopyRel f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.PathObject.RightHomotopy.rightHomotopyRel`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Cate
goryWithWeakEquivalences C]   {X Y : C} {f g : X ⟶…
-/
lemma symm [CategoryWithWeakEquivalences C]
    {f g : X ⟶ Y} (h : RightHomotopyRel f g) : RightHomotopyRel g f := by
  obtain ⟨P, ⟨h⟩⟩ := h
  exact h.symm.rightHomotopyRel
/-
**HomotopicalAlgebra.RightHomotopyRel.trans** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra.RightHomotopyRel`。
形式化陈述：trans [ModelCategory C] {f₀ f₁ f₂ : X ⟶ Y} [IsFibrant Y] (h : RightHomotop
yRel f₀ f₁) (h' : RightHomotopyRel f₁ f₂) : RightHomotopyRel f₀ f₂
参数：h : RightHomotopyRel f₀ f₁；h' : RightHomotopyRel f₁ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_good_pathObject`：exists_good_
pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) : exists (
P : PathObject Y), P.IsGood ∧ Nonempty (P.RightH…
· 使用定理 `HomotopicalAlgebra.PathObject.RightHomotopy.rightHomotopyRel`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Cate
goryWithWeakEquivalences C]   {X Y : C} {f g : X ⟶…
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
-/
lemma trans [ModelCategory C]
    {f₀ f₁ f₂ : X ⟶ Y} [IsFibrant Y] (h : RightHomotopyRel f₀ f₁)
    (h' : RightHomotopyRel f₁ f₂) : RightHomotopyRel f₀ f₂ := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨P', _, ⟨h'⟩⟩ := h'.exists_good_pathObject
  exact (h.trans h').rightHomotopyRel
/-
**HomotopicalAlgebra.RightHomotopyRel.equivalence** 是 Mathlib 中的一个引理，位于命名空间 `Hom
otopicalAlgebra.RightHomotopyRel`。
形式化陈述：equivalence [ModelCategory C] (X Y : C) [IsFibrant Y] : _root_.Equivalence
 (RightHomotopyRel (X
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.refl`：refl [ModelCategory C] (f : X 
⟶ Y) : RightHomotopyRel f f
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.symm`：symm [CategoryWithWeakEquivale
nces C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) : RightHomotopyRel g f
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.trans`：trans [ModelCategory C] {f₀ f
₁ f₂ : X ⟶ Y} [IsFibrant Y] (h : RightHomotopyRel f₀ f₁) (h' : RightHomotopyRel 
f₁ f₂) : RightHomotopyRel f₀ f₂
-/
lemma equivalence [ModelCategory C] (X Y : C) [IsFibrant Y] :
    _root_.Equivalence (RightHomotopyRel (X := X) (Y := Y)) where
  refl := .refl
  symm h := h.symm
  trans h h' := h.trans h'

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.RightHomotopyRel.postcomp** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra.RightHomotopyRel`。
形式化陈述：postcomp [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotop
yRel f g) {Z : C} (p : Y ⟶ Z) : RightHomotopyRel (f ≫ p) (g ≫ p)
参数：h : RightHomotopyRel f g；p : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_very_good_pathObject`：exists_
very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightH
omotopyRel f g) : exists (P : PathObject Y), P.IsVery…
· 使用引理 `HomotopicalAlgebra.PathObject.exists_very_good`：exists_very_good : exist
s (P : PathObject A), P.IsVeryGood
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₀_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A
) {Z : C}   (h : A ⟶ Z), Category…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₁_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A
) {Z : C}   (h : A ⟶ Z), Category…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_fst`：p_fst : P.p ≫ prod.fst = P.p₀
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₀`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_snd`：p_snd : P.p ≫ prod.snd = P.p₁
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₁`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.PathObject.IsVeryGood.cofibration_ι`：∀ {C : Type u} {
inst : CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `HomotopicalAlgebra.PathObject.weakEquivalence_ι`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakE
quivalences C]   {A : C} (self : Homo…
· 使用定理 `HomotopicalAlgebra.PathObject.IsGood.fibration_p`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Catego
ryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `HomotopicalAlgebra.PathObject.IsVeryGood.toIsGood`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Categ
oryWithWeakEquivalences C} {P : Homotop…
（共 37 条，此处仅展示前 30 条）
-/
lemma postcomp [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightHomotopyRel f g)
    {Z : C} (p : Y ⟶ Z) : RightHomotopyRel (f ≫ p) (g ≫ p) := by
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  obtain ⟨Q, _⟩ := PathObject.exists_very_good Z
  have sq : CommSq (p ≫ Q.ι) P.ι Q.p (prod.lift (P.p₀ ≫ p) (P.p₁ ≫ p)) := { }
  exact ⟨Q,
   ⟨{ h := h.h ≫ sq.lift
      h₀ := by
        have := sq.fac_right =≫ prod.fst
        simp only [Category.assoc, prod.lift_fst, Q.p_fst] at this
        simp [this]
      h₁ := by
        have := sq.fac_right =≫ prod.snd
        simp only [Category.assoc, prod.lift_snd, Q.p_snd] at this
        simp [this]
    }⟩⟩

end RightHomotopyRel

variable (X Y Z : C)

/-- In a category with weak equivalences, this is the quotient of the type
of morphisms `X ⟶ Y` by the equivalence relation generated by right homotopies. -/
/-
**HomotopicalAlgebra.RightHomotopyClass** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAl
gebra`。
形式化陈述：RightHomotopyClass [CategoryWithWeakEquivalences C]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with weak equivalences, this is the quotient of the type
of morphisms `X ⟶ Y` by the equivalence relation generated by right homotopies.
-/
def RightHomotopyClass [CategoryWithWeakEquivalences C] :=
  _root_.Quot (RightHomotopyRel (X := X) (Y := Y))

variable {X Y Z}

/-- Given `f : X ⟶ Y`, this is the class of `f` in the quotient `RightHomotopyClass X Y`. -/
/-
**HomotopicalAlgebra.RightHomotopyClass.mk** 是 Mathlib 中的一个定义，位于命名空间 `Homotopica
lAlgebra.RightHomotopyClass`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       [inst_1 : HomotopicalAlgebra.CategoryWithWeakEquivalences C] → (X ⟶ Y) 
→ HomotopicalAlgebra.RightHomotopyClass X Y
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X ⟶ Y`, this is the class of `f` in the quotient `RightHomotopyClass 
X Y`.
-/
def RightHomotopyClass.mk [CategoryWithWeakEquivalences C] :
    (X ⟶ Y) → RightHomotopyClass X Y := Quot.mk _
/-
**HomotopicalAlgebra.RightHomotopyClass.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 
`HomotopicalAlgebra.RightHomotopyClass`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : HomotopicalAlgebra.CategoryWithWeakEquivalences C],   Function.Surjective H
omotopicalAlgebra.RightHomotopyClass.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
lemma RightHomotopyClass.mk_surjective [CategoryWithWeakEquivalences C] :
    Function.Surjective (mk : (X ⟶ Y) → _) :=
  Quot.mk_surjective

namespace RightHomotopyClass

/-
**HomotopicalAlgebra.RightHomotopyClass.sound** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.RightHomotopyClass`。
形式化陈述：sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyRel
 f g) : mk f = mk g
参数：h : RightHomotopyRel f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sound [CategoryWithWeakEquivalences C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) :
    mk f = mk g := Quot.sound h

/-- The precomposition map `RightHomotopyClass Y Z → (X ⟶ Y) → RightHomotopyClass X Z`. -/
/-
**HomotopicalAlgebra.RightHomotopyClass.precomp** 是 Mathlib 中的一个定义，位于命名空间 `Homot
opicalAlgebra.RightHomotopyClass`。
形式化陈述：precomp [CategoryWithWeakEquivalences C] : RightHomotopyClass Y Z -> (X ⟶ 
Y) -> RightHomotopyClass X Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precomposition map `RightHomotopyClass Y Z → (X ⟶ Y) → RightHomotopyClass X 
Z`.
-/
def precomp [CategoryWithWeakEquivalences C] :
    RightHomotopyClass Y Z → (X ⟶ Y) → RightHomotopyClass X Z :=
  fun g f ↦ Quot.lift (fun g ↦ mk (f ≫ g)) (fun _ _ h ↦ sound (h.precomp f)) g

@[simp]
/-
**HomotopicalAlgebra.RightHomotopyClass.precomp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ho
motopicalAlgebra.RightHomotopyClass`。
形式化陈述：precomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) : (mk 
g).precomp f = mk (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma precomp_mk [CategoryWithWeakEquivalences C] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk g).precomp f = mk (f ≫ g) := rfl
/-
**HomotopicalAlgebra.RightHomotopyClass.mk_eq_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `
HomotopicalAlgebra.RightHomotopyClass`。
形式化陈述：mk_eq_mk_iff [ModelCategory C] [IsFibrant Y] (f g : X ⟶ Y) : mk f = mk g ↔
 RightHomotopyRel f g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equivalence.eqvGen_iff`：Equivalence.eqvGen_iff (h : Equivalence r) : Eqv
Gen r a b ↔ r a b
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.equivalence`：equivalence [ModelCateg
ory C] (X Y : C) [IsFibrant Y] : _root_.Equivalence (RightHomotopyRel (X
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
-/
lemma mk_eq_mk_iff [ModelCategory C] [IsFibrant Y] (f g : X ⟶ Y) :
    mk f = mk g ↔ RightHomotopyRel f g := by
  rw [← (RightHomotopyRel.equivalence X Y).eqvGen_iff]
  exact Quot.eq

end RightHomotopyClass

set_option backward.defeqAttrib.useBackward true in
/-- The left homotopy in the opposite category that is deduced from a right homotopy. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.op** 是 Mathlib 中的一个定义，位于命名空间 `H
omotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {P : HomotopicalAlgebra.PrepathObject Y} → {f g : X ⟶ Y} → P.RightHomot
opy f g → P.op.LeftHomotopy f.op g.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homotopy in the opposite category that is deduced from a right homotopy
.
-/
protected def PrepathObject.RightHomotopy.op
    {X Y : C} {P : PrepathObject Y} {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    P.op.LeftHomotopy f.op g.op where
  h := h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The left homotopy that is deduced from a right homotopy in the opposite category. -/
@[simps]
/-
**HomotopicalAlgebra.PrepathObject.RightHomotopy.unop** 是 Mathlib 中的一个定义，位于命名空间 
`HomotopicalAlgebra.PrepathObject.RightHomotopy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : Cᵒ
ᵖ} →       {P : HomotopicalAlgebra.PrepathObject Y} → {f g : X ⟶ Y} → P.RightHom
otopy f g → P.unop.LeftHomotopy f.unop g.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homotopy that is deduced from a right homotopy in the opposite category
.
-/
protected def PrepathObject.RightHomotopy.unop
    {X Y : Cᵒᵖ} {P : PrepathObject Y} {f g : X ⟶ Y} (h : P.RightHomotopy f g) :
    P.unop.LeftHomotopy f.unop g.unop where
  h := h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The right homotopy in the opposite category that is deduced from a left homotopy. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.op** 是 Mathlib 中的一个定义，位于命名空间 `Homo
topicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {P : HomotopicalAlgebra.Precylinder X} → {f g : X ⟶ Y} → P.LeftHomotopy
 f g → P.op.RightHomotopy f.op g.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homotopy in the opposite category that is deduced from a left homotopy
.
-/
protected def Precylinder.LeftHomotopy.op
    {X Y : C} {P : Precylinder X} {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    P.op.RightHomotopy f.op g.op where
  h := h.h.op
  h₀ := Quiver.Hom.unop_inj (by simp)
  h₁ := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The right homotopy that is deduced from a left homotopy in the opposite category. -/
@[simps]
/-
**HomotopicalAlgebra.Precylinder.LeftHomotopy.unop** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.Precylinder.LeftHomotopy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : Cᵒ
ᵖ} →       {P : HomotopicalAlgebra.Precylinder X} → {f g : X ⟶ Y} → P.LeftHomoto
py f g → P.unop.RightHomotopy f.unop g.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homotopy that is deduced from a left homotopy in the opposite category
.
-/
protected def Precylinder.LeftHomotopy.unop
    {X Y : Cᵒᵖ} {P : Precylinder X} {f g : X ⟶ Y} (h : P.LeftHomotopy f g) :
    P.unop.RightHomotopy f.unop g.unop where
  h := h.h.unop
  h₀ := Quiver.Hom.op_inj (by simp)
  h₁ := Quiver.Hom.op_inj (by simp)

end HomotopicalAlgebra

