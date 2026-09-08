/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The section functor as a right adjoint to the toOver functor

We show that in a cartesian monoidal category `C`, for any exponentiable object `I`, the functor
`toOver I : C ⥤ Over I` mapping an object `X` to the projection `snd : X ⊗ I ⟶ I` in `Over I`
has a right adjoint `sections I : Over I ⥤ C` whose object part is the object of sections
of `X` over `I`.

In particular, if `C` is cartesian closed, then for all objects `I` in `C`, `toOver I : C ⥤ Over I`
has a right adjoint.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed

section Sections

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Closed I]

/-- The first leg of a cospan to define `sectionsObj` as a pullback in `C`. -/
/-
**CategoryTheory.curryRightUnitorHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
`。
形式化陈述：curryRightUnitorHom : 𝟙_ C ⟶ (I ⟶[C] I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first leg of a cospan to define `sectionsObj` as a pullback in `C`.
-/
abbrev curryRightUnitorHom : 𝟙_ C ⟶ (I ⟶[C] I) :=
  curry <| (ρ_ _).hom

variable {I}
/-
**CategoryTheory.toUnit_comp_curryRightUnitorHom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：toUnit_comp_curryRightUnitorHom {A : C} : toUnit A ≫ curryRightUnitorHom I
 = curry (fst I A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toUnit_comp_curryRightUnitorHom {A : C} :
    toUnit A ≫ curryRightUnitorHom I = curry (fst I A) := by
  apply uncurry_injective
  simp [uncurry_natural_left, curryRightUnitorHom, fst_def, toUnit]

namespace Over

open ChosenPullbacksAlong

variable (I) [ChosenPullbacksAlong (curryRightUnitorHom I)]

/-- The functor mapping an object `X : Over I` to the object of sections of `X` over `I`, defined
by the following pullback diagram. The functor's mapping of morphisms is induced by `pullbackMap`,
that is by the universal property of chosen pullbacks.

```
 sections X -->  I ⟹ X
   |               |
   |               |
   v               v
  𝟙_ C   ----->  I ⟹ I
```
-/
@[simps]
/-
**CategoryTheory.Over.sections** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：sections : Over I ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor mapping an object `X : Over I` to the object of sections of `X` over
 `I`, defined
by the following pullback diagram. The functor's mapping of morphisms is induced
 by `pullbackMap`,
that is by the universal property of chosen pullbacks.

```
 sections X -->  I ⟹ X
   |               |
   |               |
   v               v
  𝟙_ C   ----->  I ⟹ I
```
-/
def sections : Over I ⥤ C where
  obj X := pullbackObj (ihom I |>.map X.hom) (curryRightUnitorHom I)
  map u := pullbackMap _ _ _ _ (ihom I |>.map u.left) (𝟙 _) (𝟙 _)
    (by simp [← Functor.map_comp]) (by cat_disch)

variable {I}

open ChosenPullbacksAlong

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The currying operation `Hom ((toOver I).obj A) X → Hom A (I ⟹ X.left)`. -/
/-
**CategoryTheory.Over.sectionsCurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ov
er`。
形式化陈述：sectionsCurry {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) : A ⟶ (secti
ons I).obj X
参数：u : (toOver I).obj A ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The currying operation `Hom ((toOver I).obj A) X → Hom A (I ⟹ X.left)`.
-/
def sectionsCurry {X : Over I} {A : C} (u : (toOver I).obj A ⟶ X) :
    A ⟶ (sections I).obj X :=
  ChosenPullbacksAlong.lift (curry ((β_ I A).hom ≫ u.left)) (toUnit A) (by
    rw [curry_natural_right, Category.assoc, ← Functor.map_comp, w,
      ← curry_natural_right, toUnit_comp_curryRightUnitorHom]
    congr
    simp [braiding_hom_snd])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The uncurrying operation `Hom A (section X) → Hom ((toOver I).obj A) X`. -/
/-
**CategoryTheory.Over.sectionsUncurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) : (toOve
r I).obj A ⟶ X
参数：v : A ⟶ (sections I).obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uncurrying operation `Hom A (section X) → Hom ((toOver I).obj A) X`.
-/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (toOver I).obj A ⟶ X :=
  letI v₂ : A ⟶ (I ⟶[C] X.left) := v ≫ fst (ihom I |>.map X.hom) (curryRightUnitorHom I)
  Over.homMk ((β_ A I).hom ≫ uncurry v₂) (by
    have comm : toUnit A ≫ (curryRightUnitorHom I) = v₂ ≫ (ihom I).map X.hom := by
      rw [IsTerminal.hom_ext isTerminalTensorUnit (toUnit A) (v ≫ snd ..)]
      simp [v₂, condition]
    dsimp [curryRightUnitorHom] at comm
    have w' := (ihom.adjunction I).homEquiv_naturality_right_square _ _ _ _ comm
    simp only [curriedTensor_obj_obj, curriedTensor_obj_map, curry,
      Equiv.symm_apply_apply] at w'
    dsimp [uncurry] at *
    rw [Category.assoc, ← w', whiskerLeft_toUnit_comp_rightUnitor_hom, braiding_hom_fst])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Over.sectionsCurry_sectionUncurry** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Over`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {I : C} [inst_2 : CategoryTheory.Close
d I]   [inst_3 : CategoryTheory.ChosenPullbacksAlong (CategoryTheory.curryRightU
nitorHom I)]   [inst_4 : CategoryTheory.BraidedCategory C] {X : CategoryTheory.O
ver I} {A : C}   {v : A ⟶ (CategoryTheory.Over.sections I).obj X},   CategoryThe
ory.Over.sectionsCurry (CategoryTheory.Over.sectionsUncurry v) = v
参数：CategoryTheory.curryRightUnitorHom I；CategoryTheory.Over.sections I；CategoryT
heory.Over.sectionsUncurry v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `CategoryTheory.MonoidalClosed.curry_uncurry`：curry_uncurry (f : X ⟶ A ⟶[
C] Y) : curry (uncurry f) = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.lift.congr_simp`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {Y Z X : C} {f : Y ⟶ X} {g : Z ⟶ X}   [
inst_1 : CategoryTheory.ChosenPullbacksAl…
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.hom_ext`：hom_ext {W : C} {φ₁ φ₂ : W 
⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _) (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ 
snd _ _) : φ₁ = φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.lift_fst`：lift_fst : lift a b h ≫ fs
t f g = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
theorem sectionsCurry_sectionUncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Over.sectionsUncurry_sectionsCurry** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Over`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {I : C} [inst_2 : CategoryTheory.Close
d I]   [inst_3 : CategoryTheory.ChosenPullbacksAlong (CategoryTheory.curryRightU
nitorHom I)]   [inst_4 : CategoryTheory.BraidedCategory C] {X : CategoryTheory.O
ver I} {A : C}   {u : (CategoryTheory.toOver I).obj A ⟶ X},   CategoryTheory.Ove
r.sectionsUncurry (CategoryTheory.Over.sectionsCurry u) = u
参数：CategoryTheory.curryRightUnitorHom I；CategoryTheory.toOver I；CategoryTheory.O
ver.sectionsCurry u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.homMk.congr_simp`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X}   (f f_1 : U.lef
t ⟶ V.left) (e_f : f = f_1…
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.lift_fst`：lift_fst : lift a b h ≫ fs
t f g = a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sectionsUncurry_sectionsCurry {X : Over I} {A : C} {u : (toOver I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

open Adjunction

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See `starSectionsAdjunction`. -/
@[simps homEquiv]
/-
**CategoryTheory.Over.coreHomEquivToOverSections** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Over`。
形式化陈述：coreHomEquivToOverSections : CoreHomEquiv (toOver I) (sections I) where ho
mEquiv A X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.sectionsUncurry_sectionsCurry`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoida
lCategory C]   {I : C} [inst_2 : Catego…
· 使用定理 `CategoryTheory.Over.sectionsCurry_sectionUncurry`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidal
Category C]   {I : C} [inst_2 : Catego…

--- 原说明 ---
An auxiliary definition which is used to define the adjunction between the star 
functor
and the sections functor. See `starSectionsAdjunction`.
-/
def coreHomEquivToOverSections : CoreHomEquiv (toOver I) (sections I) where
  homEquiv A X :=
    { toFun := sectionsCurry
      invFun := sectionsUncurry
      left_inv {u} := sectionsUncurry_sectionsCurry
      right_inv {v} := sectionsCurry_sectionUncurry }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    simp only [toOver_map]
    rw [← Over.homMk_comp]
    congr 1
    simp [uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryRightUnitorHom]
    apply ChosenPullbacksAlong.hom_ext
    · simp [← curry_natural_right]
    · simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction between the toOver functor and the sections functor. -/
@[simps! unit_app counit_app]
/-
**CategoryTheory.Over.toOverSectionsAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Over`。
形式化陈述：toOverSectionsAdj : toOver I ⊣ sections I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the toOver functor and the sections functor.
-/
def toOverSectionsAdj : toOver I ⊣ sections I :=
  .mkOfHomEquiv (coreHomEquivToOverSections I)

end Over

end Sections

end CategoryTheory

