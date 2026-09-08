/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# The shift induced on a localized category

Let `C` be a category equipped with a shift by a monoid `A`. A morphism property `W`
on `C` satisfies `W.IsCompatibleWithShift A` when for all `a : A`,
a morphism `f` is in `W` iff `f⟦a⟧'` is. When this compatibility is satisfied,
then the corresponding localized category can be equipped with
a shift by `A`, and the localization functor is compatible with the shift.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (A : Type w) [AddMonoid A] [HasShift C A]

namespace MorphismProperty

/-- A morphism property `W` on a category `C` is compatible with the shift by a
monoid `A` when for all `a : A`, a morphism `f` belongs to `W`
if and only if `f⟦a⟧'` does. -/
/-
**CategoryTheory.MorphismProperty.IsCompatibleWithShift** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     Catego
ryTheory.MorphismProperty C → (A : Type w) → [inst_1 : AddMonoid A] → [CategoryT
heory.HasShift C A] → Prop
参数：A : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property `W` on a category `C` is compatible with the shift by a
monoid `A` when for all `a : A`, a morphism `f` belongs to `W`
if and only if `f⟦a⟧'` does.
-/
class IsCompatibleWithShift : Prop where
  /-- the condition that for all `a : A`, the morphism property `W` is not changed when
  we take its inverse image by the shift functor by `a` -/
  condition : ∀ (a : A), W.inverseImage (shiftFunctor C a) = W

variable [W.IsCompatibleWithShift A]

namespace IsCompatibleWithShift

variable {A}

/-
**CategoryTheory.MorphismProperty.IsCompatibleWithShift.iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty.IsCompatibleWithShift`。
形式化陈述：iff {X Y : C} (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f
参数：f : X ⟶ Y；a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.IsCompatibleWithShift.condition`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {W : CategoryTheory.Morphis
mProperty C} {A : Type w}   {inst_1 : AddMonoid A} {i…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iff {X Y : C} (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f := by
  conv_rhs => rw [← @IsCompatibleWithShift.condition _ _ W A _ _ _ a]
  rfl
/-
**CategoryTheory.MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_invert
s** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsCompatibleWithShi
ft`。
形式化陈述：shiftFunctor_comp_inverts (a : A) : W.IsInvertedBy (shiftFunctor C a ⋙ L)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
-/
lemma shiftFunctor_comp_inverts (a : A) :
    W.IsInvertedBy (shiftFunctor C a ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)

end IsCompatibleWithShift

variable {A} in
/-
**CategoryTheory.MorphismProperty.shift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MorphismProperty`。
形式化陈述：shift {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A) : W (f⟦a⟧')
参数：hf : W f；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsCompatibleWithShift.iff`：iff {X Y : C}
 (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f
-/
lemma shift {X Y : C} {f : X ⟶ Y} (hf : W f) (a : A) : W (f⟦a⟧') := by
  simpa only [IsCompatibleWithShift.iff W f a] using hf

variable {A} in
/-- The morphism of localizer from `W` to `W` given by the functor `shiftFunctor C a`
when `a : A` and `W` is compatible with the shift by `A`. -/
/-
**CategoryTheory.MorphismProperty.shiftLocalizerMorphism** 是 Mathlib 中的一个缩写定义，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：shiftLocalizerMorphism (a : A) : LocalizerMorphism W W where functor
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of localizer from `W` to `W` given by the functor `shiftFunctor C a
`
when `a : A` and `W` is compatible with the shift by `A`.
-/
abbrev shiftLocalizerMorphism (a : A) : LocalizerMorphism W W where
  functor := shiftFunctor C a
  map := by rw [MorphismProperty.IsCompatibleWithShift.condition]

end MorphismProperty

section
variable [W.IsCompatibleWithShift A]

/-- When `L : C ⥤ D` is a localization functor with respect to a morphism property `W`
that is compatible with the shift by a monoid `A` on `C`, this is the induced
shift on the category `D`. -/
@[instance_reducible]
/-
**CategoryTheory.HasShift.localized** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ha
sShift`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (L : Cat
egoryTheory.Functor C D) →           (W : CategoryTheory.MorphismProperty C) →  
           [L.IsLocalization W] →               (A : Type w) →                 [
inst_3 : AddMonoid A] →                   [inst_4 : CategoryTheory.HasShift C A]
 → [W.IsCompatibleWithShift A] → CategoryTheory.HasShift D A
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；A : Type
 w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.full_whiskeringLeft`：full_whiskeringLeft (L 
: C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] : ((whiskeringLeft C
 D E).obj L).Full
· 使用引理 `CategoryTheory.Localization.faithful_whiskeringLeft`：faithful_whiskering
Left (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] : ((whiskeri
ngLeft C D E).obj L).Faithful
· 使用引理 `CategoryTheory.MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_
inverts`：shiftFunctor_comp_inverts (a : A) : W.IsInvertedBy (shiftFunctor C a ⋙ 
L)

--- 原说明 ---
When `L : C ⥤ D` is a localization functor with respect to a morphism property `
W`
that is compatible with the shift by a monoid `A` on `C`, this is the induced
shift on the category `D`.
-/
noncomputable def HasShift.localized : HasShift D A :=
  have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  HasShift.induced L A
    (fun a => Localization.lift (shiftFunctor C a ⋙ L)
      (MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts L W a) L)
    (fun _ => Localization.fac _ _ _)

/-- The localization functor `L : C ⥤ D` is compatible with the shift. -/
@[nolint unusedHavesSuffices, instance_reducible]
/-
**CategoryTheory.Functor.CommShift.localized** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.CommShift`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (L : Cat
egoryTheory.Functor C D) →           (W : CategoryTheory.MorphismProperty C) →  
           [inst_2 : L.IsLocalization W] →               (A : Type w) →         
        [inst_3 : AddMonoid A] →                   [inst_4 : CategoryTheory.HasS
hift C A] → [inst_5 : W.IsCompatibleWithShift A] → L.CommShift A
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；A : Type
 w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.full_whiskeringLeft`：full_whiskeringLeft (L 
: C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] : ((whiskeringLeft C
 D E).obj L).Full
· 使用引理 `CategoryTheory.Localization.faithful_whiskeringLeft`：faithful_whiskering
Left (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] : ((whiskeri
ngLeft C D E).obj L).Faithful
· 使用引理 `CategoryTheory.MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_
inverts`：shiftFunctor_comp_inverts (a : A) : W.IsInvertedBy (shiftFunctor C a ⋙ 
L)

--- 原说明 ---
The localization functor `L : C ⥤ D` is compatible with the shift.
-/
noncomputable def Functor.CommShift.localized :
    @Functor.CommShift _ _ _ _ L A _ _ (HasShift.localized L W A) :=
  have := Localization.full_whiskeringLeft L W D
  have := Localization.faithful_whiskeringLeft L W D
  Functor.CommShift.ofInduced _ _ _ _

attribute [irreducible] HasShift.localized Functor.CommShift.localized

/-- The localized category `W.Localization` is endowed with the induced shift. -/
/-
**CategoryTheory.HasShift.localization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.HasShift`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (W : C
ategoryTheory.MorphismProperty C) →       (A : Type w) →         [inst_1 : AddMo
noid A] →           [inst_2 : CategoryTheory.HasShift C A] →             [W.IsCo
mpatibleWithShift A] → CategoryTheory.HasShift W.Localization A
参数：W : CategoryTheory.MorphismProperty C；A : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localized category `W.Localization` is endowed with the induced shift.
-/
noncomputable instance HasShift.localization :
    HasShift W.Localization A :=
  HasShift.localized W.Q W A

/-- The localization functor `W.Q : C ⥤ W.Localization` is compatible with the shift. -/
/-
**CategoryTheory.MorphismProperty.commShift_Q** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (W : C
ategoryTheory.MorphismProperty C) →       (A : Type w) →         [inst_1 : AddMo
noid A] →           [inst_2 : CategoryTheory.HasShift C A] → [inst_3 : W.IsCompa
tibleWithShift A] → W.Q.CommShift A
参数：W : CategoryTheory.MorphismProperty C；A : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization functor `W.Q : C ⥤ W.Localization` is compatible with the shift
.
-/
noncomputable instance MorphismProperty.commShift_Q :
    W.Q.CommShift A :=
  Functor.CommShift.localized W.Q W A

attribute [irreducible] HasShift.localization MorphismProperty.commShift_Q

variable [W.HasLocalization]

/-- The localized category `W.Localization'` is endowed with the induced shift. -/
/-
**CategoryTheory.HasShift.localization'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.HasShift`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (W : C
ategoryTheory.MorphismProperty C) →       (A : Type w) →         [inst_1 : AddMo
noid A] →           [inst_2 : CategoryTheory.HasShift C A] →             [W.IsCo
mpatibleWithShift A] → [inst_4 : W.HasLocalization] → CategoryTheory.HasShift W.
Localization' A
参数：W : CategoryTheory.MorphismProperty C；A : Type w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instIsLocalizationLocalization'Q'`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C)   [inst_1 : W.HasLocalization], W.Q'.IsLoca…

--- 原说明 ---
The localized category `W.Localization'` is endowed with the induced shift.
-/
noncomputable instance HasShift.localization' :
    HasShift W.Localization' A :=
  HasShift.localized W.Q' W A

/-- The localization functor `W.Q' : C ⥤ W.Localization'` is compatible with the shift. -/
/-
**CategoryTheory.MorphismProperty.commShift_Q'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (W : C
ategoryTheory.MorphismProperty C) →       (A : Type w) →         [inst_1 : AddMo
noid A] →           [inst_2 : CategoryTheory.HasShift C A] →             [inst_3
 : W.IsCompatibleWithShift A] → [inst_4 : W.HasLocalization] → W.Q'.CommShift A
参数：W : CategoryTheory.MorphismProperty C；A : Type w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instIsLocalizationLocalization'Q'`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C)   [inst_1 : W.HasLocalization], W.Q'.IsLoca…

--- 原说明 ---
The localization functor `W.Q' : C ⥤ W.Localization'` is compatible with the shi
ft.
-/
noncomputable instance MorphismProperty.commShift_Q' :
    W.Q'.CommShift A :=
  Functor.CommShift.localized W.Q' W A

attribute [irreducible] HasShift.localization' MorphismProperty.commShift_Q'

end

section

open Localization

variable (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
  [HasShift D A] [HasShift E A] [L.CommShift A] [F.CommShift A]

namespace Functor

namespace commShiftOfLocalization

variable {A}

/-- Auxiliary definition for `Functor.commShiftOfLocalization`. -/
/-
**CategoryTheory.Functor.commShiftOfLocalization.iso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.commShiftOfLocalization`。
形式化陈述：iso (a : A) : shiftFunctor D a ⋙ F' ≅ F' ⋙ shiftFunctor E a
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Functor.commShiftOfLocalization`.
-/
noncomputable def iso (a : A) :
    shiftFunctor D a ⋙ F' ≅ F' ⋙ shiftFunctor E a :=
  Localization.liftNatIso L W (L ⋙ shiftFunctor D a ⋙ F')
    (L ⋙ F' ⋙ shiftFunctor E a) _ _
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (L.commShiftIso a).symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (Lifting.iso L W F F') ≪≫
        F.commShiftIso a ≪≫
        isoWhiskerRight (Lifting.iso L W F F').symm _ ≪≫ Functor.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/-
**CategoryTheory.Functor.commShiftOfLocalization.iso_hom_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor.commShiftOfLocalization`。
形式化陈述：iso_hom_app (a : A) (X : C) : (commShiftOfLocalization.iso L W F F' a).hom
.app (L.obj X) = F'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.iso L W F F').
hom.app (X⟦a⟧) ≫ (F.commShiftIso a).hom.app X ≫ (shiftFunctor E a).map ((Lifting
.iso L W F F').inv.app X)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_hom_app (a : A) (X : C) :
    (commShiftOfLocalization.iso L W F F' a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫
      (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  simp [commShiftOfLocalization.iso]

set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/-
**CategoryTheory.Functor.commShiftOfLocalization.iso_inv_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor.commShiftOfLocalization`。
形式化陈述：iso_inv_app (a : A) (X : C) : (commShiftOfLocalization.iso L W F F' a).inv
.app (L.obj X) = (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫ (F.
commShiftIso a).inv.app X ≫ (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫ F'.map ((L.c
ommShiftIso a).hom.app X)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Localization.liftNatTrans.congr_simp`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_inv_app (a : A) (X : C) :
    (commShiftOfLocalization.iso L W F F' a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫
      (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  simp [commShiftOfLocalization.iso]

end commShiftOfLocalization

set_option backward.defeqAttrib.useBackward true in
/-- In the context of localization of categories, if a functor
is induced by a functor which commutes with the shift, then
this functor commutes with the shift. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.commShiftOfLocalization** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：commShiftOfLocalization : F'.CommShift A where commShiftIso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the context of localization of categories, if a functor
is induced by a functor which commutes with the shift, then
this functor commutes with the shift.
-/
noncomputable def commShiftOfLocalization : F'.CommShift A where
  commShiftIso := commShiftOfLocalization.iso L W F F'
  commShiftIso_zero := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_zero,
      CommShift.isoZero_inv_app, map_comp, CommShift.isoZero_hom_app, Category.assoc,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality]
    dsimp
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, id_obj, map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  commShiftIso_add a b := by
    ext1
    apply natTrans_ext L W
    intro X
    dsimp
    simp only [commShiftOfLocalization.iso_hom_app, comp_obj, commShiftIso_add,
      CommShift.isoAdd_inv_app, map_comp, CommShift.isoAdd_hom_app, Category.assoc]
    congr 1
    rw [← cancel_epi (F'.map ((shiftFunctor D b).map ((L.commShiftIso a).hom.app X))),
      ← F'.map_comp_assoc, ← map_comp, Iso.hom_inv_id_app, map_id, map_id, Category.id_comp]
    conv_lhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc, ← map_comp_assoc, Category.assoc,
        ← map_comp, Iso.inv_hom_id_app]
      dsimp
      rw [map_id, Category.comp_id, ← NatTrans.naturality]
      dsimp
    conv_rhs =>
      erw [← NatTrans.naturality_assoc]
      dsimp
      rw [← Functor.map_comp_assoc, ← map_comp, Iso.hom_inv_id_app]
      dsimp
      rw [map_id, map_id, Category.id_comp, commShiftOfLocalization.iso_hom_app,
        Category.assoc, Category.assoc, Category.assoc, ← map_comp_assoc,
        Iso.inv_hom_id_app, map_id, Category.id_comp]

variable {A}
/-
**CategoryTheory.Functor.commShiftOfLocalization_iso_hom_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：commShiftOfLocalization_iso_hom_app (a : A) (X : C) : letI
参数：a : A；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.commShiftOfLocalization.iso_hom_app`：iso_hom_app 
(a : A) (X : C) : (commShiftOfLocalization.iso L W F F' a).hom.app (L.obj X) = F
'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.…
-/
lemma commShiftOfLocalization_iso_hom_app (a : A) (X : C) :
    letI := Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).hom.app (L.obj X) =
      F'.map ((L.commShiftIso a).inv.app X) ≫ (Lifting.iso L W F F').hom.app (X⟦a⟧) ≫
        (F.commShiftIso a).hom.app X ≫
          (shiftFunctor E a).map ((Lifting.iso L W F F').inv.app X) := by
  apply commShiftOfLocalization.iso_hom_app
/-
**CategoryTheory.Functor.commShiftOfLocalization_iso_inv_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：commShiftOfLocalization_iso_inv_app (a : A) (X : C) : letI
参数：a : A；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.commShiftOfLocalization.iso_inv_app`：iso_inv_app 
(a : A) (X : C) : (commShiftOfLocalization.iso L W F F' a).inv.app (L.obj X) = (
shiftFunctor E a).map ((Lifting.iso L W F F').ho…
-/
lemma commShiftOfLocalization_iso_inv_app (a : A) (X : C) :
    letI := Functor.commShiftOfLocalization L W A F F'
    (F'.commShiftIso a).inv.app (L.obj X) =
      (shiftFunctor E a).map ((Lifting.iso L W F F').hom.app X) ≫
      (F.commShiftIso a).inv.app X ≫ (Lifting.iso L W F F').inv.app (X⟦a⟧) ≫
      F'.map ((L.commShiftIso a).hom.app X) := by
  apply commShiftOfLocalization.iso_inv_app

end Functor

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.NatTrans.commShift_iso_hom_of_localization** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.NatTrans`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (L : CategoryTheory.Functor C D)   (W : CategoryTheo
ry.MorphismProperty C) [inst_3 : L.IsLocalization W] (A : Type w) [inst_4 : AddM
onoid A]   [inst_5 : CategoryTheory.HasShift C A] (F : CategoryTheory.Functor C 
E) (F' : CategoryTheory.Functor D E)   [inst_6 : CategoryTheory.Localization.Lif
ting L W F F'] [inst_7 : CategoryTheory.HasShift D A]   [inst_8 : CategoryTheory
.HasShift E A] [inst_9 : L.CommShift A] [inst_10 : F.CommShift A],   CategoryThe
ory.NatTrans.CommShift (CategoryTheory.Localization.Lifting.iso L W F F').hom A
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；A : Type
 w；F : CategoryTheory.Functor C E；F' : CategoryTheory.Functor D E；CategoryTheory
.Localization.Lifting.iso L W F F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Functor.commShiftOfLocalization_iso_hom_app`：commShiftOfL
ocalization_iso_hom_app (a : A) (X : C) : letI
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance NatTrans.commShift_iso_hom_of_localization :
    letI := Functor.commShiftOfLocalization L W A F F'
    NatTrans.CommShift (Lifting.iso L W F F').hom A := by
  let := Functor.commShiftOfLocalization L W A F F'
  constructor
  intro a
  ext X
  simp only [comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app,
    Functor.commShiftOfLocalization_iso_hom_app,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Iso.inv_hom_id_app,
    Category.comp_id, Category.id_comp, Functor.comp_obj]

end

namespace LocalizerMorphism

open Localization

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂)
  {M : Type*} [AddMonoid M] [HasShift C₁ M] [HasShift C₂ M]
  [Φ.functor.CommShift M]
  {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂)
  [HasShift D₁ M] [HasShift D₂ M] [L₁.CommShift M] [L₂.CommShift M]

section

variable (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)

variable (M) in
/-- This is the commutation of a functor `G` to shifts by an additive monoid `M` when
`e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G` is an isomorphism, `Φ` is a localizer morphism and
`L₁` is a localization functor. We assume that all categories involved
are equipped with shifts and that `L₁`, `L₂` and `Φ.functor` commute to them. -/
@[instance_reducible]
/-
**CategoryTheory.LocalizerMorphism.commShift** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.LocalizerMorphism`。
形式化陈述：commShift : G.CommShift M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the commutation of a functor `G` to shifts by an additive monoid `M` whe
n
`e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G` is an isomorphism, `Φ` is a localizer morphism and
`L₁` is a localization functor. We assume that all categories involved
are equipped with shifts and that `L₁`, `L₂` and `Φ.functor` commute to them.
-/
noncomputable def commShift : G.CommShift M := by
  letI : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  exact Functor.commShiftOfLocalization L₁ W₁ M (Φ.functor ⋙ L₂) G

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.LocalizerMorphism.commShift_iso_hom_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：commShift_iso_hom_app (m : M) (X : C₁) : letI
参数：m : M；X : C₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.commShiftOfLocalization_iso_hom_app`：commShiftOfL
ocalization_iso_hom_app (a : A) (X : C) : letI
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commShift_iso_hom_app (m : M) (X : C₁) :
    letI := Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).hom.app (L₁.obj X) =
      G.map ((L₁.commShiftIso m).inv.app X) ≫ e.inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).hom.app X) ≫
        (L₂.commShiftIso m).hom.app _ ≫ (e.hom.app X)⟦m⟧' := by
  simp [Functor.commShiftOfLocalization_iso_hom_app,
    Functor.commShiftIso_comp_hom_app]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.LocalizerMorphism.commShift_iso_inv_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：commShift_iso_inv_app (m : M) (X : C₁) : letI
参数：m : M；X : C₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.commShiftOfLocalization_iso_inv_app`：commShiftOfL
ocalization_iso_inv_app (a : A) (X : C) : letI
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_inv_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commShift_iso_inv_app (m : M) (X : C₁) :
    letI := Φ.commShift M L₁ L₂ G e
    (G.commShiftIso m).inv.app (L₁.obj X) =
      (e.inv.app X)⟦m⟧' ≫ (L₂.commShiftIso m).inv.app _ ≫
        L₂.map ((Φ.functor.commShiftIso m).inv.app X) ≫ e.hom.app _ ≫
          G.map ((L₁.commShiftIso m).hom.app X) := by
  simp [Functor.commShiftOfLocalization_iso_inv_app,
    Functor.commShiftIso_comp_inv_app]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.natTransCommShift_hom** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：natTransCommShift_hom : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.LocalizerMorphism.commShift_iso_hom_app`：commShift_iso_ho
m_app (m : M) (X : C₁) : letI
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natTransCommShift_hom :
    letI := Φ.commShift M L₁ L₂ G e
    NatTrans.CommShift e.hom M := by
  let := Φ.commShift M L₁ L₂ G e
  refine ⟨fun m ↦ ?_⟩
  ext X
  simp [Functor.commShiftIso_comp_hom_app, commShift_iso_hom_app, ← Functor.map_comp_assoc]

end

variable [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M]
  [L₂.IsLocalization W₂]

/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (Φ.localizedFunctor L₁ L₂).CommShift M :=
  Φ.commShift M L₁ L₂ _ (CatCommSq.iso ..)
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    NatTrans.CommShift (CatCommSq.iso Φ.functor W₁.Q W₂.Q
      (Φ.localizedFunctor W₁.Q W₂.Q)).hom M :=
  natTransCommShift_hom ..

end LocalizerMorphism

end CategoryTheory

