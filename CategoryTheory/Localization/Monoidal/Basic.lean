/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Trifunctor
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Localization of monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure: this means `W`
is multiplicative and stable by left and right whiskerings (this is
the type class `W.IsMonoidal`). Let `L : C ⥤ D` be a localization functor
for `W`. In the file, we construct a monoidal category structure
on `D` such that the localization functor is monoidal. The structure
is actually defined on a type synonym `LocalizedMonoidal L W ε`.
Here, the data `ε : L.obj (𝟙_ C) ≅ unit` is an isomorphism to some
object `unit : D` which allows the user to provide a preferred choice
of a unit object.

The symmetric case is considered in the file
`Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

namespace MorphismProperty

/-- A class of morphisms `W` in a monoidal category is monoidal if it is multiplicative
and stable under left and right whiskering. Under this condition, the localized
category can be equipped with a monoidal category structure, see `LocalizedMonoidal`. -/
/-
**CategoryTheory.MorphismProperty.IsMonoidal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C → [CategoryTheory.MonoidalCategory C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W` in a monoidal category is monoidal if it is multiplicat
ive
and stable under left and right whiskering. Under this condition, the localized
category can be equipped with a monoidal category structure, see `LocalizedMonoi
dal`.
-/
class IsMonoidal : Prop extends W.IsMultiplicative where
  whiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)

/-- Alternative constructor for `W.IsMonoidal` given that `W` is multiplicative and stable under
tensoring morphisms. -/
/-
**CategoryTheory.MorphismProperty.IsMonoidal.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty.IsMonoidal`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Catego
ryTheory.MorphismProperty C)   [inst_1 : CategoryTheory.MonoidalCategory C] [W.I
sMultiplicative],   (∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂),       W f 
→ W g → W (CategoryTheory.MonoidalCategoryStruct.tensorHom f g)) →     W.IsMonoi
dal
参数：W : CategoryTheory.MorphismProperty C；∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : 
Y₁ ⟶ Y₂),       W f → W g → W (CategoryTheory.MonoidalCategoryStruct.tensorHom f
 g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y

--- 原说明 ---
Alternative constructor for `W.IsMonoidal` given that `W` is multiplicative and 
stable under
tensoring morphisms.
-/
lemma IsMonoidal.mk' [W.IsMultiplicative]
    (h : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (_ : W f) (_ : W g), W (f ⊗ₘ g)) :
    W.IsMonoidal where
  whiskerLeft X _ _ g hg := by simpa using h (𝟙 X) g (W.id_mem _) hg
  whiskerRight f hf Y := by simpa using h f (𝟙 Y) hf (W.id_mem _)

variable [W.IsMonoidal]
/-
**CategoryTheory.MorphismProperty.whiskerLeft_mem** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
参数：X : C；g : Y₁ ⟶ Y₂；hg : W g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMonoidal.whiskerLeft`：∀ {C : Type u_1}
 {inst : CategoryTheory.Category.{v_1, u_1} C} {W : CategoryTheory.MorphismPrope
rty C}   {inst_1 : CategoryTheory.MonoidalCa…
-/
lemma whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g) :=
  IsMonoidal.whiskerLeft _ _ hg
/-
**CategoryTheory.MorphismProperty.whiskerRight_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)
参数：f : X₁ ⟶ X₂；hf : W f；Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMonoidal.whiskerRight`：∀ {C : Type u_1
} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : CategoryTheory.MorphismProp
erty C}   {inst_1 : CategoryTheory.MonoidalCa…
-/
lemma whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y) :=
  IsMonoidal.whiskerRight _ hf Y
/-
**CategoryTheory.MorphismProperty.tensorHom_mem** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hf : W 
f) (hg : W g) : W (f otimesₘ g)
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂；hf : W f；hg : W g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.IsMonoidal.toIsMultiplicative`：∀ {C : Ty
pe u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : CategoryTheory.Morphi
smProperty C}   {inst_1 : CategoryTheory.MonoidalCa…
· 使用引理 `CategoryTheory.MorphismProperty.whiskerRight_mem`：whiskerRight_mem {X₁ X
₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)
· 使用引理 `CategoryTheory.MorphismProperty.whiskerLeft_mem`：whiskerLeft_mem (X : C)
 {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
-/
lemma tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (hf : W f) (hg : W g) : W (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

/-- The inverse image under a monoidal functor of a monoidal morphism property which respects
isomorphisms is monoidal. -/
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse image under a monoidal functor of a monoidal morphism property which
 respects
isomorphisms is monoidal.
-/
instance {C' : Type*} [Category* C'] [MonoidalCategory C'] (F : C' ⥤ C) [F.Monoidal]
    [W.RespectsIso] : (W.inverseImage F).IsMonoidal := .mk' _ fun f g hf hg ↦ by
  simp only [inverseImage_iff] at hf hg ⊢
  rw [Functor.Monoidal.map_tensor _ f g]
  apply MorphismProperty.RespectsIso.precomp
  apply MorphismProperty.RespectsIso.postcomp
  exact tensorHom_mem _ _ _ hf hg

end MorphismProperty

/-- Given a monoidal category `C`, a localization functor `L : C ⥤ D` with respect
to `W : MorphismProperty C` which satisfies `W.IsMonoidal`, and a choice
of object `unit : D` with an isomorphism `L.obj (𝟙_ C) ≅ unit`, this is a
type synonym for `D` on which we define the localized monoidal category structure. -/
@[nolint unusedArguments]
/-
**CategoryTheory.LocalizedMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：LocalizedMonoidal (L : C ⥤ D) (W : MorphismProperty C) [W.IsMonoidal] [L.I
sLocalization W] {unit : D} (_ : L.obj (𝟙_ C) ≅ unit)
参数：L : C ⥤ D；W : MorphismProperty C；_ : L.obj (𝟙_ C) ≅ unit。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoidal category `C`, a localization functor `L : C ⥤ D` with respect
to `W : MorphismProperty C` which satisfies `W.IsMonoidal`, and a choice
of object `unit : D` with an isomorphism `L.obj (𝟙_ C) ≅ unit`, this is a
type synonym for `D` on which we define the localized monoidal category structur
e.
-/
def LocalizedMonoidal (L : C ⥤ D) (W : MorphismProperty C)
    [W.IsMonoidal] [L.IsLocalization W] {unit : D} (_ : L.obj (𝟙_ C) ≅ unit) :=
  D

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

namespace Localization

/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (LocalizedMonoidal L W ε) :=
  inferInstanceAs (Category D)

namespace Monoidal

/-- The monoidal functor from a monoidal category `C` to
its localization `LocalizedMonoidal L W ε`. -/
/-
**CategoryTheory.Localization.Monoidal.toMonoidalCategory** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：toMonoidalCategory : C ⥤ LocalizedMonoidal L W ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal functor from a monoidal category `C` to
its localization `LocalizedMonoidal L W ε`.
-/
def toMonoidalCategory : C ⥤ LocalizedMonoidal L W ε := L

/-- The isomorphism `ε : L.obj (𝟙_ C) ≅ unit`,
as `(toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit`. -/
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `ε : L.obj (𝟙_ C) ≅ unit`,
as `(toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit`.
-/
abbrev ε' : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit := ε

local notation "L'" => toMonoidalCategory L W ε
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.isInvertedBy** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isInvertedBy₂ :
    MorphismProperty.IsInvertedBy₂ W W
      (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L') := by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The localized tensor product, as a bifunctor. -/
/-
**CategoryTheory.Localization.Monoidal.tensorBifunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Localization.Monoidal`。
形式化陈述：tensorBifunctor : LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε ⥤ Loca
lizedMonoidal L W ε
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.Monoidal.isInvertedBy₂`：isInvertedBy₂ : Morp
hismProperty.IsInvertedBy₂ W W (curriedTensor C ⋙ (Functor.whiskeringRight C C D
).obj L')

--- 原说明 ---
The localized tensor product, as a bifunctor.
-/
noncomputable def tensorBifunctor :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε :=
  Localization.lift₂ _ (isInvertedBy₂ L W ε) L L
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Lifting₂ L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε) :=
  inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

/-- The bifunctor `tensorBifunctor` on `LocalizedMonoidal L W ε` is induced by
`curriedTensor C`. -/
/-
**CategoryTheory.Localization.Monoidal.tensorBifunctorIso** 是 Mathlib 中的一个缩写定义，位
于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：tensorBifunctorIso : (((Functor.whiskeringLeft₂ D).obj L').obj L').obj (te
nsorBifunctor L W ε) ≅ (Functor.postcompose₂.obj L').obj (curriedTensor C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifunctor `tensorBifunctor` on `LocalizedMonoidal L W ε` is induced by
`curriedTensor C`.
-/
noncomputable abbrev tensorBifunctorIso :
    (((Functor.whiskeringLeft₂ D).obj L').obj L').obj (tensorBifunctor L W ε) ≅
      (Functor.postcompose₂.obj L').obj (curriedTensor C) :=
  Lifting₂.iso L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (X : C) :
    Lifting L' W (tensorLeft X ⋙ L') ((tensorBifunctor L W ε).obj ((L').obj X)) := by
  apply Lifting₂.liftingLift₂ (hF := isInvertedBy₂ L W ε)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (Y : C) :
    Lifting L' W (tensorRight Y ⋙ L') ((tensorBifunctor L W ε).flip.obj ((L').obj Y)) := by
  apply Lifting₂.liftingLift₂Flip (hF := isInvertedBy₂ L W ε)

/-- The left unitor in the localized monoidal category `LocalizedMonoidal L W ε`. -/
/-
**CategoryTheory.Localization.Monoidal.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Localization.Monoidal`。
形式化陈述：leftUnitor : (tensorBifunctor L W ε).obj unit ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…

--- 原说明 ---
The left unitor in the localized monoidal category `LocalizedMonoidal L W ε`.
-/
noncomputable def leftUnitor : (tensorBifunctor L W ε).obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorLeft (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- The right unitor in the localized monoidal category `LocalizedMonoidal L W ε`. -/
/-
**CategoryTheory.Localization.Monoidal.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Localization.Monoidal`。
形式化陈述：rightUnitor : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…

--- 原说明 ---
The right unitor in the localized monoidal category `LocalizedMonoidal L W ε`.
-/
noncomputable def rightUnitor : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).flip.obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

/-- The associator in the localized monoidal category `LocalizedMonoidal L W ε`. -/
/-
**CategoryTheory.Localization.Monoidal.associator** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Localization.Monoidal`。
形式化陈述：associator : bifunctorComp₁₂ (tensorBifunctor L W ε) (tensorBifunctor L W 
ε) ≅ bifunctorComp₂₃ (tensorBifunctor L W ε) (tensorBifunctor L W ε)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…

--- 原说明 ---
The associator in the localized monoidal category `LocalizedMonoidal L W ε`.
-/
noncomputable def associator :
    bifunctorComp₁₂ (tensorBifunctor L W ε) (tensorBifunctor L W ε) ≅
      bifunctorComp₂₃ (tensorBifunctor L W ε) (tensorBifunctor L W ε) :=
  Localization.associator L' L' L' L' L' L' W W W W W
    (curriedAssociatorNatIso C) (tensorBifunctor L W ε) (tensorBifunctor L W ε)
    (tensorBifunctor L W ε) (tensorBifunctor L W ε)
/-
**CategoryTheory.Localization.Monoidal.monoidalCategoryStruct** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：monoidalCategoryStruct : MonoidalCategoryStruct (LocalizedMonoidal L W ε) 
where tensorObj X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (LocalizedMonoidal L W ε) where
  tensorObj X Y := ((tensorBifunctor L W ε).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W ε).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W ε).map f).app Y
  tensorUnit := unit
  associator X Y Z := (((associator L W ε).app X).app Y).app Z
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

/-- The compatibility isomorphism of the monoidal functor `toMonoidalCategory L W ε`
with respect to the tensor product. -/
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compatibility isomorphism of the monoidal functor `toMonoidalCategory L W ε`
with respect to the tensor product.
-/
noncomputable def μ (X Y : C) : (L').obj X ⊗ (L').obj Y ≅ (L').obj (X ⊗ Y) :=
  ((tensorBifunctorIso L W ε).app X).app Y

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (L').map f ▷ (L').obj Y ≫ (μ L W ε X₂ Y).hom =
      (μ L W ε X₁ Y).hom ≫ (L').map (f ▷ Y) :=
  NatTrans.naturality_app (tensorBifunctorIso L W ε).hom Y f

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_inv_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (μ L W ε X₁ Y).inv ≫ (L').map f ▷ (L').obj Y =
      (L').map (f ▷ Y) ≫ (μ L W ε X₂ Y).inv := by
  simp [Iso.eq_comp_inv]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (L').obj X ◁ (L').map g ≫ (μ L W ε X Y₂).hom =
      (μ L W ε X Y₁).hom ≫ (L').map (X ◁ g) :=
  ((tensorBifunctorIso L W ε).hom.app X).naturality g

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_inv_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (μ L W ε X Y₁).inv ≫ (L').obj X ◁ (L').map g =
      (L').map (X ◁ g) ≫ (μ L W ε X Y₂).inv := by
  simp [Iso.eq_comp_inv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.leftUnitor_hom_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：leftUnitor_hom_app (Y : C) : (fun_ ((L').obj Y)).hom = (ε' L W ε).inv ▷ (L
').obj Y ≫ (μ _ _ _ _ _).hom ≫ (L').map (fun_ Y).hom
参数：Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_hom_app (Y : C) :
    (λ_ ((L').obj Y)).hom =
      (ε' L W ε).inv ▷ (L').obj Y ≫ (μ _ _ _ _ _).hom ≫ (L').map (λ_ Y).hom := by
  dsimp +instances [monoidalCategoryStruct, leftUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.rightUnitor_hom_app** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：rightUnitor_hom_app (X : C) : (ρ_ ((L').obj X)).hom = (L').obj X ◁ (ε' L W
 ε).inv ≫ (μ _ _ _ _ _).hom ≫ (L').map (ρ_ X).hom
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_hom_app (X : C) :
    (ρ_ ((L').obj X)).hom =
      (L').obj X ◁ (ε' L W ε).inv ≫ (μ _ _ _ _ _).hom ≫
        (L').map (ρ_ X).hom := by
  dsimp +instances [monoidalCategoryStruct, rightUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Localization.Monoidal.associator_hom_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：associator_hom_app (X₁ X₂ X₃ : C) : (α_ ((L').obj X₁) ((L').obj X₂) ((L').
obj X₃)).hom = ((μ L W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom ≫ (L').map (α
_ X₁ X₂ X₃).hom ≫ (μ L W ε _ _).inv ≫ (𝟙 _ otimesₘ (μ L W ε _ _).inv)
参数：X₁ X₂ X₃ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Localization.associator_hom_app_app_app`：associator_hom_a
pp_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) : (((associator L₁ L₂ L₃ L₁₂ L₂₃ L W₁ W
₂ W₃ W₁₂ W₂₃ iso F₁₂' G' F' G₂₃').hom.app (L…
-/
lemma associator_hom_app (X₁ X₂ X₃ : C) :
    (α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom =
      ((μ L W ε _ _).hom ⊗ₘ 𝟙 _) ≫ (μ L W ε _ _).hom ≫ (L').map (α_ X₁ X₂ X₃).hom ≫
        (μ L W ε _ _).inv ≫ (𝟙 _ ⊗ₘ (μ L W ε _ _).inv) := by
  dsimp +instances [monoidalCategoryStruct, associator]
  simp only [Functor.map_id, comp_id, NatTrans.id_app, id_comp]
  rw [Localization.associator_hom_app_app_app]
  rfl
/-
**CategoryTheory.Localization.Monoidal.id_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
形式化陈述：id_tensorHom (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W 
ε} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
参数：X : LocalizedMonoidal L W ε；f : Y₁ ⟶ Y₂。
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
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_tensorHom (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ₘ f = X ◁ f := by
  simp +instances [monoidalCategoryStruct]
/-
**CategoryTheory.Localization.Monoidal.tensorHom_id** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
形式化陈述：tensorHom_id {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : Localize
dMonoidal L W ε) : f otimesₘ 𝟙 Y = f ▷ Y
参数：f : X₁ ⟶ X₂；Y : LocalizedMonoidal L W ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_id {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε) :
    f ⊗ₘ 𝟙 Y = f ▷ Y := by
  simp +instances [monoidalCategoryStruct]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.tensor_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Localization.Monoidal`。
形式化陈述：tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁) (
f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂) = (f₁ 
otimesₘ f₂) ≫ (g₁ otimesₘ g₂)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；g₁ : Y₁ ⟶ Z₁；g₂ : Y₂ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) = (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) := by
  simp +instances [monoidalCategoryStruct]
/-
**CategoryTheory.Localization.Monoidal.id_tensorHom_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Localization.Monoidal`。
形式化陈述：id_tensorHom_id (X₁ X₂ : LocalizedMonoidal L W ε) : 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 
(X₁ otimes X₂)
参数：X₁ X₂ : LocalizedMonoidal L W ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_tensorHom_id (X₁ X₂ : LocalizedMonoidal L W ε) : 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by
  simp +instances [monoidalCategoryStruct]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.whiskerLeft_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：whiskerLeft_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal 
L W ε} (f : X ⟶ Y) (g : Y ⟶ Z) : Q ◁ (f ≫ g) = Q ◁ f ≫ Q ◁ g
参数：Q : LocalizedMonoidal L W ε；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Q ◁ (f ≫ g) = Q ◁ f ≫ Q ◁ g := by
  simp only [← id_tensorHom, ← tensor_comp, comp_id]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.whiskerRight_comp** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：whiskerRight_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal
 L W ε} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) ▷ Q = f ▷ Q ≫ g ▷ Q
参数：Q : LocalizedMonoidal L W ε；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g) ▷ Q = f ▷ Q ≫ g ▷ Q := by
  simp only [← tensorHom_id, ← tensor_comp, comp_id]
/-
**CategoryTheory.Localization.Monoidal.whiskerLeft_id** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Localization.Monoidal`。
形式化陈述：whiskerLeft_id (X Y : LocalizedMonoidal L W ε) : X ◁ (𝟙 Y) = 𝟙 _
参数：X Y : LocalizedMonoidal L W ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_id (X Y : LocalizedMonoidal L W ε) :
    X ◁ (𝟙 Y) = 𝟙 _ := by
  simp +instances [monoidalCategoryStruct]
/-
**CategoryTheory.Localization.Monoidal.whiskerRight_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Localization.Monoidal`。
形式化陈述：whiskerRight_id (X Y : LocalizedMonoidal L W ε) : (𝟙 X) ▷ Y = 𝟙 _
参数：X Y : LocalizedMonoidal L W ε。
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
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_id (X Y : LocalizedMonoidal L W ε) :
    (𝟙 X) ▷ Y = 𝟙 _ := by
  simp +instances [monoidalCategoryStruct]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.whisker_exchange** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：whisker_exchange {Q X Y Z : LocalizedMonoidal L W ε} (f : Q ⟶ X) (g : Y ⟶ 
Z) : Q ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
参数：f : Q ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whisker_exchange {Q X Y Z : LocalizedMonoidal L W ε} (f : Q ⟶ X) (g : Y ⟶ Z) :
    Q ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.associator_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε} (f₁ : 
X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y
₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ f₂ otimesₘ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ f₂ ⊗ₘ f₃) := by
  have h₁ := (((associator L W ε).hom.app Y₁).app Y₂).naturality f₃
  have h₂ := NatTrans.congr_app (((associator L W ε).hom.app Y₁).naturality f₂) X₃
  have h₃ := NatTrans.congr_app (NatTrans.congr_app ((associator L W ε).hom.naturality f₁) X₂) X₃
  simp +instances only [monoidalCategoryStruct, Functor.map_comp, assoc]
  dsimp at h₁ h₂ h₃ ⊢
  rw [h₁, assoc, reassoc_of% h₂, reassoc_of% h₃]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.associator_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε} (f₁ : 
X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y
₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ f₂ otimesₘ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma associator_naturality₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁) :
    ((f₁ ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ▷ (X₂ ⊗ X₃)) := by
  simp only [← tensorHom_id, associator_naturality, id_tensorHom_id]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.associator_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε} (f₁ : 
X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y
₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ f₂ otimesₘ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma associator_naturality₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (f₂ : X₂ ⟶ Y₂) :
    ((X₁ ◁ f₂) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (f₂ ▷ X₃)) := by
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality]

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.associator_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε} (f₁ : 
X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y
₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ f₂ otimesₘ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma associator_naturality₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (f₃ : X₃ ⟶ Y₃) :
    ((X₁ ⊗ X₂) ◁ f₃) ≫ (α_ X₁ X₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (X₂ ◁ f₃)) := by
  simp only [← id_tensorHom, ← id_tensorHom_id, associator_naturality]
/-
**CategoryTheory.Localization.Monoidal.pentagon_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pentagon_aux₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (i : X₁ ≅ Y₁) :
    ((i.hom ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom ≫ (i.inv ▷ (X₂ ⊗ X₃)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₁_assoc, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, comp_id]
/-
**CategoryTheory.Localization.Monoidal.pentagon_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pentagon_aux₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (i : X₂ ≅ Y₂) :
    ((X₁ ◁ i.hom) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom ≫ (X₁ ◁ (i.inv ▷ X₃)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₂_assoc, ← whiskerLeft_comp, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, whiskerLeft_id, comp_id]
/-
**CategoryTheory.Localization.Monoidal.pentagon_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pentagon_aux₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (i : X₃ ≅ Y₃) :
    ((X₁ ⊗ X₂) ◁ i.hom) ≫ (α_ X₁ X₂ Y₃).hom ≫ (X₁ ◁ (X₂ ◁ i.inv)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₃_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, comp_id]
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (L').EssSurj := Localization.essSurj L' W

variable {L W ε} in
/-
**CategoryTheory.Localization.Monoidal.pentagon** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Localization.Monoidal`。
形式化陈述：pentagon (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε) : Pentagon Y₁ Y₂ Y₃ Y₄
参数：Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instEssSurjLocalizedMonoidalToMonoi
dalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_
1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Localization.Monoidal.pentagon_aux₂`：pentagon_aux₂ {X₁ X₂
 X₃ Y₂ : LocalizedMonoidal L W ε} (i : X₂ ≅ Y₂) : ((X₁ ◁ i.hom) ▷ X₃) ≫ (α_ X₁ Y
₂ X₃).hom ≫ (X₁ ◁ (i.inv ▷ X₃)) = (α_ X₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.Monoidal.associator_hom_app`：associator_hom_
app (X₁ X₂ X₃ : C) : (α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom = ((μ L 
W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom…
· 使用引理 `CategoryTheory.Localization.Monoidal.tensorHom_id`：tensorHom_id {X₁ X₂ :
 LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε) : f otimes
ₘ 𝟙 Y = f ▷ Y
· 使用引理 `CategoryTheory.Localization.Monoidal.id_tensorHom`：id_tensorHom (X : Loc
alizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂) : 𝟙 X otim
esₘ f = X ◁ f
· 使用定理 `CategoryTheory.Localization.Monoidal.whiskerLeft_comp`：whiskerLeft_comp 
(Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε} (f : X ⟶ Y) (g :
 Y ⟶ Z) : Q ◁ (f ≫ g) = Q ◁ f ≫ Q ◁ g
· 使用定理 `CategoryTheory.Localization.Monoidal.whiskerRight_comp`：whiskerRight_com
p (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε} (f : X ⟶ Y) (g
 : Y ⟶ Z) : (f ≫ g) ▷ Q = f ▷ Q ≫ g ▷ Q
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Localization.Monoidal.pentagon_aux₁`：pentagon_aux₁ {X₁ X₂
 X₃ Y₁ : LocalizedMonoidal L W ε} (i : X₁ ≅ Y₁) : ((i.hom ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X
₂ X₃).hom ≫ (i.inv ▷ (X₂ otimes X₃)) = (…
· 使用引理 `CategoryTheory.Localization.Monoidal.pentagon_aux₃`：pentagon_aux₃ {X₁ X₂
 X₃ Y₃ : LocalizedMonoidal L W ε} (i : X₃ ≅ Y₃) : ((X₁ otimes X₂) ◁ i.hom) ≫ (α_
 X₁ X₂ Y₃).hom ≫ (X₁ ◁ (X₂ ◁ i.inv)) = (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Localization.Monoidal.μ_natural_left_assoc`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Localization.Monoidal.μ_inv_natural_right_assoc`：∀ {C : T
ype u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 
: CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (W X Y Z : C)
,   CategoryTheory.CategoryStr…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Localization.Monoidal.whiskerRight_comp_assoc`：∀ {C : Typ
e u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Localization.Monoidal.whisker_exchange_assoc`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Localization.Monoidal.whiskerLeft_id`：whiskerLeft_id (X Y
 : LocalizedMonoidal L W ε) : X ◁ (𝟙 Y) = 𝟙 _
（共 44 条，此处仅展示前 30 条）
-/
lemma pentagon (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε) :
    Pentagon Y₁ Y₂ Y₃ Y₄ := by
  obtain ⟨X₁, ⟨e₁⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y₁) := ⟨_, ⟨(L').objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : ∃ X₂, Nonempty ((L').obj X₂ ≅ Y₂) := ⟨_, ⟨(L').objObjPreimageIso Y₂⟩⟩
  obtain ⟨X₃, ⟨e₃⟩⟩ : ∃ X₃, Nonempty ((L').obj X₃ ≅ Y₃) := ⟨_, ⟨(L').objObjPreimageIso Y₃⟩⟩
  obtain ⟨X₄, ⟨e₄⟩⟩ : ∃ X₄, Nonempty ((L').obj X₄ ≅ Y₄) := ⟨_, ⟨(L').objObjPreimageIso Y₄⟩⟩
  suffices Pentagon ((L').obj X₁) ((L').obj X₂) ((L').obj X₃) ((L').obj X₄) by
    dsimp [Pentagon]
    refine Eq.trans ?_ (((((e₁.inv ⊗ₘ e₂.inv) ⊗ₘ e₃.inv) ⊗ₘ e₄.inv) ≫= this =≫
      (e₁.hom ⊗ₘ e₂.hom ⊗ₘ e₃.hom ⊗ₘ e₄.hom)).trans ?_)
    · rw [← id_tensorHom, ← id_tensorHom, ← tensorHom_id, ← tensorHom_id, assoc, assoc,
        ← tensor_comp, ← associator_naturality, id_comp, ← comp_id e₁.hom,
        tensor_comp, ← associator_naturality_assoc, ← comp_id (𝟙 ((L').obj X₄)),
        ← tensor_comp_assoc, associator_naturality, comp_id, comp_id,
        ← tensor_comp_assoc, assoc, e₄.inv_hom_id, ← tensor_comp, e₁.inv_hom_id,
        ← tensor_comp, e₂.inv_hom_id, e₃.inv_hom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
    · rw [assoc, associator_naturality_assoc, associator_naturality_assoc,
        ← tensor_comp, e₁.inv_hom_id, ← tensor_comp, e₂.inv_hom_id, ← tensor_comp,
        e₃.inv_hom_id, e₄.inv_hom_id, id_tensorHom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
  dsimp [Pentagon]
  have : ((L').obj X₁ ◁ (μ L W ε X₂ X₃).inv) ▷ (L').obj X₄ ≫
      (α_ ((L').obj X₁) ((L').obj X₂ ⊗ (L').obj X₃) ((L').obj X₄)).hom ≫
        (L').obj X₁ ◁ (μ L W ε X₂ X₃).hom ▷ (L').obj X₄ =
          (α_ ((L').obj X₁) ((L').obj (X₂ ⊗ X₃)) ((L').obj X₄)).hom :=
    pentagon_aux₂ _ _ _ (μ L W ε X₂ X₃).symm
  rw [associator_hom_app, tensorHom_id, id_tensorHom, associator_hom_app, tensorHom_id,
    whiskerLeft_comp, whiskerRight_comp, whiskerRight_comp, whiskerRight_comp, assoc, assoc,
    assoc, whiskerRight_comp, assoc,
    reassoc_of% this, associator_hom_app, tensorHom_id,
    ← pentagon_aux₁ (X₂ := (L').obj X₃) (X₃ := (L').obj X₄) (i := μ L W ε X₁ X₂),
    ← pentagon_aux₃ (X₁ := (L').obj X₁) (X₂ := (L').obj X₂) (i := μ L W ε X₃ X₄),
    associator_hom_app, associator_hom_app]
  simp only [assoc, ← whiskerRight_comp_assoc, Iso.inv_hom_id, comp_id, μ_natural_left_assoc,
    id_tensorHom, ← whiskerLeft_comp, Iso.inv_hom_id_assoc]
  rw [← (L').map_comp_assoc, whiskerLeft_comp, μ_inv_natural_right_assoc, ← (L').map_comp_assoc]
  simp only [assoc, MonoidalCategory.pentagon, Functor.map_comp, tensorHom_id,
    whiskerRight_comp_assoc]
  congr 3; simp only [← assoc]; congr
  simp only [← cancel_mono (μ L W ε (X₁ ⊗ X₂) (X₃ ⊗ X₄)).inv, assoc, id_comp,
    whisker_exchange_assoc, ← whiskerRight_comp_assoc,
    Iso.inv_hom_id, whiskerRight_id, ← whiskerLeft_comp,
    whiskerLeft_id]
/-
**CategoryTheory.Localization.Monoidal.leftUnitor_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：leftUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) : 𝟙_ (Lo
calizedMonoidal L W ε) ◁ f ≫ (fun_ Y).hom = (fun_ X).hom ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) :
    𝟙_ (LocalizedMonoidal L W ε) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  simp +instances [monoidalCategoryStruct]
/-
**CategoryTheory.Localization.Monoidal.rightUnitor_naturality** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：rightUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) : f ▷ 𝟙
_ (LocalizedMonoidal L W ε) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma rightUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) :
    f ▷ 𝟙_ (LocalizedMonoidal L W ε) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f :=
  (rightUnitor L W ε).hom.naturality f

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.triangle_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangle_aux₁ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (i₁ : X₁ ≅ Y₁) (i₂ : X₂ ≅ Y₂) (i₃ : X₃ ≅ Y₃) :
    ((i₁.hom ⊗ₘ i₂.hom) ⊗ₘ i₃.hom) ≫ (α_ Y₁ Y₂ Y₃).hom ≫ (i₁.inv ⊗ₘ i₂.inv ⊗ₘ i₃.inv) =
      (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality_assoc, ← tensor_comp, Iso.hom_inv_id, id_tensorHom,
    whiskerLeft_id, comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Localization.Monoidal.triangle_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangle_aux₂ {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
    (e₁ : (L').obj X' ≅ X) (e₂ : (L').obj Y' ≅ Y) :
      e₁.hom ⊗ₘ (ε.hom ⊗ₘ e₂.hom) ≫ (λ_ Y).hom =
        (L').obj X' ◁ ((ε' L W ε).hom ▷ (L').obj Y' ≫
          𝟙_ _ ◁ e₂.hom ≫ (λ_ Y).hom) ≫ e₁.hom ▷ Y := by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, comp_id, id_comp,
    ← tensor_comp_assoc, id_comp]
  congr 3
  exact (comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.triangle_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangle_aux₃ {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
    (e₁ : (L').obj X' ≅ X) (e₂ : (L').obj Y' ≅ Y) : (ρ_ X).hom ▷ _ =
      ((e₁.inv ⊗ₘ ε.inv) ⊗ₘ e₂.inv) ≫ _ ◁ e₂.hom ≫ ((μ L W ε X' (𝟙_ C)).hom ≫
        (L').map (ρ_ X').hom) ▷ Y ≫ e₁.hom ▷ Y := by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, assoc, comp_id,
    id_comp, Iso.inv_hom_id]
  congr
  rw [← cancel_mono e₁.inv, assoc, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← rightUnitor_naturality, rightUnitor_hom_app,
    ← tensorHom_id, ← id_tensorHom, ← tensor_comp_assoc, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency.types false in
variable {L W ε} in
/-
**CategoryTheory.Localization.Monoidal.triangle** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Localization.Monoidal`。
形式化陈述：triangle (X Y : LocalizedMonoidal L W ε) : (α_ X (𝟙_ _) Y).hom ≫ X ◁ (fun_
 Y).hom = (ρ_ X).hom ▷ Y
参数：X Y : LocalizedMonoidal L W ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instEssSurjLocalizedMonoidalToMonoi
dalCategory`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_
1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.Localization.Monoidal.associator_hom_app`：associator_hom_
app (X₁ X₂ X₃ : C) : (α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom = ((μ L 
W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用引理 `CategoryTheory.Localization.Monoidal.leftUnitor_hom_app`：leftUnitor_hom_
app (Y : C) : (fun_ ((L').obj Y)).hom = (ε' L W ε).inv ▷ (L').obj Y ≫ (μ _ _ _ _
 _).hom ≫ (L').map (fun_ Y).hom
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.MonoidalCategory.triangle`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : C),   
CategoryTheory.CategoryStruct.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `CategoryTheory.Localization.Monoidal.whiskerRight_id`：whiskerRight_id (X
 Y : LocalizedMonoidal L W ε) : (𝟙 X) ▷ Y = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Localization.Monoidal.whiskerLeft_comp`：whiskerLeft_comp 
(Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε} (f : X ⟶ Y) (g :
 Y ⟶ Z) : Q ◁ (f ≫ g) = Q ◁ f ≫ Q ◁ g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用引理 `CategoryTheory.Localization.Monoidal.μ_natural_right`：μ_natural_right (X
 : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) : (L').obj X ◁ (L').map g ≫ (μ L W ε X Y₂).hom =
 (μ L W ε X Y₁).hom ≫ (L').map (X ◁ g)
· 使用定理 `CategoryTheory.Localization.Monoidal.whiskerRight_comp_assoc`：∀ {C : Typ
e u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Localization.Monoidal.tensorHom_id`：tensorHom_id {X₁ X₂ :
 LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε) : f otimes
ₘ 𝟙 Y = f ▷ Y
· 使用引理 `CategoryTheory.Localization.Monoidal.μ_natural_left`：μ_natural_left {X₁ 
X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : (L').map f ▷ (L').obj Y ≫ (μ L W ε X₂ Y).hom = (
μ L W ε X₁ Y).hom ≫ (L').map (f ▷ Y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.Localization.Monoidal.id_tensorHom`：id_tensorHom (X : Loc
alizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂) : 𝟙 X otim
esₘ f = X ◁ f
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用引理 `CategoryTheory.Localization.Monoidal.whiskerLeft_id`：whiskerLeft_id (X Y
 : LocalizedMonoidal L W ε) : X ◁ (𝟙 Y) = 𝟙 _
（共 39 条，此处仅展示前 30 条）
-/
lemma triangle (X Y : LocalizedMonoidal L W ε) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  obtain ⟨X', ⟨e₁⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
  obtain ⟨Y', ⟨e₂⟩⟩ : ∃ X₂, Nonempty ((L').obj X₂ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
  have h₁ := (associator_hom_app L W ε X' (𝟙_ _) Y' =≫
    (𝟙 ((L').obj X') ⊗ₘ (μ L W ε (𝟙_ C) Y').hom))
  simp only [assoc, id_tensorHom, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id, comp_id, Iso.inv_hom_id,
    ← cancel_mono (μ L W ε X' (𝟙_ C ⊗ Y')).hom] at h₁
  have h₂ := (ε' L W ε).hom ▷ (L').obj Y' ≫= leftUnitor_hom_app L W ε Y'
  simp only [← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id, id_comp] at h₂
  have h₃ := (((μ L W ε _ _).hom ⊗ₘ 𝟙 _) ≫ (μ L W ε _ _).hom) ≫=
    ((L').congr_map (MonoidalCategory.triangle X' Y'))
  simp only [assoc, Functor.map_comp, ← reassoc_of% h₁] at h₃
  rw [← μ_natural_left, tensorHom_id, ← whiskerRight_comp_assoc,
    ← μ_natural_right, ← Iso.comp_inv_eq, assoc, assoc, assoc,
    Iso.hom_inv_id, comp_id, ← whiskerLeft_comp, ← h₂] at h₃
  replace h₃ := ((e₁.inv ⊗ₘ ε.inv) ⊗ₘ e₂.inv) ≫= (h₃ =≫ (_ ◁ e₂.hom)) =≫ (e₁.hom ▷ _)
  simp only [← whiskerLeft_comp, assoc, ← leftUnitor_naturality, ← whisker_exchange] at h₃
  have : _ = (α_ X (𝟙_ (LocalizedMonoidal L W ε)) Y).hom :=
    triangle_aux₁ _ _ _ e₁.symm ε.symm e₂.symm
  simp only [← this, Iso.symm_hom, Iso.symm_inv, assoc,
    ← id_tensorHom, ← tensor_comp, comp_id]
  convert! h₃
  · exact triangle_aux₂ _ _ _ e₁ e₂
  · exact triangle_aux₃ _ _ _ e₁ e₂
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    MonoidalCategory (LocalizedMonoidal L W ε) where
  tensorHom_def := by intros; simp +instances [monoidalCategoryStruct]
  id_tensorHom_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  tensorHom_comp_tensorHom := by intros; simp +instances [monoidalCategoryStruct]
  whiskerLeft_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  id_whiskerRight := by
    intros
    simp +instances [monoidalCategoryStruct]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by apply associator_naturality
  leftUnitor_naturality := by intros; simp +instances [monoidalCategoryStruct]
  rightUnitor_naturality := fun f ↦ (rightUnitor L W ε).hom.naturality f
  pentagon := pentagon
  triangle := triangle

end Monoidal

end Localization

open Localization.Monoidal

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (toMonoidalCategory L W ε).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := ε.symm
      μIso X Y := μ L W ε X Y
      associativity X Y Z := by simp [associator_hom_app L W ε X Y Z]
      left_unitality Y := leftUnitor_hom_app L W ε Y
      right_unitality X := rightUnitor_hom_app L W ε X }

local notation "L'" => toMonoidalCategory L W ε
/-
**CategoryTheory.associator_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：associator_hom (X Y Z : C) : (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).h
om = (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫ (Functor.LaxMonoidal.μ (L')
 (X otimes Y) Z) ≫ (L').map (α_ X Y Z).hom ≫ (Functor.OplaxMonoidal.δ (L') X (Y 
otimes Z)) ≫ ((L').obj X) ◁ (Functor.OplaxMonoidal.δ (L') Y Z)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_assoc`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCat
egory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Functor.Monoidal.whiskerLeft_μ_δ`：whiskerLeft_μ_δ (X Y : 
C) (T : D) : T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom =
    (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
      (Functor.LaxMonoidal.μ (L') (X ⊗ Y) Z) ≫
        (L').map (α_ X Y Z).hom ≫
          (Functor.OplaxMonoidal.δ (L') X (Y ⊗ Z)) ≫
            ((L').obj X) ◁ (Functor.OplaxMonoidal.δ (L') Y Z) := by
  simp
/-
**CategoryTheory.associator_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：associator_inv (X Y Z : C) : (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).i
nv = (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫ (Functor.LaxMonoidal.μ (L')
 X (Y otimes Z)) ≫ (L').map (α_ X Y Z).inv ≫ (Functor.OplaxMonoidal.δ (L') (X ot
imes Y) Z) ≫ (Functor.OplaxMonoidal.δ (L') X Y) ▷ ((L').obj Z)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_inv_assoc`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoida
lCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Functor.Monoidal.whiskerRight_μ_δ`：whiskerRight_μ_δ (X Y 
: C) (T : D) : μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv =
    (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
      (Functor.LaxMonoidal.μ (L') X (Y ⊗ Z)) ≫
        (L').map (α_ X Y Z).inv ≫
          (Functor.OplaxMonoidal.δ (L') (X ⊗ Y) Z) ≫
            (Functor.OplaxMonoidal.δ (L') X Y) ▷ ((L').obj Z) := by
  simp


end CategoryTheory

