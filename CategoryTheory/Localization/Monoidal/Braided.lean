/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Multifunctor

/-!

# Localization of symmetric monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure. The file
`Mathlib.CategoryTheory.Localization.Monoidal.Basic` constructs a monoidal structure on
the localized on `D` such that the localization functor is monoidal.

In this file we promote this monoidal structure to a braided structure in the case where `C` is
braided, in such a way that the localization functor is braided. If `C` is symmetric monoidal, then
the monoidal structure on `D` is also symmetric.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory BraidedCategory Functor

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C] [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

section Braided

variable [BraidedCategory C]

/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε).flip :=
  inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip)

/-- The braiding on the localized category as a natural isomorphism of bifunctors. -/
/-
**CategoryTheory.Localization.Monoidal.braidingNatIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Localization.Monoidal`。
形式化陈述：braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory_1`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Cat
egory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categ
or…

--- 原说明 ---
The braiding on the localized category as a natural isomorphism of bifunctors.
-/
noncomputable def braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip :=
  lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _ (isoWhiskerRight (curriedBraidingNatIso C) _)
/-
**CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：braidingNatIso_hom_app (X Y : C) : ((braidingNatIso L W ε).hom.app ((L').o
bj X)).app ((L').obj Y) = (Functor.LaxMonoidal.μ (L') X Y) ≫ (L').map (β_ X Y).h
om ≫ (Functor.OplaxMonoidal.δ (L') Y X)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Localization.Monoidal.instIsLocalizationLocalizedMonoidal
ToMonoidalCategory_1`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Cat
egory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categ
or…
· 使用定理 `CategoryTheory.Localization.lift₂NatTrans_app_app`：lift₂NatTrans_app_app
 (τ : F₁ ⟶ F₂) (X₁ : C₁) (X₂ : C₂) : ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ
).app (L₁.obj X₁)).app (L₂.obj X₂) = ((…
· 使用定理 `CategoryTheory.BraidedCategory.curriedBraidingNatIso_hom_app_app`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mono
idalCategory C]   [inst_2 : CategoryTheory.BraidedCate…
-/
lemma braidingNatIso_hom_app (X Y : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y) =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) := by
  simp [braidingNatIso, lift₂NatIso]
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app_naturality_** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma braidingNatIso_hom_app_naturality_μ_left (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y ⊗ (L').obj Z) ≫
      (Functor.LaxMonoidal.μ (L') Y Z) ▷ (L').obj X =
        (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
          ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj (Y ⊗ Z)) :=
  (((braidingNatIso L W ε).hom.app ((L').obj X)).naturality ((Functor.LaxMonoidal.μ (L') Y Z))).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app_naturality_** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma braidingNatIso_hom_app_naturality_μ_right (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z) ≫
      (L').obj Z ◁ (Functor.LaxMonoidal.μ (L') X Y) =
        (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
          ((braidingNatIso L W ε).hom.app ((L').obj (X ⊗ Y))).app ((L').obj Z) :=
  (NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality
    ((Functor.LaxMonoidal.μ (L') X Y))) ((L').obj Z)).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.map_hexagon_forward** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：map_hexagon_forward (X Y Z : C) : (α_ ((L').obj X) ((L').obj Y) ((L').obj 
Z)).hom ≫ (((braidingNatIso L W ε).app ((L').obj X)).app (((L').obj Y) otimes ((
L').obj Z))).hom ≫ (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom = (((braiding
NatIso L W ε).app ((L').obj X)).app ((L').obj Y)).hom ▷ ((L').obj Z) ≫ (α_ ((L')
.obj Y) ((L').obj X) ((L').obj Z)).hom ≫ ((L').obj Y) ◁ (((braidingNatIso L W ε)
.app ((L').obj X)).app ((L').obj Z)).hom
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.associator_hom`：associator_hom (X Y Z : C) : (α_ ((L').ob
j X) ((L').obj Y) ((L').obj Z)).hom = (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').ob
j Z ≫ (Functor.LaxM…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app`：braidingNat
Iso_hom_app (X Y : C) : ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').
obj Y) = (Functor.LaxMonoidal.μ (L') X Y) ≫ (L').…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerRight_δ_μ_assoc`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_left`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app_naturality_μ
_left`：braidingNatIso_hom_app_naturality_μ_left (X Y Z : C) : ((braidingNatIso L
 W ε).hom.app ((L').obj X)).app ((L').obj Y otimes (L').obj Z) ≫ (F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_inv_assoc`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoida
lCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.associativity_inv_assoc`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Iso.map_hom_inv_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerLeft_δ_μ_assoc`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCate
gory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_natural_right_assoc`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Monoida
lCategory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_hexagon_forward (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom ≫
      (((braidingNatIso L W ε).app ((L').obj X)).app (((L').obj Y) ⊗ ((L').obj Z))).hom ≫
        (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom =
      (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Y)).hom ▷ ((L').obj Z) ≫
        (α_ ((L').obj Y) ((L').obj X) ((L').obj Z)).hom ≫
        ((L').obj Y) ◁ (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom := by
  simp only [associator_hom, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_left, braidingNatIso_hom_app]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.map_hexagon_reverse** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：map_hexagon_reverse (X Y Z : C) : (α_ ((L').obj X) ((L').obj Y) ((L').obj 
Z)).inv ≫ (((braidingNatIso L W ε).app ((L').obj X otimes (L').obj Y)).app ((L')
.obj Z)).hom ≫ (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv = ((L').obj X) ◁ 
(((braidingNatIso L W ε).app ((L').obj Y)).app ((L').obj Z)).hom ≫ (α_ ((L').obj
 X) ((L').obj Z) ((L').obj Y)).inv ≫ (((braidingNatIso L W ε).app ((L').obj X)).
app ((L').obj Z)).hom ▷ ((L').obj Y)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.associator_inv`：associator_inv (X Y Z : C) : (α_ ((L').ob
j X) ((L').obj Y) ((L').obj Z)).inv = (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y
 Z) ≫ (Functor.LaxM…
· 使用引理 `CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app`：braidingNat
Iso_hom_app (X Y : C) : ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').
obj Y) = (Functor.LaxMonoidal.μ (L') X Y) ≫ (L').…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用引理 `CategoryTheory.Localization.Monoidal.braidingNatIso_hom_app_naturality_μ
_right`：braidingNatIso_hom_app_naturality_μ_right (X Y Z : C) : ((braidingNatIso
 L W ε).hom.app ((L').obj X otimes (L').obj Y)).app ((L').obj Z) ≫ (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_assoc`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCat
egory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Iso.map_hom_inv_id`：map_hom_inv_id (F : C ⥤ D) : F.map e.
hom ≫ F.map e.inv = 𝟙 _
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.associativity_assoc`：∀ {C : Type u₁
} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalC
ategory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerLeft_δ_μ_assoc`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCate
gory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Iso.map_inv_hom_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_right`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerRight_δ_μ_assoc`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_natural_left_assoc`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Monoidal
Category C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_hexagon_reverse (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv ≫
      (((braidingNatIso L W ε).app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv =
      ((L').obj X) ◁ (((braidingNatIso L W ε).app ((L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj X) ((L').obj Z) ((L').obj Y)).inv ≫
        (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom ▷ ((L').obj Y) := by
  simp only [associator_inv, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.whiskerLeft_comp, assoc,
      Functor.Monoidal.whiskerLeft_δ_μ, comp_id]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_right, braidingNatIso_hom_app]
  simp
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : BraidedCategory (LocalizedMonoidal L W ε) := by
  refine .ofBifunctor (braidingNatIso L W ε) ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_forward _ _ _
  · apply natTrans₃_ext (L') (L') (L') W W W
    simpa using! map_hexagon_reverse _ _ _
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma β_hom_app (X Y : C) :
    (β_ ((L').obj X) ((L').obj Y)).hom =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) :=
  braidingNatIso_hom_app L W ε X Y
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (toMonoidalCategory L W ε).Braided where
  braided X Y := by simp [β_hom_app]

end Braided

section Symmetric

variable [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Localization.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SymmetricCategory (LocalizedMonoidal L W ε) := by
  refine .ofCurried (natTrans₂_ext (L') (L') W W fun X Y ↦ ?_)
  simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

end Symmetric

end CategoryTheory.Localization.Monoidal

