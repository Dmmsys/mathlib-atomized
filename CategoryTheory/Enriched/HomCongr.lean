/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Congruence of enriched homs

Recall that when `C` is both a category and a `V`-enriched category, we say it
is an `EnrichedOrdinaryCategory` if it comes equipped with a sufficiently
compatible equivalence between morphisms `X ⟶ Y` in `C` and morphisms
`𝟙_ V ⟶ (X ⟶[V] Y)` in `V`.

In such a `V`-enriched ordinary category `C`, isomorphisms in `C` induce
isomorphisms between hom-objects in `V`. We define this isomorphism in
`CategoryTheory.Iso.eHomCongr` and prove that it respects composition in `C`.

The treatment here parallels that for unenriched categories in
`Mathlib/CategoryTheory/HomCongr.lean` and that for sorts in
`Mathlib/Logic/Equiv/Defs.lean` (cf. `Equiv.arrowCongr`). Note, however, that
they construct equivalences between `Type`s and `Sort`s, respectively, while
in this file we construct isomorphisms between objects in `V`.
-/

@[expose] public section

universe v' v u u'

namespace CategoryTheory
namespace Iso

open Category MonoidalCategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Given isomorphisms `α : X ≅ X₁` and `β : Y ≅ Y₁` in `C`, we can construct
an isomorphism between `V` objects `X ⟶[V] Y` and `X₁ ⟶[V] Y₁`. -/
@[simps]
/-
**CategoryTheory.Iso.eHomCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：eHomCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) : (X ⟶[V] Y) ≅ (X₁ ⟶[V
] Y₁) where hom
参数：α : X ≅ X₁；β : Y ≅ Y₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given isomorphisms `α : X ≅ X₁` and `β : Y ≅ Y₁` in `C`, we can construct
an isomorphism between `V` objects `X ⟶[V] Y` and `X₁ ⟶[V] Y₁`.
-/
def eHomCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶[V] Y) ≅ (X₁ ⟶[V] Y₁) where
  hom := eHomWhiskerRight V α.inv Y ≫ eHomWhiskerLeft V X₁ β.hom
  inv := eHomWhiskerRight V α.hom Y₁ ≫ eHomWhiskerLeft V X β.inv
  hom_inv_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]
  inv_hom_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]
/-
**CategoryTheory.Iso.eHomCongr_refl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：eHomCongr_refl (X Y : C) : eHomCongr V (Iso.refl X) (Iso.refl Y) = Iso.ref
l (X ⟶[V] Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eHomCongr_hom`：∀ (V : Type u') [inst : CategoryTheory
.Category.{v', u'} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C : Type u} 
  [inst_2 : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.eHomWhiskerRight_id`：eHomWhiskerRight_id (X Y : C) : eHom
WhiskerRight V (𝟙 X) Y = 𝟙 _
· 使用引理 `CategoryTheory.eHomWhiskerLeft_id`：eHomWhiskerLeft_id (X Y : C) : eHomWh
iskerLeft V X (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eHomCongr_refl (X Y : C) :
    eHomCongr V (Iso.refl X) (Iso.refl Y) = Iso.refl (X ⟶[V] Y) := by aesop
/-
**CategoryTheory.Iso.eHomCongr_trans** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
so`。
形式化陈述：eHomCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ 
: X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) : eHomCongr V (α₁ ≪≫ α₂) (β₁ ≪≫ β₂) = eHomCongr V α₁ β
₁ ≪≫ eHomCongr V α₂ β₂
参数：α₁ : X₁ ≅ X₂；β₁ : Y₁ ≅ Y₂；α₂ : X₂ ≅ X₃；β₂ : Y₂ ≅ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eHomCongr_hom`：∀ (V : Type u') [inst : CategoryTheory
.Category.{v', u'} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C : Type u} 
  [inst_2 : CategoryTh…
· 使用引理 `CategoryTheory.eHomWhiskerRight_comp`：eHomWhiskerRight_comp {X X' X'' : 
C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) : eHomWhiskerRight V (f ≫ f') Y = eHomWh
iskerRight V f' Y ≫ eHomWh…
· 使用引理 `CategoryTheory.eHomWhiskerLeft_comp`：eHomWhiskerLeft_comp (X : C) {Y Y' 
Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') : eHomWhiskerLeft V X (g ≫ g') = eHomWhisk
erLeft V X g ≫ eHomWhiske…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eHom_whisker_exchange_assoc`：∀ (V : Type u') [inst : Cate
goryTheory.Category.{v', u'} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C 
: Type u}   [inst_2 : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eHomCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂)
    (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) :
    eHomCongr V (α₁ ≪≫ α₂) (β₁ ≪≫ β₂) =
      eHomCongr V α₁ β₁ ≪≫ eHomCongr V α₂ β₂ := by
  ext; simp [eHom_whisker_exchange_assoc]
/-
**CategoryTheory.Iso.eHomCongr_symm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：eHomCongr_symm {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) : (eHomCongr V α 
β).symm = eHomCongr V α.symm β.symm
参数：α : X ≅ X₁；β : Y ≅ Y₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eHomCongr_symm {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (eHomCongr V α β).symm = eHomCongr V α.symm β.symm := rfl

/-- `eHomCongr` respects composition of morphisms. Recall that for any
composable pair of arrows `f : X ⟶ Y` and `g : Y ⟶ Z` in `C`, the composite
`f ≫ g` in `C` defines a morphism `𝟙_ V ⟶ (X ⟶[V] Z)` in `V`. Composing with
the isomorphism `eHomCongr V α γ` yields a morphism in `V` that can be factored
through the enriched composition map as shown:
`𝟙_ V ⟶ 𝟙_ V ⊗ 𝟙_ V ⟶ (X₁ ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z₁) ⟶ (X₁ ⟶[V] Z₁)`. -/
@[reassoc]
/-
**CategoryTheory.Iso.eHomCongr_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：eHomCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
 (f : X ⟶ Y) (g : Y ⟶ Z) : eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).hom = (fun_ _
).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).hom) ▷ _ ≫ _ ◁ (eHomEquiv V g ≫ (eHom
Congr V β γ).hom) ≫ eComp V X₁ Y₁ Z₁
参数：α : X ≅ X₁；β : Y ≅ Y₁；γ : Z ≅ Z₁；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mono
idalCategory C] {X X' : C}   (f : X ⟶ X') {Z : C}   (h…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用引理 `CategoryTheory.eComp_eHomWhiskerLeft`：eComp_eHomWhiskerLeft (X Y : C) {Z
 Z' : C} (g : Z ⟶ Z') : eComp V X Y Z ≫ eHomWhiskerLeft V X g = _ ◁ eHomWhiskerL
eft V Y g ≫ eComp V X Y Z'
· 使用定理 `CategoryTheory.eHom_whisker_cancel_assoc`：∀ (V : Type u') [inst : Catego
ryTheory.Category.{v', u'} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C : 
Type u}   [inst_2 : CategoryTh…
· 使用定理 `CategoryTheory.eComp_eHomWhiskerRight_assoc`：∀ (V : Type u') [inst : Cat
egoryTheory.Category.{v', u'} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C
 : Type u}   [inst_2 : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def_assoc`：∀ {C : Type u} {𝒞 :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X
₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.eHomEquiv_comp_assoc`：∀ (V : Type u') [inst : CategoryThe
ory.Category.{v', u'} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C : Type 
u}   [inst_2 : CategoryTh…

--- 原说明 ---
`eHomCongr` respects composition of morphisms. Recall that for any
composable pair of arrows `f : X ⟶ Y` and `g : Y ⟶ Z` in `C`, the composite
`f ≫ g` in `C` defines a morphism `𝟙_ V ⟶ (X ⟶[V] Z)` in `V`. Composing with
the isomorphism `eHomCongr V α γ` yields a morphism in `V` that can be factored
through the enriched composition map as shown:
`𝟙_ V ⟶ 𝟙_ V ⊗ 𝟙_ V ⟶ (X₁ ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z₁) ⟶ (X₁ ⟶[V] Z₁)`.
-/
lemma eHomCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).hom =
      (λ_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).hom) ▷ _ ≫
        _ ◁ (eHomEquiv V g ≫ (eHomCongr V β γ).hom) ≫ eComp V X₁ Y₁ Z₁ := by
  simp only [eHomCongr, MonoidalCategory.whiskerRight_id, assoc,
    MonoidalCategory.whiskerLeft_comp]
  rw [rightUnitor_inv_naturality_assoc, rightUnitor_inv_naturality_assoc,
    rightUnitor_inv_naturality_assoc, hom_inv_id_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, ← eComp_eHomWhiskerLeft, eHom_whisker_cancel_assoc,
    ← eComp_eHomWhiskerRight_assoc, ← tensorHom_def_assoc,
    ← eHomEquiv_comp_assoc]

/-- The inverse map defined by `eHomCongr` respects composition of morphisms. -/
@[reassoc]
/-
**CategoryTheory.Iso.eHomCongr_inv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：eHomCongr_inv_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅
 Z₁) (f : X₁ ⟶ Y₁) (g : Y₁ ⟶ Z₁) : eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).inv =
 (fun_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).inv) ▷ _ ≫ _ ◁ (eHomEquiv V g
 ≫ (eHomCongr V β γ).inv) ≫ eComp V X Y Z
参数：α : X ≅ X₁；β : Y ≅ Y₁；γ : Z ≅ Z₁；f : X₁ ⟶ Y₁；g : Y₁ ⟶ Z₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Iso.eHomCongr_comp`：eHomCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (
α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y) (g : Y ⟶ Z) : eHomEquiv V (f ≫
 g) ≫ (eHomCongr V α γ)…

--- 原说明 ---
The inverse map defined by `eHomCongr` respects composition of morphisms.
-/
lemma eHomCongr_inv_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (γ : Z ≅ Z₁) (f : X₁ ⟶ Y₁) (g : Y₁ ⟶ Z₁) :
    eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).inv =
      (λ_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).inv) ▷ _ ≫
        _ ◁ (eHomEquiv V g ≫ (eHomCongr V β γ).inv) ≫ eComp V X Y Z :=
  eHomCongr_comp V α.symm β.symm γ.symm f g

end Iso
end CategoryTheory

