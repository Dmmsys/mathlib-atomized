/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

/-!
# Lemmas which are consequences of monoidal coherence

These lemmas are all proved `by coherence`.

## Future work
Investigate whether these lemmas are really needed,
or if they can be replaced by use of the `coherence` tactic.
-/

public section


open CategoryTheory Category Iso

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom''** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_tensor_hom'' (X Y : C) : (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes 
Y)).hom = (fun_ X).hom otimesₘ 𝟙 Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight`：leftUnitor_whis
kerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)
).hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_tensor_hom'' (X Y : C) :
    (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ⊗ₘ 𝟙 Y := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom'** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_tensor_hom' (X Y : C) : (fun_ (X otimes Y)).hom = (α_ (𝟙_ C) X 
Y).inv ≫ ((fun_ X).hom otimesₘ 𝟙 Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight`：leftUnitor_whis
kerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)
).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_tensor_hom' (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ ((λ_ X).hom ⊗ₘ 𝟙 Y) := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_tensor_inv'** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_tensor_inv' (X Y : C) : (fun_ (X otimes Y)).inv = ((fun_ X).inv
 otimesₘ 𝟙 Y) ≫ (α_ (𝟙_ C) X Y).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight`：leftUnitor_
inv_whiskerRight (X Y : C) : (fun_ X).inv ▷ Y = (fun_ (X otimes Y)).inv ≫ (α_ (𝟙
_ C) X Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_tensor_inv' (X Y : C) :
    (λ_ (X ⊗ Y)).inv = ((λ_ X).inv ⊗ₘ 𝟙 Y) ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.id_tensor_rightUnitor_inv** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：id_tensor_rightUnitor_inv (X Y : C) : 𝟙 X otimesₘ (ρ_ Y).inv = (ρ_ _).inv 
≫ (α_ _ _ _).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv`：whiskerLeft
_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙
_ C)).hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_tensor_rightUnitor_inv (X Y : C) : 𝟙 X ⊗ₘ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_inv_tensor_id** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_inv_tensor_id (X Y : C) : (fun_ X).inv otimesₘ 𝟙 Y = (fun_ _).i
nv ≫ (α_ _ _ _).inv
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight`：leftUnitor_
inv_whiskerRight (X Y : C) : (fun_ X).inv ▷ Y = (fun_ (X otimes Y)).inv ≫ (α_ (𝟙
_ C) X Y).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_inv_tensor_id (X Y : C) : (λ_ X).inv ⊗ₘ 𝟙 Y = (λ_ _).inv ≫ (α_ _ _ _).inv := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv_inv_hom (W X Y Z : C) : (α_ W (X otimes Y) Z).inv ≫ ((α_ W X 
Y).inv otimesₘ 𝟙 Z) ≫ (α_ (W otimes X) Y Z).hom = (𝟙 W otimesₘ (α_ X Y Z).hom) ≫
 (α_ W X (Y otimes Z)).inv
参数：W X Y Z : C。
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
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom_hom_inv`：pentagon_i
nv_inv_hom_hom_inv : (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W oti
mes X) Y Z).hom = W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_inv_hom (W X Y Z : C) :
    (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ₘ 𝟙 Z) ≫ (α_ (W ⊗ X) Y Z).hom =
      (𝟙 W ⊗ₘ (α_ X Y Z).hom) ≫ (α_ W X (Y ⊗ Z)).inv := by
  simp
/-
**CategoryTheory.MonoidalCategory.unitors_equal** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalCategory`。
形式化陈述：unitors_equal : (fun_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
-/
theorem unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence
/-
**CategoryTheory.MonoidalCategory.unitors_inv_equal** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：unitors_inv_equal : (fun_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
-/
theorem unitors_inv_equal : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
  monoidal_coherence

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.pentagon_hom_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：pentagon_hom_inv {W X Y Z : C} : (α_ W X (Y otimes Z)).hom ≫ (𝟙 W otimesₘ 
(α_ X Y Z).inv) = (α_ (W otimes X) Y Z).inv ≫ ((α_ W X Y).hom otimesₘ 𝟙 Z) ≫ (α_
 W (X otimes Y) Z).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_hom_hom_hom_inv`：pentagon_i
nv_hom_hom_hom_inv : (α_ (W otimes X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z ≫ (α_ W (X o
times Y) Z).hom = (α_ W X (Y otimes Z)).hom ≫ W ◁ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_inv {W X Y Z : C} :
    (α_ W X (Y ⊗ Z)).hom ≫ (𝟙 W ⊗ₘ (α_ X Y Z).inv) =
      (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv_hom (W X Y Z : C) : (α_ (W otimes X) Y Z).inv ≫ ((α_ W X Y).h
om otimesₘ 𝟙 Z) = (α_ W X (Y otimes Z)).hom ≫ (𝟙 W otimesₘ (α_ X Y Z).inv) ≫ (α_
 W (X otimes Y) Z).inv
参数：W X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_hom`：pentagon_h
om_inv_inv_inv_hom : (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X o
times Y) Z).inv = (α_ (W otimes X) Y Z).inv ≫ (α_ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_hom (W X Y Z : C) :
    (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊗ₘ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).hom ≫ (𝟙 W ⊗ₘ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv := by
  simp

end CategoryTheory.MonoidalCategory

