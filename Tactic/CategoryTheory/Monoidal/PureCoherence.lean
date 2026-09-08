/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes

/-!
# Coherence tactic for monoidal categories

We provide a `monoidal_coherence` tactic,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike MonoidalCategory

namespace Mathlib.Tactic.Monoidal

section

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

local infixr:81 " ◁ " => MonoidalCategory.whiskerLeftIso
local infixl:81 " ▷ " => MonoidalCategory.whiskerRightIso

/-- The composition of the normalizing isomorphisms `η_f : p ⊗ f ≅ pf` and `η_g : pf ⊗ g ≅ pfg`. -/
/-
**Mathlib.Tactic.Monoidal.normalizeIsoComp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.
Tactic.Monoidal`。
形式化陈述：normalizeIsoComp {p f g pf pfg : C} (η_f : p otimes f ≅ pf) (η_g : pf otim
es g ≅ pfg)
参数：η_f : p otimes f ≅ pf；η_g : pf otimes g ≅ pfg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of the normalizing isomorphisms `η_f : p ⊗ f ≅ pf` and `η_g : pf
 ⊗ g ≅ pfg`.
-/
abbrev normalizeIsoComp {p f g pf pfg : C} (η_f : p ⊗ f ≅ pf) (η_g : pf ⊗ g ≅ pfg) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g
/-
**Mathlib.Tactic.Monoidal.naturality_associator** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Monoidal`。
形式化陈述：naturality_associator {p f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η
_g : pf otimes g ≅ pfg) (η_h : pfg otimes h ≅ pfgh) : p ◁ (α_ f g h) ≪≫ normaliz
eIsoComp η_f (normalizeIsoComp η_g η_h) = normalizeIsoComp (normalizeIsoComp η_f
 η_g) η_h
参数：η_f : p otimes f ≅ pf；η_g : pf otimes g ≅ pfg；η_h : pfg otimes h ≅ pfgh。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRightIso_hom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory 
C] {X Y : C}   (f : X ≅ Y) (Z : C),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerRightIso_trans`：whiskerRightIso_t
rans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) : whiskerRightIso (f ≪≫ g) W = 
whiskerRightIso f W ≪≫ whiskerRightIso g W
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_associator {p f g h pf pfg pfgh : C}
    (η_f : p ⊗ f ≅ pf) (η_g : pf ⊗ g ≅ pfg) (η_h : pfg ⊗ h ≅ pfgh) :
    p ◁ (α_ f g h) ≪≫ normalizeIsoComp η_f (normalizeIsoComp η_g η_h) =
    normalizeIsoComp (normalizeIsoComp η_f η_g) η_h :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Monoidal.naturality_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Monoidal`。
形式化陈述：naturality_leftUnitor {p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) 
≪≫ η_f = normalizeIsoComp (ρ_ p) η_f
参数：η_f : p otimes f ≅ pf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRightIso_hom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory 
C] {X Y : C}   (f : X ≅ Y) (Z : C),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] (X Y : C) {Z : C}   (h : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_leftUnitor {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (λ_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p) η_f :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Monoidal.naturality_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.Monoidal`。
形式化陈述：naturality_rightUnitor {p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪
≫ η_f = normalizeIsoComp η_f (ρ_ pf)
参数：η_f : p otimes f ≅ pf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor`：whiskerLeft_rig
htUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).ho
m
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRightIso_hom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory 
C] {X Y : C}   (f : X ≅ Y) (Z : C),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_rightUnitor {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (ρ_ pf) :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Monoidal.naturality_id** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Monoidal`。
形式化陈述：naturality_id {p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f
 = η_f
参数：η_f : p otimes f ≅ pf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_refl`：whiskerLeftIso_refl
 (W X : C) : whiskerLeftIso W (Iso.refl X) = Iso.refl (W otimes X)
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_id {p f pf : C} (η_f : p ⊗ f ≅ pf) :
    p ◁ Iso.refl f ≪≫ η_f = η_f := by
  simp
/-
**Mathlib.Tactic.Monoidal.naturality_comp** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Monoidal`。
形式化陈述：naturality_comp {p f g h pf : C} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f
 ≅ pf) (η_g : p otimes g ≅ pf) (η_h : p otimes h ≅ pf) (ih_η : p ◁ η ≪≫ η_g = η_
f) (ih_θ : p ◁ θ ≪≫ η_h = η_g) : p ◁ (η ≪≫ θ) ≪≫ η_h = η_f
参数：η_f : p otimes f ≅ pf；η_g : p otimes g ≅ pf；η_h : p otimes h ≅ pf；ih_η : p ◁ 
η ≪≫ η_g = η_f；ih_θ : p ◁ θ ≪≫ η_h = η_g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_trans`：whiskerLeftIso_tra
ns (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) : whiskerLeftIso W (f ≪≫ g) = whi
skerLeftIso W f ≪≫ whiskerLeftIso W g
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_comp {p f g h pf : C} {η : f ≅ g} {θ : g ≅ h}
    (η_f : p ⊗ f ≅ pf) (η_g : p ⊗ g ≅ pf) (η_h : p ⊗ h ≅ pf)
    (ih_η : p ◁ η ≪≫ η_g = η_f) (ih_θ : p ◁ θ ≪≫ η_h = η_g) :
    p ◁ (η ≪≫ θ) ≪≫ η_h = η_f := by
  simp_all
/-
**Mathlib.Tactic.Monoidal.naturality_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.Monoidal`。
形式化陈述：naturality_whiskerLeft {p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f 
≅ pf) (η_fg : pf otimes g ≅ pfg) (η_fh : (pf otimes h) ≅ pfg) (ih_η : pf ◁ η ≪≫ 
η_fh = η_fg) : p ◁ (f ◁ η) ≪≫ normalizeIsoComp η_f η_fh = normalizeIsoComp η_f η
_fg
参数：η_f : p otimes f ≅ pf；η_fg : pf otimes g ≅ pfg；η_fh : (pf otimes h) ≅ pfg；ih_
η : pf ◁ η ≪≫ η_fh = η_fg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRightIso_hom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory 
C] {X Y : C}   (f : X ≅ Y) (Z : C),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_whiskerLeft {p f g h pf pfg : C} {η : g ≅ h}
    (η_f : p ⊗ f ≅ pf) (η_fg : pf ⊗ g ≅ pfg) (η_fh : (pf ⊗ h) ≅ pfg)
    (ih_η : pf ◁ η ≪≫ η_fh = η_fg) :
    p ◁ (f ◁ η) ≪≫ normalizeIsoComp η_f η_fh = normalizeIsoComp η_f η_fg := by
  rw [← ih_η]
  apply Iso.ext
  simp [← whisker_exchange_assoc]
/-
**Mathlib.Tactic.Monoidal.naturality_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Mat
hlib.Tactic.Monoidal`。
形式化陈述：naturality_whiskerRight {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f
 ≅ pf) (η_g : p otimes g ≅ pf) (η_fh : (pf otimes h) ≅ pfh) (ih_η : p ◁ η ≪≫ η_g
 = η_f) : p ◁ (η ▷ h) ≪≫ normalizeIsoComp η_g η_fh = normalizeIsoComp η_f η_fh
参数：η_f : p otimes f ≅ pf；η_g : p otimes g ≅ pf；η_fh : (pf otimes h) ≅ pfh；ih_η :
 p ◁ η ≪≫ η_g = η_f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRightIso_hom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory 
C] {X Y : C}   (f : X ≅ Y) (Z : C),   (Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerRightIso_trans`：whiskerRightIso_t
rans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) : whiskerRightIso (f ≪≫ g) W = 
whiskerRightIso f W ≪≫ whiskerRightIso g W
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_whiskerRight {p f g h pf pfh : C} {η : f ≅ g}
    (η_f : p ⊗ f ≅ pf) (η_g : p ⊗ g ≅ pf) (η_fh : (pf ⊗ h) ≅ pfh)
    (ih_η : p ◁ η ≪≫ η_g = η_f) :
    p ◁ (η ▷ h) ≪≫ normalizeIsoComp η_g η_fh = normalizeIsoComp η_f η_fh := by
  rw [← ih_η]
  apply Iso.ext
  simp
/-
**Mathlib.Tactic.Monoidal.naturality_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.Monoidal`。
形式化陈述：naturality_tensorHom {p f₁ g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅
 g₂} (η_f₁ : p otimes f₁ ≅ pf₁) (η_g₁ : p otimes g₁ ≅ pf₁) (η_f₂ : pf₁ otimes f₂
 ≅ pf₁f₂) (η_g₂ : pf₁ otimes g₂ ≅ pf₁f₂) (ih_η : p ◁ η ≪≫ η_g₁ = η_f₁) (ih_θ : p
f₁ ◁ θ ≪≫ η_g₂ = η_f₂) : p ◁ (η otimesᵢ θ) ≪≫ normalizeIsoComp η_g₁ η_g₂ = norma
lizeIsoComp η_f₁ η_f₂
参数：η_f₁ : p otimes f₁ ≅ pf₁；η_g₁ : p otimes g₁ ≅ pf₁；η_f₂ : pf₁ otimes f₂ ≅ pf₁f
₂；η_g₂ : pf₁ otimes g₂ ≅ pf₁f₂；ih_η : p ◁ η ≪≫ η_g₁ = η_f₁；ih_θ : pf₁ ◁ θ ≪≫ η_g
₂ = η_f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorIso_def`：tensorIso_def {X Y X' Y' 
: C} (f : X ≅ Y) (g : X' ≅ Y') : f otimesᵢ g = whiskerRightIso f X' ≪≫ whiskerLe
ftIso Y g
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
-/
theorem naturality_tensorHom {p f₁ g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂}
    (η_f₁ : p ⊗ f₁ ≅ pf₁) (η_g₁ : p ⊗ g₁ ≅ pf₁) (η_f₂ : pf₁ ⊗ f₂ ≅ pf₁f₂) (η_g₂ : pf₁ ⊗ g₂ ≅ pf₁f₂)
    (ih_η : p ◁ η ≪≫ η_g₁ = η_f₁)
    (ih_θ : pf₁ ◁ θ ≪≫ η_g₂ = η_f₂) :
    p ◁ (η ⊗ᵢ θ) ≪≫ normalizeIsoComp η_g₁ η_g₂ = normalizeIsoComp η_f₁ η_f₂ := by
  rw [tensorIso_def]
  apply naturality_comp
  · apply naturality_whiskerRight _ _ _ ih_η
  · apply naturality_whiskerLeft _ _ _ ih_θ
/-
**Mathlib.Tactic.Monoidal.naturality_inv** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Monoidal`。
形式化陈述：naturality_inv {p f g pf : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p
 otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η_f) : p ◁ η.symm ≪≫ η_f = η_g
参数：η_f : p otimes f ≅ pf；η_g : p otimes g ≅ pf；ih : p ◁ η ≪≫ η_g = η_f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_inv {p f g pf : C} {η : f ≅ g}
    (η_f : p ⊗ f ≅ pf) (η_g : p ⊗ g ≅ pf) (ih : p ◁ η ≪≫ η_g = η_f) :
    p ◁ η.symm ≪≫ η_f = η_g := by
  rw [← ih]
  apply Iso.ext
  simp
/-
**Mathlib.Tactic.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonadNormalizeNaturality MonoidalM where
  mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have pfgh : Q($ctx.C) := pfgh.e.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    have η_g : Q($pf ⊗ $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg ⊗ $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have pf : Q($ctx.C) := pf.e.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    have η_g : Q($p ⊗ $g ≅ $pf) := η_g.e
    have η_h : Q($p ⊗ $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfg : Q($ctx.C) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    have η_fg : Q($pf ⊗ $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf ⊗ $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have h : Q($ctx.C) := h.e
    have pf : Q($ctx.C) := pf.e.e
    have pfh : Q($ctx.C) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    have η_g : Q($p ⊗ $g ≅ $pf) := η_g.e
    have η_fh : Q($pf ⊗ $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp p pf₁ pf₁f₂ f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f₁ : Q($ctx.C) := f₁.e
    have g₁ : Q($ctx.C) := g₁.e
    have f₂ : Q($ctx.C) := f₂.e
    have g₂ : Q($ctx.C) := g₂.e
    have pf₁ : Q($ctx.C) := pf₁.e.e
    have pf₁f₂ : Q($ctx.C) := pf₁f₂.e.e
    have η : Q($f₁ ≅ $g₁) := η.e
    have θ : Q($f₂ ≅ $g₂) := θ.e
    have η_f₁ : Q($p ⊗ $f₁ ≅ $pf₁) := η_f₁.e
    have η_g₁ : Q($p ⊗ $g₁ ≅ $pf₁) := η_g₁.e
    have η_f₂ : Q($pf₁ ⊗ $f₂ ≅ $pf₁f₂) := η_f₂.e
    have η_g₂ : Q($pf₁ ⊗ $g₂ ≅ $pf₁f₂) := η_g₂.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g₁ = $η_f₁) := ih_η
    have ih_θ : Q($pf₁ ◁ $θ ≪≫ $η_g₂ = $η_f₂) := ih_θ
    return q(naturality_tensorHom $η_f₁ $η_g₁ $η_f₂ $η_g₂ $ih_η $ih_θ)
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    have p : Q($ctx.C) := p.e.e
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have pf : Q($ctx.C) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ⊗ $f ≅ $pf) := η_f.e
    have η_g : Q($p ⊗ $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)
/-
**Mathlib.Tactic.Monoidal.of_normalize_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Monoidal`。
形式化陈述：of_normalize_eq {f g f' : C} {η θ : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g
 : 𝟙_ C otimes g ≅ f') (h_η : 𝟙_ C ◁ η ≪≫ η_g = η_f) (h_θ : 𝟙_ C ◁ θ ≪≫ η_g = η_
f) : η = θ
参数：η_f : 𝟙_ C otimes f ≅ f'；η_g : 𝟙_ C otimes g ≅ f'；h_η : 𝟙_ C ◁ η ≪≫ η_g = η_f
；h_θ : 𝟙_ C ◁ θ ≪≫ η_g = η_f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_normalize_eq {f g f' : C} {η θ : f ≅ g} (η_f : 𝟙_ C ⊗ f ≅ f') (η_g : 𝟙_ C ⊗ g ≅ f')
    (h_η : 𝟙_ C ◁ η ≪≫ η_g = η_f)
    (h_θ : 𝟙_ C ◁ θ ≪≫ η_g = η_f) : η = θ := by
  apply Iso.ext
  calc
    η.hom = (λ_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (λ_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]
/-
**Mathlib.Tactic.Monoidal.mk_eq_of_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.Monoidal`。
形式化陈述：mk_eq_of_naturality {f g f' : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C
 otimes f ≅ f') (η_g : 𝟙_ C otimes g ≅ f') (η_hom : η'.hom = η) (Θ_hom : θ'.hom 
= θ) (Hη : whiskerLeftIso (𝟙_ C) η' ≪≫ η_g = η_f) (Hθ : whiskerLeftIso (𝟙_ C) θ'
 ≪≫ η_g = η_f) : η = θ
参数：η_f : 𝟙_ C otimes f ≅ f'；η_g : 𝟙_ C otimes g ≅ f'；η_hom : η'.hom = η；Θ_hom : 
θ'.hom = θ；Hη : whiskerLeftIso (𝟙_ C) η' ≪≫ η_g = η_f；Hθ : whiskerLeftIso (𝟙_ C)
 θ' ≪≫ η_g = η_f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeftIso_hom`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] (X : C) {Y Z : C}   (f : Y ≅ Z),   (Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_of_naturality {f g f' : C} {η θ : f ⟶ g} {η' θ' : f ≅ g}
    (η_f : 𝟙_ C ⊗ f ≅ f') (η_g : 𝟙_ C ⊗ g ≅ f')
    (η_hom : η'.hom = η) (Θ_hom : θ'.hom = θ)
    (Hη : whiskerLeftIso (𝟙_ C) η' ≪≫ η_g = η_f)
    (Hθ : whiskerLeftIso (𝟙_ C) θ' ≪≫ η_g = η_f) : η = θ :=
  calc
    η = η'.hom := η_hom.symm
    _ = (λ_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (λ_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη)]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ)]
    _ = θ := Θ_hom

end

/-
**Mathlib.Tactic.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEqOfNaturality MonoidalM where
  mkEqOfNaturality η θ ηIso θIso η_f η_g Hη Hθ := do
    let ctx ← read
    let some _monoidal := ctx.instMonoidal? | synthMonoidalError
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have f : Q($ctx.C) := f.e
    have g : Q($ctx.C) := g.e
    have f' : Q($ctx.C) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙_ _ ⊗ $f ≅ $f') := η_f.e
    have η_g : Q(𝟙_ _ ⊗ $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙_ _) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙_ _) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)

open Elab.Tactic

/-- Close the goal of the form `η = θ`, where `η` and `θ` are 2-isomorphisms made up only of
associators, unitors, and identities.
```lean
example {C : Type} [Category* C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence
```
-/
/-
**Mathlib.Tactic.Monoidal.pureCoherence** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Monoidal`。
形式化陈述：pureCoherence (mvarId : MVarId) : MetaM (List MVarId)
参数：mvarId : MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Close the goal of the form `η = θ`, where `η` and `θ` are 2-isomorphisms made up
 only of
associators, unitors, and identities.
```lean
example {C : Type} [Category* C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence
```
-/
def pureCoherence (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.pureCoherence Monoidal.Context `monoidal mvarId

@[inherit_doc pureCoherence]
elab "monoidal_coherence" : tactic => withMainContext do
  replaceMainGoal <| ← Monoidal.pureCoherence <| ← getMainGoal

end Mathlib.Tactic.Monoidal

