/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes
public import Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes
public import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence

/-!
# Coherence tactic for bicategories

We provide a `bicategory_coherence` tactic,
which proves that any two morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike Bicategory

namespace Mathlib.Tactic.Bicategory

section

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

local infixr:81 " ◁ " => Bicategory.whiskerLeftIso
local infixl:81 " ▷ " => Bicategory.whiskerRightIso

/-- The composition of the normalizing isomorphisms `η_f : p ≫ f ≅ pf` and `η_g : pf ≫ g ≅ pfg`. -/
/-
**Mathlib.Tactic.Bicategory.normalizeIsoComp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathli
b.Tactic.Bicategory`。
形式化陈述：normalizeIsoComp {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {pf : a ⟶ c} {pfg : a
 ⟶ d} (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg)
参数：η_f : p ≫ f ≅ pf；η_g : pf ≫ g ≅ pfg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of the normalizing isomorphisms `η_f : p ≫ f ≅ pf` and `η_g : pf
 ≫ g ≅ pfg`.
-/
abbrev normalizeIsoComp {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
    (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso η_f g ≪≫ η_g
/-
**Mathlib.Tactic.Bicategory.naturality_associator** 是 Mathlib 中的一个定理，位于命名空间 `Mat
hlib.Tactic.Bicategory`。
形式化陈述：naturality_associator {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf 
: a ⟶ c} {pfg : a ⟶ d} {pfgh : a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg) (η
_h : pfg ≫ h ≅ pfgh) : p ◁ (α_ f g h) ≪≫ (normalizeIsoComp η_f (normalizeIsoComp
 η_g η_h)) = (normalizeIsoComp (normalizeIsoComp η_f η_g) η_h)
参数：η_f : p ≫ f ≅ pf；η_g : pf ≫ g ≅ pfg；η_h : pfg ≫ h ≅ pfgh。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {B : Typ
e u} [inst : CategoryTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c
) (h : c ⟶ d) (i : d ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_associator
    {p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh : a ⟶ e}
    (η_f : p ≫ f ≅ pf) (η_g : pf ≫ g ≅ pfg) (η_h : pfg ≫ h ≅ pfgh) :
    p ◁ (α_ f g h) ≪≫ (normalizeIsoComp η_f (normalizeIsoComp η_g η_h)) =
    (normalizeIsoComp (normalizeIsoComp η_f η_g) η_h) :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.naturality_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Mat
hlib.Tactic.Bicategory`。
形式化陈述：naturality_leftUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ 
pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p) η_f
参数：η_f : p ≫ f ≅ pf。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc_comp_right_assoc`：∀ {B : Type u
} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c) {Z : 
a ⟶ c}   (h : CategoryTheory.CategoryStruct.com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_leftUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (λ_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p) η_f :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.naturality_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Tactic.Bicategory`。
形式化陈述：naturality_rightUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅
 pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (ρ_ pf)
参数：η_f : p ≫ f ≅ pf。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_rightUnitor {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (ρ_ pf) :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.naturality_id** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Bicategory`。
形式化陈述：naturality_id {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p 
◁ Iso.refl f ≪≫ η_f = η_f
参数：η_f : p ≫ f ≅ pf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_id {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) :
    p ◁ Iso.refl f ≪≫ η_f = η_f :=
  Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.naturality_comp** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Bicategory`。
形式化陈述：naturality_comp {p : a ⟶ b} {f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : 
g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (ih_η : p ◁ η ≪≫
 η_g = η_f) (ih_θ : p ◁ θ ≪≫ η_h = η_g) : p ◁ (η ≪≫ θ) ≪≫ η_h = η_f
参数：η_f : p ≫ f ≅ pf；η_g : p ≫ g ≅ pf；η_h : p ≫ h ≅ pf；ih_η : p ◁ η ≪≫ η_g = η_f；
ih_θ : p ◁ θ ≪≫ η_h = η_g。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_comp {p : a ⟶ b} {f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h}
    (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (η_h : p ≫ h ≅ pf)
    (ih_η : p ◁ η ≪≫ η_g = η_f) (ih_θ : p ◁ θ ≪≫ η_h = η_g) :
    p ◁ (η ≪≫ θ) ≪≫ η_h = η_f := by
  rw [← ih_η, ← ih_θ]
  apply Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.naturality_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Tactic.Bicategory`。
形式化陈述：naturality_whiskerLeft {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} 
{pfg : a ⟶ d} {η : g ≅ h} (η_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg) (η_fh : pf ≫ 
h ≅ pfg) (ih_η : pf ◁ η ≪≫ η_fh = η_fg) : p ◁ (f ◁ η) ≪≫ normalizeIsoComp η_f η_
fh = normalizeIsoComp η_f η_fg
参数：η_f : p ≫ f ≅ pf；η_fg : pf ≫ g ≅ pfg；η_fh : pf ≫ h ≅ pfg；ih_η : pf ◁ η ≪≫ η_f
h = η_fg。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_whiskerLeft {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d}
    {η : g ≅ h} (η_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg) (η_fh : pf ≫ h ≅ pfg)
    (ih_η : pf ◁ η ≪≫ η_fh = η_fg) :
    p ◁ (f ◁ η) ≪≫ normalizeIsoComp η_f η_fh = normalizeIsoComp η_f η_fg := by
  rw [← ih_η]
  apply Iso.ext (by simp [← whisker_exchange_assoc])
/-
**Mathlib.Tactic.Bicategory.naturality_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.Bicategory`。
形式化陈述：naturality_whiskerRight {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c}
 {pfh : a ⟶ d} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (η_fh : pf ≫ h 
≅ pfh) (ih_η : p ◁ η ≪≫ η_g = η_f) : p ◁ (η ▷ h) ≪≫ normalizeIsoComp η_g η_fh = 
normalizeIsoComp η_f η_fh
参数：η_f : p ≫ f ≅ pf；η_g : p ≫ g ≅ pf；η_fh : pf ≫ h ≅ pfh；ih_η : p ◁ η ≪≫ η_g = η
_f。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_whiskerRight {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d}
    {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (η_fh : pf ≫ h ≅ pfh)
    (ih_η : p ◁ η ≪≫ η_g = η_f) :
    p ◁ (η ▷ h) ≪≫ normalizeIsoComp η_g η_fh = normalizeIsoComp η_f η_fh := by
  rw [← ih_η]
  apply Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.naturality_inv** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Bicategory`。
形式化陈述：naturality_inv {p : a ⟶ b} {f g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p
 ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : p ◁ η ≪≫ η_g = η_f) : p ◁ η.symm ≪≫ η_f = η_
g
参数：η_f : p ≫ f ≅ pf；η_g : p ≫ g ≅ pf；ih : p ◁ η ≪≫ η_g = η_f。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_inv_hom_assoc`：∀ {B : Type u} [ins
t : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ 
h) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_inv {p : a ⟶ b} {f g : b ⟶ c} {pf : a ⟶ c}
    {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : p ◁ η ≪≫ η_g = η_f) :
    p ◁ η.symm ≪≫ η_f = η_g := by
  rw [← ih]
  apply Iso.ext (by simp)
/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonadNormalizeNaturality BicategoryM where
  mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have e : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($d ⟶ $e) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have pfgh : Q($a ⟶ $e) := pfgh.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($pf ≫ $g ≅ $pfg) := η_g.e
    have η_h : Q($pfg ≫ $h ≅ $pfgh) := η_h.e
    return q(naturality_associator $η_f $η_g $η_h)
  mkNaturalityLeftUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_leftUnitor $η_f)
  mkNaturalityRightUnitor p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_rightUnitor $η_f)
  mkNaturalityId p pf f η_f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    return q(naturality_id $η_f)
  mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($b ⟶ $c) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have θ : Q($g ≅ $h) := θ.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_h : Q($p ≫ $h ≅ $pf) := η_h.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    have ih_θ : Q($p ◁ $θ ≪≫ $η_h = $η_g) := ih_θ
    return q(naturality_comp $η_f $η_g $η_h $ih_η $ih_θ)
  mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := g.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($c ⟶ $d) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfg : Q($a ⟶ $d) := pfg.e.e
    have η : Q($g ≅ $h) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_fg : Q($pf ≫ $g ≅ $pfg) := η_fg.e
    have η_fh : Q($pf ≫ $h ≅ $pfg) := η_fh.e
    have ih_η : Q($pf ◁ $η ≪≫ $η_fh = $η_fg) := ih_η
    return q(naturality_whiskerLeft $η_f $η_fg $η_fh $ih_η)
  mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih_η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have h : Q($c ⟶ $d) := h.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have pfh : Q($a ⟶ $d) := pfh.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have η_fh : Q($pf ≫ $h ≅ $pfh) := η_fh.e
    have ih_η : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih_η
    return q(naturality_whiskerRight $η_f $η_g $η_fh $ih_η)
  mkNaturalityHorizontalComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := do
    throwError "horizontal composition is not implemented"
  mkNaturalityInv p pf f g η η_f η_g ih := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := p.src.e
    have b : Q($ctx.B) := p.tgt.e
    have c : Q($ctx.B) := f.tgt.e
    have p : Q($a ⟶ $b) := p.e.e
    have f : Q($b ⟶ $c) := f.e
    have g : Q($b ⟶ $c) := g.e
    have pf : Q($a ⟶ $c) := pf.e.e
    have η : Q($f ≅ $g) := η.e
    have η_f : Q($p ≫ $f ≅ $pf) := η_f.e
    have η_g : Q($p ≫ $g ≅ $pf) := η_g.e
    have ih : Q($p ◁ $η ≪≫ $η_g = $η_f) := ih
    return q(naturality_inv $η_f $η_g $ih)
/-
**Mathlib.Tactic.Bicategory.of_normalize_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Bicategory`。
形式化陈述：of_normalize_eq {f g f' : a ⟶ b} {η θ : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g :
 𝟙 a ≫ g ≅ f') (h_η : 𝟙 a ◁ η ≪≫ η_g = η_f) (h_θ : 𝟙 a ◁ θ ≪≫ η_g = η_f) : η = θ
参数：η_f : 𝟙 a ≫ f ≅ f'；η_g : 𝟙 a ≫ g ≅ f'；h_η : 𝟙 a ◁ η ≪≫ η_g = η_f；h_θ : 𝟙 a ◁ 
θ ≪≫ η_g = η_f。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
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
theorem of_normalize_eq {f g f' : a ⟶ b} {η θ : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
    (h_η : 𝟙 a ◁ η ≪≫ η_g = η_f)
    (h_θ : 𝟙 a ◁ θ ≪≫ η_g = η_f) : η = θ := by
  apply Iso.ext
  calc
    η.hom = (λ_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (λ_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_η)]
    _ = θ.hom := by
      simp [← reassoc_of% (congrArg Iso.hom h_θ)]
/-
**Mathlib.Tactic.Bicategory.mk_eq_of_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.Bicategory`。
形式化陈述：mk_eq_of_naturality {f g f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 
𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f') (Hη : η'.hom = η) (Hθ : θ'.hom = θ) (Hη' : wh
iskerLeftIso (𝟙 a) η' ≪≫ η_g = η_f) (Hθ' : whiskerLeftIso (𝟙 a) θ' ≪≫ η_g = η_f)
 : η = θ
参数：η_f : 𝟙 a ≫ f ≅ f'；η_g : 𝟙 a ≫ g ≅ f'；Hη : η'.hom = η；Hθ : θ'.hom = θ；Hη' : w
hiskerLeftIso (𝟙 a) η' ≪≫ η_g = η_f；Hθ' : whiskerLeftIso (𝟙 a) θ' ≪≫ η_g = η_f。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
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
theorem mk_eq_of_naturality {f g f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g}
    (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ f')
    (Hη : η'.hom = η) (Hθ : θ'.hom = θ)
    (Hη' : whiskerLeftIso (𝟙 a) η' ≪≫ η_g = η_f)
    (Hθ' : whiskerLeftIso (𝟙 a) θ' ≪≫ η_g = η_f) : η = θ :=
  calc
    η = η'.hom := Hη.symm
    _ = (λ_ f).inv ≫ η_f.hom ≫ η_g.inv ≫ (λ_ g).hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hη')]
    _ = θ'.hom := by
      simp [← reassoc_of% (congrArg Iso.hom Hθ')]
    _ = θ := Hθ

end

/-
**Mathlib.Tactic.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MkEqOfNaturality BicategoryM where
  mkEqOfNaturality η θ ηIso θIso η_f η_g Hη Hθ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let η' := ηIso.e
    let θ' := θIso.e
    let f ← η'.srcM
    let g ← η'.tgtM
    let f' ← η_f.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f : Q($a ⟶ $b) := f.e
    have g : Q($a ⟶ $b) := g.e
    have f' : Q($a ⟶ $b) := f'.e
    have η : Q($f ⟶ $g) := η
    have θ : Q($f ⟶ $g) := θ
    have η'_e : Q($f ≅ $g) := η'.e
    have θ'_e : Q($f ≅ $g) := θ'.e
    have η_f : Q(𝟙 $a ≫ $f ≅ $f') := η_f.e
    have η_g : Q(𝟙 $a ≫ $g ≅ $f') := η_g.e
    have η_hom : Q(Iso.hom $η'_e = $η) := ηIso.eq
    have Θ_hom : Q(Iso.hom $θ'_e = $θ) := θIso.eq
    have Hη : Q(whiskerLeftIso (𝟙 $a) $η'_e ≪≫ $η_g = $η_f) := Hη
    have Hθ : Q(whiskerLeftIso (𝟙 $a) $θ'_e ≪≫ $η_g = $η_f) := Hθ
    return q(mk_eq_of_naturality $η_f $η_g $η_hom $Θ_hom $Hη $Hθ)

open Elab.Tactic

/-- Close the goal of the form `η.hom = θ.hom`, where `η` and `θ` are 2-isomorphisms made up only of
associators, unitors, and identities.
```lean
example {B : Type} [Bicategory B] {a : B} :
  (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  bicategory_coherence
```
-/
/-
**Mathlib.Tactic.Bicategory.pureCoherence** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.Bicategory`。
形式化陈述：pureCoherence (mvarId : MVarId) : MetaM (List MVarId)
参数：mvarId : MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Close the goal of the form `η.hom = θ.hom`, where `η` and `θ` are 2-isomorphisms
 made up only of
associators, unitors, and identities.
```lean
example {B : Type} [Bicategory B] {a : B} :
  (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  bicategory_coherence
```
-/
def pureCoherence (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.pureCoherence Bicategory.Context `bicategory mvarId

@[inherit_doc pureCoherence]
elab "bicategory_coherence" : tactic => withMainContext do
  replaceMainGoal <| ← Bicategory.pureCoherence <| ← getMainGoal

end Mathlib.Tactic.Bicategory

