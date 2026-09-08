/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The category of points of a site

We define the category structure on the points of a site `(C, J)`:
a morphism between `Φ₁ ⟶ Φ₂` between two points consists of a
morphism `Φ₂.fiber ⟶ Φ₁.fiber` (SGA 4 IV 3.2).

## References
* [Alexander Grothendieck and Jean-Louis Verdier, *Exposé IV : Topos*,
  SGA 4 IV 3.2][sga-4-tome-1]

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- A morphism between points of a site consists of a morphism
between the functors `Point.fiber`, in the opposite direction. -/
@[ext]
/-
**CategoryTheory.GrothendieckTopology.Point.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.GrothendieckTopology.Point`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} → J.Point → J.Point → Type (max u w)
参数：max u w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between points of a site consists of a morphism
between the functors `Point.fiber`, in the opposite direction.
-/
structure Hom (Φ₁ Φ₂ : Point.{w} J) where
  /-- a natural transformation, in the opposite direction -/
  hom : Φ₂.fiber ⟶ Φ₁.fiber
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Point.{w} J) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨g.hom ≫ f.hom⟩

@[ext]
/-
**CategoryTheory.GrothendieckTopology.Point.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GrothendieckTopology.Point`。
形式化陈述：hom_ext {Φ₁ Φ₂ : Point.{w} J} {f g : Φ₁ ⟶ Φ₂} (h : f.hom = g.hom) : f = g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.Hom.ext`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTopology C} 
{Φ₁ Φ₂ : J.Point}   {x y : Φ₁.Hom Φ₂}, …
-/
lemma hom_ext {Φ₁ Φ₂ : Point.{w} J} {f g : Φ₁ ⟶ Φ₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.Point`。
形式化陈述：id_hom (Φ : Point.{w} J) : Hom.hom (𝟙 Φ) = 𝟙 _
参数：Φ : Point.{w} J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (Φ : Point.{w} J) : Hom.hom (𝟙 Φ) = 𝟙 _ := rfl

@[simp, reassoc]
/-
**CategoryTheory.GrothendieckTopology.Point.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：comp_hom {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃) : (f ≫ g).ho
m = g.hom ≫ f.hom
参数：f : Φ₁ ⟶ Φ₂；g : Φ₂ ⟶ Φ₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃) :
    (f ≫ g).hom = g.hom ≫ f.hom := rfl

variable {A : Type u'} [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

namespace Hom

variable {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃)

attribute [local simp] FunctorToTypes.naturality in
/-- The natural transformation on fibers of presheaves that is induced
by a morphism of points of a site. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.Hom`。
形式化陈述：presheafFiber : Φ₂.presheafFiber (A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation on fibers of presheaves that is induced
by a morphism of points of a site.
-/
noncomputable def presheafFiber :
    Φ₂.presheafFiber (A := A) ⟶ Φ₁.presheafFiber where
  app P := Φ₂.presheafFiberDesc (fun X x ↦ Φ₁.toPresheafFiber X (f.hom.app X x) P)

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_id** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.Hom`。
形式化陈述：presheafFiber_id (Φ : Point.{w} J) : presheafFiber (𝟙 Φ) (A
参数：Φ : Point.{w} J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext`：preshea
fFiber_hom_ext {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T} (h : fora
ll (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_app`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothendie
ckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.presheafFiberDesc.congr_simp`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Gro
thendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberD
esc`：toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) : Φ.toPreshea
fFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma presheafFiber_id (Φ : Point.{w} J) :
    presheafFiber (𝟙 Φ) (A := A) = 𝟙 _ := by
  cat_disch

@[reassoc, simp]
/-
**CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_comp** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.Hom`。
形式化陈述：presheafFiber_comp : (f ≫ g).presheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext`：preshea
fFiber_hom_ext {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T} (h : fora
ll (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_app`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothendie
ckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.presheafFiberDesc.congr_simp`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Gro
thendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberD
esc`：toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) : Φ.toPreshea
fFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberD
esc_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Categor
yTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma presheafFiber_comp :
    (f ≫ g).presheafFiber (A := A) = g.presheafFiber ≫ f.presheafFiber := by
  cat_disch

/-- The natural transformation on fibers of sheaves that is induced
by a morphism of points of a site. -/
/-
**CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber** 是 Mathlib 中的一个缩写定义，
位于命名空间 `CategoryTheory.GrothendieckTopology.Point.Hom`。
形式化陈述：sheafFiber : Φ₂.sheafFiber (A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation on fibers of sheaves that is induced
by a morphism of points of a site.
-/
noncomputable abbrev sheafFiber :
    Φ₂.sheafFiber (A := A) ⟶ Φ₁.sheafFiber :=
  Functor.whiskerLeft _ f.presheafFiber

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber_id** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.Hom`。
形式化陈述：sheafFiber_id (Φ : Point.{w} J) : sheafFiber (𝟙 Φ) (A
参数：Φ : Point.{w} J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_id`：presheaf
Fiber_id (Φ : Point.{w} J) : presheafFiber (𝟙 Φ) (A
-/
lemma sheafFiber_id (Φ : Point.{w} J) :
    sheafFiber (𝟙 Φ) (A := A) = 𝟙 _ := by
  cat_disch

@[reassoc, simp]
/-
**CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber_comp** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point.Hom`。
形式化陈述：sheafFiber_comp : (f ≫ g).sheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_comp`：preshe
afFiber_comp : (f ≫ g).presheafFiber (A
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_app`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothendie
ckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
-/
lemma sheafFiber_comp :
    (f ≫ g).sheafFiber (A := A) = g.sheafFiber ≫ f.sheafFiber := by
  cat_disch

end Hom

end GrothendieckTopology.Point

end CategoryTheory

