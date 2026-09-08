/-
Copyright (c) 2026 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The currying-uncurrying isomorphism between internal homs of a closed monoidal category

For a closed monoidal category `C`, we construct the isomorphism of internal hom objects
`C(x ⊗ y, z) ≅ C(y, C(x, z))` for any triple of objects `x y z : C`.

-/

@[expose] public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The currying operation taking a morphism `(z ⊗ y) ⟶ x` to a morphism `y ⟶ C(z, x)`,
  constructed as a morphism in `C` between internal homs. -/
-- TODO: Prove naturality of this morphism (requires the appropriate instances of `[Closed _]` for
-- objects in `C`).
/-
**CategoryTheory.MonoidalClosed.ihomCurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.MonoidalClosed`。
形式化陈述：ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : (ihom 
(x otimes y)).obj z ⟶ (ihom y).obj ((ihom x).obj z)
参数：x y z : C；x otimes y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom (x ⊗ y)).obj z ⟶ (ihom y).obj ((ihom x).obj z) :=
  curry (curry ((α_ x y _).inv ≫ (ihom.ev _).app z))
/-
**CategoryTheory.MonoidalClosed.uncurry_ihomCurry** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MonoidalClosed`。
形式化陈述：uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] 
: uncurry (ihomCurry x y z) = curry ((α_ x y _).inv ≫ (ihom.ev _).app z)
参数：x y z : C；x otimes y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
-/
lemma uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (ihomCurry x y z) = curry ((α_ x y _).inv ≫ (ihom.ev _).app z) :=
  uncurry_curry _
/-
**CategoryTheory.MonoidalClosed.uncurry_uncurry_ihomCurry** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：uncurry_uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x oti
mes y)] : uncurry (uncurry (ihomCurry x y z)) = (α_ x y _).inv ≫ (ihom.ev _).app
 z
参数：x y z : C；x otimes y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalClosed.uncurry_ihomCurry`：uncurry_ihomCurry (x y 
z : C) [Closed x] [Closed y] [Closed (x otimes y)] : uncurry (ihomCurry x y z) =
 curry ((α_ x y _).inv ≫ (ihom.ev _).…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uncurry_uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (uncurry (ihomCurry x y z)) = (α_ x y _).inv ≫ (ihom.ev _).app z := by
  simp [uncurry_ihomCurry]

/-- The uncurrying operation taking a morphism `y ⟶ C(x, z)` to a morphism `(x ⊗ y) ⟶ z`,
  constructed as a morphism in `C` between internal homs. -/
-- TODO: Prove naturality of this morphism (requires the appropriate instances of `[Closed _]` for
-- objects in `C`).
/-
**CategoryTheory.MonoidalClosed.ihomUncurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoidalClosed`。
形式化陈述：ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : (iho
m y).obj ((ihom x).obj z) ⟶ (ihom (x otimes y)).obj z
参数：x y z : C；x otimes y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom y).obj ((ihom x).obj z) ⟶ (ihom (x ⊗ y)).obj z :=
  curry ((α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z)
/-
**CategoryTheory.MonoidalClosed.uncurry_ihomUncurry** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MonoidalClosed`。
形式化陈述：uncurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)
] : uncurry (ihomUncurry x y z) = (α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x)
.obj z) ≫ (ihom.ev x).app z
参数：x y z : C；x otimes y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_curry`：uncurry_curry (f : A otimes
 X ⟶ Y) : uncurry (curry f) = f
-/
lemma uncurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (ihomUncurry x y z) = (α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫
    (ihom.ev x).app z :=
  uncurry_curry _

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalClosed.ihomUncurry_ihomCurry** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalClosed`。
形式化陈述：ihomUncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes 
y)] : ihomUncurry x y z ≫ ihomCurry x y z = 𝟙 _
参数：x y z : C；x otimes y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用引理 `CategoryTheory.MonoidalClosed.uncurry_uncurry_ihomCurry`：uncurry_uncurry
_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : uncurry (un
curry (ihomCurry x y z)) = (α_ x y _).inv ≫ (…
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`：uncurry_id_eq_ev : uncur
ry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用引理 `CategoryTheory.MonoidalClosed.uncurry_ihomUncurry`：uncurry_ihomUncurry (
x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : uncurry (ihomUncurry x 
y z) = (α_ x y _).hom ≫ x ◁ (ihom.ev y)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem ihomUncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    ihomUncurry x y z ≫ ihomCurry x y z = 𝟙 _ := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry, Functor.id_obj, uncurry_id_eq_ev]
  rw [associator_inv_naturality_right_assoc, ← dsimp% uncurry_eq, uncurry_ihomUncurry]
  simp
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalClosed.ihomCurry_ihomUncurry** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalClosed`。
形式化陈述：ihomCurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes 
y)] : ihomCurry x y z ≫ ihomUncurry x y z = 𝟙 _
参数：x y z : C；x otimes y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_injective`：uncurry_injective : Fun
ction.Injective (uncurry : (Y ⟶ A ⟶[C] X) -> (A otimes Y ⟶ X))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_natural_left`：uncurry_natural_left
 (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) : uncurry (f ≫ g) = _ ◁ f ≫ uncurry g
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`：uncurry_id_eq_ev : uncur
ry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
· 使用引理 `CategoryTheory.MonoidalClosed.uncurry_ihomUncurry`：uncurry_ihomUncurry (
x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : uncurry (ihomUncurry x 
y z) = (α_ x y _).hom ≫ x ◁ (ihom.ev y)…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality_right_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mon
oidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用引理 `CategoryTheory.MonoidalClosed.uncurry_uncurry_ihomCurry`：uncurry_uncurry
_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : uncurry (un
curry (ihomCurry x y z)) = (α_ x y _).inv ≫ (…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ihomCurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    ihomCurry x y z ≫ ihomUncurry x y z = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_id_eq_ev, uncurry_ihomUncurry]
  dsimp
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp [← dsimp% uncurry_eq, uncurry_uncurry_ihomCurry]

/-- The internal currying-uncurrying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))`. -/
@[simps]
/-
**CategoryTheory.MonoidalClosed.ihomCurryIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MonoidalClosed`。
形式化陈述：ihomCurryIso (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : (ih
om (x otimes y)).obj z ≅ (ihom y).obj ((ihom x).obj z) where hom
参数：x y z : C；x otimes y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalClosed.ihomCurry_ihomUncurry`：ihomCurry_ihomUncur
ry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : ihomCurry x y z ≫ i
homUncurry x y z = 𝟙 _
· 使用定理 `CategoryTheory.MonoidalClosed.ihomUncurry_ihomCurry`：ihomUncurry_ihomCur
ry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] : ihomUncurry x y z ≫
 ihomCurry x y z = 𝟙 _

--- 原说明 ---
The internal currying-uncurrying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))`.
-/
def ihomCurryIso (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom (x ⊗ y)).obj z ≅ (ihom y).obj ((ihom x).obj z) where
  hom := ihomCurry x y z
  inv := ihomUncurry x y z
  hom_inv_id := ihomCurry_ihomUncurry x y z
  inv_hom_id := ihomUncurry_ihomCurry x y z

end CategoryTheory.MonoidalClosed

end

