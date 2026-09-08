/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Lifting properties in Over categories

In this file, we show that if `sq` is a commutative square in
a category `Over S` for `S : C`, there is a lift for `sq`
if there is a lift for the underlying commutative square
in the category `C`. It follows that if `i` and `p` are
morphisms in `Over S`, then `i` has the left lifting
property with respect to `p` when `i.left` has
the left lifting property with respect to `p.left`.

-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

namespace CommSq.HasLift

/-
**CategoryTheory.CommSq.HasLift.over** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
ommSq.HasLift`。
形式化陈述：over {X₁ X₂ X₃ X₄ : Over S} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b :
 X₃ ⟶ X₄} {sq : CommSq t l r b} [CommSq.HasLift (f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.map`：∀ {C : Type u_1} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} 
D] (F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.CommSq.fac_right_assoc`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X} 
  {g : Y ⟶ B} (sq : Categor…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
-/
lemma over {X₁ X₂ X₃ X₄ : Over S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} {sq : CommSq t l r b}
    [CommSq.HasLift (f := t.left) (i := l.left) (p := r.left) (g := b.left)
      (sq.map (Over.forget _))] :
    sq.HasLift := by
  let sq' := sq.map (Over.forget _)
  dsimp at sq'
  exact ⟨⟨{
    l := Over.homMk sq'.lift
      (by rw [← Over.w b, ← sq'.fac_right_assoc, Over.w r])
  }⟩⟩

end CommSq.HasLift

namespace HasLiftingProperty

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.HasLiftingProperty.over** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.HasLiftingProperty`。
形式化陈述：over {A B X Y : Over S} (i : A ⟶ B) (p : X ⟶ Y) [HasLiftingProperty i.left
 p.left] : HasLiftingProperty i p
参数：i : A ⟶ B；p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CommSq.HasLift.over`：over {X₁ X₂ X₃ X₄ : Over S} {t : X₁ 
⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} {sq : CommSq t l r b} [CommSq.Ha
sLift (f
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.CommSq.map`：∀ {C : Type u_1} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} 
D] (F : Categor…
-/
lemma over {A B X Y : Over S}
    (i : A ⟶ B) (p : X ⟶ Y) [HasLiftingProperty i.left p.left] :
    HasLiftingProperty i p := ⟨fun _ ↦ .over⟩

end HasLiftingProperty

end CategoryTheory

