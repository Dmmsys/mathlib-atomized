/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
/-!

# Conditions for `parallelPair` to be initial

In this file we give sufficient conditions on a category `C` and parallel morphisms `f g : X ⟶ Y`
in `C` so that `parallelPair f g` becomes an initial functor.

The conditions are that there is a morphism out of `X` to every object of `C` and that any two
parallel morphisms out of `X` factor through the parallel pair `f`, `g`
(`h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z), ∃ (a : Y ⟶ Z), i = f ≫ a ∧ j = g ≫ a`).
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

open WalkingParallelPair WalkingParallelPairHom CostructuredArrow

/-
**CategoryTheory.Limits.parallelPair_initial_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：parallelPair_initial_mk' {X Y : C} (f g : X ⟶ Y) (h₁ : forall Z, Nonempty 
(X ⟶ Z)) (h₂ : forall ⦃Z : C⦄ (i j : X ⟶ Z), Zigzag (J
参数：f g : X ⟶ Y；h₁ : forall Z, Nonempty (X ⟶ Z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `CategoryTheory.Zigzag.symm`：∀ {J : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.Zigz
ag j₂ j₁
-/
lemma parallelPair_initial_mk' {X Y : C} (f g : X ⟶ Y)
    (h₁ : ∀ Z, Nonempty (X ⟶ Z))
    (h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z),
      Zigzag (J := CostructuredArrow (parallelPair f g) Z)
        (mk (Y := zero) i) (mk (Y := zero) j)) :
    (parallelPair f g).Initial where
  out Z := by
    have : Nonempty (CostructuredArrow (parallelPair f g) Z) :=
      ⟨mk (Y := zero) (h₁ Z).some⟩
    have : ∀ (x : CostructuredArrow (parallelPair f g) Z), Zigzag x
      (mk (Y := zero) (h₁ Z).some) := by
        rintro ⟨(_ | _), ⟨⟩, φ⟩
        · apply h₂
        · refine Zigzag.trans ?_ (h₂ (f ≫ φ) _)
          exact Zigzag.of_inv (homMk left)
    exact zigzag_isConnected (fun x y => (this x).trans (this y).symm)
/-
**CategoryTheory.Limits.parallelPair_initial_mk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：parallelPair_initial_mk {X Y : C} (f g : X ⟶ Y) (h₁ : forall Z, Nonempty (
X ⟶ Z)) (h₂ : forall ⦃Z : C⦄ (i j : X ⟶ Z), exists (a : Y ⟶ Z), i = f ≫ a ∧ j = 
g ≫ a) : (parallelPair f g).Initial
参数：f g : X ⟶ Y；h₁ : forall Z, Nonempty (X ⟶ Z)；h₂ : forall ⦃Z : C⦄ (i j : X ⟶ Z)
, exists (a : Y ⟶ Z), i = f ≫ a ∧ j = g ≫ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.parallelPair_initial_mk'`：parallelPair_initial_mk'
 {X Y : C} (f g : X ⟶ Y) (h₁ : forall Z, Nonempty (X ⟶ Z)) (h₂ : forall ⦃Z : C⦄ 
(i j : X ⟶ Z), Zigzag (J
· 使用定理 `CategoryTheory.Zigzag.of_hom_inv`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂),   Category
Theory.Zigzag j₁ j₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma parallelPair_initial_mk {X Y : C} (f g : X ⟶ Y)
    (h₁ : ∀ Z, Nonempty (X ⟶ Z))
    (h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z), ∃ (a : Y ⟶ Z), i = f ≫ a ∧ j = g ≫ a) :
    (parallelPair f g).Initial :=
  parallelPair_initial_mk' f g h₁ (fun Z i j => by
    obtain ⟨a, rfl, rfl⟩ := h₂ i j
    let f₁ : (mk (Y := zero) (f ≫ a) : CostructuredArrow (parallelPair f g) Z) ⟶ mk (Y := one) a :=
      homMk left
    let f₂ : (mk (Y := zero) (g ≫ a) : CostructuredArrow (parallelPair f g) Z) ⟶ mk (Y := one) a :=
      homMk right
    exact Zigzag.of_hom_inv f₁ f₂)

end Limits

end CategoryTheory

