/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Distributive.Monoidal
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!

# Distributive categories

## Main definitions

A category `C` with finite products and binary coproducts is called distributive if the
canonical distributivity morphism `(X ⨯ Y) ⨿ (X ⨯ Z) ⟶ X ⨯ (Y ⨿ Z)` is an isomorphism
for all objects `X`, `Y`, and `Z` in `C`.

## Implementation Details

A Cartesian distributive category is defined as a Cartesian monoidal category which is
monoidal distributive.

## Main results

- The coproduct coprojections are monic in a Cartesian distributive category.


## TODO

- Every Cartesian distributive category is finitary distributive, meaning that
  the left tensor product functor `X ⊗ -` preserves all finite coproducts.

- Show that any extensive distributive category can be embedded into a topos.

## References

- [J.R.B.Cockett, Introduction to distributive categories, 1993][cockett1993]
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]
-/

public section

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory Distributive CartesianMonoidalCategory

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryCoproducts C]

/-- A category `C` with finite products is Cartesian distributive if it is monoidal distributive
with respect to the Cartesian monoidal structure. -/
/-
**CategoryTheory.IsCartesianDistributive** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：IsCartesianDistributive
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` with finite products is Cartesian distributive if it is monoidal 
distributive
with respect to the Cartesian monoidal structure.
-/
abbrev IsCartesianDistributive :=
  IsMonoidalDistrib C

namespace IsCartesianDistributive

/-- To show a category is Cartesian distributive it is enough to show it is left distributive.
The right distributivity is inferred from symmetry of the Cartesian monoidal structure. -/
/-
**CategoryTheory.IsCartesianDistributive.of_isMonoidalLeftDistrib** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.IsCartesianDistributive`。
形式化陈述：of_isMonoidalLeftDistrib [IsMonoidalLeftDistrib C] : IsCartesianDistributi
ve C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDist
rib`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instNonemptyBraidedCategory`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
CartesianMonoidalCategory C],   Nonempty (CategoryTheory.B…

--- 原说明 ---
To show a category is Cartesian distributive it is enough to show it is left dis
tributive.
The right distributivity is inferred from symmetry of the Cartesian monoidal str
ucture.
-/
lemma of_isMonoidalLeftDistrib [IsMonoidalLeftDistrib C] : IsCartesianDistributive C :=
  letI : BraidedCategory C := Nonempty.some inferInstance
  SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

set_option backward.isDefEq.respectTransparency false in
/-- The coproduct coprojections are monic in a Cartesian distributive category. -/
/-
**CategoryTheory.IsCartesianDistributive.monoCoprod** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.IsCartesianDistributive`。
形式化陈述：monoCoprod [IsCartesianDistributive C] : MonoCoprod C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoCoprod.mk'`：mk' (h : forall A B : C, exists (c
 : BinaryCofan A B) (_ : IsColimit c), Mono c.inl) : MonoCoprod C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.SplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   Ca
tegoryTheory.Mono f
· 使用定理 `CategoryTheory.IsMonoidalDistrib.toIsMonoidalLeftDistrib`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCate
gory C}   {inst_2 : CategoryTheory.Limits.HasB…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.whiskerLeft_coprod_inl_leftDistrib_inv_assoc`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Monoi
dalCategory C]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft`：lift_whiskerL
eft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) : lift f g ≫ (Y ◁ h) = lif
t f (g ≫ h)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h

--- 原说明 ---
The coproduct coprojections are monic in a Cartesian distributive category.
-/
instance monoCoprod [IsCartesianDistributive C] : MonoCoprod C :=
  MonoCoprod.mk' fun A B =>
    ⟨_, coprodIsCoprod A B, ⟨fun {Z} f g he ↦ by
      let ι := coprod.inl (X := A) (Y := B)
      have : Mono (Z ◁ ι) := SplitMono.mono
        { retraction := (∂L Z A B).inv ≫ coprod.desc (𝟙 _) (fst Z B ≫ lift (𝟙 Z) f) }
      have : lift (𝟙 Z) f = lift (𝟙 Z) g := by rw [← cancel_mono (Z ◁ ι)]; aesop
      simpa only [lift_snd] using this =≫ snd _ _⟩⟩

end IsCartesianDistributive

end CategoryTheory

