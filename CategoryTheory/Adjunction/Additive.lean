/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Adjunctions between additive functors.

This provides some results and constructions for adjunctions between functors on
preadditive categories:
* If one of the adjoint functors is additive, so is the other.
* If one of the adjoint functors is additive, the equivalence `Adjunction.homEquiv` lifts to
  an additive equivalence `Adjunction.homAddEquiv`.
* We also give a version of this additive equivalence as an isomorphism of `preadditiveYoneda`
  functors (analogous to `Adjunction.compYonedaIso`), in `Adjunction.compPreadditiveYonedaIso`.

-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open CategoryTheory Category CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

/-
**CategoryTheory.Adjunction.right_adjoint_additive** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：right_adjoint_additive [F.Additive] : G.Additive where map_add {X Y} f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma right_adjoint_additive [F.Additive] : G.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.left_adjoint_additive** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：left_adjoint_additive [G.Additive] : F.Additive where map_add {X Y} f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma left_adjoint_additive [G.Additive] : F.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

variable [F.Additive]

set_option backward.defeqAttrib.useBackward true in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an `AddEquiv`.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
/-
**CategoryTheory.Adjunction.homAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：homAddEquiv (X : C) (Y : D) : AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y)
参数：X : C；Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have an adjunction `adj : F ⊣ G` of functors between preadditive categorie
s,
and if `F` is additive, then the hom set equivalence upgrades to an `AddEquiv`.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_ad
ditive` and
`Adjunction.left_adjoint_additive`.
-/
def homAddEquiv (X : C) (Y : D) : AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  { adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：homAddEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) : adj.homAddEquiv X Y 
f = adj.homEquiv X Y f
参数：X : C；Y : D；f : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homAddEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homAddEquiv X Y f = adj.homEquiv X Y f := rfl

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：homAddEquiv_symm_apply (X : C) (Y : D) (f : X ⟶ G.obj Y) : (adj.homAddEqui
v X Y).symm f = (adj.homEquiv X Y).symm f
参数：X : C；Y : D；f : X ⟶ G.obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homAddEquiv_symm_apply (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv X Y).symm f = (adj.homEquiv X Y).symm f := rfl

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_zero** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：homAddEquiv_zero (X : C) (Y : D) : adj.homEquiv X Y 0 = 0
参数：X : C；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_zero (X : C) (Y : D) : adj.homEquiv X Y 0 = 0 := map_zero (adj.homAddEquiv X Y)

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：homAddEquiv_add (X : C) (Y : D) (f f' : F.obj X ⟶ Y) : adj.homEquiv X Y (f
 + f') = adj.homEquiv X Y f + adj.homEquiv X Y f'
参数：X : C；Y : D；f f' : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_add (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f + f') = adj.homEquiv X Y f + adj.homEquiv X Y f' :=
  map_add (adj.homAddEquiv X Y) _ _

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_sub** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：homAddEquiv_sub (X : C) (Y : D) (f f' : F.obj X ⟶ Y) : adj.homEquiv X Y (f
 - f') = adj.homEquiv X Y f - adj.homEquiv X Y f'
参数：X : C；Y : D；f f' : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_sub (X : C) (Y : D) (f f' : F.obj X ⟶ Y) :
    adj.homEquiv X Y (f - f') = adj.homEquiv X Y f - adj.homEquiv X Y f' :=
  map_sub (adj.homAddEquiv X Y) _ _

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_neg** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：homAddEquiv_neg (X : C) (Y : D) (f : F.obj X ⟶ Y) : adj.homEquiv X Y (-f) 
= - adj.homEquiv X Y f
参数：X : C；Y : D；f : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_neg (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homEquiv X Y (-f) = - adj.homEquiv X Y f := map_neg (adj.homAddEquiv X Y) _

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_symm_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：homAddEquiv_symm_zero (X : C) (Y : D) : (adj.homEquiv X Y).symm 0 = 0
参数：X : C；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_symm_zero (X : C) (Y : D) :
    (adj.homEquiv X Y).symm 0 = 0 := map_zero (adj.homAddEquiv X Y).symm

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_symm_add** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：homAddEquiv_symm_add (X : C) (Y : D) (f f' : X ⟶ G.obj Y) : (adj.homEquiv 
X Y).symm (f + f') = (adj.homEquiv X Y).symm f + (adj.homEquiv X Y).symm f'
参数：X : C；Y : D；f f' : X ⟶ G.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_symm_add (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f + f') = (adj.homEquiv X Y).symm f + (adj.homEquiv X Y).symm f' :=
  map_add (adj.homAddEquiv X Y).symm _ _

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_symm_sub** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：homAddEquiv_symm_sub (X : C) (Y : D) (f f' : X ⟶ G.obj Y) : (adj.homEquiv 
X Y).symm (f - f') = (adj.homEquiv X Y).symm f - (adj.homEquiv X Y).symm f'
参数：X : C；Y : D；f f' : X ⟶ G.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_symm_sub (X : C) (Y : D) (f f' : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (f - f') = (adj.homEquiv X Y).symm f - (adj.homEquiv X Y).symm f' :=
  map_sub (adj.homAddEquiv X Y).symm _ _

@[simp]
/-
**CategoryTheory.Adjunction.homAddEquiv_symm_neg** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：homAddEquiv_symm_neg (X : C) (Y : D) (f : X ⟶ G.obj Y) : (adj.homEquiv X Y
).symm (-f) = - (adj.homEquiv X Y).symm f
参数：X : C；Y : D；f : X ⟶ G.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma homAddEquiv_symm_neg (X : C) (Y : D) (f : X ⟶ G.obj Y) :
    (adj.homEquiv X Y).symm (-f) = - (adj.homEquiv X Y).symm f :=
  map_neg (adj.homAddEquiv X Y).symm _

open Opposite in
/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the necessary
universe lifting functors.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_additive` and
`Adjunction.left_adjoint_additive`.
-/
/-
**CategoryTheory.Adjunction.compPreadditiveYonedaIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：compPreadditiveYonedaIso : G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _)
.obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} ≅ preadditiveYoneda ⋙ (whiskeringLef
t _ _ _).obj F.op ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max 
v₁ v₂}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have an adjunction `adj : F ⊣ G` of functors between preadditive categorie
s,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism 
between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the necess
ary
universe lifting functors.
Note that `F` is additive if and only if `G` is, by `Adjunction.right_adjoint_ad
ditive` and
`Adjunction.left_adjoint_additive`.
-/
def compPreadditiveYonedaIso :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} ≅
      preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
        (whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max v₁ v₂} :=
  NatIso.ofComponents
    (fun Y ↦ NatIso.ofComponents
      (fun X ↦ (AddEquiv.ulift.trans ((adj.homAddEquiv (unop X) Y).symm.trans
        AddEquiv.ulift.symm)).toAddCommGrpIso)
      (fun g ↦ by
        ext ⟨y⟩
        exact AddEquiv.ulift.injective (adj.homEquiv_naturality_left_symm g.unop y)))
    (fun f ↦ by
      ext _ ⟨x⟩
      exact AddEquiv.ulift.injective ((adj.homEquiv_naturality_right_symm x f)))
/-
**CategoryTheory.Adjunction.compPreadditiveYonedaIso_hom_app_app_apply** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：compPreadditiveYonedaIso_hom_app_app_apply (X : Cᵒᵖ) (Y : D) (a : ULift.{m
ax v₁ v₂, v₁} (Opposite.unop X ⟶ G.obj Y)) : ((adj.compPreadditiveYonedaIso.hom.
app Y).app X) a = ULift.up ((adj.homEquiv (Opposite.unop X) Y).symm (AddEquiv.ul
ift a))
参数：X : Cᵒᵖ；Y : D；a : ULift.{max v₁ v₂, v₁} (Opposite.unop X ⟶ G.obj Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compPreadditiveYonedaIso_hom_app_app_apply (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₁} (Opposite.unop X ⟶ G.obj Y)) :
      ((adj.compPreadditiveYonedaIso.hom.app Y).app X) a =
        ULift.up ((adj.homEquiv (Opposite.unop X) Y).symm (AddEquiv.ulift a)) := rfl
/-
**CategoryTheory.Adjunction.compPreadditiveYonedaIso_inv_app_app_apply** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：compPreadditiveYonedaIso_inv_app_app_apply (X : Cᵒᵖ) (Y : D) (a : ULift.{m
ax v₁ v₂, v₂} (F.obj (Opposite.unop X) ⟶ Y)) : ((adj.compPreadditiveYonedaIso.in
v.app Y).app X) a = ULift.up ((adj.homEquiv (Opposite.unop X) Y) (AddEquiv.ulift
 a))
参数：X : Cᵒᵖ；Y : D；a : ULift.{max v₁ v₂, v₂} (F.obj (Opposite.unop X) ⟶ Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compPreadditiveYonedaIso_inv_app_app_apply (X : Cᵒᵖ) (Y : D)
    (a : ULift.{max v₁ v₂, v₂} (F.obj (Opposite.unop X) ⟶ Y)) :
      ((adj.compPreadditiveYonedaIso.inv.app Y).app X) a =
        ULift.up ((adj.homEquiv (Opposite.unop X) Y) (AddEquiv.ulift a)) := rfl

end Adjunction

end CategoryTheory

