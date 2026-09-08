/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tor, the left-derived functor of tensor product

We define `Tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.

For now we have almost nothing to say about it!

It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
For now we define `Tor'` by left-deriving in the first factor,
but showing `Tor C n ≅ Tor' C n` will require a bit more theory!
Possibly it's best to axiomatize delta functors, and obtain a unique characterisation?

-/

@[expose] public section


assert_not_exists ModuleCat.abelian

noncomputable section

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable (C : Type*) [Category* C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
/-
**CategoryTheory.Tor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Tor (n : Nat) : C ⥤ C ⥤ C where obj X
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y)
 ↦ X ⊗ Y`.
-/
def Tor (n : ℕ) : C ⥤ C ⥤ C where
  obj X := Functor.leftDerived ((tensoringLeft C).obj X) n
  map f := NatTrans.leftDerived ((tensoringLeft C).map f) n

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps! obj_obj map_app obj_map]
/-
**CategoryTheory.Tor'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Tor' (n : Nat) : C ⥤ C ⥤ C
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An alternative definition of `Tor`, where we left-derive in the first factor ins
tead.
-/
def Tor' (n : ℕ) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun f => NatTrans.leftDerived ((tensoringRight C).map f) n }

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
/-
**CategoryTheory.isZero_Tor_succ_of_projective** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：isZero_Tor_succ_of_projective (X Y : C) [Projective Y] (n : Nat) : IsZero 
(((Tor C (n + 1)).obj X).obj Y)
参数：X Y : C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : Categor
yTheory.Category.{v_1, u_1} D]   [inst_2 : Category…

--- 原说明 ---
The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective.
-/
lemma isZero_Tor_succ_of_projective (X Y : C) [Projective Y] (n : ℕ) :
    IsZero (((Tor C (n + 1)).obj X).obj Y) := by
  apply Functor.isZero_leftDerived_obj_projective_succ

/-- The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective. -/
/-
**CategoryTheory.isZero_Tor'_succ_of_projective** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Abelian C] [inst_3 
: CategoryTheory.MonoidalPreadditive C]   [inst_4 : CategoryTheory.HasProjective
Resolutions C] (X Y : C) [CategoryTheory.Projective X] (n : ℕ),   CategoryTheory
.Limits.IsZero (((CategoryTheory.Tor' C (n + 1)).obj X).obj Y)
参数：C : Type u_1；X Y : C；n : ℕ；((CategoryTheory.Tor' C (n + 1)).obj X).obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : Categor
yTheory.Category.{v_1, u_1} D]   [inst_2 : Category…

--- 原说明 ---
The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective.
-/
lemma isZero_Tor'_succ_of_projective (X Y : C) [Projective X] (n : ℕ) :
    IsZero (((Tor' C (n + 1)).obj X).obj Y) := by
  apply Functor.isZero_leftDerived_obj_projective_succ

end CategoryTheory

