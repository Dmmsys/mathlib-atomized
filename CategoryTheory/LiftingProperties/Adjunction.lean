/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!

# Lifting properties and adjunction

In this file, we obtain `Adjunction.HasLiftingProperty_iff`, which states
that when we have an adjunction `adj : G ⊣ F` between two functors `G : C ⥤ D`
and `F : D ⥤ C`, then a morphism of the form `G.map i` has the left lifting
property in `D` with respect to a morphism `p` if and only the morphism `i`
has the left lifting property in `C` with respect to `F.map p`.

-/

@[expose] public section


namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D] {G : C ⥤ D} {F : D ⥤ C}

to_dual_name_hint Left Right

namespace CommSq

section

variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}

/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `G.map i` and the right map is `p` has an "adjoint" commutative
square whose left map is `i` and whose right map is `F.map p`. -/
@[to_dual
/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `i` and the right map is `F.map p` has an "adjoint" commutative
square whose left map is `G.map i` and whose right map is `p`. -/]
/-
**CategoryTheory.CommSq.right_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
CommSq`。
形式化陈述：right_adjoint (sq : CommSq u (G.map i) p v) (adj : G ⊣ F) : CommSq (adj.ho
mEquiv _ _ u) i (F.map p) (adj.homEquiv _ _ v)
参数：sq : CommSq u (G.map i) p v；adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem right_adjoint (sq : CommSq u (G.map i) p v) (adj : G ⊣ F) :
    CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _ _ v) :=
  ⟨by
    simp only [Adjunction.homEquiv_unit, assoc, ← F.map_comp, sq.w]
    rw [F.map_comp, Adjunction.unit_naturality_assoc]⟩

variable (sq : CommSq u (G.map i) p v) (adj : G ⊣ F)

/-- The liftings of a commutative are in bijection with the liftings of its (right)
adjoint square. -/
@[to_dual
/-- The liftings of a commutative are in bijection with the liftings of its (left)
adjoint square. -/]
/-
**CategoryTheory.CommSq.rightAdjointLiftStructEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CommSq`。
形式化陈述：rightAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftS
truct where toFun l
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.right_adjoint`：right_adjoint (sq : CommSq u (G.map
 i) p v) (adj : G ⊣ F) : CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _
 _ v)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def rightAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftStruct where
  toFun l :=
    { l := adj.homEquiv _ _ l.l
      fac_left := by rw [← adj.homEquiv_naturality_left, l.fac_left]
      fac_right := by rw [← Adjunction.homEquiv_naturality_right, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by
        rw [← Adjunction.homEquiv_naturality_left_symm, l.fac_left]
        apply (adj.homEquiv _ _).left_inv
      fac_right := by
        rw [← Adjunction.homEquiv_naturality_right_symm, l.fac_right]
        apply (adj.homEquiv _ _).left_inv }
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- A (right) adjoint square has a lifting if and only if the original square has a lifting. -/
@[to_dual
/-- A (left) adjoint square has a lifting if and only if the original square has a lifting. -/]
/-
**CategoryTheory.CommSq.right_adjoint_hasLift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.CommSq`。
形式化陈述：right_adjoint_hasLift_iff : HasLift (sq.right_adjoint adj) ↔ HasLift sq
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.right_adjoint`：right_adjoint (sq : CommSq u (G.map
 i) p v) (adj : G ⊣ F) : CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _
 _ v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem right_adjoint_hasLift_iff : HasLift (sq.right_adjoint adj) ↔ HasLift sq := by
  simp only [HasLift.iff]
  exact Equiv.nonempty_congr (sq.rightAdjointLiftStructEquiv adj).symm

@[to_dual]
/-
**CategoryTheory.CommSq.instHasLiftRightAdjoin** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.CommSq`。
形式化陈述：instHasLiftRightAdjoin [HasLift sq] : HasLift (sq.right_adjoint adj)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.right_adjoint`：right_adjoint (sq : CommSq u (G.map
 i) p v) (adj : G ⊣ F) : CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _
 _ v)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.right_adjoint_hasLift_iff`：right_adjoint_hasLift_i
ff : HasLift (sq.right_adjoint adj) ↔ HasLift sq
-/
instance instHasLiftRightAdjoin [HasLift sq] : HasLift (sq.right_adjoint adj) := by
  rw [right_adjoint_hasLift_iff]
  infer_instance

end

end CommSq

namespace Adjunction

@[to_dual none]
/-
**CategoryTheory.Adjunction.hasLiftingProperty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：hasLiftingProperty_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : 
X ⟶ Y) : HasLiftingProperty (G.map i) p ↔ HasLiftingProperty i (F.map p)
参数：adj : G ⊣ F；i : A ⟶ B；p : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.left_adjoint`：∀ {C : Type u_1} {D : Type u_2} [ins
t : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v
_2, u_2} D] {G : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.left_adjoint_hasLift_iff`：∀ {C : Type u_1} {D : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory
.Category.{v_2, u_2} D] {G : Categor…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.CommSq.right_adjoint`：right_adjoint (sq : CommSq u (G.map
 i) p v) (adj : G ⊣ F) : CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _
 _ v)
· 使用定理 `CategoryTheory.CommSq.right_adjoint_hasLift_iff`：right_adjoint_hasLift_i
ff : HasLift (sq.right_adjoint adj) ↔ HasLift sq
-/
theorem hasLiftingProperty_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) p ↔ HasLiftingProperty i (F.map p) := by
  constructor <;> intro <;> constructor <;> intro f g sq
  · rw [← sq.left_adjoint_hasLift_iff adj]
    infer_instance
  · rw [← sq.right_adjoint_hasLift_iff adj]
    infer_instance

end Adjunction

end CategoryTheory

