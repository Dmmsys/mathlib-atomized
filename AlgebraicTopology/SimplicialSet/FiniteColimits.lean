/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite colimits of finite simplicial sets are finite

-/

public section

universe u v

open CategoryTheory Limits

namespace SSet

variable {J : Type*} [Category J] [HasColimitsOfShape J (Type u)]
  {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)

section

include hc

/-
**SSet.iSup_range_eq_top_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：iSup_range_eq_top_of_isColimit : ⨆ (j : J), Subcomplex.range (c.ι.app j) =
 ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma iSup_range_eq_top_of_isColimit :
    ⨆ (j : J), Subcomplex.range (c.ι.app j) = ⊤ := by
  ext n x
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range,
    Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.range_eq_iSup_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：range_eq_iSup_of_isColimit {X : SSet.{u}} (φ : c.pt ⟶ X) : Subcomplex.rang
e φ = ⨆ (j : J), Subcomplex.range (c.ι.app j ≫ φ)
参数：φ : c.pt ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SSet.Subcomplex.range_comp`：range_comp {Z : SSet.{u}} (g : Y ⟶ Z) : Subc
omplex.range (f ≫ g) = (Subcomplex.range f).image g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.Subcomplex.range_eq_top`：range_eq_top [Epi f] : Subcomplex.range f 
= ⊤
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用引理 `SSet.iSup_range_eq_top_of_isColimit`：iSup_range_eq_top_of_isColimit : ⨆ 
(j : J), Subcomplex.range (c.ι.app j) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `SSet.Subcomplex.image_iSup`：image_iSup {ι : Type*} (S : ι -> X.Subcomple
x) (f : X ⟶ Y) : image (⨆ i, S i) f = ⨆ i, (S i).image f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_eq_iSup_of_isColimit {X : SSet.{u}} (φ : c.pt ⟶ X) :
    Subcomplex.range φ = ⨆ (j : J), Subcomplex.range (c.ι.app j ≫ φ) := by
  conv_lhs => rw [← Category.id_comp φ]
  simp_rw [Subcomplex.range_comp, Subcomplex.range_eq_top, ← iSup_range_eq_top_of_isColimit hc,
    Subcomplex.image_iSup]

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.hasDimensionLT_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_of_isColimit {n : Nat} (h : forall (j : J), HasDimensionLT 
(F.obj j) n) : HasDimensionLT c.pt n
参数：h : forall (j : J), HasDimensionLT (F.obj j) n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.hasDimensionLT_subcomplex_top_iff`：hasDimensionLT_subcomplex_top_if
f (X : SSet.{u}) (d : Nat) : HasDimensionLT (⊤ : X.Subcomplex) d ↔ X.HasDimensio
nLT d
· 使用引理 `SSet.iSup_range_eq_top_of_isColimit`：iSup_range_eq_top_of_isColimit : ⨆ 
(j : J), Subcomplex.range (c.ι.app j) = ⊤
· 使用引理 `SSet.hasDimensionLT_iSup_iff`：hasDimensionLT_iSup_iff {X : SSet.{u}} {ι 
: Type*} (A : ι -> X.Subcomplex) (d : Nat) : HasDimensionLT (⨆ i, A i :) d ↔ for
all i, HasDimensio…
· 使用定理 `SSet.instHasDimensionLTToSSetRange`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) (d
 : ℕ) [X.HasDimensionLT d], (SSet.Subcomplex.range f).toSSet.HasDimensionLT d
-/
lemma hasDimensionLT_of_isColimit {n : ℕ}
    (h : ∀ (j : J), HasDimensionLT (F.obj j) n) : HasDimensionLT c.pt n := by
  rw [← hasDimensionLT_subcomplex_top_iff, ← iSup_range_eq_top_of_isColimit hc,
    hasDimensionLT_iSup_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.finite_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_of_isColimit [Finite J] (h : forall (j : J), (F.obj j).Finite) : c.
pt.Finite
参数：h : forall (j : J), (F.obj j).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.finite_subcomplex_top_iff`：finite_subcomplex_top_iff : SSet.Finite 
(⊤ : X.Subcomplex) ↔ X.Finite
· 使用引理 `SSet.iSup_range_eq_top_of_isColimit`：iSup_range_eq_top_of_isColimit : ⨆ 
(j : J), Subcomplex.range (c.ι.app j) = ⊤
· 使用引理 `SSet.finite_iSup_iff`：finite_iSup_iff {X : SSet.{u}} {ι : Type*} [Finite
 ι] (A : ι -> X.Subcomplex) : SSet.Finite (⨆ i, A i :) ↔ forall i, SSet.Finite (
A i)
-/
lemma finite_of_isColimit [Finite J] (h : ∀ (j : J), (F.obj j).Finite) :
    c.pt.Finite := by
  rw [← finite_subcomplex_top_iff, ← iSup_range_eq_top_of_isColimit hc, finite_iSup_iff]
  infer_instance

end

/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊥_ SSet.{u}).Finite := by
  apply finite_of_isColimit (initialIsInitial (C := SSet.{u}))
  rintro ⟨⟨⟩⟩
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : SSet.{u}) [X.Finite] [Y.Finite] :
    (X ⨿ Y).Finite := by
  apply finite_of_isColimit (coprodIsCoprod X Y)
  rintro ⟨_ | _⟩ <;> dsimp <;> infer_instance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type v} [Finite ι] (X : ι → SSet.{u}) [HasCoproduct X]
    [∀ j, (X j).Finite] :
    (∐ X).Finite := by
  have : HasColimitsOfShape (Discrete ι) (Type u) := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
  exact finite_of_isColimit (coproductIsCoproduct X) (fun ⟨j⟩ ↦ by dsimp; infer_instance)

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.range_eq_iSup_sigma_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_eq_iSup_sigma_ι
    {ι : Type v} [HasColimitsOfShape (Discrete ι) (Type u)]
    {X : ι → SSet.{u}} {Y : SSet.{u}} [HasCoproduct X]
    (f : ∐ X ⟶ Y) :
    Subcomplex.range f = ⨆ (i : ι), Subcomplex.range (Sigma.ι X i ≫ f) := by
  rw [range_eq_iSup_of_isColimit (coproductIsCoproduct X) f]
  refine le_antisymm ?_ ?_
  · simp only [iSup_le_iff, Discrete.forall]
    intro i
    exact le_trans (by rfl) (le_iSup _ i)
  · simp only [iSup_le_iff]
    intro i
    exact le_trans (by rfl) (le_iSup _ ⟨i⟩)

end SSet

