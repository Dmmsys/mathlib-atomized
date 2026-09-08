/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/

public section


universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/--
If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
/-
**CategoryTheory.has_weakly_initial_of_weakly_initial_set_and_hasProducts** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：has_weakly_initial_of_weakly_initial_set_and_hasProducts [HasProducts.{v} 
C] {ι : Type v} {B : ι -> C} (hB : forall A : C, exists i, Nonempty (B i ⟶ A)) :
 exists T : C, forall X, Nonempty (T ⟶ X)
参数：hB : forall A : C, exists i, Nonempty (B i ⟶ A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
If `C` has (small) products and a small weakly initial set of objects, then it h
as a weakly initial
object.
-/
theorem has_weakly_initial_of_weakly_initial_set_and_hasProducts [HasProducts.{v} C] {ι : Type v}
    {B : ι → C} (hB : ∀ A : C, ∃ i, Nonempty (B i ⟶ A)) : ∃ T : C, ∀ X, Nonempty (T ⟶ X) :=
  ⟨∏ᶜ B, fun X => ⟨Pi.π _ _ ≫ (hB X).choose_spec.some⟩⟩

/-- If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
/-
**CategoryTheory.hasInitial_of_weakly_initial_and_hasWideEqualizers** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hasInitial_of_weakly_initial_and_hasWideEqualizers [HasWideEqualizers.{v} 
C] {T : C} (hT : forall X, Nonempty (T ⟶ X)) : HasInitial C
参数：hT : forall X, Nonempty (T ⟶ X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasEqualizers_of_hasWideEqualizers`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasWideEqualiz
ers C],   CategoryTheory.Limits.HasEqualizers …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.wideEqualizer.condition`：∀ {J : Type w} {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : J → (X ⟶ Y))   [inst
_1 : CategoryTheory.Limits.HasWideE…
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `CategoryTheory.cancel_mono_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {h : Y ⟶ Y},   Cat
egoryTheory.Categor…
· 使用定理 `CategoryTheory.Limits.wideEqualizer.ι_mono`：∀ {J : Type w} {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   [inst_1 
: CategoryTheory.Limits.HasWideE…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `CategoryTheory.Limits.hasInitial_of_unique`：hasInitial_of_unique (X : C)
 [forall Y, Nonempty (X ⟶ Y)] [forall Y, Subsingleton (X ⟶ Y)] : HasInitial C wh
ere has_colimit F
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
If `C` has (small) wide equalizers and a weakly initial object, then it has an i
nitial object.

The initial object is constructed as the wide equalizer of all endomorphisms on 
the given weakly
initial object.
-/
theorem hasInitial_of_weakly_initial_and_hasWideEqualizers [HasWideEqualizers.{v} C] {T : C}
    (hT : ∀ X, Nonempty (T ⟶ X)) : HasInitial C := by
  let endos := T ⟶ T
  let i := wideEqualizer.ι (id : endos → endos)
  have : Nonempty endos := ⟨𝟙 _⟩
  have : ∀ X : C, Unique (wideEqualizer (id : endos → endos) ⟶ X) := by
    intro X
    refine ⟨⟨i ≫ Classical.choice (hT X)⟩, fun a => ?_⟩
    let E := equalizer a (i ≫ Classical.choice (hT _))
    let e : E ⟶ wideEqualizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _ := by
      rw [Category.assoc, Category.assoc]
      apply wideEqualizer.condition (id : endos → endos) (h ≫ e ≫ i)
    rw [Category.comp_id, cancel_mono_id i] at this
    have : IsSplitEpi e := IsSplitEpi.mk' ⟨i ≫ h, this⟩
    rw [← cancel_epi e]
    apply equalizer.condition
  exact hasInitial_of_unique (wideEqualizer (id : endos → endos))

end CategoryTheory

