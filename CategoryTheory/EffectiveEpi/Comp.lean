/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Composition of effective epimorphisms

This file provides `EffectiveEpi` instances for certain compositions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable {C : Type*} [Category* C]

/--
An effective epi family precomposed by a family of split epis is effective epimorphic.
This version takes an explicit section to the split epis, and is mainly used to define
`effectiveEpiStructCompOfEffectiveEpiSplitEpi`,
which takes a `IsSplitEpi` instance instead.
-/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi'** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' {α : Type*} {B : C} {X
 Y : α -> C} (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) (i : (a : α) ->
 X a ⟶ Y a) (hi : forall a, i a ≫ g a = 𝟙 _) [EffectiveEpiFamily _ f] : Effectiv
eEpiFamilyStruct _ (fun a => g a ≫ f a) where desc e w
参数：f : (a : α) -> X a ⟶ B；g : (a : α) -> Y a ⟶ X a；i : (a : α) -> X a ⟶ Y a；hi :
 forall a, i a ≫ g a = 𝟙 _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) (i : (a : α) → X a ⟶ Y a)
    (hi : ∀ a, i a ≫ g a = 𝟙 _) [EffectiveEpiFamily _ f] :
    EffectiveEpiFamilyStruct _ (fun a ↦ g a ≫ f a) where
  desc e w := EffectiveEpiFamily.desc _ f (fun a ↦ i a ≫ e a) fun a₁ a₂ g₁ g₂ _ ↦ (by
    simp only [← Category.assoc]
    apply w _ _ (g₁ ≫ i a₁) (g₂ ≫ i a₂)
    simp only [Category.assoc]
    simp only [← Category.assoc, hi]
    simpa)
  fac e w a := by
    simp only [Category.assoc, EffectiveEpiFamily.fac]
    rw [← Category.id_comp (e a), ← Category.assoc, ← Category.assoc]
    apply w
    simp only [Category.comp_id, Category.id_comp, ← Category.assoc]
    aesop
  uniq _ _ _ hm := by
    apply EffectiveEpiFamily.uniq _ f
    intro a
    rw [← hm a, ← Category.assoc, ← Category.assoc, hi, Category.id_comp]

/--
An effective epi family precomposed with a family of split epis is effective epimorphic.
-/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi {α : Type*} {B : C} {X 
Y : α -> C} (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) [forall a, IsSpl
itEpi (g a)] [EffectiveEpiFamily _ f] : EffectiveEpiFamilyStruct _ (fun a => g a
 ≫ f a)
参数：f : (a : α) -> X a ⟶ B；g : (a : α) -> Y a ⟶ X a；g a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ f] : EffectiveEpiFamilyStruct _ (fun a ↦ g a ≫ f a) :=
  effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' f g
    (fun a ↦ section_ (g a))
    (fun a ↦ IsSplitEpi.id (g a))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ f] : EffectiveEpiFamily _ (fun a ↦ g a ≫ f a) :=
  ⟨⟨effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi f g⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g] [EffectiveEpi f] :
    EffectiveEpi (g ≫ f) := inferInstance
/-
**CategoryTheory.IsSplitEpi.EffectiveEpi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsSplitEpi`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {B X : C} (
f : X ⟶ B) [CategoryTheory.IsSplitEpi f],   CategoryTheory.EffectiveEpi f
参数：f : X ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.instEffectiveEpiOfEffectiveEpiFamily`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B)   [CategoryThe
ory.EffectiveEpiFamily (fun x => X) fun x…
· 使用定理 `CategoryTheory.instEffectiveEpiFamilyCompOfIsSplitEpi`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] {α : Type u_2} {B : C} {X Y : α → 
C}   (f : (a : α) → X a ⟶ B) (g : (a : α) →…
· 使用定理 `CategoryTheory.instEffectiveEpiFamily`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B) [CategoryTheory.EffectiveEpi
 f],   CategoryTheory.Effec…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
instance IsSplitEpi.EffectiveEpi {B X : C} (f : X ⟶ B) [IsSplitEpi f] : EffectiveEpi f := by
  rw [← Category.comp_id f]
  infer_instance

/--
If a family of morphisms with fixed target, precomposed by a family of epis is
effective epimorphic, then the original family is as well.
-/
/-
**CategoryTheory.effectiveEpiFamilyStructOfComp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：effectiveEpiFamilyStructOfComp {C : Type*} [Category* C] {I : Type*} {Z Y 
: I -> C} {X : C} (g : forall i, Z i ⟶ Y i) (f : forall i, Y i ⟶ X) [EffectiveEp
iFamily _ (fun i => g i ≫ f i)] [forall i, Epi (g i)] : EffectiveEpiFamilyStruct
 _ f where desc {W} φ h
参数：g : forall i, Z i ⟶ Y i；f : forall i, Y i ⟶ X；fun i => g i ≫ f i；g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a family of morphisms with fixed target, precomposed by a family of epis is
effective epimorphic, then the original family is as well.
-/
noncomputable def effectiveEpiFamilyStructOfComp {C : Type*} [Category* C]
    {I : Type*} {Z Y : I → C} {X : C} (g : ∀ i, Z i ⟶ Y i) (f : ∀ i, Y i ⟶ X)
    [EffectiveEpiFamily _ (fun i => g i ≫ f i)] [∀ i, Epi (g i)] :
    EffectiveEpiFamilyStruct _ f where
  desc {W} φ h := EffectiveEpiFamily.desc _ (fun i => g i ≫ f i)
    (fun i => g i ≫ φ i) (fun {T} i₁ i₂ g₁ g₂ eq =>
      by simpa [assoc] using h i₁ i₂ (g₁ ≫ g i₁) (g₂ ≫ g i₂) (by simpa [assoc] using eq))
  fac {W} φ h i := by
    rw [← cancel_epi (g i), ← assoc, EffectiveEpiFamily.fac _ (fun i => g i ≫ f i)]
  uniq {W} φ _ m hm := EffectiveEpiFamily.uniq _ (fun i => g i ≫ f i) _ _ _
    (fun i => by rw [assoc, hm])
/-
**CategoryTheory.effectiveEpiFamily_of_effectiveEpi_epi_comp** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamily_of_effectiveEpi_epi_comp {α : Type*} {B : C} {X Y : α -
> C} (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) [forall a, Epi (g a)] [
EffectiveEpiFamily _ (fun a => g a ≫ f a)] : EffectiveEpiFamily _ f
参数：f : (a : α) -> X a ⟶ B；g : (a : α) -> Y a ⟶ X a；g a；fun a => g a ≫ f a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma effectiveEpiFamily_of_effectiveEpi_epi_comp {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, Epi (g a)]
    [EffectiveEpiFamily _ (fun a ↦ g a ≫ f a)] : EffectiveEpiFamily _ f :=
  ⟨⟨effectiveEpiFamilyStructOfComp g f⟩⟩
/-
**CategoryTheory.effectiveEpi_of_effectiveEpi_epi_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
形式化陈述：effectiveEpi_of_effectiveEpi_epi_comp {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) 
[Epi g] [EffectiveEpi (g ≫ f)] : EffectiveEpi f
参数：f : X ⟶ B；g : Y ⟶ X；g ≫ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.effectiveEpi_iff_effectiveEpiFamily`：effectiveEpi_iff_eff
ectiveEpiFamily {B X : C} (f : X ⟶ B) : EffectiveEpi f ↔ EffectiveEpiFamily (fun
 () => X) (fun () => f)
· 使用引理 `CategoryTheory.effectiveEpiFamily_of_effectiveEpi_epi_comp`：effectiveEpi
Family_of_effectiveEpi_epi_comp {α : Type*} {B : C} {X Y : α -> C} (f : (a : α) 
-> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) [forall a…
· 使用定理 `CategoryTheory.instEffectiveEpiOfEffectiveEpiFamily`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B)   [CategoryThe
ory.EffectiveEpiFamily (fun x => X) fun x…
-/
lemma effectiveEpi_of_effectiveEpi_epi_comp {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X)
    [Epi g] [EffectiveEpi (g ≫ f)] : EffectiveEpi f :=
  have := (effectiveEpi_iff_effectiveEpiFamily (g ≫ f)).mp inferInstance
  have := effectiveEpiFamily_of_effectiveEpi_epi_comp
    (X := fun () ↦ X) (Y := fun () ↦ Y) (fun () ↦ f) (fun () ↦ g)
  inferInstance

section CompIso

variable {B B' : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
  (i : B ⟶ B')

/-
**CategoryTheory.effectiveEpiFamilyStructCompIso_aux** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructCompIso_aux {W : C} (e : (a : α) -> X a ⟶ W) (h : 
forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π a₁ ≫ i = g₂ ≫
 π a₂ ≫ i -> g₁ ≫ e a₁ = g₂ ≫ e a₂) {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z 
⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) : g₁ ≫ e a₁ = g₂ ≫ e a₂
参数：e : (a : α) -> X a ⟶ W；h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z
 ⟶ X a₂), g₁ ≫ π a₁ ≫ i = g₂ ≫ π a₂ ≫ i -> g₁ ≫ e a₁ = g₂ ≫ e a₂；a₁ a₂ : α；g₁ : 
Z ⟶ X a₁；g₂ : Z ⟶ X a₂；hg : g₁ ≫ π a₁ = g₂ ≫ π a₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem effectiveEpiFamilyStructCompIso_aux
    {W : C} (e : (a : α) → X a ⟶ W)
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ ≫ i = g₂ ≫ π a₂ ≫ i → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  grind

variable [EffectiveEpiFamily X π] [IsIso i]

/-- An effective epi family followed by an iso is an effective epi family. -/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructCompIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：effectiveEpiFamilyStructCompIso : EffectiveEpiFamilyStruct X (fun a => π a
 ≫ i) where desc e h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructCompIso : EffectiveEpiFamilyStruct X (fun a ↦ π a ≫ i) where
  desc e h := inv i ≫ EffectiveEpiFamily.desc X π e (effectiveEpiFamilyStructCompIso_aux X π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π e
      (effectiveEpiFamilyStructCompIso_aux X π i e h) (i ≫ m) hm]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EffectiveEpiFamily X (fun a ↦ π a ≫ i) := ⟨⟨effectiveEpiFamilyStructCompIso X π i⟩⟩

end CompIso

section IsoComp

variable {B : C} {α : Type*} (X Y : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
  (i : (a : α) → Y a ⟶ X a) [∀ a, IsIso (i a)]

/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : EffectiveEpiFamily Y (fun a ↦ i a ≫ π a) :=
  inferInstance

end IsoComp

end CategoryTheory

