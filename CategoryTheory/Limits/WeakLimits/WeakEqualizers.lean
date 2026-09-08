/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Weak equalizers

These are weak limits for diagrams of shape `WalkingParallelPair`.

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {X Y : C} (f g : X ⟶ Y)

/-- Two parallel morphisms `f` and `g` have a weak equalizer if the diagram `parallelPair f g`
has a weak limit. -/
/-
**CategoryTheory.Limits.HasWeakEqualizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasWeakEqualizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two parallel morphisms `f` and `g` have a weak equalizer if the diagram `paralle
lPair f g`
has a weak limit.
-/
abbrev HasWeakEqualizer :=
  HasWeakLimit (parallelPair f g)

variable [HasWeakEqualizer f g]

/-- If a weak equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `weakEqualizer f g`. -/
/-
**CategoryTheory.Limits.weakEqualizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：weakEqualizer : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a weak equalizer of `f` and `g` exists, we can access an arbitrary choice of 
such by
saying `weakEqualizer f g`.
-/
noncomputable abbrev weakEqualizer : C :=
  weakLimit (parallelPair f g)

/-- If a weak equalizer of `f` and `g` exists, we can access the morphism
`weakEqualizer f g ⟶ X` by saying `weakEqualizer.ι f g`. -/
/-
**CategoryTheory.Limits.weakEqualizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a weak equalizer of `f` and `g` exists, we can access the morphism
`weakEqualizer f g ⟶ X` by saying `weakEqualizer.ι f g`.
-/
noncomputable abbrev weakEqualizer.ι : weakEqualizer f g ⟶ X :=
  weakLimit.π (parallelPair f g) WalkingParallelPair.zero

/-- A weak equalizer cone for a parallel pair `f` and `g` -/
/-
**CategoryTheory.Limits.weakEqualizer.fork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.weakEqualizer`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} → (f g : X ⟶ Y) → [CategoryTheory.Limits.HasWeakEqualizer f g] → Category
Theory.Limits.Fork f g
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak equalizer cone for a parallel pair `f` and `g`
-/
noncomputable abbrev weakEqualizer.fork : Fork f g :=
  weakLimit.cone (parallelPair f g)

@[simp]
/-
**CategoryTheory.Limits.weakEqualizer.fork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakEqualizer.fork_ι : (weakEqualizer.fork f g).ι = weakEqualizer.ι f g :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.weakEqualizer.fork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakEqualizer.fork_π_app_zero :
    (weakEqualizer.fork f g).π.app WalkingParallelPair.zero = weakEqualizer.ι f g :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.weakEqualizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.weakEqualizer`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (
f g : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasWeakEqualizer f g],   Category
Theory.CategoryStruct.comp (CategoryTheory.Limits.weakEqualizer.ι f g) f =     C
ategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.weakEqualizer.ι f g) g
参数：f g : X ⟶ Y；CategoryTheory.Limits.weakEqualizer.ι f g；CategoryTheory.Limits.w
eakEqualizer.ι f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…
-/
theorem weakEqualizer.condition : weakEqualizer.ι f g ≫ f = weakEqualizer.ι f g ≫ g :=
  Fork.condition <| weakLimit.cone <| parallelPair f g

set_option backward.defeqAttrib.useBackward true in
/-- The weak equalizer built from `weakEqualizer.ι f g` is weakly limiting. -/
/-
**CategoryTheory.Limits.weakEqualizerIsWeakEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：weakEqualizerIsWeakEqualizer : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
 (weakEqualizer.condition f g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.weakEqualizer.condition`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f g : X ⟶ Y)   [inst_1 : Catego
ryTheory.Limits.HasWeakEqualizer f …

--- 原说明 ---
The weak equalizer built from `weakEqualizer.ι f g` is weakly limiting.
-/
def weakEqualizerIsWeakEqualizer : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
    (weakEqualizer.condition f g)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the weak equalizer of
`f` and `g` via `weakEqualizer.lift : W ⟶ weakEqualizer f g`. -/
/-
**CategoryTheory.Limits.weakEqualizer.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.weakEqualizer`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       {f g : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasWeakEq
ualizer f g] →           {W : C} →             (k : W ⟶ X) →               Categ
oryTheory.CategoryStruct.comp k f = CategoryTheory.CategoryStruct.comp k g →    
             (W ⟶ CategoryTheory.Limits.weakEqualizer f g)
参数：k : W ⟶ X；W ⟶ CategoryTheory.Limits.weakEqualizer f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the weak equal
izer of
`f` and `g` via `weakEqualizer.lift : W ⟶ weakEqualizer f g`.
-/
noncomputable abbrev weakEqualizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ weakEqualizer f g :=
  weakLimit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]
/-
**CategoryTheory.Limits.weakEqualizer.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakEqualizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    weakEqualizer.lift k h ≫ weakEqualizer.ι f g = k :=
  weakLimit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakEqualizer f g` satisfying `l ≫ weakEqualizer.ι f g = k`. -/
/-
**CategoryTheory.Limits.weakEqualizer.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.weakEqualizer`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       {f g : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasWeakEq
ualizer f g] →           {W : C} →             (k : W ⟶ X) →               Categ
oryTheory.CategoryStruct.comp k f = CategoryTheory.CategoryStruct.comp k g →    
             { l // CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.
weakEqualizer.ι f g) = k }
参数：k : W ⟶ X；CategoryTheory.Limits.weakEqualizer.ι f g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.weakEqualizer.lift_ι`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] {X Y : C} {f g : X ⟶ Y}   [inst_1 : CategoryT
heory.Limits.HasWeakEqualizer f …

--- 原说明 ---
A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakEqualizer f g` satisfying `l ≫ weakEqualizer.ι f g = k`.
-/
def weakEqualizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ weakEqualizer f g // l ≫ weakEqualizer.ι f g = k } :=
  ⟨weakEqualizer.lift k h, weakEqualizer.lift_ι _ _⟩

variable (C)

/-- A category `HasWeakEqualizers` if it has all weak limits of shape `WalkingParallelPair`,
i.e. if it has a weak equalizer for every parallel pair of morphisms. -/
/-
**CategoryTheory.Limits.HasWeakEqualizers** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：HasWeakEqualizers
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasWeakEqualizers` if it has all weak limits of shape `WalkingParall
elPair`,
i.e. if it has a weak equalizer for every parallel pair of morphisms.
-/
abbrev HasWeakEqualizers :=
  HasWeakLimitsOfShape WalkingParallelPair C

/-- A category with equalizers has weak equalizers. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with equalizers has weak equalizers.
-/
instance (priority := 100) HasWeakEqualizersOfHasEqualizers [HasEqualizers C] :
    HasWeakEqualizers C where

/-- If `C` has all weak limits of diagrams `parallelPair f g`, then it has all weak equalizers -/
/-
**CategoryTheory.Limits.hasWeakEqualizers_of_hasWeakLimit_parallelPair** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasWeakEqualizers_of_hasWeakLimit_parallelPair [forall {X Y : C} {f g : X 
⟶ Y}, HasWeakLimit (parallelPair f g)] : HasWeakEqualizers C where hasWeakLimit 
F
参数：parallelPair f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasWeakLimit_of_iso`：hasWeakLimit_of_iso {F G : J 
⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G

--- 原说明 ---
If `C` has all weak limits of diagrams `parallelPair f g`, then it has all weak 
equalizers
-/
theorem hasWeakEqualizers_of_hasWeakLimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasWeakLimit (parallelPair f g)] : HasWeakEqualizers C where
      hasWeakLimit F := hasWeakLimit_of_iso (diagramIsoParallelPair F).symm

variable {C}

/-- This is a slightly more convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[simps]
/-
**CategoryTheory.Limits.Fork.IsWeakLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Fork.IsWeakLimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       {f g : X ⟶ Y} →         (t : CategoryTheory.Limits.Fork f g) →   
        (lift : (s : CategoryTheory.Limits.Fork f g) → s.pt ⟶ t.pt) →           
  (∀ (s : CategoryTheory.Limits.Fork f g), CategoryTheory.CategoryStruct.comp (l
ift s) t.ι = s.ι) →               CategoryTheory.Limits.IsWeakLimit t
参数：t : CategoryTheory.Limits.Fork f g；lift : (s : CategoryTheory.Limits.Fork f g
) → s.pt ⟶ t.pt；∀ (s : CategoryTheory.Limits.Fork f g), CategoryTheory.CategoryS
truct.comp (lift s) t.ι = s.ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a fork is a weak limit 
cone. It
only asks for a proof of facts that carry any mathematical content
-/
def Fork.IsWeakLimit.mk (t : Fork f g) (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s) : IsWeakLimit t :=
  { lift
    fac s j :=
      WalkingParallelPair.casesOn j (fac s) <| by
        simp [← Category.assoc, fac] }

/-- This is another convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
/-
**CategoryTheory.Limits.Fork.IsWeakLimit.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Fork.IsWeakLimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       {f g : X ⟶ Y} →         (t : CategoryTheory.Limits.Fork f g) →   
        ((s : CategoryTheory.Limits.Fork f g) → { l // CategoryTheory.CategorySt
ruct.comp l t.ι = s.ι }) →             CategoryTheory.Limits.IsWeakLimit t
参数：t : CategoryTheory.Limits.Fork f g；(s : CategoryTheory.Limits.Fork f g) → { l
 // CategoryTheory.CategoryStruct.comp l t.ι = s.ι }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows a
ccess to the
same `s` for all parts.
-/
def Fork.IsWeakLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : ∀ s : Fork f g, { l // l ≫ t.ι = s.ι}) :
    IsWeakLimit t :=
  Fork.IsWeakLimit.mk t (fun s => (create s).1) (fun s => (create s).2)

end CategoryTheory.Limits

