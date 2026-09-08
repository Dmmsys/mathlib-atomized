/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of morphisms that are bounded by a cardinal

Given `P : MorphismProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `P.toSet` is `< κ`.

-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- The property that the subtype of arrows satisfying a property `P : MorphismProperty C`
is of cardinality `< κ`. -/
/-
**CategoryTheory.MorphismProperty.HasCardinalLT** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Cardinal.{w} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that the subtype of arrows satisfying a property `P : MorphismPrope
rty C`
is of cardinality `< κ`.
-/
protected abbrev HasCardinalLT (P : MorphismProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT P.toSet κ
/-
**CategoryTheory.MorphismProperty.hasCardinalLT_ofHoms** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：hasCardinalLT_ofHoms {C : Type*} [Category* C] {ι : Type*} {X Y : ι -> C} 
(f : forall i, X i ⟶ Y i) {κ : Cardinal} (h : HasCardinalLT ι κ) : (MorphismProp
erty.ofHoms f).HasCardinalLT κ
参数：f : forall i, X i ⟶ Y i；h : HasCardinalLT ι κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_surjective`：of_surjective (f : X -> Y) (hf : Function.S
urjective f) : HasCardinalLT Y κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
· 使用引理 `CategoryTheory.MorphismProperty.mem_toSet_iff`：mem_toSet_iff (f : Arrow 
C) : f in P.toSet ↔ P f.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hasCardinalLT_ofHoms {C : Type*} [Category* C]
    {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) {κ : Cardinal}
    (h : HasCardinalLT ι κ) : (MorphismProperty.ofHoms f).HasCardinalLT κ :=
  h.of_surjective (fun i ↦ ⟨Arrow.mk (f i), ⟨i⟩⟩) (by
    rintro ⟨f, hf⟩
    rw [MorphismProperty.mem_toSet_iff, MorphismProperty.ofHoms_iff] at hf
    obtain ⟨i, hf⟩ := hf
    obtain rfl : f = _ := hf
    exact ⟨i, rfl⟩)
/-
**CategoryTheory.MorphismProperty.HasCardinalLT.iSup** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty.HasCardinalLT`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {P
 : ι → CategoryTheory.MorphismProperty C}   {κ : Cardinal.{w}} [Fact κ.IsRegular
],   (∀ (i : ι), (P i).HasCardinalLT κ) → HasCardinalLT ι κ → (⨆ i, P i).HasCard
inalLT κ
参数：∀ (i : ι), (P i).HasCardinalLT κ；⨆ i, P i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.toSet_iSup`：toSet_iSup {ι : Type*} (W : 
ι -> MorphismProperty C) : (⨆ i, W i).toSet = ⋃ i, (W i).toSet
· 使用引理 `hasCardinalLT_iUnion`：hasCardinalLT_iUnion {ι : Type*} {X : Type*} (S : 
ι -> Set X) {κ : Cardinal} [Fact κ.IsRegular] (hι : HasCardinalLT ι κ) (hS : for
all i, Has…
-/
lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι → MorphismProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : ∀ i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [toSet_iSup]
  exact hasCardinalLT_iUnion _ hι hP
/-
**CategoryTheory.MorphismProperty.HasCardinalLT.sup** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.HasCardinalLT`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P₁ P₂ : Category
Theory.MorphismProperty C} {κ : Cardinal.{w}},   P₁.HasCardinalLT κ → P₂.HasCard
inalLT κ → Cardinal.aleph0 ≤ κ → (P₁ ⊔ P₂).HasCardinalLT κ
参数：P₁ ⊔ P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.toSet_max`：toSet_max (W₁ W₂ : MorphismPr
operty C) : (W₁ ⊔ W₂).toSet = W₁.toSet union W₂.toSet
· 使用引理 `hasCardinalLT_union`：hasCardinalLT_union {X : Type*} {S₁ S₂ : Set X} {κ 
: Cardinal} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardi
nalLT S₂ …
-/
lemma HasCardinalLT.sup
    {P₁ P₂ : MorphismProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [MorphismProperty.toSet_max]
  exact hasCardinalLT_union hκ h₁ h₂

end MorphismProperty

end CategoryTheory

