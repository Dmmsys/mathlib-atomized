/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves
/-!

# Description of the covering sieves of the regular topology

This file characterises the covering sieves of the regular topology.

## Main result

* `regularTopology.mem_sieves_iff_hasEffectiveEpi`: a sieve is a covering sieve for the
  regular topology if and only if it contains an effective epi.
-/

public section

namespace CategoryTheory.regularTopology

open Limits

variable {C : Type*} [Category* C] [Preregular C] {X : C}

/--
For a preregular category, any sieve that contains an `EffectiveEpi` is a covering sieve of the
regular topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpi`, but is needed for the proof.
-/
/-
**CategoryTheory.regularTopology.mem_sieves_of_hasEffectiveEpi** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：mem_sieves_of_hasEffectiveEpi (S : Sieve X) : (exists (Y : C) (π : Y ⟶ X),
 EffectiveEpi π ∧ S.arrows π) -> (S in (regularTopology C) X)
参数：S : Sieve X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用引理 `CategoryTheory.Presieve.le_of_factorsThru_sieve`：le_of_factorsThru_sieve
 {X : C} (S : Presieve X) (T : Sieve X) (h : S.FactorsThru T) : S <= T
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `CategoryTheory.Coverage.saturate_of_superset`：saturate_of_superset (K : 
Coverage C) {X : C} {S T : Sieve X} (h : S <= T) (hS : Saturate K X S) : Saturat
e K X T
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For a preregular category, any sieve that contains an `EffectiveEpi` is a coveri
ng sieve of the
regular topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpi`, but is needed f
or the proof.
-/
theorem mem_sieves_of_hasEffectiveEpi (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ S.arrows π) → (S ∈ (regularTopology C) X) := by
  rintro ⟨Y, π, h⟩
  have h_le : Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun _ ↦ π)) ≤ S := by
    rw [Sieve.generate_le_iff (Presieve.ofArrows _ _) S]
    apply Presieve.le_of_factorsThru_sieve (Presieve.ofArrows _ _) S _
    intro W g f
    refine ⟨W, 𝟙 W, ?_⟩
    cases f
    exact ⟨π, ⟨h.2, Category.id_comp π⟩⟩
  apply Coverage.saturate_of_superset (regularCoverage C) h_le
  exact Coverage.Saturate.of X _ ⟨Y, π, rfl, h.1⟩

/-- Effective epis in a preregular category are stable under composition. -/
/-
**CategoryTheory.regularTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.regu
larTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Effective epis in a preregular category are stable under composition.
-/
instance {Y Y' : C} (π : Y ⟶ X) [EffectiveEpi π]
    (π' : Y' ⟶ Y) [EffectiveEpi π'] : EffectiveEpi (π' ≫ π) := by
  rw [effectiveEpi_iff_effectiveEpiFamily, ← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows _ _)) ∈ (regularTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => regularTopology.isSheaf_yoneda_obj W _ h₂
  apply Coverage.Saturate.transitive X (Sieve.generate (Presieve.ofArrows (fun () ↦ Y)
      (fun () ↦ π)))
  · apply Coverage.Saturate.of
    use Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (regularTopology C).pullback_stable'
    apply regularTopology.mem_sieves_of_hasEffectiveEpi
    cases hY
    exact ⟨Y', π', inferInstance, Y', (𝟙 _), π' ≫ π, Presieve.ofArrows.mk (), (by simp)⟩

/-- A sieve is a cover for the regular topology if and only if it contains an `EffectiveEpi`. -/
/-
**CategoryTheory.regularTopology.mem_sieves_iff_hasEffectiveEpi** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：mem_sieves_iff_hasEffectiveEpi (S : Sieve X) : (S in (regularTopology C) X
) ↔ exists (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π)
参数：S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsSplitEpi.EffectiveEpi`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B) [CategoryTheory.IsSplitEpi 
f],   CategoryTheory.Effecti…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.regularTopology.instEffectiveEpiComp`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Preregular C] {X Y Y
' : C} (π : Y ⟶ X)   [CategoryTheory.Effe…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.regularTopology.mem_sieves_of_hasEffectiveEpi`：mem_sieves
_of_hasEffectiveEpi (S : Sieve X) : (exists (Y : C) (π : Y ⟶ X), EffectiveEpi π 
∧ S.arrows π) -> (S in (regularTopology C) X)

--- 原说明 ---
A sieve is a cover for the regular topology if and only if it contains an `Effec
tiveEpi`.
-/
theorem mem_sieves_iff_hasEffectiveEpi (S : Sieve X) :
    (S ∈ (regularTopology C) X) ↔
    ∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π) := by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      rcases hS with ⟨Y', π, h'⟩
      refine ⟨Y', π, h'.2, ?_⟩
      rcases h' with ⟨rfl, _⟩
      exact ⟨Y', 𝟙 Y', π, Presieve.ofArrows.mk (), (by simp)⟩
    | top Y => exact ⟨Y, (𝟙 Y), inferInstance, by simp only [Sieve.top_apply]⟩
    | transitive Y R S _ _ a b =>
      rcases a with ⟨Y₁, π, ⟨h₁, h₂⟩⟩
      choose Y' π' _ H using b h₂
      exact ⟨Y', π' ≫ π, inferInstance, (by simpa using H)⟩
  · exact regularTopology.mem_sieves_of_hasEffectiveEpi S

end CategoryTheory.regularTopology

