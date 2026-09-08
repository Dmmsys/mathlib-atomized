/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Data.Finite.Prod

/-!
# The Serre class of finite abelian groups

In this file, we define `isFinite : ObjectProperty AddCommGrpCat` and show
that it is a Serre class.

-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AddCommGrpCat

/-- The Serre class of finite abelian groups
in the category of abelian groups. -/
/-
**AddCommGrpCat.isFinite** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：isFinite : ObjectProperty AddCommGrpCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Serre class of finite abelian groups
in the category of abelian groups.
-/
def isFinite : ObjectProperty AddCommGrpCat.{u} :=
  fun M ↦ Finite M

@[simp]
/-
**AddCommGrpCat.prop_isFinite_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpCat`。
形式化陈述：prop_isFinite_iff (M : AddCommGrpCat.{u}) : isFinite M ↔ Finite M
参数：M : AddCommGrpCat.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prop_isFinite_iff (M : AddCommGrpCat.{u}) : isFinite M ↔ Finite M := Iff.rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : isFinite.{u}.IsSerreClass where
  exists_zero := ⟨.of PUnit, isZero_of_subsingleton _,
    by rw [prop_isFinite_iff]; infer_instance⟩
  prop_of_mono {M N} f hf hN := by
    rw [AddCommGrpCat.mono_iff_injective] at hf
    simp only [prop_isFinite_iff] at hN ⊢
    exact Finite.of_injective _ hf
  prop_of_epi {M N} f hf hM := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    simp only [prop_isFinite_iff] at hM ⊢
    exact Finite.of_surjective _ hf
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    simp only [prop_isFinite_iff] at h₁ h₃ ⊢
    have hg := hS.epi_g
    rw [AddCommGrpCat.epi_iff_surjective] at hg
    obtain ⟨s, hs⟩ := hg.hasRightInverse
    have hφ : Function.Surjective (fun (x₁, x₃) ↦ S.f x₁ + s x₃) := fun x₂ ↦ by
      obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact (x₂ - s (S.g x₂))
        (by simp [hs (S.g x₂)])
      exact ⟨⟨x₁, S.g x₂⟩, by simp [hx₁]⟩
    exact Finite.of_surjective _ hφ

end AddCommGrpCat

