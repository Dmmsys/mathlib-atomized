/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Presentation of the tensor product of two modules

Given presentations of two `A`-modules `M₁` and `M₂`, we obtain a presentation of `M₁ ⊗[A] M₂`.

-/

@[expose] public section

universe w w₁₀ w₁₁ w₂₀ w₂₁ u v₁ v₂

namespace Module

open TensorProduct

variable {A : Type u} [CommRing A] {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂]

namespace Relations

variable (relations₁ : Relations.{w₁₀, w₁₁} A) (relations₂ : Relations.{w₂₀, w₂₁} A)

/-- The tensor product of systems of linear equations. -/
@[simps]
/-
**Module.Relations.tensor** 是 Mathlib 中的一个定义，位于命名空间 `Module.Relations`。
形式化陈述：tensor : Relations A where G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of systems of linear equations.
-/
noncomputable def tensor :
    Relations A where
  G := relations₁.G × relations₂.G
  R := Sum (relations₁.R × relations₂.G) (relations₁.G × relations₂.R)
  relation
    | .inl ⟨r₁, g₂⟩ => Finsupp.embDomain (Function.Embedding.sectL relations₁.G g₂)
        (relations₁.relation r₁)
    | .inr ⟨g₁, r₂⟩ => Finsupp.embDomain (Function.Embedding.sectR g₁ relations₂.G)
        (relations₂.relation r₂)

namespace Solution

variable {relations₁ relations₂} (solution₁ : relations₁.Solution M₁)
  (solution₂ : relations₂.Solution M₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given solutions in `M₁` and `M₂` to systems of linear equations, this is the obvious
solution to the tensor product of these systems in `M₁ ⊗[A] M₂`. -/
@[simps]
/-
**Module.Relations.Solution.tensor** 是 Mathlib 中的一个定义，位于命名空间 `Module.Relations.S
olution`。
形式化陈述：tensor : (relations₁.tensor relations₂).Solution (M₁ otimes[A] M₂) where v
ar
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given solutions in `M₁` and `M₂` to systems of linear equations, this is the obv
ious
solution to the tensor product of these systems in `M₁ ⊗[A] M₂`.
-/
noncomputable def tensor : (relations₁.tensor relations₂).Solution (M₁ ⊗[A] M₂) where
  var := fun ⟨g₁, g₂⟩ => solution₁.var g₁ ⊗ₜ solution₂.var g₂
  linearCombination_var_relation := by
    rintro (⟨r₁, g₂⟩ | ⟨g₁, r₂⟩)
    · dsimp
      rw [Finsupp.linearCombination_embDomain]
      exact (solution₁.postcomp (curry (TensorProduct.comm A M₂ M₁).toLinearMap
        (solution₂.var g₂))).linearCombination_var_relation r₁
    · dsimp
      rw [Finsupp.linearCombination_embDomain]
      exact (solution₂.postcomp (curry .id (solution₁.var g₁))).linearCombination_var_relation r₂

variable {solution₁ solution₂} (h₁ : solution₁.IsPresentation) (h₂ : solution₂.IsPresentation)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two modules admits a presentation by generators and relations. -/
/-
**Module.Relations.Solution.isPresentationCoreTensor** 是 Mathlib 中的一个定义，位于命名空间 `
Module.Relations.Solution`。
形式化陈述：isPresentationCoreTensor : Solution.IsPresentationCore.{w} (solution₁.tens
or solution₂) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two modules admits a presentation by generators and relati
ons.
-/
noncomputable def isPresentationCoreTensor :
    Solution.IsPresentationCore.{w} (solution₁.tensor solution₂) where
  desc s := uncurry _ _ _ _ (h₁.desc
    { var := fun g₁ ↦ h₂.desc
        { var := fun g₂ ↦ s.var ⟨g₁, g₂⟩
          linearCombination_var_relation := fun r₂ ↦ by
            erw [← Finsupp.linearCombination_embDomain A
              (Function.Embedding.sectR g₁ relations₂.G)]
            exact s.linearCombination_var_relation (.inr ⟨g₁, r₂⟩) }
      linearCombination_var_relation := fun r₁ ↦ h₂.postcomp_injective (by
        ext g₂
        dsimp
        erw [Finsupp.apply_linearCombination A (LinearMap.applyₗ (solution₂.var g₂))]
        have := s.linearCombination_var_relation (.inl ⟨r₁, g₂⟩)
        erw [Finsupp.linearCombination_embDomain] at this
        convert! this
        ext g₁
        simp) })
  postcomp_desc _ := by aesop
  postcomp_injective h := curry_injective (h₁.postcomp_injective (by
    ext g₁ : 2
    refine h₂.postcomp_injective ?_
    ext g₂
    exact congr_var h ⟨g₁, g₂⟩))

include h₁ h₂ in
/-
**Module.Relations.Solution.IsPresentation.tensor** 是 Mathlib 中的一个定理，位于命名空间 `Mod
ule.Relations.Solution.IsPresentation`。
形式化陈述：∀ {A : Type u} [inst : CommRing A] {M₁ : Type v₁} {M₂ : Type v₂} [inst_1 :
 AddCommGroup M₁] [inst_2 : AddCommGroup M₂]   [inst_3 : _root_.Module A M₁] [in
st_4 : _root_.Module A M₂] {relations₁ : Module.Relations A}   {relations₂ : Mod
ule.Relations A} {solution₁ : relations₁.Solution M₁} {solution₂ : relations₂.So
lution M₂},   solution₁.IsPresentation → solution₂.IsPresentation → (solution₁.t
ensor solution₂).IsPresentation
参数：solution₁.tensor solution₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Relations.Solution.IsPresentationCore.isPresentation`：isPresentat
ion {solution : relations.Solution M} (h : IsPresentationCore.{max u v w₀} solut
ion) : solution.IsPresentation where bijective
-/
lemma IsPresentation.tensor : (solution₁.tensor solution₂).IsPresentation :=
  (isPresentationCoreTensor h₁ h₂).isPresentation

end Solution

end Relations

namespace Presentation

variable (pres₁ : Presentation.{w₁₀, w₁₁} A M₁) (pres₂ : Presentation.{w₂₀, w₂₁} A M₂)

/-- The presentation of the `A`-module `M₁ ⊗[A] M₂` that is deduced from
a presentation of `M₁` and a presentation of `M₂`. -/
@[simps!]
/-
**Module.Presentation.tensor** 是 Mathlib 中的一个定义，位于命名空间 `Module.Presentation`。
形式化陈述：tensor : Presentation A (M₁ otimes[A] M₂) where G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presentation of the `A`-module `M₁ ⊗[A] M₂` that is deduced from
a presentation of `M₁` and a presentation of `M₂`.
-/
noncomputable def tensor : Presentation A (M₁ ⊗[A] M₂) where
  G := _
  R := _
  relation := _
  toSolution := pres₁.toSolution.tensor pres₂.toSolution
  toIsPresentation := pres₁.toIsPresentation.tensor pres₂.toIsPresentation

end Presentation

end Module

