/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A lemma about `ApproximatesLinearOn` that needs `FiniteDimensional`

In this file we prove that in a real vector space,
a function `f` that approximates a linear equivalence on a subset `s`
can be extended to a homeomorphism of the whole space.

This used to be the only lemma in `Mathlib/Analysis/Calculus/Inverse`
depending on `FiniteDimensional`, so it was moved to a new file when the original file got split.
-/

public section

open Set
open scoped NNReal

namespace ApproximatesLinearOn

/-- In a real vector space, a function `f` that approximates a linear equivalence on a subset `s`
can be extended to a homeomorphism of the whole space. -/
/-
**ApproximatesLinearOn.exists_homeomorph_extension** 是 Mathlib 中的一个定理，位于命名空间 `Ap
proximatesLinearOn`。
形式化陈述：exists_homeomorph_extension {E : Type*} [NormedAddCommGroup E] [NormedSpac
e Real E] {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensi
onal Real F] {s : Set E} {f : E -> F} {f' : E ≃L[Real] F} {c : Real>=0} (hf : Ap
proximatesLinearOn f (f' : E ->L[Real] F) s c) (hc : Subsingleton E ∨ lipschitzE
xtensionConstant F * c < ‖(f'.symm : F ->L[Real] E)‖₊⁻¹) : exists g : E ≃ₜ F, Eq
On f g s
参数：hf : ApproximatesLinearOn f (f' : E ->L[Real] F) s c；hc : Subsingleton E ∨ li
pschitzExtensionConstant F * c < ‖(f'.symm : F ->L[Real] E)‖₊⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.extend_finite_dimension`：LipschitzOnWith.extend_finite_d
imension {α : Type*} [PseudoMetricSpace α] {E' : Type*} [NormedAddCommGroup E'] 
[NormedSpace Real E'] [Finite…
· 使用定理 `ApproximatesLinearOn.lipschitzOnWith`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LipschitzOnWith.approximatesLinearOn`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
In a real vector space, a function `f` that approximates a linear equivalence on
 a subset `s`
can be extended to a homeomorphism of the whole space.
-/
theorem exists_homeomorph_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {s : Set E}
    {f : E → F} {f' : E ≃L[ℝ] F} {c : ℝ≥0} (hf : ApproximatesLinearOn f (f' : E →L[ℝ] F) s c)
    (hc : Subsingleton E ∨ lipschitzExtensionConstant F * c < ‖(f'.symm : F →L[ℝ] E)‖₊⁻¹) :
    ∃ g : E ≃ₜ F, EqOn f g s := by
  -- the difference `f - f'` is Lipschitz on `s`. It can be extended to a Lipschitz function `u`
  -- on the whole space, with a slightly worse Lipschitz constant. Then `f' + u` will be the
  -- desired homeomorphism.
  obtain ⟨u, hu, uf⟩ :
    ∃ u : E → F, LipschitzWith (lipschitzExtensionConstant F * c) u ∧ EqOn (f - ⇑f') u s :=
    hf.lipschitzOnWith.extend_finite_dimension
  let g : E → F := fun x => f' x + u x
  have fg : EqOn f g s := fun x hx => by simp_rw [g, ← uf hx, Pi.sub_apply, add_sub_cancel]
  have hg : ApproximatesLinearOn g (f' : E →L[ℝ] F) univ (lipschitzExtensionConstant F * c) := by
    apply LipschitzOnWith.approximatesLinearOn
    rw [lipschitzOnWith_univ]
    convert! hu
    ext x
    simp only [g, add_sub_cancel_left, ContinuousLinearEquiv.coe_coe, Pi.sub_apply]
  have : FiniteDimensional ℝ E := f'.symm.finiteDimensional
  exact ⟨hg.toHomeomorph g hc, fg⟩

end ApproximatesLinearOn

