/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
/-!
# Action of `DomMulAct` and `DomAddAct` on `α →ₘ[μ] β`

If `M` acts on `α` by measure-preserving transformations, then `Mᵈᵐᵃ` acts on `α →ₘ[μ] β` by sending
each function `f` to `f ∘ (DomMulAct.mk.symm c • ·)`. We define this action and basic instances
about it.

## Implementation notes

In fact, it suffices to require that `(c • ·)` is only quasi-measure-preserving but we do not have a
typeclass for quasi-measure-preserving actions yet.

## Keywords

-/

public section

open MeasureTheory

namespace DomMulAct

variable {M N α β} [MeasurableSpace N] [MeasurableSpace α]
  {μ : MeasureTheory.Measure α} [TopologicalSpace β]

section SMul

variable [SMul M α] [MeasurableConstSMul M α] [SMulInvariantMeasure M α μ]

@[to_additive]
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul c f := f.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _)

@[to_additive]
/-
**DomMulAct.smul_aeeqFun_aeeq** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_aeeqFun_aeeq (c : Mᵈᵐᵃ) (f : α ->ₘ[μ] β) : c • f =ᵐ[μ] (f <| mk.symm 
c • ·)
参数：c : Mᵈᵐᵃ；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compMeasurePreserving`：coeFn_compMeasurePres
erving (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) : g.compMeasurePreserving
 f hf =ᵐ[μ] g ∘ f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem smul_aeeqFun_aeeq (c : Mᵈᵐᵃ) (f : α →ₘ[μ] β) :
    c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  f.coeFn_compMeasurePreserving _

@[to_additive (attr := simp)]
/-
**DomMulAct.mk_smul_mk_aeeqFun** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：mk_smul_mk_aeeqFun (c : M) (f : α -> β) (hf : AEStronglyMeasurable f μ) : 
mk c • AEEqFun.mk f hf = AEEqFun.mk (f <| c • ·) (hf.comp_measurePreserving (mea
surePreserving_smul _ _))
参数：c : M；f : α -> β；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_mk_aeeqFun (c : M) (f : α → β) (hf : AEStronglyMeasurable f μ) :
    mk c • AEEqFun.mk f hf = AEEqFun.mk (f <| c • ·)
      (hf.comp_measurePreserving (measurePreserving_smul _ _)) :=
  rfl

@[to_additive (attr := simp)]
/-
**DomMulAct.smul_aeeqFun_const** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_aeeqFun_const (c : Mᵈᵐᵃ) (b : β) : c • (AEEqFun.const α b : α ->ₘ[μ] 
β) = AEEqFun.const α b
参数：c : Mᵈᵐᵃ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_aeeqFun_const (c : Mᵈᵐᵃ) (b : β) :
    c • (AEEqFun.const α b : α →ₘ[μ] β) = AEEqFun.const α b :=
  rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul N β] [ContinuousConstSMul N β] : SMulCommClass Mᵈᵐᵃ N (α →ₘ[μ] β) where
  smul_comm := by rintro _ _ ⟨_⟩; rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul N β] [ContinuousConstSMul N β] : SMulCommClass N Mᵈᵐᵃ (α →ₘ[μ] β) :=
  .symm _ _ _

@[to_additive]
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul N α] [MeasurableConstSMul N α] [SMulInvariantMeasure N α μ] [SMulCommClass M N α] :
    SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α →ₘ[μ] β) where
  smul_comm := mk.surjective.forall.2 fun c₁ ↦ mk.surjective.forall.2 fun c₂ ↦
    (AEEqFun.induction_on · fun f hf ↦ by simp only [mk_smul_mk_aeeqFun, smul_comm])
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero β] : SMulZeroClass Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_zero _ := rfl

-- TODO: add `AEEqFun.addZeroClass`
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid β] [ContinuousAdd β] : DistribSMul Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_add := by rintro _ ⟨⟩ ⟨⟩; rfl

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [MeasurableConstSMul M α] [SMulInvariantMeasure M α μ]

@[to_additive]
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction Mᵈᵐᵃ (α →ₘ[μ] β) where
  one_smul := (AEEqFun.induction_on · fun _ _ ↦ by
    simp only [← mk_one, mk_smul_mk_aeeqFun, one_smul])
  mul_smul := mk.surjective.forall.2 fun _ ↦ mk.surjective.forall.2 fun _ ↦
    (AEEqFun.induction_on · fun _ _ ↦ by simp only [← mk_mul, mk_smul_mk_aeeqFun, mul_smul])
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid β] [ContinuousMul β] : MulDistribMulAction Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_one _ := rfl
  smul_mul := by rintro _ ⟨⟩ ⟨⟩; rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid β] [ContinuousAdd β] : DistribMulAction Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_zero := smul_zero
  smul_add := smul_add

end MulAction

end DomMulAct

