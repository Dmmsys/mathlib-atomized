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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Mᵈᵐᵃ (α ->ₘ[μ] β)
  body: f.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _)

@[to_additive]

中文:
实例 :
  签名: SMul Mᵈᵐᵃ (α ->ₘ[μ] β)
  定义体: f.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _)

@[to_additive]

Depends on / 依赖: compMeasurePreserving, f.compMeasurePreserving, measurePreserving_smul, mk.symm
-/
instance : SMul Mᵈᵐᵃ (α ->ₘ[μ] β) where
  smul c f := f.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _)

@[to_additive]
/--
theorem `smul_aeeqFun_aeeq` / 定理 `smul_aeeqFun_aeeq`

English:
theorem smul_aeeqFun_aeeq
  given: (c : Mᵈᵐᵃ) (f : α ->ₘ[μ] β)
  proof: f.coeFn_compMeasurePreserving _

@[to_additive (attr := simp)]

中文:
定理 smul_aeeqFun_aeeq
  条件: (c : Mᵈᵐᵃ) (f : α ->ₘ[μ] β)
  证明: f.coeFn_compMeasurePreserving _

@[to_additive (attr := simp)]

Depends on / 依赖: coeFn_compMeasurePreserving, f.coeFn_compMeasurePreserving
-/
theorem smul_aeeqFun_aeeq (c : Mᵈᵐᵃ) (f : α ->ₘ[μ] β) :
    c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  f.coeFn_compMeasurePreserving _

@[to_additive (attr := simp)]
/--
theorem `mk_smul_mk_aeeqFun` / 定理 `mk_smul_mk_aeeqFun`

English:
theorem mk_smul_mk_aeeqFun
  given: (c : M) (f : α -> β) (hf : AEStronglyMeasurable f μ)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_smul_mk_aeeqFun
  条件: (c : M) (f : α -> β) (hf : AEStronglyMeasurable f μ)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_smul_mk_aeeqFun (c : M) (f : α -> β) (hf : AEStronglyMeasurable f μ) :
    mk c • AEEqFun.mk f hf = AEEqFun.mk (f <| c • ·)
      (hf.comp_measurePreserving (measurePreserving_smul _ _)) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_aeeqFun_const` / 定理 `smul_aeeqFun_const`

English:
theorem smul_aeeqFun_const
  given: (c : Mᵈᵐᵃ) (b : β)
  proof: rfl

中文:
定理 smul_aeeqFun_const
  条件: (c : Mᵈᵐᵃ) (b : β)
  证明: rfl
-/
theorem smul_aeeqFun_const (c : Mᵈᵐᵃ) (b : β) :
    c • (AEEqFun.const α b : α ->ₘ[μ] β) = AEEqFun.const α b :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: N β] [ContinuousConstSMul N β] : SMulCommClass Mᵈᵐᵃ N (α ->ₘ[μ] β) where
  body: by rintro _ _ ⟨_⟩; rfl

中文:
实例 [SMul
  签名: N β] [ContinuousConstSMul N β] : SMulCommClass Mᵈᵐᵃ N (α ->ₘ[μ] β) where
  定义体: by rintro _ _ ⟨_⟩; rfl
-/
instance [SMul N β] [ContinuousConstSMul N β] : SMulCommClass Mᵈᵐᵃ N (α ->ₘ[μ] β) where
  smul_comm := by rintro _ _ ⟨_⟩; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: N β] [ContinuousConstSMul N β] : SMulCommClass N Mᵈᵐᵃ (α ->ₘ[μ] β)
  body: .symm _ _ _

@[to_additive]

中文:
实例 [SMul
  签名: N β] [ContinuousConstSMul N β] : SMulCommClass N Mᵈᵐᵃ (α ->ₘ[μ] β)
  定义体: .symm _ _ _

@[to_additive]
-/
instance [SMul N β] [ContinuousConstSMul N β] : SMulCommClass N Mᵈᵐᵃ (α ->ₘ[μ] β) :=
  .symm _ _ _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: N α] [MeasurableConstSMul N α] [SMulInvariantMeasure N α μ] [SMulCommClass M N α] :
  body: mk.surjective.forall.2 fun c₁ => mk.surjective.forall.2 fun c₂ =>
    (AEEqFun.induction_on · fun f hf => by simp only [mk_smul_mk_aeeqFun, smul_comm])

中文:
实例 [SMul
  签名: N α] [MeasurableConstSMul N α] [SMulInvariantMeasure N α μ] [SMulCommClass M N α] :
  定义体: mk.surjective.forall.2 fun c₁ => mk.surjective.forall.2 fun c₂ =>
    (AEEqFun.induction_on · fun f hf => by simp only [mk_smul_mk_aeeqFun, smul_comm])

Depends on / 依赖: mk.surjective.forall, surjective
-/
instance [SMul N α] [MeasurableConstSMul N α] [SMulInvariantMeasure N α μ] [SMulCommClass M N α] :
    SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α ->ₘ[μ] β) where
  smul_comm := mk.surjective.forall.2 fun c₁ => mk.surjective.forall.2 fun c₂ =>
    (AEEqFun.induction_on · fun f hf => by simp only [mk_smul_mk_aeeqFun, smul_comm])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: β] : SMulZeroClass Mᵈᵐᵃ (α ->ₘ[μ] β) where
  body: rfl

中文:
实例 [Zero
  签名: β] : SMulZeroClass Mᵈᵐᵃ (α ->ₘ[μ] β) where
  定义体: rfl
-/
instance [Zero β] : SMulZeroClass Mᵈᵐᵃ (α ->ₘ[μ] β) where
  smul_zero _ := rfl

-- TODO: add `AEEqFun.addZeroClass`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: β] [ContinuousAdd β] : DistribSMul Mᵈᵐᵃ (α ->ₘ[μ] β) where
  body: by rintro _ ⟨⟩ ⟨⟩; rfl

中文:
实例 [AddMonoid
  签名: β] [ContinuousAdd β] : DistribSMul Mᵈᵐᵃ (α ->ₘ[μ] β) where
  定义体: by rintro _ ⟨⟩ ⟨⟩; rfl
-/
instance [AddMonoid β] [ContinuousAdd β] : DistribSMul Mᵈᵐᵃ (α ->ₘ[μ] β) where
  smul_add := by rintro _ ⟨⟩ ⟨⟩; rfl

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [MeasurableConstSMul M α] [SMulInvariantMeasure M α μ]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Mᵈᵐᵃ (α ->ₘ[μ] β)
  body: (AEEqFun.induction_on · fun _ _ => by
    simp only [← mk_one, mk_smul_mk_aeeqFun, one_smul])
  mul_smul := mk.surjective.forall.2 fun _ => mk.surjective.forall.2 fun _ =>
    (AEEqFun.induction_on · fun _ _ => by simp only [← mk_mul, mk_smul_mk_aeeqFun, mul_smul])

中文:
实例 :
  签名: MulAction Mᵈᵐᵃ (α ->ₘ[μ] β)
  定义体: (AEEqFun.induction_on · fun _ _ => by
    simp only [← mk_one, mk_smul_mk_aeeqFun, one_smul])
  mul_smul := mk.surjective.forall.2 fun _ => mk.surjective.forall.2 fun _ =>
    (AEEqFun.induction_on · fun _ _ => by simp only [← mk_mul, mk_smul_mk_aeeqFun, mul_smul])

Depends on / 依赖: AEEqFun, AEEqFun.induction_on, induction_on, mk.surjective.forall, mk_mul, mk_one, mk_smul_mk_aeeqFun, mul_smul, one_smul, surjective
-/
instance : MulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  one_smul := (AEEqFun.induction_on · fun _ _ => by
    simp only [← mk_one, mk_smul_mk_aeeqFun, one_smul])
  mul_smul := mk.surjective.forall.2 fun _ => mk.surjective.forall.2 fun _ =>
    (AEEqFun.induction_on · fun _ _ => by simp only [← mk_mul, mk_smul_mk_aeeqFun, mul_smul])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: β] [ContinuousMul β] : MulDistribMulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  body: rfl
  smul_mul := by rintro _ ⟨⟩ ⟨⟩; rfl

中文:
实例 [Monoid
  签名: β] [ContinuousMul β] : MulDistribMulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  定义体: rfl
  smul_mul := by rintro _ ⟨⟩ ⟨⟩; rfl
-/
instance [Monoid β] [ContinuousMul β] : MulDistribMulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  smul_one _ := rfl
  smul_mul := by rintro _ ⟨⟩ ⟨⟩; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: β] [ContinuousAdd β] : DistribMulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  body: smul_zero
  smul_add := smul_add

中文:
实例 [AddMonoid
  签名: β] [ContinuousAdd β] : DistribMulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  定义体: smul_zero
  smul_add := smul_add

Depends on / 依赖: smul_zero
-/
instance [AddMonoid β] [ContinuousAdd β] : DistribMulAction Mᵈᵐᵃ (α ->ₘ[μ] β) where
  smul_zero := smul_zero
  smul_add := smul_add

end MulAction

end DomMulAct
