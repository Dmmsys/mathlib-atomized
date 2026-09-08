/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun.DomAct
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Action of `Mᵈᵐᵃ` on `Lᵖ` spaces

In this file we define action of `Mᵈᵐᵃ` on `MeasureTheory.Lp E p μ`
If `f : α → E` is a function representing an equivalence class in `Lᵖ(α, E)`, `M` acts on `α`,
and `c : M`, then `(.mk c : Mᵈᵐᵃ) • [f]` is represented by the function `a ↦ f (c • a)`.

We also prove basic properties of this action.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace DomMulAct

variable {M N α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : MeasureTheory.Measure α} {p : ℝ≥0∞}

section SMul

variable [SMul M α] [SMulInvariantMeasure M α μ] [MeasurableConstSMul M α]

@[to_additive]
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul Mᵈᵐᵃ (Lp E p μ) where
  smul c f := Lp.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _) f

@[to_additive (attr := simp)]
/-
**DomMulAct.smul_Lp_val** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_val (c : Mᵈᵐᵃ) (f : Lp E p μ) : (c • f).1 = c • f.1
参数：c : Mᵈᵐᵃ；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem smul_Lp_val (c : Mᵈᵐᵃ) (f : Lp E p μ) : (c • f).1 = c • f.1 := rfl

@[to_additive]
/-
**DomMulAct.smul_Lp_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_ae_eq (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • f =ᵐ[μ] (f <| mk.symm c • ·)
参数：c : Mᵈᵐᵃ；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.coeFn_compMeasurePreserving`：coeFn_compMeasurePreservin
g (g : Lp E p μb) (hf : MeasurePreserving f μ μb) : compMeasurePreserving f hf g
 =ᵐ[μ] g ∘ f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem smul_Lp_ae_eq (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  Lp.coeFn_compMeasurePreserving _ _

@[to_additive]
/-
**DomMulAct.mk_smul_toLp** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：mk_smul_toLp (c : M) {f : α -> E} (hf : MemLp f p μ) : mk c • hf.toLp f = 
(hf.comp_measurePreserving <| measurePreserving_smul c μ).toLp (f <| c • ·)
参数：c : M；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem mk_smul_toLp (c : M) {f : α → E} (hf : MemLp f p μ) :
    mk c • hf.toLp f =
      (hf.comp_measurePreserving <| measurePreserving_smul c μ).toLp (f <| c • ·) :=
  rfl

@[to_additive (attr := simp)]
/-
**DomMulAct.smul_Lp_const** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_const [IsFiniteMeasure μ] (c : Mᵈᵐᵃ) (a : E) : c • Lp.const p μ a 
= Lp.const p μ a
参数：c : Mᵈᵐᵃ；a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem smul_Lp_const [IsFiniteMeasure μ] (c : Mᵈᵐᵃ) (a : E) :
    c • Lp.const p μ a = Lp.const p μ a :=
  rfl

@[to_additive]
/-
**DomMulAct.mk_smul_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：mk_smul_indicatorConstLp (c : M) {s : Set α} (hs : MeasurableSet s) (hμs :
 μ s != ∞) (b : E) : mk c • indicatorConstLp p hs hμs b = indicatorConstLp p (hs
.preimage <| measurable_const_smul c) (by rwa [SMulInvariantMeasure.measure_prei
mage_smul c hs]) b
参数：c : M；hs : MeasurableSet s；hμs : μ s != ∞；b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem mk_smul_indicatorConstLp (c : M)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (b : E) :
    mk c • indicatorConstLp p hs hμs b =
      indicatorConstLp p (hs.preimage <| measurable_const_smul c)
        (by rwa [SMulInvariantMeasure.measure_preimage_smul c hs]) b :=
  rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul N α] [SMulCommClass M N α] [SMulInvariantMeasure N α μ] [MeasurableConstSMul N α] :
    SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    SMulCommClass Mᵈᵐᵃ 𝕜 (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    SMulCommClass 𝕜 Mᵈᵐᵃ (Lp E p μ) :=
  .symm _ _ _

-- We don't have a typeclass for additive versions of the next few lemmas
-- Should we add `AddDistribAddAction` with `to_additive` both from `MulDistribMulAction`
-- and `DistribMulAction`?

@[to_additive]
/-
**DomMulAct.smul_Lp_add** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_add (c : Mᵈᵐᵃ) : forall f g : Lp E p μ, c • (f + g) = c • f + c • 
g
参数：c : Mᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem smul_Lp_add (c : Mᵈᵐᵃ) : ∀ f g : Lp E p μ, c • (f + g) = c • f + c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
attribute [simp] DomAddAct.vadd_Lp_add

@[to_additive (attr := simp 1001)]
/-
**DomMulAct.smul_Lp_zero** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_zero (c : Mᵈᵐᵃ) : c • (0 : Lp E p μ) = 0
参数：c : Mᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem smul_Lp_zero (c : Mᵈᵐᵃ) : c • (0 : Lp E p μ) = 0 := rfl

@[to_additive]
/-
**DomMulAct.smul_Lp_neg** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_neg (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • (-f) = -(c • f)
参数：c : Mᵈᵐᵃ；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem smul_Lp_neg (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • (-f) = -(c • f) := by
  rcases f with ⟨⟨_⟩, _⟩; rfl

@[to_additive]
/-
**DomMulAct.smul_Lp_sub** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：smul_Lp_sub (c : Mᵈᵐᵃ) : forall f g : Lp E p μ, c • (f - g) = c • f - c • 
g
参数：c : Mᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem smul_Lp_sub (c : Mᵈᵐᵃ) : ∀ f g : Lp E p μ, c • (f - g) = c • f - c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribSMul Mᵈᵐᵃ (Lp E p μ) where
  smul_zero _ := rfl
  smul_add := by rintro _ ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

-- The next few lemmas follow from the `IsIsometricSMul` instance if `1 ≤ p`
@[to_additive (attr := simp)]
/-
**DomMulAct.norm_smul_Lp** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：norm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖ = ‖f‖
参数：c : Mᵈᵐᵃ；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.norm_compMeasurePreserving`：norm_compMeasurePreserving 
(g : Lp E p μb) (hf : MeasurePreserving f μ μb) : ‖compMeasurePreserving f hf g‖
 = ‖g‖
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem norm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]
/-
**DomMulAct.nnnorm_smul_Lp** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：nnnorm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖₊ = ‖f‖₊
参数：c : Mᵈᵐᵃ；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `MeasureTheory.Lp.norm_compMeasurePreserving`：norm_compMeasurePreserving 
(g : Lp E p μb) (hf : MeasurePreserving f μ μb) : ‖compMeasurePreserving f hf g‖
 = ‖g‖
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem nnnorm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖₊ = ‖f‖₊ :=
  NNReal.eq <| Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]
/-
**DomMulAct.dist_smul_Lp** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：dist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : dist (c • f) (c • g) = dist f g
参数：c : Mᵈᵐᵃ；f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DomMulAct.norm_smul_Lp`：norm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖
 = ‖f‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : dist (c • f) (c • g) = dist f g := by
  simp only [dist, ← smul_Lp_neg, ← smul_Lp_add, norm_smul_Lp]

@[to_additive (attr := simp)]
/-
**DomMulAct.edist_smul_Lp** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：edist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : edist (c • f) (c • g) = edist 
f g
参数：c : Mᵈᵐᵃ；f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.edist_dist`：∀ {α : Type u_1} {E : Type u_4} {m : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddComm
Group E] (f g : ↥…
· 使用定理 `DomMulAct.dist_smul_Lp`：dist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : dist 
(c • f) (c • g) = dist f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : edist (c • f) (c • g) = edist f g := by
  simp only [Lp.edist_dist, dist_smul_Lp]

variable [Fact (1 ≤ p)]

@[to_additive]
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIsometricSMul Mᵈᵐᵃ (Lp E p μ) := ⟨edist_smul_Lp⟩

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [SMulInvariantMeasure M α μ] [MeasurableConstSMul M α]

@[to_additive]
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction Mᵈᵐᵃ (Lp E p μ) := Subtype.val_injective.mulAction _ fun _ _ ↦ rfl
/-
**DomMulAct.** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction Mᵈᵐᵃ (Lp E p μ) :=
  Subtype.val_injective.distribMulAction ⟨⟨_, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

end MulAction

end DomMulAct

