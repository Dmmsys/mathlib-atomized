/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Almost everywhere differentiability of functions with locally bounded variation

In this file we show that a bounded variation function is differentiable almost everywhere.
This implies that Lipschitz functions from the real line into finite-dimensional vector spaces
are also differentiable almost everywhere.

## Main definitions and results

* `LocallyBoundedVariationOn.ae_differentiableWithinAt` shows that a bounded variation
  function on a subset of ℝ into a finite-dimensional real vector space is differentiable almost
  everywhere, with `DifferentiableWithinAt` in its conclusion.
* `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` shows that a bounded variation function on
  an interval of ℝ into a finite-dimensional real vector space is differentiable almost everywhere,
  with `DifferentiableAt` in its conclusion.
* `LipschitzOnWith.ae_differentiableWithinAt` is the same result for Lipschitz functions.

We also give several variations around these results.

-/

public section

open scoped NNReal Topology ENNReal
open Set MeasureTheory Filter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section

open Finset

variable {α : Type*} [LinearOrder α] {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s : Set α} {f : α → E} {g : α → F} {C D : ℝ≥0∞} {B : E →L[ℝ] F →L[ℝ] G}

/-
**eVariationOn_bilinear_comp_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eVariationOn_bilinear_comp_le (hf : forall x in s, ‖f x‖ₑ <= C) (hg : fora
ll x in s, ‖g x‖ₑ <= D) (B : E ->L[Real] F ->L[Real] G) : eVariationOn (fun x =>
 B (f x) (g x) : α -> G) s <= ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f 
s)
参数：hf : forall x in s, ‖f x‖ₑ <= C；hg : forall x in s, ‖g x‖ₑ <= D；B : E ->L[Rea
l] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ContinuousLinearMap.le_opENorm₂`：le_opENorm₂ [RingHomIsometric σ₁₃] (f :
 E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ₑ <= ‖f‖ₑ * ‖x‖ₑ * ‖y‖ₑ
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
（共 51 条，此处仅展示前 30 条）
-/
lemma eVariationOn_bilinear_comp_le (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D)
    (B : E →L[ℝ] F →L[ℝ] G) :
    eVariationOn (fun x ↦ B (f x) (g x) : α → G) s ≤
      ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i ∈ range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u i)))
  _ ≤ ∑ i ∈ range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u (i + 1)))) +
      ∑ i ∈ range n, edist (B (f (u i)) (g (u (i + 1)))) (B (f (u i)) (g (u i))) := by
    rw [← Finset.sum_add_distrib]
    gcongr with i hi
    apply edist_triangle
  _ = ∑ i ∈ range n, ‖B (f (u (i + 1)) - f (u i)) (g (u (i + 1)))‖ₑ +
      ∑ i ∈ range n, ‖B (f (u i)) (g (u (i + 1)) - g (u i))‖ₑ := by simp [edist_eq_enorm_sub]
  _ ≤ ∑ i ∈ range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * ‖g (u (i + 1))‖ₑ +
      ∑ i ∈ range n, ‖B‖ₑ * ‖f (u i)‖ₑ * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply ContinuousLinearMap.le_opENorm₂
    · apply ContinuousLinearMap.le_opENorm₂
  _ ≤ ∑ i ∈ range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * D +
      ∑ i ∈ range n, ‖B‖ₑ * C * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply hg _ (u_mem _)
    · apply hf _ (u_mem _)
  _ = ‖B‖ₑ * D * ∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖ₑ +
      ‖B‖ₑ * C * ∑ i ∈ range n, ‖g (u (i + 1)) - g (u i)‖ₑ := by
    simp only [← sum_mul, ← mul_sum]
    ring
  _ ≤ ‖B‖ₑ * D * eVariationOn f s + ‖B‖ₑ * C * eVariationOn g s := by
    simp only [← edist_eq_enorm_sub]
    gcongr
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi ↦ u_mem i)
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi ↦ u_mem i)
  _ = ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by ring

@[to_fun eVariationOn_fun_smul_le]
/-
**eVariationOn_smul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eVariationOn_smul_le {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F} [NormedRing 𝕜] 
[NormedAlgebra Real 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F] [IsScalarTower Real 𝕜 F]
 {C D : Real>=0∞} {s : Set α} (hf : forall x in s, ‖f x‖ₑ <= C) (hg : forall x i
n s, ‖g x‖ₑ <= D) : eVariationOn (f • g) s <= C * eVariationOn g s + D * eVariat
ionOn f s
参数：hf : forall x in s, ‖f x‖ₑ <= C；hg : forall x in s, ‖g x‖ₑ <= D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `eVariationOn_bilinear_comp_le`：eVariationOn_bilinear_comp_le (hf : foral
l x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D) (B : E ->L[Real] F ->L[
Real] G) : eVariati…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ContinuousLinearMap.opENorm_lsmul_le`：opENorm_lsmul_le : ‖(lsmul 𝕜 R : R
 ->L[𝕜] E ->L[𝕜] E)‖ₑ <= 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma eVariationOn_smul_le {𝕜 : Type*} {f : α → 𝕜} {g : α → F}
    [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    {C D : ℝ≥0∞} {s : Set α} (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D) :
    eVariationOn (f • g) s ≤ C * eVariationOn g s + D * eVariationOn f s := by
  apply (eVariationOn_bilinear_comp_le hf hg (B := ContinuousLinearMap.lsmul ℝ 𝕜)).trans
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul]

@[to_fun eVariationOn_fun_mul_le]
/-
**eVariation_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eVariation_mul_le {f g : α -> Real} {C D : Real>=0∞} {s : Set α} (hf : for
all x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D) : eVariationOn (f * g
) s <= C * eVariationOn g s + D * eVariationOn f s
参数：hf : forall x in s, ‖f x‖ₑ <= C；hg : forall x in s, ‖g x‖ₑ <= D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eVariationOn_smul_le`：eVariationOn_smul_le {𝕜 : Type*} {f : α -> 𝕜} {g :
 α -> F} [NormedRing 𝕜] [NormedAlgebra Real 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F] 
[IsScalarT…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma eVariation_mul_le {f g : α → ℝ}
    {C D : ℝ≥0∞} {s : Set α} (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D) :
    eVariationOn (f * g) s ≤ C * eVariationOn g s + D * eVariationOn f s := by
  simpa using eVariationOn_smul_le hf hg
/-
**BoundedVariationOn.bilinear_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BoundedVariationOn.bilinear_comp (hf : BoundedVariationOn f s) (hg : Bound
edVariationOn g s) (B : E ->L[Real] F ->L[Real] G) : BoundedVariationOn (fun x =
> B (f x) (g x)) s
参数：hf : BoundedVariationOn f s；hg : BoundedVariationOn g s；B : E ->L[Real] F ->L
[Real] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.BoundedVariation.0.BoundedVariationOn.bilinear
_comp._abel_1_1`：∀ {α : Type u_2} {E : Type u_1} [inst : NormedAddCommGroup E] {
f : α → E} (x y : α), f y = f x + (f y - f x)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eVariationOn.edist_le`：edist_le (f : α -> E) {s : Set α} {x y : α} (hx :
 x in s) (hy : y in s) : edist (f x) (f y) <= eVariationOn f s
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用引理 `eVariationOn_bilinear_comp_le`：eVariationOn_bilinear_comp_le (hf : foral
l x in s, ‖f x‖ₑ <= C) (hg : forall x in s, ‖g x‖ₑ <= D) (B : E ->L[Real] F ->L[
Real] G) : eVariati…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
（共 32 条，此处仅展示前 30 条）
-/
lemma BoundedVariationOn.bilinear_comp
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) (B : E →L[ℝ] F →L[ℝ] G) :
    BoundedVariationOn (fun x ↦ B (f x) (g x)) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x, hx⟩⟩
  · simp
  suffices eVariationOn (fun x ↦ (B (f x)) (g x)) s < ∞ from ne_of_lt this
  have A (y) (hy : y ∈ s) : ‖f y‖ₑ ≤ ‖f x‖ₑ + eVariationOn f s := by
    grw [show f y = f x + (f y - f x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  have A' (y) (hy : y ∈ s) : ‖g y‖ₑ ≤ ‖g x‖ₑ + eVariationOn g s := by
    grw [show g y = g x + (g y - g x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  grw [eVariationOn_bilinear_comp_le A A']
  simp [mul_add, ENNReal.mul_lt_top_iff, hf.lt_top, hg.lt_top]

@[to_fun]
/-
**BoundedVariationOn.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BoundedVariationOn.smul {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F} [NormedRing 
𝕜] [NormedAlgebra Real 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F] [IsScalarTower Real 𝕜
 F] {s : Set α} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) : Bo
undedVariationOn (f • g) s
参数：hf : BoundedVariationOn f s；hg : BoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BoundedVariationOn.bilinear_comp`：BoundedVariationOn.bilinear_comp (hf :
 BoundedVariationOn f s) (hg : BoundedVariationOn g s) (B : E ->L[Real] F ->L[Re
al] G) : BoundedVariat…
-/
lemma BoundedVariationOn.smul {𝕜 : Type*} {f : α → 𝕜} {g : α → F}
    [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    {s : Set α} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f • g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ 𝕜)

@[to_fun]
/-
**BoundedVariationOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BoundedVariationOn.mul {f g : α -> Real} {s : Set α} (hf : BoundedVariatio
nOn f s) (hg : BoundedVariationOn g s) : BoundedVariationOn (f * g) s
参数：hf : BoundedVariationOn f s；hg : BoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BoundedVariationOn.bilinear_comp`：BoundedVariationOn.bilinear_comp (hf :
 BoundedVariationOn f s) (hg : BoundedVariationOn g s) (B : E ->L[Real] F ->L[Re
al] G) : BoundedVariat…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma BoundedVariationOn.mul {f g : α → ℝ} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f * g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ ℝ)
/-
**LocallyBoundedVariationOn.bilinear_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyBoundedVariationOn.bilinear_comp (hf : LocallyBoundedVariationOn f 
s) (hg : LocallyBoundedVariationOn g s) (B : E ->L[Real] F ->L[Real] G) : Locall
yBoundedVariationOn (fun x => B (f x) (g x)) s
参数：hf : LocallyBoundedVariationOn f s；hg : LocallyBoundedVariationOn g s；B : E -
>L[Real] F ->L[Real] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `BoundedVariationOn.bilinear_comp`：BoundedVariationOn.bilinear_comp (hf :
 BoundedVariationOn f s) (hg : BoundedVariationOn g s) (B : E ->L[Real] F ->L[Re
al] G) : BoundedVariat…
-/
lemma LocallyBoundedVariationOn.bilinear_comp (hf : LocallyBoundedVariationOn f s)
    (hg : LocallyBoundedVariationOn g s) (B : E →L[ℝ] F →L[ℝ] G) :
    LocallyBoundedVariationOn (fun x ↦ B (f x) (g x)) s :=
  fun a b ha hb ↦ (hf a b ha hb).bilinear_comp (hg a b ha hb) B

@[to_fun]
/-
**LocallyBoundedVariationOn.smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyBoundedVariationOn.smul {𝕜 : Type*} {f : α -> 𝕜} {g : α -> F} [Norm
edRing 𝕜] [NormedAlgebra Real 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F] [IsScalarTower
 Real 𝕜 F] {s : Set α} (hf : LocallyBoundedVariationOn f s) (hg : LocallyBounded
VariationOn g s) : LocallyBoundedVariationOn (f • g) s
参数：hf : LocallyBoundedVariationOn f s；hg : LocallyBoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyBoundedVariationOn.bilinear_comp`：LocallyBoundedVariationOn.bilin
ear_comp (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g 
s) (B : E ->L[Real] F ->L[Rea…
-/
lemma LocallyBoundedVariationOn.smul {𝕜 : Type*} {f : α → 𝕜} {g : α → F}
    [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    {s : Set α} (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f • g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ 𝕜)

@[to_fun]
/-
**LocallyBoundedVariationOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyBoundedVariationOn.mul {f g : α -> Real} {s : Set α} (hf : LocallyB
oundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) : LocallyBoundedVari
ationOn (f * g) s
参数：hf : LocallyBoundedVariationOn f s；hg : LocallyBoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyBoundedVariationOn.bilinear_comp`：LocallyBoundedVariationOn.bilin
ear_comp (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g 
s) (B : E ->L[Real] F ->L[Rea…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma LocallyBoundedVariationOn.mul {f g : α → ℝ} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f * g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ ℝ)

end

namespace LocallyBoundedVariationOn

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiableWithinAt_of_mem`. -/
/-
**LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real** 是 Mathlib 中的
一个定理，位于命名空间 `LocallyBoundedVariationOn`。
形式化陈述：ae_differentiableWithinAt_of_mem_real {f : Real -> Real} {s : Set Real} (h
 : LocallyBoundedVariationOn f s) : forallᵐ x, x in s -> DifferentiableWithinAt 
Real f s x
参数：h : LocallyBoundedVariationOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`：LocallyBound
edVariationOn.exists_monotoneOn_sub_monotoneOn {f : α -> Real} {s : Set α} (h : 
LocallyBoundedVariationOn f s) : exists p q : α …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MonotoneOn.ae_differentiableWithinAt_of_mem`：MonotoneOn.ae_differentiabl
eWithinAt_of_mem {f : Real -> Real} {s : Set Real} (hf : MonotoneOn f s) : foral
lᵐ x, x in s -> DifferentiableWit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableWithinAt.sub`：DifferentiableWithinAt.sub (hf : Differentia
bleWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithi
nAt 𝕜 (f - g) s …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A bounded variation function into `ℝ` is differentiable almost everywhere. Super
seded by
`ae_differentiableWithinAt_of_mem`.
-/
theorem ae_differentiableWithinAt_of_mem_real {f : ℝ → ℝ} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨p, q, hp, hq, rfl⟩ : ∃ p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q :=
    h.exists_monotoneOn_sub_monotoneOn
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem] with
    x hxp hxq xs
  exact (hxp xs).sub (hxq xs)

/-- A bounded variation function into a finite-dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiableWithinAt_of_mem`. -/
/-
**LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_pi** 是 Mathlib 中的一个
定理，位于命名空间 `LocallyBoundedVariationOn`。
形式化陈述：ae_differentiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : Real -> ι
 -> Real} {s : Set Real} (h : LocallyBoundedVariationOn f s) : forallᵐ x, x in s
 -> DifferentiableWithinAt Real f s x
参数：h : LocallyBoundedVariationOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.eval`：∀ {ι : Type x} {α : ι → Type u} [inst : (i : ι) → Ps
eudoEMetricSpace (α i)] [inst_1 : Fintype ι] (i : ι),   LipschitzWith 1 (Functio
n.eval i…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real`：ae_diff
erentiableWithinAt_of_mem_real {f : Real -> Real} {s : Set Real} (h : LocallyBou
ndedVariationOn f s) : forallᵐ x, x in s -> Different…
· 使用定理 `LipschitzWith.comp_locallyBoundedVariationOn`：LipschitzWith.comp_locally
BoundedVariationOn {f : E -> F} {C : Real>=0} (hf : LipschitzWith C f) {g : α ->
 E} {s : Set α} (h : LocallyBounde…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `differentiableWithinAt_pi`：differentiableWithinAt_pi : DifferentiableWit
hinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x

--- 原说明 ---
A bounded variation function into a finite-dimensional product vector space is d
ifferentiable
almost everywhere. Superseded by `ae_differentiableWithinAt_of_mem`.
-/
theorem ae_differentiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 fun x : ι → ℝ => x i := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (fun x : ℝ => f x i) s x := fun i ↦ by
    apply ae_differentiableWithinAt_of_mem_real
    exact LipschitzWith.comp_locallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

/-- A real function into a finite-dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
/-
**LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem** 是 Mathlib 中的一个定理，
位于命名空间 `LocallyBoundedVariationOn`。
形式化陈述：ae_differentiableWithinAt_of_mem {f : Real -> V} {s : Set Real} (h : Local
lyBoundedVariationOn f s) : forallᵐ x, x in s -> DifferentiableWithinAt Real f s
 x
参数：h : LocallyBoundedVariationOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_pi`：ae_differ
entiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : Real -> ι -> Real} {s : 
Set Real} (h : LocallyBoundedVariationOn f s) : for…
· 使用定理 `LipschitzWith.comp_locallyBoundedVariationOn`：LipschitzWith.comp_locally
BoundedVariationOn {f : E -> F} {C : Real>=0} (hf : LipschitzWith C f) {g : α ->
 E} {s : Set α} (h : LocallyBounde…
· 使用定理 `ContinuousLinearEquiv.lipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Nontrivia
llyNormedField 𝕜₂] [i…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
A real function into a finite-dimensional real vector space with bounded variati
on on a set
is differentiable almost everywhere in this set.
-/
theorem ae_differentiableWithinAt_of_mem {f : ℝ → V} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let A := (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    exact (ContinuousLinearEquiv.comp_differentiableWithinAt_iff _).mp (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_locallyBoundedVariationOn h

/-- A real function into a finite-dimensional real vector space with bounded variation on an
interval is differentiable almost everywhere in this interval. This one differs from
`LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem` by using `DifferentiableAt` instead of
`DifferentiableWithinAt` in its conclusion. -/
/-
**LocallyBoundedVariationOn._root_.BoundedVariationOn.ae_differentiableAt_of_mem
_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `LocallyBoundedVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function into a finite-dimensional real vector space with bounded variati
on on an
interval is differentiable almost everywhere in this interval. This one differs 
from
`LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem` by using `Different
iableAt` instead of
`DifferentiableWithinAt` in its conclusion.
-/
theorem _root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc {f : ℝ → V} {a b : ℝ}
    (h : BoundedVariationOn f (uIcc a b)) : ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x := by
  have h₁ : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, h₁, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc, mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hx₄.left hx₂.symm) (lt_of_le_of_ne hx₄.right hx₃))

/-- A real function into a finite-dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
/-
**LocallyBoundedVariationOn.ae_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 
`LocallyBoundedVariationOn`。
形式化陈述：ae_differentiableWithinAt {f : Real -> V} {s : Set Real} (h : LocallyBound
edVariationOn f s) (hs : MeasurableSet s) : forallᵐ x ∂volume.restrict s, Differ
entiableWithinAt Real f s x
参数：h : LocallyBoundedVariationOn f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem`：ae_different
iableWithinAt_of_mem {f : Real -> V} {s : Set Real} (h : LocallyBoundedVariation
On f s) : forallᵐ x, x in s -> DifferentiableWit…

--- 原说明 ---
A real function into a finite-dimensional real vector space with bounded variati
on on a set
is differentiable almost everywhere in this set.
-/
theorem ae_differentiableWithinAt {f : ℝ → V} {s : Set ℝ} (h : LocallyBoundedVariationOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiableWithinAt_of_mem

/-- A real function into a finite-dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
/-
**LocallyBoundedVariationOn.ae_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `Local
lyBoundedVariationOn`。
形式化陈述：ae_differentiableAt {f : Real -> V} (h : LocallyBoundedVariationOn f univ)
 : forallᵐ x, DifferentiableAt Real f x
参数：h : LocallyBoundedVariationOn f univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem`：ae_different
iableWithinAt_of_mem {f : Real -> V} {s : Set Real} (h : LocallyBoundedVariation
On f s) : forallᵐ x, x in s -> DifferentiableWit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
A real function into a finite-dimensional real vector space with bounded variati
on
is differentiable almost everywhere.
-/
theorem ae_differentiableAt {f : ℝ → V} (h : LocallyBoundedVariationOn f univ) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx
  exact hx (mem_univ _)

end LocallyBoundedVariationOn

/-- A real function into a finite-dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzOnWith.ae_differentiableWithinAt_of_mem`.
-/
/-
**LipschitzOnWith.ae_differentiableWithinAt_of_mem_real** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：LipschitzOnWith.ae_differentiableWithinAt_of_mem_real {C : Real>=0} {f : R
eal -> V} {s : Set Real} (h : LipschitzOnWith C f s) : forallᵐ x, x in s -> Diff
erentiableWithinAt Real f s x
参数：h : LipschitzOnWith C f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem`：ae_different
iableWithinAt_of_mem {f : Real -> V} {s : Set Real} (h : LocallyBoundedVariation
On f s) : forallᵐ x, x in s -> DifferentiableWit…
· 使用定理 `LipschitzOnWith.locallyBoundedVariationOn`：LipschitzOnWith.locallyBounde
dVariationOn {f : Real -> E} {C : Real>=0} {s : Set Real} (hf : LipschitzOnWith 
C f s) : LocallyBoundedVariatio…

--- 原说明 ---
A real function into a finite-dimensional real vector space which is Lipschitz o
n a set
is differentiable almost everywhere in this set. For the general Rademacher theo
rem assuming
that the source space is finite dimensional, see `LipschitzOnWith.ae_differentia
bleWithinAt_of_mem`.
-/
theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem_real {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x :=
  h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

/-- A real function into a finite-dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzOnWith.ae_differentiableWithinAt`. -/
/-
**LipschitzOnWith.ae_differentiableWithinAt_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.ae_differentiableWithinAt_real {C : Real>=0} {f : Real -> 
V} {s : Set Real} (h : LipschitzOnWith C f s) (hs : MeasurableSet s) : forallᵐ x
 ∂volume.restrict s, DifferentiableWithinAt Real f s x
参数：h : LipschitzOnWith C f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableWithinAt`：ae_differentiableWi
thinAt {f : Real -> V} {s : Set Real} (h : LocallyBoundedVariationOn f s) (hs : 
MeasurableSet s) : forallᵐ x ∂volume.rest…
· 使用定理 `LipschitzOnWith.locallyBoundedVariationOn`：LipschitzOnWith.locallyBounde
dVariationOn {f : Real -> E} {C : Real>=0} {s : Set Real} (hf : LipschitzOnWith 
C f s) : LocallyBoundedVariatio…

--- 原说明 ---
A real function into a finite-dimensional real vector space which is Lipschitz o
n a set
is differentiable almost everywhere in this set. For the general Rademacher theo
rem assuming
that the source space is finite dimensional, see `LipschitzOnWith.ae_differentia
bleWithinAt`.
-/
theorem LipschitzOnWith.ae_differentiableWithinAt_real {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x :=
  h.locallyBoundedVariationOn.ae_differentiableWithinAt hs

/-- A real Lipschitz function into a finite-dimensional real vector space is differentiable
almost everywhere. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzWith.ae_differentiableAt`. -/
/-
**LipschitzWith.ae_differentiableAt_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.ae_differentiableAt_real {C : Real>=0} {f : Real -> V} (h : 
LipschitzWith C f) : forallᵐ x, DifferentiableAt Real f x
参数：h : LipschitzWith C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedVariationOn.ae_differentiableAt`：ae_differentiableAt {f : 
Real -> V} (h : LocallyBoundedVariationOn f univ) : forallᵐ x, DifferentiableAt 
Real f x
· 使用定理 `LipschitzWith.locallyBoundedVariationOn`：LipschitzWith.locallyBoundedVar
iationOn {f : Real -> E} {C : Real>=0} (hf : LipschitzWith C f) (s : Set Real) :
 LocallyBoundedVariationOn f …

--- 原说明 ---
A real Lipschitz function into a finite-dimensional real vector space is differe
ntiable
almost everywhere. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzWith.ae_differentiabl
eAt`.
-/
theorem LipschitzWith.ae_differentiableAt_real {C : ℝ≥0} {f : ℝ → V} (h : LipschitzWith C f) :
    ∀ᵐ x, DifferentiableAt ℝ f x :=
  (h.locallyBoundedVariationOn univ).ae_differentiableAt
