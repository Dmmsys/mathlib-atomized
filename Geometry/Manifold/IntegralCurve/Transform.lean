/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

This file mirrors `Mathlib/Analysis/ODE/Transform`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

public section

open Function Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

/-! ### Translation lemmas -/

section Translation

/-
**IsMIntegralCurveOn.comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.comp_add (hγ : IsMIntegralCurveOn γ v s) (dt : Real) : 
IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt in s }
参数：hγ : IsMIntegralCurveOn γ v s；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => x + m
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `HasFDerivWithinAt.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type u_…
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
lemma IsMIntegralCurveOn.comp_add (hγ : IsMIntegralCurveOn γ v s) (dt : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  intro t ht
  rw [comp_apply, ← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivWithinAt.comp t (hγ (t + dt) ht) _ subset_rfl
  refine ⟨(continuous_add_const _).continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  exact (hasFDerivWithinAt_id _ _).add_const _
/-
**isMIntegralCurveOn_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveOn_comp_add {dt : Real} : IsMIntegralCurveOn (γ ∘ (· + dt)
) v { t | t + dt in s } ↔ IsMIntegralCurveOn γ v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsMIntegralCurveOn.comp_add`：IsMIntegralCurveOn.comp_add (hγ : IsMIntegr
alCurveOn γ v s) (dt : Real) : IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt 
in s }
-/
lemma isMIntegralCurveOn_comp_add {dt : ℝ} :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } ↔ IsMIntegralCurveOn γ v s := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp
  · simp
/-
**isMIntegralCurveOn_comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveOn_comp_sub {dt : Real} : IsMIntegralCurveOn (γ ∘ (· - dt)
) v { t | t - dt in s } ↔ IsMIntegralCurveOn γ v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMIntegralCurveOn_comp_add`：isMIntegralCurveOn_comp_add {dt : Real} : I
sMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt in s } ↔ IsMIntegralCurveOn γ v 
s
-/
lemma isMIntegralCurveOn_comp_sub {dt : ℝ} :
    IsMIntegralCurveOn (γ ∘ (· - dt)) v { t | t - dt ∈ s } ↔ IsMIntegralCurveOn γ v s := by
  simpa using! isMIntegralCurveOn_comp_add (dt := -dt)
/-
**IsMIntegralCurveAt.comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt.comp_add (hγ : IsMIntegralCurveAt γ v t₀) (dt : Real) :
 IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt)
参数：hγ : IsMIntegralCurveAt γ v t₀；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMIntegralCurveAt_iff'`：isMIntegralCurveAt_iff' : IsMIntegralCurveAt γ 
v t₀ ↔ exists ε > 0, IsMIntegralCurveOn γ v (Metric.ball t₀ ε)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.ball.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : α) (ε
 : ℝ), Metric.ball x ε = {y | dist y x < ε}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a + b - c = a - c + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsMIntegralCurveOn.comp_add`：IsMIntegralCurveOn.comp_add (hγ : IsMIntegr
alCurveOn γ v s) (dt : Real) : IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt 
in s }
-/
lemma IsMIntegralCurveAt.comp_add (hγ : IsMIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert! h.comp_add dt
  rw [Metric.ball]
  simp_rw [Metric.mem_ball, Real.dist_eq, ← sub_add, add_sub_right_comm]
/-
**isMIntegralCurveAt_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_comp_add {dt : Real} : IsMIntegralCurveAt (γ ∘ (· + dt)
) v (t₀ - dt) ↔ IsMIntegralCurveAt γ v t₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `IsMIntegralCurveAt.comp_add`：IsMIntegralCurveAt.comp_add (hγ : IsMIntegr
alCurveAt γ v t₀) (dt : Real) : IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt)
-/
lemma isMIntegralCurveAt_comp_add {dt : ℝ} :
    IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) ↔ IsMIntegralCurveAt γ v t₀ := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]
/-
**isMIntegralCurveAt_comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_comp_sub {dt : Real} : IsMIntegralCurveAt (γ ∘ (· - dt)
) v (t₀ + dt) ↔ IsMIntegralCurveAt γ v t₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `isMIntegralCurveAt_comp_add`：isMIntegralCurveAt_comp_add {dt : Real} : I
sMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) ↔ IsMIntegralCurveAt γ v t₀
-/
lemma isMIntegralCurveAt_comp_sub {dt : ℝ} :
    IsMIntegralCurveAt (γ ∘ (· - dt)) v (t₀ + dt) ↔ IsMIntegralCurveAt γ v t₀ := by
  simpa using! isMIntegralCurveAt_comp_add (dt := -dt)
/-
**IsMIntegralCurve.comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.comp_add (hγ : IsMIntegralCurve γ v) (dt : Real) : IsMInt
egralCurve (γ ∘ (· + dt)) v
参数：hγ : IsMIntegralCurve γ v；dt : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMIntegralCurve_iff_isMIntegralCurveOn`：isMIntegralCurve_iff_isMIntegra
lCurveOn : IsMIntegralCurve γ v ↔ IsMIntegralCurveOn γ v univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsMIntegralCurveOn.comp_add`：IsMIntegralCurveOn.comp_add (hγ : IsMIntegr
alCurveOn γ v s) (dt : Real) : IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt 
in s }
-/
lemma IsMIntegralCurve.comp_add (hγ : IsMIntegralCurve γ v) (dt : ℝ) :
    IsMIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  simpa using hγ.comp_add dt
/-
**isMIntegralCurve_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_comp_add {dt : Real} : IsMIntegralCurve (γ ∘ (· + dt)) v 
↔ IsMIntegralCurve γ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsMIntegralCurve.comp_add`：IsMIntegralCurve.comp_add (hγ : IsMIntegralCu
rve γ v) (dt : Real) : IsMIntegralCurve (γ ∘ (· + dt)) v
-/
lemma isMIntegralCurve_comp_add {dt : ℝ} :
    IsMIntegralCurve (γ ∘ (· + dt)) v ↔ IsMIntegralCurve γ v := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]
/-
**isMIntegralCurve_comp_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_comp_sub {dt : Real} : IsMIntegralCurve (γ ∘ (· - dt)) v 
↔ IsMIntegralCurve γ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMIntegralCurve_comp_add`：isMIntegralCurve_comp_add {dt : Real} : IsMIn
tegralCurve (γ ∘ (· + dt)) v ↔ IsMIntegralCurve γ v
-/
lemma isMIntegralCurve_comp_sub {dt : ℝ} :
    IsMIntegralCurve (γ ∘ (· - dt)) v ↔ IsMIntegralCurve γ v := by
  simpa using! isMIntegralCurve_comp_add (dt := -dt)

end Translation

/-! ### Scaling lemmas -/

section Scaling

open Manifold

/-
**IsMIntegralCurveOn.comp_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveOn.comp_mul (hγ : IsMIntegralCurveOn γ v s) (a : Real) : I
sMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a in s }
参数：hγ : IsMIntegralCurveOn γ v s；a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.smulRight_comp_smulRight`：smulRight_comp_smulRight {
M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃] [TopologicalSpace M₃] [ContinuousS
Mul R₁ M₃] (f : M₃ ->L[R₁] R₁) (g …
· 使用定理 `ContinuousLinearMap.smulRight.congr_simp`：∀ {M₁ : Type u_4} [inst : Topo
logicalSpace M₁] [inst_1 : AddCommMonoid M₁] {M₂ : Type u_6}   [inst_2 : Topolog
icalSpace M₂] [inst_3 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `HasFDerivWithinAt.mul_const'`：HasFDerivWithinAt.mul_const' (ha : HasFDer
ivWithinAt a a' s x) (b : 𝔸) : HasFDerivWithinAt (fun y => a y * b) (a' <• b) s 
x
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
lemma IsMIntegralCurveOn.comp_mul (hγ : IsMIntegralCurveOn γ v s) (a : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  intro t ht
  have : (1 : ℝ →L[ℝ] ℝ).smulRight (a • v (γ (t * a))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (v (γ (t * a))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight a := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight]
  rw [comp_apply, Pi.smul_apply, this]
  refine HasMFDerivWithinAt.comp t (hγ (t * a) ht)
    ⟨(continuous_mul_const _).continuousWithinAt, ?_⟩ subset_rfl
  simp only [mfld_simps]
  exact HasFDerivWithinAt.mul_const' (hasFDerivWithinAt_id _ _) _
/-
**isMIntegralCurveOn_comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveOn_comp_mul_ne_zero {a : Real} (ha : a != 0) : IsMIntegral
CurveOn (γ ∘ (· * a)) (a • v) { t | t * a in s } ↔ IsMIntegralCurveOn γ v s
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `IsMIntegralCurveOn.comp_mul`：IsMIntegralCurveOn.comp_mul (hγ : IsMIntegr
alCurveOn γ v s) (a : Real) : IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t *
 a in s }
-/
lemma isMIntegralCurveOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } ↔ IsMIntegralCurveOn γ v s := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_ofPred_eq, mul_assoc, inv_mul_eq_div, div_self ha, mul_one, ofPred_mem_eq]
/-
**IsMIntegralCurveAt.comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurveAt.comp_mul_ne_zero (hγ : IsMIntegralCurveAt γ v t₀) {a : 
Real} (ha : a != 0) : IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a)
参数：hγ : IsMIntegralCurveAt γ v t₀；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMIntegralCurveAt_iff'`：isMIntegralCurveAt_iff' : IsMIntegralCurveAt γ 
v t₀ ↔ exists ε > 0, IsMIntegralCurveOn γ v (Metric.ball t₀ ε)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.Positivity.abs_pos_of_ne_zero`：abs_pos_of_ne_zero {α : Type
*} [AddGroup α] [LinearOrder α] [AddLeftMono α] {a : α} : a != 0 -> 0 < |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `IsMIntegralCurveOn.comp_mul`：IsMIntegralCurveOn.comp_mul (hγ : IsMIntegr
alCurveOn γ v s) (a : Real) : IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t *
 a in s }
-/
lemma IsMIntegralCurveAt.comp_mul_ne_zero (hγ : IsMIntegralCurveAt γ v t₀) {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq,
    lt_div_iff₀ (abs_pos.mpr ha), ← abs_mul, sub_mul, div_mul_cancel₀ _ ha]
/-
**isMIntegralCurveAt_comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurveAt_comp_mul_ne_zero {a : Real} (ha : a != 0) : IsMIntegral
CurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) ↔ IsMIntegralCurveAt γ v t₀
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `IsMIntegralCurveAt.comp_mul_ne_zero`：IsMIntegralCurveAt.comp_mul_ne_zero
 (hγ : IsMIntegralCurveAt γ v t₀) {a : Real} (ha : a != 0) : IsMIntegralCurveAt 
(γ ∘ (· * a)) (a • v) (t₀…
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma isMIntegralCurveAt_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) ↔ IsMIntegralCurveAt γ v t₀ := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]
/-
**IsMIntegralCurve.comp_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMIntegralCurve.comp_mul (hγ : IsMIntegralCurve γ v) (a : Real) : IsMInte
gralCurve (γ ∘ (· * a)) (a • v)
参数：hγ : IsMIntegralCurve γ v；a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMIntegralCurve_iff_isMIntegralCurveOn`：isMIntegralCurve_iff_isMIntegra
lCurveOn : IsMIntegralCurve γ v ↔ IsMIntegralCurveOn γ v univ
· 使用引理 `IsMIntegralCurveOn.comp_mul`：IsMIntegralCurveOn.comp_mul (hγ : IsMIntegr
alCurveOn γ v s) (a : Real) : IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t *
 a in s }
-/
lemma IsMIntegralCurve.comp_mul (hγ : IsMIntegralCurve γ v) (a : ℝ) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _
/-
**isMIntegralCurve_comp_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_comp_mul_ne_zero {a : Real} (ha : a != 0) : IsMIntegralCu
rve (γ ∘ (· * a)) (a • v) ↔ IsMIntegralCurve γ v
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `IsMIntegralCurve.comp_mul`：IsMIntegralCurve.comp_mul (hγ : IsMIntegralCu
rve γ v) (a : Real) : IsMIntegralCurve (γ ∘ (· * a)) (a • v)
-/
lemma isMIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) ↔ IsMIntegralCurve γ v := by
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

open ContinuousLinearMap in
/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
is a global integral curve of `v`. -/
/-
**isMIntegralCurve_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMIntegralCurve_const {x : M} (h : v x = 0) : IsMIntegralCurve (fun _ => 
x) v
参数：h : v x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.smulRight_one_eq_toSpanSingleton`：smulRight_one_eq_t
oSpanSingleton (x : M₁) : (1 : R₁ ->L[R₁] R₁).smulRight x = toSpanSingleton R₁ x
· 使用定理 `ContinuousLinearMap.toSpanSingleton_zero`：toSpanSingleton_zero : toSpanS
ingleton R₁ (0 : M₁) = 0
· 使用定理 `hasMFDerivAt_const`：hasMFDerivAt_const (c : M') (x : M) : HasMFDerivAt% 
(fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)

--- 原说明 ---
If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
is a global integral curve of `v`.
-/
lemma isMIntegralCurve_const {x : M} (h : v x = 0) : IsMIntegralCurve (fun _ ↦ x) v := by
  intro t
  rw [h, smulRight_one_eq_toSpanSingleton, toSpanSingleton_zero]
  exact hasMFDerivAt_const ..

end Scaling

