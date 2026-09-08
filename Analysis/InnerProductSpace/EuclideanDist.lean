/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Euclidean distance on a finite-dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `toEuclidean` to be
an equivalence between a finite-dimensional topological vector space and the standard Euclidean
space of the same dimension.
Then we define `Euclidean.dist x y = dist (toEuclidean x) (toEuclidean y)` and
provide some definitions (`Euclidean.ball`, `Euclidean.closedBall`) and simple lemmas about this
distance. This way we hide the usage of `toEuclidean` behind an API.
-/

@[expose] public section


open scoped Topology

open Set

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable section

open Module

/-- If `E` is a finite-dimensional space over `ℝ`, then `toEuclidean` is a continuous `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension. -/
/-
**toEuclidean** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toEuclidean : E ≃L[Real] EuclideanSpace Real (Fin <| finrank Real E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a finite-dimensional space over `ℝ`, then `toEuclidean` is a continuou
s `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension.
-/
def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin <| finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

namespace Euclidean

/-- If `x` and `y` are two points in a finite-dimensional space over `ℝ`, then `Euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
nonrec def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)

/-- Closed ball w.r.t. the Euclidean distance. -/
/-
**Euclidean.closedBall** 是 Mathlib 中的一个定义，位于命名空间 `Euclidean`。
形式化陈述：closedBall (x : E) (r : Real) : Set E
参数：x : E；r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Closed ball w.r.t. the Euclidean distance.
-/
def closedBall (x : E) (r : ℝ) : Set E :=
  {y | dist y x ≤ r}

/-- Open ball w.r.t. the Euclidean distance. -/
/-
**Euclidean.ball** 是 Mathlib 中的一个定义，位于命名空间 `Euclidean`。
形式化陈述：ball (x : E) (r : Real) : Set E
参数：x : E；r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open ball w.r.t. the Euclidean distance.
-/
def ball (x : E) (r : ℝ) : Set E :=
  {y | dist y x < r}
/-
**Euclidean.ball_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：ball_eq_preimage (x : E) (r : Real) : ball x r = toEuclidean ⁻¹' Metric.ba
ll (toEuclidean x) r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ball_eq_preimage (x : E) (r : ℝ) :
    ball x r = toEuclidean ⁻¹' Metric.ball (toEuclidean x) r :=
  rfl
/-
**Euclidean.closedBall_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：closedBall_eq_preimage (x : E) (r : Real) : closedBall x r = toEuclidean ⁻
¹' Metric.closedBall (toEuclidean x) r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem closedBall_eq_preimage (x : E) (r : ℝ) :
    closedBall x r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean x) r :=
  rfl
/-
**Euclidean.ball_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：ball_subset_closedBall {x : E} {r : Real} : ball x r subseteq closedBall x
 r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ball_subset_closedBall {x : E} {r : ℝ} : ball x r ⊆ closedBall x r := fun _ (hy : _ < r) =>
  le_of_lt hy
/-
**Euclidean.isOpen_ball** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : TopologicalSpace E] [in
st_2 : IsTopologicalAddGroup E]   [inst_3 : T2Space E] [inst_4 : _root_.Module ℝ
 E] [inst_5 : ContinuousSMul ℝ E] [inst_6 : FiniteDimensional ℝ E]   {x : E} {r 
: ℝ}, IsOpen (Euclidean.ball x r)
参数：Euclidean.ball x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
-/
@[simp] theorem isOpen_ball {x : E} {r : ℝ} : IsOpen (ball x r) :=
  Metric.isOpen_ball.preimage toEuclidean.continuous
/-
**Euclidean.mem_ball_self** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：mem_ball_self {x : E} {r : Real} (hr : 0 < r) : x in ball x r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ ball x r :=
  Metric.mem_ball_self hr
/-
**Euclidean.closedBall_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：closedBall_eq_image (x : E) (r : Real) : closedBall x r = toEuclidean.symm
 '' Metric.closedBall (toEuclidean x) r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.image_symm_eq_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `Euclidean.closedBall_eq_preimage`：closedBall_eq_preimage (x : E) (r : Re
al) : closedBall x r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean x) r
-/
theorem closedBall_eq_image (x : E) (r : ℝ) :
    closedBall x r = toEuclidean.symm '' Metric.closedBall (toEuclidean x) r := by
  rw [toEuclidean.image_symm_eq_preimage, closedBall_eq_preimage]

nonrec theorem isCompact_closedBall {x : E} {r : ℝ} : IsCompact (closedBall x r) := by
  rw [closedBall_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous
/-
**Euclidean.isClosed_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：isClosed_closedBall {x : E} {r : Real} : IsClosed (closedBall x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Euclidean.isCompact_closedBall`：∀ {E : Type u_1} [inst : AddCommGroup E]
 [inst_1 : TopologicalSpace E] [inst_2 : IsTopologicalAddGroup E]   [inst_3 : T2
Space E] [inst_4 : _…
-/
theorem isClosed_closedBall {x : E} {r : ℝ} : IsClosed (closedBall x r) :=
  isCompact_closedBall.isClosed

nonrec theorem closure_ball (x : E) {r : ℝ} (h : r ≠ 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage, ← toEuclidean.preimage_closure, closure_ball (toEuclidean x) h,
    closedBall_eq_preimage]

nonrec theorem exists_pos_lt_subset_ball {R : ℝ} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s)
    (h : s ⊆ ball x R) : ∃ r ∈ Ioo 0 R, s ⊆ ball x r := by
  rw [ball_eq_preimage, ← image_subset_iff] at h
  rcases exists_pos_lt_subset_ball hR (toEuclidean.isClosed_image.2 hs) h with ⟨r, hr, hsr⟩
  exact ⟨r, hr, image_subset_iff.1 hsr⟩
/-
**Euclidean.nhds_basis_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：nhds_basis_closedBall {x : E} : (𝓝 x).HasBasis (fun r : Real => 0 < r) (cl
osedBall x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.nhds_eq_comap`：nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = com
ap h (𝓝 (h x))
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
-/
theorem nhds_basis_closedBall {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (closedBall x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_closedBall.comap _
/-
**Euclidean.closedBall_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：closedBall_mem_nhds {x : E} {r : Real} (hr : 0 < r) : closedBall x r in 𝓝 
x
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Euclidean.nhds_basis_closedBall`：nhds_basis_closedBall {x : E} : (𝓝 x).H
asBasis (fun r : Real => 0 < r) (closedBall x)
-/
theorem closedBall_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : closedBall x r ∈ 𝓝 x :=
  nhds_basis_closedBall.mem_of_mem hr
/-
**Euclidean.nhds_basis_ball** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : Real => 0 < r) (ball x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.nhds_eq_comap`：nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = com
ap h (𝓝 (h x))
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
theorem nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (ball x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_ball.comap _
/-
**Euclidean.ball_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean`。
形式化陈述：ball_mem_nhds {x : E} {r : Real} (hr : 0 < r) : ball x r in 𝓝 x
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Euclidean.nhds_basis_ball`：nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun
 r : Real => 0 < r) (ball x)
-/
theorem ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ball x r ∈ 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr

end Euclidean

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [NormedAddCommGroup G]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f g : F → G} {n : ℕ∞}

/-
**ContDiff.euclidean_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.euclidean_dist (hf : ContDiff Real n f) (hg : ContDiff Real n g) 
(h : forall x, f x != g x) : ContDiff Real n fun x => Euclidean.dist (f x) (g x)
参数：hf : ContDiff Real n f；hg : ContDiff Real n g；h : forall x, f x != g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContDiff.dist`：ContDiff.dist (hf : ContDiff Real n f) (hg : ContDiff Rea
l n g) (hne : forall x, f x != g x) : ContDiff Real n fun y => dist (f y) (g y)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `ContinuousLinearEquiv.injective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
-/
theorem ContDiff.euclidean_dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun x => Euclidean.dist (f x) (g x) := by
  simp only [Euclidean.dist]
  apply ContDiff.dist ℝ
  exacts [(toEuclidean (E := G)).contDiff.comp hf,
    (toEuclidean (E := G)).contDiff.comp hg, fun x => toEuclidean.injective.ne (h x)]
