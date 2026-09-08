/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! # Metric structure on `α →ᵤ β` and `α →ᵤ[𝔖] β` for finite `𝔖`

When `β` is a (pseudo, extended) metric space it is a uniform space, and therefore we may
consider the type `α →ᵤ β` of functions equipped with the topology of uniform convergence. The
natural (pseudo, extended) metric on this space is given by `fun f g ↦ ⨆ x, edist (f x) (g x)`,
and this induces the existing uniformity. Unless `β` is a bounded space, this will not be a (pseudo)
metric space (except in the trivial case where `α` is empty).

When `𝔖 : Set (Set α)` is a collection of subsets, we may equip the space of functions with the
(pseudo, extended) metric `fun f g ↦ ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`. *However*, this only induces
the pre-existing uniformity on `α →ᵤ[𝔖] β` if `𝔖` is finite, and hence we only have an instance in
that case. Nevertheless, this still covers the most important case, such as when `𝔖` is a singleton.

Furthermore, we note that this is essentially a mathematical obstruction, not a technical one:
indeed, the uniformity of `α →ᵤ[𝔖] β` is countably generated only when there is a sequence
`t : ℕ → Finset (Set α)` such that, for each `n`, `t n ⊆ 𝔖`, `fun n ↦ Finset.sup (t n)` is monotone
and for every `s ∈ 𝔖`, there is some `n` such that `s ⊆ Finset.sup (t n)` (see
`UniformOnFun.isCountablyGenerated_uniformity`). So, while the `𝔖` for which `α →ᵤ[𝔖] β` is
metrizable include some non-finite `𝔖`, there are some `𝔖` which are not metrizable, and moreover,
it is only when `𝔖` is finite that `⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)` is a metric which induces the
uniformity.

There are a few advantages of equipping this space with this metric structure.

1. A function `f : X → α →ᵤ β` is Lipschitz in this metric if and only if for every `a : α` it is
  Lipschitz in the first variable with the same Lipschitz constant.
2. It provides a natural setting in which one can talk about the metrics on `α →ᵇ β` or, when
  `α` is compact, `C(α, β)`, relative to their underlying bare functions.
-/

public section

variable {α β γ : Type*} [PseudoEMetricSpace γ]
open scoped UniformConvergence NNReal ENNReal
open Filter Topology Uniformity

namespace UniformFun

section EMetric

variable [PseudoEMetricSpace β]

/-
**UniformFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : EDist (α →ᵤ β) where
  edist f g := ⨆ x, edist (toFun f x) (toFun g x)
/-
**UniformFun.edist_def** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：edist_def (f g : α ->ᵤ β) : edist f g = ⨆ x, edist (toFun f x) (toFun g x)
参数：f g : α ->ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_def (f g : α →ᵤ β) :
    edist f g = ⨆ x, edist (toFun f x) (toFun g x) :=
  rfl
/-
**UniformFun.edist_le** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：edist_le {f g : α ->ᵤ β} {C : Real>=0∞} : edist f g <= C ↔ forall x, edist
 (toFun f x) (toFun g x) <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
-/
lemma edist_le {f g : α →ᵤ β} {C : ℝ≥0∞} :
    edist f g ≤ C ↔ ∀ x, edist (toFun f x) (toFun g x) ≤ C :=
  iSup_le_iff

/-- The natural `EMetric` structure on `α →ᵤ β` given by `edist f g = ⨆ x, edist (f x) (g x)`. -/
/-
**UniformFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `EMetric` structure on `α →ᵤ β` given by `edist f g = ⨆ x, edist (f 
x) (g x)`.
-/
noncomputable instance : PseudoEMetricSpace (α →ᵤ β) where
  edist_self := by simp [edist_def]
  edist_comm := by simp [edist_def, edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x, edist (f₁ x) (f₃ x) ≤ ⨆ x, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup_mono fun _ ↦ edist_triangle _ _ _
    _ ≤ (⨆ x, edist (f₁ x) (f₂ x)) + (⨆ x, edist (f₂ x) (f₃ x)) := iSup_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    suffices 𝓤 (α →ᵤ β) = comap (fun x ↦ edist x.1 x.2) (𝓝 0) by
      simp [this, ENNReal.nhds_zero_basis.comap _ |>.eq_biInf, Set.Iio]
    rw [ENNReal.nhds_zero_basis_Iic.comap _ |>.eq_biInf]
    rw [UniformFun.hasBasis_uniformity_of_basis α β uniformity_basis_edist_le |>.eq_biInf]
    simp [UniformFun.gen, edist_le, Set.Iic]
/-
**UniformFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {β : Type*} [EMetricSpace β] : EMetricSpace (α →ᵤ β) :=
  .ofT0PseudoEMetricSpace _
/-
**UniformFun.lipschitzWith_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：lipschitzWith_iff {f : γ -> α ->ᵤ β} {K : Real>=0} : LipschitzWith K f ↔ f
orall c, LipschitzWith K (fun x => toFun (f x) c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lipschitzWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c, LipschitzWith K (fun x ↦ toFun (f x) c) := by
  simp [LipschitzWith, edist_le, forall_comm (α := α)]
/-
**UniformFun.lipschitzWith_ofFun_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：lipschitzWith_ofFun_iff {f : γ -> α -> β} {K : Real>=0} : LipschitzWith K 
(fun x => ofFun (f x)) ↔ forall c, LipschitzWith K (f · c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformFun.lipschitzWith_iff`：lipschitzWith_iff {f : γ -> α ->ᵤ β} {K : 
Real>=0} : LipschitzWith K f ↔ forall c, LipschitzWith K (fun x => toFun (f x) c
)
-/
lemma lipschitzWith_ofFun_iff {f : γ → α → β} {K : ℝ≥0} :
    LipschitzWith K (fun x ↦ ofFun (f x)) ↔ ∀ c, LipschitzWith K (f · c) :=
  lipschitzWith_iff

/-- If `f : α → γ → β` is a family of a functions, all of which are Lipschitz with the
same constant, then the family is uniformly equicontinuous. -/
/-
**UniformFun._root_.LipschitzWith.uniformEquicontinuous** 是 Mathlib 中的一个引理，位于命名空
间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → γ → β` is a family of a functions, all of which are Lipschitz with t
he
same constant, then the family is uniformly equicontinuous.
-/
lemma _root_.LipschitzWith.uniformEquicontinuous (f : α → γ → β) (K : ℝ≥0)
    (h : ∀ c, LipschitzWith K (f c)) : UniformEquicontinuous f := by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [← lipschitzWith_ofFun_iff] at h
  exact h.uniformContinuous
/-
**UniformFun.lipschitzOnWith_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：lipschitzOnWith_iff {f : γ -> α ->ᵤ β} {K : Real>=0} {s : Set γ} : Lipschi
tzOnWith K f s ↔ forall c, LipschitzOnWith K (fun x => toFun (f x) c) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lipschitzOnWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c, LipschitzOnWith K (fun x ↦ toFun (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl
/-
**UniformFun.lipschitzOnWith_ofFun_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：lipschitzOnWith_ofFun_iff {f : γ -> α -> β} {K : Real>=0} {s : Set γ} : Li
pschitzOnWith K (fun x => ofFun (f x)) s ↔ forall c, LipschitzOnWith K (f · c) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformFun.lipschitzOnWith_iff`：lipschitzOnWith_iff {f : γ -> α ->ᵤ β} {
K : Real>=0} {s : Set γ} : LipschitzOnWith K f s ↔ forall c, LipschitzOnWith K (
fun x => toFun (f x)…
-/
lemma lipschitzOnWith_ofFun_iff {f : γ → α → β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K (fun x ↦ ofFun (f x)) s ↔ ∀ c, LipschitzOnWith K (f · c) s :=
  lipschitzOnWith_iff

/-- If `f : α → γ → β` is a family of a functions, all of which are Lipschitz on `s` with the
same constant, then the family is uniformly equicontinuous on `s`. -/
/-
**UniformFun._root_.LipschitzOnWith.uniformEquicontinuousOn** 是 Mathlib 中的一个引理，位
于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → γ → β` is a family of a functions, all of which are Lipschitz on `s`
 with the
same constant, then the family is uniformly equicontinuous on `s`.
-/
lemma _root_.LipschitzOnWith.uniformEquicontinuousOn (f : α → γ → β) (K : ℝ≥0) {s : Set γ}
    (h : ∀ c, LipschitzOnWith K (f c) s) : UniformEquicontinuousOn f s := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  rw [← lipschitzOnWith_ofFun_iff] at h
  exact h.uniformContinuousOn
/-
**UniformFun.edist_eval_le** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：edist_eval_le {f g : α ->ᵤ β} {x : α} : edist (toFun f x) (toFun g x) <= e
dist f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `UniformFun.edist_le`：edist_le {f g : α ->ᵤ β} {C : Real>=0∞} : edist f g
 <= C ↔ forall x, edist (toFun f x) (toFun g x) <= C
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma edist_eval_le {f g : α →ᵤ β} {x : α} :
    edist (toFun f x) (toFun g x) ≤ edist f g :=
  edist_le.mp le_rfl x
/-
**UniformFun.lipschitzWith_eval** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：lipschitzWith_eval (x : α) : LipschitzWith 1 (fun f : α ->ᵤ β => toFun f x
)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `UniformFun.edist_eval_le`：edist_eval_le {f g : α ->ᵤ β} {x : α} : edist 
(toFun f x) (toFun g x) <= edist f g
-/
lemma lipschitzWith_eval (x : α) :
    LipschitzWith 1 (fun f : α →ᵤ β ↦ toFun f x) := by
  intro f g
  simpa using edist_eval_le

end EMetric

section Metric

variable [PseudoMetricSpace β]

/-
**UniformFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α →ᵤ β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ ↦ Real.iSup_nonneg fun i ↦ dist_nonneg)
    fun f g ↦ by
      cases isEmpty_or_nonempty α
      · simp [edist_def]
      have : BddAbove <| .range fun x ↦ dist (toFun f x) (toFun g x) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      exact ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ by simp [edist_def, ciSup_le_iff this]
/-
**UniformFun.dist_def** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：dist_def [BoundedSpace β] (f g : α ->ᵤ β) : dist f g = ⨆ x, dist (toFun f 
x) (toFun g x)
参数：f g : α ->ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_def [BoundedSpace β] (f g : α →ᵤ β) :
    dist f g = ⨆ x, dist (toFun f x) (toFun g x) :=
  rfl
/-
**UniformFun.dist_le** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：dist_le [BoundedSpace β] {f g : α ->ᵤ β} {C : Real} (hC : 0 <= C) : dist f
 g <= C ↔ forall x, dist (toFun f x) (toFun g x) <= C
参数：hC : 0 <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dist_le [BoundedSpace β] {f g : α →ᵤ β} {C : ℝ} (hC : 0 ≤ C) :
    dist f g ≤ C ↔ ∀ x, dist (toFun f x) (toFun g x) ≤ C := by
  simp_rw [dist_edist, ← ENNReal.le_ofReal_iff_toReal_le (edist_ne_top _ _) hC, edist_le]
/-
**UniformFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [BoundedSpace β] : BoundedSpace (α →ᵤ β) where
  bounded_univ := by
    rw [Metric.isBounded_iff_ediam_ne_top, ← lt_top_iff_ne_top]
    refine lt_of_le_of_lt ?_ <| BoundedSpace.bounded_univ (α := β) |>.ediam_ne_top.lt_top
    simp only [Metric.ediam_le_iff, Set.mem_univ, edist_le, forall_const]
    exact fun f g x ↦ Metric.edist_le_ediam_of_mem (Set.mem_univ _) (Set.mem_univ _)
/-
**UniformFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {β : Type*} [MetricSpace β] [BoundedSpace β] : MetricSpace (α →ᵤ β) :=
  .ofT0PseudoMetricSpace _

open BoundedContinuousFunction in
/-
**UniformFun.isometry_ofFun_boundedContinuousFunction** 是 Mathlib 中的一个引理，位于命名空间 
`UniformFun`。
形式化陈述：isometry_ofFun_boundedContinuousFunction [TopologicalSpace α] : Isometry (
ofFun ∘ DFunLike.coe : (α ->ᵇ β) -> α ->ᵤ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.edist_eq_iSup`：edist_eq_iSup : edist f g = ⨆ x
, edist (f x) (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isometry_ofFun_boundedContinuousFunction [TopologicalSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : (α →ᵇ β) → α →ᵤ β) := by
  simp [Isometry, edist_def, edist_eq_iSup]
/-
**UniformFun.isometry_ofFun_continuousMap** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`
。
形式化陈述：isometry_ofFun_continuousMap [TopologicalSpace α] [CompactSpace α] : Isome
try (ofFun ∘ DFunLike.coe : C(α, β) -> α ->ᵤ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用引理 `UniformFun.isometry_ofFun_boundedContinuousFunction`：isometry_ofFun_boun
dedContinuousFunction [TopologicalSpace α] : Isometry (ofFun ∘ DFunLike.coe : (α
 ->ᵇ β) -> α ->ᵤ β)
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
lemma isometry_ofFun_continuousMap [TopologicalSpace α] [CompactSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : C(α, β) → α →ᵤ β) :=
  isometry_ofFun_boundedContinuousFunction.comp <|
    ContinuousMap.isometryEquivBoundedOfCompact α β |>.isometry
/-
**UniformFun.edist_continuousMapMk** 是 Mathlib 中的一个引理，位于命名空间 `UniformFun`。
形式化陈述：edist_continuousMapMk [TopologicalSpace α] [CompactSpace α] {f g : α ->ᵤ β
} (hf : Continuous (toFun f)) (hg : Continuous (toFun g)) : edist (⟨_, hf⟩ : C(α
, β)) ⟨_, hg⟩ = edist f g
参数：hf : Continuous (toFun f)；hg : Continuous (toFun g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用引理 `UniformFun.isometry_ofFun_continuousMap`：isometry_ofFun_continuousMap [T
opologicalSpace α] [CompactSpace α] : Isometry (ofFun ∘ DFunLike.coe : C(α, β) -
> α ->ᵤ β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_continuousMapMk [TopologicalSpace α] [CompactSpace α]
    {f g : α →ᵤ β} (hf : Continuous (toFun f)) (hg : Continuous (toFun g)) :
    edist (⟨_, hf⟩ : C(α, β)) ⟨_, hg⟩ = edist f g := by
  simp [← isometry_ofFun_continuousMap.edist_eq]

end Metric

end UniformFun

namespace UniformOnFun

variable {𝔖 𝔗 : Set (Set α)}

section EMetric

variable [PseudoEMetricSpace β]

/-- Let `f : γ → α →ᵤ[𝔖] β`. If for every `s ∈ 𝔖` and for every `c ∈ s`, the function
`fun x ↦ f x c` is Lipschitz (with Lipschitz constant depending on `s`), then `f` is continuous. -/
/-
**UniformOnFun.continuous_of_forall_lipschitzWith** 是 Mathlib 中的一个引理，位于命名空间 `Uni
formOnFun`。
形式化陈述：continuous_of_forall_lipschitzWith {f : γ -> α ->ᵤ[𝔖] β} (K : Set α -> Rea
l>=0) (h : forall s in 𝔖, forall c in s, LipschitzWith (K s) (fun x => toFun 𝔖 (
f x) c)) : Continuous f
参数：K : Set α -> Real>=0；h : forall s in 𝔖, forall c in s, LipschitzWith (K s) (f
un x => toFun 𝔖 (f x) c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformOnFun.continuous_rng_iff`：∀ {α : Type u_1} {β : Type u_2} [inst :
 UniformSpace β] {𝔖 : Set (Set α)} {X : Type u_5} [inst_1 : TopologicalSpace X] 
  {f : X → UniformOnF…
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用引理 `UniformFun.lipschitzWith_iff`：lipschitzWith_iff {f : γ -> α ->ᵤ β} {K : 
Real>=0} : LipschitzWith K f ↔ forall c, LipschitzWith K (fun x => toFun (f x) c
)

--- 原说明 ---
Let `f : γ → α →ᵤ[𝔖] β`. If for every `s ∈ 𝔖` and for every `c ∈ s`, the functio
n
`fun x ↦ f x c` is Lipschitz (with Lipschitz constant depending on `s`), then `f
` is continuous.
-/
lemma continuous_of_forall_lipschitzWith {f : γ → α →ᵤ[𝔖] β} (K : Set α → ℝ≥0)
    (h : ∀ s ∈ 𝔖, ∀ c ∈ s, LipschitzWith (K s) (fun x ↦ toFun 𝔖 (f x) c)) :
    Continuous f := by
  rw [UniformOnFun.continuous_rng_iff]
  refine fun s hs ↦ LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

@[nolint unusedArguments]
/-
**UniformOnFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformOnFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Finite 𝔖] : EDist (α →ᵤ[𝔖] β) where
  edist f g := ⨆ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x)
/-
**UniformOnFun.edist_def** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：edist_def [Finite 𝔖] (f g : α ->ᵤ[𝔖] β) : edist f g = ⨆ x in ⋃₀ 𝔖, edist (
toFun 𝔖 f x) (toFun 𝔖 g x)
参数：f g : α ->ᵤ[𝔖] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_def [Finite 𝔖] (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) :=
  rfl
/-
**UniformOnFun.edist_def'** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：edist_def' [Finite 𝔖] (f g : α ->ᵤ[𝔖] β) : edist f g = ⨆ s in 𝔖, ⨆ x in s,
 edist (toFun 𝔖 f x) (toFun 𝔖 g x)
参数：f g : α ->ᵤ[𝔖] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_def' [Finite 𝔖] (f g : α →ᵤ[𝔖] β) :
    edist f g = ⨆ s ∈ 𝔖, ⨆ x ∈ s, edist (toFun 𝔖 f x) (toFun 𝔖 g x) := by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]
/-
**UniformOnFun.edist_eq_restrict_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`
。
形式化陈述：edist_eq_restrict_sUnion [Finite 𝔖] {f g : α ->ᵤ[𝔖] β} : edist f g = edist
 (UniformFun.ofFun ((⋃₀ 𝔖).domRestrict (toFun 𝔖 f))) (UniformFun.ofFun ((⋃₀ 𝔖).d
omRestrict (toFun 𝔖 g)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
-/
lemma edist_eq_restrict_sUnion [Finite 𝔖] {f g : α →ᵤ[𝔖] β} :
    edist f g = edist
      (UniformFun.ofFun ((⋃₀ 𝔖).domRestrict (toFun 𝔖 f)))
      (UniformFun.ofFun ((⋃₀ 𝔖).domRestrict (toFun 𝔖 g))) :=
  iSup_subtype'
/-
**UniformOnFun.edist_eq_pi_restrict** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：edist_eq_pi_restrict [Fintype 𝔖] {f g : α ->ᵤ[𝔖] β} : edist f g = edist (f
un s : 𝔖 => UniformFun.ofFun ((s : Set α).domRestrict (toFun 𝔖 f))) (fun s : 𝔖 =
> UniformFun.ofFun ((s : Set α).domRestrict (toFun 𝔖 g)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UniformOnFun.edist_def'`：edist_def' [Finite 𝔖] (f g : α ->ᵤ[𝔖] β) : edis
t f g = ⨆ s in 𝔖, ⨆ x in s, edist (toFun 𝔖 f x) (toFun 𝔖 g x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Finset.sup_univ_eq_iSup`：sup_univ_eq_iSup [CompleteLattice β] (f : α -> 
β) : Finset.univ.sup f = iSup f
-/
lemma edist_eq_pi_restrict [Fintype 𝔖] {f g : α →ᵤ[𝔖] β} :
    edist f g = edist
      (fun s : 𝔖 ↦ UniformFun.ofFun ((s : Set α).domRestrict (toFun 𝔖 f)))
      (fun s : 𝔖 ↦ UniformFun.ofFun ((s : Set α).domRestrict (toFun 𝔖 g))) := by
  simp_rw [edist_def', iSup_subtype', edist_pi_def, Finset.sup_univ_eq_iSup]
  rfl

variable [Finite 𝔖]

/-- The natural `EMetric` structure on `α →ᵤ[𝔖] β` when `𝔖` is finite given by
`edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`. -/
/-
**UniformOnFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformOnFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `EMetric` structure on `α →ᵤ[𝔖] β` when `𝔖` is finite given by
`edist f g = ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`.
-/
noncomputable instance : PseudoEMetricSpace (α →ᵤ[𝔖] β) where
  edist_self f := by simp [edist_eq_restrict_sUnion]
  edist_comm := by simp [edist_eq_restrict_sUnion, edist_comm]
  edist_triangle f₁ f₂ f₃ := by simp [edist_eq_restrict_sUnion, edist_triangle]
  toUniformSpace := inferInstance
  uniformity_edist := by
    let _ := Fintype.ofFinite 𝔖;
    simp_rw [← isUniformInducing_pi_restrict.comap_uniformity,
      PseudoEMetricSpace.uniformity_edist, comap_iInf, comap_principal, edist_eq_pi_restrict,
      Set.preimage_ofPred_eq]
/-
**UniformOnFun.edist_le** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：edist_le {f g : α ->ᵤ[𝔖] β} {C : Real>=0∞} : edist f g <= C ↔ forall x in 
⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma edist_le {f g : α →ᵤ[𝔖] β} {C : ℝ≥0∞} :
    edist f g ≤ C ↔ ∀ x ∈ ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) ≤ C := by
  simp_rw [edist_def, iSup₂_le_iff]
/-
**UniformOnFun.lipschitzWith_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：lipschitzWith_iff {f : γ -> α ->ᵤ[𝔖] β} {K : Real>=0} : LipschitzWith K f 
↔ forall c in ⋃₀ 𝔖, LipschitzWith K (fun x => toFun 𝔖 (f x) c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma lipschitzWith_iff {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzWith K (fun x ↦ toFun 𝔖 (f x) c) := by
  simp [LipschitzWith, edist_le]
  tauto
/-
**UniformOnFun.lipschitzOnWith_iff** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：lipschitzOnWith_iff {f : γ -> α ->ᵤ[𝔖] β} {K : Real>=0} {s : Set γ} : Lips
chitzOnWith K f s ↔ forall c in ⋃₀ 𝔖, LipschitzOnWith K (fun x => toFun 𝔖 (f x) 
c) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lipschitzOnWith_iff {f : γ → α →ᵤ[𝔖] β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c ∈ ⋃₀ 𝔖, LipschitzOnWith K (fun x ↦ toFun 𝔖 (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl
/-
**UniformOnFun.edist_eval_le** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：edist_eval_le {f g : α ->ᵤ[𝔖] β} {x : α} (hx : x in ⋃₀ 𝔖) : edist (toFun 𝔖
 f x) (toFun 𝔖 g x) <= edist f g
参数：hx : x in ⋃₀ 𝔖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `UniformOnFun.edist_le`：edist_le {f g : α ->ᵤ[𝔖] β} {C : Real>=0∞} : edis
t f g <= C ↔ forall x in ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) <= C
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma edist_eval_le {f g : α →ᵤ[𝔖] β} {x : α} (hx : x ∈ ⋃₀ 𝔖) :
    edist (toFun 𝔖 f x) (toFun 𝔖 g x) ≤ edist f g :=
  edist_le.mp le_rfl x hx
/-
**UniformOnFun.lipschitzWith_eval** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：lipschitzWith_eval {x : α} (hx : x in ⋃₀ 𝔖) : LipschitzWith 1 (fun f : α -
>ᵤ[𝔖] β => toFun 𝔖 f x)
参数：hx : x in ⋃₀ 𝔖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `UniformOnFun.edist_eval_le`：edist_eval_le {f g : α ->ᵤ[𝔖] β} {x : α} (hx
 : x in ⋃₀ 𝔖) : edist (toFun 𝔖 f x) (toFun 𝔖 g x) <= edist f g
-/
lemma lipschitzWith_eval {x : α} (hx : x ∈ ⋃₀ 𝔖) :
    LipschitzWith 1 (fun f : α →ᵤ[𝔖] β ↦ toFun 𝔖 f x) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using edist_eval_le hx
/-
**UniformOnFun.lipschitzWith_one_ofFun_toFun** 是 Mathlib 中的一个引理，位于命名空间 `UniformO
nFun`。
形式化陈述：lipschitzWith_one_ofFun_toFun : LipschitzWith 1 (ofFun 𝔖 ∘ UniformFun.toFu
n : (α ->ᵤ β) -> (α ->ᵤ[𝔖] β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `UniformOnFun.lipschitzWith_iff`：lipschitzWith_iff {f : γ -> α ->ᵤ[𝔖] β} 
{K : Real>=0} : LipschitzWith K f ↔ forall c in ⋃₀ 𝔖, LipschitzWith K (fun x => 
toFun 𝔖 (f x) c)
· 使用引理 `UniformFun.lipschitzWith_eval`：lipschitzWith_eval (x : α) : LipschitzWit
h 1 (fun f : α ->ᵤ β => toFun f x)
-/
lemma lipschitzWith_one_ofFun_toFun :
    LipschitzWith 1 (ofFun 𝔖 ∘ UniformFun.toFun : (α →ᵤ β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _ _ ↦ UniformFun.lipschitzWith_eval _
/-
**UniformOnFun.lipschitzWith_one_ofFun_toFun'** 是 Mathlib 中的一个引理，位于命名空间 `Uniform
OnFun`。
形式化陈述：lipschitzWith_one_ofFun_toFun' [Finite 𝔗] (h : ⋃₀ 𝔖 subseteq ⋃₀ 𝔗) : Lipsc
hitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (α ->ᵤ[𝔗] β) -> (α ->ᵤ[𝔖] β))
参数：h : ⋃₀ 𝔖 subseteq ⋃₀ 𝔗。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `UniformOnFun.lipschitzWith_iff`：lipschitzWith_iff {f : γ -> α ->ᵤ[𝔖] β} 
{K : Real>=0} : LipschitzWith K f ↔ forall c in ⋃₀ 𝔖, LipschitzWith K (fun x => 
toFun 𝔖 (f x) c)
· 使用引理 `UniformOnFun.lipschitzWith_eval`：lipschitzWith_eval {x : α} (hx : x in ⋃
₀ 𝔖) : LipschitzWith 1 (fun f : α ->ᵤ[𝔖] β => toFun 𝔖 f x)
-/
lemma lipschitzWith_one_ofFun_toFun' [Finite 𝔗] (h : ⋃₀ 𝔖 ⊆ ⋃₀ 𝔗) :
    LipschitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (α →ᵤ[𝔗] β) → (α →ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _x hx ↦ lipschitzWith_eval (h hx)
/-
**UniformOnFun.lipschitzWith_restrict** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：lipschitzWith_restrict (s : Set α) (hs : s in 𝔖) : LipschitzWith 1 (Unifor
mFun.ofFun ∘ s.domRestrict ∘ toFun 𝔖 : (α ->ᵤ[𝔖] β) -> (s ->ᵤ β))
参数：s : Set α；hs : s in 𝔖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `UniformFun.lipschitzWith_iff`：lipschitzWith_iff {f : γ -> α ->ᵤ β} {K : 
Real>=0} : LipschitzWith K f ↔ forall c, LipschitzWith K (fun x => toFun (f x) c
)
· 使用引理 `UniformOnFun.lipschitzWith_eval`：lipschitzWith_eval {x : α} (hx : x in ⋃
₀ 𝔖) : LipschitzWith 1 (fun f : α ->ᵤ[𝔖] β => toFun 𝔖 f x)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma lipschitzWith_restrict (s : Set α) (hs : s ∈ 𝔖) :
    LipschitzWith 1 (UniformFun.ofFun ∘ s.domRestrict ∘ toFun 𝔖 : (α →ᵤ[𝔖] β) → (s →ᵤ β)) :=
  UniformFun.lipschitzWith_iff.mpr fun x ↦ lipschitzWith_eval ⟨s, hs, x.2⟩
/-
**UniformOnFun.isometry_restrict** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`。
形式化陈述：isometry_restrict (s : Set α) : Isometry (UniformFun.ofFun ∘ s.domRestrict
 ∘ toFun {s} : (α ->ᵤ[{s}] β) -> (s ->ᵤ β))
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isometry_restrict (s : Set α) :
    Isometry (UniformFun.ofFun ∘ s.domRestrict ∘ toFun {s} : (α →ᵤ[{s}] β) → (s →ᵤ β)) := by
  simp [Isometry, edist_def, UniformFun.edist_def, iSup_subtype]

end EMetric

section Metric

variable [Finite 𝔖] [PseudoMetricSpace β]

/-
**UniformOnFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformOnFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α →ᵤ[𝔖] β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ ⨆ x : ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ ↦ Real.iSup_nonneg fun i ↦ dist_nonneg)
    fun f g ↦ by
      cases isEmpty_or_nonempty (⋃₀ 𝔖)
      · simp_all [edist_def]
      have : BddAbove (.range fun x : ⋃₀ 𝔖 ↦ dist (toFun 𝔖 f x) (toFun 𝔖 g x)) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
      simp [edist_def, ciSup_le_iff this]
/-
**UniformOnFun.** 是 Mathlib 中的一个实例，位于命名空间 `UniformOnFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [BoundedSpace β] : BoundedSpace (α →ᵤ[𝔖] β) where
  bounded_univ := by
    convert! lipschitzWith_one_ofFun_toFun (𝔖 := 𝔖) (β := β) |>.isBounded_image (.all Set.univ)
    ext f
    simp only [Set.mem_univ, Function.comp_apply, Set.image_univ, Set.mem_range, true_iff]
    exact ⟨UniformFun.ofFun (toFun 𝔖 f), by simp⟩
/-
**UniformOnFun.edist_continuousRestrict** 是 Mathlib 中的一个引理，位于命名空间 `UniformOnFun`
。
形式化陈述：edist_continuousRestrict [TopologicalSpace α] {f g : α ->ᵤ[𝔖] β} [CompactS
pace (⋃₀ 𝔖)] (hf : ContinuousOn (toFun 𝔖 f) (⋃₀ 𝔖)) (hg : ContinuousOn (toFun 𝔖 
g) (⋃₀ 𝔖)) : edist (⟨_, hf.domRestrict⟩ : C(⋃₀ 𝔖, β)) ⟨_, hg.domRestrict⟩ = edis
t f g
参数：⋃₀ 𝔖；hf : ContinuousOn (toFun 𝔖 f) (⋃₀ 𝔖)；hg : ContinuousOn (toFun 𝔖 g) (⋃₀ 𝔖
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.edist_eq_iSup`：edist_eq_iSup : edist f g = ⨆ (x : α), edis
t (f x) (g x)
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_continuousRestrict [TopologicalSpace α] {f g : α →ᵤ[𝔖] β}
    [CompactSpace (⋃₀ 𝔖)] (hf : ContinuousOn (toFun 𝔖 f) (⋃₀ 𝔖))
    (hg : ContinuousOn (toFun 𝔖 g) (⋃₀ 𝔖)) :
    edist (⟨_, hf.domRestrict⟩ : C(⋃₀ 𝔖, β)) ⟨_, hg.domRestrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]
/-
**UniformOnFun.edist_continuousRestrict_of_singleton** 是 Mathlib 中的一个引理，位于命名空间 `
UniformOnFun`。
形式化陈述：edist_continuousRestrict_of_singleton [TopologicalSpace α] {s : Set α} {f 
g : α ->ᵤ[{s}] β} [CompactSpace s] (hf : ContinuousOn (toFun {s} f) s) (hg : Con
tinuousOn (toFun {s} g) s) : edist (⟨_, hf.domRestrict⟩ : C(s, β)) ⟨_, hg.domRes
trict⟩ = edist f g
参数：hf : ContinuousOn (toFun {s} f) s；hg : ContinuousOn (toFun {s} g) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.edist_eq_iSup`：edist_eq_iSup : edist f g = ⨆ (x : α), edis
t (f x) (g x)
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_continuousRestrict_of_singleton [TopologicalSpace α] {s : Set α}
    {f g : α →ᵤ[{s}] β} [CompactSpace s] (hf : ContinuousOn (toFun {s} f) s)
    (hg : ContinuousOn (toFun {s} g) s) :
    edist (⟨_, hf.domRestrict⟩ : C(s, β)) ⟨_, hg.domRestrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

end Metric

end UniformOnFun

