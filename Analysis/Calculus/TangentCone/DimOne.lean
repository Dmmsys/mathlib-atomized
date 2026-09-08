/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Unique differentiability property of a set in the base field

In this file we prove that a set in the base field has the unique differentiability property at `x`
iff `x` is an accumulation point of the set, see `uniqueDiffWithinAt_iff_accPt`.
-/

public section

open Filter Metric Set
open scoped Topology

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- The tangent cone at a non-isolated point in dimension 1 is the whole space. -/
/-
**tangentConeAt_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s)) : tangentCo
neAt 𝕜 s x = univ
参数：hx : AccPt x (𝓟 s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `mem_tangentConeAt_of_frequently`：mem_tangentConeAt_of_frequently {α : Ty
pe*} (l : Filter α) (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : e
xistsᶠ n in l, x + d …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a

--- 原说明 ---
The tangent cone at a non-isolated point in dimension 1 is the whole space.
-/
theorem tangentConeAt_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s)) :
    tangentConeAt 𝕜 s x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  apply mem_tangentConeAt_of_frequently (𝓝[≠] x) (fun z ↦ y / (z - x)) (· - x)
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp) |>.mono_left inf_le_left
  · simpa [accPt_iff_frequently_nhdsNE] using hx
  · apply tendsto_nhds_of_eventually_eq
    refine eventually_mem_nhdsWithin.mono fun z hz ↦ ?_
    have : z - x ≠ 0 := by simpa [sub_eq_zero] using hz
    simp [div_mul_cancel₀ _ this]

/-- In one dimension, a point is a point of unique differentiability of a set
iff it is an accumulation point of the set. -/
/-
**uniqueDiffWithinAt_iff_accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {x : 𝕜} : UniqueDiffWithinAt 𝕜 s 
x ↔ AccPt x (𝓟 s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.accPt`：UniqueDiffWithinAt.accPt [T2Space E] [Nontrivi
al E] (h : UniqueDiffWithinAt 𝕜 s x) : AccPt x (𝓟 s)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_eq_univ`：tangentConeAt_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : A
ccPt x (𝓟 s)) : tangentConeAt 𝕜 s x = univ
· 使用定理 `Submodule.span_univ`：span_univ : span R (univ : Set M) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `AccPt.clusterPt`：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) 
: ClusterPt x F

--- 原说明 ---
In one dimension, a point is a point of unique differentiability of a set
iff it is an accumulation point of the set.
-/
theorem uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {x : 𝕜} :
    UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s) :=
  ⟨UniqueDiffWithinAt.accPt, fun h ↦
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt
