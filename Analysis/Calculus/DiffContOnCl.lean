/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Functions differentiable on a domain and continuous on its closure

Many theorems in complex analysis assume that a function is complex differentiable on a domain and
is continuous on its closure. In this file we define a predicate `DiffContOnCl` that expresses
this property and prove basic facts about this predicate.
-/

public section


open Set Filter Metric

open scoped Topology

variable (𝕜 : Type*) {E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f g : E → F} {s t : Set E} {x : E}

/-- A predicate saying that a function is differentiable on a set and is continuous on its
closure. This is a common assumption in complex analysis. -/
/-
**DiffContOnCl** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedAddCommGroup F] → [NormedSpace 𝕜 E] → [NormedSpace 𝕜 F] → (E → F) 
→ Set E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate saying that a function is differentiable on a set and is continuous 
on its
closure. This is a common assumption in complex analysis.
-/
structure DiffContOnCl (f : E → F) (s : Set E) : Prop where
  protected differentiableOn : DifferentiableOn 𝕜 f s
  protected continuousOn : ContinuousOn f (closure s)

variable {𝕜}
/-
**DifferentiableOn.diffContOnCl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.diffContOnCl (h : DifferentiableOn 𝕜 f (closure s)) : Dif
fContOnCl 𝕜 f s
参数：h : DifferentiableOn 𝕜 f (closure s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem DifferentiableOn.diffContOnCl (h : DifferentiableOn 𝕜 f (closure s)) : DiffContOnCl 𝕜 f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩
/-
**Differentiable.diffContOnCl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.diffContOnCl (h : Differentiable 𝕜 f) : DiffContOnCl 𝕜 f s
参数：h : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem Differentiable.diffContOnCl (h : Differentiable 𝕜 f) : DiffContOnCl 𝕜 f s :=
  ⟨h.differentiableOn, h.continuous.continuousOn⟩
/-
**IsClosed.diffContOnCl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.diffContOnCl_iff (hs : IsClosed s) : DiffContOnCl 𝕜 f s ↔ Differe
ntiableOn 𝕜 f s
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem IsClosed.diffContOnCl_iff (hs : IsClosed s) : DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => h.differentiableOn, fun h => ⟨h, hs.closure_eq.symm ▸ h.continuousOn⟩⟩
/-
**diffContOnCl_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：diffContOnCl_univ : DiffContOnCl 𝕜 f univ ↔ Differentiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsClosed.diffContOnCl_iff`：IsClosed.diffContOnCl_iff (hs : IsClosed s) :
 DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
-/
theorem diffContOnCl_univ : DiffContOnCl 𝕜 f univ ↔ Differentiable 𝕜 f :=
  isClosed_univ.diffContOnCl_iff.trans differentiableOn_univ
/-
**diffContOnCl_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ : E => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ : E => c) s :=
  ⟨differentiableOn_const c, continuousOn_const⟩

namespace DiffContOnCl

/-
**DiffContOnCl.comp** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl
 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
参数：hf : DiffContOnCl 𝕜 f s；hg : DiffContOnCl 𝕜 g t；h : MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.comp`：DifferentiableOn.comp {g : F -> G} {t : Set F} (h
g : DifferentiableOn 𝕜 g t) (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : 
Differentia…
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `Set.MapsTo.closure_of_continuousOn`：Set.MapsTo.closure_of_continuousOn {
t : Set β} (h : MapsTo f s t) (hc : ContinuousOn f (closure s)) : MapsTo f (clos
ure s) (closure t)
-/
theorem comp {g : G → E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
    (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t :=
  ⟨hf.1.comp hg.1 h, hf.2.comp hg.2 <| h.closure_of_continuousOn hg.2⟩
/-
**DiffContOnCl.continuousOn_ball** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：continuousOn_ball [NormedSpace Real E] {x : E} {r : Real} (h : DiffContOnC
l 𝕜 f (ball x r)) : ContinuousOn f (closedBall x r)
参数：h : DiffContOnCl 𝕜 f (ball x r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `continuousOn_singleton`：continuousOn_singleton (f : α -> β) (a : α) : Co
ntinuousOn f {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem continuousOn_ball [NormedSpace ℝ E] {x : E} {r : ℝ} (h : DiffContOnCl 𝕜 f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn
/-
**DiffContOnCl.mk_ball** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：mk_ball {x : E} {r : Real} (hd : DifferentiableOn 𝕜 f (ball x r)) (hc : Co
ntinuousOn f (closedBall x r)) : DiffContOnCl 𝕜 f (ball x r)
参数：hd : DifferentiableOn 𝕜 f (ball x r)；hc : ContinuousOn f (closedBall x r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `Metric.closure_ball_subset_closedBall`：closure_ball_subset_closedBall : 
closure (ball x ε) subseteq closedBall x ε
-/
theorem mk_ball {x : E} {r : ℝ} (hd : DifferentiableOn 𝕜 f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) : DiffContOnCl 𝕜 f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩
/-
**DiffContOnCl.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_
3 : NormedSpace 𝕜 E] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s : Set E} {x : E},
   DiffContOnCl 𝕜 f s → IsOpen s → x ∈ s → DifferentiableAt 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
protected theorem differentiableAt (h : DiffContOnCl 𝕜 f s) (hs : IsOpen s) (hx : x ∈ s) :
    DifferentiableAt 𝕜 f x :=
  h.differentiableOn.differentiableAt <| hs.mem_nhds hx
/-
**DiffContOnCl.differentiableAt'** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：differentiableAt' (h : DiffContOnCl 𝕜 f s) (hx : s in 𝓝 x) : Differentiabl
eAt 𝕜 f x
参数：h : DiffContOnCl 𝕜 f s；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
-/
theorem differentiableAt' (h : DiffContOnCl 𝕜 f s) (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.differentiableOn.differentiableAt hx
/-
**DiffContOnCl.mono** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_
3 : NormedSpace 𝕜 E] [inst_4 : NormedSpace 𝕜 F] {f : E → F} {s t : Set E},   Dif
fContOnCl 𝕜 f s → t ⊆ s → DiffContOnCl 𝕜 f t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
protected theorem mono (h : DiffContOnCl 𝕜 f s) (ht : t ⊆ s) : DiffContOnCl 𝕜 f t :=
  ⟨h.differentiableOn.mono ht, h.continuousOn.mono (closure_mono ht)⟩
/-
**DiffContOnCl.add** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (
f + g) s
参数：hf : DiffContOnCl 𝕜 f s；hg : DiffContOnCl 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.add`：DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f + g) s
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f + g) s :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
/-
**DiffContOnCl.add_const** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：add_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x
 + c) s
参数：hf : DiffContOnCl 𝕜 f s；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.add`：add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f + g) s
· 使用定理 `diffContOnCl_const`：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ :
 E => c) s
-/
theorem add_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x + c) s :=
  hf.add diffContOnCl_const
/-
**DiffContOnCl.const_add** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c +
 f x) s
参数：hf : DiffContOnCl 𝕜 f s；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.add`：add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f + g) s
· 使用定理 `diffContOnCl_const`：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ :
 E => c) s
-/
theorem const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c + f x) s :=
  diffContOnCl_const.add hf
/-
**DiffContOnCl.neg** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：neg (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (-f) s
参数：hf : DiffContOnCl 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.neg`：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) 
: DifferentiableOn 𝕜 (-f) s
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem neg (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (-f) s :=
  ⟨hf.1.neg, hf.2.neg⟩
/-
**DiffContOnCl.sub** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (
f - g) s
参数：hf : DiffContOnCl 𝕜 f s；hg : DiffContOnCl 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.sub`：DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f - g) s
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f - g) s :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
/-
**DiffContOnCl.sub_const** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x
 - c) s
参数：hf : DiffContOnCl 𝕜 f s；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `diffContOnCl_const`：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ :
 E => c) s
-/
theorem sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x - c) s :=
  hf.sub diffContOnCl_const
/-
**DiffContOnCl.const_sub** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：const_sub (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c -
 f x) s
参数：hf : DiffContOnCl 𝕜 f s；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `diffContOnCl_const`：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ :
 E => c) s
-/
theorem const_sub (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c - f x) s :=
  diffContOnCl_const.sub hf
/-
**DiffContOnCl.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [Co
ntinuousConstSMul R F] (hf : DiffContOnCl 𝕜 f s) (c : R) : DiffContOnCl 𝕜 (c • f
) s
参数：hf : DiffContOnCl 𝕜 f s；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.const_smul`：DifferentiableOn.const_smul (h : Differenti
ableOn 𝕜 f s) (c : R) : DifferentiableOn 𝕜 (c • f) s
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.const_smul`：ContinuousOn.const_smul (hg : ContinuousOn g s)
 (c : M) : ContinuousOn (c • g) s
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] (hf : DiffContOnCl 𝕜 f s) (c : R) : DiffContOnCl 𝕜 (c • f) s :=
  ⟨hf.1.const_smul c, hf.2.const_smul c⟩
/-
**DiffContOnCl.smul** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Norme
dSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {f : E -> F} {s : Set E} (hc :
 DiffContOnCl 𝕜 c s) (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (fun x => c x • 
f x) s
参数：hc : DiffContOnCl 𝕜 c s；hf : DiffContOnCl 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.smul`：DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c 
s) (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (c • f) s
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] {c : E → 𝕜'} {f : E → F} {s : Set E} (hc : DiffContOnCl 𝕜 c s)
    (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (fun x => c x • f x) s :=
  ⟨hc.1.smul hf.1, hc.2.smul hf.2⟩
/-
**DiffContOnCl.smul_const** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：smul_const {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] 
[NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {s : Set E} (hc : DiffCo
ntOnCl 𝕜 c s) (y : F) : DiffContOnCl 𝕜 (fun x => c x • y) s
参数：hc : DiffContOnCl 𝕜 c s；y : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.smul`：smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [Norme
dAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {f : E ->
 F} {s …
· 使用定理 `diffContOnCl_const`：diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ :
 E => c) s
-/
theorem smul_const {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E → 𝕜'} {s : Set E} (hc : DiffContOnCl 𝕜 c s)
    (y : F) : DiffContOnCl 𝕜 (fun x => c x • y) s :=
  hc.smul diffContOnCl_const
/-
**DiffContOnCl.inv** 是 Mathlib 中的一个定理，位于命名空间 `DiffContOnCl`。
形式化陈述：inv {f : E -> 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : forall x in closure s, f 
x != 0) : DiffContOnCl 𝕜 f⁻¹ s
参数：hf : DiffContOnCl 𝕜 f s；h₀ : forall x in closure s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.comp`：DifferentiableOn.comp {g : F -> G} {t : Set F} (h
g : DifferentiableOn 𝕜 g t) (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : 
Differentia…
· 使用定理 `differentiableOn_inv`：differentiableOn_inv : DifferentiableOn 𝕜 (fun x :
 R => x⁻¹) {x | x != 0}
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
-/
theorem inv {f : E → 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : ∀ x ∈ closure s, f x ≠ 0) :
    DiffContOnCl 𝕜 f⁻¹ s :=
  ⟨(differentiableOn_inv.comp hf.1 fun _ hx => h₀ _ (subset_closure hx) :), hf.2.inv₀ h₀⟩

end DiffContOnCl

/-
**Differentiable.comp_diffContOnCl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.comp_diffContOnCl {g : G -> E} {t : Set G} (hf : Differenti
able 𝕜 f) (hg : DiffContOnCl 𝕜 g t) : DiffContOnCl 𝕜 (f ∘ g) t
参数：hf : Differentiable 𝕜 f；hg : DiffContOnCl 𝕜 g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem Differentiable.comp_diffContOnCl {g : G → E} {t : Set G} (hf : Differentiable 𝕜 f)
    (hg : DiffContOnCl 𝕜 g t) : DiffContOnCl 𝕜 (f ∘ g) t :=
  hf.diffContOnCl.comp hg (mapsTo_image _ _)
/-
**DifferentiableOn.diffContOnCl_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.diffContOnCl_ball {U : Set E} {c : E} {R : Real} (hf : Di
fferentiableOn 𝕜 f U) (hc : closedBall c R subseteq U) : DiffContOnCl 𝕜 f (ball 
c R)
参数：hf : DifferentiableOn 𝕜 f U；hc : closedBall c R subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.mk_ball`：mk_ball {x : E} {r : Real} (hd : DifferentiableOn 
𝕜 f (ball x r)) (hc : ContinuousOn f (closedBall x r)) : DiffContOnCl 𝕜 f (ball 
x r)
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem DifferentiableOn.diffContOnCl_ball {U : Set E} {c : E} {R : ℝ} (hf : DifferentiableOn 𝕜 f U)
    (hc : closedBall c R ⊆ U) : DiffContOnCl 𝕜 f (ball c R) :=
  DiffContOnCl.mk_ball (hf.mono (ball_subset_closedBall.trans hc)) (hf.continuousOn.mono hc)
