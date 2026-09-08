/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/

public section


open Filter

open Topology Filter

variable {α β : Type*}

/-- In a separated space, a complete set is closed. -/
/-
**IsComplete.isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsComplete.isClosed [UniformSpace α] [T0Space α] {s : Set α} (h : IsComple
te s) : IsClosed s
参数：h : IsComplete s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_iff_clusterPt`：isClosed_iff_clusterPt : IsClosed s ↔ forall a, 
ClusterPt a (𝓟 s) -> a in s
· 使用定理 `Cauchy.mono'`：Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot 
g) (h_le : g <= f) : Cauchy g
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique'`：tendsto_nhds_unique' [T2Space X] {f : Y -> X} {l :
 Filter Y} {a b : X} (_ : NeBot l) (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝
 b)) : a =…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α

--- 原说明 ---
In a separated space, a complete set is closed.
-/
theorem IsComplete.isClosed [UniformSpace α] [T0Space α] {s : Set α} (h : IsComplete s) :
    IsClosed s :=
  isClosed_iff_clusterPt.2 fun a ha => by
    let f := 𝓝[s] a
    have : Cauchy f := cauchy_nhds.mono' ha inf_le_left
    rcases h f this inf_le_right with ⟨y, ys, fy⟩
    rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]
/-
**IsUniformEmbedding.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.isClosedEmbedding [UniformSpace α] [UniformSpace β] [Co
mpleteSpace α] [T0Space β] {f : α -> β} (hf : IsUniformEmbedding f) : IsClosedEm
bedding f
参数：hf : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `IsComplete.isClosed`：IsComplete.isClosed [UniformSpace α] [T0Space α] {s
 : Set α} (h : IsComplete s) : IsClosed s
· 使用引理 `IsUniformInducing.isComplete_range`：IsUniformInducing.isComplete_range [
CompleteSpace α] (hf : IsUniformInducing f) : IsComplete (range f)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
-/
theorem IsUniformEmbedding.isClosedEmbedding [UniformSpace α] [UniformSpace β] [CompleteSpace α]
    [T0Space β] {f : α → β} (hf : IsUniformEmbedding f) :
    IsClosedEmbedding f :=
  ⟨hf.isEmbedding, hf.isUniformInducing.isComplete_range.isClosed⟩

namespace IsDenseInducing

open Filter

variable [TopologicalSpace α] {β : Type*} [TopologicalSpace β]
variable {γ : Type*} [UniformSpace γ] [CompleteSpace γ] [T0Space γ]

/-
**IsDenseInducing.continuous_extend_of_cauchy** 是 Mathlib 中的一个定理，位于命名空间 `IsDense
Inducing`。
形式化陈述：continuous_extend_of_cauchy {e : α -> β} {f : α -> γ} (de : IsDenseInducin
g e) (h : forall b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend
 f)
参数：de : IsDenseInducing e；h : forall b : β, Cauchy (map f (comap e <| 𝓝 b))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.continuous_extend`：continuous_extend [T3Space γ] {f : α 
-> γ} (di : IsDenseInducing i) (hf : forall b, exists c, Tendsto f (comap i (𝓝 b
)) (𝓝 c)) : Continuous …
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
-/
theorem continuous_extend_of_cauchy {e : α → β} {f : α → γ} (de : IsDenseInducing e)
    (h : ∀ b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)

end IsDenseInducing

