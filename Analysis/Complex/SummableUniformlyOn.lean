/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of uniformly convergent series sums of functions

We collect some results about the differentiability of infinite sums.

-/

public section

/-
**SummableLocallyUniformlyOn.differentiableOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SummableLocallyUniformlyOn.differentiableOn {ι E : Type*} [NormedAddCommGr
oup E] [NormedSpace Complex E] [CompleteSpace E] {f : ι -> Complex -> E} {s : Se
t Complex} (hs : IsOpen s) (h : SummableLocallyUniformlyOn f s) (hf2 : forall n 
r, r in s -> DifferentiableAt Complex (f n) r) : DifferentiableOn Complex (fun z
 => ∑' n, f n z) s
参数：hs : IsOpen s；h : SummableLocallyUniformlyOn f s；hf2 : forall n r, r in s -> 
DifferentiableAt Complex (f n) r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.differentiableOn`：∀ {E : Type u_1} {ι : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Fi
lter ι}   {F : ι → ℂ → E} {f : ℂ…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`：∀ {α : Type u_1}
 {β : Type u_2} {ι : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β →
 α} {s : Set β}   [inst_1 : UniformSpace α] …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableWithinAt.fun_sum`：DifferentiableWithinAt.fun_sum (h : fora
ll i in u, DifferentiableWithinAt 𝕜 (A i) s x) : DifferentiableWithinAt 𝕜 (fun y
 => ∑ i in u, A i y)…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `DifferentiableOn.congr`：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f
 s) (h' : forall x in s, f₁ x = f x) : DifferentiableOn 𝕜 f₁ s
· 使用定理 `HasSumLocallyUniformlyOn.tsum_eqOn`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α] …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma SummableLocallyUniformlyOn.differentiableOn {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (h : SummableLocallyUniformlyOn f s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    DifferentiableOn ℂ (fun z ↦ ∑' n, f n z) s := by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha ↦ (hf2 a r hr).differentiableWithinAt
