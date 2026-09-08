/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# The Logarithmic derivative of an infinite product

We show that if we have an infinite product of functions `f` that is locally uniformly convergent,
then the logarithmic derivative of the product is the sum of the logarithmic derivatives of the
individual functions.

-/

public section

open Complex

/-
**logDeriv_tprod_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_tprod_eq_tsum {ι : Type*} {s : Set Complex} (hs : IsOpen s) {x : 
Complex} (hx : x in s) {f : ι -> Complex -> Complex} (hf : forall i, f i x != 0)
 (hd : forall i, DifferentiableOn Complex (f i) s) (hm : Summable fun i => logDe
riv (f i) x) (htend : MultipliableLocallyUniformlyOn f s) (hnez : ∏' i, f i x !=
 0) : logDeriv (∏' i, f i ·) x = ∑' i, logDeriv (f i) x
参数：hs : IsOpen s；hx : x in s；hf : forall i, f i x != 0；hd : forall i, Differenti
ableOn Complex (f i) s；hm : Summable fun i => logDeriv (f i) x；htend : Multiplia
bleLocallyUniformlyOn f s；hnez : ∏' i, f i x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α
} [T2Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `logDeriv_prod`：logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜
'} {x : 𝕜} (hf : forall i in s, f i x != 0) (hd : forall i in s, DifferentiableA
t 𝕜…
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Complex.logDeriv_tendsto`：logDeriv_tendsto {ι : Type*} {p : Filter ι} {f
 : ι -> Complex -> Complex} {g : Complex -> Complex} {s : Set Complex} (hs : IsO
pen s) {x : Co…
· 使用定理 `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn`：MultipliableLo
callyUniformlyOn.hasProdLocallyUniformlyOn (h : MultipliableLocallyUniformlyOn f
 s) : HasProdLocallyUniformlyOn f (∏' i, f i ·…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_finsetProd`：DifferentiableOn.fun_finsetProd (hd : f
orall i in u, DifferentiableOn 𝕜 (f i) s) : DifferentiableOn 𝕜 (∏ i in u, f i ·)
 s
-/
theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) s)
    (hm : Summable fun i ↦ logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f s)
    (hnez : ∏' i, f i x ≠ 0) :
    logDeriv (∏' i, f i ·) x = ∑' i, logDeriv (f i) x := by
  rw [Eq.comm, ← hm.hasSum_iff]
  refine logDeriv_tendsto hs hx htend.hasProdLocallyUniformlyOn (.of_forall <| by fun_prop) hnez
    |>.congr fun b ↦ ?_
  rw [logDeriv_prod (fun i _ ↦ hf i) (fun i _ ↦ (hd i x hx).differentiableAt (hs.mem_nhds hx))]
