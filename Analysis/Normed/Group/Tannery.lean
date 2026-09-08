/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Tannery's theorem

Tannery's theorem gives a sufficient criterion for the limit of an infinite sum (with respect to
an auxiliary parameter) to equal the sum of the pointwise limits. See
https://en.wikipedia.org/wiki/Tannery%27s_theorem. It is a special case of the dominated convergence
theorem (with the measure chosen to be the counting measure); but we give here a direct proof, in
order to avoid some unnecessary hypotheses that appear when specialising the general
measure-theoretic result.
-/

public section

open Filter Topology

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- **Tannery's theorem**: topological sums commute with termwise limits, when the norms of the
summands are eventually uniformly bounded by a summable function.

(This is the special case of the Lebesgue dominated convergence theorem for the counting measure
on a discrete set. However, we prove it under somewhat weaker assumptions than the general
measure-theoretic result, e.g. `G` is not assumed to be an `ℝ`-vector space or second countable,
and the limit is along an arbitrary filter rather than `atTop ℕ`.)

See also:
* `MeasureTheory.tendsto_integral_of_dominated_convergence` (for general integrals, but
  with more assumptions on `G`)
* `continuous_tsum` (continuity of infinite sums in a parameter)
-/
/-
**tendsto_tsum_of_dominated_convergence** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_tsum_of_dominated_convergence {α β G : Type*} {𝓕 : Filter α} [Norm
edAddCommGroup G] [CompleteSpace G] {f : α -> β -> G} {g : β -> G} {bound : β ->
 Real} (h_sum : Summable bound) (hab : forall k : β, Tendsto (f · k) 𝓕 (𝓝 (g k))
) (h_bound : forallᶠ n in 𝓕, forall k, ‖f n k‖ <= bound k) : Tendsto (∑' k, f · 
k) 𝓕 (𝓝 (∑' k, g k))
参数：h_sum : Summable bound；hab : forall k : β, Tendsto (f · k) 𝓕 (𝓝 (g k))；h_boun
d : forallᶠ n in 𝓕, forall k, ‖f n k‖ <= bound k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [IsEmpty β], ∑'
…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E] {x : E}, Fi
lter.Tendsto (fun a => ‖a‖) (nhds x) (nhds ‖x‖)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasSu
m…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
**Tannery's theorem**: topological sums commute with termwise limits, when the n
orms of the
summands are eventually uniformly bounded by a summable function.

(This is the special case of the Lebesgue dominated convergence theorem for the 
counting measure
on a discrete set. However, we prove it under somewhat weaker assumptions than t
he general
measure-theoretic result, e.g. `G` is not assumed to be an `ℝ`-vector space or s
econd countable,
and the limit is along an arbitrary filter rather than `atTop ℕ`.)

See also:
* `MeasureTheory.tendsto_integral_of_dominated_convergence` (for general integra
ls, but
  with more assumptions on `G`)
* `continuous_tsum` (continuity of infinite sums in a parameter)
-/
lemma tendsto_tsum_of_dominated_convergence {α β G : Type*} {𝓕 : Filter α}
    [NormedAddCommGroup G] [CompleteSpace G]
    {f : α → β → G} {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k : β, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (∑' k, f · k) 𝓕 (𝓝 (∑' k, g k)) := by
  -- WLOG β is nonempty
  rcases isEmpty_or_nonempty β
  · simpa only [tsum_empty] using tendsto_const_nhds
  -- WLOG 𝓕 ≠ ⊥
  rcases 𝓕.eq_or_neBot with rfl | _
  · simp only [tendsto_bot]
  -- Auxiliary lemmas
  have h_g_le (k : β) : ‖g k‖ ≤ bound k :=
    le_of_tendsto (tendsto_norm.comp (hab k)) <| h_bound.mono (fun n h => h k)
  have h_sumg : Summable (‖g ·‖) :=
    h_sum.of_norm_bounded (fun k ↦ (norm_norm (g k)).symm ▸ h_g_le k)
  have h_suma : ∀ᶠ n in 𝓕, Summable (‖f n ·‖) := by
    filter_upwards [h_bound] with n h
    exact h_sum.of_norm_bounded <| by simpa only [norm_norm] using h
  -- Now main proof, by an `ε / 3` argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ⟨S, hS⟩ := h_sum
  obtain ⟨T, hT⟩ : ∃ (T : Finset β), dist (∑ b ∈ T, bound b) S < ε / 3 := by
    rw [HasSum, Metric.tendsto_nhds] at hS
    exact Eventually.exists <| hS _ (by positivity)
  have h1 : ∑' (k : (Tᶜ : Set β)), bound k < ε / 3 := by
    calc _ ≤ ‖∑' (k : (Tᶜ : Set β)), bound k‖ := Real.le_norm_self _
         _ = ‖S - ∑ b ∈ T, bound b‖           := congrArg _ ?_
         _ < ε / 3                            := by rwa [dist_eq_norm, norm_sub_rev] at hT
    simpa only [h_sum.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hS.tsum_eq
  have h2 : Tendsto (∑ k ∈ T, f · k) 𝓕 (𝓝 (T.sum g)) := tendsto_finsetSum _ (fun i _ ↦ hab i)
  rw [Metric.tendsto_nhds] at h2
  filter_upwards [h2 (ε / 3) (by positivity), h_suma, h_bound] with n hn h_suma h_bound
  rw [dist_eq_norm, ← h_suma.of_norm.tsum_sub h_sumg.of_norm,
    ← (h_suma.of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hn
  · rw [(h_suma.subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm (h_suma.subtype _)).trans ?_).trans_lt h1
      exact (h_suma.subtype _).tsum_le_tsum (h_bound ·) (h_sum.subtype _)
    · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
      exact (h_sumg.subtype _).tsum_le_tsum (h_g_le ·) (h_sum.subtype _)
