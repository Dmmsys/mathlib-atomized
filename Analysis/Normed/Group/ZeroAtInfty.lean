/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# ZeroAtInftyContinuousMapClass in normed additive groups

In this file we give a characterization of the predicate `zero_at_infty` from
`ZeroAtInftyContinuousMapClass`. A continuous map `f` is zero at infinity if and only if
for every `ε > 0` there exists a `r : ℝ` such that for all `x : E` with `r < ‖x‖` it holds that
`‖f x‖ < ε`.
-/

public section

open Topology Filter

variable {E F 𝓕 : Type*}
variable [SeminormedAddGroup E] [SeminormedAddCommGroup F]
variable [FunLike 𝓕 E F] [ZeroAtInftyContinuousMapClass 𝓕 E F]

/-
**ZeroAtInftyContinuousMapClass.norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZeroAtInftyContinuousMapClass.norm_le (f : 𝓕) (ε : Real) (hε : 0 < ε) : ex
ists (r : Real), forall (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε
参数：f : 𝓕；ε : Real；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroAtInftyContinuousMapClass.zero_at_infty`：∀ {F : Type u_2} {α : outPa
ram (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α} {inst_1 : 
Zero β}   {inst_2 : TopologicalSp…
· 使用定理 `Metric.closedBall_compl_subset_of_mem_cocompact`：closedBall_compl_subset
_of_mem_cocompact {s : Set α} (hs : s in cocompact α) (c : α) : exists (r : Real
), (Metric.closedBall c r)ᶜ subseteq …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
-/
theorem ZeroAtInftyContinuousMapClass.norm_le (f : 𝓕) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε := by
  have h := zero_at_infty f
  rw [tendsto_zero_iff_norm_tendsto_zero, tendsto_def] at h
  specialize h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rcases Metric.closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hr'
  suffices x ∈ (fun x ↦ ‖f x‖) ⁻¹' Metric.ball 0 ε by simp_all
  apply hr
  simp_all

variable [ProperSpace E]
/-
**zero_at_infty_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_at_infty_of_norm_le (f : E -> F) (h : forall (ε : Real) (_hε : 0 < ε)
, exists (r : Real), forall (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε) : Tendsto f (coc
ompact E) (𝓝 0)
参数：f : E -> F；h : forall (ε : Real) (_hε : 0 < ε), exists (r : Real), forall (x 
: E) (_hx : r < ‖x‖), ‖f x‖ < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Metric.mem_cocompact_iff_closedBall_compl_subset`：mem_cocompact_iff_clos
edBall_compl_subset [ProperSpace α] (c : α) : s in cocompact α ↔ exists r, (clos
edBall c r)ᶜ subseteq s
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem zero_at_infty_of_norm_le (f : E → F)
    (h : ∀ (ε : ℝ) (_hε : 0 < ε), ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε) :
    Tendsto f (cocompact E) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  intro s hs
  rw [mem_map, Metric.mem_cocompact_iff_closedBall_compl_subset 0]
  rw [Metric.mem_nhds_iff] at hs
  rcases hs with ⟨ε, hε, hs⟩
  rcases h ε hε with ⟨r, hr⟩
  use r
  intro
  aesop
