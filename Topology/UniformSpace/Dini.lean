/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Dini's Theorem

This file proves Dini's theorem, which states that if `F n` is a monotone increasing sequence of
continuous real-valued functions on a compact set `s` converging pointwise to a continuous function
`f`, then `F n` converges uniformly to `f`.

We generalize the codomain from `ℝ` to a normed lattice additive commutative group `G`.
This theorem is true in a different generality as well: when `G` is a linearly ordered topological
group with the order topology. This weakens the norm assumption, in exchange for strengthening to
a linear order. This separate generality is not included in this file, but that generality was
included in initial drafts of the original
https://github.com/leanprover-community/mathlib4/pull/19068 and can be recovered if
necessary.

The key idea of the proof is to use a particular basis of `𝓝 0` which consists of open sets that
are somehow monotone in the sense that if `s` is in the basis, and `0 ≤ x ≤ y`, then
`y ∈ s → x ∈ s`, and so the proof would work on any topological ordered group possessing
such a basis. In the case of a linearly ordered topological group with the order topology, this
basis is `nhds_basis_Ioo`. In the case of a normed lattice additive commutative group, this basis
is `nhds_basis_ball`, and the fact that this basis satisfies the monotonicity criterion
corresponds to `HasSolidNorm`.
-/

public section

open Filter Topology

variable {ι α G : Type*} [Preorder ι] [TopologicalSpace α]
  [NormedAddCommGroup G] [Lattice G] [HasSolidNorm G] [IsOrderedAddMonoid G]

section Unbundled

open Metric

variable {F : ι → α → G} {f : α → G}

namespace Monotone

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
/-
**Monotone.tendstoLocallyUniformly_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `
Monotone`。
形式化陈述：tendstoLocallyUniformly_of_forall_tendsto (hF_cont : forall i, Continuous 
(F i)) (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : forall x, Tendsto
 (F · x) atTop (𝓝 (f x))) : TendstoLocallyUniformly F f atTop
参数：hF_cont : forall i, Continuous (F i)；hF_mono : Monotone F；hf : Continuous f；h
_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.bot_prod`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β}, ⊥ ×ˢ g 
= ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone increasing collection of continuous f
unctions
converging pointwise to a continuous function `f`, then `F n` converges locally 
uniformly to `f`.
-/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : ∀ i, Continuous (F i)) (hF_mono : Monotone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop := by
  refine (atTop : Filter ι).eq_or_neBot.elim (fun h ↦ ?eq_bot) (fun _ ↦ ?_)
  case eq_bot => simp [h, tendstoLocallyUniformly_iff_forall_tendsto]
  have F_le_f (x : α) (n : ι) : F n x ≤ f x := by
    refine _root_.ge_of_tendsto (h_tendsto x) ?_
    filter_upwards [Ici_mem_atTop n] with m hnm
    exact hF_mono hnm x
  simp_rw [Metric.tendstoLocallyUniformly_iff, dist_eq_norm']
  intro ε ε_pos x
  simp_rw +singlePass [tendsto_iff_norm_sub_tendsto_zero] at h_tendsto
  obtain ⟨n, hn⟩ := (h_tendsto x).eventually (eventually_lt_nhds ε_pos) |>.exists
  refine ⟨{y | ‖F n y - f y‖ < ε}, ⟨isOpen_lt (by fun_prop) continuous_const |>.mem_nhds hn, ?_⟩⟩
  filter_upwards [eventually_ge_atTop n] with m hnm z hz
  refine norm_le_norm_of_abs_le_abs ?_ |>.trans_lt hz
  simp only [abs_of_nonpos (sub_nonpos_of_le (F_le_f _ _)), neg_sub, sub_le_sub_iff_left]
  exact hF_mono hnm z

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions on a
set `s` converging pointwise to a continuous function `f`, then `F n` converges locally uniformly
to `f`. -/
/-
**Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间
 `Monotone`。
形式化陈述：tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α} (hF_cont : forall 
i, ContinuousOn (F i) s) (hF_mono : forall x in s, Monotone (F · x)) (hf : Conti
nuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f x))) : Tend
stoLocallyUniformlyOn F f atTop s
参数：hF_cont : forall i, ContinuousOn (F i) s；hF_mono : forall x in s, Monotone (F
 · x)；hf : ContinuousOn f s；h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 
(f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe`：tendstoL
ocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe : TendstoLocallyUniformly
On F f p s ↔ TendstoLocallyUniformly (fun i (x : s) …
· 使用引理 `Monotone.tendstoLocallyUniformly_of_forall_tendsto`：tendstoLocallyUnifor
mly_of_forall_tendsto (hF_cont : forall i, Continuous (F i)) (hF_mono : Monotone
 F) (hf : Continuous f) (h_tendsto : for…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone increasing collection of continuous f
unctions on a
set `s` converging pointwise to a continuous function `f`, then `F n` converges 
locally uniformly
to `f`.
-/
lemma tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α}
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f atTop s := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  exact tendstoLocallyUniformly_of_forall_tendsto (hF_cont · |>.domRestrict)
    (fun _ _ h x ↦ hF_mono _ x.2 h) hf.domRestrict (fun x ↦ h_tendsto x x.2)

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions on a
compact space converging pointwise to a continuous function `f`, then `F n` converges uniformly to
`f`. -/
/-
**Monotone.tendstoUniformly_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Monoton
e`。
形式化陈述：tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : forall i, C
ontinuous (F i)) (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : forall 
x, Tendsto (F · x) atTop (𝓝 (f x))) : TendstoUniformly F f atTop
参数：hF_cont : forall i, Continuous (F i)；hF_mono : Monotone F；hf : Continuous f；h
_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace`：tendstoLoc
allyUniformly_iff_tendstoUniformly_of_compactSpace [CompactSpace α] : TendstoLoc
allyUniformly F f p ↔ TendstoUniformly F f p
· 使用引理 `Monotone.tendstoLocallyUniformly_of_forall_tendsto`：tendstoLocallyUnifor
mly_of_forall_tendsto (hF_cont : forall i, Continuous (F i)) (hF_mono : Monotone
 F) (hf : Continuous f) (h_tendsto : for…

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone increasing collection of continuous f
unctions on a
compact space converging pointwise to a continuous function `f`, then `F n` conv
erges uniformly to
`f`.
-/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp <|
    tendstoLocallyUniformly_of_forall_tendsto hF_cont hF_mono hf h_tendsto

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous function `f`, then `F n` converges uniformly
to `f`. -/
/-
**Monotone.tendstoUniformlyOn_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Monot
one`。
形式化陈述：tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s) (hF_co
nt : forall i, ContinuousOn (F i) s) (hF_mono : forall x in s, Monotone (F · x))
 (hf : ContinuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f
 x))) : TendstoUniformlyOn F f atTop s
参数：hs : IsCompact s；hF_cont : forall i, ContinuousOn (F i) s；hF_mono : forall x 
in s, Monotone (F · x)；hf : ContinuousOn f s；h_tendsto : forall x in s, Tendsto 
(F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`：tendstoLoca
llyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hs : IsCompact s) : TendstoLoc
allyUniformlyOn F f p s ↔ TendstoUniformlyOn F f …
· 使用引理 `Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto`：tendstoLocallyUnif
ormlyOn_of_forall_tendsto {s : Set α} (hF_cont : forall i, ContinuousOn (F i) s)
 (hF_mono : forall x in s, Monotone (F · x…

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone increasing collection of continuous f
unctions on a
compact set `s` converging pointwise to a continuous function `f`, then `F n` co
nverges uniformly
to `f`.
-/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs |>.mp <|
    tendstoLocallyUniformlyOn_of_forall_tendsto hF_cont hF_mono hf h_tendsto

end Monotone

namespace Antitone

/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
/-
**Antitone.tendstoLocallyUniformly_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `
Antitone`。
形式化陈述：tendstoLocallyUniformly_of_forall_tendsto (hF_cont : forall i, Continuous 
(F i)) (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : forall x, Tendsto
 (F · x) atTop (𝓝 (f x))) : TendstoLocallyUniformly F f atTop
参数：hF_cont : forall i, Continuous (F i)；hF_anti : Antitone F；hf : Continuous f；h
_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.tendstoLocallyUniformly_of_forall_tendsto`：tendstoLocallyUnifor
mly_of_forall_tendsto (hF_cont : forall i, Continuous (F i)) (hF_mono : Monotone
 F) (hf : Continuous f) (h_tendsto : for…
· 使用定理 `OrderDual.instHasSolidNorm`：∀ {α : Type u_1} [inst : NormedAddCommGroup 
α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   HasSolidNorm 
αᵒᵈ
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone decreasing collection of continuous f
unctions on a
converging pointwise to a continuous function `f`, then `F n` converges locally 
uniformly to `f`.
-/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : ∀ i, Continuous (F i)) (hF_anti : Antitone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop :=
  Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
set `s` converging pointwise to a continuous function `f`, then `F n` converges locally uniformly
to `f`. -/
/-
**Antitone.tendstoLocallyUniformlyOn_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间
 `Antitone`。
形式化陈述：tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α} (hF_cont : forall 
i, ContinuousOn (F i) s) (hF_anti : forall x in s, Antitone (F · x)) (hf : Conti
nuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f x))) : Tend
stoLocallyUniformlyOn F f atTop s
参数：hF_cont : forall i, ContinuousOn (F i) s；hF_anti : forall x in s, Antitone (F
 · x)；hf : ContinuousOn f s；h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 
(f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto`：tendstoLocallyUnif
ormlyOn_of_forall_tendsto {s : Set α} (hF_cont : forall i, ContinuousOn (F i) s)
 (hF_mono : forall x in s, Monotone (F · x…
· 使用定理 `OrderDual.instHasSolidNorm`：∀ {α : Type u_1} [inst : NormedAddCommGroup 
α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   HasSolidNorm 
αᵒᵈ
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone decreasing collection of continuous f
unctions on a
set `s` converging pointwise to a continuous function `f`, then `F n` converges 
locally uniformly
to `f`.
-/
lemma tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α}
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_anti : ∀ x ∈ s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f atTop s :=
  Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
compact space converging pointwise to a continuous function `f`, then `F n` converges uniformly
to `f`. -/
/-
**Antitone.tendstoUniformly_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Antiton
e`。
形式化陈述：tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : forall i, C
ontinuous (F i)) (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : forall 
x, Tendsto (F · x) atTop (𝓝 (f x))) : TendstoUniformly F f atTop
参数：hF_cont : forall i, Continuous (F i)；hF_anti : Antitone F；hf : Continuous f；h
_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.tendstoUniformly_of_forall_tendsto`：tendstoUniformly_of_forall_
tendsto [CompactSpace α] (hF_cont : forall i, Continuous (F i)) (hF_mono : Monot
one F) (hf : Continuous f) (h_ten…
· 使用定理 `OrderDual.instHasSolidNorm`：∀ {α : Type u_1} [inst : NormedAddCommGroup 
α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   HasSolidNorm 
αᵒᵈ
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone decreasing collection of continuous f
unctions on a
compact space converging pointwise to a continuous function `f`, then `F n` conv
erges uniformly
to `f`.
-/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  Monotone.tendstoUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
/-
**Antitone.tendstoUniformlyOn_of_forall_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Antit
one`。
形式化陈述：tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s) (hF_co
nt : forall i, ContinuousOn (F i) s) (hF_anti : forall x in s, Antitone (F · x))
 (hf : ContinuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f
 x))) : TendstoUniformlyOn F f atTop s
参数：hs : IsCompact s；hF_cont : forall i, ContinuousOn (F i) s；hF_anti : forall x 
in s, Antitone (F · x)；hf : ContinuousOn f s；h_tendsto : forall x in s, Tendsto 
(F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.tendstoUniformlyOn_of_forall_tendsto`：tendstoUniformlyOn_of_for
all_tendsto {s : Set α} (hs : IsCompact s) (hF_cont : forall i, ContinuousOn (F 
i) s) (hF_mono : forall x in s, Mon…
· 使用定理 `OrderDual.instHasSolidNorm`：∀ {α : Type u_1} [inst : NormedAddCommGroup 
α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   HasSolidNorm 
αᵒᵈ
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone decreasing collection of continuous f
unctions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges u
niformly to `f`.
-/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_anti : ∀ x ∈ s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hs hF_cont hF_anti hf h_tendsto

end Antitone

end Unbundled

namespace ContinuousMap

variable {F : ι → C(α, G)} {f : C(α, G)}

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions
converging pointwise to a continuous function `f`, then `F n` converges to `f` in the
compact-open topology. -/
/-
**ContinuousMap.tendsto_of_monotone_of_pointwise** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousMap`。
形式化陈述：tendsto_of_monotone_of_pointwise (hF_mono : Monotone F) (h_tendsto : foral
l x, Tendsto (F · x) atTop (𝓝 (f x))) : Tendsto F atTop (𝓝 f)
参数：hF_mono : Monotone F；h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.tendsto_of_tendstoLocallyUniformly`：tendsto_of_tendstoLoca
llyUniformly (h : TendstoLocallyUniformly (fun i a => F i a) f p) : Tendsto F p 
(𝓝 f)
· 使用引理 `Monotone.tendstoLocallyUniformly_of_forall_tendsto`：tendstoLocallyUnifor
mly_of_forall_tendsto (hF_cont : forall i, Continuous (F i)) (hF_mono : Monotone
 F) (hf : Continuous f) (h_tendsto : for…
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone increasing collection of continuous f
unctions
converging pointwise to a continuous function `f`, then `F n` converges to `f` i
n the
compact-open topology.
-/
lemma tendsto_of_monotone_of_pointwise (hF_mono : Monotone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_tendstoLocallyUniformly <|
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto (F · |>.continuous) f.continuous h_tendsto

/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions
converging pointwise to a continuous function `f`, then `F n` converges to `f` in the
compact-open topology. -/
/-
**ContinuousMap.tendsto_of_antitone_of_pointwise** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousMap`。
形式化陈述：tendsto_of_antitone_of_pointwise (hF_anti : Antitone F) (h_tendsto : foral
l x, Tendsto (F · x) atTop (𝓝 (f x))) : Tendsto F atTop (𝓝 f)
参数：hF_anti : Antitone F；h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.tendsto_of_monotone_of_pointwise`：tendsto_of_monotone_of_p
ointwise (hF_mono : Monotone F) (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 
(f x))) : Tendsto F atTop (𝓝 f)
· 使用定理 `OrderDual.instHasSolidNorm`：∀ {α : Type u_1} [inst : NormedAddCommGroup 
α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   HasSolidNorm 
αᵒᵈ
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
**Dini's theorem**: if `F n` is a monotone decreasing collection of continuous f
unctions
converging pointwise to a continuous function `f`, then `F n` converges to `f` i
n the
compact-open topology.
-/
lemma tendsto_of_antitone_of_pointwise (hF_anti : Antitone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_monotone_of_pointwise (G := Gᵒᵈ) hF_anti h_tendsto

end ContinuousMap

