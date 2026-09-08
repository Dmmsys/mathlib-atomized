/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Cover
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Covers in a metric space

This file defines covers, aka nets, which are a quantitative notion of compactness in a metric
space.

A `ε`-cover of a set `s` is a set `N` such that every element of `s` is at distance at most `ε` to
some element of `N`.

In a proper metric space, sets admitting a finite cover are precisely the relatively compact sets.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

@[expose] public section

open Set
open scoped NNReal

namespace Metric
variable {X Y : Type*}

section PseudoEMetricSpace
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {ε δ : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetRel.IsRefl {(x, y) : X × X | edist x y ≤ ε} where refl := by simp
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetRel.IsSymm {(x, y) : X × X | edist x y ≤ ε} where symm := by simp [edist_comm]

/-- A set `N` is an *`ε`-cover* of a set `s` if every point of `s` lies at distance at most `ε` of
some point of `N`.

This is also called an *`ε`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
/-
**Metric.IsCover** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：IsCover (ε : Real>=0) (s N : Set X) : Prop
参数：ε : Real>=0；s N : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `N` is an *`ε`-cover* of a set `s` if every point of `s` lies at distance 
at most `ε` of
some point of `N`.

This is also called an *`ε`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1.
-/
def IsCover (ε : ℝ≥0) (s N : Set X) : Prop := SetRel.IsCover {(x, y) | edist x y ≤ ε} s N

@[simp] protected nonrec lemma IsCover.empty : IsCover ε ∅ N := .empty
/-
**Metric.isCover_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε : NNReal} {s : Set X}, M
etric.IsCover ε s ∅ ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.isCover_empty_right`：∀ {X : Type u_1} {U : SetRel X X} {s : Set X
}, U.IsCover s ∅ ↔ s = ∅
-/
@[simp] lemma isCover_empty_right : IsCover ε s ∅ ↔ s = ∅ := SetRel.isCover_empty_right

protected nonrec lemma IsCover.nonempty (hsN : IsCover ε s N) (hs : s.Nonempty) : N.Nonempty :=
  hsN.nonempty hs
/-
**Metric.IsCover.refl** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] (ε : NNReal) (s : Set X), M
etric.IsCover ε s s
参数：ε : NNReal；s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.rfl`：∀ {X : Type u_1} {U : SetRel X X} [U.IsRefl] {s : Se
t X}, U.IsCover s s
-/
@[simp] lemma IsCover.refl (ε : ℝ≥0) (s : Set X) : IsCover ε s s := .rfl
/-
**Metric.IsCover.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε : NNReal} {s : Set X}, M
etric.IsCover ε s s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.refl`：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] (ε :
 NNReal) (s : Set X), Metric.IsCover ε s s
-/
lemma IsCover.rfl {ε : ℝ≥0} {s : Set X} : IsCover ε s s := refl ε s

nonrec lemma IsCover.mono (hN : N₁ ⊆ N₂) (h₁ : IsCover ε s N₁) : IsCover ε s N₂ := h₁.mono hN

nonrec lemma IsCover.anti (hst : s ⊆ t) (ht : IsCover ε t N) : IsCover ε s N := ht.anti hst
/-
**Metric.IsCover.mono_radius** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε δ : NNReal} {s N : Set X
},   ε ≤ δ → Metric.IsCover ε s N → Metric.IsCover δ s N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.mono_entourage`：∀ {X : Type u_1} {U V : SetRel X X} {s N 
: Set X}, U ⊆ V → U.IsCover s N → V.IsCover s N
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsCover.mono_radius (hεδ : ε ≤ δ) (hε : IsCover ε s N) : IsCover δ s N :=
  hε.mono_entourage fun xy hxy ↦ by dsimp at *; exact le_trans hxy <| mod_cast hεδ
/-
**Metric.IsCover.image_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {f : X → Y} {s N : Set X}   {ε K₂ : NNReal}, Metric.IsCover 
ε s N → LipschitzWith K₂ f → Metric.IsCover (K₂ * ε) (f '' s) (f '' N)
参数：K₂ * ε；f '' s；f '' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
lemma IsCover.image_lipschitz {f : X → Y} {s : Set X} {N : Set X} {ε K₂ : ℝ≥0}
    (hs : IsCover ε s N) (hf : LipschitzWith K₂ f) : IsCover (K₂ * ε) (f '' s) (f '' N) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x₀, hx₀, hcover⟩ := hs hx
  dsimp at *
  exact ⟨f x₀, ⟨x₀, hx₀, by grind⟩, by grw [hf x x₀, hcover]⟩
/-
**Metric.IsCover.image_lipschitz_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Metric
.IsCover`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : PseudoEMetricSpace X] [inst_1 : Ps
eudoEMetricSpace Y] {f : X → Y} {s : Set Y}   {N : Set X} {ε K₂ : NNReal},   Met
ric.IsCover ε (f ⁻¹' s) N → LipschitzWith K₂ f → Function.Surjective f → Metric.
IsCover (K₂ * ε) s (f '' N)
参数：f ⁻¹' s；K₂ * ε；f '' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.image_lipschitz`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
PseudoEMetricSpace X] [inst_1 : PseudoEMetricSpace Y] {f : X → Y} {s N : Set X} 
  {ε K₂ : NNReal}, M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
lemma IsCover.image_lipschitz_of_surjective {f : X → Y} {s : Set Y} {N : Set X} {ε K₂ : ℝ≥0}
    (hs : IsCover ε (s.preimage f) N) (hf : LipschitzWith K₂ f) (hf_surj : f.Surjective) :
    IsCover (K₂ * ε) s (f '' N) := by
  have : IsCover (K₂ * ε) (f '' s.preimage f) (f '' N) := IsCover.image_lipschitz hs hf
  simp_all only [image_preimage_eq]
/-
**Metric._root_.Isometry.isCover_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Isometry.isCover_image_iff {f : X → Y} (hf : Isometry f) (C : Set X) :
    IsCover ε (f '' s) (f '' C) ↔ IsCover ε s C := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ by simpa using h.image_lipschitz hf.lipschitz⟩
  obtain ⟨c, hc_mem, hc⟩ := h (Set.mem_image_of_mem _ hx)
  obtain ⟨c', hc', rfl⟩ := hc_mem
  exact ⟨c', hc', le_of_eq_of_le (hf.edist_eq _ _).symm hc⟩
/-
**Metric.IsCover.singleton_of_ediam_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover
`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] {ε : NNReal} {s : Set X} {x
 : X},   Metric.ediam s ≤ ↑ε → x ∈ s → Metric.IsCover ε s {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
-/
lemma IsCover.singleton_of_ediam_le (hA : ediam s ≤ ε) (hx : x ∈ s) :
    IsCover ε s ({x} : Set X) :=
  fun _ h_mem ↦ ⟨x, by simp, (edist_le_ediam_of_mem h_mem hx).trans hA⟩
/-
**Metric.isCover_iff_subset_iUnion_closedEBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric
`。
形式化陈述：isCover_iff_subset_iUnion_closedEBall : IsCover ε s N ↔ s subseteq ⋃ y in 
N, Metric.closedEBall y ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCover_iff_subset_iUnion_closedEBall :
    IsCover ε s N ↔ s ⊆ ⋃ y ∈ N, Metric.closedEBall y ε := by
  simp [IsCover, SetRel.IsCover, subset_def]

alias isCover_iff_subset_iUnion_emetricClosedBall :=
  isCover_iff_subset_iUnion_closedEBall

/-- A maximal `ε`-separated subset of a set `s` is an `ε`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
nonrec lemma IsCover.of_maximal_isSeparated (hN : Maximal (fun N ↦ N ⊆ s ∧ IsSeparated ε N) N) :
    IsCover ε s N :=
  .of_maximal_isSeparated <| by simpa [isSeparated_iff_setRelIsSeparated] using hN

/-- A totally bounded set has finite `ε`-covers for all `ε > 0`. -/
/-
**Metric.exists_finite_isCover_of_totallyBounded** 是 Mathlib 中的一个引理，位于命名空间 `Metr
ic`。
形式化陈述：exists_finite_isCover_of_totallyBounded (hε : ε != 0) (hs : TotallyBounded
 s) : exists N subseteq s, N.Finite ∧ IsCover ε s N
参数：hε : ε != 0；hs : TotallyBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EMetric.totallyBounded_iff'`：totallyBounded_iff' {s : Set α} : TotallyBo
unded s ↔ forall ε > 0, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y i
n t, eball y ε
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A totally bounded set has finite `ε`-covers for all `ε > 0`.
-/
lemma exists_finite_isCover_of_totallyBounded (hε : ε ≠ 0) (hs : TotallyBounded s) :
    ∃ N ⊆ s, N.Finite ∧ IsCover ε s N := by
  rw [EMetric.totallyBounded_iff'] at hs
  obtain ⟨N, hNA, hN_finite, hN⟩ := hs ε (by positivity)
  simp only [isCover_iff_subset_iUnion_closedEBall]
  refine ⟨N, by simpa, by simpa, ?_⟩
  · refine hN.trans fun x hx ↦ ?_
    simp only [Set.mem_iUnion, Metric.mem_eball, exists_prop, Metric.mem_closedEBall] at hx ⊢
    obtain ⟨y, hyN, hy⟩ := hx
    exact ⟨y, hyN, hy.le⟩

/-- A relatively compact set admits a finite cover. -/
/-
**Metric.exists_finite_isCover_of_isCompact_closure** 是 Mathlib 中的一个引理，位于命名空间 `M
etric`。
形式化陈述：exists_finite_isCover_of_isCompact_closure (hε : ε != 0) (hs : IsCompact (
closure s)) : exists N subseteq s, N.Finite ∧ IsCover ε s N
参数：hε : ε != 0；hs : IsCompact (closure s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.exists_finite_isCover_of_totallyBounded`：exists_finite_isCover_of
_totallyBounded (hε : ε != 0) (hs : TotallyBounded s) : exists N subseteq s, N.F
inite ∧ IsCover ε s N
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s

--- 原说明 ---
A relatively compact set admits a finite cover.
-/
lemma exists_finite_isCover_of_isCompact_closure (hε : ε ≠ 0) (hs : IsCompact (closure s)) :
    ∃ N ⊆ s, N.Finite ∧ IsCover ε s N :=
  exists_finite_isCover_of_totallyBounded hε (hs.totallyBounded.subset subset_closure)

/-- A compact set admits a finite cover. -/
/-
**Metric.exists_finite_isCover_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：exists_finite_isCover_of_isCompact (hε : ε != 0) (hs : IsCompact s) : exis
ts N subseteq s, N.Finite ∧ IsCover ε s N
参数：hε : ε != 0；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.exists_finite_isCover_of_totallyBounded`：exists_finite_isCover_of
_totallyBounded (hε : ε != 0) (hs : TotallyBounded s) : exists N subseteq s, N.F
inite ∧ IsCover ε s N
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s

--- 原说明 ---
A compact set admits a finite cover.
-/
lemma exists_finite_isCover_of_isCompact (hε : ε ≠ 0) (hs : IsCompact s) :
    ∃ N ⊆ s, N.Finite ∧ IsCover ε s N :=
  exists_finite_isCover_of_totallyBounded hε hs.totallyBounded

end PseudoEMetricSpace

section PseudoMetricSpace
variable [PseudoMetricSpace X] {ε : ℝ≥0} {s N : Set X}

/-
**Metric.isCover_iff_subset_iUnion_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric`
。
形式化陈述：isCover_iff_subset_iUnion_closedBall : IsCover ε s N ↔ s subseteq ⋃ y in N
, closedBall y ε
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCover_iff_subset_iUnion_closedBall : IsCover ε s N ↔ s ⊆ ⋃ y ∈ N, closedBall y ε := by
  simp [IsCover, SetRel.IsCover, subset_def]

alias ⟨IsCover.subset_iUnion_closedBall, IsCover.of_subset_iUnion_closedBall⟩ :=
  isCover_iff_subset_iUnion_closedBall
/-
**Metric.IsCover.of_subset_cthickening_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric.I
sCover`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {ε : NNReal} {s N : Set X} {
δ : NNReal},   s ⊆ Metric.cthickening (↑ε) N → ε < δ → Metric.IsCover δ s N
参数：↑ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.of_subset_iUnion_closedBall`：∀ {X : Type u_1} [inst : Pse
udoMetricSpace X] {ε : NNReal} {s N : Set X},   s ⊆ ⋃ y ∈ N, Metric.closedBall y
 ↑ε → Metric.IsCover ε s N
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.cthickening_subset_iUnion_closedBall_of_lt`：cthickening_subset_iU
nion_closedBall_of_lt {α : Type*} [PseudoMetricSpace α] (E : Set α) {δ δ' : Real
} (hδ₀ : 0 < δ') (hδδ' : δ < δ') : cthi…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
-/
lemma IsCover.of_subset_cthickening_of_lt {δ : ℝ≥0} (hsN : s ⊆ cthickening ε N) (hεδ : ε < δ) :
    IsCover δ s N :=
  .of_subset_iUnion_closedBall <| hsN.trans (cthickening_subset_iUnion_closedBall_of_lt _
    (NNReal.zero_le_coe.trans_lt hεδ) hεδ)

variable [ProperSpace X]
/-
**Metric.isCover_iff_subset_cthickening** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isCover_iff_subset_cthickening (hN : IsClosed N) : IsCover ε s N ↔ s subse
teq cthickening ε N
参数：hN : IsClosed N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.isCover_iff_subset_iUnion_closedBall`：isCover_iff_subset_iUnion_c
losedBall : IsCover ε s N ↔ s subseteq ⋃ y in N, closedBall y ε
· 使用定理 `IsClosed.cthickening_eq_biUnion_closedBall`：∀ {δ : ℝ} {α : Type u_2} [in
st : PseudoMetricSpace α] [ProperSpace α] {E : Set α},   IsClosed E → 0 ≤ δ → Me
tric.cthickening δ E = ⋃ x ∈ E, …
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCover_iff_subset_cthickening (hN : IsClosed N) : IsCover ε s N ↔ s ⊆ cthickening ε N := by
  rw [isCover_iff_subset_iUnion_closedBall, hN.cthickening_eq_biUnion_closedBall ε.zero_le_coe]

alias ⟨IsCover.subset_cthickening, IsCover.of_subset_cthickening⟩ := isCover_iff_subset_cthickening
/-
**Metric.isCover_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {ε : NNReal} {s N : Set X} [
ProperSpace X],   IsClosed N → (Metric.IsCover ε (closure s) N ↔ Metric.IsCover 
ε s N)
参数：Metric.IsCover ε (closure s) N ↔ Metric.IsCover ε s N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.isCover_iff_subset_cthickening`：isCover_iff_subset_cthickening (h
N : IsClosed N) : IsCover ε s N ↔ s subseteq cthickening ε N
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Metric.isClosed_cthickening`：isClosed_cthickening {δ : Real} {E : Set α}
 : IsClosed (cthickening δ E)
-/
@[simp] lemma isCover_closure (hN : IsClosed N) : IsCover ε (closure s) N ↔ IsCover ε s N := by
  simpa [isCover_iff_subset_cthickening hN] using (isClosed_cthickening (E := N)).closure_subset_iff

protected alias ⟨_, IsCover.closure⟩ := isCover_closure

end PseudoMetricSpace

section EMetricSpace
variable [EMetricSpace X] {ε : ℝ≥0} {s N : Set X} {x : X}

/-
**Metric.isCover_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {X : Type u_1} [inst : EMetricSpace X] {s N : Set X}, Metric.IsCover 0 s
 N ↔ s ⊆ N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Metric.closedEBall_zero`：∀ {γ : Type w} [inst : EMetricSpace γ] (x : γ),
 Metric.closedEBall x 0 = {x}
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isCover_zero : IsCover 0 s N ↔ s ⊆ N := by
  simp [isCover_iff_subset_iUnion_closedEBall]

end EMetricSpace

section MetricSpace
variable [MetricSpace X] [ProperSpace X] {ε : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

/-- A closed set in a proper metric space which admits a compact cover is compact. -/
/-
**Metric.IsCover.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover`。
形式化陈述：∀ {X : Type u_1} [inst : MetricSpace X] [ProperSpace X] {ε : NNReal} {s N 
: Set X},   Metric.IsCover ε s N → IsClosed s → IsCompact N → IsCompact s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.cthickening`：∀ {α : Type u_2} [inst : PseudoMetricSpace α] [Pr
operSpace α] {s : Set α},   IsCompact s → ∀ {r : ℝ}, IsCompact (Metric.cthickeni
ng r s)
· 使用定理 `Metric.IsCover.subset_cthickening`：∀ {X : Type u_1} [inst : PseudoMetric
Space X] {ε : NNReal} {s N : Set X} [ProperSpace X],   IsClosed N → Metric.IsCov
er ε s N → s ⊆ Metric.c…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
A closed set in a proper metric space which admits a compact cover is compact.
-/
lemma IsCover.isCompact (hsN : IsCover ε s N) (hs : IsClosed s) (hN : IsCompact N) :
    IsCompact s := .of_isClosed_subset hN.cthickening hs <| hsN.subset_cthickening hN.isClosed

/-- A set in a proper metric space which admits a compact cover is relatively compact. -/
/-
**Metric.IsCover.isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric.IsCover`。
形式化陈述：∀ {X : Type u_1} [inst : MetricSpace X] [ProperSpace X] {ε : NNReal} {s N 
: Set X},   Metric.IsCover ε s N → IsCompact N → IsCompact (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.isCompact`：∀ {X : Type u_1} [inst : MetricSpace X] [Prope
rSpace X] {ε : NNReal} {s N : Set X},   Metric.IsCover ε s N → IsClosed s → IsCo
mpact N → IsCo…
· 使用定理 `Metric.IsCover.closure`：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {ε
 : NNReal} {s N : Set X} [ProperSpace X],   IsClosed N → Metric.IsCover ε s N → 
Metric.IsCov…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
A set in a proper metric space which admits a compact cover is relatively compac
t.
-/
lemma IsCover.isCompact_closure (hsN : IsCover ε s N) (hN : IsCompact N) :
    IsCompact (closure s) := (hsN.closure hN.isClosed).isCompact isClosed_closure hN

/-- A set in a proper metric space admits a finite cover iff it is relatively compact.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.3. Note that the print
edition incorrectly claims that this holds without the `ProperSpace X` assumption. -/
/-
**Metric.isCompact_closure_iff_exists_finite_isCover** 是 Mathlib 中的一个引理，位于命名空间 `
Metric`。
形式化陈述：isCompact_closure_iff_exists_finite_isCover (hε : ε != 0) : IsCompact (clo
sure s) ↔ exists N subseteq s, N.Finite ∧ IsCover ε s N where mp
参数：hε : ε != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.exists_finite_isCover_of_isCompact_closure`：exists_finite_isCover
_of_isCompact_closure (hε : ε != 0) (hs : IsCompact (closure s)) : exists N subs
eteq s, N.Finite ∧ IsCover ε s N
· 使用定理 `Metric.IsCover.isCompact_closure`：∀ {X : Type u_1} [inst : MetricSpace X
] [ProperSpace X] {ε : NNReal} {s N : Set X},   Metric.IsCover ε s N → IsCompact
 N → IsCompact (closur…
· 使用定理 `Set.Finite.isCompact`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Finite → IsCompact s

--- 原说明 ---
A set in a proper metric space admits a finite cover iff it is relatively compac
t.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.3. Note t
hat the print
edition incorrectly claims that this holds without the `ProperSpace X` assumptio
n.
-/
lemma isCompact_closure_iff_exists_finite_isCover (hε : ε ≠ 0) :
    IsCompact (closure s) ↔ ∃ N ⊆ s, N.Finite ∧ IsCover ε s N where
  mp := exists_finite_isCover_of_isCompact_closure hε
  mpr := fun ⟨_N, _, hN, hsN⟩ ↦ hsN.isCompact_closure hN.isCompact

end MetricSpace
end Metric

