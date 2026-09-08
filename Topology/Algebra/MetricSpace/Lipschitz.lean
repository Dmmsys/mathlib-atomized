/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz continuous functions

This file develops Lipschitz continuous functions further with some results that depend on algebra.
-/

public section

assert_not_exists Module.Basis Ideal

open Filter Set NNReal Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}

/-
**LipschitzWith.cauchySeq_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzWith.cauchySeq_comp {f : α -> β} (hf : LipschitzWith K f) {u : Na
t -> α} (hu : CauchySeq u) : CauchySeq (f ∘ u)
参数：hf : LipschitzWith K f；hu : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_iff_le_tendsto_0`：cauchySeq_iff_le_tendsto_0 {s : Nat -> α} : 
CauchySeq s ↔ exists b : Nat -> Real, (forall n, 0 <= b n) ∧ (forall n m N : Nat
, N <= n -> N <=…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `LipschitzWith.dist_le_mul_of_le`：dist_le_mul_of_le (hf : LipschitzWith K
 f) (hr : dist x y <= r) : dist (f x) (f y) <= K * r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma LipschitzWith.cauchySeq_comp {f : α → β} (hf : LipschitzWith K f) {u : ℕ → α}
    (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · exact fun n m N hn hm ↦ hf.dist_le_mul_of_le (hb n m N hn hm)
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _
/-
**LipschitzOnWith.cauchySeq_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.cauchySeq_comp {s : Set α} {f : α -> β} (hf : LipschitzOnW
ith K f s) {u : Nat -> α} (hu : CauchySeq u) (h'u : range u subseteq s) : Cauchy
Seq (f ∘ u)
参数：hf : LipschitzOnWith K f s；hu : CauchySeq u；h'u : range u subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_iff_le_tendsto_0`：cauchySeq_iff_le_tendsto_0 {s : Nat -> α} : 
CauchySeq s ↔ exists b : Nat -> Real, (forall n, 0 <= b n) ∧ (forall n m N : Nat
, N <= n -> N <=…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzOnWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : α →
 β}, LipschitzOnW…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma LipschitzOnWith.cauchySeq_comp {s : Set α} {f : α → β} (hf : LipschitzOnWith K f s)
    {u : ℕ → α} (hu : CauchySeq u) (h'u : range u ⊆ s) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · intro n m N hn hm
    have A n : u n ∈ s := h'u (mem_range_self _)
    apply (hf.dist_le_mul _ (A n) _ (A m)).trans
    exact mul_le_mul_of_nonneg_left (hb n m N hn hm) K.2
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
/-
**continuousAt_of_locally_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_of_locally_lipschitz {f : α -> β} {x : α} {r : Real} (hr : 0 
< r) (K : Real) (h : forall y, dist y x < r -> dist (f y) (f x) <= K * dist y x)
 : ContinuousAt f x
参数：hr : 0 < r；K : Real；h : forall y, dist y x < r -> dist (f y) (f x) <= K * dis
t y x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用引理 `squeeze_zero'`：squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf :
 forallᶠ t in t₀, 0 <= f t) (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g 
t₀ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a function is locally Lipschitz around a point, then it is continuous at this
 point.
-/
theorem continuousAt_of_locally_lipschitz {f : α → β} {x : α} {r : ℝ} (hr : 0 < r) (K : ℝ)
    (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) : ContinuousAt f x := by
  -- We use `h` to squeeze `dist (f y) (f x)` between `0` and `K * dist y x`
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (mem_of_superset (ball_mem_nhds _ hr) h) ?_)
  -- Then show that `K * dist y x` tends to zero as `y → x`
  exact Continuous.tendsto' (by fun_prop) x 0 (by simp)

/-- If `f` is locally Lipschitz on a compact set `s`, it is Lipschitz on `s`. -/
/-
**LocallyLipschitzOn.exists_lipschitzOnWith_of_compact** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：LocallyLipschitzOn.exists_lipschitzOnWith_of_compact {f : α -> β} {s : Set
 α} (hs : IsCompact s) (hf : LocallyLipschitzOn s f) : exists K, LipschitzOnWith
 K f s
参数：hs : IsCompact s；hf : LocallyLipschitzOn s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitzOn.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α},   Lo
callyLipschitzOn s f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `IsCompact.bddAbove_image`：IsCompact.bddAbove_image [ClosedIciTopology α]
 [Nonempty α] {f : β -> α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K
) : BddAbove (…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsCompact.diff`：IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCo
mpact (s \ t)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `ContinuousOn.div`：ContinuousOn.div (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (h₀ : forall x in s, g x != 0) : ContinuousOn (f / g) s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 149 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is locally Lipschitz on a compact set `s`, it is Lipschitz on `s`.
-/
lemma LocallyLipschitzOn.exists_lipschitzOnWith_of_compact {f : α → β} {s : Set α}
    (hs : IsCompact s) (hf : LocallyLipschitzOn s f) : ∃ K, LipschitzOnWith K f s := by
  /- `f` being locally Lipschitz on `s` means that it is continuous and that it is Lipschitz on a
  ball of some radius `ε x hx` within `s` with Lipschitz bound `K x hx` around every `x ∈ s`. -/
  have hf' := hf.continuousOn
  replace hf : ∀ x ∈ s, ∃ ε > 0, ∃ K, LipschitzOnWith K f (ball x ε ∩ s) := fun x hx ↦ by
    let ⟨K, t, ht, hf⟩ := hf hx
    let ⟨ε, hε, hε'⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨ε, hε, K, hf.mono hε'⟩
  choose ε hε K hf using hf
  /- We also have constants `K' x hx` for all `x ∈ s` such that `edist (f x) (f y) ≤ K' * edist x y`
  for all `y ∈ s` outside of `ball x (ε x hx)`, by continuity of
  `fun y ↦ dist (f x) (f y) / dist x y` on the compact set `s.diff (ball x (ε x hx))`. -/
  have (x) (hx : x ∈ s) : ∃ K' : ℝ≥0, ∀ y ∈ s.diff (ball x (ε x hx)),
      edist (f x) (f y) ≤ K' * edist x y := by
    let ⟨K', hK'⟩ := (hs.diff isOpen_ball).bddAbove_image
      (f := fun y ↦ dist (f x) (f y) / dist x y) <| .div (.mono (by fun_prop) s.sdiff_subset)
        (by fun_prop) fun y hy ↦ ((hε x hx).trans_le <| not_lt.1 <| dist_comm x y ▸ hy.2).ne'
    refine ⟨.mk (K' ⊔ 0) le_sup_right, fun y hy ↦ ?_⟩
    simp_rw [edist_nndist, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    refine (div_le_iff₀ ?_).1 ?_
    · exact NNReal.coe_pos.1 <| coe_nndist x y ▸
        ((hε x hx).trans_le <| not_lt.1 <| dist_comm x y ▸ hy.2)
    · simp [← NNReal.coe_le_coe, (mem_upperBounds.1 hK') _ <| mem_image_of_mem _ hy]
  choose K' hK' using this
  /- By compactness of `s`, there exists some finite set `t` such that the balls of radius
  `ε x hx / 2` around all `x ∈ t` cover `s`. -/
  obtain ⟨t, ht⟩ := hs.elim_nhdsWithin_subcover' (fun x hx ↦ s ∩ ball x (ε x hx / 2))
    (fun x hx ↦ inter_mem_nhdsWithin s <| ball_mem_nhds x <| half_pos <| hε x hx)
  /- For every `z ∈ t` we can show that `f` satisfies the Lipschitz condition with bound
  `K z hz + 2 * K' z hz` for all points `x ∈ s ∩ ball z (ε z hz / 2)` and `y ∈ s`, so `f` is
  Lipschitz on `s` with the supremum of these bounds over all `z ∈ t` as its bound. -/
  use t.sup fun i ↦ K _ i.2 + 2 * K' _ i.2
  intro x hx y hy
  let ⟨z, hz, hx'⟩ := mem_iUnion₂.1 <| ht hx
  by_cases hy' : y ∈ ball z.1 (ε _ z.2)
  · /- For `y ∈ ball z (ε z hz)` this follows from `f` being Lipschitz with bound `K z hz`
    on `ball z (ε z hz)`. -/
    refine (hf _ z.2 ⟨hx'.2.trans <| half_lt_self <| hε _ z.2, hx⟩ ⟨hy', hy⟩).trans <|
      mul_le_mul_of_nonneg_right ?_ zero_le
    exact ENNReal.coe_le_coe.2 <| t.le_sup_of_le hz <| le_self_add
  · /- For `y ∉ ball z (ε z hz)` this follows by using the triangle inequality, bounding
    the distances from `f z` to `f x` and `f y` using the bounds `K z hz` and `K' z hz`, and then
    using the triangle inequality again for `edist z y ≤ edist x z + edist x y ≤ 2 * edist x y`. -/
    calc edist (f x) (f y)
      _ ≤ edist (f z) (f x) + edist (f z) (f y) := edist_triangle_left _ _ _
      _ ≤ (K _ z.2) * edist z.1 x + edist (f z) (f y) := add_le_add_left
        (hf _ z.2 ⟨mem_ball_self <| hε _ z.2, z.2⟩ ⟨hx'.2.trans <| half_lt_self <| hε _ z.2, hx⟩) _
      _ ≤ (K _ z.2) * edist z.1 x + (K' _ z.2) * edist z.1 y :=
        add_le_add_right (hK' _ z.2 _ ⟨hy, hy'⟩) _
      _ ≤ (K _ z.2) * edist z.1 x + (K' _ z.2) * (edist x z.1 + edist x y) := by
        gcongr; exact edist_triangle_left z.1 y x
      _ ≤ (K _ z.2) * edist x y + (K' _ z.2) * (edist x y + edist x y) := by
        simp_rw [edist_dist, dist_comm _ x]
        gcongr <;> linarith [mem_ball.1 hx'.2, (not_lt (α := ℝ)).1 hy', dist_triangle_left y z x]
      _ = ↑(K _ z.2 + 2 * K' _ z.2) * edist x y := by push_cast; ring
      _ ≤ _ := by gcongr; exact .trans (by rfl) (t.le_sup hz)
