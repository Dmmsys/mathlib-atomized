/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals against peak functions

A sequence of peak functions is a sequence of functions with average one concentrating around
a point `x₀`. Given such a sequence `φₙ`, then `∫ φₙ g` tends to `g x₀` in many situations, with
a whole zoo of possible assumptions on `φₙ` and `g`. This file is devoted to such results. Such
functions are also called approximations of unity, or approximations of identity.

## Main results

* `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`: If a sequence of peak
  functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
  `g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `g x₀`.
* `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`:
  If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
  then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
  concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀`
  if `g` is continuous on `s`.
* `tendsto_integral_comp_smul_smul_of_integrable`:
  If a nonnegative function `φ` has integral one and decays quickly enough at infinity,
  then its renormalizations `x ↦ c ^ d * φ (c • x)` form a sequence of peak functions as `c → ∞`.
  Therefore, `∫ (c ^ d * φ (c • x)) • g x` converges to `g 0` as `c → ∞` if `g` is continuous
  at `0` and integrable.

Note that there are related results about convolution with respect to peak functions in the file
`Mathlib/Analysis/Convolution.lean`, such as `MeasureTheory.convolution_tendsto_right` there.
-/

public section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open scoped Topology ENNReal

/-!
### General convergent result for integrals against a sequence of peak functions
-/

open Set

variable {α E ι : Type*} {hm : MeasurableSpace α} {μ : Measure α} [TopologicalSpace α]
  [BorelSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] {g : α → E} {l : Filter ι} {x₀ : α}
  {s t : Set α} {φ : ι → α → ℝ} {a : E}

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and has a limit at `x₀`, then `φᵢ • g` is eventually integrable. -/
/-
**integrableOn_peak_smul_of_integrableOn_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：integrableOn_peak_smul_of_integrableOn_of_tendsto (hs : MeasurableSet s) (
h'st : t in 𝓝[s] x₀) (hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUnif
ormlyOn φ 0 l (s \ u)) (hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1)) (h'
iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s)) (hmg : Integrabl
eOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) : forallᶠ i in l, IntegrableOn (fun
 x => φ i x • g x) s μ
参数：hs : MeasurableSet s；h'st : t in 𝓝[s] x₀；hlφ : forall u : Set α, IsOpen u -> 
x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u)；hiφ : Tendsto (fun i => ∫ x in t, φ 
i x ∂μ) l (𝓝 1)；h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s)
；hmg : IntegrableOn g s μ；hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Integrable.of_integral_ne_zero`：∀ {α : Type u_1} {G : Type
 u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSp
ace α}   {μ : MeasureTheory.Measur…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `MeasureTheory.Integrable.smul_of_top_right`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If a sequence of peak functions `φᵢ` converges uniformly to zero away from a poi
nt `x₀`, and
`g` is integrable and has a limit at `x₀`, then `φᵢ • g` is eventually integrabl
e.
-/
theorem integrableOn_peak_smul_of_integrableOn_of_tendsto
    (hs : MeasurableSet s) (h'st : t ∈ 𝓝[s] x₀)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) :
    ∀ᶠ i in l, IntegrableOn (fun x => φ i x • g x) s μ := by
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ t ∧ ∀ x ∈ u ∩ s, g x ∈ ball a 1 := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'st (hcg (ball_mem_nhds _ zero_lt_one)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.trans inter_subset_right⟩
    rw [inter_comm]
    exact hu.trans inter_subset_left
  rw [tendsto_iff_norm_sub_tendsto_zero] at hiφ
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) 1 zero_lt_one,
    (tendsto_order.1 hiφ).2 1 zero_lt_one, h'iφ] with i hi h'i h''i
  have I : IntegrableOn (φ i) t μ := .of_integral_ne_zero (fun h ↦ by simp [h] at h'i)
  have A : IntegrableOn (fun x => φ i x • g x) (s \ u) μ := by
    refine Integrable.smul_of_top_right (hmg.mono sdiff_subset le_rfl) ?_
    apply memLp_top_of_bound (h''i.mono_set sdiff_subset) 1
    filter_upwards [self_mem_ae_restrict (hs.diff u_open.measurableSet)] with x hx
    simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
  have B : IntegrableOn (fun x => φ i x • g x) (s ∩ u) μ := by
    apply Integrable.smul_of_top_left
    · exact IntegrableOn.mono_set I ut
    · apply
        memLp_top_of_bound (hmg.mono_set inter_subset_left).aestronglyMeasurable (‖a‖ + 1)
      filter_upwards [self_mem_ae_restrict (hs.inter u_open.measurableSet)] with x hx
      rw [inter_comm] at hx
      exact (norm_lt_of_mem_ball (hu x hx)).le
  convert! A.union B
  simp only [sdiff_union_inter]

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` is integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`.
Auxiliary lemma where one assumes additionally `a = 0`. -/
/-
**tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux (hs : Measura
bleSet s) (ht : MeasurableSet t) (hts : t subseteq s) (h'ts : t in 𝓝[s] x₀) (hnφ
 : forallᶠ i in l, forall x in s, 0 <= φ i x) (hlφ : forall u : Set α, IsOpen u 
-> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u)) (hiφ : Tendsto (fun i => ∫ x in 
t, φ i x ∂μ) l (𝓝 1)) (h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.rest
rict s)) (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 0)) : Tendsto 
(fun i : ι => ∫ x in s, φ 
参数：hs : MeasurableSet s；ht : MeasurableSet t；hts : t subseteq s；h'ts : t in 𝓝[s]
 x₀；hnφ : forallᶠ i in l, forall x in s, 0 <= φ i x；hlφ : forall u : Set α, IsOp
en u -> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u)；hiφ : Tendsto (fun i => ∫ x 
in t, φ i x ∂μ) l (𝓝 1)；h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.res
trict s)；hmg : IntegrableOn g s μ；hcg : Tendsto g (𝓝[s] x₀) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 137 条，此处仅展示前 30 条）

--- 原说明 ---
If a sequence of peak functions `φᵢ` converges uniformly to zero away from a poi
nt `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` i
s integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`.
Auxiliary lemma where one assumes additionally `a = 0`.
-/
theorem tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s) (h'ts : t ∈ 𝓝[s] x₀)
    (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 0)) :
    Tendsto (fun i : ι => ∫ x in s, φ i x • g x ∂μ) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε εpos => ?_
  obtain ⟨δ, hδ, δpos, δone⟩ : ∃ δ, (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ < ε ∧ 0 < δ ∧ δ < 1 := by
    have A :
      Tendsto (fun δ => (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ) (𝓝[>] 0)
        (𝓝 ((0 * ∫ x in s, ‖g x‖ ∂μ) + 2 * 0)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (tendsto_id.mul tendsto_const_nhds).add (tendsto_id.const_mul _)
    rw [zero_mul, zero_add, mul_zero] at A
    have : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT zero_lt_one
    rcases (((tendsto_order.1 A).2 ε εpos).and this).exists with ⟨δ, hδ, h'δ⟩
    exact ⟨δ, hδ, h'δ.1, h'δ.2⟩
  suffices ∀ᶠ i in l, ‖∫ x in s, φ i x • g x ∂μ‖ ≤ (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ by
    filter_upwards [this] with i hi
    simp only [dist_zero_right]
    exact hi.trans_lt hδ
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ t ∧ ∀ x ∈ u ∩ s, g x ∈ ball 0 δ := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'ts (hcg (ball_mem_nhds _ δpos)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.trans inter_subset_right⟩
    rw [inter_comm]
    exact hu.trans inter_subset_left
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) δ δpos,
    (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hiφ)).2 δ δpos, hnφ,
    integrableOn_peak_smul_of_integrableOn_of_tendsto hs h'ts hlφ hiφ h'iφ hmg hcg]
    with i hi h'i hφpos h''i
  have I : IntegrableOn (φ i) t μ := by
    apply Integrable.of_integral_ne_zero (fun h ↦ ?_)
    simp [h] at h'i
    linarith
  have B : ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ 2 * δ :=
    calc
      ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ ∫ x in s ∩ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in s ∩ u, ‖φ i x‖ * δ ∂μ := by
        refine setIntegral_mono_on ?_ ?_ (hs.inter u_open.measurableSet) fun x hx => ?_
        · exact IntegrableOn.mono_set h''i.norm inter_subset_left
        · exact IntegrableOn.mono_set (I.norm.mul_const _) ut
        rw [norm_smul]
        gcongr
        rw [inter_comm] at hu
        exact (mem_ball_zero_iff.1 (hu x hx)).le
      _ ≤ ∫ x in t, ‖φ i x‖ * δ ∂μ := by
        apply setIntegral_mono_set
        · exact I.norm.mul_const _
        · exact Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) δpos.le
        · exact Eventually.of_forall ut
      _ = ∫ x in t, φ i x * δ ∂μ := by
        apply setIntegral_congr_fun ht fun x hx => ?_
        rw [Real.norm_of_nonneg (hφpos _ (hts hx))]
      _ = (∫ x in t, φ i x ∂μ) * δ := by rw [integral_mul_const]
      _ ≤ 2 * δ := by gcongr; linarith [(le_abs_self _).trans h'i.le]
  have C : ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ :=
    calc
      ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ ∫ x in s \ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in s \ u, δ * ‖g x‖ ∂μ := by
        refine setIntegral_mono_on ?_ ?_ (hs.diff u_open.measurableSet) fun x hx => ?_
        · exact IntegrableOn.mono_set h''i.norm sdiff_subset
        · exact IntegrableOn.mono_set (hmg.norm.const_mul _) sdiff_subset
        rw [norm_smul]
        gcongr
        simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
      _ ≤ δ * ∫ x in s, ‖g x‖ ∂μ := by
        rw [integral_const_mul]
        apply mul_le_mul_of_nonneg_left (setIntegral_mono_set hmg.norm _ _) δpos.le
        · filter_upwards with x using norm_nonneg _
        · filter_upwards using sdiff_subset (s := s) (t := u)
  calc
    ‖∫ x in s, φ i x • g x ∂μ‖ =
      ‖(∫ x in s \ u, φ i x • g x ∂μ) + ∫ x in s ∩ u, φ i x • g x ∂μ‖ := by
      conv_lhs => rw [← sdiff_union_inter s u]
      rw [setIntegral_union disjoint_sdiff_inter (hs.inter u_open.measurableSet)
          (h''i.mono_set sdiff_subset) (h''i.mono_set inter_subset_left)]
    _ ≤ ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ := norm_add_le _ _
    _ ≤ (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ := add_le_add C B

variable [CompleteSpace E]

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` is integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`. Version localized to a subset. -/
/-
**tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto (hs : MeasurableS
et s) {t : Set α} (ht : MeasurableSet t) (hts : t subseteq s) (h'ts : t in 𝓝[s] 
x₀) (h't : μ t != ∞) (hnφ : forallᶠ i in l, forall x in s, 0 <= φ i x) (hlφ : fo
rall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u)) (hiφ : 
Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1)) (h'iφ : forallᶠ i in l, AEStrongl
yMeasurable (φ i) (μ.restrict s)) (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝
[s] x₀) (𝓝 a)) : Tendsto (
参数：hs : MeasurableSet s；ht : MeasurableSet t；hts : t subseteq s；h'ts : t in 𝓝[s]
 x₀；h't : μ t != ∞；hnφ : forallᶠ i in l, forall x in s, 0 <= φ i x；hlφ : forall 
u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u)；hiφ : Tendsto
 (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1)；h'iφ : forallᶠ i in l, AEStronglyMeasurab
le (φ i) (μ.restrict s)；hmg : IntegrableOn g s μ；hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux`：tendsto_se
tIntegral_peak_smul_of_integrableOn_of_tendsto_aux (hs : MeasurableSet s) (ht : 
MeasurableSet t) (hts : t subseteq s) (h'ts : t in…
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integrableOn_indicator_iff`：integrableOn_indicator_iff (hs
 : MeasurableSet s) : IntegrableOn (indicator s f) t μ ↔ IntegrableOn f (s inter
 t) μ
· 使用定理 `MeasureTheory.integrableOn_const_iff`：integrableOn_const_iff {C : ε'} (h
C : ‖C‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If a sequence of peak functions `φᵢ` converges uniformly to zero away from a poi
nt `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` i
s integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`. Version localized to 
a subset.
-/
theorem tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet t) (hts : t ⊆ s) (h'ts : t ∈ 𝓝[s] x₀)
    (h't : μ t ≠ ∞) (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) :
    Tendsto (fun i : ι ↦ ∫ x in s, φ i x • g x ∂μ) l (𝓝 a) := by
  let h := g - t.indicator (fun _ ↦ a)
  have A : Tendsto (fun i : ι => (∫ x in s, φ i x • h x ∂μ) + (∫ x in t, φ i x ∂μ) • a) l
      (𝓝 (0 + (1 : ℝ) • a)) := by
    refine Tendsto.add ?_ (Tendsto.smul hiφ tendsto_const_nhds)
    apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux hs ht hts h'ts
        hnφ hlφ hiφ h'iφ
    · apply hmg.sub
      simp only [integrableOn_indicator_iff ht, integrableOn_const_iff (C := a)]
      right
      exact lt_of_le_of_lt (measure_mono inter_subset_left) (h't.lt_top)
    · rw [← sub_self a]
      apply Tendsto.sub hcg
      apply tendsto_const_nhds.congr'
      filter_upwards [h'ts] with x hx using by simp [hx]
  simp only [one_smul, zero_add] at A
  refine Tendsto.congr' ?_ A
  filter_upwards [integrableOn_peak_smul_of_integrableOn_of_tendsto hs h'ts
    hlφ hiφ h'iφ hmg hcg,
    (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hiφ)).2 1 zero_lt_one] with i hi h'i
  simp only [h, Pi.sub_apply, smul_sub, ← indicator_smul_apply]
  rw [integral_sub hi, setIntegral_indicator ht, inter_eq_right.mpr hts,
    integral_smul_const, sub_add_cancel]
  rw [integrable_indicator_iff ht]
  apply Integrable.smul_const
  rw [restrict_restrict ht, inter_eq_left.mpr hts]
  exact .of_integral_ne_zero (fun h ↦ by simp [h] at h'i)

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` is integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`. -/
/-
**tendsto_integral_peak_smul_of_integrable_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：tendsto_integral_peak_smul_of_integrable_of_tendsto {t : Set α} (ht : Meas
urableSet t) (h'ts : t in 𝓝 x₀) (h't : μ t != ∞) (hnφ : forallᶠ i in l, forall x
, 0 <= φ i x) (hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn
 φ 0 l uᶜ) (hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1)) (h'iφ : forallᶠ
 i in l, AEStronglyMeasurable (φ i) μ) (hmg : Integrable g μ) (hcg : Tendsto g (
𝓝 x₀) (𝓝 a)) : Tendsto (fun i : ι => ∫ x, φ i x • g x ∂μ) l (𝓝 a)
参数：ht : MeasurableSet t；h'ts : t in 𝓝 x₀；h't : μ t != ∞；hnφ : forallᶠ i in l, fo
rall x, 0 <= φ i x；hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniform
lyOn φ 0 l uᶜ；hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1)；h'iφ : forallᶠ
 i in l, AEStronglyMeasurable (φ i) μ；hmg : Integrable g μ；hcg : Tendsto g (𝓝 x₀
) (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`：tendsto_setInt
egral_peak_smul_of_integrableOn_of_tendsto (hs : MeasurableSet s) {t : Set α} (h
t : MeasurableSet t) (hts : t subseteq s) (h't…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ

--- 原说明 ---
If a sequence of peak functions `φᵢ` converges uniformly to zero away from a poi
nt `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` i
s integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`.
-/
theorem tendsto_integral_peak_smul_of_integrable_of_tendsto
    {t : Set α} (ht : MeasurableSet t) (h'ts : t ∈ 𝓝 x₀)
    (h't : μ t ≠ ∞) (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l uᶜ)
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) μ)
    (hmg : Integrable g μ) (hcg : Tendsto g (𝓝 x₀) (𝓝 a)) :
    Tendsto (fun i : ι ↦ ∫ x, φ i x • g x ∂μ) l (𝓝 a) := by
  suffices Tendsto (fun i : ι ↦ ∫ x in univ, φ i x • g x ∂μ) l (𝓝 a) by simpa
  exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto MeasurableSet.univ ht (x₀ := x₀)
    (subset_univ _) (by simpa [nhdsWithin_univ]) h't (by simpa)
    (by simpa [← compl_eq_univ_sdiff] using hlφ) hiφ
    (by simpa) (by simpa) (by simpa [nhdsWithin_univ])

/-!
### Peak functions of the form `x ↦ (c x) ^ n / ∫ (c y) ^ n`
-/

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all neighborhoods of `x₀` within `s`.
For a less precise but more usable version, see
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
/-
**tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWit
hin_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhd
sWithin_pos [MetrizableSpace α] [IsLocallyFiniteMeasure μ] (hs : IsCompact s) (h
μ : forall u, IsOpen u -> x₀ in u -> 0 < μ (u inter s)) {c : α -> Real} (hc : Co
ntinuousOn c s) (h'c : forall y in s, y != x₀ -> c y < c x₀) (hnc : forall x in 
s, 0 <= c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ in s) (hmg : IntegrableOn g s μ) (hcg : 
ContinuousWithinAt g s x₀) : Tendsto (fun n : Nat => (∫ x in s, c x ^ n ∂μ)⁻¹ • 
∫ x in s, c x ^ n • g x ∂μ
参数：hs : IsCompact s；hμ : forall u, IsOpen u -> x₀ in u -> 0 < μ (u inter s)；hc :
 ContinuousOn c s；h'c : forall y in s, y != x₀ -> c y < c x₀；hnc : forall x in s
, 0 <= c x；hnc₀ : 0 < c x₀；h₀ : x₀ in s；hmg : IntegrableOn g s μ；hcg : Continuou
sWithinAt g s x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasureTheory.setIntegral_nonneg`：setIntegral_nonneg (hs : MeasurableSet
 s) (hf : forall x, x in s -> 0 <= f x) : 0 <= ∫ x in s, f x ∂μ
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `ContinuousOn.integrableOn_compact`：ContinuousOn.integrableOn_compact [T2
Space X] (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `ContinuousOn.pow`：ContinuousOn.pow {f : X -> M} {s : Set X} (hf : Contin
uousOn f s) (n : Nat) : ContinuousOn (f ^ n) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`：setIntegral_pos_
iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : Int
egrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff`：continuousOn_iff : ContinuousOn f s ↔ forall x in s, f
orall t : Set β, IsOpen t -> f x in t -> exists u, IsOpen u ∧ x in u ∧ u inter s
 subse…
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
If a continuous function `c` realizes its maximum at a unique point `x₀` in a co
mpact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak f
unctions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges 
to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all neighborhoods of `x₀` withi
n `s`.
For a less precise but more usable version, see
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] (hs : IsCompact s)
    (hμ : ∀ u, IsOpen u → x₀ ∈ u → 0 < μ (u ∩ s)) {c : α → ℝ} (hc : ContinuousOn c s)
    (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀) (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ s)
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  /- We apply the general result
    `tendsto_setIntegral_peak_smul_of_integrableOn_of_continuousWithinAt` to the sequence of
    peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
    sequence converges uniformly to zero on any set `s \ u` away from `x₀`. By compactness, the
    function `c` is bounded by `t < c x₀` there. Consider `t' ∈ (t, c x₀)`, and a neighborhood `v`
    of `x₀` where `c x ≥ t'`, by continuity. Then `∫ (c x) ^ n` is bounded below by `t' ^ n μ v`.
    It follows that, on `s \ u`, then `φₙ x ≤ t ^ n / (t' ^ n μ v)`,
    which tends (exponentially fast) to zero with `n`. -/
  let φ : ℕ → α → ℝ := fun n x => (∫ x in s, c x ^ n ∂μ)⁻¹ * c x ^ n
  have hnφ : ∀ n, ∀ x ∈ s, 0 ≤ φ n x := by
    intro n x hx
    apply mul_nonneg (inv_nonneg.2 _) (pow_nonneg (hnc x hx) _)
    exact setIntegral_nonneg hs.measurableSet fun x hx => pow_nonneg (hnc x hx) _
  have I : ∀ n, IntegrableOn (fun x => c x ^ n) s μ := fun n =>
    ContinuousOn.integrableOn_compact hs (hc.pow n)
  have J : ∀ n, 0 ≤ᵐ[μ.restrict s] fun x : α => c x ^ n := by
    intro n
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    exact pow_nonneg (hnc x hx) n
  have P : ∀ n, (0 : ℝ) < ∫ x in s, c x ^ n ∂μ := by
    intro n
    refine (setIntegral_pos_iff_support_of_nonneg_ae (J n) (I n)).2 ?_
    obtain ⟨u, u_open, x₀_u, hu⟩ : ∃ u : Set α, IsOpen u ∧ x₀ ∈ u ∧ u ∩ s ⊆ c ⁻¹' Ioi 0 :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi (0 : ℝ)) isOpen_Ioi hnc₀
    apply (hμ u u_open x₀_u).trans_le
    exact measure_mono fun x hx => ⟨ne_of_gt (pow_pos (a := c x) (hu hx) _), hx.2⟩
  have hiφ : ∀ n, ∫ x in s, φ n x ∂μ = 1 := fun n => by
    rw [integral_const_mul, inv_mul_cancel₀ (P n).ne']
  have A : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 atTop (s \ u) := by
    intro u u_open x₀u
    obtain ⟨t, t_pos, tx₀, ht⟩ : ∃ t, 0 ≤ t ∧ t < c x₀ ∧ ∀ x ∈ s \ u, c x ≤ t := by
      rcases eq_empty_or_nonempty (s \ u) with (h | h)
      · exact
          ⟨0, le_rfl, hnc₀, by simp only [h, mem_empty_iff_false, IsEmpty.forall_iff, imp_true_iff]⟩
      obtain ⟨x, hx, h'x⟩ : ∃ x ∈ s \ u, ∀ y ∈ s \ u, c y ≤ c x :=
        IsCompact.exists_isMaxOn (hs.diff u_open) h (hc.mono sdiff_subset)
      refine ⟨c x, hnc x hx.1, h'c x hx.1 ?_, h'x⟩
      rintro rfl
      exact hx.2 x₀u
    obtain ⟨t', tt', t'x₀⟩ : ∃ t', t < t' ∧ t' < c x₀ := exists_between tx₀
    have t'_pos : 0 < t' := t_pos.trans_lt tt'
    obtain ⟨v, v_open, x₀_v, hv⟩ : ∃ v : Set α, IsOpen v ∧ x₀ ∈ v ∧ v ∩ s ⊆ c ⁻¹' Ioi t' :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi t') isOpen_Ioi t'x₀
    have M : ∀ n, ∀ x ∈ s \ u, φ n x ≤ (μ.real (v ∩ s))⁻¹ * (t / t') ^ n := by
      intro n x hx
      have B : t' ^ n * μ.real (v ∩ s) ≤ ∫ y in s, c y ^ n ∂μ :=
        calc
          t' ^ n * μ.real (v ∩ s) = ∫ _ in v ∩ s, t' ^ n ∂μ := by simp [mul_comm]
          _ ≤ ∫ y in v ∩ s, c y ^ n ∂μ := by
            apply setIntegral_mono_on _ _ (v_open.measurableSet.inter hs.measurableSet) _
            · refine integrableOn_const (C := t' ^ n) ?_
              exact (lt_of_le_of_lt (measure_mono inter_subset_right) hs.measure_lt_top).ne
            · exact (I n).mono inter_subset_right le_rfl
            · intro x hx
              exact pow_le_pow_left₀ t'_pos.le (hv hx).le _
          _ ≤ ∫ y in s, c y ^ n ∂μ :=
            setIntegral_mono_set (I n) (J n) (Eventually.of_forall inter_subset_right)
      simp_rw [φ, ← div_eq_inv_mul, div_pow, div_div]
      have := ENNReal.toReal_pos (hμ v v_open x₀_v).ne'
        ((measure_mono inter_subset_right).trans_lt hs.measure_lt_top).ne
      gcongr
      · exact hnc _ hx.1
      · exact ht x hx
    have N :
      Tendsto (fun n => (μ.real (v ∩ s))⁻¹ * (t / t') ^ n) atTop
        (𝓝 ((μ.real (v ∩ s))⁻¹ * 0)) := by
      apply Tendsto.mul tendsto_const_nhds _
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg t_pos t'_pos.le)
      exact (div_lt_one t'_pos).2 tt'
    rw [mul_zero] at N
    refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
    filter_upwards [(tendsto_order.1 N).2 ε εpos] with n hn x hx
    simp only [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (hnφ n x hx.1)]
    exact (M n x hx).trans_lt hn
  have : Tendsto (fun i : ℕ => ∫ x : α in s, φ i x • g x ∂μ) atTop (𝓝 (g x₀)) := by
    have B : Tendsto (fun i ↦ ∫ (x : α) in s, φ i x ∂μ) atTop (𝓝 1) :=
      tendsto_const_nhds.congr (fun n ↦ (hiφ n).symm)
    have C : ∀ᶠ (i : ℕ) in atTop, AEStronglyMeasurable (fun x ↦ φ i x) (μ.restrict s) := by
      apply Eventually.of_forall (fun n ↦ ((I n).const_mul _).aestronglyMeasurable)
    exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto hs.measurableSet
      hs.measurableSet (Subset.rfl) (self_mem_nhdsWithin)
      hs.measure_lt_top.ne (Eventually.of_forall hnφ) A B C hmg hcg
  convert! this
  simp_rw [φ, ← smul_smul, integral_smul]

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all open sets.
For a less precise but more usable version, see
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
/-
**tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableO
n [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCo
mpact s) {c : α -> Real} (hc : ContinuousOn c s) (h'c : forall y in s, y != x₀ -
> c y < c x₀) (hnc : forall x in s, 0 <= c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ in clos
ure (interior s)) (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
 Tendsto (fun n : Nat => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) 
atTop (𝓝 (g x₀))
参数：hs : IsCompact s；hc : ContinuousOn c s；h'c : forall y in s, y != x₀ -> c y < 
c x₀；hnc : forall x in s, 0 <= c x；hnc₀ : 0 < c x₀；h₀ : x₀ in closure (interior 
s)；hmg : IntegrableOn g s μ；hcg : ContinuousWithinAt g s x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_n
hdsWithin_pos`：tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_me
asure_nhdsWithin_pos [MetrizableSpace α] [IsLocallyFiniteMeasure μ] (hs : I…
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If a continuous function `c` realizes its maximum at a unique point `x₀` in a co
mpact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak f
unctions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges 
to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all open sets.
For a less precise but more usable version, see
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α → ℝ} (hc : ContinuousOn c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
    (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop
      (𝓝 (g x₀)) := by
  have : x₀ ∈ s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  apply
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos hs _ hc
      h'c hnc hnc₀ this hmg hcg
  intro u u_open x₀_u
  calc
    0 < μ (u ∩ interior s) :=
      (u_open.inter isOpen_interior).measure_pos μ (_root_.mem_closure_iff.1 h₀ u u_open x₀_u)
    _ ≤ μ (u ∩ s) := by gcongr; apply interior_subset

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
continuous on `s`. -/
/-
**tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousO
n [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCo
mpact s) {c : α -> Real} (hc : ContinuousOn c s) (h'c : forall y in s, y != x₀ -
> c y < c x₀) (hnc : forall x in s, 0 <= c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ in clos
ure (interior s)) (hmg : ContinuousOn g s) : Tendsto (fun n : Nat => (∫ x in s, 
c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop (𝓝 (g x₀))
参数：hs : IsCompact s；hc : ContinuousOn c s；h'c : forall y in s, y != x₀ -> c y < 
c x₀；hnc : forall x in s, 0 <= c x；hnc₀ : 0 < c x₀；h₀ : x₀ in closure (interior 
s)；hmg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrabl
eOn`：tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
 [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure…
· 使用定理 `ContinuousOn.integrableOn_compact`：ContinuousOn.integrableOn_compact [T2
Space X] (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If a continuous function `c` realizes its maximum at a unique point `x₀` in a co
mpact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak f
unctions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges 
to `g x₀` if `g` is
continuous on `s`.
-/
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α → ℝ} (hc : ContinuousOn c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
    (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
    (hmg : ContinuousOn g s) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop (𝓝 (g x₀)) :=
  haveI : x₀ ∈ s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn hs hc h'c hnc hnc₀ h₀
    (hmg.integrableOn_compact hs) (hmg x₀ this)

/-!
### Peak functions of the form `x ↦ c ^ dim * φ (c x)`
-/

open Module Bornology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [IsAddHaarMeasure μ]

/-- Consider a nonnegative function `φ` with integral one, decaying quickly enough at infinity.
Then suitable renormalizations of `φ` form a sequence of peak functions around the origin:
`∫ (c ^ d * φ (c • x)) • g x` converges to `g 0` as `c → ∞` if `g` is continuous at `0`
and integrable. -/
/-
**tendsto_integral_comp_smul_smul_of_integrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_comp_smul_smul_of_integrable {φ : F -> Real} (hφ : forall
 x, 0 <= φ x) (h'φ : ∫ x, φ x ∂μ = 1) (h : Tendsto (fun x => ‖x‖ ^ finrank Real 
F * φ x) (cobounded F) (𝓝 0)) {g : F -> E} (hg : Integrable g μ) (h'g : Continuo
usAt g 0) : Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ (c • x)) •
 g x ∂μ) atTop (𝓝 (g 0))
参数：hφ : forall x, 0 <= φ x；h'φ : ∫ x, φ x ∂μ = 1；h : Tendsto (fun x => ‖x‖ ^ fin
rank Real F * φ x) (cobounded F) (𝓝 0)；hg : Integrable g μ；h'g : ContinuousAt g 
0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_of_integral_eq_one`：integrable_of_integral_eq_o
ne {f : α -> Real} (h : ∫ x, f x ∂μ = 1) : Integrable f μ
· 使用定理 `tendsto_integral_peak_smul_of_integrable_of_tendsto`：tendsto_integral_pe
ak_smul_of_integrable_of_tendsto {t : Set α} (ht : MeasurableSet t) (h'ts : t in
 𝓝 x₀) (h't : μ t != ∞) (hnφ : forallᶠ i …
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsCompact.measure_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.hasBasis_cobounded_compl_closedBall`：hasBasis_cobounded_compl_clo
sedBall (c : α) : (cobounded α).HasBasis (fun _ => True) (fun r => (closedBall c
 r)ᶜ)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 116 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a nonnegative function `φ` with integral one, decaying quickly enough a
t infinity.
Then suitable renormalizations of `φ` form a sequence of peak functions around t
he origin:
`∫ (c ^ d * φ (c • x)) • g x` converges to `g 0` as `c → ∞` if `g` is continuous
 at `0`
and integrable.
-/
theorem tendsto_integral_comp_smul_smul_of_integrable
    {φ : F → ℝ} (hφ : ∀ x, 0 ≤ φ x) (h'φ : ∫ x, φ x ∂μ = 1)
    (h : Tendsto (fun x ↦ ‖x‖ ^ finrank ℝ F * φ x) (cobounded F) (𝓝 0))
    {g : F → E} (hg : Integrable g μ) (h'g : ContinuousAt g 0) :
    Tendsto (fun (c : ℝ) ↦ ∫ x, (c ^ (finrank ℝ F) * φ (c • x)) • g x ∂μ) atTop (𝓝 (g 0)) := by
  have I : Integrable φ μ := integrable_of_integral_eq_one h'φ
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto (t := closedBall 0 1) (x₀ := 0)
  · exact isClosed_closedBall.measurableSet
  · exact closedBall_mem_nhds _ zero_lt_one
  · exact (isCompact_closedBall 0 1).measure_ne_top
  · filter_upwards [Ici_mem_atTop 0] with c (hc : 0 ≤ c) x using mul_nonneg (by positivity) (hφ _)
  · intro u u_open hu
    apply tendstoUniformlyOn_iff.2 (fun ε εpos ↦ ?_)
    obtain ⟨δ, δpos, h'u⟩ : ∃ δ > 0, ball 0 δ ⊆ u := Metric.isOpen_iff.1 u_open _ hu
    obtain ⟨M, Mpos, hM⟩ : ∃ M > 0, ∀ ⦃x : F⦄, x ∈ (closedBall 0 M)ᶜ →
        ‖x‖ ^ finrank ℝ F * φ x < δ ^ finrank ℝ F * ε := by
      rcases (hasBasis_cobounded_compl_closedBall (0 : F)).eventually_iff.1
        ((tendsto_order.1 h).2 (δ ^ finrank ℝ F * ε) (by positivity)) with ⟨M, -, hM⟩
      refine ⟨max M 1, zero_lt_one.trans_le (le_max_right _ _), fun x hx ↦ hM ?_⟩
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, le_max_iff, not_or, not_le] at hx
      simpa using hx.1
    filter_upwards [Ioi_mem_atTop (M / δ)] with c (hc : M / δ < c) x hx
    have cpos : 0 < c := lt_trans (by positivity) hc
    suffices c ^ finrank ℝ F * φ (c • x) < ε by simpa [abs_of_nonneg (hφ _), abs_of_nonneg cpos.le]
    have hδx : δ ≤ ‖x‖ := by
      have : x ∈ (ball 0 δ)ᶜ := fun h ↦ hx (h'u h)
      simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
    suffices δ ^ finrank ℝ F * (c ^ finrank ℝ F * φ (c • x)) < δ ^ finrank ℝ F * ε by
      rwa [mul_lt_mul_iff_of_pos_left (by positivity)] at this
    calc
      δ ^ finrank ℝ F * (c ^ finrank ℝ F * φ (c • x))
      _ ≤ ‖x‖ ^ finrank ℝ F * (c ^ finrank ℝ F * φ (c • x)) := by
        gcongr; exact mul_nonneg (by positivity) (hφ _)
      _ = ‖c • x‖ ^ finrank ℝ F * φ (c • x) := by
        simp [norm_smul, abs_of_pos cpos, mul_pow]; ring
      _ < δ ^ finrank ℝ F * ε := by
        apply hM
        rw [div_lt_iff₀ δpos] at hc
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg cpos.le, not_le]
        exact hc.trans_le (by gcongr)
  · have : Tendsto (fun c ↦ ∫ (x : F) in closedBall 0 c, φ x ∂μ) atTop (𝓝 1) := by
      rw [← h'φ]
      exact (aecover_closedBall tendsto_id).integral_tendsto_of_countably_generated I
    apply this.congr'
    filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    rw [integral_const_mul, setIntegral_comp_smul_of_pos _ _ _ hc, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), _root_.smul_closedBall _ _ zero_le_one]
    simp [abs_of_nonneg hc.le]
  · filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    exact (I.comp_smul hc.ne').aestronglyMeasurable.const_mul _
  · exact hg
  · exact h'g

/-- Consider a nonnegative function `φ` with integral one, decaying quickly enough at infinity.
Then suitable renormalizations of `φ` form a sequence of peak functions around any point:
`∫ (c ^ d * φ (c • (x₀ - x)) • g x` converges to `g x₀` as `c → ∞` if `g` is continuous at `x₀`
and integrable. -/
/-
**tendsto_integral_comp_smul_smul_of_integrable'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_comp_smul_smul_of_integrable' {φ : F -> Real} (hφ : foral
l x, 0 <= φ x) (h'φ : ∫ x, φ x ∂μ = 1) (h : Tendsto (fun x => ‖x‖ ^ finrank Real
 F * φ x) (cobounded F) (𝓝 0)) {g : F -> E} {x₀ : F} (hg : Integrable g μ) (h'g 
: ContinuousAt g x₀) : Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ
 (c • (x₀ - x))) • g x ∂μ) atTop (𝓝 (g x₀))
参数：hφ : forall x, 0 <= φ x；h'φ : ∫ x, φ x ∂μ = 1；h : Tendsto (fun x => ‖x‖ ^ fin
rank Real F * φ x) (cobounded F) (𝓝 0)；hg : Integrable g μ；h'g : ContinuousAt g 
x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Integrable.comp_neg`：∀ {G : Type u_4} {F : Type u_6} [inst
 : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Measure
 G}   [inst_2 : AddGrou…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `MeasureTheory.Integrable.comp_add_left`：∀ {G : Type u_4} {F : Type u_6} 
[inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Me
asure G}   [inst_2 : AddGrou…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `tendsto_integral_comp_smul_smul_of_integrable`：tendsto_integral_comp_smu
l_smul_of_integrable {φ : F -> Real} (hφ : forall x, 0 <= φ x) (h'φ : ∫ x, φ x ∂
μ = 1) (h : Tendsto (fun x => ‖x‖ ^…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a nonnegative function `φ` with integral one, decaying quickly enough a
t infinity.
Then suitable renormalizations of `φ` form a sequence of peak functions around a
ny point:
`∫ (c ^ d * φ (c • (x₀ - x)) • g x` converges to `g x₀` as `c → ∞` if `g` is con
tinuous at `x₀`
and integrable.
-/
theorem tendsto_integral_comp_smul_smul_of_integrable'
    {φ : F → ℝ} (hφ : ∀ x, 0 ≤ φ x) (h'φ : ∫ x, φ x ∂μ = 1)
    (h : Tendsto (fun x ↦ ‖x‖ ^ finrank ℝ F * φ x) (cobounded F) (𝓝 0))
    {g : F → E} {x₀ : F} (hg : Integrable g μ) (h'g : ContinuousAt g x₀) :
    Tendsto (fun (c : ℝ) ↦ ∫ x, (c ^ (finrank ℝ F) * φ (c • (x₀ - x))) • g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  let f := fun x ↦ g (x₀ - x)
  have If : Integrable f μ := by simpa [f, sub_eq_add_neg] using (hg.comp_add_left x₀).comp_neg
  have : Tendsto (fun (c : ℝ) ↦ ∫ x, (c ^ (finrank ℝ F) * φ (c • x)) • f x ∂μ)
      atTop (𝓝 (f 0)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable hφ h'φ h If
    have A : ContinuousAt g (x₀ - 0) := by simpa using h'g
    exact A.comp <| by fun_prop
  simp only [f, sub_zero] at this
  convert! this using 2 with c
  conv_rhs => rw [← integral_add_left_eq_self x₀ (μ := μ)
    (f := fun x ↦ (c ^ finrank ℝ F * φ (c • x)) • g (x₀ - x)), ← integral_neg_eq_self]
  simp [sub_eq_add_neg]
