/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`: Egorov's theorem which shows that a sequence of
  almost everywhere convergent functions converges uniformly except on an arbitrarily small set.

-/

@[expose] public section


noncomputable section

open MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [PseudoEMetricSpace β] {μ : Measure α}

namespace Egorov

/-- Given a sequence of functions `f` and a function `g`, `notConvergentSeq f g n j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (n + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
/-
**MeasureTheory.Egorov.notConvergentSeq** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.Egorov`。
形式化陈述：notConvergentSeq [Preorder ι] (f : ι -> α -> β) (g : α -> β) (n : Nat) (j 
: ι) : Set α
参数：f : ι -> α -> β；g : α -> β；n : Nat；j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence of functions `f` and a function `g`, `notConvergentSeq f g n j`
 is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (n + 
1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem.
-/
def notConvergentSeq [Preorder ι] (f : ι → α → β) (g : α → β) (n : ℕ) (j : ι) : Set α :=
  ⋃ (k) (_ : j ≤ k), { x | (n : ℝ≥0∞)⁻¹ < edist (f k x) (g x) }

variable {n : ℕ} {j : ι} {s : Set α} {ε : ℝ} {f : ι → α → β} {g : α → β}
/-
**MeasureTheory.Egorov.mem_notConvergentSeq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Egorov`。
形式化陈述：mem_notConvergentSeq_iff [Preorder ι] {x : α} : x in notConvergentSeq f g 
n j ↔ exists k >= j, (n : Real>=0∞)⁻¹ < edist (f k x) (g x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_notConvergentSeq_iff [Preorder ι] {x : α} :
    x ∈ notConvergentSeq f g n j ↔ ∃ k ≥ j, (n : ℝ≥0∞)⁻¹ < edist (f k x) (g x) := by
  simp_rw [notConvergentSeq, Set.mem_iUnion, exists_prop, mem_ofPred]
/-
**MeasureTheory.Egorov.notConvergentSeq_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Egorov`。
形式化陈述：notConvergentSeq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion₂_mono'`：iUnion₂_mono' {s : forall i, κ i -> Set α} {t : foral
l i', κ' i' -> Set α} (h : forall i j, exists i' j', s i j subseteq t i' j') : ⋃
 (i) (j…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem notConvergentSeq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n) :=
  fun _ _ hjk => Set.iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Set.Subset.rfl⟩
/-
**MeasureTheory.Egorov.measure_inter_notConvergentSeq_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Egorov`。
形式化陈述：measure_inter_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι] (hf
g : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) 
: μ (s inter ⋂ j, notConvergentSeq f g n j) = 0
参数：hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))；n : Na
t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem measure_inter_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ ⋂ j, notConvergentSeq f g n j) = 0 := by
  simp_rw [EMetric.tendsto_atTop, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero, ← hfg]
  refine measure_mono fun x => ?_
  simp only [Set.mem_inter_iff, Set.mem_iInter, mem_notConvergentSeq_iff]
  push Not
  rintro ⟨hmem, hx⟩
  refine ⟨hmem, (n : ℝ≥0∞)⁻¹, by simp, fun N => ?_⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩
/-
**MeasureTheory.Egorov.notConvergentSeq_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Egorov`。
形式化陈述：notConvergentSeq_measurableSet [Preorder ι] [Countable ι] (hf : forall n, 
Measurable (fun a => edist (f n a) (g a))) : MeasurableSet (notConvergentSeq f g
 n j)
参数：hf : forall n, Measurable (fun a => edist (f n a) (g a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem notConvergentSeq_measurableSet [Preorder ι] [Countable ι]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a))) :
    MeasurableSet (notConvergentSeq f g n j) :=
  MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_lt measurable_const <| hf k
/-
**MeasureTheory.Egorov.measure_notConvergentSeq_tendsto_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Egorov`。
形式化陈述：measure_notConvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι] (hf
 : forall n, Measurable (fun a => edist (f n a) (g a))) (hsm : MeasurableSet s) 
(hs : μ s != ∞) (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝
 (g x))) (n : Nat) : Tendsto (fun j => μ (s inter notConvergentSeq f g n j)) atT
op (𝓝 0)
参数：hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : MeasurableSet 
s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 
(g x))；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Egorov.measure_inter_notConvergentSeq_eq_zero`：measure_int
er_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι] (hfg : forallᵐ x ∂μ,
 x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x…
· 使用定理 `Set.inter_iInter`：inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s inter ⋂ i, t i) = ⋂ i, s inter t i
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atTop`：tendsto_measure_iInter_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `Filter.atTop.isCountablyGenerated`：∀ {α : Type u_1} [inst : Preorder α] 
[Countable α], Filter.atTop.IsCountablyGenerated
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.Egorov.notConvergentSeq_measurableSet`：notConvergentSeq_me
asurableSet [Preorder ι] [Countable ι] (hf : forall n, Measurable (fun a => edis
t (f n a) (g a))) : MeasurableSet (notCon…
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `MeasureTheory.Egorov.notConvergentSeq_antitone`：notConvergentSeq_antiton
e [Preorder ι] : Antitone (notConvergentSeq f g n)
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem measure_notConvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a))) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    Tendsto (fun j => μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty ι with h | h
  · have : (fun j => μ (s ∩ notConvergentSeq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
  rw [← measure_inter_notConvergentSeq_eq_zero hfg n, Set.inter_iInter]
  refine tendsto_measure_iInter_atTop
    (fun n ↦ (hsm.inter <| notConvergentSeq_measurableSet hf).nullMeasurableSet)
    (fun k l hkl => Set.inter_subset_inter_right _ <| notConvergentSeq_antitone hkl)
    ⟨h.some, ne_top_of_le_ne_top hs (measure_mono Set.inter_subset_left)⟩

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]
/-
**MeasureTheory.Egorov.exists_notConvergentSeq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Egorov`。
形式化陈述：exists_notConvergentSeq_lt (hε : 0 < ε) (hf : forall n, Measurable (fun a 
=> edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : forallᵐ 
x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) : exists j :
 ι, μ (s inter notConvergentSeq f g n j) <= ENNReal.ofReal (ε * 2⁻¹ ^ n)
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tendsto_atTop`：∀ {β : Type u_2} [Nonempty β] [inst : Semilattice
Sup β] {f : β → ENNReal} {a : ENNReal},   a ≠ ⊤ → (Filter.Tendsto f Filter.atTop
 (nhds a) ↔…
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `MeasureTheory.Egorov.measure_notConvergentSeq_tendsto_zero`：measure_notC
onvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι] (hf : forall n, Measu
rable (fun a => edist (f n a) (g a))) (hsm : Mea…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem exists_notConvergentSeq_lt (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ∃ j : ι, μ (s ∩ notConvergentSeq f g n j) ≤ ENNReal.ofReal (ε * 2⁻¹ ^ n) := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
    (measure_notConvergentSeq_tendsto_zero hf hsm hs hfg n) (.ofReal (ε * 2⁻¹ ^ n))
      (by positivity)
  rw [zero_add] at hN
  exact ⟨N, (hN N le_rfl).2⟩

/-- Given some `ε > 0`, `notConvergentSeqLTIndex` provides the index such that
`notConvergentSeq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ n`.

This definition is useful for Egorov's theorem. -/
/-
**MeasureTheory.Egorov.notConvergentSeqLTIndex** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.Egorov`。
形式化陈述：notConvergentSeqLTIndex (hε : 0 < ε) (hf : forall n, Measurable (fun a => 
edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : forallᵐ x ∂
μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) : ι
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Egorov.exists_notConvergentSeq_lt`：exists_notConvergentSeq
_lt (hε : 0 < ε) (hf : forall n, Measurable (fun a => edist (f n a) (g a))) (hsm
 : MeasurableSet s) (hs : μ s != ∞) (…

--- 原说明 ---
Given some `ε > 0`, `notConvergentSeqLTIndex` provides the index such that
`notConvergentSeq` (intersected with a set of finite measure) has measure less t
han
`ε * 2⁻¹ ^ n`.

This definition is useful for Egorov's theorem.
-/
def notConvergentSeqLTIndex (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) : ι :=
  Classical.choose <| exists_notConvergentSeq_lt hε hf hsm hs hfg n
/-
**MeasureTheory.Egorov.notConvergentSeqLTIndex_spec** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Egorov`。
形式化陈述：notConvergentSeqLTIndex_spec (hε : 0 < ε) (hf : forall n, Measurable (fun 
a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : forall
ᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) : μ (s int
er notConvergentSeq f g n (notConvergentSeqLTIndex hε hf hsm hs hfg n)) <= ENNRe
al.ofReal (ε * 2⁻¹ ^ n)
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Egorov.exists_notConvergentSeq_lt`：exists_notConvergentSeq
_lt (hε : 0 < ε) (hf : forall n, Measurable (fun a => edist (f n a) (g a))) (hsm
 : MeasurableSet s) (hs : μ s != ∞) (…
-/
theorem notConvergentSeqLTIndex_spec (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ notConvergentSeq f g n (notConvergentSeqLTIndex hε hf hsm hs hfg n)) ≤
      ENNReal.ofReal (ε * 2⁻¹ ^ n) :=
  Classical.choose_spec <| exists_notConvergentSeq_lt hε hf hsm hs hfg n

/-- Given some `ε > 0`, `iUnionNotConvergentSeq` is the union of `notConvergentSeq` with
specific indices such that `iUnionNotConvergentSeq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
/-
**MeasureTheory.Egorov.iUnionNotConvergentSeq** 是 Mathlib 中的一个定义，位于命名空间 `Measure
Theory.Egorov`。
形式化陈述：iUnionNotConvergentSeq (hε : 0 < ε) (hf : forall n, Measurable (fun a => e
dist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : forallᵐ x ∂μ
, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Given some `ε > 0`, `iUnionNotConvergentSeq` is the union of `notConvergentSeq` 
with
specific indices such that `iUnionNotConvergentSeq` has measure less equal than 
`ε`.

This definition is useful for Egorov's theorem.
-/
def iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s ∩ notConvergentSeq f g n (notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg n)
/-
**MeasureTheory.Egorov.iUnionNotConvergentSeq_measurableSet** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Egorov`。
形式化陈述：iUnionNotConvergentSeq_measurableSet (hε : 0 < ε) (hf : forall n, Measurab
le (fun a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg 
: forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable
Set iUnionNotConvergentSeq hε hf hsm hs hfg
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.Egorov.notConvergentSeq_measurableSet`：notConvergentSeq_me
asurableSet [Preorder ι] [Countable ι] (hf : forall n, Measurable (fun a => edis
t (f n a) (g a))) : MeasurableSet (notCon…
-/
theorem iUnionNotConvergentSeq_measurableSet (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableSet <| iUnionNotConvergentSeq hε hf hsm hs hfg :=
  MeasurableSet.iUnion fun _ ↦ hsm.inter <| notConvergentSeq_measurableSet hf
/-
**MeasureTheory.Egorov.measure_iUnionNotConvergentSeq** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Egorov`。
形式化陈述：measure_iUnionNotConvergentSeq (hε : 0 < ε) (hf : forall n, Measurable (fu
n a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : fora
llᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) : μ (iUnionNotConv
ergentSeq hε hf hsm hs hfg) <= ENNReal.ofReal ε
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `MeasureTheory.Egorov.notConvergentSeqLTIndex_spec`：notConvergentSeqLTInd
ex_spec (hε : 0 < ε) (hf : forall n, Measurable (fun a => edist (f n a) (g a))) 
(hsm : MeasurableSet s) (hs : μ s != ∞)…
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_tsum_of_nonneg`：ENNReal.ofReal_tsum_of_nonneg {f : α -> R
eal} (hf_nonneg : forall n, 0 <= f n) (hf : Summable f) : ENNReal.ofReal (∑' n, 
f n) = ∑' n, ENNRea…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `summable_geometric_two`：summable_geometric_two : Summable fun n : Nat =>
 ((1 : Real) / 2) ^ n
· 使用定理 `tsum_geometric_two`：tsum_geometric_two : (∑' n : Nat, ((1 : Real) / 2) ^
 n) = 2
（共 35 条，此处仅展示前 30 条）
-/
theorem measure_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (iUnionNotConvergentSeq hε hf hsm hs hfg) ≤ ENNReal.ofReal ε := by
  refine le_trans (measure_iUnion_le _) (le_trans
    (ENNReal.tsum_le_tsum <| notConvergentSeqLTIndex_spec (half_pos hε) hf hsm hs hfg) ?_)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two,
    ← ENNReal.ofReal_mul (half_pos hε).le, div_mul_cancel₀ ε two_ne_zero]
  · intro n; positivity
  · rw [inv_eq_one_div]
    exact summable_geometric_two
/-
**MeasureTheory.Egorov.iUnionNotConvergentSeq_subset** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Egorov`。
形式化陈述：iUnionNotConvergentSeq_subset (hε : 0 < ε) (hf : forall n, Measurable (fun
 a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : foral
lᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) : iUnionNotConverge
ntSeq hε hf hsm hs hfg subseteq s
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Egorov.iUnionNotConvergentSeq.eq_1`：∀ {α : Type u_1} {β : 
Type u_2} {ι : Type u_3} {m : MeasurableSpace α} [inst : PseudoEMetricSpace β]  
 {μ : MeasureTheory.Measure α} {s : Se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem iUnionNotConvergentSeq_subset (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    iUnionNotConvergentSeq hε hf hsm hs hfg ⊆ s := by
  rw [iUnionNotConvergentSeq, ← Set.inter_iUnion]
  exact Set.inter_subset_left
/-
**MeasureTheory.Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.Egorov`。
形式化陈述：tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq (hε : 0 < ε) (hf : forall 
n, Measurable (fun a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s 
!= ∞) (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
 TendstoUniformlyOn f g atTop (s \ Egorov.iUnionNotConvergentSeq hε hf hsm hs hf
g)
参数：hε : 0 < ε；hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : Mea
surableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x
) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EMetric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {ι : Type*} {F : 
ι -> β -> α} {f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p 
s ↔ forall ε > 0, fo…
· 使用定理 `ENNReal.exists_inv_nat_lt`：exists_inv_nat_lt {a : Real>=0∞} (h : a != 0)
 : exists n : Nat, (n : Real>=0∞)⁻¹ < a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Egorov.mem_notConvergentSeq_iff`：mem_notConvergentSeq_iff 
[Preorder ι] {x : α} : x in notConvergentSeq f g n j ↔ exists k >= j, (n : Real>
=0∞)⁻¹ < edist (f k x) (g x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
-/
theorem tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a))) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg) := by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  rw [eventually_atTop]
  refine ⟨Egorov.notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg N, fun n hn x hx => ?_⟩
  refine lt_of_le_of_lt ?_ hN
  have : edist (f n x) (g x) ≤ (N : ℝ≥0∞)⁻¹ :=
    not_lt.mp fun h ↦ hx.2 <| Set.mem_iUnion.2 ⟨N, hx.1, mem_notConvergentSeq_iff.2 ⟨n, hn, h⟩⟩
  simpa [edist_comm]

@[deprecated (since := "2026-06-03")]
alias tendstoUniformlyOn_diff_iUnionNotConvergentSeq :=
  tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]
  {f : ι → α → β} {g : α → β} {s : Set α}

/-- **Egorov's theorem**: If `f : ι → α → β` is a sequence of functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite measure,
and the distance between `f n a` and `g a` is measurable for all `n`,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
/-
**MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist (hf : forall n, Measu
rable (fun a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs : μ s != ∞) (h
fg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real
} (hε : 0 < ε) : exists t subseteq s, MeasurableSet t ∧ μ t <= ENNReal.ofReal ε 
∧ TendstoUniformlyOn f g atTop (s \ t)
参数：hf : forall n, Measurable (fun a => edist (f n a) (g a))；hsm : MeasurableSet 
s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 
(g x))；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Egorov.iUnionNotConvergentSeq_subset`：iUnionNotConvergentS
eq_subset (hε : 0 < ε) (hf : forall n, Measurable (fun a => edist (f n a) (g a))
) (hsm : MeasurableSet s) (hs : μ s != ∞…
· 使用定理 `MeasureTheory.Egorov.iUnionNotConvergentSeq_measurableSet`：iUnionNotConv
ergentSeq_measurableSet (hε : 0 < ε) (hf : forall n, Measurable (fun a => edist 
(f n a) (g a))) (hsm : MeasurableSet s) (hs : μ…
· 使用定理 `MeasureTheory.Egorov.measure_iUnionNotConvergentSeq`：measure_iUnionNotCo
nvergentSeq (hε : 0 < ε) (hf : forall n, Measurable (fun a => edist (f n a) (g a
))) (hsm : MeasurableSet s) (hs : μ s != …
· 使用定理 `MeasureTheory.Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq`：te
ndstoUniformlyOn_sdiff_iUnionNotConvergentSeq (hε : 0 < ε) (hf : forall n, Measu
rable (fun a => edist (f n a) (g a))) (hsm : MeasurableSet…

--- 原说明 ---
**Egorov's theorem**: If `f : ι → α → β` is a sequence of functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite mea
sure,
and the distance between `f n a` and `g a` is measurable for all `n`,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` 
converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually
 `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges u
niformly except on
an arbitrarily small set.
-/
theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq hε hf hsm hs hfg⟩

/-- **Egorov's theorem**: If `f : ι → α → β` is a sequence of strongly measurable functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite measure,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
/-
**MeasureTheory.tendstoUniformlyOn_of_ae_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：tendstoUniformlyOn_of_ae_tendsto (hf : forall n, StronglyMeasurable (f n))
 (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s != ∞) (hfg : fora
llᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real} (hε : 0
 < ε) : exists t subseteq s, MeasurableSet t ∧ μ t <= ENNReal.ofReal ε ∧ Tendsto
UniformlyOn f g atTop (s \ t)
参数：hf : forall n, StronglyMeasurable (f n)；hg : StronglyMeasurable g；hsm : Measu
rableSet s；hs : μ s != ∞；hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) 
atTop (𝓝 (g x))；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist`：tend
stoUniformlyOn_of_ae_tendsto_of_measurable_edist (hf : forall n, Measurable (fun
 a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs …
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `MeasureTheory.StronglyMeasurable.edist`：∀ {α : Type u_1} {x : Measurable
Space α} {β : Type u_5} [inst : PseudoEMetricSpace β] {f g : α → β},   MeasureTh
eory.StronglyMeasurable f → …

--- 原说明 ---
**Egorov's theorem**: If `f : ι → α → β` is a sequence of strongly measurable fu
nctions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite mea
sure,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` 
converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually
 `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges u
niformly except on
an arbitrarily small set.
-/
theorem tendstoUniformlyOn_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (fun n ↦ ((hf n).edist hg).measurable) hsm hs hfg hε

/-- Egorov's theorem for finite measure spaces.
Version with measurable distances. -/
/-
**MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' [IsFiniteMeasure μ] 
(hf : forall n, Measurable (fun a => edist (f n a) (g a))) (hfg : forallᵐ x ∂μ, 
Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real} (hε : 0 < ε) : exists t, Me
asurableSet t ∧ μ t <= ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ
参数：hf : forall n, Measurable (fun a => edist (f n a) (g a))；hfg : forallᵐ x ∂μ, 
Tendsto (fun n => f n x) atTop (𝓝 (g x))；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist`：tend
stoUniformlyOn_of_ae_tendsto_of_measurable_edist (hf : forall n, Measurable (fun
 a => edist (f n a) (g a))) (hsm : MeasurableSet s) (hs …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s

--- 原说明 ---
Egorov's theorem for finite measure spaces.
Version with measurable distances.
-/
theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' [IsFiniteMeasure μ]
    (hf : ∀ n, Measurable (fun a ↦ edist (f n a) (g a)))
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ := by
  have ⟨t, _, ht, htendsto⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist hf MeasurableSet.univ
    (measure_ne_top μ Set.univ) (by filter_upwards [hfg] with _ htendsto _ using htendsto) hε
  refine ⟨_, ht, ?_⟩
  rwa [Set.compl_eq_univ_sdiff]

/-- Egorov's theorem for finite measure spaces. -/
/-
**MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：tendstoUniformlyOn_of_ae_tendsto' [IsFiniteMeasure μ] (hf : forall n, Stro
nglyMeasurable (f n)) (hg : StronglyMeasurable g) (hfg : forallᵐ x ∂μ, Tendsto (
fun n => f n x) atTop (𝓝 (g x))) {ε : Real} (hε : 0 < ε) : exists t, MeasurableS
et t ∧ μ t <= ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ
参数：hf : forall n, StronglyMeasurable (f n)；hg : StronglyMeasurable g；hfg : foral
lᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'`：ten
dstoUniformlyOn_of_ae_tendsto_of_measurable_edist' [IsFiniteMeasure μ] (hf : for
all n, Measurable (fun a => edist (f n a) (g a))) (hfg : …
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `MeasureTheory.StronglyMeasurable.edist`：∀ {α : Type u_1} {x : Measurable
Space α} {β : Type u_5} [inst : PseudoEMetricSpace β] {f g : α → β},   MeasureTh
eory.StronglyMeasurable f → …

--- 原说明 ---
Egorov's theorem for finite measure spaces.
-/
theorem tendstoUniformlyOn_of_ae_tendsto' [IsFiniteMeasure μ] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ :=
  tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' (fun n ↦ ((hf n).edist hg).measurable)
    hfg hε

end MeasureTheory

