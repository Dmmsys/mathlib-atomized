/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Monotone convergence theorem and addition of Lebesgue integrals

The monotone convergence theorem (aka Beppo Levi lemma) states that the Lebesgue integral and
supremum can be swapped for a pointwise monotone sequence of functions. This file first proves
several variants of this theorem, then uses it to show that the Lebesgue integral is additive
(assuming one of the functions is at least `AEMeasurable`) and respects multiplication by
a constant.
-/

public section

namespace MeasureTheory

open Set Filter ENNReal Topology NNReal SimpleFunc

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

section MonotoneConvergence

/-- **Monotone convergence theorem**, version with `Measurable` functions. -/
/-
**MeasureTheory.lintegral_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iSup {f : Nat -> α -> Real>=0∞} (hf : forall n, Measurable (f n)
) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ
参数：hf : forall n, Measurable (f n)；h_mono : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_eq_nnreal`：lintegral_eq_nnreal {m : MeasurableSp
ace α} (f : α -> Real>=0∞) (μ : Measure α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0
) (_ : forall x, ↑(φ x)…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `ENNReal.le_of_forall_lt_one_mul_le`：le_of_forall_lt_one_mul_le {x y : Re
al>=0∞} (h : forall a < 1, a * x <= y) : x <= y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_coe`：lt_iff_exists_coe : a < b ↔ exists p : Real>=
0, a = p ∧ ↑p < b
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
**Monotone convergence theorem**, version with `Measurable` functions.
-/
theorem lintegral_iSup {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  set c : ℝ≥0 → ℝ≥0∞ := (↑)
  set F := fun a : α => ⨆ n, f n a
  refine le_antisymm ?_ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine iSup_le fun s => iSup_le fun hsf => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  let rs := s.map fun a => r * a
  have eq_rs : rs.map c = (const α r : α →ₛ ℝ≥0∞) * map c s := rfl
  have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ { a | p ≤ f n a } := by
    intro p
    rw [← inter_iUnion]; nth_rw 1 [← inter_univ (map c rs ⁻¹' {p})]
    refine Set.ext fun x => and_congr_right fun hx => (iff_of_eq (true_iff _)).2 ?_
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp only [coe_map, mem_preimage, Function.comp_apply, mem_singleton_iff] at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [Ne, ← ENNReal.coe_eq_zero]
    have : s x ≠ 0 := right_ne_zero_of_mul this
    have : (rs.map c) x < ⨆ n : ℕ, f n x := by
      refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ?_) (hsf x)
      suffices r * s x < 1 * s x by simpa
      gcongr
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
  have mono : ∀ r : ℝ≥0∞, Monotone fun n => rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a } := by
    intro r i j h
    refine inter_subset_inter_right _ ?_
    simp_rw [subset_def, mem_ofPred]
    intro x hx
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet {a : α | map c rs a ≤ f n a} := fun n =>
    measurableSet_le (SimpleFunc.measurable _) (hf n)
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ r ∈ (rs.map c).range, r * μ (rs.map c ⁻¹' {r}) := by
      rw [← const_mul_lintegral, eq_rs, SimpleFunc.lintegral]
    _ = ∑ r ∈ (rs.map c).range, r * μ (⋃ n, rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(eq _).symm]
    _ = ∑ r ∈ (rs.map c).range, ⨆ n, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      Finset.sum_congr rfl fun x _ => by rw [(mono x).measure_iUnion, ENNReal.mul_iSup]
    _ = ⨆ n, ∑ r ∈ (rs.map c).range, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      refine ENNReal.finsetSum_iSup_of_monotone fun p i j h ↦ ?_
      gcongr _ * μ ?_
      exact mono p h
    _ ≤ ⨆ n : ℕ, ((rs.map c).restrict { a | (rs.map c) a ≤ f n a }).lintegral μ := by
      gcongr with n
      rw [restrict_lintegral _ (h_meas n)]
      refine le_of_eq (Finset.sum_congr rfl fun r _ => ?_)
      congr 2 with a
      refine and_congr_right ?_
      simp +contextual
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      simp only [← SimpleFunc.lintegral_eq_lintegral]
      gcongr with n a
      simp only [map_apply] at h_meas
      simp only [coe_map, restrict_apply _ (h_meas _), (· ∘ ·)]
      exact indicator_apply_le id

/-- **Monotone convergence theorem**, version with `AEMeasurable` functions. -/
/-
**MeasureTheory.lintegral_iSup'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iSup' {f : Nat -> α -> Real>=0∞} (hf : forall n, AEMeasurable (f
 n) μ) (h_mono : forallᵐ x ∂μ, Monotone fun n => f n x) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂μ
参数：hf : forall n, AEMeasurable (f n) μ；h_mono : forallᵐ x ∂μ, Monotone fun n => 
f n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `aeSeq.prop_of_mem_aeSeqSet`：prop_of_mem_aeSeqSet (hf : forall i, AEMeasu
rable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) : p x fun n => aeSeq hf p n x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `aeSeq.iSup`：iSup [SupSet β] [Countable ι] (hf : forall i, AEMeasurable (
f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f
…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `aeSeq.measurable`：measurable (hf : forall i, AEMeasurable (f i) μ) (p : 
α -> (ι -> β) -> Prop) (i : ι) : Measurable (aeSeq hf p i)
· 使用定理 `aeSeq.aeSeq_n_eq_fun_n_ae`：aeSeq_n_eq_fun_n_ae [Countable ι] (hf : foral
l i, AEMeasurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeS
eq hf p n =ᵐ[μ]…

--- 原说明 ---
**Monotone convergence theorem**, version with `AEMeasurable` functions.
-/
theorem lintegral_iSup' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Monotone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_mono
  have h_ae_seq_mono : Monotone (aeSeq hf p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet hf p
    · exact aeSeq.prop_of_mem_aeSeqSet hf hx hnm
    · simp only [aeSeq, hx, if_false, le_rfl]
  rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  simp_rw [iSup_apply]
  rw [lintegral_iSup (aeSeq.measurable hf p) h_ae_seq_mono]
  congr with n
  exact lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae hf hp n)

/-- **Monotone convergence theorem** expressed with limits. -/
/-
**MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：lintegral_tendsto_of_tendsto_of_monotone {f : Nat -> α -> Real>=0∞} {F : α
 -> Real>=0∞} (hf : forall n, AEMeasurable (f n) μ) (h_mono : forallᵐ x ∂μ, Mono
tone fun n => f n x) (h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (
𝓝 <| F x)) : Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ)
参数：hf : forall n, AEMeasurable (f n) μ；h_mono : forallᵐ x ∂μ, Monotone fun n => 
f n x；h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_iSup'`：lintegral_iSup' {f : Nat -> α -> Real>=0∞
} (hf : forall n, AEMeasurable (f n) μ) (h_mono : forallᵐ x ∂μ, Monotone fun n =
> f n x) : ∫⁻ a, ⨆ …
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal

--- 原说明 ---
**Monotone convergence theorem** expressed with limits.
-/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ) := by
  have : Monotone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_mono.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iSup this
  rw [← lintegral_iSup' hf h_mono]
  refine lintegral_congr_ae ?_
  filter_upwards [h_mono, h_tendsto] with _ hx_mono hx_tendsto using
    tendsto_nhds_unique hx_tendsto (tendsto_atTop_iSup hx_mono)

/-- Weaker version of the **monotone convergence theorem**. -/
/-
**MeasureTheory.lintegral_iSup_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_iSup_ae {f : Nat -> α -> Real>=0∞} (hf : forall n, Measurable (f
 n)) (h_mono : forall n, forallᵐ a ∂μ, f n a <= f n.succ a) : ∫⁻ a, ⨆ n, f n a ∂
μ = ⨆ n, ∫⁻ a, f n a ∂μ
参数：hf : forall n, Measurable (f n)；h_mono : forall n, forallᵐ a ∂μ, f n a <= f n
.succ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `Measurable.piecewise`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g :
 α → β} {m : MeasurableSpace α} {mβ : MeasurableSpace β}   {x : DecidablePred fu
n x => x ∈…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Weaker version of the **monotone convergence theorem**.
-/
theorem lintegral_iSup_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  classical
  let ⟨s, hs⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_all_iff.2 h_mono))
  let g n a := if a ∈ s then 0 else f n a
  have g_eq_f : ∀ᵐ a ∂μ, ∀ n, g n a = f n a :=
    (measure_eq_zero_iff_ae_notMem.1 hs.2.2).mono fun a ha n => if_neg ha
  calc
    ∫⁻ a, ⨆ n, f n a ∂μ = ∫⁻ a, ⨆ n, g n a ∂μ :=
      lintegral_congr_ae <| g_eq_f.mono fun a ha => by simp only [ha]
    _ = ⨆ n, ∫⁻ a, g n a ∂μ :=
      (lintegral_iSup (fun n => measurable_const.piecewise hs.2.1 (hf n))
        (monotone_nat_of_le_succ fun n a => ?_))
    _ = ⨆ n, ∫⁻ a, f n a ∂μ := by simp only [lintegral_congr_ae (g_eq_f.mono fun _a ha => ha _)]
  simp only [g]
  split_ifs with h
  · rfl
  · have := Set.notMem_subset hs.1 h
    simp only [not_forall, not_le, mem_ofPred_eq, not_exists, not_lt] at this
    exact this n

open Encodable in
/-- **Monotone convergence theorem** for a supremum over a directed family and indexed by a
countable type. -/
/-
**MeasureTheory.lintegral_iSup_directed_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：lintegral_iSup_directed_of_measurable [Countable β] {f : β -> α -> Real>=0
∞} (hf : forall b, Measurable (f b)) (h_directed : Directed (· <= ·) f) : ∫⁻ a, 
⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ
参数：hf : forall b, Measurable (f b)；h_directed : Directed (· <= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Directed.le_sequence`：le_sequence (a : α) : f a <= f (hf.sequence f (enc
ode a + 1))
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `Directed.sequence_mono`：sequence_mono : Monotone (f ∘ hf.sequence f)
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ

--- 原说明 ---
**Monotone convergence theorem** for a supremum over a directed family and index
ed by a
countable type.
-/
theorem lintegral_iSup_directed_of_measurable [Countable β] {f : β → α → ℝ≥0∞}
    (hf : ∀ b, Measurable (f b)) (h_directed : Directed (· ≤ ·) f) :
    ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp
  inhabit β
  have : ∀ a, ⨆ b, f b a = ⨆ n, f (h_directed.sequence f n) a := by
    intro a
    refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun n => le_iSup (fun n => f n a) _)
    exact le_iSup_of_le (encode b + 1) (h_directed.le_sequence b a)
  calc
    ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ := by simp only [this]
    _ = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :=
      (lintegral_iSup (fun n => hf _) h_directed.sequence_mono)
    _ = ⨆ b, ∫⁻ a, f b a ∂μ := by
      refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun b => ?_)
      · exact le_iSup (fun b => ∫⁻ a, f b a ∂μ) _
      · exact le_iSup_of_le (encode b + 1) (lintegral_mono <| h_directed.le_sequence b)

/-- **Monotone convergence theorem** for a supremum over a directed family and indexed by a
countable type. -/
/-
**MeasureTheory.lintegral_iSup_directed** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：lintegral_iSup_directed [Countable β] {f : β -> α -> Real>=0∞} (hf : foral
l b, AEMeasurable (f b) μ) (h_directed : Directed (· <= ·) f) : ∫⁻ a, ⨆ b, f b a
 ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ
参数：hf : forall b, AEMeasurable (f b) μ；h_directed : Directed (· <= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet`：aeSeq_eq_fun_of_mem_aeSeqSet (hf : f
orall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : aeSeq
 hf p i x = f i x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `aeSeq.iSup`：iSup [SupSet β] [Countable ι] (hf : forall i, AEMeasurable (
f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f
…
· 使用定理 `aeSeq.aeSeq_n_eq_fun_n_ae`：aeSeq_n_eq_fun_n_ae [Countable ι] (hf : foral
l i, AEMeasurable (f i) μ) (hp : forallᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeS
eq hf p n =ᵐ[μ]…
· 使用定理 `MeasureTheory.lintegral_iSup_directed_of_measurable`：lintegral_iSup_dire
cted_of_measurable [Countable β] {f : β -> α -> Real>=0∞} (hf : forall b, Measur
able (f b)) (h_directed : Directed (· <= …
· 使用定理 `aeSeq.measurable`：measurable (hf : forall i, AEMeasurable (f i) μ) (p : 
α -> (ι -> β) -> Prop) (i : ι) : Measurable (aeSeq hf p i)

--- 原说明 ---
**Monotone convergence theorem** for a supremum over a directed family and index
ed by a
countable type.
-/
theorem lintegral_iSup_directed [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ b, AEMeasurable (f b) μ)
    (h_directed : Directed (· ≤ ·) f) : ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (β → ENNReal) → Prop := fun x f' => Directed LE.le f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := by
    filter_upwards [] with x i j
    obtain ⟨z, hz₁, hz₂⟩ := h_directed i j
    exact ⟨z, hz₁ x, hz₂ x⟩
  have h_ae_seq_directed : Directed LE.le (aeSeq hf p) := by
    intro b₁ b₂
    obtain ⟨z, hz₁, hz₂⟩ := h_directed b₁ b₂
    refine ⟨z, ?_, ?_⟩ <;>
      · intro x
        by_cases hx : x ∈ aeSeqSet hf p
        · repeat rw [aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hx]
          apply_rules [hz₁, hz₂]
        · simp only [aeSeq, hx, if_false]
          exact le_rfl
  convert! lintegral_iSup_directed_of_measurable (aeSeq.measurable hf p) h_ae_seq_directed using 1
  · simp_rw [← iSup_apply]
    rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  · congr 1
    ext1 b
    rw [lintegral_congr_ae]
    apply EventuallyEq.symm
    exact aeSeq.aeSeq_n_eq_fun_n_ae hf hp _

/-- **Fatou's lemma**, version with `AEMeasurable` functions indexed by `ℕ`. -/
/-
**MeasureTheory.lintegral_liminf_nat_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Fatou's lemma**, version with `AEMeasurable` functions indexed by `ℕ`.
-/
private theorem lintegral_liminf_nat_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  calc
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup' (fun _ => .biInf _ (to_countable _) (fun i _ ↦ h_meas i))
        (ae_of_all μ fun _ _ _ hnm => iInf_le_iInf_of_subset fun _ hi => le_trans hnm hi))
    _ ≤ ⨆ n : ℕ, ⨅ i ≥ n, ∫⁻ a, f i a ∂μ := iSup_mono fun _ => le_iInf₂_lintegral _
    _ = atTop.liminf fun n => ∫⁻ a, f n a ∂μ := Filter.liminf_eq_iSup_iInf_of_nat.symm

/-- **Fatou's lemma**, version with `AEMeasurable` functions. -/
/-
**MeasureTheory.lintegral_liminf_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_liminf_le' {ι : Type*} {f : ι -> α -> Real>=0∞} {u : Filter ι} [
IsCountablyGenerated u] (h_meas : forall i, AEMeasurable (f i) μ) : ∫⁻ a, liminf
 (fun i => f i a) u ∂μ <= liminf (fun i => ∫⁻ a, f i a ∂μ) u
参数：h_meas : forall i, AEMeasurable (f i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.liminf_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.liminf f ⊥ = ⊤
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `exists_seq_tendsto_liminf`：exists_seq_tendsto_liminf [NeBot f] {u : β ->
 α} [IsCountablyGenerated f] (hc : IsCoboundedUnder (· >= ·) f u
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Tendsto.liminf_le_liminf_comp`：∀ {ι : Type u_6} {α : Type u_7} {β
 : Type u_8} [inst : ConditionallyCompleteLattice β] {v : ι → α} {u : α → β}   {
f : Filter ι} {g : Filter …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.Lebesgue.Add.0.MeasureTheory.lin
tegral_liminf_nat_le'`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α} {f : ℕ → α → ENNReal},   (∀ (n : ℕ), AEMeasurable (f n) μ) →     ∫
⁻ (…
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
**Fatou's lemma**, version with `AEMeasurable` functions.
-/
theorem lintegral_liminf_le' {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u := by
  by_cases! hu : ¬ u.NeBot
  · simp_all
  · obtain ⟨g, hg⟩ : ∃ g : ℕ → ι,
        Tendsto (fun n => ∫⁻ a, f (g n) a ∂μ) atTop (𝓝 (liminf (fun i => ∫⁻ a, f i a ∂μ) u)) ∧
        Tendsto g atTop u :=
      exists_seq_tendsto_liminf
    calc
    _ ≤ ∫⁻ a, liminf (fun n => f (g n) a) atTop ∂μ :=
      lintegral_mono fun a => hg.2.liminf_le_liminf_comp
    _ ≤ liminf (fun n => ∫⁻ a, f (g n) a ∂μ) atTop :=
      lintegral_liminf_nat_le' (fun n => h_meas (g n))
    _ = _ := hg.1.liminf_eq

/-- **Fatou's lemma**, version with `Measurable` functions. -/
/-
**MeasureTheory.lintegral_liminf_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_liminf_le {ι : Type*} {f : ι -> α -> Real>=0∞} {u : Filter ι} [I
sCountablyGenerated u] (h_meas : forall i, Measurable (f i)) : ∫⁻ a, liminf (fun
 i => f i a) u ∂μ <= liminf (fun i => ∫⁻ a, f i a ∂μ) u
参数：h_meas : forall i, Measurable (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_liminf_le'`：lintegral_liminf_le' {ι : Type*} {f 
: ι -> α -> Real>=0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : forall i
, AEMeasurable (f i) μ) …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
**Fatou's lemma**, version with `Measurable` functions.
-/
theorem lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u :=
  lintegral_liminf_le' fun n => (h_meas n).aemeasurable

end MonotoneConvergence

section Add

/-
**MeasureTheory.lintegral_eq_iSup_eapprox_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：lintegral_eq_iSup_eapprox_lintegral {f : α -> Real>=0∞} (hf : Measurable f
) : ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
-/
theorem lintegral_eq_iSup_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ :=
  calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      congr; ext a; rw [iSup_eapprox_apply hf]
    _ = ⨆ n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      apply lintegral_iSup
      · fun_prop
      · intro i j h
        exact monotone_eapprox f h
    _ = ⨆ n, (eapprox f n).lintegral μ := by
      congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]

/-- Generalization of `lintegral_eq_iSup_eapprox_lintegral` to ae-measurable functions. -/
/-
**MeasureTheory.lintegral_eq_iSup_eapprox_lintegral'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：lintegral_eq_iSup_eapprox_lintegral' {f : α -> Real>=0∞} (hf : AEMeasurabl
e f μ) : ∫⁻ a, f a ∂μ = ⨆ n, (eapprox (hf.mk f) n).lintegral μ
参数：hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)

--- 原说明 ---
Generalization of `lintegral_eq_iSup_eapprox_lintegral` to ae-measurable functio
ns.
-/
theorem lintegral_eq_iSup_eapprox_lintegral' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox (hf.mk f) n).lintegral μ := by
  rw [lintegral_congr_ae hf.ae_eq_mk, lintegral_eq_iSup_eapprox_lintegral hf.measurable_mk]
/-
**MeasureTheory.lintegral_eapprox_le_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：lintegral_eapprox_le_lintegral {f : α -> Real>=0∞} (hf : Measurable f) (n 
: Nat) : (eapprox f n).lintegral μ <= ∫⁻ x, f x ∂μ
参数：hf : Measurable f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma lintegral_eapprox_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (eapprox f n).lintegral μ ≤ ∫⁻ x, f x ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  exact le_iSup (fun n ↦ (eapprox f n).lintegral μ) n
/-
**MeasureTheory.measure_support_eapprox_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_support_eapprox_lt_top {f : α -> Real>=0∞} (hf_meas : Measurable f
) (hf : ∫⁻ x, f x ∂μ != ∞) (n : Nat) : μ (Function.support (eapprox f n)) < ∞
参数：hf_meas : Measurable f；hf : ∫⁻ x, f x ∂μ != ∞；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.SimpleFunc.measure_support_lt_top_of_lintegral_ne_top`：mea
sure_support_lt_top_of_lintegral_ne_top {f : α ->ₛ Real>=0∞} (hf : f.lintegral μ
 != ∞) : μ (support f) < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `MeasureTheory.lintegral_eapprox_le_lintegral`：lintegral_eapprox_le_linte
gral {f : α -> Real>=0∞} (hf : Measurable f) (n : Nat) : (eapprox f n).lintegral
 μ <= ∫⁻ x, f x ∂μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma measure_support_eapprox_lt_top {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∫⁻ x, f x ∂μ ≠ ∞) (n : ℕ) :
    μ (Function.support (eapprox f n)) < ∞ :=
  measure_support_lt_top_of_lintegral_ne_top <|
    ((lintegral_eapprox_le_lintegral hf_meas n).trans_lt hf.lt_top).ne

/-- The sum of the lower Lebesgue integrals of two functions is less than or equal to the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)measurable. -/
/-
**MeasureTheory.le_lintegral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_lintegral_add (f g : α -> Real>=0∞) : ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ <= ∫⁻
 a, f a + g a ∂μ
参数：f g : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用引理 `ENNReal.biSup_add_biSup_le'`：biSup_add_biSup_le' {p : ι -> Prop} {q : κ 
-> Prop} (hp : exists i, p i) (hq : exists j, q j) {g : κ -> Real>=0∞} (h : fora
ll i, p i -> fora…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Pi.instCanonicallyOrderedAddForall`：∀ {ι : Type u_6} {Z : ι → Type u_7} 
[inst : (i : ι) → AddMonoid (Z i)] [inst_1 : (i : ι) → PartialOrder (Z i)]   [∀ 
(i : ι), CanonicallyOrde…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.SimpleFunc.add_lintegral`：add_lintegral (f g : α ->ₛ Real>
=0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ

--- 原说明 ---
The sum of the lower Lebesgue integrals of two functions is less than or equal t
o the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)mea
surable.
-/
theorem le_lintegral_add (f g : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ := by
  simp only [lintegral]
  refine ENNReal.biSup_add_biSup_le' (p := fun h : α →ₛ ℝ≥0∞ => h ≤ f)
    (q := fun h : α →ₛ ℝ≥0∞ => h ≤ g) ⟨0, zero_le⟩ ⟨0, zero_le⟩ fun f' hf' g' hg' => ?_
  exact le_iSup₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge

-- Use stronger lemmas `lintegral_add_left`/`lintegral_add_right` instead
/-
**MeasureTheory.lintegral_add_aux** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_aux {f g : α -> Real>=0∞} (hf : Measurable f) (hg : Measurab
le g) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ENNReal.iSup_add_iSup_of_monotone`：iSup_add_iSup_of_monotone {ι : Type*}
 [Preorder ι] [IsDirectedOrder ι] {f g : ι -> Real>=0∞} (hf : Monotone f) (hg : 
Monotone g) : iSup f + …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.add_lintegral`：add_lintegral (f g : α ->ₛ Real>
=0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono`：lintegral_mono {f g : α ->ₛ Rea
l>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.lintegral μ <= g.lintegral ν
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
-/
theorem lintegral_add_aux {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  calc
    ∫⁻ a, f a + g a ∂μ =
        ∫⁻ a, (⨆ n, (eapprox f n : α → ℝ≥0∞) a) + ⨆ n, (eapprox g n : α → ℝ≥0∞) a ∂μ := by
      simp only [iSup_eapprox_apply, hf, hg]
    _ = ∫⁻ a, ⨆ n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a ∂μ := by
      congr; funext a
      rw [ENNReal.iSup_add_iSup_of_monotone]
      · simp only [Pi.add_apply]
      · intro i j h
        exact monotone_eapprox _ h a
      · intro i j h
        exact monotone_eapprox _ h a
    _ = ⨆ n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.add_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        simp only [Pi.add_apply, SimpleFunc.coe_add]
      · fun_prop
      · intro i j h a
        dsimp
        gcongr <;> exact monotone_eapprox _ h _
    _ = (⨆ n, (eapprox f n).lintegral μ) + ⨆ n, (eapprox g n).lintegral μ := by
      refine (ENNReal.iSup_add_iSup_of_monotone ?_ ?_).symm <;>
        · intro i j h
          exact SimpleFunc.lintegral_mono (monotone_eapprox _ h) le_rfl
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is integrable, see also
`MeasureTheory.lintegral_add_right` and primed versions of these lemmas. -/
@[simp]
/-
**MeasureTheory.lintegral_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_left {f : α -> Real>=0∞} (hf : Measurable f) (g : α -> Real>
=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ
参数：hf : Measurable f；g : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `MeasureTheory.lintegral_add_aux`：lintegral_add_aux {f g : α -> Real>=0∞}
 (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `Measurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ G], 
Meas…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `MeasureTheory.le_lintegral_add`：le_lintegral_add (f g : α -> Real>=0∞) :
 ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ <= ∫⁻ a, f a + g a ∂μ

--- 原说明 ---
If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then
 the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is 
integrable, see also
`MeasureTheory.lintegral_add_right` and primed versions of these lemmas.
-/
theorem lintegral_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  refine le_antisymm ?_ (le_lintegral_add _ _)
  rcases exists_measurable_le_lintegral_eq μ fun a => f a + g a with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, φ a ∂μ := hφ_eq
    _ ≤ ∫⁻ a, f a + (φ a - f a) ∂μ := lintegral_mono fun a => le_add_tsub
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, φ a - f a ∂μ := lintegral_add_aux hf (hφm.sub hf)
    _ ≤ ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by gcongr with a; exact tsub_le_iff_left.2 <| hφ_le _
/-
**MeasureTheory.lintegral_add_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_left' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (g : α -> 
Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ
参数：hf : AEMeasurable f μ；g : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.fun_add`：∀ {α : Type u} {β : Type v} [inst : Add β] 
{f f' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → (fun i => f i + 
f' i) =ᶠ[l] fun i…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem lintegral_add_left' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  rw [lintegral_congr_ae hf.ae_eq_mk, ← lintegral_add_left hf.measurable_mk,
    lintegral_congr_ae (hf.ae_eq_mk.fun_add (ae_eq_refl g))]
/-
**MeasureTheory.lintegral_add_right'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_right' (f : α -> Real>=0∞) {g : α -> Real>=0∞} (hg : AEMeasu
rable g μ) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ
参数：f : α -> Real>=0∞；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
-/
theorem lintegral_add_right' (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  simpa only [add_comm] using lintegral_add_left' hg f

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `g` is integrable, see also
`MeasureTheory.lintegral_add_left` and primed versions of these lemmas. -/
@[simp]
/-
**MeasureTheory.lintegral_add_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_right (f : α -> Real>=0∞) {g : α -> Real>=0∞} (hg : Measurab
le g) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ
参数：f : α -> Real>=0∞；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_add_right'`：lintegral_add_right' (f : α -> Real>
=0∞) {g : α -> Real>=0∞} (hg : AEMeasurable g μ) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f 
a ∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then
 the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `g` is 
integrable, see also
`MeasureTheory.lintegral_add_left` and primed versions of these lemmas.
-/
theorem lintegral_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  lintegral_add_right' f hg.aemeasurable
/-
**MeasureTheory.lintegral_finsetSum'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_finsetSum' (s : Finset β) {f : β -> α -> Real>=0∞} (hf : forall 
b in s, AEMeasurable (f b) μ) : ∫⁻ a, ∑ b in s, f b a ∂μ = ∑ b in s, ∫⁻ a, f b a
 ∂μ
参数：s : Finset β；hf : forall b in s, AEMeasurable (f b) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lintegral_finsetSum' (s : Finset β) {f : β → α → ℝ≥0∞}
    (hf : ∀ b ∈ s, AEMeasurable (f b) μ) :
    ∫⁻ a, ∑ b ∈ s, f b a ∂μ = ∑ b ∈ s, ∫⁻ a, f b a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    rw [Finset.forall_mem_insert] at hf
    rw [lintegral_add_left' hf.1, ih hf.2]

@[deprecated (since := "2026-04-08")] alias lintegral_finset_sum' := lintegral_finsetSum'
/-
**MeasureTheory.lintegral_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_finsetSum (s : Finset β) {f : β -> α -> Real>=0∞} (hf : forall b
 in s, Measurable (f b)) : ∫⁻ a, ∑ b in s, f b a ∂μ = ∑ b in s, ∫⁻ a, f b a ∂μ
参数：s : Finset β；hf : forall b in s, Measurable (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_finsetSum'`：lintegral_finsetSum' (s : Finset β) 
{f : β -> α -> Real>=0∞} (hf : forall b in s, AEMeasurable (f b) μ) : ∫⁻ a, ∑ b 
in s, f b a ∂μ = ∑ b in …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_finsetSum (s : Finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, Measurable (f b)) :
    ∫⁻ a, ∑ b ∈ s, f b a ∂μ = ∑ b ∈ s, ∫⁻ a, f b a ∂μ :=
  lintegral_finsetSum' s fun b hb => (hf b hb).aemeasurable

@[deprecated (since := "2026-04-08")] alias lintegral_finset_sum := lintegral_finsetSum
/-
**MeasureTheory.lintegral_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_tsum [Countable β] {f : β -> α -> Real>=0∞} (hf : forall i, AEMe
asurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ
参数：hf : forall i, AEMeasurable (f i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tsum_eq_iSup_sum`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α)
, f a = ⨆ s, ∑ a ∈ s, f a
· 使用定理 `MeasureTheory.lintegral_iSup_directed`：lintegral_iSup_directed [Countabl
e β] {f : β -> α -> Real>=0∞} (hf : forall b, AEMeasurable (f b) μ) (h_directed 
: Directed (· <= ·) f) : ∫⁻…
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `Finset.aemeasurable_fun_sum`：∀ {M : Type u_2} {ι : Type u_3} {α : Type u
_4} [inst : AddCommMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]   {
m : MeasurableSpa…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_finsetSum'`：lintegral_finsetSum' (s : Finset β) 
{f : β -> α -> Real>=0∞} (hf : forall b in s, AEMeasurable (f b) μ) : ∫⁻ a, ∑ b 
in s, f b a ∂μ = ∑ b in …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_tsum [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ := by
  classical
  simp only [ENNReal.tsum_eq_iSup_sum]
  rw [lintegral_iSup_directed]
  · simp [lintegral_finsetSum' _ fun i _ => hf i]
  · intro b
    exact Finset.aemeasurable_fun_sum _ fun i _ => hf i
  · intro s t
    use s ∪ t
    constructor
    · exact fun a => Finset.sum_le_sum_of_subset Finset.subset_union_left
    · exact fun a => Finset.sum_le_sum_of_subset Finset.subset_union_right

end Add

section Mul

@[simp]
/-
**MeasureTheory.lintegral_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_const_mul (r : Real>=0∞) {f : α -> Real>=0∞} (hf : Measurable f)
 : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
参数：r : Real>=0∞；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用定理 `MeasureTheory.SimpleFunc.const_mul_lintegral`：const_mul_lintegral (f : α
 ->ₛ Real>=0∞) (x : Real>=0∞) : (const α x * f).lintegral μ = x * f.lintegral μ
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
-/
theorem lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ :=
  calc
    ∫⁻ a, r * f a ∂μ = ∫⁻ a, ⨆ n, (const α r * eapprox f n) a ∂μ := by
      congr
      funext a
      rw [← iSup_eapprox_apply hf, ENNReal.mul_iSup]
      simp
    _ = ⨆ n, r * (eapprox f n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.const_mul_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
      · intro n
        exact SimpleFunc.measurable _
      · intro i j h a
        dsimp
        gcongr
        exact monotone_eapprox _ h _
    _ = r * ∫⁻ a, f a ∂μ := by rw [← ENNReal.mul_iSup, lintegral_eq_iSup_eapprox_lintegral hf]
/-
**MeasureTheory.lintegral_const_mul''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_const_mul'' (r : Real>=0∞) {f : α -> Real>=0∞} (hf : AEMeasurabl
e f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
参数：r : Real>=0∞；hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
-/
theorem lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (EventuallyEq.fun_comp hf.ae_eq_mk _)
  rw [A, B, lintegral_const_mul _ hf.measurable_mk]
/-
**MeasureTheory.lintegral_const_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_const_mul_le (r : Real>=0∞) (f : α -> Real>=0∞) : r * ∫⁻ a, f a 
∂μ <= ∫⁻ a, r * f a ∂μ
参数：r : Real>=0∞；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_def`：∀ {α : Type u_4} {m : MeasurableSpace α} (μ
 : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.lintegral μ f = ⨆
 g, ⨆ (_ : ⇑g ≤ f…
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.const_mul_lintegral`：const_mul_lintegral (f : α
 ->ₛ Real>=0∞) (x : Real>=0∞) : (const α x * f).lintegral μ = x * f.lintegral μ
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    r * ∫⁻ a, f a ∂μ ≤ ∫⁻ a, r * f a ∂μ := by
  rw [lintegral, ENNReal.mul_iSup]
  refine iSup_le fun s => ?_
  rw [ENNReal.mul_iSup, iSup_le_iff]
  intro hs
  rw [← SimpleFunc.const_mul_lintegral, lintegral]
  refine le_iSup_of_le (const α r * s) (le_iSup_of_le (fun x => ?_) le_rfl)
  dsimp
  grw [hs x]
/-
**MeasureTheory.lintegral_const_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_const_mul' (r : Real>=0∞) (f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻
 a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
参数：r : Real>=0∞；f : α -> Real>=0∞；hr : r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.lintegral_const_mul_le`：lintegral_const_mul_le (r : Real>=
0∞) (f : α -> Real>=0∞) : r * ∫⁻ a, f a ∂μ <= ∫⁻ a, r * f a ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
theorem lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ := by
  by_cases h : r = 0
  · simp [h]
  apply le_antisymm _ (lintegral_const_mul_le r f)
  have rinv : r * r⁻¹ = 1 := ENNReal.mul_inv_cancel h hr
  have rinv' : r⁻¹ * r = 1 := by
    rw [mul_comm]
    exact rinv
  have := lintegral_const_mul_le (μ := μ) r⁻¹ fun x => r * f x
  simp only [(mul_assoc _ _ _).symm, rinv'] at this
  simpa [(mul_assoc _ _ _).symm, rinv] using mul_le_mul_right this r
/-
**MeasureTheory.lintegral_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mul_const (r : Real>=0∞) {f : α -> Real>=0∞} (hf : Measurable f)
 : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
参数：r : Real>=0∞；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul r hf]
/-
**MeasureTheory.lintegral_mul_const''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mul_const'' (r : Real>=0∞) {f : α -> Real>=0∞} (hf : AEMeasurabl
e f μ) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
参数：r : Real>=0∞；hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_const_mul''`：lintegral_const_mul'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a
 ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul'' r hf]
/-
**MeasureTheory.lintegral_mul_const_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_mul_const_le (r : Real>=0∞) (f : α -> Real>=0∞) : (∫⁻ a, f a ∂μ)
 * r <= ∫⁻ a, f a * r ∂μ
参数：r : Real>=0∞；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.lintegral_const_mul_le`：lintegral_const_mul_le (r : Real>=
0∞) (f : α -> Real>=0∞) : r * ∫⁻ a, f a ∂μ <= ∫⁻ a, r * f a ∂μ
-/
theorem lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂μ) * r ≤ ∫⁻ a, f a * r ∂μ := by
  simp_rw [mul_comm, lintegral_const_mul_le r f]
/-
**MeasureTheory.lintegral_mul_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_mul_const' (r : Real>=0∞) (f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻
 a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
参数：r : Real>=0∞；f : α -> Real>=0∞；hr : r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul' r f hr]

/-- A double integral of a product where each factor contains only one variable
is a product of integrals -/
/-
**MeasureTheory.lintegral_lintegral_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measure β} {f : α -> 
Real>=0∞} {g : β -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) : 
∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν
参数：hf : AEMeasurable f μ；hg : AEMeasurable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_const_mul''`：lintegral_const_mul'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a
 ∂μ
· 使用定理 `MeasureTheory.lintegral_mul_const''`：lintegral_mul_const'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ
) * r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A double integral of a product where each factor contains only one variable
is a product of integrals
-/
theorem lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ≥0∞}
    {g : β → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]

end Mul

section Trim

variable {m m0 : MeasurableSpace α}

/-
**MeasureTheory.lintegral_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_trim {μ : Measure α} (hm : m <= m0) {f : α -> Real>=0∞} (hf : Me
asurable[m] f) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ
参数：hm : m <= m0；hf : Measurable[m] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_induction`：Measurable.ennreal_induction {motive : (α 
-> Real>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s ->
 motive (Set.indic…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lintegral_trim {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  refine
    @Measurable.ennreal_induction α m (fun f => ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ) ?_ ?_ ?_ f hf
  · intro c s hs
    rw [lintegral_indicator hs, lintegral_indicator (hm s hs), setLIntegral_const,
      setLIntegral_const]
    suffices h_trim_s : μ.trim hm s = μ s by rw [h_trim_s]
    exact trim_measurableSet_eq hm hs
  · intro f g _ hf _ hf_prop hg_prop
    have h_m := lintegral_add_left (μ := Measure.trim μ hm) hf g
    have h_m0 := lintegral_add_left (μ := μ) (Measurable.mono hf hm le_rfl) g
    rwa [hf_prop, hg_prop, ← h_m0] at h_m
  · intro f hf hf_mono hf_prop
    rw [lintegral_iSup hf hf_mono]
    rw [lintegral_iSup (fun n => Measurable.mono (hf n) hm le_rfl) hf_mono]
    congr with n
    exact hf_prop n
/-
**MeasureTheory.lintegral_trim_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_trim_ae {μ : Measure α} (hm : m <= m0) {f : α -> Real>=0∞} (hf :
 AEMeasurable f (μ.trim hm)) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ
参数：hm : m <= m0；hf : AEMeasurable f (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.lintegral_trim`：lintegral_trim {μ : Measure α} (hm : m <= 
m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f 
a ∂μ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
-/
theorem lintegral_trim_ae {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.trim hm)) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f a ∂μ := by
  rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), lintegral_congr_ae hf.ae_eq_mk,
    lintegral_trim hm hf.measurable_mk]
/-
**MeasureTheory.setLIntegral_trim_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_trim_ae {μ : Measure α} (hm : m <= m0) {f : α -> Real>=0∞} (h
f : AEMeasurable f (μ.trim hm)) {s : Set α} (hs : MeasurableSet[m] s) : ∫⁻ x in 
s, f x ∂μ.trim hm = ∫⁻ x in s, f x ∂μ
参数：hm : m <= m0；hf : AEMeasurable f (μ.trim hm)；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_trim_ae`：lintegral_trim_ae {μ : Measure α} (hm :
 m <= m0) {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.trim hm)) : ∫⁻ a, f a ∂μ.t
rim hm = ∫⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.restrict_trim`：restrict_trim (hm : m <= m0) (μ : Measure α
) (hs : @MeasurableSet α m s) : @Measure.restrict α m (μ.trim hm) s = (μ.restric
t s).trim hm
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
-/
theorem setLIntegral_trim_ae {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.trim hm)) {s : Set α} (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, f x ∂μ.trim hm = ∫⁻ x in s, f x ∂μ := by
  rw [← lintegral_trim_ae hm]
  all_goals rw [← restrict_trim hm _ hs]
  exact hf.restrict
/-
**MeasureTheory.setLIntegral_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_trim {μ : Measure α} (hm : m <= m0) {f : α -> Real>=0∞} (hf :
 Measurable[m] f) {s : Set α} (hs : MeasurableSet[m] s) : ∫⁻ x in s, f x ∂μ.trim
 hm = ∫⁻ x in s, f x ∂μ
参数：hm : m <= m0；hf : Measurable[m] f；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLIntegral_trim_ae`：setLIntegral_trim_ae {μ : Measure α}
 (hm : m <= m0) {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.trim hm)) {s : Set α
} (hs : MeasurableSet[m]…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setLIntegral_trim {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞}
    (hf : Measurable[m] f) {s : Set α} (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, f x ∂μ.trim hm = ∫⁻ x in s, f x ∂μ :=
  setLIntegral_trim_ae _ hf.aemeasurable hs

end Trim

end MeasureTheory

