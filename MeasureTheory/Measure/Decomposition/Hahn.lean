/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Loic Simon
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Unsigned Hahn decomposition theorem

This file proves the unsigned version of the Hahn decomposition theorem.

## Main definitions

* `MeasureTheory.IsHahnDecomposition`: characterizes a set where `μ ≤ ν` (and the
  reverse inequality on the complement),

## Main statements

* `hahn_decomposition` : Given two finite measures `μ` and `ν`, there exists a measurable set `s`
  such that any measurable set `t` included in `s` satisfies `ν t ≤ μ t`, and any
  measurable set `u` included in the complement of `s` satisfies `μ u ≤ ν u`.
* `exists_isHahnDecomposition` : reformulation of `hahn_decomposition` using the
  `IsHahnDecomposition` structure which relies on the measure restriction.

## Tags

Hahn decomposition
-/

public section

assert_not_exists MeasureTheory.Measure.rnDeriv
assert_not_exists MeasureTheory.VectorMeasure

open Set Filter Topology ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Hahn decomposition theorem** -/
/-
**MeasureTheory.hahn_decomposition** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hahn_decomposition (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure 
ν] : exists s, MeasurableSet s ∧ (forall t, MeasurableSet t -> t subseteq s -> ν
 t <= μ t) ∧ forall t, MeasurableSet t -> t subseteq sᶜ -> μ t <= ν t
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `ENNReal.toNNReal_add`：toNNReal_add {r₁ r₂ : Real>=0∞} (h₁ : r₁ != ∞) (h₂
 : r₂ != ∞) : (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Decomposition.Hahn.0.MeasureTheor
y.hahn_decomposition._abel_1_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ ν :
 MeasureTheory.Measure α) (s t : Set α),   ↑(μ (s ∩ t)).toNNReal + ↑(μ (s \ t)).
toNNReal + (…
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toNNReal`：tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) 
: Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal)
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atTop`：tendsto_measure_iInter_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
（共 192 条，此处仅展示前 30 条）

--- 原说明 ---
**Hahn decomposition theorem**
-/
theorem hahn_decomposition (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ s, MeasurableSet s ∧ (∀ t, MeasurableSet t → t ⊆ s → ν t ≤ μ t) ∧
      ∀ t, MeasurableSet t → t ⊆ sᶜ → μ t ≤ ν t := by
  let d : Set α → ℝ := fun s => ((μ s).toNNReal : ℝ) - (ν s).toNNReal
  let c : Set ℝ := d '' { s | MeasurableSet s }
  let γ : ℝ := sSup c
  have hμ : ∀ s, μ s ≠ ∞ := measure_ne_top μ
  have hν : ∀ s, ν s ≠ ∞ := measure_ne_top ν
  have to_nnreal_μ : ∀ s, ((μ s).toNNReal : ℝ≥0∞) = μ s := fun s => ENNReal.coe_toNNReal <| hμ _
  have to_nnreal_ν : ∀ s, ((ν s).toNNReal : ℝ≥0∞) = ν s := fun s => ENNReal.coe_toNNReal <| hν _
  have d_split s t (ht : MeasurableSet t) : d s = d (s \ t) + d (s ∩ t) := by
    dsimp only [d]
    rw [← measure_inter_add_sdiff s ht, ← measure_inter_add_sdiff s ht,
      ENNReal.toNNReal_add (hμ _) (hμ _), ENNReal.toNNReal_add (hν _) (hν _), NNReal.coe_add,
      NNReal.coe_add]
    simp only [sub_eq_add_neg, neg_add]
    abel
  have d_Union (s : ℕ → Set α) (hm : Monotone s) :
    Tendsto (fun n => d (s n)) atTop (𝓝 (d (⋃ n, s n))) := by
    refine Tendsto.sub ?_ ?_ <;>
      refine NNReal.tendsto_coe.2 <| (ENNReal.tendsto_toNNReal ?_).comp <|
        tendsto_measure_iUnion_atTop hm
    · exact hμ _
    · exact hν _
  have d_Inter (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) (hm : ∀ n m, n ≤ m → s m ⊆ s n) :
        Tendsto (fun n => d (s n)) atTop (𝓝 (d (⋂ n, s n))) := by
    refine Tendsto.sub ?_ ?_ <;>
      refine NNReal.tendsto_coe.2 <| (ENNReal.tendsto_toNNReal <| ?_).comp <|
        tendsto_measure_iInter_atTop (fun n ↦ (hs n).nullMeasurableSet) hm ?_
    exacts [hμ _, ⟨0, hμ _⟩, hν _, ⟨0, hν _⟩]
  have bdd_c : BddAbove c := by
    use (μ univ).toNNReal
    rintro r ⟨s, _hs, rfl⟩
    refine le_trans (sub_le_self _ <| NNReal.coe_nonneg _) ?_
    rw [NNReal.coe_le_coe, ← ENNReal.coe_le_coe, to_nnreal_μ, to_nnreal_μ]
    exact measure_mono (subset_univ _)
  have c_nonempty : c.Nonempty := Nonempty.image _ ⟨_, MeasurableSet.empty⟩
  have d_le_γ : ∀ s, MeasurableSet s → d s ≤ γ := fun s hs => le_csSup bdd_c ⟨s, hs, rfl⟩
  have (n : ℕ) : ∃ s : Set α, MeasurableSet s ∧ γ - (1 / 2) ^ n < d s := by
    have : γ - (1 / 2) ^ n < γ := sub_lt_self γ (pow_pos (half_pos zero_lt_one) n)
    rcases exists_lt_of_lt_csSup c_nonempty this with ⟨r, ⟨s, hs, rfl⟩, hlt⟩
    exact ⟨s, hs, hlt⟩
  rcases Classical.axiom_of_choice this with ⟨e, he⟩
  change ℕ → Set α at e
  have he₁ : ∀ n, MeasurableSet (e n) := fun n => (he n).1
  have he₂ : ∀ n, γ - (1 / 2) ^ n < d (e n) := fun n => (he n).2
  let f : ℕ → ℕ → Set α := fun n m => (Finset.Ico n (m + 1)).inf e
  have hf n m : MeasurableSet (f n m) := by
    simp only [f, Finset.inf_eq_iInf]
    exact MeasurableSet.biInter (to_countable _) fun i _ => he₁ _
  have f_subset_f {a b c d} (hab : a ≤ b) (hcd : c ≤ d) : f a d ⊆ f b c := by
    simp_rw [f, Finset.inf_eq_iInf]
    exact biInter_subset_biInter_left (Finset.Ico_subset_Ico hab <| Nat.succ_le_succ hcd)
  have f_succ n m (hnm : n ≤ m) : f n (m + 1) = f n m ∩ e (m + 1) := by
    have : n ≤ m + 1 := le_of_lt (Nat.succ_le_succ hnm)
    simp_rw [f, ← Finset.insert_Ico_right_eq_Ico_add_one this, Finset.inf_insert,
      Set.inter_comm]
    rfl
  have le_d_f n m (h : m ≤ n) : γ - 2 * (1 / 2) ^ m + (1 / 2) ^ n ≤ d (f m n) := by
    refine Nat.le_induction ?_ ?_ n h
    · have := he₂ m
      simp_rw [f, Nat.Ico_succ_singleton, Finset.inf_singleton]
      linarith
    · intro n (hmn : m ≤ n) ih
      refine le_of_add_le_add_left (a := γ) ?_
      calc
        γ + (γ - 2 * (1 / 2) ^ m + (1 / 2) ^ (n + 1)) =
            γ + (γ - 2 * (1 / 2) ^ m + ((1 / 2) ^ n - (1 / 2) ^ (n + 1))) := by
          rw [pow_succ, mul_one_div, _root_.sub_half]
        _ = γ - (1 / 2) ^ (n + 1) + (γ - 2 * (1 / 2) ^ m + (1 / 2) ^ n) := by
          simp only [sub_eq_add_neg]; abel
        _ ≤ d (e (n + 1)) + d (f m n) := add_le_add (le_of_lt <| he₂ _) ih
        _ ≤ d (e (n + 1)) + d (f m n \ e (n + 1)) + d (f m (n + 1)) := by
          rw [f_succ _ _ hmn, d_split (f m n) (e (n + 1)) (he₁ _), add_assoc]
        _ = d (e (n + 1) ∪ f m n) + d (f m (n + 1)) := by
          rw [d_split (e (n + 1) ∪ f m n) (e (n + 1)), union_sdiff_left, union_inter_cancel_left]
          · abel
          · exact he₁ _
        _ ≤ γ + d (f m (n + 1)) := by grw [d_le_γ _ <| (he₁ _).union (hf _ _)]
  let s := ⋃ m, ⋂ n, f m n
  have γ_le_d_s : γ ≤ d s := by
    have hγ : Tendsto (fun m : ℕ => γ - 2 * (1 / 2) ^ m) atTop (𝓝 γ) := by
      suffices Tendsto (fun m : ℕ => γ - 2 * (1 / 2) ^ m) atTop (𝓝 (γ - 2 * 0)) by
        simpa only [mul_zero, tsub_zero]
      exact
        tendsto_const_nhds.sub <|
          tendsto_const_nhds.mul <|
            tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt <| half_pos <| zero_lt_one)
              (half_lt_self zero_lt_one)
    have hd : Tendsto (fun m => d (⋂ n, f m n)) atTop (𝓝 (d (⋃ m, ⋂ n, f m n))) := by
      refine d_Union _ ?_
      exact fun n m hnm =>
        subset_iInter fun i => Subset.trans (iInter_subset (f n) i) <| f_subset_f hnm <| le_rfl
    refine le_of_tendsto_of_tendsto' hγ hd fun m => ?_
    have : Tendsto (fun n => d (f m n)) atTop (𝓝 (d (⋂ n, f m n))) := by
      refine d_Inter _ ?_ ?_
      · intro n
        exact hf _ _
      · intro n m hnm
        exact f_subset_f le_rfl hnm
    refine ge_of_tendsto this (eventually_atTop.2 ⟨m, fun n hmn => ?_⟩)
    change γ - 2 * (1 / 2) ^ m ≤ d (f m n)
    refine le_trans ?_ (le_d_f _ _ hmn)
    exact le_add_of_le_of_nonneg le_rfl (pow_nonneg (le_of_lt <| half_pos <| zero_lt_one) _)
  have hs : MeasurableSet s := MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m => hf _ _
  refine ⟨s, hs, ?_, ?_⟩
  · intro t ht hts
    have : 0 ≤ d t :=
      (add_le_add_iff_left γ).1 <|
        calc
          γ + 0 ≤ d s := by rw [add_zero]; exact γ_le_d_s
          _ = d (s \ t) + d t := by rw [d_split s _ ht, inter_eq_self_of_subset_right hts]
          _ ≤ γ + d t := add_le_add (d_le_γ _ (hs.diff ht)) le_rfl
    rw [← to_nnreal_μ, ← to_nnreal_ν, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    simpa only [d, le_sub_iff_add_le, zero_add] using this
  · intro t ht hts
    have : d t ≤ 0 :=
      (add_le_add_iff_left γ).1 <|
        calc
          γ + d t ≤ d s + d t := by gcongr
          _ = d (s ∪ t) := by
            rw [d_split (s ∪ t) _ ht, union_sdiff_right, union_inter_cancel_right,
              (subset_compl_iff_disjoint_left.1 hts).sdiff_eq_left]
          _ ≤ γ + 0 := by rw [add_zero]; exact d_le_γ _ (hs.union ht)
    rw [← to_nnreal_μ, ← to_nnreal_ν, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    simpa only [d, sub_le_iff_le_add, zero_add] using this


/-- A set where `μ ≤ ν` (and the reverse inequality on the complement),
defined via measurable set and measure restriction comparisons. -/
/-
**MeasureTheory.IsHahnDecomposition** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {mα : MeasurableSpace α} → MeasureTheory.Measure α → Meas
ureTheory.Measure α → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set where `μ ≤ ν` (and the reverse inequality on the complement),
defined via measurable set and measure restriction comparisons.
-/
structure IsHahnDecomposition (μ ν : Measure α) (s : Set α) : Prop where
  measurableSet : MeasurableSet s
  le_on : μ.restrict s ≤ ν.restrict s
  ge_on_compl : ν.restrict sᶜ ≤ μ.restrict sᶜ
/-
**MeasureTheory.IsHahnDecomposition.compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IsHahnDecomposition`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
{s : Set α},   MeasureTheory.IsHahnDecomposition μ ν s → MeasureTheory.IsHahnDec
omposition ν μ sᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.IsHahnDecomposition.measurableSet`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.
IsHahnDecomposition μ ν s → Measurabl…
· 使用定理 `MeasureTheory.IsHahnDecomposition.ge_on_compl`：∀ {α : Type u_1} {mα : Me
asurableSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.Is
HahnDecomposition μ ν s → ν.restric…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.IsHahnDecomposition.le_on`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.IsHahnDe
composition μ ν s → μ.restric…
-/
lemma IsHahnDecomposition.compl {μ ν : Measure α} {s : Set α}
    (h : IsHahnDecomposition μ ν s) : IsHahnDecomposition ν μ sᶜ where
  measurableSet := h.measurableSet.compl
  le_on := h.ge_on_compl
  ge_on_compl := by simpa using h.le_on
/-
**MeasureTheory.exists_isHahnDecomposition** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：exists_isHahnDecomposition (μ ν : Measure α) [IsFiniteMeasure μ] [IsFinite
Measure ν] : exists s : Set α, IsHahnDecomposition μ ν s
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hahn_decomposition`：hahn_decomposition (μ ν : Measure α) [
IsFiniteMeasure μ] [IsFiniteMeasure ν] : exists s, MeasurableSet s ∧ (forall t, 
MeasurableSet t -> t s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma exists_isHahnDecomposition (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ s : Set α, IsHahnDecomposition μ ν s := by
  obtain ⟨s, hs, h₁, h₂⟩ := hahn_decomposition ν μ
  refine ⟨s, hs, ?_, ?_⟩
  all_goals
    rw [Measure.le_iff]
    intros
    simp [*]

end MeasureTheory

