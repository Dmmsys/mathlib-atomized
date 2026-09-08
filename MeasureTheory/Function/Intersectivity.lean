/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Bergelson's intersectivity lemma

This file proves the Bergelson intersectivity lemma: In a finite measure space, a sequence of events
that have measure at least `r` has an infinite subset whose finite intersections all have positive
volume.

This is in some sense a finitary version of the second Borel-Cantelli lemma.

## References

[Bergelson, *Sets of recurrence of `ℤᵐ`-actions and properties of sets of differences in
`ℤᵐ`*][bergelson1985]

## TODO

Restate the theorem using the upper density of a set of naturals, once we have it. This will make
`bergelson'` be actually strong (and please then rename it to `strong_bergelson`).

Use the ergodic theorem to deduce the refinement of the Poincaré recurrence theorem proved by
Bergelson.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal

variable {ι α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {r : ℝ≥0∞}

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume.

TODO: The infinity of `t` should be strengthened to `t` having positive natural density. -/
/-
**bergelson'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bergelson' {s : Nat -> Set α} (hs : forall n, MeasurableSet (s n)) (hr₀ : 
r != 0) (hr : forall n, r <= μ (s n)) : exists t : Set Nat, t.Infinite ∧ forall 
⦃u⦄, u subseteq t -> u.Finite -> 0 < μ (⋂ n in u, s n)
参数：hs : forall n, MeasurableSet (s n)；hr₀ : r != 0；hr : forall n, r <= μ (s n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_iUnion_null`：∀ {α : Type u_1} {F : Type u_3} [inst
 : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   {ι
 : Sort u_4} [Countable…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.meas_eLpNormEssSup_lt`：meas_eLpNormEssSup_lt {f : α -> ε} 
: μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.eLpNormEssSup_eq_zero_iff`：eLpNormEssSup_eq_zero_iff {f : 
α -> ε} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Set.indicator_ae_eq_zero`：∀ {α : Type u_1} {F : Type u_3} [inst : FunLik
e F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ : F} {M
 : Type u_4} […
· 使用定理 `Function.support_one`：∀ {ι : Type u_1} (R : Type u_5) [inst : Zero R] [i
nst_1 : One R] [NeZero 1], Function.support 1 = Set.univ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
（共 125 条，此处仅展示前 30 条）

--- 原说明 ---
**Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of eve
nts that have
measure at least `r` has an infinite subset whose finite intersections all have 
positive volume.

TODO: The infinity of `t` should be strengthened to `t` having positive natural 
density.
-/
lemma bergelson' {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n)) (hr₀ : r ≠ 0)
    (hr : ∀ n, r ≤ μ (s n)) :
    ∃ t : Set ℕ, t.Infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.Finite → 0 < μ (⋂ n ∈ u, s n) := by
  -- We let `M f` be the set on which the norm of `f` exceeds its essential supremum, and `N` be the
  -- union of `M` of the finite products of the indicators of the `s n`.
  let M (f : α → ℝ) : Set α := {x | eLpNormEssSup f μ < ‖f x‖₊}
  let N : Set α := ⋃ u : Finset ℕ, M (Set.indicator (⋂ n ∈ u, s n) 1)
  -- `N` is a null set since `M f` is a null set for each `f`.
  have hN₀ : μ N = 0 := measure_iUnion_null fun u ↦ meas_eLpNormEssSup_lt
  -- The important thing about `N` is that if we remove `N` from our space, then finite unions of
  -- the `s n` are null iff they are empty.
  have hN₁ (u : Finset ℕ) : ((⋂ n ∈ u, s n) \ N).Nonempty → 0 < μ (⋂ n ∈ u, s n) := by
    simp_rw [pos_iff_ne_zero]
    rintro ⟨x, hx⟩ hu
    refine hx.2 (mem_iUnion.2 ⟨u, ?_⟩)
    rw [mem_ofPred, indicator_of_mem hx.1, eLpNormEssSup_eq_zero_iff.2]
    · simp
    · rwa [indicator_ae_eq_zero, Function.support_one, inter_univ]
  -- Define `f n` to be the average of the first `n + 1` indicators of the `s k`.
  let f (n : ℕ) : α → ℝ≥0∞ := (↑(n + 1) : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range (n + 1), (s k).indicator 1
  -- We gather a few simple properties of `f`.
  have hfapp : ∀ n a, f n a = (↑(n + 1))⁻¹ * ∑ k ∈ Finset.range (n + 1), (s k).indicator 1 a := by
    simp only [f, Pi.smul_apply, Finset.sum_apply,
    forall_const, imp_true_iff, smul_eq_mul]
  have hf n : Measurable (f n) := by fun_prop (disch := exact hs _)
  have hf₁ n : f n ≤ 1 := by
    rintro a
    rw [hfapp, ← ENNReal.div_eq_inv_mul]
    refine (ENNReal.div_le_iff_le_mul (Or.inl <| Nat.cast_ne_zero.2 n.succ_ne_zero) <|
      Or.inr one_ne_zero).2 ?_
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.card_range n.succ]
    exact Finset.sum_le_card_nsmul _ _ _ fun _ _ ↦ indicator_le (fun _ _ ↦ le_rfl) _
  -- By assumption, `f n` has integral at least `r`.
  have hrf n : r ≤ ∫⁻ a, f n a ∂μ := by
    simp_rw [hfapp]
    rw [lintegral_const_mul _ <| Finset.measurable_fun_sum _
        fun _ _ ↦ measurable_one.indicator <| hs _,
      lintegral_finsetSum _ fun _ _ ↦ measurable_one.indicator (hs _)]
    simp only [lintegral_indicator_one (hs _)]
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (by simp) (by simp), ← nsmul_eq_mul']
    simpa using Finset.card_nsmul_le_sum (Finset.range (n + 1)) _ _ fun _ _ ↦ hr _
  -- Collect some basic fact
  have hμ : μ ≠ 0 := by rintro rfl; exact hr₀ <| le_bot_iff.1 <| hr 0
  have : ∫⁻ x, limsup (f · x) atTop ∂μ ≤ μ univ := by
    rw [← lintegral_one]
    exact lintegral_mono fun a ↦ limsup_le_of_le ⟨0, fun R _ ↦ bot_le⟩ <|
      Eventually.of_forall fun n ↦ hf₁ _ _
  -- By the first moment method, there exists some `x ∉ N` such that `limsup f n x` is at least `r`.
  obtain ⟨x, hxN, hx⟩ := exists_notMem_null_laverage_le hμ
    (ne_top_of_le_ne_top (by finiteness) this) hN₀
  replace hx : r / μ univ ≤ limsup (f · x) atTop :=
    calc
      _ ≤ limsup (⨍⁻ x, f · x ∂μ) atTop := le_limsup_of_le ⟨1, eventually_map.2 ?_⟩ fun b hb ↦ ?_
      _ ≤ ⨍⁻ x, limsup (f · x) atTop ∂μ := limsup_lintegral_le 1 hf (ae_of_all _ <| hf₁ ·) (by simp)
      _ ≤ limsup (f · x) atTop := hx
  -- This exactly means that the `s n` containing `x` have all their finite intersection non-null.
  · refine ⟨{n | x ∈ s n}, fun hxs ↦ ?_, fun u hux hu ↦ ?_⟩
    -- This next block proves that a set of strictly positive natural density is infinite, mixed
    -- with the fact that `{n | x ∈ s n}` has strictly positive natural density.
    -- TODO: Separate it out to a lemma once we have a natural density API.
    · refine ENNReal.div_ne_zero.2 ⟨hr₀, by finiteness⟩ <| eq_bot_mono hx <|
        Tendsto.limsup_eq <| tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (h := fun n ↦ (n.succ : ℝ≥0∞)⁻¹ * hxs.toFinset.card) ?_ bot_le fun n ↦ mul_le_mul_right ?_ _
      · simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_inv_nat_nhds_zero.comp <|
          tendsto_add_atTop_nat 1) (.inr <| ENNReal.natCast_ne_top _)
      · classical
        simpa only [Finset.sum_apply, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_le]
          using! Finset.card_le_card fun m hm ↦ hxs.mem_toFinset.2 (Finset.mem_filter.1 hm).2
    · simp_rw [← hu.mem_toFinset]
      exact hN₁ _ ⟨x, mem_iInter₂.2 fun n hn ↦ hux <| hu.mem_toFinset.1 hn, hxN⟩
  · refine Eventually.of_forall fun n ↦ ?_
    obtain rfl | _ := eq_zero_or_neZero μ
    · simp
    · rw [← laverage_const μ 1]
      exact lintegral_mono (hf₁ _)
  · obtain ⟨n, hn⟩ := hb.exists
    rw [laverage_eq] at hn
    exact (ENNReal.div_le_div_right (hrf _) _).trans hn

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume. -/
/-
**bergelson** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bergelson [Infinite ι] {s : ι -> Set α} (hs : forall i, MeasurableSet (s i
)) (hr₀ : r != 0) (hr : forall i, r <= μ (s i)) : exists t : Set ι, t.Infinite ∧
 forall ⦃u⦄, u subseteq t -> u.Finite -> 0 < μ (⋂ i in u, s i)
参数：hs : forall i, MeasurableSet (s i)；hr₀ : r != 0；hr : forall i, r <= μ (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `bergelson'`：bergelson' {s : Nat -> Set α} (hs : forall n, MeasurableSet 
(s n)) (hr₀ : r != 0) (hr : forall n, r <= μ (s n)) : exists t : Set Nat, t.Infi
…
· 使用定理 `Set.Infinite.image`：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β},
 Set.InjOn f s → s.Infinite → (f '' s).Infinite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Set.preimage_subset_of_surjOn`：preimage_subset_of_surjOn {t : Set β} (hf
 : Injective f) (h : SurjOn f s t) : f ⁻¹' t subseteq s
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j

--- 原说明 ---
**Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of eve
nts that have
measure at least `r` has an infinite subset whose finite intersections all have 
positive volume.
-/
lemma bergelson [Infinite ι] {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (hr₀ : r ≠ 0)
    (hr : ∀ i, r ≤ μ (s i)) :
    ∃ t : Set ι, t.Infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.Finite → 0 < μ (⋂ i ∈ u, s i) := by
  obtain ⟨t, ht, h⟩ := bergelson' (fun n ↦ hs <| Infinite.natEmbedding _ n) hr₀ (fun n ↦ hr _)
  refine ⟨_, ht.image <| (Infinite.natEmbedding _).injective.injOn, fun u hut hu ↦
    (h (preimage_subset_of_surjOn (Infinite.natEmbedding _).injective hut) <| hu.preimage
    (Embedding.injective _).injOn).trans_le <| measure_mono <| subset_iInter₂ fun i hi ↦ ?_⟩
  obtain ⟨n, -, rfl⟩ := hut hi
  exact iInter₂_subset n hi
