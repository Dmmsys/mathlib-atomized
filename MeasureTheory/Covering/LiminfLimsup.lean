/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Liminf, limsup, and uniformly locally doubling measures.

This file is a place to collect lemmas about liminf and limsup for subsets of a metric space
carrying a uniformly locally doubling measure.

## Main results:

* `blimsup_cthickening_mul_ae_eq`: the limsup of the closed thickening of a sequence of subsets
  of a metric space is unchanged almost everywhere for a uniformly locally doubling measure if the
  sequence of distances is multiplied by a positive scale factor. This is a generalisation of a
  result of Cassels, appearing as Lemma 9 on page 217 of
  [J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).
* `blimsup_thickening_mul_ae_eq`: a variant of `blimsup_cthickening_mul_ae_eq` for thickenings
  rather than closed thickenings.

-/

public section


open Set Filter Metric MeasureTheory TopologicalSpace

open scoped NNReal ENNReal Topology

variable {α : Type*}
variable [PseudoMetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
variable (μ : Measure α) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]

/-- This is really an auxiliary result en route to `blimsup_cthickening_ae_le_of_eventually_mul_le`
(which is itself an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`).

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
/-
**blimsup_cthickening_ae_le_of_eventually_mul_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：blimsup_cthickening_ae_le_of_eventually_mul_le_aux (p : Nat -> Prop) {s : 
Nat -> Set α} (hs : forall i, IsClosed (s i)) {r₁ r₂ : Nat -> Real} (hr : Tendst
o r₁ atTop (𝓝[>] 0)) (hrp : 0 <= r₁) {M : Real} (hM : 0 < M) (hM' : M < 1) (hMr 
: forallᶠ i in atTop, M * r₁ i <= r₂ i) : (blimsup (fun i => cthickening (r₁ i) 
(s i)) atTop p : Set α) <=ᵐ[μ] (blimsup (fun i => cthickening (r₂ i) (s i)) atTo
p p : Set α)
参数：p : Nat -> Prop；hs : forall i, IsClosed (s i)；hr : Tendsto r₁ atTop (𝓝[>] 0)；
hrp : 0 <= r₁；hM : 0 < M；hM' : M < 1；hMr : forallᶠ i in atTop, M * r₁ i <= r₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae`：exists_mem_of
_measure_ne_zero_of_ae (hs : μ s != 0) {p : α -> Prop} (hp : forallᵐ x ∂μ.restri
ct s, p x) : exists x, x in s ∧ p x
· 使用定理 `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`：ae_tendsto_measur
e_inter_div (S : Set α) (K : Real) : forallᵐ x ∂μ.restrict S, forall {ι : Type*}
 {l : Filter ι} (w : ι -> α) (δ : ι -> Real…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Filter.exists_forall_mem_of_hasBasis_mem_blimsup'`：exists_forall_mem_of_
hasBasis_mem_blimsup' {l : Filter β} {b : ι -> Set β} (hl : l.HasBasis (fun _ =>
 True) b) {u : β -> Set α} {p : β -> Pr…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 121 条，此处仅展示前 30 条）

--- 原说明 ---
This is really an auxiliary result en route to `blimsup_cthickening_ae_le_of_eve
ntually_mul_le`
(which is itself an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`
).

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932.
-/
theorem blimsup_cthickening_ae_le_of_eventually_mul_le_aux (p : ℕ → Prop) {s : ℕ → Set α}
    (hs : ∀ i, IsClosed (s i)) {r₁ r₂ : ℕ → ℝ} (hr : Tendsto r₁ atTop (𝓝[>] 0)) (hrp : 0 ≤ r₁)
    {M : ℝ} (hM : 0 < M) (hM' : M < 1) (hMr : ∀ᶠ i in atTop, M * r₁ i ≤ r₂ i) :
    (blimsup (fun i => cthickening (r₁ i) (s i)) atTop p : Set α) ≤ᵐ[μ]
      (blimsup (fun i => cthickening (r₂ i) (s i)) atTop p : Set α) := by
  /- Sketch of proof:

  Assume that `p` is identically true for simplicity. Let `Y₁ i = cthickening (r₁ i) (s i)`, define
  `Y₂` similarly except using `r₂`, and let `(Z i) = ⋃_{j ≥ i} (Y₂ j)`. Our goal is equivalent to
  showing that `μ ((limsup Y₁) \ (Z i)) = 0` for all `i`.

  Assume for contradiction that `μ ((limsup Y₁) \ (Z i)) ≠ 0` for some `i` and let
  `W = (limsup Y₁) \ (Z i)`. Apply Lebesgue's density theorem to obtain a point `d` in `W` of
  density `1`. Since `d ∈ limsup Y₁`, there is a subsequence of `j ↦ Y₁ j`, indexed by
  `f 0 < f 1 < ...`, such that `d ∈ Y₁ (f j)` for all `j`. For each `j`, we may thus choose
  `w j ∈ s (f j)` such that `d ∈ B j`, where `B j = closedBall (w j) (r₁ (f j))`. Note that
  since `d` has density one, `μ (W ∩ (B j)) / μ (B j) → 1`.

  We obtain our contradiction by showing that there exists `η < 1` such that
  `μ (W ∩ (B j)) / μ (B j) ≤ η` for sufficiently large `j`. In fact we claim that `η = 1 - C⁻¹`
  is such a value where `C` is the scaling constant of `M⁻¹` for the uniformly locally doubling
  measure `μ`.

  To prove the claim, let `b j = closedBall (w j) (M * r₁ (f j))` and for given `j` consider the
  sets `b j` and `W ∩ (B j)`. These are both subsets of `B j` and are disjoint for large enough `j`
  since `M * r₁ j ≤ r₂ j` and thus `b j ⊆ Z i ⊆ Wᶜ`. We thus have:
  `μ (b j) + μ (W ∩ (B j)) ≤ μ (B j)`. Combining this with `μ (B j) ≤ C * μ (b j)` we obtain
  the required inequality. -/
  set Y₁ : ℕ → Set α := fun i => cthickening (r₁ i) (s i)
  set Y₂ : ℕ → Set α := fun i => cthickening (r₂ i) (s i)
  let Z : ℕ → Set α := fun i => ⋃ (j) (_ : p j ∧ i ≤ j), Y₂ j
  suffices ∀ i, μ (atTop.blimsup Y₁ p \ Z i) = 0 by
    rwa [ae_le_set, @blimsup_eq_iInf_biSup_of_nat _ _ _ Y₂, iInf_eq_iInter, sdiff_iInter,
      measure_iUnion_null_iff]
  intro i
  set W := atTop.blimsup Y₁ p \ Z i
  by_contra contra
  obtain ⟨d, hd, hd'⟩ : ∃ d, d ∈ W ∧ ∀ {ι : Type _} {l : Filter ι} (w : ι → α) (δ : ι → ℝ),
      Tendsto δ l (𝓝[>] 0) → (∀ᶠ j in l, d ∈ closedBall (w j) (2 * δ j)) →
        Tendsto (fun j => μ (W ∩ closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) :=
    Measure.exists_mem_of_measure_ne_zero_of_ae contra
      (IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ W 2)
  replace hd : d ∈ blimsup Y₁ atTop p := ((mem_sdiff _).mp hd).1
  obtain ⟨f : ℕ → ℕ, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup' atTop_basis hd
  simp only [forall_and] at hf
  obtain ⟨hf₀ : ∀ j, d ∈ cthickening (r₁ (f j)) (s (f j)), hf₁, hf₂ : ∀ j, j ≤ f j⟩ := hf
  have hf₃ : Tendsto f atTop atTop :=
    tendsto_atTop_atTop.mpr fun j => ⟨f j, fun i hi => (hf₂ j).trans (hi.trans <| hf₂ i)⟩
  replace hr : Tendsto (r₁ ∘ f) atTop (𝓝[>] 0) := hr.comp hf₃
  replace hMr : ∀ᶠ j in atTop, M * r₁ (f j) ≤ r₂ (f j) := hf₃.eventually hMr
  replace hf₀ : ∀ j, ∃ w ∈ s (f j), d ∈ closedBall w (2 * r₁ (f j)) := by
    intro j
    specialize hrp (f j)
    rw [Pi.zero_apply] at hrp
    rcases eq_or_lt_of_le hrp with (hr0 | hrp')
    · specialize hf₀ j
      rw [← hr0, cthickening_zero, (hs (f j)).closure_eq] at hf₀
      exact ⟨d, hf₀, by simp [← hr0]⟩
    · simpa using mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (s (f j))
        (by positivity) (lt_two_mul_self hrp') (hf₀ j))
  choose w hw hw' using hf₀
  let C := IsUnifLocDoublingMeasure.scalingConstantOf μ M⁻¹
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ M⁻¹)
  suffices ∃ η < (1 : ℝ≥0),
      ∀ᶠ j in atTop, μ (W ∩ closedBall (w j) (r₁ (f j))) / μ (closedBall (w j) (r₁ (f j))) ≤ η by
    obtain ⟨η, hη, hη'⟩ := this
    replace hη' : 1 ≤ η := by
      simpa only [ENNReal.one_le_coe_iff] using
        le_of_tendsto (hd' w (fun j => r₁ (f j)) hr <| Eventually.of_forall hw') hη'
    exact (lt_self_iff_false _).mp (lt_of_lt_of_le hη hη')
  refine ⟨1 - C⁻¹, tsub_lt_self zero_lt_one (inv_pos.mpr hC), ?_⟩
  replace hC : C ≠ 0 := ne_of_gt hC
  let b : ℕ → Set α := fun j => closedBall (w j) (M * r₁ (f j))
  let B : ℕ → Set α := fun j => closedBall (w j) (r₁ (f j))
  have h₁ : ∀ j, b j ⊆ B j := fun j =>
    closedBall_subset_closedBall (mul_le_of_le_one_left (hrp (f j)) hM'.le)
  have h₂ : ∀ j, W ∩ B j ⊆ B j := fun j => inter_subset_right
  have h₃ : ∀ᶠ j in atTop, Disjoint (b j) (W ∩ B j) := by
    apply hMr.mp
    rw [eventually_atTop]
    refine
      ⟨i, fun j hj hj' => Disjoint.inf_right (B j) <| Disjoint.inf_right' (blimsup Y₁ atTop p) ?_⟩
    change Disjoint (b j) (Z i)ᶜ
    rw [disjoint_compl_right_iff_subset]
    refine (closedBall_subset_cthickening (hw j) (M * r₁ (f j))).trans
      ((cthickening_mono hj' _).trans fun a ha => ?_)
    simp only [Z, mem_iUnion, exists_prop]
    exact ⟨f j, ⟨hf₁ j, hj.trans (hf₂ j)⟩, ha⟩
  have h₄ : ∀ᶠ j in atTop, μ (B j) ≤ C * μ (b j) :=
    (hr.eventually (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'
      μ M hM)).mono fun j hj => hj (w j)
  refine (h₃.and h₄).mono fun j hj₀ => ?_
  change μ (W ∩ B j) / μ (B j) ≤ ↑(1 - C⁻¹)
  rcases eq_or_ne (μ (B j)) ∞ with (hB | hB); · simp [hB]
  apply ENNReal.div_le_of_le_mul
  rw [ENNReal.coe_sub, ENNReal.coe_one, ENNReal.sub_mul fun _ _ => hB, one_mul]
  replace hB : ↑C⁻¹ * μ (B j) ≠ ∞ := by finiteness
  obtain ⟨hj₁ : Disjoint (b j) (W ∩ B j), hj₂ : μ (B j) ≤ C * μ (b j)⟩ := hj₀
  replace hj₂ : ↑C⁻¹ * μ (B j) ≤ μ (b j) := by
    rw [ENNReal.coe_inv hC, ← ENNReal.div_eq_inv_mul]
    exact ENNReal.div_le_of_le_mul' hj₂
  have hj₃ : ↑C⁻¹ * μ (B j) + μ (W ∩ B j) ≤ μ (B j) := by
    grw [hj₂]
    rw [← measure_union' hj₁ measurableSet_closedBall]
    grw [union_subset (h₁ j) (h₂ j)]
  replace hj₃ := tsub_le_tsub_right hj₃ (↑C⁻¹ * μ (B j))
  rwa [ENNReal.add_sub_cancel_left hB] at hj₃

/-- This is really an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
/-
**blimsup_cthickening_ae_le_of_eventually_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：blimsup_cthickening_ae_le_of_eventually_mul_le (p : Nat -> Prop) {s : Nat 
-> Set α} {M : Real} (hM : 0 < M) {r₁ r₂ : Nat -> Real} (hr : Tendsto r₁ atTop (
𝓝[>] 0)) (hMr : forallᶠ i in atTop, M * r₁ i <= r₂ i) : (blimsup (fun i => cthic
kening (r₁ i) (s i)) atTop p : Set α) <=ᵐ[μ] (blimsup (fun i => cthickening (r₂ 
i) (s i)) atTop p : Set α)
参数：p : Nat -> Prop；hM : 0 < M；hr : Tendsto r₁ atTop (𝓝[>] 0)；hMr : forallᶠ i in 
atTop, M * r₁ i <= r₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_max_zero`：cthickening_max_zero (δ : Real) (E : Set α)
 : cthickening (max 0 δ) E = cthickening δ E
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Filter.mono_blimsup'`：mono_blimsup' (h : forallᶠ x in f, p x -> u x <= v
 x) : blimsup u f p <= blimsup v f p
· 使用定理 `Metric.cthickening_mono`：cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂
) (E : Set α) : cthickening δ₁ E subseteq cthickening δ₂ E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Metric.cthickening_closure`：cthickening_closure : cthickening δ (closure
 s) = cthickening δ s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `blimsup_cthickening_ae_le_of_eventually_mul_le_aux`：blimsup_cthickening_
ae_le_of_eventually_mul_le_aux (p : Nat -> Prop) {s : Nat -> Set α} (hs : forall
 i, IsClosed (s i)) {r₁ r₂ : Nat -> Real…
· 使用定理 `Filter.tendsto_nhds_max_right`：Filter.tendsto_nhds_max_right {l : Filter
 β} {a : α} (h : Tendsto f l (𝓝[>] a)) : Tendsto (fun i => max a (f i)) l (𝓝[>] 
a)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
This is really an auxiliary result en route to `blimsup_cthickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932.
-/
theorem blimsup_cthickening_ae_le_of_eventually_mul_le (p : ℕ → Prop) {s : ℕ → Set α} {M : ℝ}
    (hM : 0 < M) {r₁ r₂ : ℕ → ℝ} (hr : Tendsto r₁ atTop (𝓝[>] 0))
    (hMr : ∀ᶠ i in atTop, M * r₁ i ≤ r₂ i) :
    (blimsup (fun i => cthickening (r₁ i) (s i)) atTop p : Set α) ≤ᵐ[μ]
      (blimsup (fun i => cthickening (r₂ i) (s i)) atTop p : Set α) := by
  let R₁ i := max 0 (r₁ i)
  let R₂ i := max 0 (r₂ i)
  have hRp : 0 ≤ R₁ := fun i => le_max_left 0 (r₁ i)
  replace hMr : ∀ᶠ i in atTop, M * R₁ i ≤ R₂ i := by
    refine hMr.mono fun i hi ↦ ?_
    rw [mul_max_of_nonneg _ _ hM.le, mul_zero]
    exact max_le_max (le_refl 0) hi
  simp_rw [← cthickening_max_zero (r₁ _), ← cthickening_max_zero (r₂ _)]
  rcases le_or_gt 1 M with hM' | hM'
  · apply LE.le.eventuallyLE
    refine mono_blimsup' (hMr.mono fun i hi _ => cthickening_mono ?_ (s i))
    exact (le_mul_of_one_le_left (hRp i) hM').trans hi
  · simp only [← @cthickening_closure _ _ _ (s _)]
    have hs : ∀ i, IsClosed (closure (s i)) := fun i => isClosed_closure
    exact blimsup_cthickening_ae_le_of_eventually_mul_le_aux μ p hs
      (tendsto_nhds_max_right hr) hRp hM hM' hMr

/-- Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the closed
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

See also `blimsup_thickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
/-
**blimsup_cthickening_mul_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：blimsup_cthickening_mul_ae_eq (p : Nat -> Prop) (s : Nat -> Set α) {M : Re
al} (hM : 0 < M) (r : Nat -> Real) (hr : Tendsto r atTop (𝓝 0)) : (blimsup (fun 
i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ] (blimsup (fun i => cthi
ckening (r i) (s i)) atTop p : Set α)
参数：p : Nat -> Prop；s : Nat -> Set α；hM : 0 < M；r : Nat -> Real；hr : Tendsto r at
Top (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.TendstoNhdsWithinIoi.const_mul`：Filter.TendstoNhdsWithinIoi.const
_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => b * f a
) l (𝓝[>] (b * c))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `blimsup_cthickening_ae_le_of_eventually_mul_le`：blimsup_cthickening_ae_l
e_of_eventually_mul_le (p : Nat -> Prop) {s : Nat -> Set α} {M : Real} (hM : 0 <
 M) {r₁ r₂ : Nat -> Real} (hr : Tend…
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Tendsto.if'`：∀ {α : Type u_5} {β : Type u_6} {l₁ : Filter α} {l₂ 
: Filter β} {f g : α → β} {p : α → Prop} [inst : DecidablePred p],   Filter.Tend
sto f l₁…
· 使用定理 `tendsto_one_div_add_atTop_nhds_zero_nat`：tendsto_one_div_add_atTop_nhds_
zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [Con
tinuousSMul Rat>=0 𝕜] : Tends…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of 
radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the clo
sed
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally 
doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](casse
ls1950).

See also `blimsup_thickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932.
-/
theorem blimsup_cthickening_mul_ae_eq (p : ℕ → Prop) (s : ℕ → Set α) {M : ℝ} (hM : 0 < M)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
  have : ∀ (p : ℕ → Prop) {r : ℕ → ℝ} (_ : Tendsto r atTop (𝓝[>] 0)),
      (blimsup (fun i => cthickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
        (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) := by
    clear p hr r; intro p r hr
    have hr' : Tendsto (fun i => M * r i) atTop (𝓝[>] 0) := by
      convert! TendstoNhdsWithinIoi.const_mul hM hr <;> simp only [mul_zero]
    refine eventuallyLE_antisymm_iff.mpr ⟨?_, ?_⟩
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p (inv_pos.mpr hM) hr'
        (Eventually.of_forall fun i => by rw [inv_mul_cancel_left₀ hM.ne' (r i)])
    · exact blimsup_cthickening_ae_le_of_eventually_mul_le μ p hM hr
        (Eventually.of_forall fun i => le_refl _)
  let r' : ℕ → ℝ := fun i => if 0 < r i then r i else 1 / ((i : ℝ) + 1)
  have hr' : Tendsto r' atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨Tendsto.if' hr tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun i => ?_⟩
    by_cases hi : 0 < r i
    · simp [r', hi]
    · simp only [r', hi, one_div, mem_Ioi, if_false, inv_pos]; positivity
  have h₀ : ∀ i, p i ∧ 0 < r i → cthickening (r i) (s i) = cthickening (r' i) (s i) := by
    grind
  have h₁ : ∀ i, p i ∧ 0 < r i → cthickening (M * r i) (s i) = cthickening (M * r' i) (s i) := by
    rintro i ⟨-, hi⟩; simp only [r', hi, if_true]
  have h₂ : ∀ i, p i ∧ r i ≤ 0 → cthickening (M * r i) (s i) = cthickening (r i) (s i) := by
    rintro i ⟨-, hi⟩
    have hi' : M * r i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hi
    rw [cthickening_of_nonpos hi, cthickening_of_nonpos hi']
  have hp : p = fun i => p i ∧ 0 < r i ∨ p i ∧ r i ≤ 0 := by
    ext i; simp [← and_or_left, lt_or_ge 0 (r i)]
  rw [hp, blimsup_or_eq_sup, blimsup_or_eq_sup]
  simp only [sup_eq_union]
  rw [blimsup_congr (Eventually.of_forall h₀), blimsup_congr (Eventually.of_forall h₁),
    blimsup_congr (Eventually.of_forall h₂)]
  exact ae_eq_set_union (this (fun i => p i ∧ 0 < r i) hr') (ae_eq_refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**blimsup_cthickening_ae_eq_blimsup_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：blimsup_cthickening_ae_eq_blimsup_thickening {p : Nat -> Prop} {s : Nat ->
 Set α} {r : Nat -> Real} (hr : Tendsto r atTop (𝓝 0)) (hr' : forallᶠ i in atTop
, p i -> 0 < r i) : (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α)
 =ᵐ[μ] (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α)
参数：hr : Tendsto r atTop (𝓝 0)；hr' : forallᶠ i in atTop, p i -> 0 < r i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyLE_congr`：eventuallyLE_congr {f f' g g' : α -> β} (hf :
 f =ᶠ[l] f') (hg : g =ᶠ[l] g') : f <=ᶠ[l] g ↔ f' <=ᶠ[l] g'
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `blimsup_cthickening_mul_ae_eq`：blimsup_cthickening_mul_ae_eq (p : Nat ->
 Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M) (r : Nat -> Real) (hr : Tendst
o r atTop (𝓝 0)) : …
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Filter.mono_blimsup'`：mono_blimsup' (h : forallᶠ x in f, p x -> u x <= v
 x) : blimsup u f p <= blimsup v f p
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Metric.cthickening_subset_thickening'`：cthickening_subset_thickening' {δ
₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) : cthickening δ₁ E su
bseteq thickening δ₂ E
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 77 条，此处仅展示前 30 条）
-/
theorem blimsup_cthickening_ae_eq_blimsup_thickening {p : ℕ → Prop} {s : ℕ → Set α} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hr' : ∀ᶠ i in atTop, p i → 0 < r i) :
    (blimsup (fun i => cthickening (r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  refine eventuallyLE_antisymm_iff.mpr ⟨?_, LE.le.eventuallyLE ?_⟩
  · rw [eventuallyLE_congr (blimsup_cthickening_mul_ae_eq μ p s (one_half_pos (α := ℝ)) r hr).symm
      EventuallyEq.rfl]
    apply LE.le.eventuallyLE
    refine mono_blimsup' (hr'.mono fun i hi pi => cthickening_subset_thickening' (hi pi) ?_ (s i))
    nlinarith [hi pi]
  · exact mono_blimsup fun i _ => thickening_subset_cthickening _ _

/-- An auxiliary result en route to `blimsup_thickening_mul_ae_eq`. -/
/-
**blimsup_thickening_mul_ae_eq_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：blimsup_thickening_mul_ae_eq_aux (p : Nat -> Prop) (s : Nat -> Set α) {M :
 Real} (hM : 0 < M) (r : Nat -> Real) (hr : Tendsto r atTop (𝓝 0)) (hr' : forall
ᶠ i in atTop, p i -> 0 < r i) : (blimsup (fun i => thickening (M * r i) (s i)) a
tTop p : Set α) =ᵐ[μ] (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α
)
参数：p : Nat -> Prop；s : Nat -> Set α；hM : 0 < M；r : Nat -> Real；hr : Tendsto r at
Top (𝓝 0)；hr' : forallᶠ i in atTop, p i -> 0 < r i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `blimsup_cthickening_ae_eq_blimsup_thickening`：blimsup_cthickening_ae_eq_
blimsup_thickening {p : Nat -> Prop} {s : Nat -> Set α} {r : Nat -> Real} (hr : 
Tendsto r atTop (𝓝 0)) (hr' : fora…
· 使用定理 `blimsup_cthickening_mul_ae_eq`：blimsup_cthickening_mul_ae_eq (p : Nat ->
 Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M) (r : Nat -> Real) (hr : Tendst
o r atTop (𝓝 0)) : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
An auxiliary result en route to `blimsup_thickening_mul_ae_eq`.
-/
theorem blimsup_thickening_mul_ae_eq_aux (p : ℕ → Prop) (s : ℕ → Set α) {M : ℝ} (hM : 0 < M)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hr' : ∀ᶠ i in atTop, p i → 0 < r i) :
    (blimsup (fun i => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  have h₁ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  have h₂ := blimsup_cthickening_mul_ae_eq μ p s hM r hr
  replace hr : Tendsto (fun i => M * r i) atTop (𝓝 0) := by convert! hr.const_mul M; simp
  replace hr' : ∀ᶠ i in atTop, p i → 0 < M * r i := hr'.mono fun i hi hip ↦ mul_pos hM (hi hip)
  have h₃ := blimsup_cthickening_ae_eq_blimsup_thickening (s := s) μ hr hr'
  exact h₃.symm.trans (h₂.trans h₁)

/-- Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](cassels1950).

See also `blimsup_cthickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932. -/
/-
**blimsup_thickening_mul_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：blimsup_thickening_mul_ae_eq (p : Nat -> Prop) (s : Nat -> Set α) {M : Rea
l} (hM : 0 < M) (r : Nat -> Real) (hr : Tendsto r atTop (𝓝 0)) : (blimsup (fun i
 => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ] (blimsup (fun i => thicke
ning (r i) (s i)) atTop p : Set α)
参数：p : Nat -> Prop；s : Nat -> Set α；hM : 0 < M；r : Nat -> Real；hr : Tendsto r at
Top (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_congr'`：blimsup_congr' {f : Filter β} {p q : β -> Prop} {
u : β -> α} (h : forallᶠ x in f, u x != ⊥ -> (p x ↔ q x)) : blimsup u f p = blim
sup u f q
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.thickening_nonempty_iff`：∀ {α : Type u} [inst : PseudoEMetricSpac
e α] {ε : ℝ} {s : Set α}, (Metric.thickening ε s).Nonempty ↔ 0 < ε ∧ s.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `mul_pos_iff_of_pos_left`：mul_pos_iff_of_pos_left [PosMulStrictMono α] [P
osMulReflectLT α] (h : 0 < a) : 0 < a * b ↔ 0 < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `blimsup_thickening_mul_ae_eq_aux`：blimsup_thickening_mul_ae_eq_aux (p : 
Nat -> Prop) (s : Nat -> Set α) {M : Real} (hM : 0 < M) (r : Nat -> Real) (hr : 
Tendsto r atTop (𝓝 0))…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Given a sequence of subsets `sᵢ` of a metric space, together with a sequence of 
radii `rᵢ`
such that `rᵢ → 0`, the set of points which belong to infinitely many of the
`rᵢ`-thickenings of `sᵢ` is unchanged almost everywhere for a uniformly locally 
doubling measure if
the `rᵢ` are all scaled by a positive constant.

This lemma is a generalisation of Lemma 9 appearing on page 217 of
[J.W.S. Cassels, *Some metrical theorems in Diophantine approximation. I*](casse
ls1950).

See also `blimsup_cthickening_mul_ae_eq`.

NB: The `: Set α` type ascription is present because of
https://github.com/leanprover-community/mathlib/issues/16932.
-/
theorem blimsup_thickening_mul_ae_eq (p : ℕ → Prop) (s : ℕ → Set α) {M : ℝ} (hM : 0 < M) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) :
    (blimsup (fun i => thickening (M * r i) (s i)) atTop p : Set α) =ᵐ[μ]
      (blimsup (fun i => thickening (r i) (s i)) atTop p : Set α) := by
  let q : ℕ → Prop := fun i => p i ∧ 0 < r i
  have hq {u : ℕ → Set α} (hu : ∀ i, u i ≠ ∅ → 0 < r i) :
      blimsup u atTop p = blimsup u atTop q :=
    blimsup_congr' <| Eventually.of_forall fun i hi ↦ by simp [q, hu i hi]
  rw [hq fun i hi ↦ (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1,
    hq fun i hi ↦ (mul_pos_iff_of_pos_left hM).1 <|
      (thickening_nonempty_iff.1 <| nonempty_iff_ne_empty.2 hi).1]
  exact blimsup_thickening_mul_ae_eq_aux μ q s hM r hr (Eventually.of_forall fun i hi => hi.2)
