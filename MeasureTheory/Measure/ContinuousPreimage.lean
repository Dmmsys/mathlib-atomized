/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Continuity of the preimage of a set under a measure-preserving continuous function

In this file we prove that the preimage of a null measurable set `s : Set Y`
under a measure-preserving continuous function `f : C(X, Y)` is continuous in `f`
in the sense that `μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))` tends to zero as `f a` tends to `g`.

As a corollary, we show that
for a continuous family of continuous maps `f z : C(X, Y)`,
a null measurable set `s`, and a null measurable set `t` of finite measure,
the set of parameters `z` such that `f z ⁻¹' t` is a.e. equal to `s` is a closed set.
-/

public section

open Filter Set
open scoped ENNReal symmDiff Topology

namespace MeasureTheory

variable {α X Y Z : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  [TopologicalSpace Z]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

/-- Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compact sets
and `ν` is a locally finite measure.
Let `f : α → C(X, Y)` be a family of continuous maps
that converges to a continuous map `g : C(X, Y)` in the compact-open topology along a filter `l`.
Suppose that `g` is a measure-preserving map
and `f a` is a measure-preserving map eventually along `l`.
Then for any finite measure measurable set `s`,
the preimages `f a ⁻¹' s` tend to the preimage `g ⁻¹' s` in measure.
More precisely, the measure of the symmetric difference of these two sets tends to zero. -/
/-
**MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_symmDiff_preimage_nhds_zero {l : Filter α} {f : α -> C(X, 
Y)} {g : C(X, Y)} {s : Set Y} (hfg : Tendsto f l (𝓝 g)) (hf : forallᶠ a in l, Me
asurePreserving (f a) μ ν) (hg : MeasurePreserving g μ ν) (hs : NullMeasurableSe
t s ν) (hνs : ν s != ∞) : Tendsto (fun a => μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))) l (𝓝 0)
参数：X, Y；X, Y；hfg : Tendsto f l (𝓝 g)；hf : forallᶠ a in l, MeasurePreserving (f a
) μ ν；hg : MeasurePreserving g μ ν；hs : NullMeasurableSet s ν；hνs : ν s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.map_of_continuous`：∀ {α :
 Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure 
α} [inst_1 : TopologicalSpace α]   [BorelSpace α] [ins…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ENNReal.tendsto_nhds_zero`：∀ {α : Type u_1} {f : Filter α} {u : α → ENNR
eal}, Filter.Tendsto u f (nhds 0) ↔ ∀ ε > 0, ∀ᶠ (x : α) in f, u x ≤ ε
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasurableSet.exists_isCompact_isClosed_sdiff_lt`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
] [BorelSpace α]   [R1Space α] [μ.Inne…
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsClosed.nullMeasurableSet`：IsClosed.nullMeasurableSet {μ} (h : IsClosed
 s) : NullMeasurableSet s μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ContinuousMap.tendsto_nhds_compactOpen`：tendsto_nhds_compactOpen {l : Fi
lter α} {f : α -> C(Y, Z)} {g : C(Y, Z)} : Tendsto f l (𝓝 g) ↔ forall K, IsCompa
ct K -> forall U, IsOpen U -…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.measure_symmDiff_le`：measure_symmDiff_le (s t u : Set α) :
 μ (s ∆ u) <= μ (s ∆ t) + μ (t ∆ u)
· 使用定理 `symmDiff_of_ge`：symmDiff_of_ge {a b : α} (h : b <= a) : a ∆ b = a \ b
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
Let `X` and `Y` be R₁ topological spaces
with Borel σ-algebras and measures `μ` and `ν`, respectively.
Suppose that `μ` is inner regular for finite measure sets with respect to compac
t sets
and `ν` is a locally finite measure.
Let `f : α → C(X, Y)` be a family of continuous maps
that converges to a continuous map `g : C(X, Y)` in the compact-open topology al
ong a filter `l`.
Suppose that `g` is a measure-preserving map
and `f a` is a measure-preserving map eventually along `l`.
Then for any finite measure measurable set `s`,
the preimages `f a ⁻¹' s` tend to the preimage `g ⁻¹' s` in measure.
More precisely, the measure of the symmetric difference of these two sets tends 
to zero.
-/
theorem tendsto_measure_symmDiff_preimage_nhds_zero
    {l : Filter α} {f : α → C(X, Y)} {g : C(X, Y)} {s : Set Y} (hfg : Tendsto f l (𝓝 g))
    (hf : ∀ᶠ a in l, MeasurePreserving (f a) μ ν) (hg : MeasurePreserving g μ ν)
    (hs : NullMeasurableSet s ν) (hνs : ν s ≠ ∞) :
    Tendsto (fun a ↦ μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))) l (𝓝 0) := by
  have : ν.InnerRegularCompactLTTop := by
    rw [← hg.map_eq]
    exact .map_of_continuous (map_continuous _)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- Without loss of generality, `s` is an open set.
  wlog hso : IsOpen s generalizing s ε
  · have H : 0 < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.coe_ne_top
    -- Indeed, we can choose an open set `U` such that `ν (U ∆ s) < ε / 3`,
    -- apply the lemma to `U`, then use the triangle inequality for `μ (_ ∆ _)`.
    rcases hs.exists_isOpen_symmDiff_lt hνs H.ne' with ⟨U, hUo, hU, hUs⟩
    have hmU : NullMeasurableSet U ν := hUo.measurableSet.nullMeasurableSet
    replace hUs := hUs.le
    filter_upwards [hf, this hmU hU.ne _ H hUo] with a hfa ha
    calc
      μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))
        ≤ μ ((f a ⁻¹' s) ∆ (f a ⁻¹' U)) + μ ((f a ⁻¹' U) ∆ (g ⁻¹' U))
          + μ ((g ⁻¹' U) ∆ (g ⁻¹' s)) := by
        refine (measure_symmDiff_le _ (g ⁻¹' U) _).trans ?_
        gcongr
        apply measure_symmDiff_le
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · rwa [← preimage_symmDiff, hfa.measure_preimage (hs.symmDiff hmU), symmDiff_comm]
        · rwa [← preimage_symmDiff, hg.measure_preimage (hmU.symmDiff hs)]
      _ = ε := by simp
  -- Take a compact closed subset `K ⊆ g ⁻¹' s` of almost full measure,
  -- `μ (g ⁻¹' s \ K) < ε / 2`.
  have hνs' : μ (g ⁻¹' s) ≠ ∞ := by rwa [hg.measure_preimage hs]
  obtain ⟨K, hKg, hKco, hKcl, hKμ⟩ :
      ∃ K, MapsTo g K s ∧ IsCompact K ∧ IsClosed K ∧ μ (g ⁻¹' s \ K) < ε / 2 :=
    (hg.measurable hso.measurableSet).exists_isCompact_isClosed_sdiff_lt hνs' <| by simp [hε.ne']
  have hKm : NullMeasurableSet K μ := hKcl.nullMeasurableSet
  -- Take `a` such that `f a` is measure preserving and maps `K` to `s`.
  -- This is possible, because `K` is a compact set and `s` is an open set.
  filter_upwards [hf, ContinuousMap.tendsto_nhds_compactOpen.mp hfg K hKco s hso hKg] with a hfa ha
  -- Then each of the sets `g ⁻¹' s ∆ K = g ⁻¹' s \ K` and `f a ⁻¹' s ∆ K = f a ⁻¹' s \ K`
  -- have measure at most `ε / 2`, thus `f a ⁻¹' s ∆ g ⁻¹' s` has measure at most `ε`.
  rw [← ENNReal.add_halves ε]
  refine (measure_symmDiff_le _ K _).trans ?_
  rw [symmDiff_of_ge ha.subset_preimage, symmDiff_of_le hKg.subset_preimage]
  gcongr
  have hK' : μ K ≠ ∞ := ne_top_of_le_ne_top hνs' <| measure_mono hKg.subset_preimage
  rw [measure_sdiff_le_iff_le_add hKm ha.subset_preimage hK', hfa.measure_preimage hs,
    ← hg.measure_preimage hs, ← measure_sdiff_le_iff_le_add hKm hKg.subset_preimage hK']
  exact hKμ.le

set_option backward.isDefEq.respectTransparency false in
/-- Let `f : Z → C(X, Y)` be a continuous (in the compact open topology) family
of continuous measure-preserving maps.
Let `t : Set Y` be a null measurable set of finite measure.
Then for any `s`, the set of parameters `z`
such that the preimage of `t` under `f_z` is a.e. equal to `s`
is a closed set.

In particular, if `X = Y` and `s = t`,
then we see that the a.e. stabilizer of a set is a closed set. -/
/-
**MeasureTheory.isClosed_setOfPred_preimage_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：isClosed_setOfPred_preimage_ae_eq {f : Z -> C(X, Y)} (hf : Continuous f) (
hfm : forall z, MeasurePreserving (f z) μ ν) (s : Set X) {t : Set Y} (htm : Null
MeasurableSet t ν) (ht : ν t != ∞) : IsClosed {z | f z ⁻¹' t =ᵐ[μ] s}
参数：X, Y；hf : Continuous f；hfm : forall z, MeasurePreserving (f z) μ ν；s : Set X；
htm : NullMeasurableSet t ν；ht : ν t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.measure_symmDiff_eq_zero_iff`：measure_symmDiff_eq_zero_iff
 {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero`：tendsto_measu
re_symmDiff_preimage_nhds_zero {l : Filter α} {f : α -> C(X, Y)} {g : C(X, Y)} {
s : Set Y} (hfg : Tendsto f l (𝓝 g)) (hf : fora…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.EventuallyEq.symmDiff`：∀ {α : Type u} {s t s' t' : Set α} {l : Fi
lter α}, s =ᶠ[l] t → s' =ᶠ[l] t' → symmDiff s s' =ᶠ[l] symmDiff t t'
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f

--- 原说明 ---
Let `f : Z → C(X, Y)` be a continuous (in the compact open topology) family
of continuous measure-preserving maps.
Let `t : Set Y` be a null measurable set of finite measure.
Then for any `s`, the set of parameters `z`
such that the preimage of `t` under `f_z` is a.e. equal to `s`
is a closed set.

In particular, if `X = Y` and `s = t`,
then we see that the a.e. stabilizer of a set is a closed set.
-/
theorem isClosed_setOfPred_preimage_ae_eq {f : Z → C(X, Y)} (hf : Continuous f)
    (hfm : ∀ z, MeasurePreserving (f z) μ ν) (s : Set X)
    {t : Set Y} (htm : NullMeasurableSet t ν) (ht : ν t ≠ ∞) :
    IsClosed {z | f z ⁻¹' t =ᵐ[μ] s} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  replace hz : ∀ᶠ ε : ℝ≥0∞ in 𝓝 0, ε < μ ((f z ⁻¹' t) ∆ s) := by
    apply gt_mem_nhds
    rwa [pos_iff_ne_zero, ne_eq, measure_symmDiff_eq_zero_iff]
  filter_upwards [(tendsto_measure_symmDiff_preimage_nhds_zero (hf.tendsto z)
    (.of_forall hfm) (hfm z) htm ht).eventually hz] with w hw
  intro (hw' : f w ⁻¹' t =ᵐ[μ] s)
  rw [measure_congr (hw'.symmDiff (ae_eq_refl _)), symmDiff_comm] at hw
  exact hw.false

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_preimage_ae_eq := isClosed_setOfPred_preimage_ae_eq

end MeasureTheory

