/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Gaps
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Fundamental theorem of calculus and integration by parts for absolutely continuous functions

This file proves that:
* `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`: If `f` is absolutely continuous on
  `uIcc a b`, then *Fundamental Theorem of Calculus* holds for `f'` on `a..b`, i.e.
  `∫ (x : ℝ) in a..b, deriv f x = f b - f a`.
* `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`:
  *Integration by Parts* holds for absolutely continuous functions, i.e. if `f` and `g` are
  absolutely continuous on `uIcc a b`, then
  `∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x`.

## Tags
absolutely continuous, fundamental theorem of calculus, integration by parts
-/

public section

variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

open Filter Fin.NatCast Function MeasureTheory Set

open scoped Topology

/-- If `f` has derivative `f'` a.e. on `[d, b]` and `η` is positive, then there is a collection of
pairwise disjoint closed subintervals of `[a, b]` of total length `b - a` where the slope of `f`
on each subinterval `[x, y]` differs from `f' x` by at most `η`. -/
/-
**exists_dist_slope_lt_pairwiseDisjoint_hasSum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_dist_slope_lt_pairwiseDisjoint_hasSum {f f' : Real -> F} {d b η : R
eal} (hdb : d <= b) (hf : forallᵐ x, x in Ioo d b -> HasDerivAt f (f' x) x) (hη 
: 0 < η) : exists u : Set (Real × Real), (forall z in u, (d < z.1 ∧ z.1 < z.2 ∧ 
z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η) ∧ u.PairwiseDisjoint (fun z => I
cc z.1 z.2) ∧ HasSum (fun (z : u) => z.val.2 - z.val.1) (b - d)
参数：hdb : d <= b；hf : forallᵐ x, x in Ioo d b -> HasDerivAt f (f' x) x；hη : 0 < η
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Vitali.exists_disjoint_covering_ae'`：exists_disjoint_covering_ae' [Pseud
oMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTop
ology α] (μ : Measure α) …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.volume_closedBall`：volume_closedBall (a r : Real) : volume (Metric.
closedBall a r) = ofReal (2 * r)
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 138 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` has derivative `f'` a.e. on `[d, b]` and `η` is positive, then there is a
 collection of
pairwise disjoint closed subintervals of `[a, b]` of total length `b - a` where 
the slope of `f`
on each subinterval `[x, y]` differs from `f' x` by at most `η`.
-/
lemma exists_dist_slope_lt_pairwiseDisjoint_hasSum {f f' : ℝ → F} {d b η : ℝ}
    (hdb : d ≤ b) (hf : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f (f' x) x) (hη : 0 < η) :
    ∃ u : Set (ℝ × ℝ),
      (∀ z ∈ u, (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η) ∧
      u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧
      HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d) := by
  -- Proof idea: Use `Vitali.exists_disjoint_covering_ae'` to get a Vitali cover of `[a, b]`
  -- consisting of closed subintervals `[x, y]` on which the slope of `f` differs from `f' x` by
  -- at most `η`.
  rcases hdb.eq_or_lt with rfl | hdb
  · exact ⟨∅, by simp⟩
  let t := {z : ℝ × ℝ | (d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) ∧ dist (slope f z.1 z.2) (f' z.1) < η}
  let s := {x ∈ Ioo d b | HasDerivAt f (f' x) x}
  obtain ⟨u, ⟨hu₁, hu₂, hu₃, hu₄⟩⟩ : ∃ u ⊆ t, u.Countable ∧
      u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2) ∧ volume (s \ ⋃ z ∈ u, Icc z.1 z.2) = 0 := by
    apply Vitali.exists_disjoint_covering_ae' volume s t 6 (Prod.snd - Prod.fst) Prod.fst
      (fun z ↦ Icc z.1 z.2)
    · grind [Metric.closedBall, Real.dist_eq, Pi.sub_apply, abs_le']
    · intro A hA
      simp only [Pi.sub_apply, Real.volume_closedBall, ENNReal.coe_ofNat, Real.volume_Icc]
      rw [show 6 = ENNReal.ofReal 6 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_le_ofReal_iff (by grind)]
      linarith
    · simp +contextual [t]
    · simp [isClosed_Icc]
    · intro x hx
      apply Eventually.frequently
      have := hasDerivAt_iff_tendsto_slope.mp hx.right
      obtain ⟨δ, hδ₁, hδ₂⟩ := (Metric.tendsto_nhdsWithin_nhds).mp
        (hasDerivAt_iff_tendsto_slope.mp hx.right) η hη
      have evn_bound {α : ℝ} (hα : 0 < α) : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ε < α := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        exact ⟨Ioo (-α) α, by grind, isOpen_Ioo, by grind⟩
      have evn_pos : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε :=
        eventually_mem_of_tendsto_nhdsWithin (fun _ a ↦ a)
      filter_upwards [evn_pos, evn_bound hη, evn_bound hδ₁,
                      evn_bound (α := (b - x) / 2) (by simp [hx.left.right])]
        with ε hε₁ hε₂ hε₃ hε₄
      refine ⟨(x, x + ε), ⟨⟨hx.1.1, by linarith, by linarith⟩, ?_⟩, by simp, rfl⟩
      exact hδ₂ (by grind) (by simp [abs_eq_self.mpr hε₁.le, hε₃])
  simp only [t, subset_def, mem_ofPred_eq] at hu₁
  refine ⟨u, ⟨hu₁, hu₃, ?_⟩⟩
  have : Countable u := by simp [hu₂]
  have : Pairwise (Disjoint on fun (z : u) ↦ Icc z.val.1 z.val.2) :=
    fun z₁ z₂ hz₁z₂ ↦ hu₃ z₁.prop z₂.prop (Subtype.coe_ne_coe.mpr hz₁z₂)
  replace hu₄ : volume (Ioo d b \ ⋃ z ∈ u, Icc z.1 z.2) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem] at hu₄ ⊢
    filter_upwards [hf, hu₄] with x hx₁ hx₂
    grind
  have vol_sum : volume (⋃ z : u, Icc z.val.1 z.val.2) = ENNReal.ofReal (b - d) := by
    convert!
      Real.volume_Ioo ▸
        measure_eq_measure_of_null_sdiff (by simp only [iUnion_subset_iff]; grind) hu₄ using 2
    simp
  rw [measure_iUnion this (by simp)] at vol_sum
  simp_rw [Real.volume_Icc] at vol_sum
  apply_fun fun x ↦ x.toReal at vol_sum
  rw [ENNReal.tsum_toReal_eq (by simp), ENNReal.toReal_ofReal (by linarith),
      ← Summable.hasSum_iff (by grind [tsum_def])] at vol_sum
  grind [ENNReal.toReal_ofReal]

/-- If `f` is absolutely continuous on `[d, b]` and there is a collection of pairwise disjoint
closed subintervals of `(d, b)` of total length `b - d` such that the sum of `dist (f x) (f y)` for
`[x, y]` in the collection is equal to `y`, then `dist (f b) (f d) ≤ y`. -/
/-
**AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum** 是 Mathlib 
中的一个引理，位于命名空间 ``。
形式化陈述：AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum {f : Rea
l -> X} {d b y : Real} (hdb : d <= b) (hf : AbsolutelyContinuousOnInterval f d b
) {u : Set (Real × Real)} (hu₁ : forall z in u, d < z.1 ∧ z.1 < z.2 ∧ z.2 < b) (
hu₂ : u.PairwiseDisjoint (fun z => Icc z.1 z.2)) (hu₃ : HasSum (fun (z : u) => z
.val.2 - z.val.1) (b - d)) (hu₄ : HasSum (fun (z : u) => dist (f z.val.1) (f z.v
al.2)) y) : dist (f d) (f b) <= y
参数：hdb : d <= b；hf : AbsolutelyContinuousOnInterval f d b；Real × Real；hu₁ : fora
ll z in u, d < z.1 ∧ z.1 < z.2 ∧ z.2 < b；hu₂ : u.PairwiseDisjoint (fun z => Icc 
z.1 z.2)；hu₃ : HasSum (fun (z : u) => z.val.2 - z.val.1) (b - d)；hu₄ : HasSum (f
un (z : u) => dist (f z.val.1) (f z.val.2)) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.subset`：∀ {α : Type u_1} {ι : Type u_4} [inst : Par
tialOrder α] [inst_1 : OrderBot α] {s t : Set ι} {f : ι → α},   t.PairwiseDisjoi
nt f → s ⊆ t → s.…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.intervalGapsWithin_le_fst`：intervalGapsWithin_le_fst {a b : α} (h
Fab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) : a <= (F.interval
GapsWithin h a b j).1
· 使用定理 `Finset.intervalGapsWithin_fst_le_snd`：intervalGapsWithin_fst_le_snd {a b
 : α} (hab : a <= b) (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <
= b) (hF : (SetLike.coe F)…
· 使用定理 `Finset.intervalGapsWithin_snd_le`：intervalGapsWithin_snd_le {a b : α} (h
Fab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) : (F.intervalGapsW
ithin h a b j).2 <= b
· 使用定理 `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`：intervalGapsWithin_pairw
iseDisjoint_Ioc {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ 
z.2 <= b) : (Set.Iio (k + 1)).Pairwi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is absolutely continuous on `[d, b]` and there is a collection of pairwis
e disjoint
closed subintervals of `(d, b)` of total length `b - d` such that the sum of `di
st (f x) (f y)` for
`[x, y]` in the collection is equal to `y`, then `dist (f b) (f d) ≤ y`.
-/
lemma AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum {f : ℝ → X} {d b y : ℝ}
    (hdb : d ≤ b) (hf : AbsolutelyContinuousOnInterval f d b) {u : Set (ℝ × ℝ)}
    (hu₁ : ∀ z ∈ u, d < z.1 ∧ z.1 < z.2 ∧ z.2 < b)
    (hu₂ : u.PairwiseDisjoint (fun z ↦ Icc z.1 z.2))
    (hu₃ : HasSum (fun (z : u) ↦ z.val.2 - z.val.1) (b - d))
    (hu₄ : HasSum (fun (z : u) ↦ dist (f z.val.1) (f z.val.2)) y) :
    dist (f d) (f b) ≤ y := by
  -- Proof idea: The complement of the collection of subintervals of `[d, b]` encoded in `u` can
  -- be approached by the complement of subcollections encoded by finite subsets `s ⊆ u`. These
  -- complements are encoded using `Finset.intervalGapsWithin`.
  -- Their total length tends to `0` as `s` tends to `u` and by absolute continuity of `f`, the sum
  -- of `dist (f x) (f y)` for `[x, y]` in the complement tends to `0` as `s` tends to `u`.
  -- Finally we use the triangle inequality of `dist` to obtain the result.
  let u_coe (s : Finset u) : Finset (ℝ × ℝ) := s.image Subtype.val
  replace hu₁ (s : Finset u) : ∀ ⦃z : ℝ × ℝ⦄, z ∈ u_coe s → d ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := by
    grind
  replace hu₂ (s : Finset u) : (SetLike.coe (u_coe s)).PairwiseDisjoint fun z ↦ Icc z.1 z.2 :=
    hu₂.subset (by grind)
  let T (s : Finset u) :=
    ((u_coe s).card + 1, fun (i : ℕ) ↦ (u_coe s).intervalGapsWithin rfl d b i)
  have hT₁ (s : Finset u) (i : ℕ) := (u_coe s).intervalGapsWithin_le_fst rfl i (hu₁ s)
  have hT₂ (s : Finset u) (i : ℕ) :=
    (u_coe s).intervalGapsWithin_fst_le_snd rfl i hdb (hu₁ s) (hu₂ s)
  have hT₃ (s : Finset u) (i : ℕ) := (u_coe s).intervalGapsWithin_snd_le rfl i (hu₁ s)
  have hT₄ (s : Finset u) := (u_coe s).intervalGapsWithin_pairwiseDisjoint_Ioc rfl (hu₁ s)
  have hT : univ.MapsTo T (disjWithin d b) := by
    intro s _
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `simp`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
    problem in the new canonicalizer; a minimization would help. The original proof was:
    `grind [disjWithin, uIcc_of_le]` -/
    simp [disjWithin]
    grind [uIcc_of_le]
  have u_coe_sum (s : Finset u) (g : ℝ → ℝ → ℝ) :
      ∑ b ∈ s, (g b.val.1 b.val.2) = ∑ z ∈ u_coe s, (g z.1 z.2) :=
    Finset.sum_nbij Subtype.val (by simp [u_coe]) (by simp)
      (by simp only [Finset.coe_image, u_coe]; tauto) (by simp)
  replace hu₃ : Tendsto T atTop (totalLengthFilter ⊓ 𝓟 (disjWithin d b)) := by
    refine tendsto_inf.mpr ⟨?_, hT.tendsto.mono_left (by simp)⟩
    simp only [totalLengthFilter, tendsto_comap_iff]
    convert! hu₃.const_sub (b - d) with s
    · simp only [comp_apply]
      rw [Finset.sum_congr rfl (g := fun i ↦ ((T s).2 i).2 - ((T s).2 i).1)
            (fun i hi ↦ by rw [dist_comm, Real.dist_eq, abs_of_nonneg (by grind)])]
      convert! (u_coe s).sum_intervalGapsWithin_eq_sub_sub_sum rfl id
      exact u_coe_sum s fun x y ↦ y - x
    · abel
  rw [HasSum] at hu₄
  simp_rw [u_coe_sum _ fun x y ↦ dist (f x) (f y)] at hu₄
  have sum_tendsto := hf.comp hu₃ |>.add hu₄
  simp only [comp_apply, zero_add] at sum_tendsto
  have dist_le_sum (s : Finset u) :
      dist (f d) (f b) ≤
      ∑ i ∈ Finset.range (T s).1, dist (f ((T s).2 i).1) (f ((T s).2 i).2) +
      (∑ b ∈ u_coe s, dist (f b.1) (f b.2)) := by
    rw [Finset.sum_eq_sum_range_intervalGapsWithin _ rfl (fun x y ↦ dist (f x) (f y)),
        Finset.sum_range_succ, add_right_comm, ← Finset.sum_add_distrib]
    grw [← Finset.sum_le_sum (fun _ _ ↦ dist_triangle _ _ _),
        ← dist_le_range_sum_dist,
        ← dist_triangle]
    simp [T]
  exact le_of_tendsto_of_tendsto' (by simp) sum_tendsto dist_le_sum

/-- If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc a b`, then `f`
is constant on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero {f : Real -> F}
 {a b : Real} (hf : AbsolutelyContinuousOnInterval f a b) (hf₀ : forallᵐ x, x in
 uIcc a b -> HasDerivAt f 0 x) : exists C, forall x in uIcc a b, f x = C
参数：hf : AbsolutelyContinuousOnInterval f a b；hf₀ : forallᵐ x, x in uIcc a b -> H
asDerivAt f 0 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 136 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is absolutely continuous on `uIcc a b` and `f' x = 0` for a.e. `x ∈ uIcc 
a b`, then `f`
is constant on `uIcc a b`.
-/
theorem AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hf₀ : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f 0 x) :
    ∃ C, ∀ x ∈ uIcc a b, f x = C := by
  -- Proof idea : Assume wlog `a < b`. We need to show that `f d = f b` for any `d ∈ [a, b]`.
  -- Fix `d`. It suffices to show that `dist (f d) (f b) ≤ r` for any `r > 0`. Fix `r`.
  -- Use `exists_dist_slope_lt_pairwiseDisjoint_hasSum` with `η = r / (b - d)` to
  -- get a cover of `[d, b]` consisting of closed subintervals with total length `b - d` such that
  -- the slope of `f` on each subinterval has absolute value `≤ η`. The sum of `dist (f x) (f y)`
  -- for `[x, y]` in the cover must therefore be `≤ (b - d) * η = r`. Use
  -- `AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum` to conclude that
  -- `dist (f d) (f b) ≤ r`.
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this (a := b) (b := a) hf.symm (uIcc_comm a b ▸ hf₀) (by linarith)
  suffices ∀ x ∈ uIcc a b, f x = f b by use f b
  rw [uIcc_of_le hab] at hf₀ ⊢
  intro d hd
  suffices ∀ r > 0, dist (f d) (f b) ≤ r by
    contrapose! this
    exact exists_between (dist_pos.mpr this)
  intro r hr
  rw [mem_Icc] at hd
  have had : a ≤ d := by linarith
  rcases hd.right.eq_or_lt with rfl | hdb
  · simp [hr.le]
  replace hf₀ : ∀ᵐ x, x ∈ Ioo d b → HasDerivAt f 0 x := by
    filter_upwards [hf₀] with x _ _ using by grind
  have hfdb' : 0 < r / (b - d) := by apply div_pos <;> linarith
  have ⟨u, hu₁, hu₂, hu₃⟩ :=
    exists_dist_slope_lt_pairwiseDisjoint_hasSum hd.right hf₀ hfdb'
  let g := fun (z : u) ↦ dist (f z.val.1) (f z.val.2)
  have g_nonneg : 0 ≤ g := by intro; simp [g]
  have g_finsum_bound (s : Finset u) : ∑ z ∈ s, g z ≤ r := by
    have (z : u) (hz : z ∈ s) : g z ≤ r / (b - d) * (z.val.2 - z.val.1) := by
      have slope_bound := hu₁ z (by simp) |>.right |>.le
      have : 0 < z.val.2 - z.val.1 := by linarith [hu₁ z (by simp)]
      grw [← slope_bound]
      simp only [dist_eq_norm, slope, vsub_eq_sub, sub_zero, g, mul_comm]
      nth_rw 1 [← Real.norm_of_nonneg this.le]
      simp only [norm_smul, Real.norm_eq_abs, norm_inv]
      field_simp
      rw [norm_sub_rev]
    grw [Finset.sum_le_sum this]
    rw [← Finset.mul_sum]
    have : ∑ z ∈ s, (z.val.2 - z.val.1) ≤ b - d :=
      hu₃.tsum_eq ▸ Summable.sum_le_tsum _ (by grind) hu₃.summable
    grw [this]
    field_simp
    grind
  have hu₄ := summable_of_sum_le g_nonneg g_finsum_bound |>.hasSum
  have g_sum_bound := Real.tsum_le_of_sum_le g_nonneg g_finsum_bound
  have := (hf.mono (by grind [uIcc_of_le])).dist_le_of_pairwiseDisjoint_hasSum hd.right
    (fun s hs ↦ hu₁ s hs |>.left) hu₂ hu₃ hu₄
  linarith

/-- *Fundamental Theorem of Calculus* for absolutely continuous functions: if `f` is absolutely
continuous on `uIcc a b`, then `∫ (x : ℝ) in a..b, deriv f x = f b - f a`. -/
/-
**AbsolutelyContinuousOnInterval.integral_deriv_eq_sub** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：AbsolutelyContinuousOnInterval.integral_deriv_eq_sub {f : Real -> Real} {a
 b : Real} (hf : AbsolutelyContinuousOnInterval f a b) : ∫ (x : Real) in a..b, d
eriv f x = f b - f a
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`：∀ {f
 : ℝ → ℝ} {a b c : ℝ},   IntervalIntegrable f MeasureTheory.volume a b →     c ∈
 Set.uIcc a b → AbsolutelyContinuousOnInterval (fun x =>…
· 使用定理 `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`：AbsolutelyConti
nuousOnInterval.intervalIntegrable_deriv {f : Real -> Real} {a b : Real} (hf : A
bsolutelyContinuousOnInterval f a b) : Interv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AbsolutelyContinuousOnInterval.sub`：sub (hf : AbsolutelyContinuousOnInte
rval f a b) (hg : AbsolutelyContinuousOnInterval g a b) : AbsolutelyContinuousOn
Interval (f - g) a b
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IntervalIntegrable.ae_hasDerivAt_integral`：IntervalIntegrable.ae_hasDeri
vAt_integral {f : Real -> E} {a b : Real} (hf : IntervalIntegrable f volume a b)
 : forallᵐ x, x in uIcc a b -> …
· 使用定理 `AbsolutelyContinuousOnInterval.ae_differentiableAt`：ae_differentiableAt 
{f : Real -> Real} {a b : Real} (hf : AbsolutelyContinuousOnInterval f a b) : fo
rallᵐ (x : Real), x in uIcc a b -> Diffe…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyConti
nuousFun.0.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub._abel_1_1`：∀ {f 
: ℝ → ℝ} (x : ℝ), 0 = deriv f x - deriv f x
· 使用定理 `HasDerivAt.sub`：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f - g) (f' - g') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`：AbsolutelyCo
ntinuousOnInterval.const_of_ae_hasDerivAt_zero {f : Real -> F} {a b : Real} (hf 
: AbsolutelyContinuousOnInterval f a b) (hf₀ : f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
*Fundamental Theorem of Calculus* for absolutely continuous functions: if `f` is
 absolutely
continuous on `uIcc a b`, then `∫ (x : ℝ) in a..b, deriv f x = f b - f a`.
-/
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ (x : ℝ) in a..b, deriv f x = f b - f a := by
  have f_deriv_integral_ac :=
    hf.intervalIntegrable_deriv.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp)
  let g (x : ℝ) := f x - ∫ (t : ℝ) in a..x, deriv f t
  have g_ac : AbsolutelyContinuousOnInterval g a b := hf.sub (f_deriv_integral_ac)
  have g_ae_deriv_zero : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [hf.ae_differentiableAt, hf.intervalIntegrable_deriv.ae_hasDerivAt_integral]
      with x hx₁ hx₂ hx₃
    convert! (hx₁ hx₃).hasDerivAt.sub (hx₂ hx₃ a (by simp))
    abel
  obtain ⟨C, hC⟩ := g_ac.const_of_ae_hasDerivAt_zero g_ae_deriv_zero
  have : f a = g a := by simp [g]
  have := hC a (by simp)
  have := hC b (by simp)
  grind

/-- The integral of the derivative of a product of two absolutely continuous functions. -/
/-
**AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub {f g : Real -> Re
al} {a b : Real} (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyCon
tinuousOnInterval g a b) : ∫ x in a..b, deriv f x * g x + f x * deriv g x = f b 
* g b - f a * g a
参数：hf : AbsolutelyContinuousOnInterval f a b；hg : AbsolutelyContinuousOnInterval
 g a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`：AbsolutelyContinuo
usOnInterval.integral_deriv_eq_sub {f : Real -> Real} {a b : Real} (hf : Absolut
elyContinuousOnInterval f a b) : ∫ (x : Re…
· 使用定理 `AbsolutelyContinuousOnInterval.fun_mul`：∀ {a b : ℝ} {f g : ℝ → ℝ},   Abs
olutelyContinuousOnInterval f a b →     AbsolutelyContinuousOnInterval g a b → A
bsolutelyContinuousOnInterva…
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AbsolutelyContinuousOnInterval.ae_differentiableAt`：ae_differentiableAt 
{f : Real -> Real} {a b : Real} (hf : AbsolutelyContinuousOnInterval f a b) : fo
rallᵐ (x : Real), x in uIcc a b -> Diffe…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'

--- 原说明 ---
The integral of the derivative of a product of two absolutely continuous functio
ns.
-/
theorem AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, deriv f x * g x + f x * deriv g x = f b * g b - f a * g a := by
  rw [← (hf.fun_mul hg).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hf.ae_differentiableAt, hg.ae_differentiableAt] with x hx₁ hx₂ hx₃
  have hx₄ : x ∈ uIcc a b := uIoc_subset_uIcc hx₃
  have hx₅ := (hx₁ hx₄).hasDerivAt.mul (hx₂ hx₄).hasDerivAt
  exact hx₅.deriv.symm

/-- *Integration by parts* for absolutely continuous functions. -/
/-
**AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul {f g : Real
 -> Real} {a b : Real} (hf : AbsolutelyContinuousOnInterval f a b) (hg : Absolut
elyContinuousOnInterval g a b) : ∫ x in a..b, f x * deriv g x = f b * g b - f a 
* g a - ∫ x in a..b, deriv f x * g x
参数：hf : AbsolutelyContinuousOnInterval f a b；hg : AbsolutelyContinuousOnInterval
 g a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub`：AbsolutelyCont
inuousOnInterval.integral_deriv_mul_eq_sub {f g : Real -> Real} {a b : Real} (hf
 : AbsolutelyContinuousOnInterval f a b) (hg :…
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `IntervalIntegrable.add`：add [ContinuousAdd ε] (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x + g
 x) μ a b
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
· 使用定理 `IntervalIntegrable.mul_continuousOn`：mul_continuousOn {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => f x * g x…
· 使用定理 `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`：AbsolutelyConti
nuousOnInterval.intervalIntegrable_deriv {f : Real -> Real} {a b : Real} (hf : A
bsolutelyContinuousOnInterval f a b) : Interv…
· 使用定理 `AbsolutelyContinuousOnInterval.continuousOn`：continuousOn (hf : Absolute
lyContinuousOnInterval f a b) : ContinuousOn f (uIcc a b)
· 使用定理 `IntervalIntegrable.continuousOn_mul`：continuousOn_mul {f g : Real -> A} 
(hf : IntervalIntegrable f μ a b) (hg : ContinuousOn g [[a, b]]) : IntervalInteg
rable (fun x => g x * f x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
*Integration by parts* for absolutely continuous functions.
-/
theorem AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, f x * deriv g x = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  rw [← AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hf hg,
      ← intervalIntegral.integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hf.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn).add
      (hg.intervalIntegrable_deriv.continuousOn_mul hf.continuousOn)
  · exact hf.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn
