/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.Residual
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Analysis.PSeries

/-!
# Volume of the set of Liouville numbers

In this file we prove that the set of Liouville numbers with exponent (irrationality measure)
strictly greater than two is a set of Lebesgue measure zero, see
`volume_iUnion_setOfPred_liouvilleWith`.

Since this set is a residual set, we show that the filters `residual` and `ae volume` are disjoint.
These filters correspond to two common notions of genericity on `ℝ`: residual sets and sets of full
measure. The fact that the filters are disjoint means that two mutually exclusive properties can be
“generic” at the same time (in the sense of different “genericity” filters).

## Tags

Liouville number, Lebesgue measure, residual, generic property
-/

public section

open scoped Filter ENNReal Topology NNReal

open Filter Set Metric MeasureTheory Real

/-
**setOfPred_liouvilleWith_subset_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_liouvilleWith_subset_aux : { x : Real | exists p > 2, LiouvilleW
ith p x } subseteq ⋃ m : Int, (· + (m : Real)) ⁻¹' ⋃ n > (0 : Nat), { x : Real |
 existsᶠ b : Nat in atTop, exists a in Finset.Icc (0 : Int) b, |x - (a : Int) / 
b| < 1 / (b : Real) ^ (2 + 1 / n : Real) }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `exists_nat_one_div_lt`：exists_nat_one_div_lt (hε : 0 < ε) : exists n : N
at, 1 / (n + 1 : K) < ε
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LiouvilleWith.frequently_lt_rpow_neg`：frequently_lt_rpow_neg (h : Liouvi
lleWith p x) (hlt : q < p) : existsᶠ n : Nat in atTop, exists m : Int, x != m / 
n ∧ |x - m / n| < n ^ (-q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_sub_iff_add_lt'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, b < c - a ↔ a + b < c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
（共 81 条，此处仅展示前 30 条）
-/
theorem setOfPred_liouvilleWith_subset_aux :
    { x : ℝ | ∃ p > 2, LiouvilleWith p x } ⊆
      ⋃ m : ℤ, (· + (m : ℝ)) ⁻¹' ⋃ n > (0 : ℕ),
        { x : ℝ | ∃ᶠ b : ℕ in atTop, ∃ a ∈ Finset.Icc (0 : ℤ) b,
          |x - (a : ℤ) / b| < 1 / (b : ℝ) ^ (2 + 1 / n : ℝ) } := by
  rintro x ⟨p, hp, hxp⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩
  rw [lt_sub_iff_add_lt'] at hn
  suffices ∀ y : ℝ, LiouvilleWith p y → y ∈ Ico (0 : ℝ) 1 → ∃ᶠ b : ℕ in atTop,
      ∃ a ∈ Finset.Icc (0 : ℤ) b, |y - a / b| < 1 / (b : ℝ) ^ (2 + 1 / (n + 1 : ℕ) : ℝ) by
    simp only [mem_iUnion, mem_preimage]
    have hx : x + ↑(-⌊x⌋) ∈ Ico (0 : ℝ) 1 := by
      simp only [Int.floor_le, Int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self_iff,
        mem_Ico, Int.cast_neg, le_add_neg_iff_add_le]
    exact ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩
  clear hxp x; intro x hxp hx01
  refine ((hxp.frequently_lt_rpow_neg hn).and_eventually (eventually_ge_atTop 1)).mono ?_
  rintro b ⟨⟨a, -, hlt⟩, hb⟩
  rw [rpow_neg b.cast_nonneg, ← one_div, ← Nat.cast_succ] at hlt
  refine ⟨a, ?_, hlt⟩
  replace hb : (1 : ℝ) ≤ b := Nat.one_le_cast.2 hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans_le hb
  replace hlt : |x - a / b| < 1 / b := by
    refine hlt.trans_le (one_div_le_one_div_of_le hb0 ?_)
    calc
      (b : ℝ) = (b : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
      _ ≤ (b : ℝ) ^ (2 + 1 / (n + 1 : ℕ) : ℝ) :=
        rpow_le_rpow_of_exponent_le hb (one_le_two.trans ?_)
    simpa using n.cast_add_one_pos.le
  rw [sub_div' hb0.ne', abs_div, abs_of_pos hb0, div_lt_div_iff_of_pos_right hb0, abs_sub_lt_iff,
    sub_lt_iff_lt_add, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add'] at hlt
  rw [Finset.mem_Icc, ← Int.lt_add_one_iff, ← Int.lt_add_one_iff, ← neg_lt_iff_pos_add, add_comm, ←
    @Int.cast_lt ℝ, ← @Int.cast_lt ℝ]
  push_cast
  refine ⟨lt_of_le_of_lt ?_ hlt.1, hlt.2.trans_le ?_⟩
  · simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
  · rw [add_le_add_iff_left]
    exact mul_le_of_le_one_left hb0.le hx01.2.le

@[deprecated (since := "2026-07-09")]
alias setOf_liouvilleWith_subset_aux := setOfPred_liouvilleWith_subset_aux

/-- The set of numbers satisfying the Liouville condition with some exponent `p > 2` has Lebesgue
measure zero. -/
@[simp]
/-
**volume_iUnion_setOfPred_liouvilleWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_iUnion_setOfPred_liouvilleWith : volume (⋃ (p : Real) (_hp : 2 < p)
, { x : Real | LiouvilleWith p x }) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `setOfPred_liouvilleWith_subset_aux`：setOfPred_liouvilleWith_subset_aux :
 { x : Real | exists p > 2, LiouvilleWith p x } subseteq ⋃ m : Int, (· + (m : Re
al)) ⁻¹' ⋃ n > (0 : Nat)…
· 使用定理 `MeasureTheory.measure_iUnion_null_iff`：measure_iUnion_null_iff {ι : Sort
*} [Countable ι] {s : ι -> Set α} : μ (⋃ i, s i) = 0 ↔ forall i, μ (s i) = 0
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `MeasureTheory.measure_preimage_add_right`：∀ {G : Type u_1} [inst : Measu
rableSpace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure
 G)   [μ.IsAddRightInvariant] …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_biUnion_null_iff`：measure_biUnion_null_iff {I : Se
t ι} (hI : I.Countable) {s : ι -> Set α} : μ (⋃ i in I, s i) = 0 ↔ forall i in I
, μ (s i) = 0
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 117 条，此处仅展示前 30 条）

--- 原说明 ---
The set of numbers satisfying the Liouville condition with some exponent `p > 2`
 has Lebesgue
measure zero.
-/
theorem volume_iUnion_setOfPred_liouvilleWith :
    volume (⋃ (p : ℝ) (_hp : 2 < p), { x : ℝ | LiouvilleWith p x }) = 0 := by
  simp only [← ofPred_exists, exists_prop]
  refine measure_mono_null setOfPred_liouvilleWith_subset_aux ?_
  rw [measure_iUnion_null_iff]; intro m; rw [measure_preimage_add_right]; clear m
  refine (measure_biUnion_null_iff <| to_countable _).2 fun n (hn : 1 ≤ n) => ?_
  generalize hr : (2 + 1 / n : ℝ) = r
  replace hr : 2 < r := by simp [← hr, zero_lt_one.trans_le hn]
  clear hn n
  refine measure_setOfPred_frequently_eq_zero ?_
  simp only [ofPred_exists, ← exists_prop, ← Real.dist_eq, ← mem_ball, ofPred_mem_eq]
  set B : ℤ → ℕ → Set ℝ := fun a b => ball (a / b) (1 / (b : ℝ) ^ r)
  have hB : ∀ a b, volume (B a b) = ↑((2 : ℝ≥0) / (b : ℝ≥0) ^ r) := fun a b ↦ by
    rw [Real.volume_ball, mul_one_div, ← NNReal.coe_two, ← NNReal.coe_natCast, ← NNReal.coe_rpow,
      ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal]
  have : ∀ b : ℕ, volume (⋃ a ∈ Finset.Icc (0 : ℤ) b, B a b) ≤
      ↑(2 * ((b : ℝ≥0) ^ (1 - r) + (b : ℝ≥0) ^ (-r))) := fun b ↦
    calc
      volume (⋃ a ∈ Finset.Icc (0 : ℤ) b, B a b) ≤ ∑ a ∈ Finset.Icc (0 : ℤ) b, volume (B a b) :=
        measure_biUnion_finset_le _ _
      _ = ↑((b + 1) * (2 / (b : ℝ≥0) ^ r)) := by
        simp only [hB, Int.card_Icc, Finset.sum_const, nsmul_eq_mul, sub_zero,
          Int.toNat_natCast, ← Nat.cast_succ, ENNReal.coe_mul, ENNReal.coe_natCast]
      _ = _ := by
        have : 1 - r ≠ 0 := by linarith
        rw [ENNReal.coe_inj]
        simp [add_mul, div_eq_mul_inv, NNReal.rpow_neg, NNReal.rpow_sub' this, mul_add,
          mul_left_comm]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2 ?_) (ENNReal.tsum_le_tsum this)
  refine (Summable.add ?_ ?_).mul_left _ <;> simp only [NNReal.summable_rpow] <;> linarith

@[deprecated (since := "2026-07-09")]
alias volume_iUnion_setOf_liouvilleWith := volume_iUnion_setOfPred_liouvilleWith
/-
**ae_not_liouvilleWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_not_liouvilleWith : forallᵐ x, forall p > (2 : Real), ¬LiouvilleWith p 
x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `volume_iUnion_setOfPred_liouvilleWith`：volume_iUnion_setOfPred_liouville
With : volume (⋃ (p : Real) (_hp : 2 < p), { x : Real | LiouvilleWith p x }) = 0
-/
theorem ae_not_liouvilleWith : ∀ᵐ x, ∀ p > (2 : ℝ), ¬LiouvilleWith p x := by
  simpa only [ae_iff, not_forall, Classical.not_not, ofPred_exists] using
    volume_iUnion_setOfPred_liouvilleWith
/-
**ae_not_liouville** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_not_liouville : forallᵐ x, ¬Liouville x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ae_not_liouvilleWith`：ae_not_liouvilleWith : forallᵐ x, forall p > (2 : 
Real), ¬LiouvilleWith p x
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Liouville.liouvilleWith`：∀ {x : ℝ}, Liouville x → ∀ (p : ℝ), LiouvilleWi
th p x
-/
theorem ae_not_liouville : ∀ᵐ x, ¬Liouville x :=
  ae_not_liouvilleWith.mono fun _ h₁ h₂ => h₁ 3 (by norm_num) (h₂.liouvilleWith 3)

/-- The set of Liouville numbers has Lebesgue measure zero. -/
@[simp]
/-
**volume_setOfPred_liouville** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_setOfPred_liouville : volume { x : Real | Liouville x } = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ae_not_liouville`：ae_not_liouville : forallᵐ x, ¬Liouville x

--- 原说明 ---
The set of Liouville numbers has Lebesgue measure zero.
-/
theorem volume_setOfPred_liouville : volume { x : ℝ | Liouville x } = 0 := by
  simpa only [ae_iff, Classical.not_not] using ae_not_liouville

@[deprecated (since := "2026-07-09")]
alias volume_setOf_liouville := volume_setOfPred_liouville

/-- The filters `residual ℝ` and `ae volume` are disjoint. This means that there exists a residual
set of Lebesgue measure zero (e.g., the set of Liouville numbers). -/
/-
**Real.disjoint_residual_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.disjoint_residual_ae : Disjoint (residual Real) (ae volume)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `eventually_residual_liouville`：eventually_residual_liouville : forallᶠ x
 in residual Real, Liouville x
· 使用定理 `ae_not_liouville`：ae_not_liouville : forallᵐ x, ¬Liouville x

--- 原说明 ---
The filters `residual ℝ` and `ae volume` are disjoint. This means that there exi
sts a residual
set of Lebesgue measure zero (e.g., the set of Liouville numbers).
-/
theorem Real.disjoint_residual_ae : Disjoint (residual ℝ) (ae volume) :=
  disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville
