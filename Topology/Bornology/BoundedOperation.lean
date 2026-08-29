/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations.

In particular, when combined with type classes which guarantee continuity of the same operations,
we can equip bounded continuous functions with the corresponding operations.

## Main definitions

* `BoundedAdd R`: a class guaranteeing boundedness of addition.
* `BoundedSub R`: a class guaranteeing boundedness of subtraction.
* `BoundedMul R`: a class guaranteeing boundedness of multiplication.

-/

public section

open scoped NNReal

section bounded_sub
/-!
### Bounded subtraction
-/

open scoped Pointwise

/--
Definition of `BoundedSub` / `BoundedSub` 的定义

English:
class BoundedSub
  parameters: (R : Type*) [Bornology R] [Sub R]
  axioms and operations (1):
    - isBounded_sub : forall {s t : Set R}, Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s - t)

中文:
类 BoundedSub
  参数: (R : 类型) [Bornology R] [Sub R]
  公理与运算 (1 个):
    - isBounded_sub : 对任意 {s t : Set R}, Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s - t)
-/
class BoundedSub (R : Type*) [Bornology R] [Sub R] : Prop where
  isBounded_sub : forall {s t : Set R},
    Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s - t)

variable {R : Type*}

/--
lemma `isBounded_sub` / 引理 `isBounded_sub`

English:
lemma isBounded_sub
  statement: [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
  proof: BoundedSub.isBounded_sub hs ht

中文:
引理 isBounded_sub
  结论: [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
  证明: BoundedSub.isBounded_sub hs ht

Depends on / 依赖: BoundedSub, BoundedSub.isBounded_sub, isBounded_sub
-/
lemma isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s - t) := BoundedSub.isBounded_sub hs ht

/--
lemma `sub_bounded_of_bounded_of_bounded` / 引理 `sub_bounded_of_bounded_of_bounded`

English:
lemma sub_bounded_of_bounded_of_bounded
  statement: {X : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
  proof: by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    isBounded_sub (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_sel

中文:
引理 sub_bounded_of_bounded_of_bounded
  结论: {X : 类型} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
  证明: by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    isBounded_sub (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_sel

Depends on / 依赖: Metric, Metric.isBounded_iff.mp, Metric.isBounded_range_iff.mpr, Set.mem_range_self, Set.sub_mem_sub, f_bdd, g_bdd, isBounded_iff, isBounded_range_iff, isBounded_sub, mem_range_self, sub_mem_sub
-/
lemma sub_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
    {f g : X -> R} (f_bdd : exists C, forall x y, dist (f x) (f y) <= C)
    (g_bdd : exists C, forall x y, dist (g x) (g y) <= C) :
    exists C, forall x y, dist ((f - g) x) ((f - g) y) <= C := by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    isBounded_sub (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

/--
lemma `boundedSub_of_lipschitzWith_sub` / 引理 `boundedSub_of_lipschitzWith_sub`

English:
lemma boundedSub_of_lipschitzWith_sub
  statement: [PseudoMetricSpace R] [Sub R] {K : NNReal}
  proof: by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    convert! lip.isBounded_image bdd
    simp

中文:
引理 boundedSub_of_lipschitzWith_sub
  结论: [PseudoMetricSpace R] [Sub R] {K : NN实数}
  证明: by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    convert! lip.isBounded_image bdd
    simp

Depends on / 依赖: Bornology, Bornology.IsBounded, Bornology.IsBounded.prod, IsBounded, convert, isBounded_image, lip.isBounded_image, s_bdd, t_bdd
-/
lemma boundedSub_of_lipschitzWith_sub [PseudoMetricSpace R] [Sub R] {K : NNReal}
    (lip : LipschitzWith K (fun (p : R × R) => p.1 - p.2)) :
    BoundedSub R where
  isBounded_sub {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    convert! lip.isBounded_image bdd
    simp

end bounded_sub

section bounded_mul
/-!
### Bounded multiplication and addition
-/

open scoped Pointwise
open Set

/--
Definition of `BoundedAdd` / `BoundedAdd` 的定义

English:
class BoundedAdd
  parameters: (R : Type*) [Bornology R] [Add R]
  axioms and operations (1):
    - isBounded_add : forall {s t : Set R}, Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s + t)

中文:
类 BoundedAdd
  参数: (R : 类型) [Bornology R] [Add R]
  公理与运算 (1 个):
    - isBounded_add : 对任意 {s t : Set R}, Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s + t)
-/
class BoundedAdd (R : Type*) [Bornology R] [Add R] : Prop where
  isBounded_add : forall {s t : Set R},
    Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s + t)

/-- A typeclass saying that `(p : R × R) ↦ p.1 * p.2` maps any product of bounded sets to a bounded
set. This property automatically holds for non-unital seminormed rings, but it also holds, e.g.,
for `ℝ≥0`. -/
@[to_additive]
/--
Definition of `BoundedMul` / `BoundedMul` 的定义

English:
class BoundedMul
  parameters: (R : Type*) [Bornology R] [Mul R]
  axioms and operations (1):
    - isBounded_mul : forall {s t : Set R}, Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s * t)

中文:
类 BoundedMul
  参数: (R : 类型) [Bornology R] [Mul R]
  公理与运算 (1 个):
    - isBounded_mul : 对任意 {s t : Set R}, Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s * t)
-/
class BoundedMul (R : Type*) [Bornology R] [Mul R] : Prop where
  isBounded_mul : forall {s t : Set R},
    Bornology.IsBounded s -> Bornology.IsBounded t -> Bornology.IsBounded (s * t)

variable {R : Type*}

@[to_additive]
/--
lemma `isBounded_mul` / 引理 `isBounded_mul`

English:
lemma isBounded_mul
  statement: [Bornology R] [Mul R] [BoundedMul R] {s t : Set R}
  proof: BoundedMul.isBounded_mul hs ht

@[to_additive]

中文:
引理 isBounded_mul
  结论: [Bornology R] [Mul R] [BoundedMul R] {s t : Set R}
  证明: BoundedMul.isBounded_mul hs ht

@[to_additive]

Depends on / 依赖: BoundedMul, BoundedMul.isBounded_mul, isBounded_mul
-/
lemma isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s * t) := BoundedMul.isBounded_mul hs ht

@[to_additive]
/--
lemma `isBounded_pow` / 引理 `isBounded_pow`

English:
lemma isBounded_pow
  statement: {R : Type*} [Bornology R] [Monoid R] [BoundedMul R] {s : Set R}
  proof: by
  induction n with
  | zero =>
    by_cases s_empty : s = ∅
    · simp [s_empty]
    simp_rw [← nonempty_iff_ne_empty] at s_empty
    simp [s_empty]
  | succ n hn =>
    have obs : ((fun x => x ^ (n + 1)) '' s) subseteq ((fun x => x ^ n) '' s) * s := by
      intro x hx
      simp only [mem_image

中文:
引理 isBounded_pow
  结论: {R : 类型} [Bornology R] [Monoid R] [BoundedMul R] {s : Set R}
  证明: by
  induction n with
  | zero =>
    by_cases s_empty : s = ∅
    · simp [s_empty]
    simp_rw [← nonempty_iff_ne_empty] at s_empty
    simp [s_empty]
  | succ n hn =>
    have obs : ((fun x => x ^ (n + 1)) '' s) subseteq ((fun x => x ^ n) '' s) * s := by
      intro x hx
      simp only [mem_image

Depends on / 依赖: Set.mul_mem_mul, isBounded_mul, mem_image, mul_mem_mul, nonempty_iff_ne_empty, pow_succ, s_bdd, s_empty, simp_rw, subset, subseteq, y_in_s, ypow_eq_x
-/
lemma isBounded_pow {R : Type*} [Bornology R] [Monoid R] [BoundedMul R] {s : Set R}
    (s_bdd : Bornology.IsBounded s) (n : Nat) :
    Bornology.IsBounded ((fun x => x ^ n) '' s) := by
  induction n with
  | zero =>
    by_cases s_empty : s = ∅
    · simp [s_empty]
    simp_rw [← nonempty_iff_ne_empty] at s_empty
    simp [s_empty]
  | succ n hn =>
    have obs : ((fun x => x ^ (n + 1)) '' s) subseteq ((fun x => x ^ n) '' s) * s := by
      intro x hx
      simp only [mem_image] at hx
      obtain ⟨y, y_in_s, ypow_eq_x⟩ := hx
      rw [← ypow_eq_x]; rw [pow_succ y n]
      apply Set.mul_mem_mul _ y_in_s
      use y
    exact (isBounded_mul hn s_bdd).subset obs

@[to_additive]
/--
lemma `mul_bounded_of_bounded_of_bounded` / 引理 `mul_bounded_of_bounded_of_bounded`

English:
lemma mul_bounded_of_bounded_of_bounded
  statement: {X : Type*} [PseudoMetricSpace R] [Mul R] [BoundedMul R]
  proof: by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    isBounded_mul (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.mul_mem_mul (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.mul_mem_mul (Set.mem_range_sel

中文:
引理 mul_bounded_of_bounded_of_bounded
  结论: {X : 类型} [PseudoMetricSpace R] [Mul R] [BoundedMul R]
  证明: by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    isBounded_mul (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.mul_mem_mul (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.mul_mem_mul (Set.mem_range_sel

Depends on / 依赖: Metric, Metric.isBounded_iff.mp, Metric.isBounded_range_iff.mpr, Set.mem_range_self, Set.mul_mem_mul, f_bdd, g_bdd, isBounded_iff, isBounded_mul, isBounded_range_iff, mem_range_self, mul_mem_mul
-/
lemma mul_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Mul R] [BoundedMul R]
    {f g : X -> R} (f_bdd : exists C, forall x y, dist (f x) (f y) <= C)
    (g_bdd : exists C, forall x y, dist (g x) (g y) <= C) :
    exists C, forall x y, dist ((f * g) x) ((f * g) y) <= C := by
obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
    isBounded_mul (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.mul_mem_mul (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.mul_mem_mul (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoMetricSpace
  signature: R] [Monoid R] [LipschitzMul R] : BoundedMul R where
  body: by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    obtain ⟨C, mul_lip⟩ := ‹LipschitzMul R›.lipschitz_mul
    convert! mul_lip.isBounded_image bdd
    ext p
    simp only [Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro ⟨a, a_in_s, b, b_in

中文:
实例 [PseudoMetricSpace
  签名: R] [Monoid R] [LipschitzMul R] : BoundedMul R where
  定义体: by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    obtain ⟨C, mul_lip⟩ := ‹LipschitzMul R›.lipschitz_mul
    convert! mul_lip.isBounded_image bdd
    ext p
    simp only [Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro ⟨a, a_in_s, b, b_in

Depends on / 依赖: Bornology, Bornology.IsBounded, Bornology.IsBounded.prod, IsBounded, LipschitzMul, Prod.exists, Set.mem_image, Set.mem_prod, Set.mul_mem_mul, a_in_s, b_in_t, convert, eq_p, isBounded_image, lipschitz_mul, mem_image, mem_prod, mul_lip, mul_lip.isBounded_image, mul_mem_mul
-/
instance [PseudoMetricSpace R] [Monoid R] [LipschitzMul R] : BoundedMul R where
  isBounded_mul {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    obtain ⟨C, mul_lip⟩ := ‹LipschitzMul R›.lipschitz_mul
    convert! mul_lip.isBounded_image bdd
    ext p
    simp only [Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro ⟨a, a_in_s, b, b_in_t, eq_p⟩
      exact ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
    · intro ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
      simpa [← eq_p] using Set.mul_mem_mul a_in_s b_in_t

end bounded_mul

section SeminormedAddCommGroup
/-!
### Bounded operations in seminormed additive commutative groups
-/

variable {R : Type*} [SeminormedAddCommGroup R]

/--
lemma `SeminormedAddCommGroup.lipschitzWith_sub` / 引理 `SeminormedAddCommGroup.lipschitzWith_sub`

English:
lemma SeminormedAddCommGroup.lipschitzWith_sub
  proof: by
  convert! LipschitzWith.prod_fst.sub LipschitzWith.prod_snd
  norm_num

中文:
引理 SeminormedAddCommGroup.lipschitzWith_sub
  证明: by
  convert! LipschitzWith.prod_fst.sub LipschitzWith.prod_snd
  norm_num

Depends on / 依赖: LipschitzWith, LipschitzWith.prod_fst.sub, LipschitzWith.prod_snd, convert, prod_fst, prod_snd
-/
lemma SeminormedAddCommGroup.lipschitzWith_sub :
    LipschitzWith 2 (fun (p : R × R) => p.1 - p.2) := by
  convert! LipschitzWith.prod_fst.sub LipschitzWith.prod_snd
  norm_num

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedSub R
  body: boundedSub_of_lipschitzWith_sub SeminormedAddCommGroup.lipschitzWith_sub

中文:
实例 :
  签名: BoundedSub R
  定义体: boundedSub_of_lipschitzWith_sub SeminormedAddCommGroup.lipschitzWith_sub

Depends on / 依赖: SeminormedAddCommGroup, SeminormedAddCommGroup.lipschitzWith_sub, boundedSub_of_lipschitzWith_sub, lipschitzWith_sub
-/
instance : BoundedSub R := boundedSub_of_lipschitzWith_sub SeminormedAddCommGroup.lipschitzWith_sub

open Filter Pointwise Bornology

/-
TODO:
* Generalize the following to bornologies and `BoundedFoo` classes.
* Add `BoundedNeg`, `BoundedInv` and `BoundedDiv` in the process.
-/

@[simp]
/--
lemma `tendsto_add_const_cobounded` / 引理 `tendsto_add_const_cobounded`

English:
lemma tendsto_add_const_cobounded
  given: (x : R)
  proof: by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_sub hs (t := { x }) isBounded_singleton using 1
  ext y
  simp [sub_eq_iff_eq_add]

@[simp]

中文:
引理 tendsto_add_const_cobounded
  条件: (x : R)
  证明: by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_sub hs (t := { x }) isBounded_singleton using 1
  ext y
  simp [sub_eq_iff_eq_add]

@[simp]

Depends on / 依赖: Set.preimage_compl, convert, isBounded_compl_iff, isBounded_singleton, isBounded_sub, isCobounded_def, mem_map, preimage_compl, sub_eq_iff_eq_add
-/
lemma tendsto_add_const_cobounded (x : R) :
    Tendsto (· + x) (cobounded R) (cobounded R) := by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_sub hs (t := { x }) isBounded_singleton using 1
  ext y
  simp [sub_eq_iff_eq_add]

@[simp]
/--
lemma `tendsto_const_add_cobounded` / 引理 `tendsto_const_add_cobounded`

English:
lemma tendsto_const_add_cobounded
  given: (x : R)
  proof: by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_add isBounded_singleton (s := {-x}) hs using 1
  ext y
  simp

@[simp]

中文:
引理 tendsto_const_add_cobounded
  条件: (x : R)
  证明: by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_add isBounded_singleton (s := {-x}) hs using 1
  ext y
  simp

@[simp]

Depends on / 依赖: Set.preimage_compl, convert, isBounded_add, isBounded_compl_iff, isBounded_singleton, isCobounded_def, mem_map, preimage_compl
-/
lemma tendsto_const_add_cobounded (x : R) :
    Tendsto (x + ·) (cobounded R) (cobounded R) := by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_add isBounded_singleton (s := {-x}) hs using 1
  ext y
  simp

@[simp]
/--
theorem `tendsto_sub_const_cobounded` / 定理 `tendsto_sub_const_cobounded`

English:
theorem tendsto_sub_const_cobounded
  given: (x : R)
  proof: by
  simpa only [sub_eq_add_neg] using tendsto_add_const_cobounded (-x)

@[simp]

中文:
定理 tendsto_sub_const_cobounded
  条件: (x : R)
  证明: by
  simpa only [sub_eq_add_neg] using tendsto_add_const_cobounded (-x)

@[simp]

Depends on / 依赖: sub_eq_add_neg, tendsto_add_const_cobounded
-/
theorem tendsto_sub_const_cobounded (x : R) :
    Tendsto (· - x) (cobounded R) (cobounded R) := by
  simpa only [sub_eq_add_neg] using tendsto_add_const_cobounded (-x)

@[simp]
/--
theorem `tendsto_const_sub_cobounded` / 定理 `tendsto_const_sub_cobounded`

English:
theorem tendsto_const_sub_cobounded
  given: (x : R)
  proof: by
  simpa only [sub_eq_add_neg] using! (tendsto_const_add_cobounded x).comp tendsto_neg_cobounded

中文:
定理 tendsto_const_sub_cobounded
  条件: (x : R)
  证明: by
  simpa only [sub_eq_add_neg] using! (tendsto_const_add_cobounded x).comp tendsto_neg_cobounded

Depends on / 依赖: sub_eq_add_neg, tendsto_const_add_cobounded, tendsto_neg_cobounded
-/
theorem tendsto_const_sub_cobounded (x : R) :
    Tendsto (x - ·) (cobounded R) (cobounded R) := by
  simpa only [sub_eq_add_neg] using! (tendsto_const_add_cobounded x).comp tendsto_neg_cobounded

end SeminormedAddCommGroup

section NonUnitalSeminormedRing
/-!
### Bounded operations in non-unital seminormed rings
-/

variable {R : Type*} [NonUnitalSeminormedRing R]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedMul R
  body: by
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x

中文:
实例 :
  签名: BoundedMul R
  定义体: by
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x

Depends on / 依赖: Metric, Metric.isBounded_iff, Metric.isBounded_iff_subset_closedBall, Metric.nonempty_closedBall.mp, Set.mem_mul.mp, dist_eq_norm, isBounded_iff, isBounded_iff_subset_closedBall, mem_mul, nonempty_closedBall, w_eq, z_eq
-/
instance : BoundedMul R where
  isBounded_mul {s t} hs ht := by
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := Set.mem_mul.mp hw
    rw [← w_eq]; rw [← z_eq]; rw [dist_eq_norm]
    have hAf' : 0 <= Af := Metric.nonempty_closedBall.mp ⟨_, hAf hx₁⟩
    have aux : forall {x y}, x in s -> y in t -> ‖x * y‖ <= Af * Ag := by
      intro x y x_in_s y_in_t
      apply (norm_mul_le _ _).trans (mul_le_mul _ _ (norm_nonneg _) hAf')
      · exact mem_closedBall_zero_iff.mp (hAf x_in_s)
      · exact mem_closedBall_zero_iff.mp (hAg y_in_t)
    calc ‖x₁ * y₁ - x₂ * y₂‖
     _ <= ‖x₁ * y₁‖ + ‖x₂ * y₂‖ := norm_sub_le _ _
     _ <= Af * Ag + Af * Ag := add_le_add (aux hx₁ hy₁) (aux hx₂ hy₂)
     _ = 2 * Af * Ag := by simp [← two_mul, mul_assoc]

end NonUnitalSeminormedRing

section NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedSub Real>=0
  body: boundedSub_of_lipschitzWith_sub NNReal.lipschitzWith_sub

中文:
实例 :
  签名: BoundedSub 实数>=0
  定义体: boundedSub_of_lipschitzWith_sub NNReal.lipschitzWith_sub

Depends on / 依赖: NNReal, NNReal.lipschitzWith_sub, boundedSub_of_lipschitzWith_sub, lipschitzWith_sub
-/
instance : BoundedSub Real>=0 := boundedSub_of_lipschitzWith_sub NNReal.lipschitzWith_sub

open Metric in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedMul Real>=0
  body: by
    obtain ⟨Af, hAf⟩ := (isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (isBounded_iff_subset_closedBall 0).mp ht
    have key : IsCompact (closedBall (0 : Real>=0) Af ×ˢ closedBall (0 : Real>=0) Ag) :=
      IsCompact.prod (isCompact_closedBall _ _) (isCompact_closedBall _ _)
 

中文:
实例 :
  签名: BoundedMul 实数>=0
  定义体: by
    obtain ⟨Af, hAf⟩ := (isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (isBounded_iff_subset_closedBall 0).mp ht
    have key : IsCompact (closedBall (0 : Real>=0) Af ×ˢ closedBall (0 : Real>=0) Ag) :=
      IsCompact.prod (isCompact_closedBall _ _) (isCompact_closedBall _ _)
 

Depends on / 依赖: Bornology, Bornology.IsBounded.subset, IsBounded, IsCompact, IsCompact.prod, Set.mem_prod, closedBall, continuous_mul, isBounded, isBounded_iff_subset_closedBall, isCompact_closedBall, key.image, mem_prod, subset, x_in_s, xy_eq, y_in_t
-/
instance : BoundedMul Real>=0 where
  isBounded_mul {s t} hs ht := by
    obtain ⟨Af, hAf⟩ := (isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (isBounded_iff_subset_closedBall 0).mp ht
    have key : IsCompact (closedBall (0 : Real>=0) Af ×ˢ closedBall (0 : Real>=0) Ag) :=
      IsCompact.prod (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    apply Bornology.IsBounded.subset (key.image continuous_mul).isBounded
    intro _ ⟨x, x_in_s, y, y_in_t, xy_eq⟩
    exact ⟨⟨x, y⟩, by simpa only [Set.mem_prod] using ⟨⟨hAf x_in_s, hAg y_in_t⟩, xy_eq⟩⟩

end NNReal
