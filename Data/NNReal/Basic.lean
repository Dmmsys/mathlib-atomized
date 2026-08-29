/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Floor
public import Mathlib.Data.Real.Pointwise
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Order.Lattice.Nat

/-!
# Basic results on nonnegative real numbers

This file contains all results on `NNReal` that do not directly follow from its basic structure.
As a consequence, it is a bit of a random collection of results, and is a good target for cleanup.

## Notation

This file uses `ℝ≥0` as a localized notation for `NNReal`.
-/

public section

assert_not_exists TrivialStar

open Function Set
open scoped BigOperators

namespace NNReal
variable {M : Type*} [Zero M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorSemiring Real>=0
  body: inferInstanceAs FloorSemiring (Subtype _)

@[simp, norm_cast]

中文:
实例 :
  签名: FloorSemiring 实数>=0
  定义体: inferInstanceAs FloorSemiring (Subtype _)

@[simp, norm_cast]

Depends on / 依赖: FloorSemiring, Subtype
-/
noncomputable instance : FloorSemiring Real>=0 := inferInstanceAs FloorSemiring (Subtype _)

@[simp, norm_cast]
/--
theorem `coe_mulIndicator` / 定理 `coe_mulIndicator`

English:
theorem coe_mulIndicator
  given: {α} (s : Set α) (f : α -> Real>=0) (a : α)
  proof: map_mulIndicator toRealHom _ _ _

@[simp, norm_cast]

中文:
定理 coe_mulIndicator
  条件: {α} (s : Set α) (f : α -> 实数>=0) (a : α)
  证明: map_mulIndicator toRealHom _ _ _

@[simp, norm_cast]

Depends on / 依赖: map_mulIndicator, toRealHom
-/
theorem coe_mulIndicator {α} (s : Set α) (f : α -> Real>=0) (a : α) :
    ((s.mulIndicator f a : Real>=0) : Real) = s.mulIndicator (fun x => ↑(f x)) a :=
  map_mulIndicator toRealHom _ _ _

@[simp, norm_cast]
/--
theorem `coe_indicator` / 定理 `coe_indicator`

English:
theorem coe_indicator
  given: {α} (s : Set α) (f : α -> Real>=0) (a : α)
  proof: map_indicator toRealHom _ _ _

@[simp, norm_cast]

中文:
定理 coe_indicator
  条件: {α} (s : Set α) (f : α -> 实数>=0) (a : α)
  证明: map_indicator toRealHom _ _ _

@[simp, norm_cast]

Depends on / 依赖: map_indicator, toRealHom
-/
theorem coe_indicator {α} (s : Set α) (f : α -> Real>=0) (a : α) :
    ((s.indicator f a : Real>=0) : Real) = s.indicator (fun x => ↑(f x)) a :=
  map_indicator toRealHom _ _ _

@[simp, norm_cast]
/--
theorem `coe_mulSingle` / 定理 `coe_mulSingle`

English:
theorem coe_mulSingle
  given: {α} [DecidableEq α] (a : α) (b : Real>=0) (c : α)
  proof: by
  simpa using coe_mulIndicator {a} (fun _ => b) c

@[simp, norm_cast]

中文:
定理 coe_mulSingle
  条件: {α} [DecidableEq α] (a : α) (b : 实数>=0) (c : α)
  证明: by
  simpa using coe_mulIndicator {a} (fun _ => b) c

@[simp, norm_cast]

Depends on / 依赖: coe_mulIndicator
-/
theorem coe_mulSingle {α} [DecidableEq α] (a : α) (b : Real>=0) (c : α) :
    ((Pi.mulSingle a b : α -> Real>=0) c : Real) = (Pi.mulSingle a b : α -> Real) c := by
  simpa using coe_mulIndicator {a} (fun _ => b) c

@[simp, norm_cast]
/--
theorem `coe_single` / 定理 `coe_single`

English:
theorem coe_single
  given: {α} [DecidableEq α] (a : α) (b : Real>=0) (c : α)
  proof: by
  simpa using coe_indicator {a} (fun _ => b) c

@[norm_cast]

中文:
定理 coe_single
  条件: {α} [DecidableEq α] (a : α) (b : 实数>=0) (c : α)
  证明: by
  simpa using coe_indicator {a} (fun _ => b) c

@[norm_cast]

Depends on / 依赖: coe_indicator
-/
theorem coe_single {α} [DecidableEq α] (a : α) (b : Real>=0) (c : α) :
    ((Pi.single a b : α -> Real>=0) c : Real) = (Pi.single a b : α -> Real) c := by
  simpa using coe_indicator {a} (fun _ => b) c

@[norm_cast]
/--
theorem `coe_list_sum` / 定理 `coe_list_sum`

English:
theorem coe_list_sum
  given: (l : List Real>=0)
  statement: ((l.sum : Real>=0) : Real) = (l.map (↑)).sum
  proof: map_list_sum toRealHom l

@[norm_cast]

中文:
定理 coe_list_sum
  条件: (l : List 实数>=0)
  结论: ((l.sum : 实数>=0) : 实数) = (l.map (↑)).sum
  证明: map_list_sum toRealHom l

@[norm_cast]

Depends on / 依赖: map_list_sum, toRealHom
-/
theorem coe_list_sum (l : List Real>=0) : ((l.sum : Real>=0) : Real) = (l.map (↑)).sum :=
  map_list_sum toRealHom l

@[norm_cast]
/--
theorem `coe_list_prod` / 定理 `coe_list_prod`

English:
theorem coe_list_prod
  given: (l : List Real>=0)
  statement: ((l.prod : Real>=0) : Real) = (l.map (↑)).prod
  proof: map_list_prod toRealHom l

@[norm_cast]

中文:
定理 coe_list_prod
  条件: (l : List 实数>=0)
  结论: ((l.prod : 实数>=0) : 实数) = (l.map (↑)).prod
  证明: map_list_prod toRealHom l

@[norm_cast]

Depends on / 依赖: map_list_prod, toRealHom
-/
theorem coe_list_prod (l : List Real>=0) : ((l.prod : Real>=0) : Real) = (l.map (↑)).prod :=
  map_list_prod toRealHom l

@[norm_cast]
/--
theorem `coe_multiset_sum` / 定理 `coe_multiset_sum`

English:
theorem coe_multiset_sum
  given: (s : Multiset Real>=0)
  statement: ((s.sum : Real>=0) : Real) = (s.map (↑)).sum
  proof: map_multiset_sum toRealHom s

@[norm_cast]

中文:
定理 coe_multiset_sum
  条件: (s : Multiset 实数>=0)
  结论: ((s.sum : 实数>=0) : 实数) = (s.map (↑)).sum
  证明: map_multiset_sum toRealHom s

@[norm_cast]

Depends on / 依赖: map_multiset_sum, toRealHom
-/
theorem coe_multiset_sum (s : Multiset Real>=0) : ((s.sum : Real>=0) : Real) = (s.map (↑)).sum :=
  map_multiset_sum toRealHom s

@[norm_cast]
/--
theorem `coe_multiset_prod` / 定理 `coe_multiset_prod`

English:
theorem coe_multiset_prod
  given: (s : Multiset Real>=0)
  statement: ((s.prod : Real>=0) : Real) = (s.map (↑)).prod
  proof: map_multiset_prod toRealHom s

中文:
定理 coe_multiset_prod
  条件: (s : Multiset 实数>=0)
  结论: ((s.prod : 实数>=0) : 实数) = (s.map (↑)).prod
  证明: map_multiset_prod toRealHom s

Depends on / 依赖: map_multiset_prod, toRealHom
-/
theorem coe_multiset_prod (s : Multiset Real>=0) : ((s.prod : Real>=0) : Real) = (s.map (↑)).prod :=
  map_multiset_prod toRealHom s

variable {ι : Type*} {s : Finset ι} {f : ι -> Real}

@[simp, norm_cast]
/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: (s : Finset ι) (f : ι -> Real>=0)
  statement: ∑ i in s, f i = ∑ i in s, (f i : Real)
  proof: map_sum toRealHom _ _

@[simp, norm_cast]

中文:
定理 coe_sum
  条件: (s : Finset ι) (f : ι -> 实数>=0)
  结论: ∑ i in s, f i = ∑ i in s, (f i : 实数)
  证明: map_sum toRealHom _ _

@[simp, norm_cast]

Depends on / 依赖: map_sum, toRealHom
-/
theorem coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f i = ∑ i in s, (f i : Real) :=
  map_sum toRealHom _ _

@[simp, norm_cast]
/--
lemma `toReal_finsuppSum` / 引理 `toReal_finsuppSum`

English:
lemma toReal_finsuppSum
  given: (f : ι ->₀ M) (g : ι -> M -> Real>=0)
  proof: map_finsuppSum toRealHom ..

@[simp, norm_cast]

中文:
引理 toReal_finsuppSum
  条件: (f : ι ->₀ M) (g : ι -> M -> 实数>=0)
  证明: map_finsuppSum toRealHom ..

@[simp, norm_cast]

Depends on / 依赖: map_finsuppSum, toRealHom
-/
lemma toReal_finsuppSum (f : ι ->₀ M) (g : ι -> M -> Real>=0) :
    f.sum g = f.sum (fun i m => toReal (g i m)) := map_finsuppSum toRealHom ..

@[simp, norm_cast]
/--
lemma `toReal_finsuppProd` / 引理 `toReal_finsuppProd`

English:
lemma toReal_finsuppProd
  given: (f : ι ->₀ M) (g : ι -> M -> Real>=0)
  proof: map_finsuppProd toRealHom ..

@[simp, norm_cast]

中文:
引理 toReal_finsuppProd
  条件: (f : ι ->₀ M) (g : ι -> M -> 实数>=0)
  证明: map_finsuppProd toRealHom ..

@[simp, norm_cast]

Depends on / 依赖: map_finsuppProd, toRealHom
-/
lemma toReal_finsuppProd (f : ι ->₀ M) (g : ι -> M -> Real>=0) :
    f.prod g = f.prod (fun i m => toReal (g i m)) := map_finsuppProd toRealHom ..

@[simp, norm_cast]
/--
lemma `coe_expect` / 引理 `coe_expect`

English:
lemma coe_expect
  given: (s : Finset ι) (f : ι -> Real>=0)
  statement: 𝔼 i in s, f i = 𝔼 i in s, (f i : Real)
  proof: map_expect toRealHom ..

中文:
引理 coe_expect
  条件: (s : Finset ι) (f : ι -> 实数>=0)
  结论: 𝔼 i in s, f i = 𝔼 i in s, (f i : 实数)
  证明: map_expect toRealHom ..

Depends on / 依赖: map_expect, toRealHom
-/
lemma coe_expect (s : Finset ι) (f : ι -> Real>=0) : 𝔼 i in s, f i = 𝔼 i in s, (f i : Real) :=
  map_expect toRealHom ..

/--
theorem `_root_.Real.toNNReal_sum_of_nonneg` / 定理 `_root_.Real.toNNReal_sum_of_nonneg`

English:
theorem _root_.Real.toNNReal_sum_of_nonneg
  given: (hf : forall i in s, 0 <= f i)
  proof: by
  rw [← coe_inj]; rw [NNReal.coe_sum]; rw [Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

@[simp, norm_cast]

中文:
定理 _root_.Real.toNNReal_sum_of_nonneg
  条件: (hf : 对任意 i in s, 0 <= f i)
  证明: by
  rw [← coe_inj]; rw [NNReal.coe_sum]; rw [Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_nonneg, NNReal, NNReal.coe_sum, Real.coe_toNNReal, coe_inj, coe_sum, coe_toNNReal, sum_congr, sum_nonneg
-/
theorem _root_.Real.toNNReal_sum_of_nonneg (hf : forall i in s, 0 <= f i) :
    Real.toNNReal (∑ a in s, f a) = ∑ a in s, Real.toNNReal (f a) := by
  rw [← coe_inj]; rw [NNReal.coe_sum]; rw [Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Finset ι) (f : ι -> Real>=0)
  statement: ↑(∏ a in s, f a) = ∏ a in s, (f a : Real)
  proof: map_prod toRealHom _ _

中文:
定理 coe_prod
  条件: (s : Finset ι) (f : ι -> 实数>=0)
  结论: ↑(∏ a in s, f a) = ∏ a in s, (f a : 实数)
  证明: map_prod toRealHom _ _

Depends on / 依赖: map_prod, toRealHom
-/
theorem coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s, f a) = ∏ a in s, (f a : Real) :=
  map_prod toRealHom _ _

/--
theorem `_root_.Real.toNNReal_prod_of_nonneg` / 定理 `_root_.Real.toNNReal_prod_of_nonneg`

English:
theorem _root_.Real.toNNReal_prod_of_nonneg
  given: (hf : forall a, a in s -> 0 <= f a)
  proof: by
  rw [← coe_inj]; rw [NNReal.coe_prod]; rw [Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

中文:
定理 _root_.Real.toNNReal_prod_of_nonneg
  条件: (hf : 对任意 a, a in s -> 0 <= f a)
  证明: by
  rw [← coe_inj]; rw [NNReal.coe_prod]; rw [Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_nonneg, NNReal, NNReal.coe_prod, Real.coe_toNNReal, coe_inj, coe_prod, coe_toNNReal, prod_congr, prod_nonneg
-/
theorem _root_.Real.toNNReal_prod_of_nonneg (hf : forall a, a in s -> 0 <= f a) :
    Real.toNNReal (∏ a in s, f a) = ∏ a in s, Real.toNNReal (f a) := by
  rw [← coe_inj]; rw [NNReal.coe_prod]; rw [Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

/--
theorem `le_iInf_add_iInf` / 定理 `le_iInf_add_iInf`

English:
theorem le_iInf_add_iInf
  statement: {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι -> Real>=0} {g : ι' -> Real>=0}
  proof: by
  rw [← NNReal.coe_le_coe]; rw [NNReal.coe_add]; rw [coe_iInf]; rw [coe_iInf]
  exact le_ciInf_add_ciInf h

中文:
定理 le_iInf_add_iInf
  结论: {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι -> 实数>=0} {g : ι' -> 实数>=0}
  证明: by
  rw [← NNReal.coe_le_coe]; rw [NNReal.coe_add]; rw [coe_iInf]; rw [coe_iInf]
  exact le_ciInf_add_ciInf h

Depends on / 依赖: NNReal, NNReal.coe_add, NNReal.coe_le_coe, coe_add, coe_iInf, coe_le_coe, le_ciInf_add_ciInf
-/
theorem le_iInf_add_iInf {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι -> Real>=0} {g : ι' -> Real>=0}
    {a : Real>=0} (h : forall i j, a <= f i + g j) : a <= (⨅ i, f i) + ⨅ j, g j := by
  rw [← NNReal.coe_le_coe]; rw [NNReal.coe_add]; rw [coe_iInf]; rw [coe_iInf]
  exact le_ciInf_add_ciInf h

/--
theorem `mul_finset_sup` / 定理 `mul_finset_sup`

English:
theorem mul_finset_sup
  given: {α} (r : Real>=0) (s : Finset α) (f : α -> Real>=0)
  proof: Finset.apply_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)

中文:
定理 mul_finset_sup
  条件: {α} (r : 实数>=0) (s : Finset α) (f : α -> 实数>=0)
  证明: Finset.apply_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)

Depends on / 依赖: Finset, Finset.apply_sup_eq_sup_comp, NNReal, NNReal.mul_sup, apply_sup_eq_sup_comp, mul_sup, mul_zero
-/
theorem mul_finset_sup {α} (r : Real>=0) (s : Finset α) (f : α -> Real>=0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.apply_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)

/--
theorem `finset_sup_mul` / 定理 `finset_sup_mul`

English:
theorem finset_sup_mul
  given: {α} (s : Finset α) (f : α -> Real>=0) (r : Real>=0)
  proof: Finset.apply_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)

中文:
定理 finset_sup_mul
  条件: {α} (s : Finset α) (f : α -> 实数>=0) (r : 实数>=0)
  证明: Finset.apply_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)

Depends on / 依赖: Finset, Finset.apply_sup_eq_sup_comp, NNReal, NNReal.sup_mul, apply_sup_eq_sup_comp, sup_mul, zero_mul
-/
theorem finset_sup_mul {α} (s : Finset α) (f : α -> Real>=0) (r : Real>=0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.apply_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)

/--
theorem `finset_sup_div` / 定理 `finset_sup_div`

English:
theorem finset_sup_div
  given: {α} {f : α -> Real>=0} {s : Finset α} (r : Real>=0)
  proof: by simp only [div_eq_inv_mul, mul_finset_sup]

中文:
定理 finset_sup_div
  条件: {α} {f : α -> 实数>=0} {s : Finset α} (r : 实数>=0)
  证明: by simp only [div_eq_inv_mul, mul_finset_sup]

Depends on / 依赖: div_eq_inv_mul, mul_finset_sup
-/
theorem finset_sup_div {α} {f : α -> Real>=0} {s : Finset α} (r : Real>=0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]

section Set

/--
lemma `bddAbove_natCast_image_iff` / 引理 `bddAbove_natCast_image_iff`

English:
lemma bddAbove_natCast_image_iff
  given: {s : Set Nat}
  statement: BddAbove ((↑) '' s : Set Real>=0) ↔ BddAbove s
  proof: ⟨.imp' Nat.floor (by simp [upperBounds, Nat.le_floor_iff]), .imp' (↑) (by simp [upperBounds])⟩

中文:
引理 bddAbove_natCast_image_iff
  条件: {s : Set 自然数}
  结论: BddAbove ((↑) '' s : Set 实数>=0) ↔ BddAbove s
  证明: ⟨.imp' Nat.floor (by simp [upperBounds, Nat.le_floor_iff]), .imp' (↑) (by simp [upperBounds])⟩
-/
@[simp] lemma bddAbove_natCast_image_iff {s : Set Nat} : BddAbove ((↑) '' s : Set Real>=0) ↔ BddAbove s :=
  ⟨.imp' Nat.floor (by simp [upperBounds, Nat.le_floor_iff]), .imp' (↑) (by simp [upperBounds])⟩

/--
lemma `bddAbove_range_natCast_iff` / 引理 `bddAbove_range_natCast_iff`

English:
lemma bddAbove_range_natCast_iff
  given: {ι : Sort*} (f : ι -> Nat)
  proof: by
  rw [← bddAbove_natCast_image_iff]; rw [← Set.range_comp]
  rfl

中文:
引理 bddAbove_range_natCast_iff
  条件: {ι : Sort*} (f : ι -> 自然数)
  证明: by
  rw [← bddAbove_natCast_image_iff]; rw [← Set.range_comp]
  rfl
-/
@[simp, norm_cast] lemma bddAbove_range_natCast_iff {ι : Sort*} (f : ι -> Nat) :
    BddAbove (Set.range (f ·) : Set NNReal) ↔ BddAbove (Set.range f) := by
  rw [← bddAbove_natCast_image_iff]; rw [← Set.range_comp]
  rfl

end Set

open Real

section Sub


/--
theorem `sub_div` / 定理 `sub_div`

English:
theorem sub_div
  given: (a b c : Real>=0)
  statement: (a - b) / c = a / c - b / c
  proof: tsub_div _ _ _

中文:
定理 sub_div
  条件: (a b c : 实数>=0)
  结论: (a - b) / c = a / c - b / c
  证明: tsub_div _ _ _

Depends on / 依赖: tsub_div
-/
theorem sub_div (a b c : Real>=0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _

/-- This lemma is needed for the `norm_cast` simp set. Outside of this use case `Nat.coe_sub`
should be used. -/
@[norm_cast]
/--
theorem `coe_sub_of_lt` / 定理 `coe_sub_of_lt`

English:
theorem coe_sub_of_lt
  given: {a b : Real>=0} (h : a < b)
  proof: NNReal.coe_sub h.le

中文:
定理 coe_sub_of_lt
  条件: {a b : 实数>=0} (h : a < b)
  证明: NNReal.coe_sub h.le
-/
protected theorem coe_sub_of_lt {a b : Real>=0} (h : a < b) :
    ((b - a : Real>=0) : Real) = b - a := NNReal.coe_sub h.le

end Sub

section Csupr

open Set

variable {ι : Sort*} {f : ι -> Real>=0}

/--
theorem `iInf_mul` / 定理 `iInf_mul`

English:
theorem iInf_mul
  given: (f : ι -> Real>=0) (a : Real>=0)
  statement: iInf f * a = ⨅ i, f i * a
  proof: by
  rw [← coe_inj]; rw [NNReal.coe_mul]; rw [coe_iInf]; rw [coe_iInf]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _

中文:
定理 iInf_mul
  条件: (f : ι -> 实数>=0) (a : 实数>=0)
  结论: iInf f * a = ⨅ i, f i * a
  证明: by
  rw [← coe_inj]; rw [NNReal.coe_mul]; rw [coe_iInf]; rw [coe_iInf]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.coe_nonneg, Real.iInf_mul_of_nonneg, coe_iInf, coe_inj, coe_mul, coe_nonneg, iInf_mul_of_nonneg
-/
theorem iInf_mul (f : ι -> Real>=0) (a : Real>=0) : iInf f * a = ⨅ i, f i * a := by
  rw [← coe_inj]; rw [NNReal.coe_mul]; rw [coe_iInf]; rw [coe_iInf]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _

/--
theorem `mul_iInf` / 定理 `mul_iInf`

English:
theorem mul_iInf
  given: (f : ι -> Real>=0) (a : Real>=0)
  statement: a * iInf f = ⨅ i, a * f i
  proof: by
  simpa only [mul_comm] using iInf_mul f a

中文:
定理 mul_iInf
  条件: (f : ι -> 实数>=0) (a : 实数>=0)
  结论: a * iInf f = ⨅ i, a * f i
  证明: by
  simpa only [mul_comm] using iInf_mul f a

Depends on / 依赖: iInf_mul, mul_comm
-/
theorem mul_iInf (f : ι -> Real>=0) (a : Real>=0) : a * iInf f = ⨅ i, a * f i := by
  simpa only [mul_comm] using iInf_mul f a

/--
theorem `mul_iSup` / 定理 `mul_iSup`

English:
theorem mul_iSup
  given: (f : ι -> Real>=0) (a : Real>=0)
  statement: (a * ⨆ i, f i) = ⨆ i, a * f i
  proof: by
  rw [← coe_inj]; rw [NNReal.coe_mul]; rw [NNReal.coe_iSup]; rw [NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _

中文:
定理 mul_iSup
  条件: (f : ι -> 实数>=0) (a : 实数>=0)
  结论: (a * ⨆ i, f i) = ⨆ i, a * f i
  证明: by
  rw [← coe_inj]; rw [NNReal.coe_mul]; rw [NNReal.coe_iSup]; rw [NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _

Depends on / 依赖: NNReal, NNReal.coe_iSup, NNReal.coe_mul, NNReal.coe_nonneg, Real.mul_iSup_of_nonneg, coe_iSup, coe_inj, coe_mul, coe_nonneg, mul_iSup_of_nonneg
-/
theorem mul_iSup (f : ι -> Real>=0) (a : Real>=0) : (a * ⨆ i, f i) = ⨆ i, a * f i := by
  rw [← coe_inj]; rw [NNReal.coe_mul]; rw [NNReal.coe_iSup]; rw [NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _

/--
theorem `iSup_mul` / 定理 `iSup_mul`

English:
theorem iSup_mul
  given: (f : ι -> Real>=0) (a : Real>=0)
  statement: (⨆ i, f i) * a = ⨆ i, f i * a
  proof: by
  rw [mul_comm]; rw [mul_iSup]
  simp_rw [mul_comm]

中文:
定理 iSup_mul
  条件: (f : ι -> 实数>=0) (a : 实数>=0)
  结论: (⨆ i, f i) * a = ⨆ i, f i * a
  证明: by
  rw [mul_comm]; rw [mul_iSup]
  simp_rw [mul_comm]

Depends on / 依赖: mul_comm, mul_iSup, simp_rw
-/
theorem iSup_mul (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm]; rw [mul_iSup]
  simp_rw [mul_comm]

/--
theorem `iSup_div` / 定理 `iSup_div`

English:
theorem iSup_div
  given: (f : ι -> Real>=0) (a : Real>=0)
  statement: (⨆ i, f i) / a = ⨆ i, f i / a
  proof: by
  simp only [div_eq_mul_inv, iSup_mul]

中文:
定理 iSup_div
  条件: (f : ι -> 实数>=0) (a : 实数>=0)
  结论: (⨆ i, f i) / a = ⨆ i, f i / a
  证明: by
  simp only [div_eq_mul_inv, iSup_mul]

Depends on / 依赖: div_eq_mul_inv, iSup_mul
-/
theorem iSup_div (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, iSup_mul]

/--
theorem `mul_iSup_le` / 定理 `mul_iSup_le`

English:
theorem mul_iSup_le
  given: {a : Real>=0} {g : Real>=0} {h : ι -> Real>=0} (H : forall j, g * h j <= a)
  statement: g * iSup h <= a
  proof: by
  rw [mul_iSup]
  exact ciSup_le' H

中文:
定理 mul_iSup_le
  条件: {a : 实数>=0} {g : 实数>=0} {h : ι -> 实数>=0} (H : 对任意 j, g * h j <= a)
  结论: g * iSup h <= a
  证明: by
  rw [mul_iSup]
  exact ciSup_le' H

Depends on / 依赖: ciSup_le, mul_iSup
-/
theorem mul_iSup_le {a : Real>=0} {g : Real>=0} {h : ι -> Real>=0} (H : forall j, g * h j <= a) : g * iSup h <= a := by
  rw [mul_iSup]
  exact ciSup_le' H

/--
theorem `iSup_mul_le` / 定理 `iSup_mul_le`

English:
theorem iSup_mul_le
  given: {a : Real>=0} {g : ι -> Real>=0} {h : Real>=0} (H : forall i, g i * h <= a)
  statement: iSup g * h <= a
  proof: by
  rw [iSup_mul]
  exact ciSup_le' H

中文:
定理 iSup_mul_le
  条件: {a : 实数>=0} {g : ι -> 实数>=0} {h : 实数>=0} (H : 对任意 i, g i * h <= a)
  结论: iSup g * h <= a
  证明: by
  rw [iSup_mul]
  exact ciSup_le' H

Depends on / 依赖: ciSup_le, iSup_mul
-/
theorem iSup_mul_le {a : Real>=0} {g : ι -> Real>=0} {h : Real>=0} (H : forall i, g i * h <= a) : iSup g * h <= a := by
  rw [iSup_mul]
  exact ciSup_le' H

/--
theorem `iSup_mul_iSup_le` / 定理 `iSup_mul_iSup_le`

English:
theorem iSup_mul_iSup_le
  given: {a : Real>=0} {g h : ι -> Real>=0} (H : forall i j, g i * h j <= a)
  proof: iSup_mul_le fun _ => mul_iSup_le H _

中文:
定理 iSup_mul_iSup_le
  条件: {a : 实数>=0} {g h : ι -> 实数>=0} (H : 对任意 i j, g i * h j <= a)
  证明: iSup_mul_le fun _ => mul_iSup_le H _

Depends on / 依赖: iSup_mul_le, mul_iSup_le
-/
theorem iSup_mul_iSup_le {a : Real>=0} {g h : ι -> Real>=0} (H : forall i j, g i * h j <= a) :
    iSup g * iSup h <= a :=
iSup_mul_le fun _ => mul_iSup_le H _

variable [Nonempty ι]

/--
theorem `le_mul_iInf` / 定理 `le_mul_iInf`

English:
theorem le_mul_iInf
  given: {a : Real>=0} {g : Real>=0} {h : ι -> Real>=0} (H : forall j, a <= g * h j)
  statement: a <= g * iInf h
  proof: by
  rw [mul_iInf]
  exact le_ciInf H

中文:
定理 le_mul_iInf
  条件: {a : 实数>=0} {g : 实数>=0} {h : ι -> 实数>=0} (H : 对任意 j, a <= g * h j)
  结论: a <= g * iInf h
  证明: by
  rw [mul_iInf]
  exact le_ciInf H

Depends on / 依赖: le_ciInf, mul_iInf
-/
theorem le_mul_iInf {a : Real>=0} {g : Real>=0} {h : ι -> Real>=0} (H : forall j, a <= g * h j) : a <= g * iInf h := by
  rw [mul_iInf]
  exact le_ciInf H

/--
theorem `le_iInf_mul` / 定理 `le_iInf_mul`

English:
theorem le_iInf_mul
  given: {a : Real>=0} {g : ι -> Real>=0} {h : Real>=0} (H : forall i, a <= g i * h)
  statement: a <= iInf g * h
  proof: by
  rw [iInf_mul]
  exact le_ciInf H

中文:
定理 le_iInf_mul
  条件: {a : 实数>=0} {g : ι -> 实数>=0} {h : 实数>=0} (H : 对任意 i, a <= g i * h)
  结论: a <= iInf g * h
  证明: by
  rw [iInf_mul]
  exact le_ciInf H

Depends on / 依赖: iInf_mul, le_ciInf
-/
theorem le_iInf_mul {a : Real>=0} {g : ι -> Real>=0} {h : Real>=0} (H : forall i, a <= g i * h) : a <= iInf g * h := by
  rw [iInf_mul]
  exact le_ciInf H

/--
theorem `le_iInf_mul_iInf` / 定理 `le_iInf_mul_iInf`

English:
theorem le_iInf_mul_iInf
  given: {a : Real>=0} {g h : ι -> Real>=0} (H : forall i j, a <= g i * h j)
  proof: le_iInf_mul fun i => le_mul_iInf H i

中文:
定理 le_iInf_mul_iInf
  条件: {a : 实数>=0} {g h : ι -> 实数>=0} (H : 对任意 i j, a <= g i * h j)
  证明: le_iInf_mul fun i => le_mul_iInf H i

Depends on / 依赖: le_iInf_mul, le_mul_iInf
-/
theorem le_iInf_mul_iInf {a : Real>=0} {g h : ι -> Real>=0} (H : forall i j, a <= g i * h j) :
    a <= iInf g * iInf h :=
le_iInf_mul fun i => le_mul_iInf H i

/--
lemma `natCast_iSup` / 引理 `natCast_iSup`

English:
lemma natCast_iSup
  given: {ι : Sort*} (f : ι -> Nat)
  proof: by
  by_cases h : BddAbove (Set.range f)
  · apply eq_of_forall_ge_iff
    simp [ciSup_le_iff', ← Nat.le_floor_iff, *]
  · simp [*]

中文:
引理 natCast_iSup
  条件: {ι : Sort*} (f : ι -> 自然数)
  证明: by
  by_cases h : BddAbove (Set.range f)
  · apply eq_of_forall_ge_iff
    simp [ciSup_le_iff', ← Nat.le_floor_iff, *]
  · simp [*]
-/
@[simp, norm_cast] lemma natCast_iSup {ι : Sort*} (f : ι -> Nat) :
    ⨆ i, f i = (⨆ i, f i : NNReal) := by
  by_cases h : BddAbove (Set.range f)
  · apply eq_of_forall_ge_iff
    simp [ciSup_le_iff', ← Nat.le_floor_iff, *]
  · simp [*]

/--
lemma `natCast_iInf` / 引理 `natCast_iInf`

English:
lemma natCast_iInf
  given: {ι : Sort*} (f : ι -> Nat)
  proof: by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [iInf_empty]
  apply eq_of_forall_le_iff
  simp [le_ciInf_iff, ← Nat.ceil_le]

中文:
引理 natCast_iInf
  条件: {ι : Sort*} (f : ι -> 自然数)
  证明: by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [iInf_empty]
  apply eq_of_forall_le_iff
  simp [le_ciInf_iff, ← Nat.ceil_le]
-/
@[simp, norm_cast] lemma natCast_iInf {ι : Sort*} (f : ι -> Nat) :
    ⨅ i, f i = (⨅ i, f i : NNReal) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [iInf_empty]
  apply eq_of_forall_le_iff
  simp [le_ciInf_iff, ← Nat.ceil_le]

end Csupr

section rify

/--
lemma `toReal_eq` / 引理 `toReal_eq`

English:
lemma toReal_eq
  given: (a b : Real>=0)
  statement: a = b ↔ (a : Real) = (b : Real)
  proof: by simp

中文:
引理 toReal_eq
  条件: (a b : 实数>=0)
  结论: a = b ↔ (a : 实数) = (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma toReal_eq (a b : Real>=0) : a = b ↔ (a : Real) = (b : Real) := by simp

/--
lemma `toReal_le` / 引理 `toReal_le`

English:
lemma toReal_le
  given: (a b : Real>=0)
  statement: a <= b ↔ (a : Real) <= (b : Real)
  proof: by simp

中文:
引理 toReal_le
  条件: (a b : 实数>=0)
  结论: a <= b ↔ (a : 实数) <= (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma toReal_le (a b : Real>=0) : a <= b ↔ (a : Real) <= (b : Real) := by simp

/--
lemma `toReal_lt` / 引理 `toReal_lt`

English:
lemma toReal_lt
  given: (a b : Real>=0)
  statement: a < b ↔ (a : Real) < (b : Real)
  proof: by simp

中文:
引理 toReal_lt
  条件: (a b : 实数>=0)
  结论: a < b ↔ (a : 实数) < (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma toReal_lt (a b : Real>=0) : a < b ↔ (a : Real) < (b : Real) := by simp

/--
lemma `toReal_ne` / 引理 `toReal_ne`

English:
lemma toReal_ne
  given: (a b : Real>=0)
  statement: a != b ↔ (a : Real) != (b : Real)
  proof: by simp

中文:
引理 toReal_ne
  条件: (a b : 实数>=0)
  结论: a != b ↔ (a : 实数) != (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma toReal_ne (a b : Real>=0) : a != b ↔ (a : Real) != (b : Real) := by simp

end rify

@[simp]
/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: range toReal = Ici 0
  proof: Subtype.range_coe

@[simp]

中文:
定理 range_coe
  结论: range to实数 = Ici 0
  证明: Subtype.range_coe

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe, range_coe
-/
theorem range_coe : range toReal = Ici 0 := Subtype.range_coe

@[simp]
/--
theorem `image_coe_Ici` / 定理 `image_coe_Ici`

English:
theorem image_coe_Ici
  given: (x : Real>=0)
  statement: toReal '' Ici x = Ici ↑x
  proof: image_subtype_val_Ici_Ici ..

@[simp]

中文:
定理 image_coe_Ici
  条件: (x : 实数>=0)
  结论: to实数 '' Ici x = Ici ↑x
  证明: image_subtype_val_Ici_Ici ..

@[simp]

Depends on / 依赖: image_subtype_val_Ici_Ici
-/
theorem image_coe_Ici (x : Real>=0) : toReal '' Ici x = Ici ↑x := image_subtype_val_Ici_Ici ..

@[simp]
/--
theorem `image_coe_Iic` / 定理 `image_coe_Iic`

English:
theorem image_coe_Iic
  given: (x : Real>=0)
  statement: toReal '' Iic x = Icc 0 ↑x
  proof: image_subtype_val_Ici_Iic ..

@[simp]

中文:
定理 image_coe_Iic
  条件: (x : 实数>=0)
  结论: to实数 '' Iic x = Icc 0 ↑x
  证明: image_subtype_val_Ici_Iic ..

@[simp]

Depends on / 依赖: image_subtype_val_Ici_Iic
-/
theorem image_coe_Iic (x : Real>=0) : toReal '' Iic x = Icc 0 ↑x := image_subtype_val_Ici_Iic ..

@[simp]
/--
theorem `image_coe_Ioi` / 定理 `image_coe_Ioi`

English:
theorem image_coe_Ioi
  given: (x : Real>=0)
  statement: toReal '' Ioi x = Ioi ↑x
  proof: image_subtype_val_Ici_Ioi ..

@[simp]

中文:
定理 image_coe_Ioi
  条件: (x : 实数>=0)
  结论: to实数 '' Ioi x = Ioi ↑x
  证明: image_subtype_val_Ici_Ioi ..

@[simp]

Depends on / 依赖: image_subtype_val_Ici_Ioi
-/
theorem image_coe_Ioi (x : Real>=0) : toReal '' Ioi x = Ioi ↑x := image_subtype_val_Ici_Ioi ..

@[simp]
/--
theorem `image_coe_Iio` / 定理 `image_coe_Iio`

English:
theorem image_coe_Iio
  given: (x : Real>=0)
  statement: toReal '' Iio x = Ico 0 ↑x
  proof: image_subtype_val_Ici_Iio ..

@[simp]

中文:
定理 image_coe_Iio
  条件: (x : 实数>=0)
  结论: to实数 '' Iio x = Ico 0 ↑x
  证明: image_subtype_val_Ici_Iio ..

@[simp]

Depends on / 依赖: image_subtype_val_Ici_Iio
-/
theorem image_coe_Iio (x : Real>=0) : toReal '' Iio x = Ico 0 ↑x := image_subtype_val_Ici_Iio ..

@[simp]
/--
theorem `image_coe_Icc` / 定理 `image_coe_Icc`

English:
theorem image_coe_Icc
  given: (x y : Real>=0)
  statement: toReal '' Icc x y = Icc ↑x ↑y
  proof: image_subtype_val_Icc (s := Ici 0) ..

@[simp]

中文:
定理 image_coe_Icc
  条件: (x y : 实数>=0)
  结论: to实数 '' Icc x y = Icc ↑x ↑y
  证明: image_subtype_val_Icc (s := Ici 0) ..

@[simp]

Depends on / 依赖: image_subtype_val_Icc
-/
theorem image_coe_Icc (x y : Real>=0) : toReal '' Icc x y = Icc ↑x ↑y :=
  image_subtype_val_Icc (s := Ici 0) ..

@[simp]
/--
theorem `image_coe_Ioc` / 定理 `image_coe_Ioc`

English:
theorem image_coe_Ioc
  given: (x y : Real>=0)
  statement: toReal '' Ioc x y = Ioc ↑x ↑y
  proof: image_subtype_val_Ioc (s := Ici 0) ..

@[simp]

中文:
定理 image_coe_Ioc
  条件: (x y : 实数>=0)
  结论: to实数 '' Ioc x y = Ioc ↑x ↑y
  证明: image_subtype_val_Ioc (s := Ici 0) ..

@[simp]

Depends on / 依赖: image_subtype_val_Ioc
-/
theorem image_coe_Ioc (x y : Real>=0) : toReal '' Ioc x y = Ioc ↑x ↑y :=
  image_subtype_val_Ioc (s := Ici 0) ..

@[simp]
/--
theorem `image_coe_Ico` / 定理 `image_coe_Ico`

English:
theorem image_coe_Ico
  given: (x y : Real>=0)
  statement: toReal '' Ico x y = Ico ↑x ↑y
  proof: image_subtype_val_Ico (s := Ici 0) ..

@[simp]

中文:
定理 image_coe_Ico
  条件: (x y : 实数>=0)
  结论: to实数 '' Ico x y = Ico ↑x ↑y
  证明: image_subtype_val_Ico (s := Ici 0) ..

@[simp]

Depends on / 依赖: image_subtype_val_Ico
-/
theorem image_coe_Ico (x y : Real>=0) : toReal '' Ico x y = Ico ↑x ↑y :=
  image_subtype_val_Ico (s := Ici 0) ..

@[simp]
/--
theorem `image_coe_Ioo` / 定理 `image_coe_Ioo`

English:
theorem image_coe_Ioo
  given: (x y : Real>=0)
  statement: toReal '' Ioo x y = Ioo ↑x ↑y
  proof: image_subtype_val_Ioo (s := Ici 0) ..

@[simp]

中文:
定理 image_coe_Ioo
  条件: (x y : 实数>=0)
  结论: to实数 '' Ioo x y = Ioo ↑x ↑y
  证明: image_subtype_val_Ioo (s := Ici 0) ..

@[simp]

Depends on / 依赖: image_subtype_val_Ioo
-/
theorem image_coe_Ioo (x y : Real>=0) : toReal '' Ioo x y = Ioo ↑x ↑y :=
  image_subtype_val_Ioo (s := Ici 0) ..

@[simp]
/--
theorem `image_coe_uIcc` / 定理 `image_coe_uIcc`

English:
theorem image_coe_uIcc
  given: (x y : Real>=0)
  statement: toReal '' uIcc x y = uIcc ↑x ↑y
  proof: image_subtype_val_uIcc (s := Ici 0) ..

@[simp]

中文:
定理 image_coe_uIcc
  条件: (x y : 实数>=0)
  结论: to实数 '' uIcc x y = uIcc ↑x ↑y
  证明: image_subtype_val_uIcc (s := Ici 0) ..

@[simp]

Depends on / 依赖: image_subtype_val_uIcc
-/
theorem image_coe_uIcc (x y : Real>=0) : toReal '' uIcc x y = uIcc ↑x ↑y :=
  image_subtype_val_uIcc (s := Ici 0) ..

@[simp]
/--
theorem `image_coe_uIoc` / 定理 `image_coe_uIoc`

English:
theorem image_coe_uIoc
  given: (x y : Real>=0)
  statement: toReal '' uIoc x y = uIoc ↑x ↑y
  proof: image_subtype_val_uIoc (s := Ici 0) ..

@[simp]

中文:
定理 image_coe_uIoc
  条件: (x y : 实数>=0)
  结论: to实数 '' uIoc x y = uIoc ↑x ↑y
  证明: image_subtype_val_uIoc (s := Ici 0) ..

@[simp]

Depends on / 依赖: image_subtype_val_uIoc
-/
theorem image_coe_uIoc (x y : Real>=0) : toReal '' uIoc x y = uIoc ↑x ↑y :=
  image_subtype_val_uIoc (s := Ici 0) ..

@[simp]
/--
theorem `image_coe_uIoo` / 定理 `image_coe_uIoo`

English:
theorem image_coe_uIoo
  given: (x y : Real>=0)
  statement: toReal '' uIoo x y = uIoo ↑x ↑y
  proof: image_subtype_val_uIoo (s := Ici 0) ..

中文:
定理 image_coe_uIoo
  条件: (x y : 实数>=0)
  结论: to实数 '' uIoo x y = uIoo ↑x ↑y
  证明: image_subtype_val_uIoo (s := Ici 0) ..

Depends on / 依赖: image_subtype_val_uIoo
-/
theorem image_coe_uIoo (x y : Real>=0) : toReal '' uIoo x y = uIoo ↑x ↑y :=
  image_subtype_val_uIoo (s := Ici 0) ..

end NNReal
