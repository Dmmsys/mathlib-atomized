/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.SetTheory.Cardinal.Arithmetic

import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Cardinality of Hahn series

We define `HahnSeries.cardSupp` as the cardinality of the support of a Hahn series, and find bounds
for the cardinalities of different operations. We also build the subgroups, subrings, etc. of Hahn
series bounded by a given infinite cardinal.
-/

@[expose] public section

open Cardinal

namespace HahnSeries

variable {Γ R S α : Type*}

/-! ### Cardinality function -/

section PartialOrder
variable [PartialOrder Γ]

section Zero
variable [Zero R]

/--
Definition of `cardSupp` / `cardSupp` 的定义

English:
definition cardSupp
  signature: (x : R⟦Γ⟧)
  body: #x.support

中文:
定义 cardSupp
  签名: (x : R⟦Γ⟧)
  定义体: #x.support

Depends on / 依赖: support, x.support
-/
def cardSupp (x : R⟦Γ⟧) : Cardinal :=
  #x.support

/--
theorem `cardSupp_congr` / 定理 `cardSupp_congr`

English:
theorem cardSupp_congr
  given: [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support)
  proof: by
  simp_rw [cardSupp, h]

中文:
定理 cardSupp_congr
  条件: [零 S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support)
  证明: by
  simp_rw [cardSupp, h]

Depends on / 依赖: cardSupp, simp_rw
-/
theorem cardSupp_congr [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support) :
    x.cardSupp = y.cardSupp := by
  simp_rw [cardSupp, h]

/--
theorem `cardSupp_mono` / 定理 `cardSupp_mono`

English:
theorem cardSupp_mono
  given: [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support subseteq y.support)
  proof: mk_le_mk_of_subset h

@[simp]

中文:
定理 cardSupp_mono
  条件: [零 S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support subseteq y.support)
  证明: mk_le_mk_of_subset h

@[simp]

Depends on / 依赖: mk_le_mk_of_subset
-/
theorem cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support subseteq y.support) :
    x.cardSupp <= y.cardSupp :=
  mk_le_mk_of_subset h

@[simp]
/--
theorem `cardSupp_zero` / 定理 `cardSupp_zero`

English:
theorem cardSupp_zero
  statement: cardSupp (0 : R⟦Γ⟧) = 0
  proof: by
  simp [cardSupp]

中文:
定理 cardSupp_zero
  结论: cardSupp (0 : R⟦Γ⟧) = 0
  证明: by
  simp [cardSupp]

Depends on / 依赖: cardSupp
-/
theorem cardSupp_zero : cardSupp (0 : R⟦Γ⟧) = 0 := by
  simp [cardSupp]

/--
theorem `cardSupp_single_of_ne` / 定理 `cardSupp_single_of_ne`

English:
theorem cardSupp_single_of_ne
  given: (a : Γ) {r : R} (h : r != 0)
  statement: cardSupp (single a r) = 1
  proof: by
  rw [cardSupp]; rw [support_single_of_ne h]; rw [mk_singleton]

中文:
定理 cardSupp_single_of_ne
  条件: (a : Γ) {r : R} (h : r != 0)
  结论: cardSupp (single a r) = 1
  证明: by
  rw [cardSupp]; rw [support_single_of_ne h]; rw [mk_singleton]

Depends on / 依赖: cardSupp, mk_singleton, support_single_of_ne
-/
theorem cardSupp_single_of_ne (a : Γ) {r : R} (h : r != 0) : cardSupp (single a r) = 1 := by
  rw [cardSupp]; rw [support_single_of_ne h]; rw [mk_singleton]

/--
theorem `cardSupp_single_le` / 定理 `cardSupp_single_le`

English:
theorem cardSupp_single_le
  given: (a : Γ) (r : R)
  statement: cardSupp (single a r) <= 1
  proof: (mk_le_mk_of_subset support_single_subset).trans_eq (mk_singleton a)

@[simp]

中文:
定理 cardSupp_single_le
  条件: (a : Γ) (r : R)
  结论: cardSupp (single a r) <= 1
  证明: (mk_le_mk_of_subset support_single_subset).trans_eq (mk_singleton a)

@[simp]

Depends on / 依赖: mk_le_mk_of_subset, mk_singleton, support_single_subset, trans_eq
-/
theorem cardSupp_single_le (a : Γ) (r : R) : cardSupp (single a r) <= 1 :=
  (mk_le_mk_of_subset support_single_subset).trans_eq (mk_singleton a)

@[simp]
/--
theorem `cardSupp_one_le` / 定理 `cardSupp_one_le`

English:
theorem cardSupp_one_le
  given: [Zero Γ] [One R]
  statement: cardSupp (1 : R⟦Γ⟧) <= 1
  proof: cardSupp_single_le ..

@[simp]

中文:
定理 cardSupp_one_le
  条件: [零 Γ] [幺 R]
  结论: cardSupp (1 : R⟦Γ⟧) <= 1
  证明: cardSupp_single_le ..

@[simp]

Depends on / 依赖: cardSupp_single_le
-/
theorem cardSupp_one_le [Zero Γ] [One R] : cardSupp (1 : R⟦Γ⟧) <= 1 :=
  cardSupp_single_le ..

@[simp]
/--
theorem `cardSupp_one` / 定理 `cardSupp_one`

English:
theorem cardSupp_one
  given: [Zero Γ] [One R] [NeZero (1 : R)]
  statement: cardSupp (1 : R⟦Γ⟧) = 1
  proof: cardSupp_single_of_ne _ one_ne_zero

中文:
定理 cardSupp_one
  条件: [零 Γ] [幺 R] [NeZero (1 : R)]
  结论: cardSupp (1 : R⟦Γ⟧) = 1
  证明: cardSupp_single_of_ne _ one_ne_zero

Depends on / 依赖: cardSupp_single_of_ne, one_ne_zero
-/
theorem cardSupp_one [Zero Γ] [One R] [NeZero (1 : R)] : cardSupp (1 : R⟦Γ⟧) = 1 :=
  cardSupp_single_of_ne _ one_ne_zero

/--
theorem `cardSupp_map_le` / 定理 `cardSupp_map_le`

English:
theorem cardSupp_map_le
  given: [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S)
  statement: (x.map f).cardSupp <= x.cardSupp
  proof: cardSupp_mono support_map_subset ..

中文:
定理 cardSupp_map_le
  条件: [零 S] (x : R⟦Γ⟧) (f : 保零态射 R S)
  结论: (x.map f).cardSupp <= x.cardSupp
  证明: cardSupp_mono support_map_subset ..

Depends on / 依赖: cardSupp_mono, support_map_subset
-/
theorem cardSupp_map_le [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) : (x.map f).cardSupp <= x.cardSupp :=
cardSupp_mono support_map_subset ..

/--
theorem `cardSupp_truncLT_le` / 定理 `cardSupp_truncLT_le`

English:
theorem cardSupp_truncLT_le
  given: [DecidableLT Γ] (x : R⟦Γ⟧) (c : Γ)
  proof: cardSupp_mono support_truncLT_subset ..

中文:
定理 cardSupp_truncLT_le
  条件: [DecidableLT Γ] (x : R⟦Γ⟧) (c : Γ)
  证明: cardSupp_mono support_truncLT_subset ..

Depends on / 依赖: cardSupp_mono, support_truncLT_subset
-/
theorem cardSupp_truncLT_le [DecidableLT Γ] (x : R⟦Γ⟧) (c : Γ) :
    (truncLT c x).cardSupp <= x.cardSupp :=
cardSupp_mono support_truncLT_subset ..

/--
theorem `cardSupp_smul_le` / 定理 `cardSupp_smul_le`

English:
theorem cardSupp_smul_le
  given: (s : S) (x : R⟦Γ⟧) [SMulZeroClass S R]
  statement: (s • x).cardSupp <= x.cardSupp
  proof: cardSupp_mono support_smul_subset ..

中文:
定理 cardSupp_smul_le
  条件: (s : S) (x : R⟦Γ⟧) [SMulZero类 S R]
  结论: (s • x).cardSupp <= x.cardSupp
  证明: cardSupp_mono support_smul_subset ..

Depends on / 依赖: cardSupp_mono, support_smul_subset
-/
theorem cardSupp_smul_le (s : S) (x : R⟦Γ⟧) [SMulZeroClass S R] : (s • x).cardSupp <= x.cardSupp :=
cardSupp_mono support_smul_subset ..

end Zero

/--
theorem `cardSupp_neg_le` / 定理 `cardSupp_neg_le`

English:
theorem cardSupp_neg_le
  given: [NegZeroClass R] (x : R⟦Γ⟧)
  statement: (-x).cardSupp <= x.cardSupp
  proof: cardSupp_mono support_neg_subset ..

中文:
定理 cardSupp_neg_le
  条件: [NegZero类 R] (x : R⟦Γ⟧)
  结论: (-x).cardSupp <= x.cardSupp
  证明: cardSupp_mono support_neg_subset ..

Depends on / 依赖: cardSupp_mono, support_neg_subset
-/
theorem cardSupp_neg_le [NegZeroClass R] (x : R⟦Γ⟧) : (-x).cardSupp <= x.cardSupp :=
cardSupp_mono support_neg_subset ..

/--
theorem `cardSupp_add_le` / 定理 `cardSupp_add_le`

English:
theorem cardSupp_add_le
  given: [AddMonoid R] (x y : R⟦Γ⟧)
  statement: (x + y).cardSupp <= x.cardSupp + y.cardSupp
  proof: (mk_le_mk_of_subset (support_add_subset ..)).trans (mk_union_le ..)

@[simp]

中文:
定理 cardSupp_add_le
  条件: [加法幺半群 R] (x y : R⟦Γ⟧)
  结论: (x + y).cardSupp <= x.cardSupp + y.cardSupp
  证明: (mk_le_mk_of_subset (support_add_subset ..)).trans (mk_union_le ..)

@[simp]

Depends on / 依赖: mk_le_mk_of_subset, mk_union_le, support_add_subset
-/
theorem cardSupp_add_le [AddMonoid R] (x y : R⟦Γ⟧) : (x + y).cardSupp <= x.cardSupp + y.cardSupp :=
  (mk_le_mk_of_subset (support_add_subset ..)).trans (mk_union_le ..)

@[simp]
/--
theorem `cardSupp_neg` / 定理 `cardSupp_neg`

English:
theorem cardSupp_neg
  given: [AddGroup R] (x : R⟦Γ⟧)
  statement: (-x).cardSupp = x.cardSupp
  proof: cardSupp_congr support_neg

中文:
定理 cardSupp_neg
  条件: [加法群 R] (x : R⟦Γ⟧)
  结论: (-x).cardSupp = x.cardSupp
  证明: cardSupp_congr support_neg

Depends on / 依赖: cardSupp_congr, support_neg
-/
theorem cardSupp_neg [AddGroup R] (x : R⟦Γ⟧) : (-x).cardSupp = x.cardSupp :=
  cardSupp_congr support_neg

/--
theorem `cardSupp_sub_le` / 定理 `cardSupp_sub_le`

English:
theorem cardSupp_sub_le
  given: [AddGroup R] (x y : R⟦Γ⟧)
  statement: (x - y).cardSupp <= x.cardSupp + y.cardSupp
  proof: (mk_le_mk_of_subset (support_sub_subset ..)).trans (mk_union_le ..)

中文:
定理 cardSupp_sub_le
  条件: [加法群 R] (x y : R⟦Γ⟧)
  结论: (x - y).cardSupp <= x.cardSupp + y.cardSupp
  证明: (mk_le_mk_of_subset (support_sub_subset ..)).trans (mk_union_le ..)

Depends on / 依赖: mk_le_mk_of_subset, mk_union_le, support_sub_subset
-/
theorem cardSupp_sub_le [AddGroup R] (x y : R⟦Γ⟧) : (x - y).cardSupp <= x.cardSupp + y.cardSupp :=
  (mk_le_mk_of_subset (support_sub_subset ..)).trans (mk_union_le ..)

/--
theorem `cardSupp_mul_le` / 定理 `cardSupp_mul_le`

English:
theorem cardSupp_mul_le
  statement: [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
  proof: (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le

中文:
定理 cardSupp_mul_le
  结论: [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ] [非幺非结合半环 R]
  证明: (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le

Depends on / 依赖: mk_add_le, mk_le_mk_of_subset, support_mul_subset
-/
theorem cardSupp_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
    (x y : R⟦Γ⟧) : (x * y).cardSupp <= x.cardSupp * y.cardSupp :=
  (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le

/--
theorem `cardSupp_single_mul_le` / 定理 `cardSupp_single_mul_le`

English:
theorem cardSupp_single_mul_le
  statement: [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  proof: by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_left (cardSupp_single_le ..) _)

中文:
定理 cardSupp_single_mul_le
  结论: [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ]
  证明: by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_left (cardSupp_single_le ..) _)

Depends on / 依赖: cardSupp_mul_le, cardSupp_single_le, mul_le_mul_left
-/
theorem cardSupp_single_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) :
    (single a r * x).cardSupp <= x.cardSupp := by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_left (cardSupp_single_le ..) _)

/--
theorem `cardSupp_mul_single_le` / 定理 `cardSupp_mul_single_le`

English:
theorem cardSupp_mul_single_le
  statement: [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  proof: by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_right (cardSupp_single_le ..) _)

中文:
定理 cardSupp_mul_single_le
  结论: [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ]
  证明: by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_right (cardSupp_single_le ..) _)

Depends on / 依赖: cardSupp_mul_le, cardSupp_single_le, mul_le_mul_right
-/
theorem cardSupp_mul_single_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) :
    (x * single a r).cardSupp <= x.cardSupp := by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_right (cardSupp_single_le ..) _)

/--
theorem `cardSupp_pow_le` / 定理 `cardSupp_pow_le`

English:
theorem cardSupp_pow_le
  statement: [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
  proof: by
  induction n with
  | zero => simp
  | succ n IH =>
simpa [pow_succ] using (cardSupp_mul_le ..).trans mul_le_mul_left IH _

中文:
定理 cardSupp_pow_le
  结论: [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ] [半环 R]
  证明: by
  induction n with
  | zero => simp
  | succ n IH =>
simpa [pow_succ] using (cardSupp_mul_le ..).trans mul_le_mul_left IH _

Depends on / 依赖: cardSupp_mul_le, mul_le_mul_left, pow_succ
-/
theorem cardSupp_pow_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
    (x : R⟦Γ⟧) (n : Nat) : (x ^ n).cardSupp <= x.cardSupp ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
simpa [pow_succ] using (cardSupp_mul_le ..).trans mul_le_mul_left IH _

/--
theorem `cardSupp_hsum_le` / 定理 `cardSupp_hsum_le`

English:
theorem cardSupp_hsum_le
  given: [AddCommMonoid R] (s : SummableFamily Γ R α)
  proof: (lift_le.2 <| mk_le_mk_of_subset (SummableFamily.support_hsum_subset ..)).trans
    mk_iUnion_le_sum_mk_lift

中文:
定理 cardSupp_hsum_le
  条件: [加法交换幺半群 R] (s : SummableFamily Γ R α)
  证明: (lift_le.2 <| mk_le_mk_of_subset (SummableFamily.support_hsum_subset ..)).trans
    mk_iUnion_le_sum_mk_lift

Depends on / 依赖: SummableFamily, SummableFamily.support_hsum_subset, lift_le, mk_iUnion_le_sum_mk_lift, mk_le_mk_of_subset, support_hsum_subset
-/
theorem cardSupp_hsum_le [AddCommMonoid R] (s : SummableFamily Γ R α) :
    lift s.hsum.cardSupp <= sum fun a => (s a).cardSupp :=
  (lift_le.2 <| mk_le_mk_of_subset (SummableFamily.support_hsum_subset ..)).trans
    mk_iUnion_le_sum_mk_lift

end PartialOrder

section LinearOrder
variable [LinearOrder Γ]

/--
theorem `cardSupp_hsum_powers_le` / 定理 `cardSupp_hsum_powers_le`

English:
theorem cardSupp_hsum_powers_le
  statement: [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  proof: by
  grw [← lift_uzero (cardSupp _), ← sum_pow_le_max_aleph0, cardSupp_hsum_le, sum_le_sum]
  intro i
  rw [SummableFamily.powers_toFun]
  split_ifs
  · exact cardSupp_pow_le ..
  · cases i <;> simp

中文:
定理 cardSupp_hsum_powers_le
  结论: [加法交换幺半群 Γ] [是OrderedCancelAdd幺半群 Γ] [交换环 R]
  证明: by
  grw [← lift_uzero (cardSupp _), ← sum_pow_le_max_aleph0, cardSupp_hsum_le, sum_le_sum]
  intro i
  rw [SummableFamily.powers_toFun]
  split_ifs
  · exact cardSupp_pow_le ..
  · cases i <;> simp

Depends on / 依赖: SummableFamily, SummableFamily.powers_toFun, cardSupp, cardSupp_hsum_le, cardSupp_pow_le, lift_uzero, powers_toFun, split_ifs, sum_le_sum, sum_pow_le_max_aleph0
-/
theorem cardSupp_hsum_powers_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
    (x : R⟦Γ⟧) : (SummableFamily.powers x).hsum.cardSupp <= max ℵ₀ x.cardSupp := by
  grw [← lift_uzero (cardSupp _), ← sum_pow_le_max_aleph0, cardSupp_hsum_le, sum_le_sum]
  intro i
  rw [SummableFamily.powers_toFun]
  split_ifs
  · exact cardSupp_pow_le ..
  · cases i <;> simp

/--
theorem `cardSupp_inv_le` / 定理 `cardSupp_inv_le`

English:
theorem cardSupp_inv_le
  given: [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x : R⟦Γ⟧)
  proof: by
  obtain rfl | hx := eq_or_ne x 0; · simp
.trans apply (cardSupp_single_mul_le ..).trans (cardSupp_hsum_powers_le ..)
  gcongr
refine (cardSupp_single_mul_le _ (-x.order) x.leadingCoeff⁻¹).trans' cardSupp_mono fun _ => ?_
  aesop (add simp [coeff_single_mul])

中文:
定理 cardSupp_inv_le
  条件: [加法交换群 Γ] [是OrderedAdd幺半群 Γ] [域 R] (x : R⟦Γ⟧)
  证明: by
  obtain rfl | hx := eq_or_ne x 0; · simp
.trans apply (cardSupp_single_mul_le ..).trans (cardSupp_hsum_powers_le ..)
  gcongr
refine (cardSupp_single_mul_le _ (-x.order) x.leadingCoeff⁻¹).trans' cardSupp_mono fun _ => ?_
  aesop (add simp [coeff_single_mul])

Depends on / 依赖: cardSupp_hsum_powers_le, cardSupp_mono, cardSupp_single_mul_le, coeff_single_mul, eq_or_ne, leadingCoeff, x.leadingCoeff, x.order
-/
theorem cardSupp_inv_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x : R⟦Γ⟧) :
    x⁻¹.cardSupp <= max ℵ₀ x.cardSupp := by
  obtain rfl | hx := eq_or_ne x 0; · simp
.trans apply (cardSupp_single_mul_le ..).trans (cardSupp_hsum_powers_le ..)
  gcongr
refine (cardSupp_single_mul_le _ (-x.order) x.leadingCoeff⁻¹).trans' cardSupp_mono fun _ => ?_
  aesop (add simp [coeff_single_mul])

/--
theorem `cardSupp_div_le` / 定理 `cardSupp_div_le`

English:
theorem cardSupp_div_le
  given: [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x y : R⟦Γ⟧)
  proof: (cardSupp_mul_le ..).trans mul_le_mul_right (cardSupp_inv_le y) _

中文:
定理 cardSupp_div_le
  条件: [加法交换群 Γ] [是OrderedAdd幺半群 Γ] [域 R] (x y : R⟦Γ⟧)
  证明: (cardSupp_mul_le ..).trans mul_le_mul_right (cardSupp_inv_le y) _

Depends on / 依赖: cardSupp_inv_le, cardSupp_mul_le, mul_le_mul_right
-/
theorem cardSupp_div_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x y : R⟦Γ⟧) :
    (x / y).cardSupp <= x.cardSupp * max ℵ₀ y.cardSupp :=
(cardSupp_mul_le ..).trans mul_le_mul_right (cardSupp_inv_le y) _

end LinearOrder

/-! ### Substructures -/

variable (κ : Cardinal)

section AddMonoid
variable [PartialOrder Γ] [AddMonoid R] [hκ : Fact (ℵ₀ <= κ)]

variable (Γ R) in
/-- The `κ`-bounded submonoid of Hahn series with less than `κ` terms. -/
@[simps!]
/--
Definition of `cardSuppLTAddSubmonoid` / `cardSuppLTAddSubmonoid` 的定义

English:
definition cardSuppLTAddSubmonoid
  signature: : AddSubmonoid R⟦Γ⟧ where
  body: {x | x.cardSupp < κ}
  zero_mem' := by simpa using aleph0_pos.trans_le hκ.out
add_mem' hx hy := (cardSupp_add_le ..).trans_lt add_lt_of_lt hκ.out hx hy

@[simp]

中文:
定义 cardSuppLTAddSubmonoid
  签名: : 加法子幺半群 R⟦Γ⟧ where
  定义体: {x | x.cardSupp < κ}
  zero_mem' := by simpa using aleph0_pos.trans_le hκ.out
add_mem' hx hy := (cardSupp_add_le ..).trans_lt add_lt_of_lt hκ.out hx hy

@[simp]

Depends on / 依赖: cardSupp, x.cardSupp
-/
def cardSuppLTAddSubmonoid : AddSubmonoid R⟦Γ⟧ where
  carrier := {x | x.cardSupp < κ}
  zero_mem' := by simpa using aleph0_pos.trans_le hκ.out
add_mem' hx hy := (cardSupp_add_le ..).trans_lt add_lt_of_lt hκ.out hx hy

@[simp]
/--
theorem `mem_cardSuppLTAddSubmonoid` / 定理 `mem_cardSuppLTAddSubmonoid`

English:
theorem mem_cardSuppLTAddSubmonoid
  given: {x : R⟦Γ⟧}
  statement: x in cardSuppLTAddSubmonoid Γ R κ ↔ x.cardSupp < κ
  proof: .rfl

中文:
定理 mem_cardSuppLTAddSubmonoid
  条件: {x : R⟦Γ⟧}
  结论: x in cardSuppLTAddSubmonoid Γ R κ ↔ x.cardSupp < κ
  证明: .rfl

Depends on / 依赖: CSLift, CSLift.lift
-/
theorem mem_cardSuppLTAddSubmonoid {x : R⟦Γ⟧} : x in cardSuppLTAddSubmonoid Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end AddMonoid

section AddGroup
variable [PartialOrder Γ] [AddGroup R] [hκ : Fact (ℵ₀ <= κ)]

variable (Γ R) in
/-- The `κ`-bounded subgroup of Hahn series with less than `κ` terms. -/
@[simps!]
/--
Definition of `cardSuppLTAddSubgroup` / `cardSuppLTAddSubgroup` 的定义

English:
definition cardSuppLTAddSubgroup
  signature: : AddSubgroup R⟦Γ⟧ where
  body: by simp
  __ := cardSuppLTAddSubmonoid Γ R κ

@[simp]

中文:
定义 cardSuppLTAddSubgroup
  签名: : 加法子群 R⟦Γ⟧ where
  定义体: by simp
  __ := cardSuppLTAddSubmonoid Γ R κ

@[simp]

Depends on / 依赖: CSLift, CSLift.lift, cardSuppLTAddSubmonoid
-/
def cardSuppLTAddSubgroup : AddSubgroup R⟦Γ⟧ where
  neg_mem' := by simp
  __ := cardSuppLTAddSubmonoid Γ R κ

@[simp]
/--
theorem `mem_cardSuppLTAddSubgroup` / 定理 `mem_cardSuppLTAddSubgroup`

English:
theorem mem_cardSuppLTAddSubgroup
  given: {x : R⟦Γ⟧}
  statement: x in cardSuppLTAddSubgroup Γ R κ ↔ x.cardSupp < κ
  proof: .rfl

中文:
定理 mem_cardSuppLTAddSubgroup
  条件: {x : R⟦Γ⟧}
  结论: x in cardSuppLTAddSubgroup Γ R κ ↔ x.cardSupp < κ
  证明: .rfl

Depends on / 依赖: CSLift, CSLift.lift
-/
theorem mem_cardSuppLTAddSubgroup {x : R⟦Γ⟧} : x in cardSuppLTAddSubgroup Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end AddGroup

section Subring
variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Ring R]
  [hκ : Fact (ℵ₀ <= κ)]

variable (Γ R) in
/--
Definition of `cardSuppLTSubring` / `cardSuppLTSubring` 的定义

English:
definition cardSuppLTSubring
  signature: : Subring R⟦Γ⟧ where
  body: cardSupp_one_le.trans_lt one_lt_aleph0.trans_le hκ.out
mul_mem' hx hy := (cardSupp_mul_le ..).trans_lt mul_lt_of_lt hκ.out hx hy
  __ := cardSuppLTAddSubgroup Γ R κ

@[simp]

中文:
定义 cardSuppLTSubring
  签名: : 子环 R⟦Γ⟧ where
  定义体: cardSupp_one_le.trans_lt one_lt_aleph0.trans_le hκ.out
mul_mem' hx hy := (cardSupp_mul_le ..).trans_lt mul_lt_of_lt hκ.out hx hy
  __ := cardSuppLTAddSubgroup Γ R κ

@[simp]

Depends on / 依赖: cardSupp_one_le, cardSupp_one_le.trans_lt, one_lt_aleph0, one_lt_aleph0.trans_le, trans_le, trans_lt
-/
def cardSuppLTSubring : Subring R⟦Γ⟧ where
one_mem' := cardSupp_one_le.trans_lt one_lt_aleph0.trans_le hκ.out
mul_mem' hx hy := (cardSupp_mul_le ..).trans_lt mul_lt_of_lt hκ.out hx hy
  __ := cardSuppLTAddSubgroup Γ R κ

@[simp]
/--
theorem `mem_cardSuppLTSubring` / 定理 `mem_cardSuppLTSubring`

English:
theorem mem_cardSuppLTSubring
  given: {x : R⟦Γ⟧}
  statement: x in cardSuppLTSubring Γ R κ ↔ x.cardSupp < κ
  proof: .rfl

中文:
定理 mem_cardSuppLTSubring
  条件: {x : R⟦Γ⟧}
  结论: x in cardSuppLTSubring Γ R κ ↔ x.cardSupp < κ
  证明: .rfl
-/
theorem mem_cardSuppLTSubring {x : R⟦Γ⟧} : x in cardSuppLTSubring Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end Subring

section Subfield
variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] [hκ : Fact (ℵ₀ < κ)]

variable (Γ R) in
/-- The `κ`-bounded subfield of Hahn series with less than `κ` terms. -/
@[simps!]
/--
Definition of `cardSuppLTSubfield` / `cardSuppLTSubfield` 的定义

English:
definition cardSuppLTSubfield
  signature: : Subfield R⟦Γ⟧ where
  body: (cardSupp_inv_le _).trans_lt by simpa [hκ.out]
  __ := have : Fact (ℵ₀ <= κ) := ⟨hκ.out.le⟩; cardSuppLTSubring Γ R κ

@[simp]

中文:
定义 cardSuppLTSubfield
  签名: : 子域 R⟦Γ⟧ where
  定义体: (cardSupp_inv_le _).trans_lt by simpa [hκ.out]
  __ := have : Fact (ℵ₀ <= κ) := ⟨hκ.out.le⟩; cardSuppLTSubring Γ R κ

@[simp]

Depends on / 依赖: cardSupp_inv_le, trans_lt
-/
def cardSuppLTSubfield : Subfield R⟦Γ⟧ where
inv_mem' _ _ := (cardSupp_inv_le _).trans_lt by simpa [hκ.out]
  __ := have : Fact (ℵ₀ <= κ) := ⟨hκ.out.le⟩; cardSuppLTSubring Γ R κ

@[simp]
/--
theorem `mem_cardSuppLTSubfield` / 定理 `mem_cardSuppLTSubfield`

English:
theorem mem_cardSuppLTSubfield
  given: {x : R⟦Γ⟧}
  statement: x in cardSuppLTSubfield Γ R κ ↔ x.cardSupp < κ
  proof: .rfl

中文:
定理 mem_cardSuppLTSubfield
  条件: {x : R⟦Γ⟧}
  结论: x in cardSuppLTSubfield Γ R κ ↔ x.cardSupp < κ
  证明: .rfl
-/
theorem mem_cardSuppLTSubfield {x : R⟦Γ⟧} : x in cardSuppLTSubfield Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end Subfield
end HahnSeries
