/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Disjointed
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Big operators indexed by intervals

This file proves lemmas about `∏ x ∈ Ixx a b, f x` and `∑ x ∈ Ixx a b, f x`.
-/

public section

open Order

variable {α M : Type*} [CommMonoid M] {f : α -> M} {a b : α}

namespace Finset
section PartialOrder
variable [PartialOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
/--
lemma `mul_prod_Ico_eq_prod_Icc` / 引理 `mul_prod_Ico_eq_prod_Icc`

English:
lemma mul_prod_Ico_eq_prod_Icc
  given: (h : a <= b)
  statement: f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x
  proof: by
  rw [Icc_eq_cons_Ico h]; rw [prod_cons]

@[to_additive]

中文:
引理 mul_prod_Ico_eq_prod_Icc
  条件: (h : a <= b)
  结论: f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x
  证明: by
  rw [Icc_eq_cons_Ico h]; rw [prod_cons]

@[to_additive]

Depends on / 依赖: Icc_eq_cons_Ico, prod_cons
-/
lemma mul_prod_Ico_eq_prod_Icc (h : a <= b) : f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x := by
  rw [Icc_eq_cons_Ico h]; rw [prod_cons]

@[to_additive]
/--
lemma `prod_Ico_mul_eq_prod_Icc` / 引理 `prod_Ico_mul_eq_prod_Icc`

English:
lemma prod_Ico_mul_eq_prod_Icc
  given: (h : a <= b)
  statement: (∏ x in Ico a b, f x) * f b = ∏ x in Icc a b, f x
  proof: by
  rw [mul_comm]; rw [mul_prod_Ico_eq_prod_Icc h]

@[to_additive]

中文:
引理 prod_Ico_mul_eq_prod_Icc
  条件: (h : a <= b)
  结论: (∏ x in Ico a b, f x) * f b = ∏ x in Icc a b, f x
  证明: by
  rw [mul_comm]; rw [mul_prod_Ico_eq_prod_Icc h]

@[to_additive]

Depends on / 依赖: mul_comm, mul_prod_Ico_eq_prod_Icc
-/
lemma prod_Ico_mul_eq_prod_Icc (h : a <= b) : (∏ x in Ico a b, f x) * f b = ∏ x in Icc a b, f x := by
  rw [mul_comm]; rw [mul_prod_Ico_eq_prod_Icc h]

@[to_additive]
/--
lemma `mul_prod_Ioc_eq_prod_Icc` / 引理 `mul_prod_Ioc_eq_prod_Icc`

English:
lemma mul_prod_Ioc_eq_prod_Icc
  given: (h : a <= b)
  statement: f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x
  proof: by
  rw [Icc_eq_cons_Ioc h]; rw [prod_cons]

@[to_additive]

中文:
引理 mul_prod_Ioc_eq_prod_Icc
  条件: (h : a <= b)
  结论: f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x
  证明: by
  rw [Icc_eq_cons_Ioc h]; rw [prod_cons]

@[to_additive]

Depends on / 依赖: Icc_eq_cons_Ioc, prod_cons
-/
lemma mul_prod_Ioc_eq_prod_Icc (h : a <= b) : f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h]; rw [prod_cons]

@[to_additive]
/--
lemma `prod_Ioc_mul_eq_prod_Icc` / 引理 `prod_Ioc_mul_eq_prod_Icc`

English:
lemma prod_Ioc_mul_eq_prod_Icc
  given: (h : a <= b)
  statement: (∏ x in Ioc a b, f x) * f a = ∏ x in Icc a b, f x
  proof: by
  rw [mul_comm]; rw [mul_prod_Ioc_eq_prod_Icc h]

@[to_additive]

中文:
引理 prod_Ioc_mul_eq_prod_Icc
  条件: (h : a <= b)
  结论: (∏ x in Ioc a b, f x) * f a = ∏ x in Icc a b, f x
  证明: by
  rw [mul_comm]; rw [mul_prod_Ioc_eq_prod_Icc h]

@[to_additive]

Depends on / 依赖: mul_comm, mul_prod_Ioc_eq_prod_Icc
-/
lemma prod_Ioc_mul_eq_prod_Icc (h : a <= b) : (∏ x in Ioc a b, f x) * f a = ∏ x in Icc a b, f x := by
  rw [mul_comm]; rw [mul_prod_Ioc_eq_prod_Icc h]

@[to_additive]
/--
lemma `mul_prod_Ioo_eq_prod_Ico` / 引理 `mul_prod_Ioo_eq_prod_Ico`

English:
lemma mul_prod_Ioo_eq_prod_Ico
  given: (h : a < b)
  statement: f a * ∏ x in Ioo a b, f x = ∏ x in Ico a b, f x
  proof: by
  rw [Ico_eq_cons_Ioo h]; rw [prod_cons]

@[to_additive]

中文:
引理 mul_prod_Ioo_eq_prod_Ico
  条件: (h : a < b)
  结论: f a * ∏ x in Ioo a b, f x = ∏ x in Ico a b, f x
  证明: by
  rw [Ico_eq_cons_Ioo h]; rw [prod_cons]

@[to_additive]

Depends on / 依赖: Ico_eq_cons_Ioo, prod_cons
-/
lemma mul_prod_Ioo_eq_prod_Ico (h : a < b) : f a * ∏ x in Ioo a b, f x = ∏ x in Ico a b, f x := by
  rw [Ico_eq_cons_Ioo h]; rw [prod_cons]

@[to_additive]
/--
lemma `prod_Ioo_mul_eq_prod_Ico` / 引理 `prod_Ioo_mul_eq_prod_Ico`

English:
lemma prod_Ioo_mul_eq_prod_Ico
  given: (h : a < b)
  statement: (∏ x in Ioo a b, f x) * f a = ∏ x in Ico a b, f x
  proof: by
  rw [mul_comm]; rw [mul_prod_Ioo_eq_prod_Ico h]

@[to_additive]

中文:
引理 prod_Ioo_mul_eq_prod_Ico
  条件: (h : a < b)
  结论: (∏ x in Ioo a b, f x) * f a = ∏ x in Ico a b, f x
  证明: by
  rw [mul_comm]; rw [mul_prod_Ioo_eq_prod_Ico h]

@[to_additive]

Depends on / 依赖: mul_comm, mul_prod_Ioo_eq_prod_Ico
-/
lemma prod_Ioo_mul_eq_prod_Ico (h : a < b) : (∏ x in Ioo a b, f x) * f a = ∏ x in Ico a b, f x := by
  rw [mul_comm]; rw [mul_prod_Ioo_eq_prod_Ico h]

@[to_additive]
/--
lemma `mul_prod_Ioo_eq_prod_Ioc` / 引理 `mul_prod_Ioo_eq_prod_Ioc`

English:
lemma mul_prod_Ioo_eq_prod_Ioc
  given: (h : a < b)
  statement: f b * ∏ x in Ioo a b, f x = ∏ x in Ioc a b, f x
  proof: by
  rw [Ioc_eq_cons_Ioo h]; rw [prod_cons]

@[to_additive]

中文:
引理 mul_prod_Ioo_eq_prod_Ioc
  条件: (h : a < b)
  结论: f b * ∏ x in Ioo a b, f x = ∏ x in Ioc a b, f x
  证明: by
  rw [Ioc_eq_cons_Ioo h]; rw [prod_cons]

@[to_additive]

Depends on / 依赖: Ioc_eq_cons_Ioo, prod_cons
-/
lemma mul_prod_Ioo_eq_prod_Ioc (h : a < b) : f b * ∏ x in Ioo a b, f x = ∏ x in Ioc a b, f x := by
  rw [Ioc_eq_cons_Ioo h]; rw [prod_cons]

@[to_additive]
/--
lemma `prod_Ioo_mul_eq_prod_Ioc` / 引理 `prod_Ioo_mul_eq_prod_Ioc`

English:
lemma prod_Ioo_mul_eq_prod_Ioc
  given: (h : a < b)
  statement: (∏ x in Ioo a b, f x) * f b = ∏ x in Ioc a b, f x
  proof: by
  rw [mul_comm]; rw [mul_prod_Ioo_eq_prod_Ioc h]

中文:
引理 prod_Ioo_mul_eq_prod_Ioc
  条件: (h : a < b)
  结论: (∏ x in Ioo a b, f x) * f b = ∏ x in Ioc a b, f x
  证明: by
  rw [mul_comm]; rw [mul_prod_Ioo_eq_prod_Ioc h]

Depends on / 依赖: mul_comm, mul_prod_Ioo_eq_prod_Ioc
-/
lemma prod_Ioo_mul_eq_prod_Ioc (h : a < b) : (∏ x in Ioo a b, f x) * f b = ∏ x in Ioc a b, f x := by
  rw [mul_comm]; rw [mul_prod_Ioo_eq_prod_Ioc h]

variable [AddMonoidWithOne α] [SuccAddOrder α]

@[to_additive]
/--
theorem `prod_eq_prod_Ico_succ_bot` / 定理 `prod_eq_prod_Ico_succ_bot`

English:
theorem prod_eq_prod_Ico_succ_bot
  given: {a b : Nat} (hab : a < b) (f : Nat -> M)
  proof: by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha]; rw [Finset.insert_Ico_add_one_left_eq_Ico hab]

中文:
定理 prod_eq_prod_Ico_succ_bot
  条件: {a b : 自然数} (hab : a < b) (f : 自然数 -> M)
  证明: by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha]; rw [Finset.insert_Ico_add_one_left_eq_Ico hab]

Depends on / 依赖: Finset, Finset.insert_Ico_add_one_left_eq_Ico, insert_Ico_add_one_left_eq_Ico, prod_insert
-/
theorem prod_eq_prod_Ico_succ_bot {a b : Nat} (hab : a < b) (f : Nat -> M) :
    ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha]; rw [Finset.insert_Ico_add_one_left_eq_Ico hab]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
/--
lemma `mul_prod_Ioi_eq_prod_Ici` / 引理 `mul_prod_Ioi_eq_prod_Ici`

English:
lemma mul_prod_Ioi_eq_prod_Ici
  given: (a : α)
  statement: f a * ∏ x in Ioi a, f x = ∏ x in Ici a, f x
  proof: by
  rw [Ici_eq_cons_Ioi]; rw [prod_cons]

@[to_additive]

中文:
引理 mul_prod_Ioi_eq_prod_Ici
  条件: (a : α)
  结论: f a * ∏ x in Ioi a, f x = ∏ x in Ici a, f x
  证明: by
  rw [Ici_eq_cons_Ioi]; rw [prod_cons]

@[to_additive]

Depends on / 依赖: Ici_eq_cons_Ioi, prod_cons
-/
lemma mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x in Ioi a, f x = ∏ x in Ici a, f x := by
  rw [Ici_eq_cons_Ioi]; rw [prod_cons]

@[to_additive]
/--
lemma `prod_Ioi_mul_eq_prod_Ici` / 引理 `prod_Ioi_mul_eq_prod_Ici`

English:
lemma prod_Ioi_mul_eq_prod_Ici
  given: (a : α)
  statement: (∏ x in Ioi a, f x) * f a = ∏ x in Ici a, f x
  proof: by
  rw [mul_comm]; rw [mul_prod_Ioi_eq_prod_Ici]

中文:
引理 prod_Ioi_mul_eq_prod_Ici
  条件: (a : α)
  结论: (∏ x in Ioi a, f x) * f a = ∏ x in Ici a, f x
  证明: by
  rw [mul_comm]; rw [mul_prod_Ioi_eq_prod_Ici]

Depends on / 依赖: mul_comm, mul_prod_Ioi_eq_prod_Ici
-/
lemma prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x in Ioi a, f x) * f a = ∏ x in Ici a, f x := by
  rw [mul_comm]; rw [mul_prod_Ioi_eq_prod_Ici]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
/--
lemma `mul_prod_Iio_eq_prod_Iic` / 引理 `mul_prod_Iio_eq_prod_Iic`

English:
lemma mul_prod_Iio_eq_prod_Iic
  given: (a : α)
  statement: f a * ∏ x in Iio a, f x = ∏ x in Iic a, f x
  proof: by
  rw [Iic_eq_cons_Iio]; rw [prod_cons]

@[to_additive]

中文:
引理 mul_prod_Iio_eq_prod_Iic
  条件: (a : α)
  结论: f a * ∏ x in Iio a, f x = ∏ x in Iic a, f x
  证明: by
  rw [Iic_eq_cons_Iio]; rw [prod_cons]

@[to_additive]

Depends on / 依赖: Iic_eq_cons_Iio, prod_cons
-/
lemma mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x in Iio a, f x = ∏ x in Iic a, f x := by
  rw [Iic_eq_cons_Iio]; rw [prod_cons]

@[to_additive]
/--
lemma `prod_Iio_mul_eq_prod_Iic` / 引理 `prod_Iio_mul_eq_prod_Iic`

English:
lemma prod_Iio_mul_eq_prod_Iic
  given: (a : α)
  statement: (∏ x in Iio a, f x) * f a = ∏ x in Iic a, f x
  proof: by
  rw [mul_comm]; rw [mul_prod_Iio_eq_prod_Iic]

中文:
引理 prod_Iio_mul_eq_prod_Iic
  条件: (a : α)
  结论: (∏ x in Iio a, f x) * f a = ∏ x in Iic a, f x
  证明: by
  rw [mul_comm]; rw [mul_prod_Iio_eq_prod_Iic]

Depends on / 依赖: mul_comm, mul_prod_Iio_eq_prod_Iic
-/
lemma prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x in Iio a, f x) * f a = ∏ x in Iic a, f x := by
  rw [mul_comm]; rw [mul_prod_Iio_eq_prod_Iic]

end LocallyFiniteOrderBot

end PartialOrder

section LinearOrder
variable [LinearOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α] [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]

@[to_additive (dont_translate := α) sum_Ico_add_eq_sum_Ico_add_one]
/--
lemma `prod_Ico_mul_eq_prod_Ico_add_one` / 引理 `prod_Ico_mul_eq_prod_Ico_add_one`

English:
lemma prod_Ico_mul_eq_prod_Ico_add_one
  given: (hab : a <= b) (f : α -> M)
  proof: by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab]; rw [prod_insert right_notMem_Ico]; rw [mul_comm]

中文:
引理 prod_Ico_mul_eq_prod_Ico_add_one
  条件: (hab : a <= b) (f : α -> M)
  证明: by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab]; rw [prod_insert right_notMem_Ico]; rw [mul_comm]

Depends on / 依赖: Finset, Finset.insert_Ico_right_eq_Ico_add_one, insert_Ico_right_eq_Ico_add_one, mul_comm, prod_insert, right_notMem_Ico
-/
lemma prod_Ico_mul_eq_prod_Ico_add_one (hab : a <= b) (f : α -> M) :
    (∏ x in Ico a b, f x) * f b = ∏ x in Ico a (b + 1), f x := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab]; rw [prod_insert right_notMem_Ico]; rw [mul_comm]

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive (dont_translate := α)]
/--
lemma `prod_Iio_add_one_comm` / 引理 `prod_Iio_add_one_comm`

English:
lemma prod_Iio_add_one_comm
  statement: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: by
  simp [Iio_add_one_eq_Iic, ← Iio_insert, Finset.prod_insert]

@[to_additive (dont_translate := α) (attr := simp)]

中文:
引理 prod_Iio_add_one_comm
  结论: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: by
  simp [Iio_add_one_eq_Iic, ← Iio_insert, Finset.prod_insert]

@[to_additive (dont_translate := α) (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_insert, Iio_add_one_eq_Iic, Iio_insert, prod_insert
-/
lemma prod_Iio_add_one_comm [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α -> M) : ∏ i < a + 1, f i = f a * (∏ i < a, f i) := by
  simp [Iio_add_one_eq_Iic, ← Iio_insert, Finset.prod_insert]

@[to_additive (dont_translate := α) (attr := simp)]
/--
lemma `prod_Iio_add_one` / 引理 `prod_Iio_add_one`

English:
lemma prod_Iio_add_one
  statement: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: by
  simp_rw [prod_Iio_add_one_comm, mul_comm]

@[to_additive (dont_translate := α)]

中文:
引理 prod_Iio_add_one
  结论: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: by
  simp_rw [prod_Iio_add_one_comm, mul_comm]

@[to_additive (dont_translate := α)]

Depends on / 依赖: mul_comm, prod_Iio_add_one_comm, simp_rw
-/
lemma prod_Iio_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α -> M) : ∏ i < a + 1, f i = (∏ i < a, f i) * f a := by
  simp_rw [prod_Iio_add_one_comm, mul_comm]

@[to_additive (dont_translate := α)]
/--
lemma `prod_Iic_add_one_comm` / 引理 `prod_Iic_add_one_comm`

English:
lemma prod_Iic_add_one_comm
  statement: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: by
  simp only [← Iio_insert, mem_Iio, lt_self_iff_false, not_false_eq_true, prod_insert,
    prod_Iio_add_one_comm]

@[to_additive (dont_translate := α) (attr := simp)]

中文:
引理 prod_Iic_add_one_comm
  结论: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: by
  simp only [← Iio_insert, mem_Iio, lt_self_iff_false, not_false_eq_true, prod_insert,
    prod_Iio_add_one_comm]

@[to_additive (dont_translate := α) (attr := simp)]

Depends on / 依赖: Iio_insert, lt_self_iff_false, mem_Iio, not_false_eq_true, prod_Iio_add_one_comm, prod_insert
-/
lemma prod_Iic_add_one_comm [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α -> M) : ∏ i <= a + 1, f i = f (a + 1) * (∏ i <= a, f i) := by
  simp only [← Iio_insert, mem_Iio, lt_self_iff_false, not_false_eq_true, prod_insert,
    prod_Iio_add_one_comm]

@[to_additive (dont_translate := α) (attr := simp)]
/--
lemma `prod_Iic_add_one` / 引理 `prod_Iic_add_one`

English:
lemma prod_Iic_add_one
  statement: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  proof: by
  simp_rw [prod_Iic_add_one_comm, mul_comm]

中文:
引理 prod_Iic_add_one
  结论: [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
  证明: by
  simp_rw [prod_Iic_add_one_comm, mul_comm]

Depends on / 依赖: mul_comm, prod_Iic_add_one_comm, simp_rw
-/
lemma prod_Iic_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (a : α) (f : α -> M) : ∏ i <= a + 1, f i = (∏ i <= a, f i) * f (a + 1) := by
  simp_rw [prod_Iic_add_one_comm, mul_comm]

end LocallyFiniteOrderBot

section LocallyFiniteOrderTopBot
variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

@[to_additive]
/--
lemma `prod_prod_Ioi_mul_eq_prod_prod_off_diag` / 引理 `prod_prod_Ioi_mul_eq_prod_prod_off_diag`

English:
lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag
  given: (f : α -> α -> M)
  proof: by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma']; rw [prod_sigma']
  refine prod_nbij' (fun i => ⟨i.2, i.1⟩) (fun i => ⟨i.2, i.1⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

中文:
引理 prod_prod_Ioi_mul_eq_prod_prod_off_diag
  条件: (f : α -> α -> M)
  证明: by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma']; rw [prod_sigma']
  refine prod_nbij' (fun i => ⟨i.2, i.1⟩) (fun i => ⟨i.2, i.1⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

Depends on / 依赖: Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib, prod_nbij, prod_sigma, simp_rw
-/
lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag (f : α -> α -> M) :
    ∏ i, ∏ j in Ioi i, f j i * f i j = ∏ i, ∏ j in {i}ᶜ, f j i := by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma']; rw [prod_sigma']
  refine prod_nbij' (fun i => ⟨i.2, i.1⟩) (fun i => ⟨i.2, i.1⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

end LocallyFiniteOrderTopBot

end LinearOrder

set_option backward.isDefEq.respectTransparency false in
/-- Given a sequence of finite sets `s₀ ⊆ s₁ ⊆ s₂ ⋯`, the product of `gᵢ` over `i ∈ sₙ` is equal
to `∏_{i ∈ s₀} gᵢ` * `∏_{j < n, i ∈ sⱼ₊₁ \ sⱼ} gᵢ`. -/
@[to_additive /-- Given a sequence of finite sets `s₀ ⊆ s₁ ⊆ s₂ ⋯`, the sum of `gᵢ` over `i ∈ sₙ` is
equal to `∑_{i ∈ s₀} gᵢ` + `∑_{j < n, i ∈ sⱼ₊₁ \ sⱼ} gᵢ`.-/]
/--
lemma `prod_eq_prod_range_sdiff` / 引理 `prod_eq_prod_range_sdiff`

English:
lemma prod_eq_prod_range_sdiff
  proof: by
  conv_lhs => rw [← hs.partialSups_eq, ← disjiUnion_Iic_disjointed, Iic_eq_Icc,
    prod_disjiUnion, Nat.bot_eq_zero, ← Nat.range_succ_eq_Icc_zero, prod_range_succ', mul_comm]
  congrm (∏ x in ?_, g x) * ∏ k in range n, ∏ x in s (k + 1) \ ?_, g x
  · simp
  · change (Iic k).sup (s ∘ id) = s k
   

中文:
引理 prod_eq_prod_range_sdiff
  证明: by
  conv_lhs => rw [← hs.partialSups_eq, ← disjiUnion_Iic_disjointed, Iic_eq_Icc,
    prod_disjiUnion, Nat.bot_eq_zero, ← Nat.range_succ_eq_Icc_zero, prod_range_succ', mul_comm]
  congrm (∏ x in ?_, g x) * ∏ k in range n, ∏ x in s (k + 1) \ ?_, g x
  · simp
  · change (Iic k).sup (s ∘ id) = s k
   

Depends on / 依赖: Iic_eq_Icc, Nat.bot_eq_zero, Nat.range_succ_eq_Icc_zero, apply_sup_eq_sup_comp_of_nonempty, bot_eq_zero, congrm, conv_lhs, disjiUnion_Iic_disjointed, hs.partialSups_eq, mul_comm, nonempty_Iic, partialSups_eq, prod_disjiUnion, prod_range_succ, range_succ_eq_Icc_zero, sup_Iic
-/
lemma prod_eq_prod_range_sdiff
    {α β : Type*} [DecidableEq α] [CommMonoid β] (s : Nat -> Finset α) (hs : Monotone s)
    (g : α -> β) (n : Nat) :
    ∏ i in s n, g i = (∏ i in s 0, g i) * ∏ i in range n, ∏ j in s (i + 1) \ s i, g j := by
  conv_lhs => rw [← hs.partialSups_eq, ← disjiUnion_Iic_disjointed, Iic_eq_Icc,
    prod_disjiUnion, Nat.bot_eq_zero, ← Nat.range_succ_eq_Icc_zero, prod_range_succ', mul_comm]
  congrm (∏ x in ?_, g x) * ∏ k in range n, ∏ x in s (k + 1) \ ?_, g x
  · simp
  · change (Iic k).sup (s ∘ id) = s k
    rw [← apply_sup_eq_sup_comp_of_nonempty hs nonempty_Iic]; rw [sup_Iic]

end Finset
