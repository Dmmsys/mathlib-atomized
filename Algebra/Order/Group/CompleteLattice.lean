/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Distributivity of group operations over supremum/infimum
-/

public section

open Function Set

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι -> G}

section Right
variable [MulRightMono G]

@[to_additive]
/--
lemma `ciSup_mul` / 引理 `ciSup_mul`

English:
lemma ciSup_mul
  given: (hf : BddAbove (range f)) (a : G)
  statement: (⨆ i, f i) * a = ⨆ i, f i * a
  proof: (OrderIso.mulRight a).map_ciSup hf

@[to_additive]

中文:
引理 ciSup_mul
  条件: (hf : BddAbove (range f)) (a : G)
  结论: (⨆ i, f i) * a = ⨆ i, f i * a
  证明: (OrderIso.mulRight a).map_ciSup hf

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulRight, map_ciSup, mulRight
-/
lemma ciSup_mul (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_ciSup hf

@[to_additive]
/--
lemma `ciSup_div` / 引理 `ciSup_div`

English:
lemma ciSup_div
  given: (hf : BddAbove (range f)) (a : G)
  statement: (⨆ i, f i) / a = ⨆ i, f i / a
  proof: by
  simp only [div_eq_mul_inv, ciSup_mul hf]

@[to_additive]

中文:
引理 ciSup_div
  条件: (hf : BddAbove (range f)) (a : G)
  结论: (⨆ i, f i) / a = ⨆ i, f i / a
  证明: by
  simp only [div_eq_mul_inv, ciSup_mul hf]

@[to_additive]

Depends on / 依赖: ciSup_mul, div_eq_mul_inv
-/
lemma ciSup_div (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, ciSup_mul hf]

@[to_additive]
/--
lemma `ciInf_mul` / 引理 `ciInf_mul`

English:
lemma ciInf_mul
  given: (hf : BddBelow (range f)) (a : G)
  statement: (⨅ i, f i) * a = ⨅ i, f i * a
  proof: (OrderIso.mulRight a).map_ciInf hf

@[to_additive]

中文:
引理 ciInf_mul
  条件: (hf : BddBelow (range f)) (a : G)
  结论: (⨅ i, f i) * a = ⨅ i, f i * a
  证明: (OrderIso.mulRight a).map_ciInf hf

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulRight, map_ciInf, mulRight
-/
lemma ciInf_mul (hf : BddBelow (range f)) (a : G) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  (OrderIso.mulRight a).map_ciInf hf

@[to_additive]
/--
lemma `ciInf_div` / 引理 `ciInf_div`

English:
lemma ciInf_div
  given: (hf : BddBelow (range f)) (a : G)
  statement: (⨅ i, f i) / a = ⨅ i, f i / a
  proof: by
  simp only [div_eq_mul_inv, ciInf_mul hf]

中文:
引理 ciInf_div
  条件: (hf : BddBelow (range f)) (a : G)
  结论: (⨅ i, f i) / a = ⨅ i, f i / a
  证明: by
  simp only [div_eq_mul_inv, ciInf_mul hf]

Depends on / 依赖: ciInf_mul, div_eq_mul_inv
-/
lemma ciInf_div (hf : BddBelow (range f)) (a : G) : (⨅ i, f i) / a = ⨅ i, f i / a := by
  simp only [div_eq_mul_inv, ciInf_mul hf]

end Right

section Left
variable [MulLeftMono G]

@[to_additive]
/--
lemma `mul_ciSup` / 引理 `mul_ciSup`

English:
lemma mul_ciSup
  given: (hf : BddAbove (range f)) (a : G)
  statement: (a * ⨆ i, f i) = ⨆ i, a * f i
  proof: (OrderIso.mulLeft a).map_ciSup hf

@[to_additive]

中文:
引理 mul_ciSup
  条件: (hf : BddAbove (range f)) (a : G)
  结论: (a * ⨆ i, f i) = ⨆ i, a * f i
  证明: (OrderIso.mulLeft a).map_ciSup hf

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, map_ciSup, mulLeft
-/
lemma mul_ciSup (hf : BddAbove (range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_ciSup hf

@[to_additive]
/--
lemma `mul_ciInf` / 引理 `mul_ciInf`

English:
lemma mul_ciInf
  given: (hf : BddBelow (range f)) (a : G)
  statement: (a * ⨅ i, f i) = ⨅ i, a * f i
  proof: (OrderIso.mulLeft a).map_ciInf hf

中文:
引理 mul_ciInf
  条件: (hf : BddBelow (range f)) (a : G)
  结论: (a * ⨅ i, f i) = ⨅ i, a * f i
  证明: (OrderIso.mulLeft a).map_ciInf hf

Depends on / 依赖: OrderIso, OrderIso.mulLeft, map_ciInf, mulLeft
-/
lemma mul_ciInf (hf : BddBelow (range f)) (a : G) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  (OrderIso.mulLeft a).map_ciInf hf

end Left
