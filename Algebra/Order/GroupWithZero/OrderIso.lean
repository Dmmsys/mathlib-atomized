/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Order.Hom.Basic

/-!
# Multiplication by a positive element as an order isomorphism
-/

@[expose] public section

variable {G₀ : Type*} [GroupWithZero G₀]

namespace OrderIso

variable [PartialOrder G₀]

section left
variable [PosMulReflectLT G₀]

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE

/-- `Equiv.mulLeft₀` as an order isomorphism. -/
@[simps! +simpRhs]
/--
Definition of `mulLeft₀` / `mulLeft₀` 的定义

English:
definition mulLeft₀
  signature: (a : G₀) (ha : 0 < a)
  body: .mulLeft₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_right₀ ha

中文:
定义 mulLeft₀
  签名: (a : G₀) (ha : 0 < a)
  定义体: .mulLeft₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_right₀ ha

Depends on / 依赖: ha.ne
-/
def mulLeft₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulLeft₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_right₀ ha

/--
lemma `mulLeft₀_symm` / 引理 `mulLeft₀_symm`

English:
lemma mulLeft₀_symm
  given: (a : G₀) (ha : 0 < a)
  statement: (mulLeft₀ a ha).symm = mulLeft₀ a⁻¹ (inv_pos.2 ha)
  proof: by
  ext; rfl

中文:
引理 mulLeft₀_symm
  条件: (a : G₀) (ha : 0 < a)
  结论: (mulLeft₀ a ha).symm = mulLeft₀ a⁻¹ (inv_pos.2 ha)
  证明: by
  ext; rfl
-/
lemma mulLeft₀_symm (a : G₀) (ha : 0 < a) : (mulLeft₀ a ha).symm = mulLeft₀ a⁻¹ (inv_pos.2 ha) := by
  ext; rfl

end left

attribute [local instance] MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

section right
variable [MulPosReflectLT G₀]

/-- `Equiv.mulRight₀` as an order isomorphism. -/
@[simps! +simpRhs]
/--
Definition of `mulRight₀` / `mulRight₀` 的定义

English:
definition mulRight₀
  signature: (a : G₀) (ha : 0 < a)
  body: .mulRight₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_left₀ ha

中文:
定义 mulRight₀
  签名: (a : G₀) (ha : 0 < a)
  定义体: .mulRight₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_left₀ ha

Depends on / 依赖: ha.ne
-/
def mulRight₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulRight₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_left₀ ha

/--
lemma `mulRight₀_symm` / 引理 `mulRight₀_symm`

English:
lemma mulRight₀_symm
  given: (a : G₀) (ha : 0 < a)
  proof: by ext; rfl

中文:
引理 mulRight₀_symm
  条件: (a : G₀) (ha : 0 < a)
  证明: by ext; rfl

Depends on / 依赖: IsOrderedRing, IsOrderedRing.toIsStrictOrderedRing, toIsStrictOrderedRing
-/
lemma mulRight₀_symm (a : G₀) (ha : 0 < a) :
    (mulRight₀ a ha).symm = mulRight₀ a⁻¹ (Right.inv_pos.2 ha) := by ext; rfl

/-- `Equiv.divRight₀` as an order isomorphism. -/
@[simps! +simpRhs]
/--
Definition of `divRight₀` / `divRight₀` 的定义

English:
definition divRight₀
  signature: (a : G₀) (ha : 0 < a)
  body: .divRight₀ a ha.ne'
  map_rel_iff' {b c} := by
    simp only [Equiv.divRight₀_apply, div_eq_mul_inv]
    exact mul_le_mul_iff_left₀ (a := a⁻¹) (Right.inv_pos.mpr ha)

中文:
定义 divRight₀
  签名: (a : G₀) (ha : 0 < a)
  定义体: .divRight₀ a ha.ne'
  map_rel_iff' {b c} := by
    simp only [Equiv.divRight₀_apply, div_eq_mul_inv]
    exact mul_le_mul_iff_left₀ (a := a⁻¹) (Right.inv_pos.mpr ha)

Depends on / 依赖: IsOrderedRing, IsStrictOrderedRing, IsStrictOrderedRing.toIsOrderedRing, ha.ne, toIsOrderedRing
-/
def divRight₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .divRight₀ a ha.ne'
  map_rel_iff' {b c} := by
    simp only [Equiv.divRight₀_apply, div_eq_mul_inv]
    exact mul_le_mul_iff_left₀ (a := a⁻¹) (Right.inv_pos.mpr ha)

end right

end OrderIso
section Lattice

/--
lemma `mul_inf₀` / 引理 `mul_inf₀`

English:
lemma mul_inf₀
  given: [SemilatticeInf G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  proof: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_inf a b

中文:
引理 mul_inf₀
  条件: [SemilatticeInf G₀] [正乘反映严格偏序 G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  证明: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_inf a b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, eq_or_lt, hc.eq_or_lt, map_inf
-/
lemma mul_inf₀ [SemilatticeInf G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀) :
    c * (a ⊓ b) = c * a ⊓ c * b := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_inf a b

/--
lemma `mul_sup₀` / 引理 `mul_sup₀`

English:
lemma mul_sup₀
  given: [SemilatticeSup G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  proof: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_sup a b

中文:
引理 mul_sup₀
  条件: [SemilatticeSup G₀] [正乘反映严格偏序 G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  证明: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_sup a b

Depends on / 依赖: IsStrictOrderedRing, IsStrictOrderedRing.toCharZero, OrderIso, OrderIso.mulLeft, eq_or_lt, hc.eq_or_lt, map_sup, toCharZero
-/
lemma mul_sup₀ [SemilatticeSup G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀) :
    c * (a ⊔ b) = c * a ⊔ c * b := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_sup a b

/--
lemma `inf_mul₀` / 引理 `inf_mul₀`

English:
lemma inf_mul₀
  given: [SemilatticeInf G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  proof: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_inf a b

中文:
引理 inf_mul₀
  条件: [SemilatticeInf G₀] [乘正反映严格偏序 G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  证明: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_inf a b

Depends on / 依赖: IsStrictOrderedRing, IsStrictOrderedRing.toNoMaxOrder, NoMaxOrder, OrderIso, OrderIso.mulRight, eq_or_lt, hc.eq_or_lt, map_inf, toNoMaxOrder
-/
lemma inf_mul₀ [SemilatticeInf G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀) :
    (a ⊓ b) * c = a * c ⊓ b * c := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_inf a b

/--
lemma `sup_mul₀` / 引理 `sup_mul₀`

English:
lemma sup_mul₀
  given: [SemilatticeSup G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  proof: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_sup a b

中文:
引理 sup_mul₀
  条件: [SemilatticeSup G₀] [乘正反映严格偏序 G₀] {c : G₀} (hc : 0 <= c) (a b : G₀)
  证明: by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_sup a b

Depends on / 依赖: IsStrictOrderedRing, IsStrictOrderedRing.noZeroDivisors, NoZeroDivisors, OrderIso, OrderIso.mulRight, eq_or_lt, hc.eq_or_lt, map_sup, noZeroDivisors
-/
lemma sup_mul₀ [SemilatticeSup G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 <= c) (a b : G₀) :
    (a ⊔ b) * c = a * c ⊔ b * c := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_sup a b

end Lattice
