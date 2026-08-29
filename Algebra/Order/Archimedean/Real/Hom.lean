/-
Copyright (c) 2024 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Algebra.Order.Archimedean.Hom -- shake: keep (Subsingleton (ℝ →+*o ℝ)), cf. lean#13417
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.CompleteField

/-!
# Uniqueness of ring homomorphisms to the real numbers

This file contains results about ring homomorphisms to `ℝ`.

## Main results

* `Real.nonemptyOrderRingHom`: For any archimedean ordered field `α`, there exists
  a monotone ring homomorphism `α →+*o ℝ`.
* `Real.RingHom.unique`: There exists no nontrivial ring homomorphism `ℝ →+* ℝ`.
-/

public section

-- Note that we already know `Subsingleton (α →+*o ℝ)` here.
-- We intentionally do not define instance `Unique (α →+*o ℝ)` to avoid instance diamonds.
/--
Instance `Real.nonemptyOrderRingHom` / 实例 `Real.nonemptyOrderRingHom`

English:
instance Real.nonemptyOrderRingHom
  signature: (α : Type*)
  body: ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingHom α Real⟩

中文:
实例 实数.nonemptyOrderRingHom
  签名: (α : 类型)
  定义体: ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingHom α Real⟩

Depends on / 依赖: ConditionallyCompleteLinearOrderedField, ConditionallyCompleteLinearOrderedField.inducedOrderRingHom, inducedOrderRingHom
-/
instance Real.nonemptyOrderRingHom (α : Type*)
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] : Nonempty (α ->+*o Real) :=
  ⟨ConditionallyCompleteLinearOrderedField.inducedOrderRingHom α Real⟩

/--
theorem `ringHom_monotone` / 定理 `ringHom_monotone`

English:
theorem ringHom_monotone
  statement: {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
  proof: (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

中文:
定理 ringHom_monotone
  结论: {R S : 类型} [环 R] [偏序 R] [是OrderedAdd幺半群 R]
  证明: (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

Depends on / 依赖: map_mul, monotone_iff_map_nonneg, mul_self_nonneg
-/
theorem ringHom_monotone {R S : Type*} [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [Ring S] [LinearOrder S] [IsOrderedAddMonoid S] [PosMulMono S]
    (hR : forall r : R, 0 <= r -> IsSquare r) (f : R ->+* S) : Monotone f :=
  (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_mul]; apply mul_self_nonneg

/--
Instance `Real.RingHom.unique` / 实例 `Real.RingHom.unique`

English:
instance Real.RingHom.unique
  signature: : Unique (Real ->+* Real) where
  body: RingHom.id Real
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (Real ->+*o Real) _
      ⟨f, ringHom_monotone (fun _ => Real.isSquare_iff.mpr) f⟩ default)

@[simp]

中文:
实例 实数.环态射.unique
  签名: : 唯一 (实数 ->+* 实数) where
  定义体: RingHom.id Real
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (Real ->+*o Real) _
      ⟨f, ringHom_monotone (fun _ => Real.isSquare_iff.mpr) f⟩ default)

@[simp]

Depends on / 依赖: RingHom, RingHom.id
-/
instance Real.RingHom.unique : Unique (Real ->+* Real) where
  default := RingHom.id Real
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (Real ->+*o Real) _
      ⟨f, ringHom_monotone (fun _ => Real.isSquare_iff.mpr) f⟩ default)

@[simp]
/--
theorem `Real.ringHom_apply` / 定理 `Real.ringHom_apply`

English:
theorem Real.ringHom_apply
  given: {F : Type*} [FunLike F Real Real] [RingHomClass F Real Real] (f : F) (r : Real)
  proof: DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r

中文:
定理 实数.ringHom_apply
  条件: {F : 类型} [函数状 F 实数 实数] [环态射类 F 实数 实数] (f : F) (r : 实数)
  证明: DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r

Depends on / 依赖: DFunLike, DFunLike.congr_fun, RingHomClass, RingHomClass.toRingHom, Unique, Unique.eq_default, congr_fun, eq_default, toRingHom
-/
theorem Real.ringHom_apply {F : Type*} [FunLike F Real Real] [RingHomClass F Real Real] (f : F) (r : Real) :
    f r = r :=
  DFunLike.congr_fun (Unique.eq_default (RingHomClass.toRingHom f)) r
