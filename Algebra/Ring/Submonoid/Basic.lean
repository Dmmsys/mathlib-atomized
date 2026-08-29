/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Ring.Defs

/-! # Lemmas about additive closures of `Subsemigroup`. -/

public section

open AddSubmonoid

namespace MulMemClass
variable {M R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

/--
lemma `mul_right_mem_add_closure` / 引理 `mul_right_mem_add_closure`

English:
lemma mul_right_mem_add_closure
  given: (ha : a in closure (S : Set R)) (hb : b in S)
  proof: by
  induction ha using closure_induction with
  | mem r hr => exact mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  | zero => simp only [zero_mul, zero_mem _]
  | add r s _ _ hr hs => simpa only [add_mul] using add_mem hr hs

中文:
引理 mul_right_mem_add_closure
  条件: (ha : a in closure (S : 集合 R)) (hb : b in S)
  证明: by
  induction ha using closure_induction with
  | mem r hr => exact mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  | zero => simp only [zero_mul, zero_mem _]
  | add r s _ _ hr hs => simpa only [add_mul] using add_mem hr hs

Depends on / 依赖: add_mem, add_mul, closure_induction, mem_closure, mem_closure.mpr, mul_mem, zero_mem, zero_mul
-/
lemma mul_right_mem_add_closure (ha : a in closure (S : Set R)) (hb : b in S) :
    a * b in closure (S : Set R) := by
  induction ha using closure_induction with
  | mem r hr => exact mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  | zero => simp only [zero_mul, zero_mem _]
  | add r s _ _ hr hs => simpa only [add_mul] using add_mem hr hs

/--
lemma `mul_mem_add_closure` / 引理 `mul_mem_add_closure`

English:
lemma mul_mem_add_closure
  statement: (ha : a in closure (S : Set R))
  proof: by
  induction hb using closure_induction with
  | mem r hr => exact MulMemClass.mul_right_mem_add_closure ha hr
  | zero => simp only [mul_zero, zero_mem _]
  | add r s _ _ hr hs => simpa only [mul_add] using add_mem hr hs

中文:
引理 mul_mem_add_closure
  结论: (ha : a in closure (S : 集合 R))
  证明: by
  induction hb using closure_induction with
  | mem r hr => exact MulMemClass.mul_right_mem_add_closure ha hr
  | zero => simp only [mul_zero, zero_mem _]
  | add r s _ _ hr hs => simpa only [mul_add] using add_mem hr hs

Depends on / 依赖: MulMemClass, MulMemClass.mul_right_mem_add_closure, add_mem, closure_induction, mul_add, mul_right_mem_add_closure, mul_zero, zero_mem
-/
lemma mul_mem_add_closure (ha : a in closure (S : Set R))
    (hb : b in closure (S : Set R)) : a * b in closure (S : Set R) := by
  induction hb using closure_induction with
  | mem r hr => exact MulMemClass.mul_right_mem_add_closure ha hr
  | zero => simp only [mul_zero, zero_mem _]
  | add r s _ _ hr hs => simpa only [mul_add] using add_mem hr hs

/--
lemma `mul_left_mem_add_closure` / 引理 `mul_left_mem_add_closure`

English:
lemma mul_left_mem_add_closure
  given: (ha : a in S) (hb : b in closure (S : Set R))
  proof: mul_mem_add_closure (mem_closure.mpr fun _sT hT => hT ha) hb

中文:
引理 mul_left_mem_add_closure
  条件: (ha : a in S) (hb : b in closure (S : 集合 R))
  证明: mul_mem_add_closure (mem_closure.mpr fun _sT hT => hT ha) hb

Depends on / 依赖: mem_closure, mem_closure.mpr, mul_mem_add_closure
-/
lemma mul_left_mem_add_closure (ha : a in S) (hb : b in closure (S : Set R)) :
    a * b in closure (S : Set R) :=
  mul_mem_add_closure (mem_closure.mpr fun _sT hT => hT ha) hb

end MulMemClass
