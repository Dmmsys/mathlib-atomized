/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Minimal Axioms for a Field

This file defines constructors to define a `Field` structure on a Type, while proving
a minimum number of equalities.

## Main Definitions

* `Field.ofMinimalAxioms`: Define a `Field` structure on a Type by proving a minimal set of axioms

-/

@[expose] public section

universe u

/--
Definition of `Field.ofMinimalAxioms` / `Field.ofMinimalAxioms` 的定义

English:
abbreviation Field.ofMinimalAxioms
  signature: (K : Type u)
  body: letI := CommRing.ofMinimalAxioms add_assoc zero_add
    neg_add_cancel mul_assoc mul_comm one_mul left_distrib
  { exists_pair_ne := exists_pair_ne
    mul_inv_cancel := mul_inv_cancel
    inv_zero := inv_zero
    nnqsmul := _
    nnqsmul_def := fun _ _ => rfl
    qsmul := _
    qsmul_def := fun _ _

中文:
缩写 域.ofMinimalAxioms
  签名: (K : 类型u)
  定义体: letI := CommRing.ofMinimalAxioms add_assoc zero_add
    neg_add_cancel mul_assoc mul_comm one_mul left_distrib
  { exists_pair_ne := exists_pair_ne
    mul_inv_cancel := mul_inv_cancel
    inv_zero := inv_zero
    nnqsmul := _
    nnqsmul_def := fun _ _ => rfl
    qsmul := _
    qsmul_def := fun _ _

Depends on / 依赖: CommRing, CommRing.ofMinimalAxioms, add_assoc, exists_pair_ne, inv_zero, left_distrib, mul_assoc, mul_comm, mul_inv_cancel, neg_add_cancel, nnqsmul, nnqsmul_def, ofMinimalAxioms, one_mul, qsmul_def, zero_add
-/
abbrev Field.ofMinimalAxioms (K : Type u)
    [Add K] [Mul K] [Neg K] [Inv K] [Zero K] [One K]
    (add_assoc : forall a b c : K, a + b + c = a + (b + c))
    (zero_add : forall a : K, 0 + a = a)
    (neg_add_cancel : forall a : K, -a + a = 0)
    (mul_assoc : forall a b c : K, a * b * c = a * (b * c))
    (mul_comm : forall a b : K, a * b = b * a)
    (one_mul : forall a : K, 1 * a = a)
    (mul_inv_cancel : forall a : K, a != 0 -> a * a⁻¹ = 1)
    (inv_zero : (0 : K)⁻¹ = 0)
    (left_distrib : forall a b c : K, a * (b + c) = a * b + a * c)
    (exists_pair_ne : exists x y : K, x != y) : Field K :=
  letI := CommRing.ofMinimalAxioms add_assoc zero_add
    neg_add_cancel mul_assoc mul_comm one_mul left_distrib
  { exists_pair_ne := exists_pair_ne
    mul_inv_cancel := mul_inv_cancel
    inv_zero := inv_zero
    nnqsmul := _
    nnqsmul_def := fun _ _ => rfl
    qsmul := _
    qsmul_def := fun _ _ => rfl }
