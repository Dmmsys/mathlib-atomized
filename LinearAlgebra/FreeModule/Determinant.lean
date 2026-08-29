/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Determinants in free (finite) modules

Quite a lot of our results on determinants (that you might know in vector spaces) will work for all
free (finite) modules over any commutative ring.

## Main results

* `LinearMap.det_zero''`: The determinant of the constant zero map is zero, in a finite free
  nontrivial module.
-/

public section


@[simp high]
/--
theorem `LinearMap.det_zero''` / 定理 `LinearMap.det_zero''`

English:
theorem LinearMap.det_zero''
  statement: {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  let : Nonempty (Module.Free.ChooseBasisIndex R M) := (Module.Free.chooseBasis R M).index_nonempty
  nontriviality R
  exact LinearMap.det_zero' (Module.Free.chooseBasis R M)

中文:
定理 线性映射.det_zero''
  结论: {R M : 类型} [交换环 R] [加法交换群 M] [模 R M]
  证明: by
  let : Nonempty (Module.Free.ChooseBasisIndex R M) := (Module.Free.chooseBasis R M).index_nonempty
  nontriviality R
  exact LinearMap.det_zero' (Module.Free.chooseBasis R M)

Depends on / 依赖: ChooseBasisIndex, LinearMap, LinearMap.det_zero, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Nonempty, chooseBasis, det_zero, index_nonempty, nontriviality
-/
theorem LinearMap.det_zero'' {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [Nontrivial M] : LinearMap.det (0 : M ->ₗ[R] M) = 0 := by
  let : Nonempty (Module.Free.ChooseBasisIndex R M) := (Module.Free.chooseBasis R M).index_nonempty
  nontriviality R
  exact LinearMap.det_zero' (Module.Free.chooseBasis R M)
