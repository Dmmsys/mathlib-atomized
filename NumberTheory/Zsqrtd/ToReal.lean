/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Image of `Zsqrtd` in `ℝ`

This file defines `Zsqrtd.toReal` and related lemmas.
It is in a separate file to avoid pulling in all of `Data.Real` into `Data.Zsqrtd`.
-/

@[expose] public section


namespace Zsqrtd

/-- The image of `Zsqrtd` in `ℝ`, using `Real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `toReal h (star a)`. -/
@[simps!]
/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: {d : Int} (h : 0 <= d)
  body: lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg h)⟩

中文:
定义 toReal
  签名: {d : 整数} (h : 0 <= d)
  定义体: lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg h)⟩

Depends on / 依赖: Int.cast_nonneg, Real.mul_self_sqrt, cast_nonneg, mul_self_sqrt
-/
noncomputable def toReal {d : Int} (h : 0 <= d) : Int√d ->+* Real :=
  lift ⟨√↑d, Real.mul_self_sqrt (Int.cast_nonneg h)⟩

/--
theorem `toReal_injective` / 定理 `toReal_injective`

English:
theorem toReal_injective
  given: {d : Int} (h0d : 0 <= d) (hd : forall n : Int, d != n * n)
  proof: lift_injective _ hd

中文:
定理 toReal_injective
  条件: {d : 整数} (h0d : 0 <= d) (hd : 对任意 n : 整数, d != n * n)
  证明: lift_injective _ hd

Depends on / 依赖: lift_injective
-/
theorem toReal_injective {d : Int} (h0d : 0 <= d) (hd : forall n : Int, d != n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd

end Zsqrtd
