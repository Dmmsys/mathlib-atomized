/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.RingTheory.Ideal.Defs

/-!

# Big operators for ideals

This contains some results on the big operators `∑` and `∏` interacting with the `Ideal` type.
-/

public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  given: (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -> α}
  proof: Submodule.sum_mem I

中文:
定理 sum_mem
  条件: (I : 理想 α) {ι : 类型} {t : 有限集 ι} {f : ι -> α}
  证明: Submodule.sum_mem I

Depends on / 依赖: Submodule, Submodule.sum_mem, sum_mem
-/
theorem sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -> α} :
    (forall c in t, f c in I) -> (∑ i in t, f i) in I :=
  Submodule.sum_mem I

end Ideal
