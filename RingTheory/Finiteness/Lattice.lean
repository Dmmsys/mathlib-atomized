/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite suprema of finite modules

-/

public section

namespace Submodule

open Module

variable {R V} [Ring R] [AddCommGroup V] [Module R V]

/--
Instance `finite_iSup` / 实例 `finite_iSup`

English:
instance finite_iSup
  signature: {ι : Sort*} [Finite ι] (S : ι -> Submodule R V)
  body: by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down]; rw [← Finset.sup_univ_eq_iSup]
  exact Submodule.finite_finset_sup _ _

中文:
实例 finite_iSup
  签名: {ι : 类型层*} [有限 ι] (S : ι -> 子模 R V)
  定义体: by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down]; rw [← Finset.sup_univ_eq_iSup]
  exact Submodule.finite_finset_sup _ _

Depends on / 依赖: Finset, Finset.sup_univ_eq_iSup, Submodule, Submodule.finite_finset_sup, finite_finset_sup, iSup_plift_down, nonempty_fintype, sup_univ_eq_iSup
-/
instance finite_iSup {ι : Sort*} [Finite ι] (S : ι -> Submodule R V)
    [forall i, Module.Finite R (S i)] : Module.Finite R ↑(⨆ i, S i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down]; rw [← Finset.sup_univ_eq_iSup]
  exact Submodule.finite_finset_sup _ _

end Submodule
