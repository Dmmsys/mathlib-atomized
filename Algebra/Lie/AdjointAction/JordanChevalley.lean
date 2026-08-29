/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Jordan–Chevalley decomposition and the adjoint action

This file contains results about the interaction between the adjoint action `LieAlgebra.ad` and
the Jordan–Chevalley decomposition.

## Main results

* `LieAlgebra.ad_mem_adjoin_of_isSemisimple`: for a JC decomposition, `ad(s) ∈ K[ad(n + s)]`.
* `LieAlgebra.ad_mem_adjoin_of_isNilpotent`: for a JC decomposition, `ad(n) ∈ K[ad(n + s)]`.
-/

public section

namespace LieAlgebra

open Algebra

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] {n s : Module.End K V}

attribute [local instance 100] LieRing.ofAssociativeRing

/--
theorem `ad_mem_adjoin_of_isSemisimple` / 定理 `ad_mem_adjoin_of_isSemisimple`

English:
theorem ad_mem_adjoin_of_isSemisimple
  proof: by
  obtain ⟨n', hn'_adj, s', hs'_adj, hn'_nil, hs'_ss, h_jc⟩ :=
    (ad K _ (n + s)).exists_isNilpotent_isSemisimple
  have hc' : Commute n' s' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs'_adj
      (Algebra.commute_of_mem_adjoin_self hn'_adj).symm
  obtain ⟨-, hs_eq⟩ := Module.End

中文:
定理 ad_mem_adjoin_of_isSemisimple
  证明: by
  obtain ⟨n', hn'_adj, s', hs'_adj, hn'_nil, hs'_ss, h_jc⟩ :=
    (ad K _ (n + s)).exists_isNilpotent_isSemisimple
  have hc' : Commute n' s' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs'_adj
      (Algebra.commute_of_mem_adjoin_self hn'_adj).symm
  obtain ⟨-, hs_eq⟩ := Module.End

Depends on / 依赖: Algebra, Algebra.commute_of_mem_adjoin_self, Algebra.commute_of_mem_adjoin_singleton_of_commute, Commute, LieAlgebra, LieAlgebra.ad_isSemisimple_of_isSemisimple, LieAlgebra.ad_nilpotent_of_nilpotent, LieAlgebra.commute_ad_of_commute, Module, Module.End.isNilpotent_isSemisimple_unique, _adj, _nil, ad_isSemisimple_of_isSemisimple, ad_nilpotent_of_nilpotent, commute_ad_of_commute, commute_of_mem_adjoin_self, commute_of_mem_adjoin_singleton_of_commute, exists_isNilpotent_isSemisimple, h_jc, h_jc.symm.trans
-/
theorem ad_mem_adjoin_of_isSemisimple
    (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple) :
    ad K _ s in K[ad K _ (n + s)] := by
  obtain ⟨n', hn'_adj, s', hs'_adj, hn'_nil, hs'_ss, h_jc⟩ :=
    (ad K _ (n + s)).exists_isNilpotent_isSemisimple
  have hc' : Commute n' s' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs'_adj
      (Algebra.commute_of_mem_adjoin_self hn'_adj).symm
  obtain ⟨-, hs_eq⟩ := Module.End.isNilpotent_isSemisimple_unique hn'_nil hs'_ss
    (LieAlgebra.ad_nilpotent_of_nilpotent (R := K) hn)
    (LieAlgebra.ad_isSemisimple_of_isSemisimple hs) hc'
    (LieAlgebra.commute_ad_of_commute hc) (h_jc.symm.trans (map_add (ad K _) n s))
  rwa [hs_eq] at hs'_adj

/--
theorem `ad_mem_adjoin_of_isNilpotent` / 定理 `ad_mem_adjoin_of_isNilpotent`

English:
theorem ad_mem_adjoin_of_isNilpotent
  proof: by
  have : ad K _ n = ad K _ (n + s) - ad K _ s := by simp [map_add]
  rw [this]
  exact sub_mem (Algebra.self_mem_adjoin_singleton K _) (ad_mem_adjoin_of_isSemisimple hc hn hs)

中文:
定理 ad_mem_adjoin_of_isNilpotent
  证明: by
  have : ad K _ n = ad K _ (n + s) - ad K _ s := by simp [map_add]
  rw [this]
  exact sub_mem (Algebra.self_mem_adjoin_singleton K _) (ad_mem_adjoin_of_isSemisimple hc hn hs)

Depends on / 依赖: Algebra, Algebra.self_mem_adjoin_singleton, ad_mem_adjoin_of_isSemisimple, map_add, self_mem_adjoin_singleton, sub_mem
-/
theorem ad_mem_adjoin_of_isNilpotent
    (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple) :
    ad K _ n in K[ad K _ (n + s)] := by
  have : ad K _ n = ad K _ (n + s) - ad K _ s := by simp [map_add]
  rw [this]
  exact sub_mem (Algebra.self_mem_adjoin_singleton K _) (ad_mem_adjoin_of_isSemisimple hc hn hs)

end LieAlgebra
