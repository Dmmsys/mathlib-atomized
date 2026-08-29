/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Lemmas about index and multiplication-by-n

In this file we collect some results involving the multiplication-by-`n` map
`nsmulAddMonoidHom n` (for a natural number `n`) on a commutative additive group
and the (relative) index of subgroups.
-/

public section

namespace AddSubgroup

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

open Module

open QuotientAddGroup in
variable (M) in
/--
lemma `index_range_nsmul` / 引理 `index_range_nsmul`

English:
lemma index_range_nsmul
  given: [Free Int M] [Module.Finite Int M] (n : Nat)
  proof: calc
    _ = (nsmulAddMonoidHom (α := (Fin (finrank Int M) -> Int)) n).range.index := by
      simpa [AddEquiv.map_range_nsmulAddMonoidHom]
        using (index_map_equiv (nsmulAddMonoidHom (α := M) n).range
                (Module.finBasis Int M).equivFun.toAddEquiv).symm
    _ = _ := by
      simp [index_eq_card, Nat.card_congr (addEquivPiModRangeNSMulAddMonoidHom _ n).toEquiv,
        Nat.card_fun, Int.range_nsmulAddMonoidHom,
        Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv]

中文:
引理 index_range_nsmul
  条件: [自由 整数 M] [模.有限 整数 M] (n : 自然数)
  证明: calc
    _ = (nsmulAddMonoidHom (α := (Fin (finrank Int M) -> Int)) n).range.index := by
      simpa [AddEquiv.map_range_nsmulAddMonoidHom]
        using (index_map_equiv (nsmulAddMonoidHom (α := M) n).range
                (Module.finBasis Int M).equivFun.toAddEquiv).symm
    _ = _ := by
      simp [index_eq_card, Nat.card_congr (addEquivPiModRangeNSMulAddMonoidHom _ n).toEquiv,
        Nat.card_fun, Int.range_nsmulAddMonoidHom,
        Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv]

Depends on / 依赖: finrank, range.index
-/
lemma index_range_nsmul [Free Int M] [Module.Finite Int M] (n : Nat) :
    (nsmulAddMonoidHom (α := M) n).range.index = n ^ finrank Int M :=
  calc
    _ = (nsmulAddMonoidHom (α := (Fin (finrank Int M) -> Int)) n).range.index := by
      simpa [AddEquiv.map_range_nsmulAddMonoidHom]
        using (index_map_equiv (nsmulAddMonoidHom (α := M) n).range
                (Module.finBasis Int M).equivFun.toAddEquiv).symm
    _ = _ := by
      simp [index_eq_card, Nat.card_congr (addEquivPiModRangeNSMulAddMonoidHom _ n).toEquiv,
        Nat.card_fun, Int.range_nsmulAddMonoidHom,
        Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv]

/--
lemma `relIndex_map_nsmul` / 引理 `relIndex_map_nsmul`

English:
lemma relIndex_map_nsmul
  statement: (n : Nat) (S : AddSubgroup M) [Free Int ↥S.toIntSubmodule]
  proof: by
  simpa only [relIndex, addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
    using! index_range_nsmul S.toIntSubmodule n

中文:
引理 relIndex_map_nsmul
  结论: (n : 自然数) (S : 加法子群 M) [自由 整数 ↥S.to整数Submodule]
  证明: by
  simpa only [relIndex, addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
    using! index_range_nsmul S.toIntSubmodule n

Depends on / 依赖: S.toIntSubmodule, addSubgroupOf_map_nsmulAddMonoidHom_eq_range, finrank, index_range_nsmul, relIndex, toIntSubmodule
-/
lemma relIndex_map_nsmul (n : Nat) (S : AddSubgroup M) [Free Int ↥S.toIntSubmodule]
    [Module.Finite Int ↥S.toIntSubmodule] :
    (S.map (nsmulAddMonoidHom (α := M) n)).relIndex S = n ^ finrank Int S := by
  simpa only [relIndex, addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
    using! index_range_nsmul S.toIntSubmodule n

/--
lemma `distribSMulToLinearMap_injective_of_isTorsionFree` / 引理 `distribSMulToLinearMap_injective_of_isTorsionFree`

English:
lemma distribSMulToLinearMap_injective_of_isTorsionFree
  given: [IsTorsionFree Int M] {n : Nat} (hn : n != 0)
  proof: LinearMap.ker_eq_bot.mp (Submodule.eq_bot_iff _).mpr fun x hx => by simp_all

中文:
引理 distribSMulToLinearMap_injective_of_isTorsionFree
  条件: [是无挠 整数 M] {n : 自然数} (hn : n != 0)
  证明: LinearMap.ker_eq_bot.mp (Submodule.eq_bot_iff _).mpr fun x hx => by simp_all

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mp, Submodule, Submodule.eq_bot_iff, eq_bot_iff, ker_eq_bot
-/
lemma distribSMulToLinearMap_injective_of_isTorsionFree [IsTorsionFree Int M] {n : Nat} (hn : n != 0) :
    Function.Injective (DistribSMul.toLinearMap Int M n) :=
LinearMap.ker_eq_bot.mp (Submodule.eq_bot_iff _).mpr fun x hx => by simp_all

/--
lemma `nsmulAddMonoidHom_injective_of_isTorsionFree` / 引理 `nsmulAddMonoidHom_injective_of_isTorsionFree`

English:
lemma nsmulAddMonoidHom_injective_of_isTorsionFree
  given: [IsTorsionFree Int M] {n : Nat} (hn : n != 0)
  proof: (AddMonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff_forall _).mpr fun x hx => by simp_all

中文:
引理 nsmulAddMonoidHom_injective_of_isTorsionFree
  条件: [是无挠 整数 M] {n : 自然数} (hn : n != 0)
  证明: (AddMonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff_forall _).mpr fun x hx => by simp_all
-/
lemma nsmulAddMonoidHom_injective_of_isTorsionFree [IsTorsionFree Int M] {n : Nat} (hn : n != 0) :
    Function.Injective (nsmulAddMonoidHom (α := M) n) :=
(AddMonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff_forall _).mpr fun x hx => by simp_all

/--
lemma `finrank_eq_of_finiteIndex` / 引理 `finrank_eq_of_finiteIndex`

English:
lemma finrank_eq_of_finiteIndex
  statement: [Module.Finite Int M] [IsTorsionFree Int M] (A : AddSubgroup M)
  proof: by
  refine le_antisymm A.toIntSubmodule.finrank_le ?_
  have : finrank Int (DistribSMul.toLinearMap Int M A.index).range = finrank Int M :=
(DistribSMul.toLinearMap ..).finrank_range_of_inj
      distribSMulToLinearMap_injective_of_isTorsionFree FiniteIndex.index_ne_zero
  rw [← this]
refine Submodule.finrank_mono (OrderIso.symm_apply_le toIntSubmodule).mp fun m hm => ?_
  obtain ⟨x, rfl⟩ : exists x, A.index • x = m := by simpa using hm
  exact A.nsmul_index_mem x

中文:
引理 finrank_eq_of_finiteIndex
  结论: [模.有限 整数 M] [是无挠 整数 M] (A : 加法子群 M)
  证明: by
  refine le_antisymm A.toIntSubmodule.finrank_le ?_
  have : finrank Int (DistribSMul.toLinearMap Int M A.index).range = finrank Int M :=
(DistribSMul.toLinearMap ..).finrank_range_of_inj
      distribSMulToLinearMap_injective_of_isTorsionFree FiniteIndex.index_ne_zero
  rw [← this]
refine Submodule.finrank_mono (OrderIso.symm_apply_le toIntSubmodule).mp fun m hm => ?_
  obtain ⟨x, rfl⟩ : exists x, A.index • x = m := by simpa using hm
  exact A.nsmul_index_mem x

Depends on / 依赖: A.index, A.nsmul_index_mem, A.toIntSubmodule.finrank_le, DistribSMul, DistribSMul.toLinearMap, FiniteIndex, FiniteIndex.index_ne_zero, OrderIso, OrderIso.symm_apply_le, Submodule, Submodule.finrank_mono, distribSMulToLinearMap_injective_of_isTorsionFree, finrank, finrank_le, finrank_mono, finrank_range_of_inj, index_ne_zero, le_antisymm, nsmul_index_mem, symm_apply_le
-/
lemma finrank_eq_of_finiteIndex [Module.Finite Int M] [IsTorsionFree Int M] (A : AddSubgroup M)
    [A.FiniteIndex] :
    finrank Int A = finrank Int M := by
  refine le_antisymm A.toIntSubmodule.finrank_le ?_
  have : finrank Int (DistribSMul.toLinearMap Int M A.index).range = finrank Int M :=
(DistribSMul.toLinearMap ..).finrank_range_of_inj
      distribSMulToLinearMap_injective_of_isTorsionFree FiniteIndex.index_ne_zero
  rw [← this]
refine Submodule.finrank_mono (OrderIso.symm_apply_le toIntSubmodule).mp fun m hm => ?_
  obtain ⟨x, rfl⟩ : exists x, A.index • x = m := by simpa using hm
  exact A.nsmul_index_mem x

/--
lemma `finrank_eq_of_isFiniteRelIndex` / 引理 `finrank_eq_of_isFiniteRelIndex`

English:
lemma finrank_eq_of_isFiniteRelIndex
  statement: {A B : AddSubgroup M} [Module.Finite Int B] [IsTorsionFree Int B]
  proof: by
  have : (A.addSubgroupOf B).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_addSubgroupOf
  rw [← finrank_eq_of_finiteIndex (A.addSubgroupOf B)]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

中文:
引理 finrank_eq_of_isFiniteRelIndex
  结论: {A B : 加法子群 M} [模.有限 整数 B] [是无挠 整数 B]
  证明: by
  have : (A.addSubgroupOf B).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_addSubgroupOf
  rw [← finrank_eq_of_finiteIndex (A.addSubgroupOf B)]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

Depends on / 依赖: A.addSubgroupOf, FiniteIndex, IsFiniteRelIndex, IsFiniteRelIndex.to_finiteIndex_addSubgroupOf, addSubgroupOf, addSubgroupOfEquivOfLe, finrank_eq, finrank_eq_of_finiteIndex, symm.toIntLinearEquiv.finrank_eq, toIntLinearEquiv, to_finiteIndex_addSubgroupOf
-/
lemma finrank_eq_of_isFiniteRelIndex {A B : AddSubgroup M} [Module.Finite Int B] [IsTorsionFree Int B]
    (h : A <= B) [A.IsFiniteRelIndex B] :
    finrank Int A = finrank Int B := by
  have : (A.addSubgroupOf B).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_addSubgroupOf
  rw [← finrank_eq_of_finiteIndex (A.addSubgroupOf B)]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

end AddSubgroup

end
