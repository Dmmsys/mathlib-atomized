/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang, Oliver Nash
-/
module

public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Profinite

/-!
# Further separation lemmas
-/

public section

variable {X : Type*}

namespace CompletelyRegularSpace

variable [TopologicalSpace X] [T35Space X]

/--
theorem `totallySeparatedSpace_of_cardinalMk_lt_continuum` / 定理 `totallySeparatedSpace_of_cardinalMk_lt_continuum`

English:
theorem totallySeparatedSpace_of_cardinalMk_lt_continuum
  given: (h : Cardinal.mk X < Cardinal.continuum)
  proof: totallySeparatedSpace_of_t0_of_basis_clopen
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum h

中文:
定理 totallySeparatedSpace_of_cardinalMk_lt_continuum
  条件: (h : 基数.mk X < 基数.continuum)
  证明: totallySeparatedSpace_of_t0_of_basis_clopen
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum h

Depends on / 依赖: CompletelyRegularSpace, CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum, isTopologicalBasis_clopens_of_cardinalMk_lt_continuum, totallySeparatedSpace_of_t0_of_basis_clopen
-/
theorem totallySeparatedSpace_of_cardinalMk_lt_continuum (h : Cardinal.mk X < Cardinal.continuum) :
    TotallySeparatedSpace X :=
totallySeparatedSpace_of_t0_of_basis_clopen
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: X] : TotallySeparatedSpace X
  body: totallySeparatedSpace_of_cardinalMk_lt_continuum
    (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt Cardinal.aleph0_lt_continuum

中文:
实例 [可数
  签名: X] : TotallySeparated空间 X
  定义体: totallySeparatedSpace_of_cardinalMk_lt_continuum
    (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt Cardinal.aleph0_lt_continuum

Depends on / 依赖: Cardinal, Cardinal.aleph0_lt_continuum, Cardinal.mk_le_aleph0_iff.mpr, aleph0_lt_continuum, mk_le_aleph0_iff, totallySeparatedSpace_of_cardinalMk_lt_continuum, trans_lt
-/
instance [Countable X] : TotallySeparatedSpace X :=
totallySeparatedSpace_of_cardinalMk_lt_continuum
    (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt Cardinal.aleph0_lt_continuum

/--
lemma `_root_.Set.Countable.totallySeparatedSpace` / 引理 `_root_.Set.Countable.totallySeparatedSpace`

English:
lemma _root_.Set.Countable.totallySeparatedSpace
  given: {s : Set X} (h : s.Countable)
  proof: have : _root_.Countable s := h
  inferInstanceAs (TotallySeparatedSpace s)

中文:
引理 _root_.集合.可数.totallySeparatedSpace
  条件: {s : 集合 X} (h : s.可数)
  证明: have : _root_.Countable s := h
  inferInstanceAs (TotallySeparatedSpace s)
-/
protected lemma _root_.Set.Countable.totallySeparatedSpace {s : Set X} (h : s.Countable) :
    TotallySeparatedSpace s :=
  have : _root_.Countable s := h
  inferInstanceAs (TotallySeparatedSpace s)

end CompletelyRegularSpace

/--
theorem `Set.Countable.isTotallyDisconnected` / 定理 `Set.Countable.isTotallyDisconnected`

English:
theorem Set.Countable.isTotallyDisconnected
  given: [MetricSpace X] {s : Set X} (hs : s.Countable)
  proof: by
  rw [← totallyDisconnectedSpace_subtype_iff]
  have : Countable s := hs
  infer_instance

中文:
定理 集合.可数.isTotallyDisconnected
  条件: [度量空间 X] {s : 集合 X} (hs : s.可数)
  证明: by
  rw [← totallyDisconnectedSpace_subtype_iff]
  have : Countable s := hs
  infer_instance

Depends on / 依赖: Countable, infer_instance, totallyDisconnectedSpace_subtype_iff
-/
theorem Set.Countable.isTotallyDisconnected [MetricSpace X] {s : Set X} (hs : s.Countable) :
    IsTotallyDisconnected s := by
  rw [← totallyDisconnectedSpace_subtype_iff]
  have : Countable s := hs
  infer_instance
