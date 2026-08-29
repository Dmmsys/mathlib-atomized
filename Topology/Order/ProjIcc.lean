/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Order.Basic

/-!
# Projection onto a closed interval

In this file we prove that the projection `Set.projIcc f a b h` is a quotient map, and use it
to show that `Set.IccExtend h f` is continuous if and only if `f` is continuous.
-/

public section


open Set Filter Topology

variable {α β γ : Type*} [LinearOrder α] {a b c : α} {h : a <= b}

/--
theorem `Filter.Tendsto.IccExtend` / 定理 `Filter.Tendsto.IccExtend`

English:
theorem Filter.Tendsto.IccExtend
  statement: (f : γ -> Icc a b -> β) {la : Filter α} {lb : Filter β}
  proof: hf.comp tendsto_id.prodMap tendsto_map

中文:
定理 滤子.收敛.IccExtend
  结论: (f : γ -> 闭区间 a b -> β) {la : 滤子 α} {lb : 滤子 β}
  证明: hf.comp tendsto_id.prodMap tendsto_map
-/
protected theorem Filter.Tendsto.IccExtend (f : γ -> Icc a b -> β) {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (hf : Tendsto ↿f (lc ×ˢ la.map (projIcc a b h)) lb) :
    Tendsto (↿(IccExtend h ∘ f)) (lc ×ˢ la) lb :=
hf.comp tendsto_id.prodMap tendsto_map

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

@[continuity, fun_prop]
/--
theorem `continuous_projIcc` / 定理 `continuous_projIcc`

English:
theorem continuous_projIcc
  statement: Continuous (projIcc a b h)
  proof: Continuous.subtype_mk (by fun_prop) _

中文:
定理 continuous_projIcc
  结论: 连续 (projIcc a b h)
  证明: Continuous.subtype_mk (by fun_prop) _

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
theorem continuous_projIcc : Continuous (projIcc a b h) := Continuous.subtype_mk (by fun_prop) _

/--
theorem `isQuotientMap_projIcc` / 定理 `isQuotientMap_projIcc`

English:
theorem isQuotientMap_projIcc
  statement: IsQuotientMap (projIcc a b h) where
  proof: projIcc_surjective h
  isCoinducing := .of_isOpen_preimage_iff_isOpen fun s =>
    ⟨fun hs => ⟨_, hs, by ext; simp⟩, fun hs => hs.preimage continuous_projIcc⟩

@[simp]

中文:
定理 isQuotientMap_projIcc
  结论: 是商映射 (projIcc a b h) where
  证明: projIcc_surjective h
  isCoinducing := .of_isOpen_preimage_iff_isOpen fun s =>
    ⟨fun hs => ⟨_, hs, by ext; simp⟩, fun hs => hs.preimage continuous_projIcc⟩

@[simp]

Depends on / 依赖: projIcc_surjective
-/
theorem isQuotientMap_projIcc : IsQuotientMap (projIcc a b h) where
  surjective := projIcc_surjective h
  isCoinducing := .of_isOpen_preimage_iff_isOpen fun s =>
    ⟨fun hs => ⟨_, hs, by ext; simp⟩, fun hs => hs.preimage continuous_projIcc⟩

@[simp]
/--
theorem `continuous_IccExtend_iff` / 定理 `continuous_IccExtend_iff`

English:
theorem continuous_IccExtend_iff
  given: {f : Icc a b -> β}
  statement: Continuous (IccExtend h f) ↔ Continuous f
  proof: isQuotientMap_projIcc.continuous_iff.symm

中文:
定理 continuous_IccExtend_iff
  条件: {f : 闭区间 a b -> β}
  结论: 连续 (IccExtend h f) ↔ 连续 f
  证明: isQuotientMap_projIcc.continuous_iff.symm

Depends on / 依赖: continuous_iff, isQuotientMap_projIcc, isQuotientMap_projIcc.continuous_iff.symm
-/
theorem continuous_IccExtend_iff {f : Icc a b -> β} : Continuous (IccExtend h f) ↔ Continuous f :=
  isQuotientMap_projIcc.continuous_iff.symm

/-- See Note [continuity lemma statement]. -/
@[fun_prop]
/--
theorem `Continuous.IccExtend` / 定理 `Continuous.IccExtend`

English:
theorem Continuous.IccExtend
  statement: {f : γ -> Icc a b -> β} {g : γ -> α} (hf : Continuous ↿f)
  proof: show Continuous (↿f ∘ fun x => (x, projIcc a b h (g x)))
from hf.comp continuous_id.prodMk continuous_projIcc.comp hg

中文:
定理 连续.IccExtend
  结论: {f : γ -> 闭区间 a b -> β} {g : γ -> α} (hf : 连续 ↿f)
  证明: show Continuous (↿f ∘ fun x => (x, projIcc a b h (g x)))
from hf.comp continuous_id.prodMk continuous_projIcc.comp hg
-/
protected theorem Continuous.IccExtend {f : γ -> Icc a b -> β} {g : γ -> α} (hf : Continuous ↿f)
    (hg : Continuous g) : Continuous fun a => IccExtend h (f a) (g a) :=
  show Continuous (↿f ∘ fun x => (x, projIcc a b h (g x)))
from hf.comp continuous_id.prodMk continuous_projIcc.comp hg

/-- A useful special case of `Continuous.IccExtend`. -/
@[continuity, fun_prop]
/--
theorem `Continuous.Icc_extend'` / 定理 `Continuous.Icc_extend'`

English:
theorem Continuous.Icc_extend'
  given: {f : Icc a b -> β} (hf : Continuous f)
  proof: hf.comp continuous_projIcc

@[fun_prop]

中文:
定理 连续.Icc_extend'
  条件: {f : 闭区间 a b -> β} (hf : 连续 f)
  证明: hf.comp continuous_projIcc

@[fun_prop]
-/
protected theorem Continuous.Icc_extend' {f : Icc a b -> β} (hf : Continuous f) :
    Continuous (IccExtend h f) :=
  hf.comp continuous_projIcc

@[fun_prop]
/--
theorem `ContinuousAt.IccExtend` / 定理 `ContinuousAt.IccExtend`

English:
theorem ContinuousAt.IccExtend
  statement: {x : γ} (f : γ -> Icc a b -> β) {g : γ -> α}
  proof: show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
ContinuousAt.comp hf continuousAt_id.prodMk continuous_projIcc.continuousAt.comp hg

中文:
定理 ContinuousAt.IccExtend
  结论: {x : γ} (f : γ -> 闭区间 a b -> β) {g : γ -> α}
  证明: show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
ContinuousAt.comp hf continuousAt_id.prodMk continuous_projIcc.continuousAt.comp hg

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, continuousAt, continuousAt_id, continuousAt_id.prodMk, continuous_projIcc, continuous_projIcc.continuousAt.comp, prodMk, projIcc
-/
theorem ContinuousAt.IccExtend {x : γ} (f : γ -> Icc a b -> β) {g : γ -> α}
    (hf : ContinuousAt ↿f (x, projIcc a b h (g x))) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => IccExtend h (f a) (g a)) x :=
  show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
ContinuousAt.comp hf continuousAt_id.prodMk continuous_projIcc.continuousAt.comp hg
