/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Urysohn's lemma for bounded continuous functions

In this file we reformulate Urysohn's lemma `exists_continuous_zero_one_of_isClosed` in terms of
bounded continuous functions `X →ᵇ ℝ`. These lemmas live in a separate file because
`Topology.ContinuousMap.Bounded` imports too many other files.

## Tags

Urysohn's lemma, normal topological space
-/

public section


open BoundedContinuousFunction

open Set Function

/--
theorem `exists_bounded_zero_one_of_closed` / 定理 `exists_bounded_zero_one_of_closed`

English:
theorem exists_bounded_zero_one_of_closed
  statement: {X : Type*} [TopologicalSpace X] [NormalSpace X]
  proof: let ⟨f, hfs, hft, hf⟩ := exists_continuous_zero_one_of_isClosed hs ht hd
  ⟨⟨f, 1, fun _ _ => Real.dist_le_of_mem_Icc_01 (hf _) (hf _)⟩, hfs, hft, hf⟩

中文:
定理 存在_bounded_zero_one_of_closed
  结论: {X : 类型} [拓扑空间 X] [正规空间 X]
  证明: let ⟨f, hfs, hft, hf⟩ := exists_continuous_zero_one_of_isClosed hs ht hd
  ⟨⟨f, 1, fun _ _ => Real.dist_le_of_mem_Icc_01 (hf _) (hf _)⟩, hfs, hft, hf⟩

Depends on / 依赖: Real.dist_le_of_mem_Icc_01, dist_le_of_mem_Icc_01, exists_continuous_zero_one_of_isClosed
-/
theorem exists_bounded_zero_one_of_closed {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    exists f : X ->ᵇ Real, EqOn f 0 s ∧ EqOn f 1 t ∧ forall x, f x in Icc (0 : Real) 1 :=
  let ⟨f, hfs, hft, hf⟩ := exists_continuous_zero_one_of_isClosed hs ht hd
  ⟨⟨f, 1, fun _ _ => Real.dist_le_of_mem_Icc_01 (hf _) (hf _)⟩, hfs, hft, hf⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `exists_bounded_mem_Icc_of_closed_of_le` / 定理 `exists_bounded_mem_Icc_of_closed_of_le`

English:
theorem exists_bounded_mem_Icc_of_closed_of_le
  statement: {X : Type*} [TopologicalSpace X] [NormalSpace X]
  proof: let ⟨f, hfs, hft, hf01⟩ := exists_bounded_zero_one_of_closed hs ht hd
  ⟨BoundedContinuousFunction.const X a + (b - a) • f, fun x hx => by simp [hfs hx], fun x hx => by
    simp [hft hx], fun x =>
    ⟨by dsimp; nlinarith [(hf01 x).1], by dsimp; nlinarith [(hf01 x).2]⟩⟩

中文:
定理 存在_bounded_mem_Icc_of_closed_of_le
  结论: {X : 类型} [拓扑空间 X] [正规空间 X]
  证明: let ⟨f, hfs, hft, hf01⟩ := exists_bounded_zero_one_of_closed hs ht hd
  ⟨BoundedContinuousFunction.const X a + (b - a) • f, fun x hx => by simp [hfs hx], fun x hx => by
    simp [hft hx], fun x =>
    ⟨by dsimp; nlinarith [(hf01 x).1], by dsimp; nlinarith [(hf01 x).2]⟩⟩

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.const, exists_bounded_zero_one_of_closed
-/
theorem exists_bounded_mem_Icc_of_closed_of_le {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) {a b : Real} (hle : a <= b) :
    exists f : X ->ᵇ Real, EqOn f (Function.const X a) s ∧ EqOn f (Function.const X b) t ∧
    forall x, f x in Icc a b :=
  let ⟨f, hfs, hft, hf01⟩ := exists_bounded_zero_one_of_closed hs ht hd
  ⟨BoundedContinuousFunction.const X a + (b - a) • f, fun x hx => by simp [hfs hx], fun x hx => by
    simp [hft hx], fun x =>
    ⟨by dsimp; nlinarith [(hf01 x).1], by dsimp; nlinarith [(hf01 x).2]⟩⟩
