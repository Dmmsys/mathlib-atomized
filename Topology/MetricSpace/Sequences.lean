/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Sequential compacts in metric spaces

In this file we prove 2 versions of Bolzano-Weierstrass theorem for proper metric spaces.
-/

public section

open Filter Bornology Metric
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

variable [ProperSpace X] {s : Set X}

/--
theorem `tendsto_subseq_of_frequently_bounded` / 定理 `tendsto_subseq_of_frequently_bounded`

English:
theorem tendsto_subseq_of_frequently_bounded
  statement: (hs : IsBounded s) {x : Nat -> X}
  proof: have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : existsᶠ n in atTop, x n in closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

中文:
定理 tendsto_subseq_of_frequently_bounded
  结论: (hs : IsBounded s) {x : 自然数 -> X}
  证明: have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : existsᶠ n in atTop, x n in closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

Depends on / 依赖: IsSeqCompact, closure, hcs.subseq_of_frequently_in, hs.isCompact_closure.isSeqCompact, hx.mono, isCompact_closure, isSeqCompact, subseq_of_frequently_in, subset_closure
-/
theorem tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : Nat -> X}
    (hx : existsᶠ n in atTop, x n in s) :
    exists a in closure s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : existsᶠ n in atTop, x n in closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

/--
theorem `tendsto_subseq_of_bounded` / 定理 `tendsto_subseq_of_bounded`

English:
theorem tendsto_subseq_of_bounded
  given: (hs : IsBounded s) {x : Nat -> X} (hx : forall n, x n in s)
  proof: tendsto_subseq_of_frequently_bounded hs Frequently.of_forall hx

中文:
定理 tendsto_subseq_of_bounded
  条件: (hs : IsBounded s) {x : 自然数 -> X} (hx : 对任意 n, x n in s)
  证明: tendsto_subseq_of_frequently_bounded hs Frequently.of_forall hx

Depends on / 依赖: Frequently, Frequently.of_forall, of_forall, tendsto_subseq_of_frequently_bounded
-/
theorem tendsto_subseq_of_bounded (hs : IsBounded s) {x : Nat -> X} (hx : forall n, x n in s) :
    exists a in closure s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
tendsto_subseq_of_frequently_bounded hs Frequently.of_forall hx
