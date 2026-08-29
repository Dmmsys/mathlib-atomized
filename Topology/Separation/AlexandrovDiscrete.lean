/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.AlexandrovDiscrete

/-!
# T1 Alexandrov-discrete topology is discrete
-/

public section

open Filter

variable {X : Type*} [TopologicalSpace X]

@[simp]
/--
lemma `nhdsKer_eq_of_t1Space` / 引理 `nhdsKer_eq_of_t1Space`

English:
lemma nhdsKer_eq_of_t1Space
  given: [T1Space X] (s : Set X)
  statement: nhdsKer s = s
  proof: by
  ext; simp [mem_nhdsKer_iff_specializes]

中文:
引理 nhdsKer_eq_of_t1Space
  条件: [T1空间 X] (s : 集合 X)
  结论: nhdsKer s = s
  证明: by
  ext; simp [mem_nhdsKer_iff_specializes]

Depends on / 依赖: mem_nhdsKer_iff_specializes
-/
lemma nhdsKer_eq_of_t1Space [T1Space X] (s : Set X) : nhdsKer s = s := by
  ext; simp [mem_nhdsKer_iff_specializes]

instance (priority := low) [AlexandrovDiscrete X] [T1Space X] : DiscreteTopology X := by
  simp [discreteTopology_iff_nhds, ← principal_nhdsKer_singleton]
