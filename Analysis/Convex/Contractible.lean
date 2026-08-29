/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Homotopy.Contractible

/-!
# A convex set is contractible

In this file we prove that a (star) convex set in a real topological vector space is a contractible
topological space.
-/

public section


variable {E : Type*} [AddCommGroup E] [Module Real E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul Real E] {s : Set E} {x : E}

/--
theorem `StarConvex.contractibleSpace` / 定理 `StarConvex.contractibleSpace`

English:
theorem StarConvex.contractibleSpace
  given: (h : StarConvex Real x s) (hne : s.Nonempty)
  proof: by
  refine
    (contractible_iff_id_nullhomotopic s).2 ⟨⟨x, h.mem hne⟩,
      ⟨⟨⟨fun p => ⟨p.1.1 • x + (1 - p.1.1) • (p.2 : E), ?_⟩, ?_⟩, fun x => by simp, fun x => by simp⟩⟩⟩
  · exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel _ _)
  · fun_prop

中文:
定理 StarConvex.contractibleSpace
  条件: (h : StarConvex 实数 x s) (hne : s.Nonempty)
  证明: by
  refine
    (contractible_iff_id_nullhomotopic s).2 ⟨⟨x, h.mem hne⟩,
      ⟨⟨⟨fun p => ⟨p.1.1 • x + (1 - p.1.1) • (p.2 : E), ?_⟩, ?_⟩, fun x => by simp, fun x => by simp⟩⟩⟩
  · exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel _ _)
  · fun_prop
-/
protected theorem StarConvex.contractibleSpace (h : StarConvex Real x s) (hne : s.Nonempty) :
    ContractibleSpace s := by
  refine
    (contractible_iff_id_nullhomotopic s).2 ⟨⟨x, h.mem hne⟩,
      ⟨⟨⟨fun p => ⟨p.1.1 • x + (1 - p.1.1) • (p.2 : E), ?_⟩, ?_⟩, fun x => by simp, fun x => by simp⟩⟩⟩
  · exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel _ _)
  · fun_prop

/--
theorem `Convex.contractibleSpace` / 定理 `Convex.contractibleSpace`

English:
theorem Convex.contractibleSpace
  given: (hs : Convex Real s) (hne : s.Nonempty)
  proof: let ⟨_, hx⟩ := hne
  (hs.starConvex hx).contractibleSpace hne

中文:
定理 Convex.contractibleSpace
  条件: (hs : Convex 实数 s) (hne : s.Nonempty)
  证明: let ⟨_, hx⟩ := hne
  (hs.starConvex hx).contractibleSpace hne
-/
protected theorem Convex.contractibleSpace (hs : Convex Real s) (hne : s.Nonempty) :
    ContractibleSpace s :=
  let ⟨_, hx⟩ := hne
  (hs.starConvex hx).contractibleSpace hne

instance (priority := 100) RealTopologicalVectorSpace.contractibleSpace : ContractibleSpace E :=
(Homeomorph.Set.univ E).contractibleSpace_iff.mp
    convex_univ.contractibleSpace Set.univ_nonempty
