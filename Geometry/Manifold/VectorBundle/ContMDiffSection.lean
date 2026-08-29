/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.Notation

/-!
# `C^n` sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a vector bundle over a manifold `M` and prove that it's a module over the base field.

In passing, we prove that binary and finite sums, differences and scalar products of `C^n`
sections are `C^n`.

-/

@[expose] public section


open Bundle Filter Function

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : Nat∞ω)
  (V : M -> Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [forall x : M, TopologicalSpace (V x)] [FiberBundle F V]

-- Binary and finite sums, negative, differences and scalar products of smooth sections are smooth
section operations

-- Let V be a vector bundle
variable [forall x, AddCommGroup (V x)] [forall x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

variable {I F n V}

variable {f : M -> 𝕜} {a : 𝕜} {s t : Π x : M, V x} {u : Set M} {x₀ : M}

/--
lemma `ContMDiffWithinAt.add_section` / 引理 `ContMDiffWithinAt.add_section`

English:
lemma ContMDiffWithinAt.add_section
  given: (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀)
  proof: by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx

中文:
引理 ContMDiffWithinAt.add_section
  条件: (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀)
  证明: by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, contMDiffWithinAt_section, e.baseSet, e.linear, e.open_baseSet.mem_nhds, eventually_of_mem, hs.add, linear, mem_baseSet_trivializationAt, mem_nhds, mem_nhdsWithin_of_mem_nhds, open_baseSet, trivializationAt
-/
lemma ContMDiffWithinAt.add_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) :
    CMDiffAt[u] n (T% (s + t)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).1
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1

/--
lemma `ContMDiffAt.add_section` / 引理 `ContMDiffAt.add_section`

English:
lemma ContMDiffAt.add_section
  given: (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀)
  proof: by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.add_section ht

中文:
引理 ContMDiffAt.add_section
  条件: (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀)
  证明: by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.add_section ht

Depends on / 依赖: add_section, contMDiffWithinAt_univ, hs.add_section
-/
lemma ContMDiffAt.add_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀) :
    CMDiffAt n (T% (s + t)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.add_section ht

/--
lemma `ContMDiffOn.add_section` / 引理 `ContMDiffOn.add_section`

English:
lemma ContMDiffOn.add_section
  given: (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t))
  proof: fun x₀ hx₀ => (hs x₀ hx₀).add_section (ht x₀ hx₀)

中文:
引理 ContMDiffOn.add_section
  条件: (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t))
  证明: fun x₀ hx₀ => (hs x₀ hx₀).add_section (ht x₀ hx₀)

Depends on / 依赖: add_section
-/
lemma ContMDiffOn.add_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)) :
    CMDiff[u] n (T% (s + t)) :=
  fun x₀ hx₀ => (hs x₀ hx₀).add_section (ht x₀ hx₀)

/--
lemma `ContMDiff.add_section` / 引理 `ContMDiff.add_section`

English:
lemma ContMDiff.add_section
  given: (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t))
  proof: fun x₀ => (hs x₀).add_section (ht x₀)

中文:
引理 ContMDiff.add_section
  条件: (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t))
  证明: fun x₀ => (hs x₀).add_section (ht x₀)

Depends on / 依赖: add_section
-/
lemma ContMDiff.add_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) :
    CMDiff n (T% (s + t)) :=
  fun x₀ => (hs x₀).add_section (ht x₀)

/--
lemma `ContMDiffWithinAt.neg_section` / 引理 `ContMDiffWithinAt.neg_section`

English:
lemma ContMDiffWithinAt.neg_section
  proof: by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      a

中文:
引理 ContMDiffWithinAt.neg_section
  证明: by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      a

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, contMDiffWithinAt_section, e.baseSet, e.linear, e.open_baseSet.mem_nhds, eventually_of_mem, hs.neg.congr_of_eventuallyEq, linear, map_neg, mem_baseSet_trivializationAt, mem_nhds, mem_nhdsWithin_of_mem_nhds, open_baseSet, trivializationAt
-/
lemma ContMDiffWithinAt.neg_section
    (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (-s)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).map_neg
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg

/--
lemma `ContMDiffAt.neg_section` / 引理 `ContMDiffAt.neg_section`

English:
lemma ContMDiffAt.neg_section
  given: (hs : CMDiffAt n (T% s) x₀)
  statement: CMDiffAt n (T% (-s)) x₀
  proof: by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.neg_section

中文:
引理 ContMDiffAt.neg_section
  条件: (hs : CMDiffAt n (T% s) x₀)
  结论: CMDiffAt n (T% (-s)) x₀
  证明: by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.neg_section

Depends on / 依赖: contMDiffWithinAt_univ, hs.neg_section, neg_section
-/
lemma ContMDiffAt.neg_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (-s)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.neg_section

/--
lemma `ContMDiffOn.neg_section` / 引理 `ContMDiffOn.neg_section`

English:
lemma ContMDiffOn.neg_section
  given: (hs : CMDiff[u] n (T% s))
  statement: CMDiff[u] n (T% (-s))
  proof: fun x₀ hx₀ => (hs x₀ hx₀).neg_section

中文:
引理 ContMDiffOn.neg_section
  条件: (hs : CMDiff[u] n (T% s))
  结论: CMDiff[u] n (T% (-s))
  证明: fun x₀ hx₀ => (hs x₀ hx₀).neg_section

Depends on / 依赖: neg_section
-/
lemma ContMDiffOn.neg_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (-s)) :=
  fun x₀ hx₀ => (hs x₀ hx₀).neg_section

/--
lemma `ContMDiff.neg_section` / 引理 `ContMDiff.neg_section`

English:
lemma ContMDiff.neg_section
  given: (hs : CMDiff n (T% s))
  statement: CMDiff n (T% (-s))
  proof: fun x₀ => (hs x₀).neg_section

中文:
引理 ContMDiff.neg_section
  条件: (hs : CMDiff n (T% s))
  结论: CMDiff n (T% (-s))
  证明: fun x₀ => (hs x₀).neg_section

Depends on / 依赖: neg_section
-/
lemma ContMDiff.neg_section (hs : CMDiff n (T% s)) : CMDiff n (T% (-s)) :=
  fun x₀ => (hs x₀).neg_section

/--
lemma `ContMDiffWithinAt.sub_section` / 引理 `ContMDiffWithinAt.sub_section`

English:
lemma ContMDiffWithinAt.sub_section
  given: (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀)
  proof: by
  rw [sub_eq_add_neg]
  exact hs.add_section ht.neg_section

中文:
引理 ContMDiffWithinAt.sub_section
  条件: (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀)
  证明: by
  rw [sub_eq_add_neg]
  exact hs.add_section ht.neg_section

Depends on / 依赖: add_section, hs.add_section, ht.neg_section, neg_section, sub_eq_add_neg
-/
lemma ContMDiffWithinAt.sub_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) :
    CMDiffAt[u] n (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  exact hs.add_section ht.neg_section

/--
lemma `ContMDiffAt.sub_section` / 引理 `ContMDiffAt.sub_section`

English:
lemma ContMDiffAt.sub_section
  given: (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀)
  proof: by
  rw [sub_eq_add_neg]
  apply hs.add_section ht.neg_section

中文:
引理 ContMDiffAt.sub_section
  条件: (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀)
  证明: by
  rw [sub_eq_add_neg]
  apply hs.add_section ht.neg_section

Depends on / 依赖: add_section, hs.add_section, ht.neg_section, neg_section, sub_eq_add_neg
-/
lemma ContMDiffAt.sub_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀) :
    CMDiffAt n (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  apply hs.add_section ht.neg_section

/--
lemma `ContMDiffOn.sub_section` / 引理 `ContMDiffOn.sub_section`

English:
lemma ContMDiffOn.sub_section
  given: (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t))
  proof: fun x₀ hx₀ => (hs x₀ hx₀).sub_section (ht x₀ hx₀)

中文:
引理 ContMDiffOn.sub_section
  条件: (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t))
  证明: fun x₀ hx₀ => (hs x₀ hx₀).sub_section (ht x₀ hx₀)

Depends on / 依赖: sub_section
-/
lemma ContMDiffOn.sub_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)) :
    CMDiff[u] n (T% (s - t)) :=
  fun x₀ hx₀ => (hs x₀ hx₀).sub_section (ht x₀ hx₀)

/--
lemma `ContMDiff.sub_section` / 引理 `ContMDiff.sub_section`

English:
lemma ContMDiff.sub_section
  given: (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t))
  statement: CMDiff n (T% (s - t))
  proof: fun x₀ => (hs x₀).sub_section (ht x₀)

中文:
引理 ContMDiff.sub_section
  条件: (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t))
  结论: CMDiff n (T% (s - t))
  证明: fun x₀ => (hs x₀).sub_section (ht x₀)

Depends on / 依赖: sub_section
-/
lemma ContMDiff.sub_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) : CMDiff n (T% (s - t)) :=
  fun x₀ => (hs x₀).sub_section (ht x₀)

/--
lemma `ContMDiffWithinAt.smul_section` / 引理 `ContMDiffWithinAt.smul_section`

English:
lemma ContMDiffWithinAt.smul_section
  given: (hf : CMDiffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀)
  proof: by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
 

中文:
引理 ContMDiffWithinAt.smul_section
  条件: (hf : CMDiffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀)
  证明: by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
 

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, contMDiffWithinAt_section, e.baseSet, e.linear, e.open_baseSet.mem_nhds, eventually_of_mem, hf.smul, linear, mem_baseSet_trivializationAt, mem_nhds, mem_nhdsWithin_of_mem_nhds, open_baseSet, trivializationAt
-/
lemma ContMDiffWithinAt.smul_section (hf : CMDiffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀) :
    CMDiffAt[u] n (T% (f • s)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).2
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

/--
lemma `ContMDiffAt.smul_section` / 引理 `ContMDiffAt.smul_section`

English:
lemma ContMDiffAt.smul_section
  given: (hf : CMDiffAt n f x₀) (hs : CMDiffAt n (T% s) x₀)
  proof: by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

中文:
引理 ContMDiffAt.smul_section
  条件: (hf : CMDiffAt n f x₀) (hs : CMDiffAt n (T% s) x₀)
  证明: by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

Depends on / 依赖: contMDiffWithinAt_univ, smul_section
-/
lemma ContMDiffAt.smul_section (hf : CMDiffAt n f x₀) (hs : CMDiffAt n (T% s) x₀) :
    CMDiffAt n (T% (f • s)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

/--
lemma `ContMDiffOn.smul_section` / 引理 `ContMDiffOn.smul_section`

English:
lemma ContMDiffOn.smul_section
  given: (hf : CMDiff[u] n f) (hs : CMDiff[u] n (T% s))
  proof: fun x₀ hx₀ => (hf x₀ hx₀).smul_section (hs x₀ hx₀)

中文:
引理 ContMDiffOn.smul_section
  条件: (hf : CMDiff[u] n f) (hs : CMDiff[u] n (T% s))
  证明: fun x₀ hx₀ => (hf x₀ hx₀).smul_section (hs x₀ hx₀)

Depends on / 依赖: smul_section
-/
lemma ContMDiffOn.smul_section (hf : CMDiff[u] n f) (hs : CMDiff[u] n (T% s)) :
    CMDiff[u] n (T% (f • s)) :=
  fun x₀ hx₀ => (hf x₀ hx₀).smul_section (hs x₀ hx₀)

/--
lemma `ContMDiff.smul_section` / 引理 `ContMDiff.smul_section`

English:
lemma ContMDiff.smul_section
  given: (hf : CMDiff n f) (hs : CMDiff n (T% s))
  statement: CMDiff n (T% (f • s))
  proof: fun x₀ => (hf x₀).smul_section (hs x₀)

中文:
引理 ContMDiff.smul_section
  条件: (hf : CMDiff n f) (hs : CMDiff n (T% s))
  结论: CMDiff n (T% (f • s))
  证明: fun x₀ => (hf x₀).smul_section (hs x₀)

Depends on / 依赖: smul_section
-/
lemma ContMDiff.smul_section (hf : CMDiff n f) (hs : CMDiff n (T% s)) : CMDiff n (T% (f • s)) :=
  fun x₀ => (hf x₀).smul_section (hs x₀)

/--
lemma `ContMDiffWithinAt.const_smul_section` / 引理 `ContMDiffWithinAt.const_smul_section`

English:
lemma ContMDiffWithinAt.const_smul_section
  proof: contMDiffWithinAt_const.smul_section hs

中文:
引理 ContMDiffWithinAt.const_smul_section
  证明: contMDiffWithinAt_const.smul_section hs

Depends on / 依赖: contMDiffWithinAt_const, contMDiffWithinAt_const.smul_section, smul_section
-/
lemma ContMDiffWithinAt.const_smul_section
    (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (a • s)) x₀ :=
  contMDiffWithinAt_const.smul_section hs

/--
lemma `ContMDiffAt.const_smul_section` / 引理 `ContMDiffAt.const_smul_section`

English:
lemma ContMDiffAt.const_smul_section
  given: (hs : CMDiffAt n (T% s) x₀)
  statement: CMDiffAt n (T% (a • s)) x₀
  proof: contMDiffAt_const.smul_section hs

中文:
引理 ContMDiffAt.const_smul_section
  条件: (hs : CMDiffAt n (T% s) x₀)
  结论: CMDiffAt n (T% (a • s)) x₀
  证明: contMDiffAt_const.smul_section hs

Depends on / 依赖: contMDiffAt_const, contMDiffAt_const.smul_section, smul_section
-/
lemma ContMDiffAt.const_smul_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (a • s)) x₀ :=
  contMDiffAt_const.smul_section hs

/--
lemma `ContMDiffOn.const_smul_section` / 引理 `ContMDiffOn.const_smul_section`

English:
lemma ContMDiffOn.const_smul_section
  given: (hs : CMDiff[u] n (T% s))
  statement: CMDiff[u] n (T% (a • s))
  proof: contMDiffOn_const.smul_section hs

中文:
引理 ContMDiffOn.const_smul_section
  条件: (hs : CMDiff[u] n (T% s))
  结论: CMDiff[u] n (T% (a • s))
  证明: contMDiffOn_const.smul_section hs

Depends on / 依赖: contMDiffOn_const, contMDiffOn_const.smul_section, smul_section
-/
lemma ContMDiffOn.const_smul_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (a • s)) :=
  contMDiffOn_const.smul_section hs

/--
lemma `ContMDiff.const_smul_section` / 引理 `ContMDiff.const_smul_section`

English:
lemma ContMDiff.const_smul_section
  given: (hs : CMDiff n (T% s))
  statement: CMDiff n (T% (a • s))
  proof: fun x₀ => (hs x₀).const_smul_section

中文:
引理 ContMDiff.const_smul_section
  条件: (hs : CMDiff n (T% s))
  结论: CMDiff n (T% (a • s))
  证明: fun x₀ => (hs x₀).const_smul_section

Depends on / 依赖: const_smul_section
-/
lemma ContMDiff.const_smul_section (hs : CMDiff n (T% s)) : CMDiff n (T% (a • s)) :=
  fun x₀ => (hs x₀).const_smul_section

variable {ι : Type*} {t : ι -> (x : M) -> V x}

/--
lemma `ContMDiffWithinAt.sum_section` / 引理 `ContMDiffWithinAt.sum_section`

English:
lemma ContMDiffWithinAt.sum_section
  statement: {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using! contMDiffWithinAt_zeroSection ..
  | insert i s hi h =>
    simp only [Finset.sum_insert hi]
    apply (hs _ (s.mem_insert_self i)).add_section
    exact h fun i a => hs _ (s.mem_insert_

中文:
引理 ContMDiffWithinAt.sum_section
  结论: {s : Finset ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using! contMDiffWithinAt_zeroSection ..
  | insert i s hi h =>
    simp only [Finset.sum_insert hi]
    apply (hs _ (s.mem_insert_self i)).add_section
    exact h fun i a => hs _ (s.mem_insert_

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_empty, Finset.sum_insert, add_section, classical, contMDiffWithinAt_zeroSection, induction_on, insert, mem_insert_of_mem, mem_insert_self, s.mem_insert_of_mem, s.mem_insert_self, sum_empty, sum_insert
-/
lemma ContMDiffWithinAt.sum_section {s : Finset ι}
    (hs : forall i in s, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x => (∑ i in s, (t i x)))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using! contMDiffWithinAt_zeroSection ..
  | insert i s hi h =>
    simp only [Finset.sum_insert hi]
    apply (hs _ (s.mem_insert_self i)).add_section
    exact h fun i a => hs _ (s.mem_insert_of_mem a)

/--
lemma `ContMDiffAt.sum_section` / 引理 `ContMDiffAt.sum_section`

English:
lemma ContMDiffAt.sum_section
  statement: {s : Finset ι}
  proof: by
  simp_rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .sum_section hs

中文:
引理 ContMDiffAt.sum_section
  结论: {s : Finset ι}
  证明: by
  simp_rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .sum_section hs

Depends on / 依赖: contMDiffWithinAt_univ, simp_rw, sum_section
-/
lemma ContMDiffAt.sum_section {s : Finset ι}
    (hs : forall i in s, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x => (∑ i in s, (t i x)))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .sum_section hs

/--
lemma `ContMDiffOn.sum_section` / 引理 `ContMDiffOn.sum_section`

English:
lemma ContMDiffOn.sum_section
  statement: {s : Finset ι}
  proof: fun x₀ hx₀ => .sum_section fun i hi => hs i hi x₀ hx₀

中文:
引理 ContMDiffOn.sum_section
  结论: {s : Finset ι}
  证明: fun x₀ hx₀ => .sum_section fun i hi => hs i hi x₀ hx₀

Depends on / 依赖: sum_section
-/
lemma ContMDiffOn.sum_section {s : Finset ι}
    (hs : forall i in s, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x => (∑ i in s, (t i x)))) :=
  fun x₀ hx₀ => .sum_section fun i hi => hs i hi x₀ hx₀

/--
lemma `ContMDiff.sum_section` / 引理 `ContMDiff.sum_section`

English:
lemma ContMDiff.sum_section
  given: {s : Finset ι} (hs : forall i in s, CMDiff n (T% (t i ·)))
  proof: fun x₀ => .sum_section fun i hi => (hs i hi) x₀

中文:
引理 ContMDiff.sum_section
  条件: {s : Finset ι} (hs : 对任意 i in s, CMDiff n (T% (t i ·)))
  证明: fun x₀ => .sum_section fun i hi => (hs i hi) x₀

Depends on / 依赖: sum_section
-/
lemma ContMDiff.sum_section {s : Finset ι} (hs : forall i in s, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x => (∑ i in s, (t i x)))) :=
  fun x₀ => .sum_section fun i hi => (hs i hi) x₀

/--
lemma `ContMDiffOn.smul_section_of_tsupport` / 引理 `ContMDiffOn.smul_section_of_tsupport`

English:
lemma ContMDiffOn.smul_section_of_tsupport
  statement: {s : Π (x : M), V x} {ψ : M -> 𝕜} (hψ : CMDiff[u] n ψ)
  proof: by
  apply contMDiff_of_contMDiffOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
· exact Set.

中文:
引理 ContMDiffOn.smul_section_of_tsupport
  结论: {s : Π (x : M), V x} {ψ : M -> 𝕜} (hψ : CMDiff[u] n ψ)
  证明: by
  apply contMDiff_of_contMDiffOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
· exact Set.

Depends on / 依赖: Set.compl_subset_compl.mpr, Set.compl_subset_iff_union.mp, compl_subset_compl, compl_subset_iff_union, contMDiffOn, contMDiff_of_contMDiffOn_union_of_isOpen, contMDiff_zeroSection, image_eq_zero_of_notMem_tsupport, isClosed_tsupport, isOpen_compl_iff, isOpen_compl_iff.mpr, smul_section, tsupport, zeroSection
-/
lemma ContMDiffOn.smul_section_of_tsupport {s : Π (x : M), V x} {ψ : M -> 𝕜} (hψ : CMDiff[u] n ψ)
    (ht : IsOpen u) (ht' : tsupport ψ subseteq u) (hs : CMDiff[u] n (T% s)) :
    CMDiff n (T% (ψ • s)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
· exact Set.compl_subset_iff_union.mp Set.compl_subset_compl.mpr ht'

/--
lemma `ContMDiffWithinAt.sum_section_of_locallyFinite` / 引理 `ContMDiffWithinAt.sum_section_of_locallyFinite`

English:
lemma ContMDiffWithinAt.sum_section_of_locallyFinite
  proof: by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i => {x | t i x != 0}) i inter u').Nonempty}
  have := hfin.fintype
  have : CMDiffAt

中文:
引理 ContMDiffWithinAt.sum_section_of_locallyFinite
  证明: by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i => {x | t i x != 0}) i inter u').Nonempty}
  have := hfin.fintype
  have : CMDiffAt
-/
lemma ContMDiffWithinAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x => ∑' i, (t i x))) x₀ := by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i => {x | t i x != 0}) i inter u').Nonempty}
  have := hfin.fintype
  have : CMDiffAt[u inter u'] n (T% (fun x => (∑ i in s, (t i x)))) x₀ :=
    .sum_section fun i hi => ((ht' i).mono Set.inter_subset_left)
  apply (contMDiffWithinAt_inter hu').mp
  apply this.congr fun y hy => ?_
  · rw [TotalSpace.mk_inj, tsum_eq_sum']
    refine support_subset_iff'.mpr fun i hi => ?_
    by_contra! h
    have : i in s.toFinset := by
      refine Set.mem_toFinset.mpr ?_
      simp only [s, ne_eq, Set.mem_ofPred_eq]
      use x₀
      simpa using ⟨h, mem_of_mem_nhds hu'⟩
    exact hi this
  rw [TotalSpace.mk_inj]; rw [tsum_eq_sum']
  refine support_subset_iff'.mpr fun i hi => ?_
  by_contra! h
  have : i in s.toFinset := by
    refine Set.mem_toFinset.mpr ?_
    simp only [s, ne_eq, Set.mem_ofPred_eq]
    use y
    simpa using ⟨h, Set.mem_of_mem_inter_right hy⟩
  exact hi this

/--
lemma `ContMDiffAt.sum_section_of_locallyFinite` / 引理 `ContMDiffAt.sum_section_of_locallyFinite`

English:
lemma ContMDiffAt.sum_section_of_locallyFinite
  statement: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  proof: by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

中文:
引理 ContMDiffAt.sum_section_of_locallyFinite
  结论: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  证明: by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

Depends on / 依赖: contMDiffWithinAt_univ, simp_rw, sum_section_of_locallyFinite
-/
lemma ContMDiffAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x => (∑' i, (t i x)))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

/--
lemma `ContMDiffOn.sum_section_of_locallyFinite` / 引理 `ContMDiffOn.sum_section_of_locallyFinite`

English:
lemma ContMDiffOn.sum_section_of_locallyFinite
  statement: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  proof: fun x hx => .sum_section_of_locallyFinite ht (ht' · x hx)

中文:
引理 ContMDiffOn.sum_section_of_locallyFinite
  结论: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  证明: fun x hx => .sum_section_of_locallyFinite ht (ht' · x hx)

Depends on / 依赖: Aux_single, Matrix, Matrix.toLinearMap, sum_section_of_locallyFinite
-/
lemma ContMDiffOn.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x => ∑' i, (t i x))) :=
  fun x hx => .sum_section_of_locallyFinite ht (ht' · x hx)

/--
lemma `ContMDiff.sum_section_of_locallyFinite` / 引理 `ContMDiff.sum_section_of_locallyFinite`

English:
lemma ContMDiff.sum_section_of_locallyFinite
  statement: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  proof: fun x => .sum_section_of_locallyFinite ht fun i => ht' i x

中文:
引理 ContMDiff.sum_section_of_locallyFinite
  结论: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  证明: fun x => .sum_section_of_locallyFinite ht fun i => ht' i x

Depends on / 依赖: sum_section_of_locallyFinite
-/
lemma ContMDiff.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x => ∑' i, (t i x))) :=
  fun x => .sum_section_of_locallyFinite ht fun i => ht' i x

-- Future: the next four lemmas can presumably be generalised, but some hypotheses on the supports
-- of the sections `t i` are necessary.
/--
lemma `ContMDiffWithinAt.finsum_section_of_locallyFinite` / 引理 `ContMDiffWithinAt.finsum_section_of_locallyFinite`

English:
lemma ContMDiffWithinAt.finsum_section_of_locallyFinite
  proof: by
  apply (ContMDiffWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy => ?_) (by grind) trivial
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ι)]
  choose U hu hfin using ht y
  have : {x | t x y != 0} subseteq {i | ((fun i => {x | t i x != 0}) i inte

中文:
引理 ContMDiffWithinAt.finsum_section_of_locallyFinite
  证明: by
  apply (ContMDiffWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy => ?_) (by grind) trivial
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ι)]
  choose U hu hfin using ht y
  have : {x | t x y != 0} subseteq {i | ((fun i => {x | t i x != 0}) i inte

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.sum_section_of_locallyFinite, Finite, Nonempty, Set.Finite.subset, Set.mem_ofPred, Set.univ, SummationFilter, SummationFilter.unconditional, mem_ofPred, mem_of_mem_nhds, subset, subseteq, sum_section_of_locallyFinite, tsum_eq_finsum, unconditional
-/
lemma ContMDiffWithinAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x => ∑ᶠ i, t i x)) x₀ := by
  apply (ContMDiffWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy => ?_) (by grind) trivial
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ι)]
  choose U hu hfin using ht y
  have : {x | t x y != 0} subseteq {i | ((fun i => {x | t i x != 0}) i inter U).Nonempty} := by
    intro x hx
    rw [Set.mem_ofPred] at hx ⊢
    use y
    simpa using ⟨hx, mem_of_mem_nhds hu⟩
  exact Set.Finite.subset hfin this

/--
lemma `ContMDiffAt.finsum_section_of_locallyFinite` / 引理 `ContMDiffAt.finsum_section_of_locallyFinite`

English:
lemma ContMDiffAt.finsum_section_of_locallyFinite
  proof: by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

中文:
引理 ContMDiffAt.finsum_section_of_locallyFinite
  证明: by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

Depends on / 依赖: contMDiffWithinAt_univ, finsum_section_of_locallyFinite, simp_rw
-/
lemma ContMDiffAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x => ∑ᶠ i, t i x)) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

/--
lemma `ContMDiffOn.finsum_section_of_locallyFinite` / 引理 `ContMDiffOn.finsum_section_of_locallyFinite`

English:
lemma ContMDiffOn.finsum_section_of_locallyFinite
  proof: fun x hx => .finsum_section_of_locallyFinite ht fun i => ht' i x hx

中文:
引理 ContMDiffOn.finsum_section_of_locallyFinite
  证明: fun x hx => .finsum_section_of_locallyFinite ht fun i => ht' i x hx

Depends on / 依赖: finsum_section_of_locallyFinite
-/
lemma ContMDiffOn.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x => ∑ᶠ i, t i x)) :=
  fun x hx => .finsum_section_of_locallyFinite ht fun i => ht' i x hx

/--
lemma `ContMDiff.finsum_section_of_locallyFinite` / 引理 `ContMDiff.finsum_section_of_locallyFinite`

English:
lemma ContMDiff.finsum_section_of_locallyFinite
  statement: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  proof: fun x => .finsum_section_of_locallyFinite ht fun i => ht' i x

中文:
引理 ContMDiff.finsum_section_of_locallyFinite
  结论: (ht : LocallyFinite fun i => {x : M | t i x != 0})
  证明: fun x => .finsum_section_of_locallyFinite ht fun i => ht' i x

Depends on / 依赖: BilinForm, BilinForm.toMatrix, finsum_section_of_locallyFinite, toMatrix
-/
lemma ContMDiff.finsum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : M | t i x != 0})
    (ht' : forall i, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x => ∑ᶠ i, t i x)) :=
  fun x => .finsum_section_of_locallyFinite ht fun i => ht' i x

end operations

/--
Definition of `ContMDiffSection` / `ContMDiffSection` 的定义

English:
structure ContMDiffSection
  parameters: where
  axioms and operations (2):
    - toFun : forall x, V x
    - contMDiff_toFun : CMDiff n (T% toFun)

中文:
结构 ContMDiffSection
  参数: where
  公理与运算 (2 个):
    - toFun : 对任意 x, V x
    - contMDiff_toFun : CMDiff n (T% toFun)
-/
structure ContMDiffSection where
  /-- the underlying function of this section -/
  protected toFun : forall x, V x
  /-- proof that this section is `C^n` -/
  protected contMDiff_toFun : CMDiff n (T% toFun)

@[inherit_doc] scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {n} {F} {V}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DFunLike Cₛ^n⟮I; F, V⟯ M V
  body: ContMDiffSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

中文:
实例 :
  签名: DFunLike Cₛ^n⟮I; F, V⟯ M V
  定义体: ContMDiffSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

Depends on / 依赖: ContMDiffSection, ContMDiffSection.toFun, Matrix, Matrix.toLinearMap, _apply, mul_comm, mul_left_comm, smul_eq_mul
-/
instance : DFunLike Cₛ^n⟮I; F, V⟯ M V where
  coe := ContMDiffSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
/--
theorem `coeFn_mk` / 定理 `coeFn_mk`

English:
theorem coeFn_mk
  given: (s : forall x, V x) (hs : CMDiff n (T% s))
  statement: (mk s hs : forall x, V x) = s
  proof: rfl

中文:
定理 coeFn_mk
  条件: (s : 对任意 x, V x) (hs : CMDiff n (T% s))
  结论: (mk s hs : 对任意 x, V x) = s
  证明: rfl

Depends on / 依赖: Matrix, Matrix.toLinearMap, _apply
-/
theorem coeFn_mk (s : forall x, V x) (hs : CMDiff n (T% s)) : (mk s hs : forall x, V x) = s := rfl

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  given: (s : Cₛ^n⟮I; F, V⟯)
  statement: CMDiff n (T% fun x => s x)
  proof: s.contMDiff_toFun

中文:
定理 contMDiff
  条件: (s : Cₛ^n⟮I; F, V⟯)
  结论: CMDiff n (T% fun x => s x)
  证明: s.contMDiff_toFun

Depends on / 依赖: Matrix, Matrix.toBilin, Pi.single_apply, _apply, single_apply, toBilin
-/
protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) : CMDiff n (T% fun x => s x) :=
  s.contMDiff_toFun

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: ⦃s t
  statement: Cₛ^n⟮I; F, V⟯⦄ (h : (s : forall x, V x) = t) : s = t
  proof: DFunLike.ext' h

中文:
定理 coe_inj
  条件: ⦃s t
  结论: Cₛ^n⟮I; F, V⟯⦄ (h : (s : 对任意 x, V x) = t) : s = t
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : forall x, V x) = t) : s = t :=
  DFunLike.ext' h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Cₛ^n⟮I; F, V⟯ -> forall x, V x)
  proof: coe_inj

@[ext]

中文:
定理 coe_injective
  结论: Injective ((↑) : Cₛ^n⟮I; F, V⟯ -> 对任意 x, V x)
  证明: coe_inj

@[ext]

Depends on / 依赖: BilinForm, BilinForm.toMatrix, coe_inj, symm_symm, toMatrix
-/
theorem coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ -> forall x, V x) :=
  coe_inj

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, s x = t x)
  statement: s = t
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: (h : 对任意 x, s x = t x)
  结论: s = t
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext, Matrix, Matrix.toBilin, apply_symm_apply, toBilin
-/
theorem ext (h : forall x, s x = t x) : s = t := DFunLike.ext _ _ h

section
variable [forall x, AddCommGroup (V x)] [forall x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add Cₛ^n⟮I; F, V⟯
  body: ⟨fun s t => ⟨s + t, s.contMDiff.add_section t.contMDiff⟩⟩

@[simp]

中文:
实例 instAdd
  签名: : Add Cₛ^n⟮I; F, V⟯
  定义体: ⟨fun s t => ⟨s + t, s.contMDiff.add_section t.contMDiff⟩⟩

@[simp]

Depends on / 依赖: add_section, contMDiff, s.contMDiff.add_section, t.contMDiff
-/
instance instAdd : Add Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t => ⟨s + t, s.contMDiff.add_section t.contMDiff⟩⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (s t : Cₛ^n⟮I; F, V⟯)
  statement: ⇑(s + t) = ⇑s + t
  proof: rfl

中文:
定理 coe_add
  条件: (s t : Cₛ^n⟮I; F, V⟯)
  结论: ⇑(s + t) = ⇑s + t
  证明: rfl

Depends on / 依赖: LinearMap, LinearMap.toMatrix, _apply
-/
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t :=
  rfl

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub Cₛ^n⟮I; F, V⟯
  body: ⟨fun s t => ⟨s - t, s.contMDiff.sub_section t.contMDiff⟩⟩

@[simp]

中文:
实例 instSub
  签名: : Sub Cₛ^n⟮I; F, V⟯
  定义体: ⟨fun s t => ⟨s - t, s.contMDiff.sub_section t.contMDiff⟩⟩

@[simp]

Depends on / 依赖: B.toMatrix, contMDiff, s.contMDiff.sub_section, sub_section, t.contMDiff
-/
instance instSub : Sub Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t => ⟨s - t, s.contMDiff.sub_section t.contMDiff⟩⟩

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (s t : Cₛ^n⟮I; F, V⟯)
  statement: ⇑(s - t) = s - t
  proof: rfl

中文:
定理 coe_sub
  条件: (s t : Cₛ^n⟮I; F, V⟯)
  结论: ⇑(s - t) = s - t
  证明: rfl

Depends on / 依赖: B.toMatrix, _comp
-/
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero Cₛ^n⟮I; F, V⟯
  body: ⟨⟨fun _ => 0, (contMDiff_zeroSection 𝕜 V).of_le le_top⟩⟩

中文:
实例 instZero
  签名: : Zero Cₛ^n⟮I; F, V⟯
  定义体: ⟨⟨fun _ => 0, (contMDiff_zeroSection 𝕜 V).of_le le_top⟩⟩

Depends on / 依赖: B.toMatrix, contMDiff_zeroSection, le_top, of_le
-/
instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun _ => 0, (contMDiff_zeroSection 𝕜 V).of_le le_top⟩⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited Cₛ^n⟮I; F, V⟯
  body: ⟨0⟩

@[simp]

中文:
实例 inhabited
  签名: : Inhabited Cₛ^n⟮I; F, V⟯
  定义体: ⟨0⟩

@[simp]
-/
instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0
  证明: rfl

Depends on / 依赖: LinearMap, LinearMap.mul_toMatrix, mul_toMatrix
-/
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg Cₛ^n⟮I; F, V⟯
  body: ⟨fun s => ⟨-s, s.contMDiff.neg_section⟩⟩

@[simp]

中文:
实例 instNeg
  签名: : Neg Cₛ^n⟮I; F, V⟯
  定义体: ⟨fun s => ⟨-s, s.contMDiff.neg_section⟩⟩

@[simp]

Depends on / 依赖: B.toMatrix, _mul, contMDiff, neg_section, s.contMDiff.neg_section
-/
instance instNeg : Neg Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s => ⟨-s, s.contMDiff.neg_section⟩⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (s : Cₛ^n⟮I; F, V⟯)
  statement: ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s
  proof: rfl

中文:
定理 coe_neg
  条件: (s : Cₛ^n⟮I; F, V⟯)
  结论: ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s
  证明: rfl

Depends on / 依赖: BilinForm, BilinForm.toMatrix, _comp, _toBilin, _toLin, injective, toMatrix
-/
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl

/--
Instance `instNSMul` / 实例 `instNSMul`

English:
instance instNSMul
  signature: : SMul Nat Cₛ^n⟮I; F, V⟯
  body: ⟨nsmulRec⟩

@[simp]

中文:
实例 instNSMul
  签名: : SMul 自然数 Cₛ^n⟮I; F, V⟯
  定义体: ⟨nsmulRec⟩

@[simp]

Depends on / 依赖: nsmulRec
-/
instance instNSMul : SMul Nat Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩

@[simp]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (s : Cₛ^n⟮I; F, V⟯) (k : Nat)
  statement: ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s
  proof: by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

中文:
定理 coe_nsmul
  条件: (s : Cₛ^n⟮I; F, V⟯) (k : 自然数)
  结论: ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s
  证明: by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

Depends on / 依赖: simp_rw, succ_nsmul, zero_smul
-/
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : Nat) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

/--
Instance `instZSMul` / 实例 `instZSMul`

English:
instance instZSMul
  signature: : SMul Int Cₛ^n⟮I; F, V⟯
  body: ⟨zsmulRec⟩

@[simp]

中文:
实例 instZSMul
  签名: : SMul 整数 Cₛ^n⟮I; F, V⟯
  定义体: ⟨zsmulRec⟩

@[simp]

Depends on / 依赖: zsmulRec
-/
instance instZSMul : SMul Int Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩

@[simp]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (s : Cₛ^n⟮I; F, V⟯) (z : Int)
  statement: ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s
  proof: by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

中文:
定理 coe_zsmul
  条件: (s : Cₛ^n⟮I; F, V⟯) (z : 整数)
  结论: ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s
  证明: by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

Depends on / 依赖: Int.ofNat_eq_natCast, Neg.neg, coe_nsmul, congr_arg, natCast_zsmul, negSucc_zsmul, ofNat_eq_natCast
-/
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : Int) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s := by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup Cₛ^n⟮I; F, V⟯
  body: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

中文:
实例 instAddCommGroup
  签名: : AddCommGroup Cₛ^n⟮I; F, V⟯
  定义体: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

Depends on / 依赖: addCommGroup, coe_add, coe_injective, coe_injective.addCommGroup, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul
-/
instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul 𝕜 Cₛ^n⟮I; F, V⟯
  body: ⟨fun c s => ⟨c • ⇑s, s.contMDiff.const_smul_section⟩⟩

@[simp]

中文:
实例 instSMul
  签名: : SMul 𝕜 Cₛ^n⟮I; F, V⟯
  定义体: ⟨fun c s => ⟨c • ⇑s, s.contMDiff.const_smul_section⟩⟩

@[simp]

Depends on / 依赖: const_smul_section, contMDiff, s.contMDiff.const_smul_section
-/
instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ :=
  ⟨fun c s => ⟨c • ⇑s, s.contMDiff.const_smul_section⟩⟩

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯)
  statement: ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s
  proof: rfl

中文:
定理 coe_smul
  条件: (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯)
  结论: ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s
  证明: rfl
-/
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s :=
  rfl

variable (I F V n) in
/--
Definition of `coeAddHom` / `coeAddHom` 的定义

English:
definition coeAddHom
  signature: : Cₛ^n⟮I; F, V⟯ ->+ forall x, V x where
  body: (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

中文:
定义 coeAddHom
  签名: : Cₛ^n⟮I; F, V⟯ ->+ 对任意 x, V x where
  定义体: (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
-/
def coeAddHom : Cₛ^n⟮I; F, V⟯ ->+ forall x, V x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/--
theorem `coeAddHom_apply` / 定理 `coeAddHom_apply`

English:
theorem coeAddHom_apply
  given: (s : Cₛ^n⟮I; F, V⟯)
  statement: coeAddHom I F n V s = s
  proof: rfl

中文:
定理 coeAddHom_apply
  条件: (s : Cₛ^n⟮I; F, V⟯)
  结论: coeAddHom I F n V s = s
  证明: rfl
-/
theorem coeAddHom_apply (s : Cₛ^n⟮I; F, V⟯) : coeAddHom I F n V s = s := rfl

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module 𝕜 Cₛ^n⟮I; F, V⟯
  body: coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

中文:
实例 instModule
  签名: : Module 𝕜 Cₛ^n⟮I; F, V⟯
  定义体: coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

Depends on / 依赖: coeAddHom, coe_injective, coe_injective.module, coe_smul, module
-/
instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

end

/--
theorem `mdifferentiable'` / 定理 `mdifferentiable'`

English:
theorem mdifferentiable'
  given: (s : Cₛ^n⟮I; F, V⟯) (hn : n != 0)
  statement: MDiff (T% fun x => s x)
  proof: s.contMDiff.mdifferentiable hn

中文:
定理 mdifferentiable'
  条件: (s : Cₛ^n⟮I; F, V⟯) (hn : n != 0)
  结论: MDiff (T% fun x => s x)
  证明: s.contMDiff.mdifferentiable hn
-/
protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : n != 0) : MDiff (T% fun x => s x) :=
  s.contMDiff.mdifferentiable hn

/--
theorem `mdifferentiable` / 定理 `mdifferentiable`

English:
theorem mdifferentiable
  given: (s : Cₛ^∞⟮I; F, V⟯)
  statement: MDiff (T% fun x => s x)
  proof: s.contMDiff.mdifferentiable (by simp)

中文:
定理 mdifferentiable
  条件: (s : Cₛ^∞⟮I; F, V⟯)
  结论: MDiff (T% fun x => s x)
  证明: s.contMDiff.mdifferentiable (by simp)
-/
protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) : MDiff (T% fun x => s x) :=
  s.contMDiff.mdifferentiable (by simp)

/--
theorem `mdifferentiableAt` / 定理 `mdifferentiableAt`

English:
theorem mdifferentiableAt
  given: (s : Cₛ^∞⟮I; F, V⟯) {x}
  statement: MDiffAt (T% fun x => s x) x
  proof: s.mdifferentiable x

中文:
定理 mdifferentiableAt
  条件: (s : Cₛ^∞⟮I; F, V⟯) {x}
  结论: MDiffAt (T% fun x => s x) x
  证明: s.mdifferentiable x
-/
protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} : MDiffAt (T% fun x => s x) x :=
  s.mdifferentiable x

end ContMDiffSection
