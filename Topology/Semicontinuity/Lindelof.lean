/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Envelopes of Semicontinuous functions on Hereditarily Lindelöf spaces

In this file, we show that, if `X` is a hereditarily Lindelöf space and `𝓕` is any family
of upper semicontinuous functions on `X`, then there is a countable subfamily `𝓕'`
with the same infimum / lower envelope. Most importantly, this applies whenever `X` has a
`SecondCountableTopology`.

The codomain `E` of the functions is assumed to be linearly ordered, and to admit a countable
order-dense subset. In particular we do not assume that arbitrary infima exist in `E`, so our
result is of the form "if `IsGLB 𝓕 s`, then there is a countable `𝓕' ⊆ 𝓕` such that `IsGLB 𝓕' s`".

Of course we also provide the dual statements for lower semicontinuous functions.

## Implementation Notes

There is currently no way to state the hypothesis "`E` admits a countable order-dense subset"
which would be inferrable by typeclass inference. Instead, we assume
`[TopologicalSpace E] [OrderClosedTopology E] [DenselyOrdered E] [SeparableSpace E]`, and
use `Dense.exists_between` to show that a chosen countable dense subset is order-dense.

This is not completely satisfying because the hypotheses on `E` should be purely order-theoretic,
but in practice `E` is either `Real`, `NNReal`, `ENNReal` or `EReal`, all of which are already
equipped with the order topology.

## References

* [N. Bourbaki, *Topologie Générale*, Chapitre IX, Appendice I][bourbaki1974] (this appendix does
  not seem to exist in the English translation)
-/

public section

open Set TopologicalSpace

variable {X E : Type*} [TopologicalSpace X] [HereditarilyLindelofSpace X] [LinearOrder E]
  [TopologicalSpace E] [OrderClosedTopology E] [DenselyOrdered E] [SeparableSpace E]
-- Note: we shouldn't really need a topology on `E`: we just want the conclusion of
-- `SeparableSpace` + `Dense.exists_between`.

/--
theorem `exists_countable_upperSemicontinuous_isGLB` / 定理 `exists_countable_upperSemicontinuous_isGLB`

English:
theorem exists_countable_upperSemicontinuous_isGLB
  statement: {s : X -> E} {𝓕 : Set (X -> E)}
  proof: by
  simp_rw [isGLB_pi] at *
  rcases exists_countable_dense E with ⟨D, D_count, D_dense⟩
  let U (f : X -> E) (d : E) : Set X := {x | f x < d}
.isOpen_preimage d have U_open {f} (hf : f in 𝓕) (d : E) : IsOpen (U f d) := h𝓕_cont f hf
  have (d : E) : {x | s x < d} = ⋃ f : 𝓕, U f d := by
    ext x
    simp [U, isGLB_lt_iff (h𝓕 x)]
  have (d : E) : exists A subseteq 𝓕, A.Countable ∧ {x | s x < d} = ⋃ f in A, U f d := by
    simp_rw [this d]
    rcases eq_open_union_countable (fun f : 𝓕 => U f d) (fun f => U_open f.2 d) with ⟨t, t_count, ht⟩
    use (↑) '' t, image_val_subset, t_count.image _
    rw [← ht]; rw [biUnion_image]
  choose A A_sub A_count hA using this
  set 𝓕' := ⋃ d in D, A d
  have 𝓕'_sub : 𝓕' subseteq 𝓕 := iUnion₂_subset fun d _ => A_sub d
  use 𝓕', 𝓕'_sub, D_count.biUnion fun d _ => A_count d
  refine fun x => ⟨lowerBounds_mono_set (image_mono 𝓕'_sub) (h𝓕 x).1, fun e he => ?_⟩
  by_contra! H
  rcases D_dense.exists_between H with ⟨d, d_mem, hd⟩
  obtain ⟨f, f_mem, hf⟩ : exists f in A d, f x < d := by
    have : x in {y | s y < d} := hd.1
    simpa only [hA d, mem_iUnion₂, exists_prop, U, mem_ofPred_eq] using this
  suffices e < e by simpa
.trans hd.2 exact (he (mem_image_of_mem _ (mem_iUnion₂_of_mem d_mem f_mem))).trans_lt hf

中文:
定理 存在_countable_upperSemicontinuous_isGLB
  结论: {s : X -> E} {𝓕 : 集合 (X -> E)}
  证明: by
  simp_rw [isGLB_pi] at *
  rcases exists_countable_dense E with ⟨D, D_count, D_dense⟩
  let U (f : X -> E) (d : E) : Set X := {x | f x < d}
.isOpen_preimage d have U_open {f} (hf : f in 𝓕) (d : E) : IsOpen (U f d) := h𝓕_cont f hf
  have (d : E) : {x | s x < d} = ⋃ f : 𝓕, U f d := by
    ext x
    simp [U, isGLB_lt_iff (h𝓕 x)]
  have (d : E) : exists A subseteq 𝓕, A.Countable ∧ {x | s x < d} = ⋃ f in A, U f d := by
    simp_rw [this d]
    rcases eq_open_union_countable (fun f : 𝓕 => U f d) (fun f => U_open f.2 d) with ⟨t, t_count, ht⟩
    use (↑) '' t, image_val_subset, t_count.image _
    rw [← ht]; rw [biUnion_image]
  choose A A_sub A_count hA using this
  set 𝓕' := ⋃ d in D, A d
  have 𝓕'_sub : 𝓕' subseteq 𝓕 := iUnion₂_subset fun d _ => A_sub d
  use 𝓕', 𝓕'_sub, D_count.biUnion fun d _ => A_count d
  refine fun x => ⟨lowerBounds_mono_set (image_mono 𝓕'_sub) (h𝓕 x).1, fun e he => ?_⟩
  by_contra! H
  rcases D_dense.exists_between H with ⟨d, d_mem, hd⟩
  obtain ⟨f, f_mem, hf⟩ : exists f in A d, f x < d := by
    have : x in {y | s y < d} := hd.1
    simpa only [hA d, mem_iUnion₂, exists_prop, U, mem_ofPred_eq] using this
  suffices e < e by simpa
.trans hd.2 exact (he (mem_image_of_mem _ (mem_iUnion₂_of_mem d_mem f_mem))).trans_lt hf

Depends on / 依赖: A.Countable, Countable, D_count, D_dense, IsOpen, U_open, eq_open_union_countable, exists_countable_dense, isGLB_lt_iff, isGLB_pi, isOpen_preimage, simp_rw, subseteq
-/
theorem exists_countable_upperSemicontinuous_isGLB {s : X -> E} {𝓕 : Set (X -> E)}
    (h𝓕_cont : forall f in 𝓕, UpperSemicontinuous f) (h𝓕 : IsGLB 𝓕 s) :
    exists 𝓕' subseteq 𝓕, 𝓕'.Countable ∧ IsGLB 𝓕' s := by
  simp_rw [isGLB_pi] at *
  rcases exists_countable_dense E with ⟨D, D_count, D_dense⟩
  let U (f : X -> E) (d : E) : Set X := {x | f x < d}
.isOpen_preimage d have U_open {f} (hf : f in 𝓕) (d : E) : IsOpen (U f d) := h𝓕_cont f hf
  have (d : E) : {x | s x < d} = ⋃ f : 𝓕, U f d := by
    ext x
    simp [U, isGLB_lt_iff (h𝓕 x)]
  have (d : E) : exists A subseteq 𝓕, A.Countable ∧ {x | s x < d} = ⋃ f in A, U f d := by
    simp_rw [this d]
    rcases eq_open_union_countable (fun f : 𝓕 => U f d) (fun f => U_open f.2 d) with ⟨t, t_count, ht⟩
    use (↑) '' t, image_val_subset, t_count.image _
    rw [← ht]; rw [biUnion_image]
  choose A A_sub A_count hA using this
  set 𝓕' := ⋃ d in D, A d
  have 𝓕'_sub : 𝓕' subseteq 𝓕 := iUnion₂_subset fun d _ => A_sub d
  use 𝓕', 𝓕'_sub, D_count.biUnion fun d _ => A_count d
  refine fun x => ⟨lowerBounds_mono_set (image_mono 𝓕'_sub) (h𝓕 x).1, fun e he => ?_⟩
  by_contra! H
  rcases D_dense.exists_between H with ⟨d, d_mem, hd⟩
  obtain ⟨f, f_mem, hf⟩ : exists f in A d, f x < d := by
    have : x in {y | s y < d} := hd.1
    simpa only [hA d, mem_iUnion₂, exists_prop, U, mem_ofPred_eq] using this
  suffices e < e by simpa
.trans hd.2 exact (he (mem_image_of_mem _ (mem_iUnion₂_of_mem d_mem f_mem))).trans_lt hf

/--
theorem `exists_countable_lowerSemicontinuous_isLUB` / 定理 `exists_countable_lowerSemicontinuous_isLUB`

English:
theorem exists_countable_lowerSemicontinuous_isLUB
  statement: {s : X -> E} {𝓕 : Set (X -> E)}
  proof: exists_countable_upperSemicontinuous_isGLB (E := Eᵒᵈ) h𝓕_cont h𝓕

中文:
定理 存在_countable_lowerSemicontinuous_isLUB
  结论: {s : X -> E} {𝓕 : 集合 (X -> E)}
  证明: exists_countable_upperSemicontinuous_isGLB (E := Eᵒᵈ) h𝓕_cont h𝓕

Depends on / 依赖: exists_countable_upperSemicontinuous_isGLB
-/
theorem exists_countable_lowerSemicontinuous_isLUB {s : X -> E} {𝓕 : Set (X -> E)}
    (h𝓕_cont : forall f in 𝓕, LowerSemicontinuous f) (h𝓕 : IsLUB 𝓕 s) :
    exists 𝓕' subseteq 𝓕, 𝓕'.Countable ∧ IsLUB 𝓕' s :=
  exists_countable_upperSemicontinuous_isGLB (E := Eᵒᵈ) h𝓕_cont h𝓕

end
