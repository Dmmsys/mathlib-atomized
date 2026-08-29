/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Closure

/-!
# Matroid IsCircuits

A 'Circuit' of a matroid `M` is a minimal set `C` that is dependent in `M`.
A matroid is determined by its set of circuits, and often the circuits
offer a more compact description of a matroid than the collection of independent sets or bases.
In matroids arising from graphs, circuits correspond to graphical cycles.

## Main Declarations

* `Matroid.IsCircuit M C` means that `C` is minimally dependent in `M`.
* For an `Indep`endent set `I` whose closure contains an element `e ∉ I`,
  `Matroid.fundCircuit M e I` is the unique circuit contained in `insert e I`.
* `Matroid.Indep.fundCircuit_isCircuit` states that `Matroid.fundCircuit M e I` is indeed a circuit.
* `Matroid.IsCircuit.eq_fundCircuit_of_subset` states that `Matroid.fundCircuit M e I` is the
  unique circuit contained in `insert e I`.
* `Matroid.dep_iff_superset_isCircuit` states that the dependent subsets of the ground set
  are precisely those that contain a circuit.
* `Matroid.ext_isCircuit` : a matroid is determined by its collection of circuits.
* `Matroid.IsCircuit.strong_multi_elimination` : the strong circuit elimination rule for an
  infinite collection of circuits.
* `Matroid.IsCircuit.strong_elimination` : the strong circuit elimination rule for two circuits.
* `Matroid.finitary_iff_forall_isCircuit_finite` : finitary matroids are precisely those whose
  circuits are all finite.
* `Matroid.IsCocircuit M C` means that `C` is minimally dependent in `M✶`,
  or equivalently that `M.E \ C` is a hyperplane of `M`.
* `Matroid.fundCocircuit M B e` is the unique cocircuit that intersects the base `B` precisely
  in the element `e`.
* `Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit` : `e` is in the fundamental circuit
  for `B` and `f` iff `f` is in the fundamental cocircuit for `B` and `e`.

## Implementation Details

Since `Matroid.fundCircuit M e I` is only sensible if `I` is independent and `e ∈ M.closure I \ I`,
to avoid hypotheses being explicitly included in the definition,
junk values need to be chosen if either hypothesis fails.
The definition is chosen so that the junk values satisfy
`M.fundCircuit e I = {e}` for `e ∈ I` or `e ∉ M.E` and
`M.fundCircuit e I = insert e I` if `e ∈ M.E \ M.closure I`.
These make the useful statement `e ∈ M.fundCircuit e I ⊆ insert e I` true unconditionally.
-/

@[expose] public section

variable {α : Type*} {M : Matroid α} {C C' I X Y R : Set α} {e f x y : α}

open Set

namespace Matroid

/--
Definition of `IsCircuit` / `IsCircuit` 的定义

English:
definition IsCircuit
  signature: (M : Matroid α)
  body: Minimal M.Dep

中文:
定义 是Circuit
  签名: (M : 拟阵 α)
  定义体: Minimal M.Dep

Depends on / 依赖: M.Dep, Minimal
-/
def IsCircuit (M : Matroid α) := Minimal M.Dep

/--
lemma `isCircuit_def` / 引理 `isCircuit_def`

English:
lemma isCircuit_def
  statement: M.IsCircuit C ↔ Minimal M.Dep C
  proof: Iff.rfl

中文:
引理 isCircuit_def
  结论: M.是Circuit C ↔ 极小 M.Dep C
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCircuit_def : M.IsCircuit C ↔ Minimal M.Dep C := Iff.rfl

/--
lemma `IsCircuit.dep` / 引理 `IsCircuit.dep`

English:
lemma IsCircuit.dep
  given: (hC : M.IsCircuit C)
  statement: M.Dep C
  proof: hC.prop

中文:
引理 是Circuit.dep
  条件: (hC : M.是Circuit C)
  结论: M.Dep C
  证明: hC.prop

Depends on / 依赖: hC.prop
-/
lemma IsCircuit.dep (hC : M.IsCircuit C) : M.Dep C :=
  hC.prop

/--
lemma `IsCircuit.not_indep` / 引理 `IsCircuit.not_indep`

English:
lemma IsCircuit.not_indep
  given: (hC : M.IsCircuit C)
  statement: ¬ M.Indep C
  proof: hC.dep.not_indep

中文:
引理 是Circuit.not_indep
  条件: (hC : M.是Circuit C)
  结论: ¬ M.Indep C
  证明: hC.dep.not_indep

Depends on / 依赖: hC.dep.not_indep, not_indep
-/
lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
  hC.dep.not_indep

/--
lemma `IsCircuit.minimal` / 引理 `IsCircuit.minimal`

English:
lemma IsCircuit.minimal
  given: (hC : M.IsCircuit C)
  statement: Minimal M.Dep C
  proof: hC

@[aesop unsafe 20% (rule_sets := [Matroid])]

中文:
引理 是Circuit.minimal
  条件: (hC : M.是Circuit C)
  结论: 极小 M.Dep C
  证明: hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
-/
lemma IsCircuit.minimal (hC : M.IsCircuit C) : Minimal M.Dep C :=
  hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
/--
lemma `IsCircuit.subset_ground` / 引理 `IsCircuit.subset_ground`

English:
lemma IsCircuit.subset_ground
  given: (hC : M.IsCircuit C)
  statement: C subseteq M.E
  proof: hC.dep.subset_ground

中文:
引理 是Circuit.subset_ground
  条件: (hC : M.是Circuit C)
  结论: C subseteq M.E
  证明: hC.dep.subset_ground

Depends on / 依赖: hC.dep.subset_ground, subset_ground
-/
lemma IsCircuit.subset_ground (hC : M.IsCircuit C) : C subseteq M.E :=
  hC.dep.subset_ground

/--
lemma `IsCircuit.nonempty` / 引理 `IsCircuit.nonempty`

English:
lemma IsCircuit.nonempty
  given: (hC : M.IsCircuit C)
  statement: C.Nonempty
  proof: hC.dep.nonempty

中文:
引理 是Circuit.nonempty
  条件: (hC : M.是Circuit C)
  结论: C.非空
  证明: hC.dep.nonempty

Depends on / 依赖: hC.dep.nonempty, nonempty
-/
lemma IsCircuit.nonempty (hC : M.IsCircuit C) : C.Nonempty :=
  hC.dep.nonempty

/--
lemma `empty_not_isCircuit` / 引理 `empty_not_isCircuit`

English:
lemma empty_not_isCircuit
  given: (M : Matroid α)
  statement: ¬M.IsCircuit ∅
  proof: fun h => by simpa using h.nonempty

中文:
引理 empty_not_isCircuit
  条件: (M : 拟阵 α)
  结论: ¬M.是Circuit ∅
  证明: fun h => by simpa using h.nonempty

Depends on / 依赖: h.nonempty, nonempty
-/
lemma empty_not_isCircuit (M : Matroid α) : ¬M.IsCircuit ∅ :=
  fun h => by simpa using h.nonempty

/--
lemma `isCircuit_iff` / 引理 `isCircuit_iff`

English:
lemma isCircuit_iff
  statement: M.IsCircuit C ↔ M.Dep C ∧ forall ⦃D⦄, M.Dep D -> D subseteq C -> D = C
  proof: by
  simp_rw [isCircuit_def, minimal_subset_iff, eq_comm (a := C)]

中文:
引理 isCircuit_iff
  结论: M.是Circuit C ↔ M.Dep C ∧ 对任意 ⦃D⦄, M.Dep D -> D subseteq C -> D = C
  证明: by
  simp_rw [isCircuit_def, minimal_subset_iff, eq_comm (a := C)]

Depends on / 依赖: eq_comm, isCircuit_def, minimal_subset_iff, simp_rw
-/
lemma isCircuit_iff : M.IsCircuit C ↔ M.Dep C ∧ forall ⦃D⦄, M.Dep D -> D subseteq C -> D = C := by
  simp_rw [isCircuit_def, minimal_subset_iff, eq_comm (a := C)]

/--
lemma `IsCircuit.ssubset_indep` / 引理 `IsCircuit.ssubset_indep`

English:
lemma IsCircuit.ssubset_indep
  given: (hC : M.IsCircuit C) (hXC : X ⊂ C)
  statement: M.Indep X
  proof: by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h => hXC.ne ((isCircuit_iff.1 hC).2 h hXC.subset)

中文:
引理 是Circuit.ssubset_indep
  条件: (hC : M.是Circuit C) (hXC : X ⊂ C)
  结论: M.Indep X
  证明: by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h => hXC.ne ((isCircuit_iff.1 hC).2 h hXC.subset)

Depends on / 依赖: hC.subset_ground, hXC.ne, hXC.subset, hXC.subset.trans, isCircuit_iff, not_dep_iff, subset, subset_ground
-/
lemma IsCircuit.ssubset_indep (hC : M.IsCircuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h => hXC.ne ((isCircuit_iff.1 hC).2 h hXC.subset)

/--
lemma `IsCircuit.minimal_not_indep` / 引理 `IsCircuit.minimal_not_indep`

English:
lemma IsCircuit.minimal_not_indep
  given: (hC : M.IsCircuit C)
  statement: Minimal (¬ M.Indep ·) C
  proof: by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a => ssubset_indep hC a

中文:
引理 是Circuit.minimal_not_indep
  条件: (hC : M.是Circuit C)
  结论: 极小 (¬ M.Indep ·) C
  证明: by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a => ssubset_indep hC a

Depends on / 依赖: and_iff_right, hC.not_indep, minimal_iff_forall_ssubset, not_indep, not_not, simp_rw, ssubset_indep
-/
lemma IsCircuit.minimal_not_indep (hC : M.IsCircuit C) : Minimal (¬ M.Indep ·) C := by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a => ssubset_indep hC a

/--
lemma `isCircuit_iff_minimal_not_indep` / 引理 `isCircuit_iff_minimal_not_indep`

English:
lemma isCircuit_iff_minimal_not_indep
  given: (hCE : C subseteq M.E)
  statement: M.IsCircuit C ↔ Minimal (¬ M.Indep ·) C
  proof: ⟨IsCircuit.minimal_not_indep, fun h => ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC => (h.eq_of_superset hJ.not_indep hJC).le⟩⟩

中文:
引理 isCircuit_iff_minimal_not_indep
  条件: (hCE : C subseteq M.E)
  结论: M.是Circuit C ↔ 极小 (¬ M.Indep ·) C
  证明: ⟨IsCircuit.minimal_not_indep, fun h => ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC => (h.eq_of_superset hJ.not_indep hJC).le⟩⟩

Depends on / 依赖: IsCircuit, IsCircuit.minimal_not_indep, eq_of_superset, h.eq_of_superset, h.prop, hJ.not_indep, minimal_not_indep, not_indep, not_indep_iff
-/
lemma isCircuit_iff_minimal_not_indep (hCE : C subseteq M.E) : M.IsCircuit C ↔ Minimal (¬ M.Indep ·) C :=
  ⟨IsCircuit.minimal_not_indep, fun h => ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC => (h.eq_of_superset hJ.not_indep hJC).le⟩⟩

/--
lemma `IsCircuit.sdiff_singleton_indep` / 引理 `IsCircuit.sdiff_singleton_indep`

English:
lemma IsCircuit.sdiff_singleton_indep
  given: (hC : M.IsCircuit C) (he : e in C)
  statement: M.Indep (C \ {e})
  proof: hC.ssubset_indep (sdiff_singleton_ssubset.2 he)

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_indep := IsCircuit.sdiff_singleton_indep

中文:
引理 是Circuit.sdiff_singleton_indep
  条件: (hC : M.是Circuit C) (he : e in C)
  结论: M.Indep (C \ {e})
  证明: hC.ssubset_indep (sdiff_singleton_ssubset.2 he)

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_indep := IsCircuit.sdiff_singleton_indep

Depends on / 依赖: hC.ssubset_indep, sdiff_singleton_ssubset, ssubset_indep
-/
lemma IsCircuit.sdiff_singleton_indep (hC : M.IsCircuit C) (he : e in C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (sdiff_singleton_ssubset.2 he)

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_indep := IsCircuit.sdiff_singleton_indep

/--
lemma `isCircuit_iff_forall_ssubset` / 引理 `isCircuit_iff_forall_ssubset`

English:
lemma isCircuit_iff_forall_ssubset
  statement: M.IsCircuit C ↔ M.Dep C ∧ forall ⦃I⦄, I ⊂ C -> M.Indep I
  proof: by
  rw [IsCircuit]; rw [minimal_iff_forall_ssubset]; rw [and_congr_right_iff]
  exact fun h => ⟨fun h' I hIC => ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC => (h hIC).not_dep⟩

中文:
引理 isCircuit_iff_对任意_ssubset
  结论: M.是Circuit C ↔ M.Dep C ∧ 对任意 ⦃I⦄, I ⊂ C -> M.Indep I
  证明: by
  rw [IsCircuit]; rw [minimal_iff_forall_ssubset]; rw [and_congr_right_iff]
  exact fun h => ⟨fun h' I hIC => ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC => (h hIC).not_dep⟩

Depends on / 依赖: IsCircuit, and_congr_right_iff, h.subset_ground, hIC.subset.trans, minimal_iff_forall_ssubset, not_dep, not_dep_iff, subset, subset_ground
-/
lemma isCircuit_iff_forall_ssubset : M.IsCircuit C ↔ M.Dep C ∧ forall ⦃I⦄, I ⊂ C -> M.Indep I := by
  rw [IsCircuit]; rw [minimal_iff_forall_ssubset]; rw [and_congr_right_iff]
  exact fun h => ⟨fun h' I hIC => ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC => (h hIC).not_dep⟩

/--
lemma `isCircuit_antichain` / 引理 `isCircuit_antichain`

English:
lemma isCircuit_antichain
  statement: IsAntichain (· subseteq ·) (Set.ofPred M.IsCircuit)
  proof: fun _ hC _ hC' hne hss => hne (IsCircuit.minimal hC').eq_of_subset hC.dep hss

中文:
引理 isCircuit_antichain
  结论: IsAntichain (· subseteq ·) (集合.ofPred M.是Circuit)
  证明: fun _ hC _ hC' hne hss => hne (IsCircuit.minimal hC').eq_of_subset hC.dep hss

Depends on / 依赖: IsCircuit, IsCircuit.minimal, eq_of_subset, hC.dep, minimal
-/
lemma isCircuit_antichain : IsAntichain (· subseteq ·) (Set.ofPred M.IsCircuit) :=
fun _ hC _ hC' hne hss => hne (IsCircuit.minimal hC').eq_of_subset hC.dep hss

/--
lemma `IsCircuit.eq_of_not_indep_subset` / 引理 `IsCircuit.eq_of_not_indep_subset`

English:
lemma IsCircuit.eq_of_not_indep_subset
  given: (hC : M.IsCircuit C) (hX : ¬ M.Indep X) (hXC : X subseteq C)
  proof: eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

中文:
引理 是Circuit.eq_of_not_indep_subset
  条件: (hC : M.是Circuit C) (hX : ¬ M.Indep X) (hXC : X subseteq C)
  证明: eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

Depends on / 依赖: eq_of_le_of_not_lt, hC.ssubset_indep, ssubset_indep
-/
lemma IsCircuit.eq_of_not_indep_subset (hC : M.IsCircuit C) (hX : ¬ M.Indep X) (hXC : X subseteq C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

/--
lemma `IsCircuit.eq_of_dep_subset` / 引理 `IsCircuit.eq_of_dep_subset`

English:
lemma IsCircuit.eq_of_dep_subset
  given: (hC : M.IsCircuit C) (hX : M.Dep X) (hXC : X subseteq C)
  statement: X = C
  proof: hC.eq_of_not_indep_subset hX.not_indep hXC

中文:
引理 是Circuit.eq_of_dep_subset
  条件: (hC : M.是Circuit C) (hX : M.Dep X) (hXC : X subseteq C)
  结论: X = C
  证明: hC.eq_of_not_indep_subset hX.not_indep hXC

Depends on / 依赖: eq_of_not_indep_subset, hC.eq_of_not_indep_subset, hX.not_indep, not_indep
-/
lemma IsCircuit.eq_of_dep_subset (hC : M.IsCircuit C) (hX : M.Dep X) (hXC : X subseteq C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC

/--
lemma `IsCircuit.not_ssubset` / 引理 `IsCircuit.not_ssubset`

English:
lemma IsCircuit.not_ssubset
  given: (hC : M.IsCircuit C) (hC' : M.IsCircuit C')
  statement: ¬C' ⊂ C
  proof: fun h' => h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

中文:
引理 是Circuit.not_ssubset
  条件: (hC : M.是Circuit C) (hC' : M.是Circuit C')
  结论: ¬C' ⊂ C
  证明: fun h' => h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

Depends on / 依赖: eq_of_dep_subset, hC.eq_of_dep_subset, subset
-/
lemma IsCircuit.not_ssubset (hC : M.IsCircuit C) (hC' : M.IsCircuit C') : ¬C' ⊂ C :=
  fun h' => h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

/--
lemma `IsCircuit.eq_of_subset_isCircuit` / 引理 `IsCircuit.eq_of_subset_isCircuit`

English:
lemma IsCircuit.eq_of_subset_isCircuit
  given: (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C subseteq C')
  proof: hC'.eq_of_dep_subset hC.dep h

中文:
引理 是Circuit.eq_of_subset_isCircuit
  条件: (hC : M.是Circuit C) (hC' : M.是Circuit C') (h : C subseteq C')
  证明: hC'.eq_of_dep_subset hC.dep h

Depends on / 依赖: eq_of_dep_subset, hC.dep
-/
lemma IsCircuit.eq_of_subset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C subseteq C') :
    C = C' :=
  hC'.eq_of_dep_subset hC.dep h

/--
lemma `IsCircuit.eq_of_superset_isCircuit` / 引理 `IsCircuit.eq_of_superset_isCircuit`

English:
lemma IsCircuit.eq_of_superset_isCircuit
  given: (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C' subseteq C)
  proof: (hC'.eq_of_subset_isCircuit hC h).symm

中文:
引理 是Circuit.eq_of_superset_isCircuit
  条件: (hC : M.是Circuit C) (hC' : M.是Circuit C') (h : C' subseteq C)
  证明: (hC'.eq_of_subset_isCircuit hC h).symm

Depends on / 依赖: eq_of_subset_isCircuit
-/
lemma IsCircuit.eq_of_superset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C' subseteq C) :
    C = C' :=
  (hC'.eq_of_subset_isCircuit hC h).symm

/--
lemma `isCircuit_iff_dep_forall_sdiff_singleton_indep` / 引理 `isCircuit_iff_dep_forall_sdiff_singleton_indep`

English:
lemma isCircuit_iff_dep_forall_sdiff_singleton_indep
  proof: by
  wlog hCE : C subseteq M.E
  · exact iff_of_false (hCE ∘ IsCircuit.subset_ground) (fun h => hCE h.1.subset_ground)
  simp [isCircuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_sdiff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX => hY <| hX.subset hYX)]

@[depr

中文:
引理 isCircuit_iff_dep_对任意_sdiff_singleton_indep
  证明: by
  wlog hCE : C subseteq M.E
  · exact iff_of_false (hCE ∘ IsCircuit.subset_ground) (fun h => hCE h.1.subset_ground)
  simp [isCircuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_sdiff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX => hY <| hX.subset hYX)]

@[depr

Depends on / 依赖: IsCircuit, IsCircuit.subset_ground, M.Indep, hX.subset, iff_of_false, isCircuit_iff_minimal_not_indep, minimal_iff_forall_sdiff_singleton, not_indep_iff, subset, subset_ground, subseteq
-/
lemma isCircuit_iff_dep_forall_sdiff_singleton_indep :
    M.IsCircuit C ↔ M.Dep C ∧ forall e in C, M.Indep (C \ {e}) := by
  wlog hCE : C subseteq M.E
  · exact iff_of_false (hCE ∘ IsCircuit.subset_ground) (fun h => hCE h.1.subset_ground)
  simp [isCircuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_sdiff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX => hY <| hX.subset hYX)]

@[deprecated (since := "2026-06-03")]
alias isCircuit_iff_dep_forall_diff_singleton_indep :=
  isCircuit_iff_dep_forall_sdiff_singleton_indep


/--
lemma `Indep.insert_isCircuit_of_forall` / 引理 `Indep.insert_isCircuit_of_forall`

English:
lemma Indep.insert_isCircuit_of_forall
  statement: (hI : M.Indep I) (heI : e ∉ I) (he : e in M.closure I)
  proof: by
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]; rw [hI.insert_dep_iff]; rw [and_iff_right ⟨he]; rw [heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_sdiff_singleton_comm (by rintro rfl; contradiction)]; rw [(hI.sdiff _).insert_indep_iff_of_notMem (by simp [heI])]
  exact ⟨mem_gr

中文:
引理 Indep.insert_isCircuit_of_对任意
  结论: (hI : M.Indep I) (heI : e ∉ I) (he : e in M.closure I)
  证明: by
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]; rw [hI.insert_dep_iff]; rw [and_iff_right ⟨he]; rw [heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_sdiff_singleton_comm (by rintro rfl; contradiction)]; rw [(hI.sdiff _).insert_indep_iff_of_notMem (by simp [heI])]
  exact ⟨mem_gr

Depends on / 依赖: and_iff_right, hI.insert_dep_iff, hI.sdiff, insert_dep_iff, insert_indep_iff_of_notMem, insert_sdiff_singleton_comm, isCircuit_iff_dep_forall_sdiff_singleton_indep, mem_ground_of_mem_closure
-/
lemma Indep.insert_isCircuit_of_forall (hI : M.Indep I) (heI : e ∉ I) (he : e in M.closure I)
    (h : forall f in I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]; rw [hI.insert_dep_iff]; rw [and_iff_right ⟨he]; rw [heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_sdiff_singleton_comm (by rintro rfl; contradiction)]; rw [(hI.sdiff _).insert_indep_iff_of_notMem (by simp [heI])]
  exact ⟨mem_ground_of_mem_closure he, h f hfI⟩

/--
lemma `Indep.insert_isCircuit_of_forall_of_nontrivial` / 引理 `Indep.insert_isCircuit_of_forall_of_nontrivial`

English:
lemma Indep.insert_isCircuit_of_forall_of_nontrivial
  statement: (hI : M.Indep I) (hInt : I.Nontrivial)
  proof: by
  refine hI.insert_isCircuit_of_forall (fun heI => ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

中文:
引理 Indep.insert_isCircuit_of_对任意_of_nontrivial
  结论: (hI : M.Indep I) (h整数 : I.非平凡)
  证明: by
  refine hI.insert_isCircuit_of_forall (fun heI => ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

Depends on / 依赖: exists_ne, hI.insert_isCircuit_of_forall, hInt.exists_ne, hne.symm, insert_isCircuit_of_forall, mem_closure_of_mem
-/
lemma Indep.insert_isCircuit_of_forall_of_nontrivial (hI : M.Indep I) (hInt : I.Nontrivial)
    (he : e in M.closure I) (h : forall f in I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  refine hI.insert_isCircuit_of_forall (fun heI => ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

/--
lemma `IsCircuit.sdiff_singleton_isBasis` / 引理 `IsCircuit.sdiff_singleton_isBasis`

English:
lemma IsCircuit.sdiff_singleton_isBasis
  given: (hC : M.IsCircuit C) (he : e in C)
  proof: by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_sdiff_singleton]; rw [(hC.sdiff_singleton_indep he).isBasis_insert_iff]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem he]
  exact Or.inl hC.dep

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_isBasis := IsCircuit.sdiff_s

中文:
引理 是Circuit.sdiff_singleton_isBasis
  条件: (hC : M.是Circuit C) (he : e in C)
  证明: by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_sdiff_singleton]; rw [(hC.sdiff_singleton_indep he).isBasis_insert_iff]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem he]
  exact Or.inl hC.dep

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_isBasis := IsCircuit.sdiff_s

Depends on / 依赖: Or.inl, hC.dep, hC.sdiff_singleton_indep, insert_eq_of_mem, insert_sdiff_singleton, isBasis_insert_iff, nth_rw, sdiff_singleton_indep
-/
lemma IsCircuit.sdiff_singleton_isBasis (hC : M.IsCircuit C) (he : e in C) :
    M.IsBasis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_sdiff_singleton]; rw [(hC.sdiff_singleton_indep he).isBasis_insert_iff]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem he]
  exact Or.inl hC.dep

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_isBasis := IsCircuit.sdiff_singleton_isBasis

/--
lemma `IsCircuit.isBasis_iff_eq_sdiff_singleton` / 引理 `IsCircuit.isBasis_iff_eq_sdiff_singleton`

English:
lemma IsCircuit.isBasis_iff_eq_sdiff_singleton
  given: (hC : M.IsCircuit C)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.sdiff_singleton_indep he.1)
      (subset_sdiff_singleton h.subset he.2) sdiff_subset⟩
  rintro ⟨e, he, rf

中文:
引理 是Circuit.isBasis_iff_eq_sdiff_singleton
  条件: (hC : M.是Circuit C)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.sdiff_singleton_indep he.1)
      (subset_sdiff_singleton h.subset he.2) sdiff_subset⟩
  rintro ⟨e, he, rf

Depends on / 依赖: eq_of_subset_indep, exists_of_ssubset, h.eq_of_subset_indep, h.indep, h.subset, h.subset.ssubset_of_ne, hC.dep.not_indep, hC.sdiff_singleton_indep, hC.sdiff_singleton_isBasis, not_indep, sdiff_singleton_indep, sdiff_singleton_isBasis, sdiff_subset, ssubset_of_ne, subset, subset_sdiff_singleton
-/
lemma IsCircuit.isBasis_iff_eq_sdiff_singleton (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ exists e in C, I = C \ {e} := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.sdiff_singleton_indep he.1)
      (subset_sdiff_singleton h.subset he.2) sdiff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.sdiff_singleton_isBasis he

@[deprecated (since := "2026-06-03")]
alias IsCircuit.isBasis_iff_eq_diff_singleton := IsCircuit.isBasis_iff_eq_sdiff_singleton

/--
lemma `IsCircuit.isBasis_iff_insert_eq` / 引理 `IsCircuit.isBasis_iff_insert_eq`

English:
lemma IsCircuit.isBasis_iff_insert_eq
  given: (hC : M.IsCircuit C)
  proof: by
  rw [hC.isBasis_iff_eq_sdiff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ => ⟨e, ⟨he, fun heI => (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ => ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_sdiff_singleton, insert_eq_of_mem he]
  rw [hC]; rw [insert_sdiff_self_of_notMem he.2]

中文:
引理 是Circuit.isBasis_iff_insert_eq
  条件: (hC : M.是Circuit C)
  证明: by
  rw [hC.isBasis_iff_eq_sdiff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ => ⟨e, ⟨he, fun heI => (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ => ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_sdiff_singleton, insert_eq_of_mem he]
  rw [hC]; rw [insert_sdiff_self_of_notMem he.2]

Depends on / 依赖: hC.isBasis_iff_eq_sdiff_singleton, hI.subset, insert_eq_of_mem, insert_sdiff_self_of_notMem, insert_sdiff_singleton, isBasis_iff_eq_sdiff_singleton, subset
-/
lemma IsCircuit.isBasis_iff_insert_eq (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ exists e in C \ I, C = insert e I := by
  rw [hC.isBasis_iff_eq_sdiff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ => ⟨e, ⟨he, fun heI => (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ => ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_sdiff_singleton, insert_eq_of_mem he]
  rw [hC]; rw [insert_sdiff_self_of_notMem he.2]


/--
lemma `IsCircuit.isCircuit_restrict_of_subset` / 引理 `IsCircuit.isCircuit_restrict_of_subset`

English:
lemma IsCircuit.isCircuit_restrict_of_subset
  given: (hC : M.IsCircuit C) (hCR : C subseteq R)
  proof: by
  simp_rw [isCircuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC => hC.2 hI (hIC.trans hC.1.2) hIC⟩

中文:
引理 是Circuit.isCircuit_restrict_of_subset
  条件: (hC : M.是Circuit C) (hCR : C subseteq R)
  证明: by
  simp_rw [isCircuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC => hC.2 hI (hIC.trans hC.1.2) hIC⟩

Depends on / 依赖: and_imp, dep_iff, hIC.trans, isCircuit_iff, restrict_dep_iff, simp_rw
-/
lemma IsCircuit.isCircuit_restrict_of_subset (hC : M.IsCircuit C) (hCR : C subseteq R) :
    (M ↾ R).IsCircuit C := by
  simp_rw [isCircuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC => hC.2 hI (hIC.trans hC.1.2) hIC⟩

/--
lemma `restrict_isCircuit_iff` / 引理 `restrict_isCircuit_iff`

English:
lemma restrict_isCircuit_iff
  given: (hR : R subseteq M.E := by aesop_mat)
  proof: by
  refine ⟨?_, fun h => h.1.isCircuit_restrict_of_subset h.2⟩
  simp_rw [isCircuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h => ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC => h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

中文:
引理 restrict_isCircuit_iff
  条件: (hR : R subseteq M.E := by aesop_mat)
  证明: by
  refine ⟨?_, fun h => h.1.isCircuit_restrict_of_subset h.2⟩
  simp_rw [isCircuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h => ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC => h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

Depends on / 依赖: IsCircuit, M.IsCircuit, aesop_mat, and_imp, dep_iff, hCR.trans, hIC.trans, isCircuit_iff, isCircuit_restrict_of_subset, restrict_dep_iff, simp_rw, subseteq
-/
lemma restrict_isCircuit_iff (hR : R subseteq M.E := by aesop_mat) :
    (M ↾ R).IsCircuit C ↔ M.IsCircuit C ∧ C subseteq R := by
  refine ⟨?_, fun h => h.1.isCircuit_restrict_of_subset h.2⟩
  simp_rw [isCircuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h => ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC => h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

/-! ### Fundamental IsCircuits -/

/--
Definition of `fundCircuit` / `fundCircuit` 的定义

English:
definition fundCircuit
  signature: (M : Matroid α) (e : α) (I : Set α)
  body: insert e (I inter ⋂₀ {J | J subseteq I ∧ M.closure {e} subseteq M.closure J})

中文:
定义 fundCircuit
  签名: (M : 拟阵 α) (e : α) (I : 集合 α)
  定义体: insert e (I inter ⋂₀ {J | J subseteq I ∧ M.closure {e} subseteq M.closure J})

Depends on / 依赖: M.closure, closure, insert, subseteq
-/
def fundCircuit (M : Matroid α) (e : α) (I : Set α) : Set α :=
  insert e (I inter ⋂₀ {J | J subseteq I ∧ M.closure {e} subseteq M.closure J})

/--
lemma `fundCircuit_eq_sInter` / 引理 `fundCircuit_eq_sInter`

English:
lemma fundCircuit_eq_sInter
  given: (he : e in M.closure I)
  proof: by
  rw [fundCircuit]
  simp_rw [closure_subset_closure_iff_subset_closure
    (show {e} subseteq M.E by simpa using mem_ground_of_mem_closure he), singleton_subset_iff]
  rw [inter_eq_self_of_subset_right (sInter_subset_of_mem (by simpa))]

中文:
引理 fundCircuit_eq_s整数er
  条件: (he : e in M.closure I)
  证明: by
  rw [fundCircuit]
  simp_rw [closure_subset_closure_iff_subset_closure
    (show {e} subseteq M.E by simpa using mem_ground_of_mem_closure he), singleton_subset_iff]
  rw [inter_eq_self_of_subset_right (sInter_subset_of_mem (by simpa))]

Depends on / 依赖: closure_subset_closure_iff_subset_closure, fundCircuit, inter_eq_self_of_subset_right, mem_ground_of_mem_closure, sInter_subset_of_mem, simp_rw, singleton_subset_iff, subseteq
-/
lemma fundCircuit_eq_sInter (he : e in M.closure I) :
    M.fundCircuit e I = insert e (⋂₀ {J | J subseteq I ∧ e in M.closure J}) := by
  rw [fundCircuit]
  simp_rw [closure_subset_closure_iff_subset_closure
    (show {e} subseteq M.E by simpa using mem_ground_of_mem_closure he), singleton_subset_iff]
  rw [inter_eq_self_of_subset_right (sInter_subset_of_mem (by simpa))]

/--
lemma `fundCircuit_subset_insert` / 引理 `fundCircuit_subset_insert`

English:
lemma fundCircuit_subset_insert
  given: (M : Matroid α) (e : α) (I : Set α)
  proof: insert_subset_insert inter_subset_left

中文:
引理 fundCircuit_subset_insert
  条件: (M : 拟阵 α) (e : α) (I : 集合 α)
  证明: insert_subset_insert inter_subset_left

Depends on / 依赖: insert_subset_insert, inter_subset_left
-/
lemma fundCircuit_subset_insert (M : Matroid α) (e : α) (I : Set α) :
    M.fundCircuit e I subseteq insert e I :=
  insert_subset_insert inter_subset_left

/--
lemma `fundCircuit_subset_ground` / 引理 `fundCircuit_subset_ground`

English:
lemma fundCircuit_subset_ground
  given: (he : e in M.E) (hI : I subseteq M.E := by aesop_mat)
  proof: (M.fundCircuit_subset_insert e I).trans (insert_subset he hI)

中文:
引理 fundCircuit_subset_ground
  条件: (he : e in M.E) (hI : I subseteq M.E := by aesop_mat)
  证明: (M.fundCircuit_subset_insert e I).trans (insert_subset he hI)

Depends on / 依赖: M.fundCircuit, M.fundCircuit_subset_insert, aesop_mat, fundCircuit, fundCircuit_subset_insert, insert_subset, subseteq
-/
lemma fundCircuit_subset_ground (he : e in M.E) (hI : I subseteq M.E := by aesop_mat) :
    M.fundCircuit e I subseteq M.E :=
  (M.fundCircuit_subset_insert e I).trans (insert_subset he hI)

/--
lemma `mem_fundCircuit` / 引理 `mem_fundCircuit`

English:
lemma mem_fundCircuit
  given: (M : Matroid α) (e : α) (I : Set α)
  statement: e in fundCircuit M e I
  proof: mem_insert ..

中文:
引理 mem_fundCircuit
  条件: (M : 拟阵 α) (e : α) (I : 集合 α)
  结论: e in fundCircuit M e I
  证明: mem_insert ..

Depends on / 依赖: mem_insert
-/
lemma mem_fundCircuit (M : Matroid α) (e : α) (I : Set α) : e in fundCircuit M e I :=
  mem_insert ..

/--
lemma `fundCircuit_sdiff_eq_inter` / 引理 `fundCircuit_sdiff_eq_inter`

English:
lemma fundCircuit_sdiff_eq_inter
  given: (M : Matroid α) (heI : e ∉ I)
  proof: (subset_inter sdiff_subset (by simp [fundCircuit_subset_insert])).antisymm
    (subset_sdiff_singleton inter_subset_left (by simp [heI]))

@[deprecated (since := "2026-06-03")] alias fundCircuit_diff_eq_inter := fundCircuit_sdiff_eq_inter

中文:
引理 fundCircuit_sdiff_eq_inter
  条件: (M : 拟阵 α) (heI : e ∉ I)
  证明: (subset_inter sdiff_subset (by simp [fundCircuit_subset_insert])).antisymm
    (subset_sdiff_singleton inter_subset_left (by simp [heI]))

@[deprecated (since := "2026-06-03")] alias fundCircuit_diff_eq_inter := fundCircuit_sdiff_eq_inter

Depends on / 依赖: antisymm, fundCircuit_subset_insert, inter_subset_left, sdiff_subset, subset_inter, subset_sdiff_singleton
-/
lemma fundCircuit_sdiff_eq_inter (M : Matroid α) (heI : e ∉ I) :
    (M.fundCircuit e I) \ {e} = (M.fundCircuit e I) inter I :=
  (subset_inter sdiff_subset (by simp [fundCircuit_subset_insert])).antisymm
    (subset_sdiff_singleton inter_subset_left (by simp [heI]))

@[deprecated (since := "2026-06-03")] alias fundCircuit_diff_eq_inter := fundCircuit_sdiff_eq_inter

/--
lemma `fundCircuit_eq_of_mem` / 引理 `fundCircuit_eq_of_mem`

English:
lemma fundCircuit_eq_of_mem
  given: (heX : e in X)
  statement: M.fundCircuit e X = {e}
  proof: by
  suffices h : forall a in X, (forall t subseteq X, M.closure {e} subseteq M.closure t -> a in t) -> a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun b hbX h => h _ (singleton_subset_iff.2 heX) Subset.rfl

中文:
引理 fundCircuit_eq_of_mem
  条件: (heX : e in X)
  结论: M.fundCircuit e X = {e}
  证明: by
  suffices h : forall a in X, (forall t subseteq X, M.closure {e} subseteq M.closure t -> a in t) -> a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun b hbX h => h _ (singleton_subset_iff.2 heX) Subset.rfl

Depends on / 依赖: M.closure, Subset, Subset.rfl, closure, fundCircuit, singleton_subset_iff, subset_antisymm_iff, subseteq
-/
lemma fundCircuit_eq_of_mem (heX : e in X) : M.fundCircuit e X = {e} := by
  suffices h : forall a in X, (forall t subseteq X, M.closure {e} subseteq M.closure t -> a in t) -> a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun b hbX h => h _ (singleton_subset_iff.2 heX) Subset.rfl

/--
lemma `fundCircuit_eq_of_notMem_ground` / 引理 `fundCircuit_eq_of_notMem_ground`

English:
lemma fundCircuit_eq_of_notMem_ground
  given: (heX : e ∉ M.E)
  statement: M.fundCircuit e X = {e}
  proof: by
  suffices h : forall a in X, (forall t subseteq X, M.closure {e} subseteq M.closure t -> a in t) -> a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  simp_rw [← M.closure_inter_ground {e}, singleton_inter_eq_empty.2 heX]
  exact fun a haX h => by simpa using h ∅ (empty_subset X) rfl.subset

中文:
引理 fundCircuit_eq_of_notMem_ground
  条件: (heX : e ∉ M.E)
  结论: M.fundCircuit e X = {e}
  证明: by
  suffices h : forall a in X, (forall t subseteq X, M.closure {e} subseteq M.closure t -> a in t) -> a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  simp_rw [← M.closure_inter_ground {e}, singleton_inter_eq_empty.2 heX]
  exact fun a haX h => by simpa using h ∅ (empty_subset X) rfl.subset

Depends on / 依赖: M.closure, M.closure_inter_ground, closure, closure_inter_ground, empty_subset, fundCircuit, rfl.subset, simp_rw, singleton_inter_eq_empty, subset, subset_antisymm_iff, subseteq
-/
lemma fundCircuit_eq_of_notMem_ground (heX : e ∉ M.E) : M.fundCircuit e X = {e} := by
  suffices h : forall a in X, (forall t subseteq X, M.closure {e} subseteq M.closure t -> a in t) -> a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  simp_rw [← M.closure_inter_ground {e}, singleton_inter_eq_empty.2 heX]
  exact fun a haX h => by simpa using h ∅ (empty_subset X) rfl.subset

/--
lemma `Indep.fundCircuit_isCircuit` / 引理 `Indep.fundCircuit_isCircuit`

English:
lemma Indep.fundCircuit_isCircuit
  given: (hI : M.Indep I) (hecl : e in M.closure I) (heI : e ∉ I)
  proof: by
  have aux : ⋂₀ {J | J subseteq I ∧ e in M.closure J} subseteq I := sInter_subset_of_mem (by simpa)
  rw [fundCircuit_eq_sInter hecl]
  refine (hI.subset aux).insert_isCircuit_of_forall ?_ ?_ ?_
  · simp [show exists x subseteq I, e in M.closure x ∧ e ∉ x from ⟨I, by simp [hecl, heI]⟩]
  · rw [hI

中文:
引理 Indep.fundCircuit_isCircuit
  条件: (hI : M.Indep I) (hecl : e in M.closure I) (heI : e ∉ I)
  证明: by
  have aux : ⋂₀ {J | J subseteq I ∧ e in M.closure J} subseteq I := sInter_subset_of_mem (by simpa)
  rw [fundCircuit_eq_sInter hecl]
  refine (hI.subset aux).insert_isCircuit_of_forall ?_ ?_ ?_
  · simp [show exists x subseteq I, e in M.closure x ∧ e ∉ x from ⟨I, by simp [hecl, heI]⟩]
  · rw [hI

Depends on / 依赖: M.closure, and_imp, closure, closure_sInter_eq_biInter_closure_of_forall_subset, contextual, fundCircuit_eq_sInter, hI.closure_sInter_eq_biInter_closure_of_forall_subset, hI.subset, insert_isCircuit_of_forall, mem_ofPred_eq, mem_sInter, sInter_subset_of_mem, sdiff_subset, sdiff_subset.trans, subset, subseteq
-/
lemma Indep.fundCircuit_isCircuit (hI : M.Indep I) (hecl : e in M.closure I) (heI : e ∉ I) :
    M.IsCircuit (M.fundCircuit e I) := by
  have aux : ⋂₀ {J | J subseteq I ∧ e in M.closure J} subseteq I := sInter_subset_of_mem (by simpa)
  rw [fundCircuit_eq_sInter hecl]
  refine (hI.subset aux).insert_isCircuit_of_forall ?_ ?_ ?_
  · simp [show exists x subseteq I, e in M.closure x ∧ e ∉ x from ⟨I, by simp [hecl, heI]⟩]
  · rw [hI.closure_sInter_eq_biInter_closure_of_forall_subset ⟨I, by simpa⟩ (by simp +contextual)]
    simp
  simp only [mem_sInter, mem_ofPred_eq, and_imp]
  exact fun f hf hecl => (hf _ (sdiff_subset.trans aux) hecl).2 rfl

/--
lemma `Indep.mem_fundCircuit_iff` / 引理 `Indep.mem_fundCircuit_iff`

English:
lemma Indep.mem_fundCircuit_iff
  given: (hI : M.Indep I) (hecl : e in M.closure I) (heI : e ∉ I)
  proof: by
  obtain rfl | hne := eq_or_ne x e
  · simp [hI.sdiff, mem_fundCircuit]
  suffices (forall t subseteq I, e in M.closure t -> x in t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCircuit_eq_sInter hecl, hne, ← insert_sdiff_singleton_comm hne.symm,
      (hI.sdiff _).insert_indep_iff, mem_ground_of_

中文:
引理 Indep.mem_fundCircuit_iff
  条件: (hI : M.Indep I) (hecl : e in M.closure I) (heI : e ∉ I)
  证明: by
  obtain rfl | hne := eq_or_ne x e
  · simp [hI.sdiff, mem_fundCircuit]
  suffices (forall t subseteq I, e in M.closure t -> x in t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCircuit_eq_sInter hecl, hne, ← insert_sdiff_singleton_comm hne.symm,
      (hI.sdiff _).insert_indep_iff, mem_ground_of_

Depends on / 依赖: M.closure, M.closure_subset_closure, closure, closure_subset_closure, eq_or_ne, fundCircuit_eq_sInter, hI.sdiff, hne.symm, insert_indep_iff, insert_sdiff_singleton_comm, mem_fundCircuit, mem_ground_of_mem_closure, sdiff_subset, subset_sdiff_singleton, subseteq
-/
lemma Indep.mem_fundCircuit_iff (hI : M.Indep I) (hecl : e in M.closure I) (heI : e ∉ I) :
    x in M.fundCircuit e I ↔ M.Indep (insert e I \ {x}) := by
  obtain rfl | hne := eq_or_ne x e
  · simp [hI.sdiff, mem_fundCircuit]
  suffices (forall t subseteq I, e in M.closure t -> x in t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCircuit_eq_sInter hecl, hne, ← insert_sdiff_singleton_comm hne.symm,
      (hI.sdiff _).insert_indep_iff, mem_ground_of_mem_closure hecl, heI]
  refine ⟨fun h hecl => (h _ sdiff_subset hecl).2 rfl, fun h J hJ heJ => by_contra fun hxJ => h ?_⟩
  exact M.closure_subset_closure (subset_sdiff_singleton hJ hxJ) heJ

/--
lemma `IsBase.fundCircuit_isCircuit` / 引理 `IsBase.fundCircuit_isCircuit`

English:
lemma IsBase.fundCircuit_isCircuit
  given: {B : Set α} (hB : M.IsBase B) (hxE : x in M.E) (hxB : x ∉ B)
  proof: hB.indep.fundCircuit_isCircuit (by rwa [hB.closure_eq]) hxB

中文:
引理 IsBase.fundCircuit_isCircuit
  条件: {B : 集合 α} (hB : M.IsBase B) (hxE : x in M.E) (hxB : x ∉ B)
  证明: hB.indep.fundCircuit_isCircuit (by rwa [hB.closure_eq]) hxB

Depends on / 依赖: closure_eq, fundCircuit_isCircuit, hB.closure_eq, hB.indep.fundCircuit_isCircuit
-/
lemma IsBase.fundCircuit_isCircuit {B : Set α} (hB : M.IsBase B) (hxE : x in M.E) (hxB : x ∉ B) :
    M.IsCircuit (M.fundCircuit x B) :=
  hB.indep.fundCircuit_isCircuit (by rwa [hB.closure_eq]) hxB

/--
lemma `IsCircuit.eq_fundCircuit_of_subset` / 引理 `IsCircuit.eq_fundCircuit_of_subset`

English:
lemma IsCircuit.eq_fundCircuit_of_subset
  statement: (hC : M.IsCircuit C) (hI : M.Indep I)
  proof: by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I subseteq C by
    refine hC.eq_of_superset_isCircuit (hI.fundCircuit_isCircuit ?_ fun heI => ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.supers

中文:
引理 是Circuit.eq_fundCircuit_of_subset
  结论: (hC : M.是Circuit C) (hI : M.Indep I)
  证明: by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I subseteq C by
    refine hC.eq_of_superset_isCircuit (hI.fundCircuit_isCircuit ?_ fun heI => ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.supers

Depends on / 依赖: M.closure, M.fundCircuit, closure, eq_of_superset_isCircuit, fundCircuit, fundCircuit_isCircuit, hC.dep.superset, hC.eq_of_superset_isCircuit, hC.not_indep, hC.sdiff_singleton_isBasis, hC.subset_ground, hCs.trans, hI.fundCircuit_isCircuit, hI.mem_closure_iff, hI.subset, hI.subset_ground, insert_subset, mem_closure_iff, not_indep, sdiff_singleton_isBasis
-/
lemma IsCircuit.eq_fundCircuit_of_subset (hC : M.IsCircuit C) (hI : M.Indep I)
    (hCs : C subseteq insert e I) : C = M.fundCircuit e I := by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I subseteq C by
    refine hC.eq_of_superset_isCircuit (hI.fundCircuit_isCircuit ?_ fun heI => ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.superset hCs (insert_subset (hC.subset_ground heC) hI.subset_ground))
    exact hC.not_indep (hI.subset (hCs.trans (by simp [heI])))
  have heCcl := (hC.sdiff_singleton_isBasis heC).subset_closure heC
  have heI : e in M.closure I := M.closure_subset_closure hCeI heCcl
  rw [fundCircuit_eq_sInter heI]
refine insert_subset heC (sInter_subset_of_mem (t := C \ {e}) ?_).trans sdiff_subset
  exact ⟨hCeI, heCcl⟩

/--
lemma `fundCircuit_restrict` / 引理 `fundCircuit_restrict`

English:
lemma fundCircuit_restrict
  given: {R : Set α} (hIR : I subseteq R) (heR : e in R) (hR : R subseteq M.E)
  proof: by
  simp_rw [fundCircuit, M.restrict_closure_eq (R := R) (X := {e}) (by simpa)]
  apply subset_antisymm
  · gcongr 5 with J hJI; intro heJ
    simp only [restrict_closure_eq']
    refine (inter_subset_inter_left _ ?_).trans subset_union_left
    rwa [inter_eq_self_of_subset_left (hJI.trans hIR)]
  

中文:
引理 fundCircuit_restrict
  条件: {R : 集合 α} (hIR : I subseteq R) (heR : e in R) (hR : R subseteq M.E)
  证明: by
  simp_rw [fundCircuit, M.restrict_closure_eq (R := R) (X := {e}) (by simpa)]
  apply subset_antisymm
  · gcongr 5 with J hJI; intro heJ
    simp only [restrict_closure_eq']
    refine (inter_subset_inter_left _ ?_).trans subset_union_left
    rwa [inter_eq_self_of_subset_left (hJI.trans hIR)]
  

Depends on / 依赖: M.restrict_closure_eq, and_true, closure_subset_closure_of_subset_closure, fundCircuit, hJI.trans, inter_eq_self_of_subset_left, inter_subset_inter_left, inter_subset_right, restrict_closure_eq, simp_rw, subset_antisymm, subset_inter_iff, subset_trans, subset_union_left
-/
lemma fundCircuit_restrict {R : Set α} (hIR : I subseteq R) (heR : e in R) (hR : R subseteq M.E) :
    (M ↾ R).fundCircuit e I = M.fundCircuit e I := by
  simp_rw [fundCircuit, M.restrict_closure_eq (R := R) (X := {e}) (by simpa)]
  apply subset_antisymm
  · gcongr 5 with J hJI; intro heJ
    simp only [restrict_closure_eq']
    refine (inter_subset_inter_left _ ?_).trans subset_union_left
    rwa [inter_eq_self_of_subset_left (hJI.trans hIR)]
  gcongr 5 with J hJI; intro heJ
  refine closure_subset_closure_of_subset_closure ?_
  rw [restrict_closure_eq _ (hJI.trans hIR) hR] at heJ
  simp only [subset_inter_iff, inter_subset_right, and_true] at heJ
  exact subset_trans (by simpa [M.mem_closure_of_mem' (mem_singleton e) (hR heR)]) heJ

/--
lemma `fundCircuit_restrict_univ` / 引理 `fundCircuit_restrict_univ`

English:
lemma fundCircuit_restrict_univ
  given: (M : Matroid α)
  proof: by
  have aux (A B) : M.closure A subseteq B union univ \ M.E ↔ M.closure A subseteq B := by
    refine ⟨fun h => ?_, fun h => h.trans subset_union_left⟩
    refine (subset_inter h (M.closure_subset_ground A)).trans ?_
    simp [union_inter_distrib_right]
  simp [fundCircuit, aux]

中文:
引理 fundCircuit_restrict_univ
  条件: (M : 拟阵 α)
  证明: by
  have aux (A B) : M.closure A subseteq B union univ \ M.E ↔ M.closure A subseteq B := by
    refine ⟨fun h => ?_, fun h => h.trans subset_union_left⟩
    refine (subset_inter h (M.closure_subset_ground A)).trans ?_
    simp [union_inter_distrib_right]
  simp [fundCircuit, aux]
-/
@[simp] lemma fundCircuit_restrict_univ (M : Matroid α) :
    (M ↾ univ).fundCircuit e I = M.fundCircuit e I := by
  have aux (A B) : M.closure A subseteq B union univ \ M.E ↔ M.closure A subseteq B := by
    refine ⟨fun h => ?_, fun h => h.trans subset_union_left⟩
    refine (subset_inter h (M.closure_subset_ground A)).trans ?_
    simp [union_inter_distrib_right]
  simp [fundCircuit, aux]


/--
lemma `Dep.exists_isCircuit_subset` / 引理 `Dep.exists_isCircuit_subset`

English:
lemma Dep.exists_isCircuit_subset
  given: (hX : M.Dep X)
  statement: exists C, C subseteq X ∧ M.IsCircuit C
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCircuit e I, (M.fundCircuit_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCircuit_isCircuit (hI.sub

中文:
引理 Dep.存在_isCircuit_subset
  条件: (hX : M.Dep X)
  结论: 存在 C, C subseteq X ∧ M.是Circuit C
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCircuit e I, (M.fundCircuit_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCircuit_isCircuit (hI.sub

Depends on / 依赖: M.exists_isBasis, M.fundCircuit, M.fundCircuit_subset_insert, exists_isBasis, exists_of_ssubset, fundCircuit, fundCircuit_isCircuit, fundCircuit_subset_insert, hI.indep.fundCircuit_isCircuit, hI.indep.not_dep, hI.subset, hI.subset.ssubset_of_ne, hI.subset_closure, insert_subset, not_dep, ssubset_of_ne, subset, subset_closure
-/
lemma Dep.exists_isCircuit_subset (hX : M.Dep X) : exists C, C subseteq X ∧ M.IsCircuit C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCircuit e I, (M.fundCircuit_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCircuit_isCircuit (hI.subset_closure heX) heI⟩

/--
lemma `dep_iff_superset_isCircuit` / 引理 `dep_iff_superset_isCircuit`

English:
lemma dep_iff_superset_isCircuit
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: ⟨Dep.exists_isCircuit_subset, fun ⟨C, hCX, hC⟩ => hC.dep.superset hCX⟩

中文:
引理 dep_iff_superset_isCircuit
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: ⟨Dep.exists_isCircuit_subset, fun ⟨C, hCX, hC⟩ => hC.dep.superset hCX⟩

Depends on / 依赖: Dep.exists_isCircuit_subset, IsCircuit, M.Dep, M.IsCircuit, aesop_mat, exists_isCircuit_subset, hC.dep.superset, subseteq, superset
-/
lemma dep_iff_superset_isCircuit (hX : X subseteq M.E := by aesop_mat) :
    M.Dep X ↔ exists C, C subseteq X ∧ M.IsCircuit C :=
  ⟨Dep.exists_isCircuit_subset, fun ⟨C, hCX, hC⟩ => hC.dep.superset hCX⟩

/--
lemma `dep_iff_superset_isCircuit'` / 引理 `dep_iff_superset_isCircuit'`

English:
lemma dep_iff_superset_isCircuit'
  statement: M.Dep X ↔ (exists C, C subseteq X ∧ M.IsCircuit C) ∧ X subseteq M.E
  proof: ⟨fun h => ⟨h.exists_isCircuit_subset, h.subset_ground⟩,
    fun ⟨⟨C, hCX, hC⟩, h⟩ => hC.dep.superset hCX⟩

中文:
引理 dep_iff_superset_isCircuit'
  结论: M.Dep X ↔ (存在 C, C subseteq X ∧ M.是Circuit C) ∧ X subseteq M.E
  证明: ⟨fun h => ⟨h.exists_isCircuit_subset, h.subset_ground⟩,
    fun ⟨⟨C, hCX, hC⟩, h⟩ => hC.dep.superset hCX⟩

Depends on / 依赖: exists_isCircuit_subset, h.exists_isCircuit_subset, h.subset_ground, hC.dep.superset, subset_ground, superset
-/
lemma dep_iff_superset_isCircuit' : M.Dep X ↔ (exists C, C subseteq X ∧ M.IsCircuit C) ∧ X subseteq M.E :=
  ⟨fun h => ⟨h.exists_isCircuit_subset, h.subset_ground⟩,
    fun ⟨⟨C, hCX, hC⟩, h⟩ => hC.dep.superset hCX⟩

/--
lemma `indep_iff_forall_subset_not_isCircuit'` / 引理 `indep_iff_forall_subset_not_isCircuit'`

English:
lemma indep_iff_forall_subset_not_isCircuit'
  proof: by
  simp_rw [indep_iff_not_dep, dep_iff_superset_isCircuit']
  aesop

中文:
引理 indep_iff_对任意_subset_not_isCircuit'
  证明: by
  simp_rw [indep_iff_not_dep, dep_iff_superset_isCircuit']
  aesop

Depends on / 依赖: dep_iff_superset_isCircuit, indep_iff_not_dep, simp_rw
-/
lemma indep_iff_forall_subset_not_isCircuit' :
    M.Indep I ↔ (forall C, C subseteq I -> ¬M.IsCircuit C) ∧ I subseteq M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_isCircuit']
  aesop

/--
lemma `indep_iff_forall_subset_not_isCircuit` / 引理 `indep_iff_forall_subset_not_isCircuit`

English:
lemma indep_iff_forall_subset_not_isCircuit
  given: (hI : I subseteq M.E := by aesop_mat)
  proof: by
  rw [indep_iff_forall_subset_not_isCircuit']; rw [and_iff_left hI]

中文:
引理 indep_iff_对任意_subset_not_isCircuit
  条件: (hI : I subseteq M.E := by aesop_mat)
  证明: by
  rw [indep_iff_forall_subset_not_isCircuit']; rw [and_iff_left hI]

Depends on / 依赖: IsCircuit, M.Indep, M.IsCircuit, aesop_mat, and_iff_left, indep_iff_forall_subset_not_isCircuit, subseteq
-/
lemma indep_iff_forall_subset_not_isCircuit (hI : I subseteq M.E := by aesop_mat) :
    M.Indep I ↔ forall C, C subseteq I -> ¬M.IsCircuit C := by
  rw [indep_iff_forall_subset_not_isCircuit']; rw [and_iff_left hI]


/--
lemma `IsCircuit.closure_sdiff_singleton_eq` / 引理 `IsCircuit.closure_sdiff_singleton_eq`

English:
lemma IsCircuit.closure_sdiff_singleton_eq
  given: (hC : M.IsCircuit C) (e : α)
  proof: (em (e in C)).elim
    (fun he => by rw [(hC.sdiff_singleton_isBasis he).closure_eq_closure])
    (fun he => by rw [sdiff_singleton_eq_self he])

@[deprecated (since := "2026-06-03")]
alias IsCircuit.closure_diff_singleton_eq := IsCircuit.closure_sdiff_singleton_eq

中文:
引理 是Circuit.closure_sdiff_singleton_eq
  条件: (hC : M.是Circuit C) (e : α)
  证明: (em (e in C)).elim
    (fun he => by rw [(hC.sdiff_singleton_isBasis he).closure_eq_closure])
    (fun he => by rw [sdiff_singleton_eq_self he])

@[deprecated (since := "2026-06-03")]
alias IsCircuit.closure_diff_singleton_eq := IsCircuit.closure_sdiff_singleton_eq

Depends on / 依赖: closure_eq_closure, hC.sdiff_singleton_isBasis, sdiff_singleton_eq_self, sdiff_singleton_isBasis
-/
lemma IsCircuit.closure_sdiff_singleton_eq (hC : M.IsCircuit C) (e : α) :
    M.closure (C \ {e}) = M.closure C :=
  (em (e in C)).elim
    (fun he => by rw [(hC.sdiff_singleton_isBasis he).closure_eq_closure])
    (fun he => by rw [sdiff_singleton_eq_self he])

@[deprecated (since := "2026-06-03")]
alias IsCircuit.closure_diff_singleton_eq := IsCircuit.closure_sdiff_singleton_eq

/--
lemma `IsCircuit.subset_closure_sdiff_singleton` / 引理 `IsCircuit.subset_closure_sdiff_singleton`

English:
lemma IsCircuit.subset_closure_sdiff_singleton
  given: (hC : M.IsCircuit C) (e : α)
  proof: by
  rw [hC.closure_sdiff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

@[deprecated (since := "2026-06-03")]
alias IsCircuit.subset_closure_diff_singleton := IsCircuit.subset_closure_sdiff_singleton

中文:
引理 是Circuit.subset_closure_sdiff_singleton
  条件: (hC : M.是Circuit C) (e : α)
  证明: by
  rw [hC.closure_sdiff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

@[deprecated (since := "2026-06-03")]
alias IsCircuit.subset_closure_diff_singleton := IsCircuit.subset_closure_sdiff_singleton

Depends on / 依赖: M.subset_closure, closure_sdiff_singleton_eq, hC.closure_sdiff_singleton_eq, hC.subset_ground, subset_closure, subset_ground
-/
lemma IsCircuit.subset_closure_sdiff_singleton (hC : M.IsCircuit C) (e : α) :
    C subseteq M.closure (C \ {e}) := by
  rw [hC.closure_sdiff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

@[deprecated (since := "2026-06-03")]
alias IsCircuit.subset_closure_diff_singleton := IsCircuit.subset_closure_sdiff_singleton

/--
lemma `IsCircuit.mem_closure_sdiff_singleton_of_mem` / 引理 `IsCircuit.mem_closure_sdiff_singleton_of_mem`

English:
lemma IsCircuit.mem_closure_sdiff_singleton_of_mem
  given: (hC : M.IsCircuit C) (heC : e in C)
  proof: hC.subset_closure_sdiff_singleton e heC

@[deprecated (since := "2026-06-03")]
alias IsCircuit.mem_closure_diff_singleton_of_mem := IsCircuit.mem_closure_sdiff_singleton_of_mem

中文:
引理 是Circuit.mem_closure_sdiff_singleton_of_mem
  条件: (hC : M.是Circuit C) (heC : e in C)
  证明: hC.subset_closure_sdiff_singleton e heC

@[deprecated (since := "2026-06-03")]
alias IsCircuit.mem_closure_diff_singleton_of_mem := IsCircuit.mem_closure_sdiff_singleton_of_mem

Depends on / 依赖: hC.subset_closure_sdiff_singleton, subset_closure_sdiff_singleton
-/
lemma IsCircuit.mem_closure_sdiff_singleton_of_mem (hC : M.IsCircuit C) (heC : e in C) :
    e in M.closure (C \ {e}) :=
  hC.subset_closure_sdiff_singleton e heC

@[deprecated (since := "2026-06-03")]
alias IsCircuit.mem_closure_diff_singleton_of_mem := IsCircuit.mem_closure_sdiff_singleton_of_mem

/--
lemma `exists_isCircuit_of_mem_closure` / 引理 `exists_isCircuit_of_mem_closure`

English:
lemma exists_isCircuit_of_mem_closure
  given: (he : e in M.closure X) (heX : e ∉ X)
  proof: let ⟨I, hI⟩ := M.exists_isBasis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_isCircuit (by rwa [hI.closure_eq_closure]) (notMem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩

中文:
引理 存在_isCircuit_of_mem_closure
  条件: (he : e in M.closure X) (heX : e ∉ X)
  证明: let ⟨I, hI⟩ := M.exists_isBasis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_isCircuit (by rwa [hI.closure_eq_closure]) (notMem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩

Depends on / 依赖: M.exists_isBasis, M.mem_fundCircuit, closure_eq_closure, exists_isBasis, fundCircuit_isCircuit, fundCircuit_subset_insert, hI.closure_eq_closure, hI.indep.fundCircuit_isCircuit, hI.subset, insert_subset_insert, mem_fundCircuit, notMem_subset, subset
-/
lemma exists_isCircuit_of_mem_closure (he : e in M.closure X) (heX : e ∉ X) :
    exists C subseteq insert e X, M.IsCircuit C ∧ e in C :=
  let ⟨I, hI⟩ := M.exists_isBasis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_isCircuit (by rwa [hI.closure_eq_closure]) (notMem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩

/--
lemma `mem_closure_iff_exists_isCircuit` / 引理 `mem_closure_iff_exists_isCircuit`

English:
lemma mem_closure_iff_exists_isCircuit
  given: (he : e ∉ X)
  proof: ⟨fun h => exists_isCircuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ => mem_of_mem_of_subset
    (hC.mem_closure_sdiff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

中文:
引理 mem_closure_iff_存在_isCircuit
  条件: (he : e ∉ X)
  证明: ⟨fun h => exists_isCircuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ => mem_of_mem_of_subset
    (hC.mem_closure_sdiff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

Depends on / 依赖: M.closure_subset_closure, closure_subset_closure, exists_isCircuit_of_mem_closure, hC.mem_closure_sdiff_singleton_of_mem, mem_closure_sdiff_singleton_of_mem, mem_of_mem_of_subset
-/
lemma mem_closure_iff_exists_isCircuit (he : e ∉ X) :
    e in M.closure X ↔ exists C subseteq insert e X, M.IsCircuit C ∧ e in C :=
  ⟨fun h => exists_isCircuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ => mem_of_mem_of_subset
    (hC.mem_closure_sdiff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩


/--
lemma `ext_isCircuit` / 引理 `ext_isCircuit`

English:
lemma ext_isCircuit
  statement: {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
  proof: by
  have h' {C} : M₁.IsCircuit C ↔ M₂.IsCircuit C :=
    (em (C subseteq M₁.E)).elim (h (C := C)) (fun hC => iff_of_false (mt IsCircuit.subset_ground hC)
      (mt IsCircuit.subset_ground fun hss => hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI => ?_
  simp_rw [indep_iff_forall_subset_

中文:
引理 ext_isCircuit
  结论: {M₁ M₂ : 拟阵 α} (hE : M₁.E = M₂.E)
  证明: by
  have h' {C} : M₁.IsCircuit C ↔ M₂.IsCircuit C :=
    (em (C subseteq M₁.E)).elim (h (C := C)) (fun hC => iff_of_false (mt IsCircuit.subset_ground hC)
      (mt IsCircuit.subset_ground fun hss => hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI => ?_
  simp_rw [indep_iff_forall_subset_

Depends on / 依赖: IsCircuit, IsCircuit.subset_ground, ext_indep, hE.symm, hI.trans_eq, hss.trans_eq, iff_of_false, indep_iff_forall_subset_not_isCircuit, simp_rw, subset_ground, subseteq, trans_eq
-/
lemma ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : forall ⦃C⦄, C subseteq M₁.E -> (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ = M₂ := by
  have h' {C} : M₁.IsCircuit C ↔ M₂.IsCircuit C :=
    (em (C subseteq M₁.E)).elim (h (C := C)) (fun hC => iff_of_false (mt IsCircuit.subset_ground hC)
      (mt IsCircuit.subset_ground fun hss => hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI => ?_
  simp_rw [indep_iff_forall_subset_not_isCircuit hI, h',
    indep_iff_forall_subset_not_isCircuit (hI.trans_eq hE)]

/--
lemma `ext_isCircuit_not_indep` / 引理 `ext_isCircuit_not_indep`

English:
lemma ext_isCircuit_not_indep
  statement: {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
  proof: by
  refine ext_isCircuit hE fun C hCE => ⟨fun hC => ?_, fun hC => ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_isCircuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_isCir

中文:
引理 ext_isCircuit_not_indep
  结论: {M₁ M₂ : 拟阵 α} (hE : M₁.E = M₂.E)
  证明: by
  refine ext_isCircuit hE fun C hCE => ⟨fun hC => ?_, fun hC => ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_isCircuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_isCir

Depends on / 依赖: eq_of_not_indep_subset, exists_isCircuit_subset, ext_isCircuit, hC.eq_of_not_indep_subset, not_indep_iff
-/
lemma ext_isCircuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h₁ : forall C, M₁.IsCircuit C -> ¬ M₂.Indep C) (h₂ : forall C, M₂.IsCircuit C -> ¬ M₁.Indep C) :
    M₁ = M₂ := by
  refine ext_isCircuit hE fun C hCE => ⟨fun hC => ?_, fun hC => ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_isCircuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_isCircuit_subset
  rwa [← hC.eq_of_not_indep_subset (h₁ C' hC') hC'C]

/--
lemma `ext_iff_isCircuit` / 引理 `ext_iff_isCircuit`

English:
lemma ext_iff_isCircuit
  given: {M₁ M₂ : Matroid α}
  proof: ⟨fun h => by simp [h], fun h => ext_isCircuit h.1 fun C hC => h.2 (C := C)⟩

中文:
引理 ext_iff_isCircuit
  条件: {M₁ M₂ : 拟阵 α}
  证明: ⟨fun h => by simp [h], fun h => ext_isCircuit h.1 fun C hC => h.2 (C := C)⟩

Depends on / 依赖: ext_isCircuit
-/
lemma ext_iff_isCircuit {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ forall C, M₁.IsCircuit C ↔ M₂.IsCircuit C :=
  ⟨fun h => by simp [h], fun h => ext_isCircuit h.1 fun C hC => h.2 (C := C)⟩

section Elimination

/-! ### Circuit Elimination -/

variable {ι : Type*} {J C₀ C₁ C₂ : Set α}

/--
lemma `IsCircuit.strong_multi_elimination_insert` / 引理 `IsCircuit.strong_multi_elimination_insert`

English:
lemma IsCircuit.strong_multi_elimination_insert
  statement: (x : ι -> α) (I : ι -> Set α) (z : α)
  proof: by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z in M.closure ((⋃ i, I i) union (J \ {z})) 

中文:
引理 是Circuit.strong_multi_elimination_insert
  结论: (x : ι -> α) (I : ι -> 集合 α) (z : α)
  证明: by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z in M.closure ((⋃ i, I i) union (J \ {z})) 
-/
lemma IsCircuit.strong_multi_elimination_insert (x : ι -> α) (I : ι -> Set α) (z : α)
    (hxI : forall i, x i ∉ I i) (hC : forall i, M.IsCircuit (insert (x i) (I i)))
    (hJx : M.IsCircuit (J union range x)) (hzJ : z in J) (hzI : forall i, z ∉ I i) :
    exists C' subseteq J union ⋃ i, I i, M.IsCircuit C' ∧ z in C' := by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z in M.closure ((⋃ i, I i) union (J \ {z})) by
    rw [mem_closure_iff_exists_isCircuit (by simp [hzI])] at hcl
    obtain ⟨C', hC'ss, hC', hzC'⟩ := hcl
    refine ⟨C', ?_, hC', hzC'⟩
    rwa [union_comm, ← insert_union, insert_sdiff_singleton, insert_eq_of_mem hzJ] at hC'ss
  have hC' (i) : M.closure (I i) = M.closure (insert (x i) (I i)) := by
    simpa [sdiff_singleton_eq_self (hxI _)] using (hC i).closure_sdiff_singleton_eq (x i)
  -- This is true because each `I i` spans `x i` and `(range x) ∪ (J \ {z})` spans `z`.
  rw [closure_union_congr_left <| closure_iUnion_congr _ _ hC']; rw [iUnion_insert_eq_range_union_iUnion]; rw [union_right_comm]
  refine mem_of_mem_of_subset (hJx.mem_closure_sdiff_singleton_of_mem (.inl hzJ))
    (M.closure_subset_closure (subset_trans ?_ subset_union_left))
  rw [union_sdiff_distrib]; rw [union_comm]
  exact union_subset_union_left _ sdiff_subset

/--
lemma `IsCircuit.strong_multi_elimination` / 引理 `IsCircuit.strong_multi_elimination`

English:
lemma IsCircuit.strong_multi_elimination
  statement: (hC₀ : M.IsCircuit C₀) (x : ι -> α) (C : ι -> Set α) (z : α)
  proof: by
  have hwin := IsCircuit.strong_multi_elimination_insert (M := M) x (fun i => (C i \ {x i}))
    (J := C₀ \ range x) (z := z) (by simp) (fun i => ?_) ?_ ⟨hzC₀, ?_⟩ ?_
  · obtain ⟨C', hC'ss, hC', hzC'⟩ := hwin
    refine ⟨C', hC'ss.trans ?_, hC', hzC'⟩
    refine union_subset (sdiff_subset_sdiff_l

中文:
引理 是Circuit.strong_multi_elimination
  结论: (hC₀ : M.是Circuit C₀) (x : ι -> α) (C : ι -> 集合 α) (z : α)
  证明: by
  have hwin := IsCircuit.strong_multi_elimination_insert (M := M) x (fun i => (C i \ {x i}))
    (J := C₀ \ range x) (z := z) (by simp) (fun i => ?_) ?_ ⟨hzC₀, ?_⟩ ?_
  · obtain ⟨C', hC'ss, hC', hzC'⟩ := hwin
    refine ⟨C', hC'ss.trans ?_, hC', hzC'⟩
    refine union_subset (sdiff_subset_sdiff_l

Depends on / 依赖: IsCircuit, IsCircuit.strong_multi_elimination_insert, disjoint_iff_forall_ne, iUnion_subset, sdiff_subset, sdiff_subset.trans, sdiff_subset_sdiff_left, ss.trans, strong_multi_elimination_insert, subset_iUnion, subset_sdiff, subset_union_left, subset_union_of_subset_right, union_subset
-/
lemma IsCircuit.strong_multi_elimination (hC₀ : M.IsCircuit C₀) (x : ι -> α) (C : ι -> Set α) (z : α)
    (hC : forall i, M.IsCircuit (C i)) (h_mem_C₀ : forall i, x i in C₀) (h_mem : forall i, x i in C i)
    (h_unique : forall ⦃i i'⦄, x i in C i' -> i = i') (hzC₀ : z in C₀) (hzC : forall i, z ∉ C i) :
    exists C' subseteq (C₀ union ⋃ i, C i) \ range x, M.IsCircuit C' ∧ z in C' := by
  have hwin := IsCircuit.strong_multi_elimination_insert (M := M) x (fun i => (C i \ {x i}))
    (J := C₀ \ range x) (z := z) (by simp) (fun i => ?_) ?_ ⟨hzC₀, ?_⟩ ?_
  · obtain ⟨C', hC'ss, hC', hzC'⟩ := hwin
    refine ⟨C', hC'ss.trans ?_, hC', hzC'⟩
    refine union_subset (sdiff_subset_sdiff_left subset_union_left)
      (iUnion_subset fun i => subset_sdiff.2
        ⟨sdiff_subset.trans (subset_union_of_subset_right (subset_iUnion ..) _), ?_⟩)
    rw [disjoint_iff_forall_ne]
    rintro _ he _ ⟨j, hj, rfl⟩ rfl
    obtain rfl : j = i := h_unique he.1
    simp at he
  · simpa [insert_eq_of_mem (h_mem i)] using hC i
  · rwa [sdiff_union_self, union_eq_self_of_subset_right]
    rintro _ ⟨i, hi, rfl⟩
    exact h_mem_C₀ i
  · rintro ⟨i, hi, rfl⟩
    exact hzC _ (h_mem i)
  simp only [mem_sdiff, mem_singleton_iff, not_and, not_not]
  exact fun i hzi => (hzC i hzi).elim

/--
lemma `IsCircuit.strong_multi_elimination_set` / 引理 `IsCircuit.strong_multi_elimination_set`

English:
lemma IsCircuit.strong_multi_elimination_set
  statement: (hC₀ : M.IsCircuit C₀) (X : Set α) (S : Set (Set α))
  proof: by
  choose! C hC using hX
  simp only [forall_and] at hC
  have hwin := hC₀.strong_multi_elimination (fun x : X => x) (fun x => C x) z ?_ ?_ ?_ ?_ hzC₀ ?_
  · obtain ⟨C', hC'ss, hC', hz⟩ := hwin
    refine ⟨C', hC'ss.trans (sdiff_subset_sdiff (union_subset_union_right _ ?_) (by simp)), hC', hz⟩
   

中文:
引理 是Circuit.strong_multi_elimination_set
  结论: (hC₀ : M.是Circuit C₀) (X : 集合 α) (S : 集合 (集合 α))
  证明: by
  choose! C hC using hX
  simp only [forall_and] at hC
  have hwin := hC₀.strong_multi_elimination (fun x : X => x) (fun x => C x) z ?_ ?_ ?_ ?_ hzC₀ ?_
  · obtain ⟨C', hC'ss, hC', hz⟩ := hwin
    refine ⟨C', hC'ss.trans (sdiff_subset_sdiff (union_subset_union_right _ ?_) (by simp)), hC', hz⟩
   

Depends on / 依赖: Subtype, Subtype.forall, forall_and, sdiff_subset_sdiff, singleton_subset_iff, ss.trans, strong_multi_elimination, subset_sUnion_of_mem, union_subset_union_right
-/
lemma IsCircuit.strong_multi_elimination_set (hC₀ : M.IsCircuit C₀) (X : Set α) (S : Set (Set α))
    (z : α) (hCS : forall C in S, M.IsCircuit C) (hXC₀ : X subseteq C₀) (hX : forall x in X, exists C in S, C inter X = {x})
    (hzC₀ : z in C₀) (hz : forall C in S, z ∉ C) : exists C' subseteq (C₀ union ⋃₀ S) \ X, M.IsCircuit C' ∧ z in C' := by
  choose! C hC using hX
  simp only [forall_and] at hC
  have hwin := hC₀.strong_multi_elimination (fun x : X => x) (fun x => C x) z ?_ ?_ ?_ ?_ hzC₀ ?_
  · obtain ⟨C', hC'ss, hC', hz⟩ := hwin
    refine ⟨C', hC'ss.trans (sdiff_subset_sdiff (union_subset_union_right _ ?_) (by simp)), hC', hz⟩
    simpa using fun e heX => (subset_sUnion_of_mem (hC.1 e heX))
· simpa using fun e heX => hCS _ hC.1 e heX
  · simpa using fun e heX => hXC₀ heX
  · simp only [Subtype.forall, ← singleton_subset_iff (s := C _)]
    exact fun e heX => by simp [← hC.2 e heX]
  · simp only [Subtype.forall, Subtype.mk.injEq]
    refine fun e heX f hfX hef => ?_
    simpa [hC.2 f hfX] using subset_inter (singleton_subset_iff.2 hef) (singleton_subset_iff.2 heX)
  simpa using fun e heX heC => hz _ (hC.1 e heX) heC

/--
lemma `IsCircuit.strong_elimination` / 引理 `IsCircuit.strong_elimination`

English:
lemma IsCircuit.strong_elimination
  statement: (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (heC₁ : e in C₁)
  proof: by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit => e) (fun _ => C₂) f
    (by simpa) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (sdiff_subset_sdiff (by simp) (by simp)), hC, hfC⟩

中文:
引理 是Circuit.strong_elimination
  结论: (hC₁ : M.是Circuit C₁) (hC₂ : M.是Circuit C₂) (heC₁ : e in C₁)
  证明: by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit => e) (fun _ => C₂) f
    (by simpa) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (sdiff_subset_sdiff (by simp) (by simp)), hC, hfC⟩

Depends on / 依赖: hCs.trans, sdiff_subset_sdiff, strong_multi_elimination
-/
lemma IsCircuit.strong_elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (heC₁ : e in C₁)
    (heC₂ : e in C₂) (hfC₁ : f in C₁) (hfC₂ : f ∉ C₂) :
    exists C subseteq (C₁ union C₂) \ {e}, M.IsCircuit C ∧ f in C := by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit => e) (fun _ => C₂) f
    (by simpa) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (sdiff_subset_sdiff (by simp) (by simp)), hC, hfC⟩

/--
lemma `IsCircuit.elimination` / 引理 `IsCircuit.elimination`

English:
lemma IsCircuit.elimination
  given: (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (h : C₁ != C₂) (e : α)
  proof: by
have hnss : ¬ (C₁ subseteq C₂) := fun hss => h hC₁.eq_of_subset_isCircuit hC₂ hss
  obtain ⟨f, hf₁, hf₂⟩ := not_subset.1 hnss
  by_cases he₁ : e in C₁
  · by_cases he₂ : e in C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subs

中文:
引理 是Circuit.elimination
  条件: (hC₁ : M.是Circuit C₁) (hC₂ : M.是Circuit C₂) (h : C₁ != C₂) (e : α)
  证明: by
have hnss : ¬ (C₁ subseteq C₂) := fun hss => h hC₁.eq_of_subset_isCircuit hC₂ hss
  obtain ⟨f, hf₁, hf₂⟩ := not_subset.1 hnss
  by_cases he₁ : e in C₁
  · by_cases he₂ : e in C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subs

Depends on / 依赖: eq_of_subset_isCircuit, not_subset, strong_elimination, subset_sdiff_singleton, subset_union_left, subset_union_right, subseteq
-/
lemma IsCircuit.elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (h : C₁ != C₂) (e : α) :
    exists C subseteq (C₁ union C₂) \ {e}, M.IsCircuit C := by
have hnss : ¬ (C₁ subseteq C₂) := fun hss => h hC₁.eq_of_subset_isCircuit hC₂ hss
  obtain ⟨f, hf₁, hf₂⟩ := not_subset.1 hnss
  by_cases he₁ : e in C₁
  · by_cases he₂ : e in C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subset_sdiff_singleton subset_union_right he₂, hC₂⟩
  exact ⟨C₁, subset_sdiff_singleton subset_union_left he₁, hC₁⟩

end Elimination

/-! ### Finitary Matroids -/
section Finitary

/--
lemma `IsCircuit.finite` / 引理 `IsCircuit.finite`

English:
lemma IsCircuit.finite
  given: [Finitary M] (hC : M.IsCircuit C)
  statement: C.Finite
  proof: by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push Not at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

中文:
引理 是Circuit.finite
  条件: [Finitary M] (hC : M.是Circuit C)
  结论: C.有限
  证明: by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push Not at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

Depends on / 依赖: eq_of_not_indep_subset, hC.dep.not_indep, hC.eq_of_not_indep_subset, indep_iff_forall_finite_subset_indep, not_indep
-/
lemma IsCircuit.finite [Finitary M] (hC : M.IsCircuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push Not at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

/--
lemma `finitary_iff_forall_isCircuit_finite` / 引理 `finitary_iff_forall_isCircuit_finite`

English:
lemma finitary_iff_forall_isCircuit_finite
  statement: M.Finitary ↔ forall C, M.IsCircuit C -> C.Finite
  proof: by
  refine ⟨fun _ _ => IsCircuit.finite, fun h =>
    ⟨fun I hI => indep_iff_not_dep.2 ⟨fun hd => ?_,fun x hx => ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
exact hC.dep.not_indep hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

中文:
引理 finitary_iff_对任意_isCircuit_finite
  结论: M.Finitary ↔ 对任意 C, M.是Circuit C -> C.有限
  证明: by
  refine ⟨fun _ _ => IsCircuit.finite, fun h =>
    ⟨fun I hI => indep_iff_not_dep.2 ⟨fun hd => ?_,fun x hx => ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
exact hC.dep.not_indep hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

Depends on / 依赖: IsCircuit, IsCircuit.finite, exists_isCircuit_subset, finite, finite_singleton, hC.dep.not_indep, hd.exists_isCircuit_subset, indep_iff_not_dep, not_indep, subset_ground
-/
lemma finitary_iff_forall_isCircuit_finite : M.Finitary ↔ forall C, M.IsCircuit C -> C.Finite := by
  refine ⟨fun _ _ => IsCircuit.finite, fun h =>
    ⟨fun I hI => indep_iff_not_dep.2 ⟨fun hd => ?_,fun x hx => ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
exact hC.dep.not_indep hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

/--
lemma `exists_mem_finite_closure_of_mem_closure` / 引理 `exists_mem_finite_closure_of_mem_closure`

English:
lemma exists_mem_finite_closure_of_mem_closure
  given: [M.Finitary] (he : e in M.closure X)
  proof: by
  by_cases heY : e in X
  · obtain ⟨J, hJ⟩ := M.exists_isBasis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_isCircuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC

中文:
引理 存在_mem_finite_closure_of_mem_closure
  条件: [M.Finitary] (he : e in M.closure X)
  证明: by
  by_cases heY : e in X
  · obtain ⟨J, hJ⟩ := M.exists_isBasis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_isCircuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC

Depends on / 依赖: M.exists_isBasis, exists_isBasis, exists_isCircuit_of_mem_closure, finite, finite_singleton, hC.finite.sdiff, hC.mem_closure_sdiff_singleton_of_mem, hC.sdiff_singleton_indep, hJ.indep, hJ.subset, hJ.subset.trans, hJ.subset_closure, mem_closure_sdiff_singleton_of_mem, sdiff_singleton_indep, subset, subset_closure
-/
lemma exists_mem_finite_closure_of_mem_closure [M.Finitary] (he : e in M.closure X) :
    exists I subseteq X, I.Finite ∧ M.Indep I ∧ e in M.closure I := by
  by_cases heY : e in X
  · obtain ⟨J, hJ⟩ := M.exists_isBasis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_isCircuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC.finite.sdiff, hC.sdiff_singleton_indep heC,
    hC.mem_closure_sdiff_singleton_of_mem heC⟩

/--
lemma `exists_subset_finite_closure_of_subset_closure` / 引理 `exists_subset_finite_closure_of_subset_closure`

English:
lemma exists_subset_finite_closure_of_subset_closure
  statement: [M.Finitary] (hX : X.Finite)
  proof: by
  suffices aux : exists T subseteq Y, T.Finite ∧ X subseteq M.closure T by
    obtain ⟨T, hT, hTfin, hXT⟩ := aux
    obtain ⟨I, hI⟩ := M.exists_isBasis' T
    exact ⟨_, hI.subset.trans hT, hTfin.subset hI.subset, hI.indep, by rwa [hI.closure_eq_closure]⟩
  refine Finite.induction_on_subset X hX ⟨

中文:
引理 存在_subset_finite_closure_of_subset_closure
  结论: [M.Finitary] (hX : X.有限)
  证明: by
  suffices aux : exists T subseteq Y, T.Finite ∧ X subseteq M.closure T by
    obtain ⟨T, hT, hTfin, hXT⟩ := aux
    obtain ⟨I, hI⟩ := M.exists_isBasis' T
    exact ⟨_, hI.subset.trans hT, hTfin.subset hI.subset, hI.indep, by rwa [hI.closure_eq_closure]⟩
  refine Finite.induction_on_subset X hX ⟨

Depends on / 依赖: Finite, Finite.induction_on_subset, M.closure, M.exists_isBasis, T.Finite, closure, closure_eq_closure, exists_isBasis, exists_mem_finite_closure_of_mem_closure, hI.closure_eq_closure, hI.indep, hI.subset, hI.subset.trans, hSfin.union, hTfin.subset, induction_on_subset, insert_subse, subset, subseteq, union_subset
-/
lemma exists_subset_finite_closure_of_subset_closure [M.Finitary] (hX : X.Finite)
    (hXY : X subseteq M.closure Y) : exists I subseteq Y, I.Finite ∧ M.Indep I ∧ X subseteq M.closure I := by
  suffices aux : exists T subseteq Y, T.Finite ∧ X subseteq M.closure T by
    obtain ⟨T, hT, hTfin, hXT⟩ := aux
    obtain ⟨I, hI⟩ := M.exists_isBasis' T
    exact ⟨_, hI.subset.trans hT, hTfin.subset hI.subset, hI.indep, by rwa [hI.closure_eq_closure]⟩
  refine Finite.induction_on_subset X hX ⟨∅, by simp⟩ (fun {e Z} heX _ heZ ⟨T, hTY, hTfin, hT⟩ => ?_)
  obtain ⟨S, hSY, hSfin, -, heS⟩ := exists_mem_finite_closure_of_mem_closure (hXY heX)
  exact ⟨S union T, union_subset hSY hTY, hSfin.union hTfin, insert_subset
    (M.closure_mono subset_union_left heS) (hT.trans (M.closure_mono subset_union_right))⟩

end Finitary

/-! ### IsCocircuits -/
section IsCocircuit

variable {K B : Set α}

/--
Definition of `IsCocircuit` / `IsCocircuit` 的定义

English:
abbreviation IsCocircuit
  signature: (M : Matroid α) (K : Set α)
  body: M✶.IsCircuit K

中文:
缩写 IsCocircuit
  签名: (M : 拟阵 α) (K : 集合 α)
  定义体: M✶.IsCircuit K

Depends on / 依赖: IsCircuit
-/
abbrev IsCocircuit (M : Matroid α) (K : Set α) : Prop := M✶.IsCircuit K

/--
lemma `isCocircuit_def` / 引理 `isCocircuit_def`

English:
lemma isCocircuit_def
  statement: M.IsCocircuit K ↔ M✶.IsCircuit K
  proof: Iff.rfl

中文:
引理 isCocircuit_def
  结论: M.IsCocircuit K ↔ M✶.是Circuit K
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircuit K := Iff.rfl

/--
lemma `IsCocircuit.isCircuit` / 引理 `IsCocircuit.isCircuit`

English:
lemma IsCocircuit.isCircuit
  given: (hK : M.IsCocircuit K)
  statement: M✶.IsCircuit K
  proof: hK

中文:
引理 IsCocircuit.isCircuit
  条件: (hK : M.IsCocircuit K)
  结论: M✶.是Circuit K
  证明: hK
-/
lemma IsCocircuit.isCircuit (hK : M.IsCocircuit K) : M✶.IsCircuit K :=
  hK

/--
lemma `IsCircuit.isCocircuit` / 引理 `IsCircuit.isCocircuit`

English:
lemma IsCircuit.isCocircuit
  given: (hC : M.IsCircuit C)
  statement: M✶.IsCocircuit C
  proof: by
  rwa [isCocircuit_def, dual_dual]

中文:
引理 是Circuit.isCocircuit
  条件: (hC : M.是Circuit C)
  结论: M✶.IsCocircuit C
  证明: by
  rwa [isCocircuit_def, dual_dual]

Depends on / 依赖: dual_dual, isCocircuit_def
-/
lemma IsCircuit.isCocircuit (hC : M.IsCircuit C) : M✶.IsCocircuit C := by
  rwa [isCocircuit_def, dual_dual]

/--
lemma `IsCocircuit.nonempty` / 引理 `IsCocircuit.nonempty`

English:
lemma IsCocircuit.nonempty
  given: (hC : M.IsCocircuit C)
  statement: C.Nonempty
  proof: hC.isCircuit.nonempty

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
引理 IsCocircuit.nonempty
  条件: (hC : M.IsCocircuit C)
  结论: C.非空
  证明: hC.isCircuit.nonempty

@[aesop unsafe 10% (rule_sets := [Matroid])]

Depends on / 依赖: hC.isCircuit.nonempty, isCircuit, nonempty
-/
lemma IsCocircuit.nonempty (hC : M.IsCocircuit C) : C.Nonempty :=
  hC.isCircuit.nonempty

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
lemma `IsCocircuit.subset_ground` / 引理 `IsCocircuit.subset_ground`

English:
lemma IsCocircuit.subset_ground
  given: (hC : M.IsCocircuit C)
  statement: C subseteq M.E
  proof: hC.isCircuit.subset_ground

中文:
引理 IsCocircuit.subset_ground
  条件: (hC : M.IsCocircuit C)
  结论: C subseteq M.E
  证明: hC.isCircuit.subset_ground

Depends on / 依赖: hC.isCircuit.subset_ground, isCircuit, subset_ground
-/
lemma IsCocircuit.subset_ground (hC : M.IsCocircuit C) : C subseteq M.E :=
  hC.isCircuit.subset_ground

/--
lemma `dual_isCocircuit_iff` / 引理 `dual_isCocircuit_iff`

English:
lemma dual_isCocircuit_iff
  statement: M✶.IsCocircuit C ↔ M.IsCircuit C
  proof: by
  rw [isCocircuit_def]; rw [dual_dual]

中文:
引理 dual_isCocircuit_iff
  结论: M✶.IsCocircuit C ↔ M.是Circuit C
  证明: by
  rw [isCocircuit_def]; rw [dual_dual]
-/
@[simp] lemma dual_isCocircuit_iff : M✶.IsCocircuit C ↔ M.IsCircuit C := by
  rw [isCocircuit_def]; rw [dual_dual]

/--
lemma `coindep_iff_forall_subset_not_isCocircuit` / 引理 `coindep_iff_forall_subset_not_isCocircuit`

English:
lemma coindep_iff_forall_subset_not_isCocircuit
  proof: indep_iff_forall_subset_not_isCircuit'

中文:
引理 coindep_iff_对任意_subset_not_isCocircuit
  证明: indep_iff_forall_subset_not_isCircuit'

Depends on / 依赖: indep_iff_forall_subset_not_isCircuit
-/
lemma coindep_iff_forall_subset_not_isCocircuit :
    M.Coindep X ↔ (forall K, K subseteq X -> ¬M.IsCocircuit K) ∧ X subseteq M.E :=
  indep_iff_forall_subset_not_isCircuit'

/--
lemma `isCocircuit_iff_minimal` / 引理 `isCocircuit_iff_minimal`

English:
lemma isCocircuit_iff_minimal
  proof: by
  have aux : M✶.Dep = fun X => (forall B, M.IsBase B -> (X inter B).Nonempty) ∧ X subseteq M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def]; rw [isCircuit_def]; rw [aux]; rw [iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h => h.1) fun X hX =>
    ⟨X inter M.E, 

中文:
引理 isCocircuit_iff_minimal
  证明: by
  have aux : M✶.Dep = fun X => (forall B, M.IsBase B -> (X inter B).Nonempty) ∧ X subseteq M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def]; rw [isCircuit_def]; rw [aux]; rw [iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h => h.1) fun X hX =>
    ⟨X inter M.E, 

Depends on / 依赖: IsBase, M.IsBase, Nonempty, dual_dep_iff_forall, hB.subset_ground, iff_comm, inter_assoc, inter_eq_self_of_subset_right, inter_subset_left, inter_subset_right, isCircuit_def, isCocircuit_def, minimal_iff_minimal_of_imp_of_forall, subset_ground, subseteq
-/
lemma isCocircuit_iff_minimal :
    M.IsCocircuit K ↔ Minimal (fun X => forall B, M.IsBase B -> (X inter B).Nonempty) K := by
  have aux : M✶.Dep = fun X => (forall B, M.IsBase B -> (X inter B).Nonempty) ∧ X subseteq M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def]; rw [isCircuit_def]; rw [aux]; rw [iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h => h.1) fun X hX =>
    ⟨X inter M.E, inter_subset_left, fun B hB => ?_, inter_subset_right⟩
  rw [inter_assoc]; rw [inter_eq_self_of_subset_right hB.subset_ground]
  exact hX B hB

/--
lemma `isCocircuit_iff_minimal_compl_nonspanning` / 引理 `isCocircuit_iff_minimal_compl_nonspanning`

English:
lemma isCocircuit_iff_minimal_compl_nonspanning
  proof: by
  convert! isCocircuit_iff_minimal with K
  rw [spanning_iff_exists_isBase_subset]
  simp_rw [not_exists, subset_sdiff, not_and, not_disjoint_iff_nonempty_inter, ← and_imp,
    and_iff_left_of_imp IsBase.subset_ground, inter_comm K]

中文:
引理 isCocircuit_iff_minimal_compl_nonspanning
  证明: by
  convert! isCocircuit_iff_minimal with K
  rw [spanning_iff_exists_isBase_subset]
  simp_rw [not_exists, subset_sdiff, not_and, not_disjoint_iff_nonempty_inter, ← and_imp,
    and_iff_left_of_imp IsBase.subset_ground, inter_comm K]

Depends on / 依赖: IsBase, IsBase.subset_ground, and_iff_left_of_imp, and_imp, convert, inter_comm, isCocircuit_iff_minimal, not_and, not_disjoint_iff_nonempty_inter, not_exists, simp_rw, spanning_iff_exists_isBase_subset, subset_ground, subset_sdiff
-/
lemma isCocircuit_iff_minimal_compl_nonspanning :
    M.IsCocircuit K ↔ Minimal (fun X => ¬ M.Spanning (M.E \ X)) K := by
  convert! isCocircuit_iff_minimal with K
  rw [spanning_iff_exists_isBase_subset]
  simp_rw [not_exists, subset_sdiff, not_and, not_disjoint_iff_nonempty_inter, ← and_imp,
    and_iff_left_of_imp IsBase.subset_ground, inter_comm K]

/--
lemma `IsBase.compl_closure_sdiff_singleton_isCocircuit` / 引理 `IsBase.compl_closure_sdiff_singleton_isCocircuit`

English:
lemma IsBase.compl_closure_sdiff_singleton_isCocircuit
  given: (hB : M.IsBase B) (he : e in B)
  proof: by
  rw [isCocircuit_iff_minimal_compl_nonspanning]; rw [minimal_subset_iff]; rw [sdiff_sdiff_cancel_left (M.closure_subset_ground _)]; rw [closure_spanning_iff (sdiff_subset.trans hB.subset_ground)]
  have hB' := (isBase_iff_minimal_spanning.1 hB)
  refine ⟨fun hsp => hB'.notMem_of_prop_sdiff_singl

中文:
引理 IsBase.compl_closure_sdiff_singleton_isCocircuit
  条件: (hB : M.IsBase B) (he : e in B)
  证明: by
  rw [isCocircuit_iff_minimal_compl_nonspanning]; rw [minimal_subset_iff]; rw [sdiff_sdiff_cancel_left (M.closure_subset_ground _)]; rw [closure_spanning_iff (sdiff_subset.trans hB.subset_ground)]
  have hB' := (isBase_iff_minimal_spanning.1 hB)
  refine ⟨fun hsp => hB'.notMem_of_prop_sdiff_singl

Depends on / 依赖: IsBase, M.IsBase, M.closure_subset_ground, antisymm, closure_spanning_iff, closure_subset_ground, hB.subset_ground, hXss.antisymm, hsp.spa, insert, isBase_iff_minimal_spanning, isCocircuit_iff_minimal_compl_nonspanning, minimal_subset_iff, notMem_of_prop_sdiff_singleton, sdiff_sdiff_cancel_left, sdiff_subset, sdiff_subset.trans, sdiff_subset_comm, subset_ground, subset_sdiff
-/
lemma IsBase.compl_closure_sdiff_singleton_isCocircuit (hB : M.IsBase B) (he : e in B) :
    M.IsCocircuit (M.E \ M.closure (B \ {e})) := by
  rw [isCocircuit_iff_minimal_compl_nonspanning]; rw [minimal_subset_iff]; rw [sdiff_sdiff_cancel_left (M.closure_subset_ground _)]; rw [closure_spanning_iff (sdiff_subset.trans hB.subset_ground)]
  have hB' := (isBase_iff_minimal_spanning.1 hB)
  refine ⟨fun hsp => hB'.notMem_of_prop_sdiff_singleton hsp he, fun X hX hXss => hXss.antisymm' ?_⟩
  rw [sdiff_subset_comm]
  refine fun f hf => by_contra fun fcl => hX ?_
  rw [subset_sdiff] at hXss
  suffices hsp : M.IsBase (insert f (B \ {e})) by
refine hsp.spanning.superset insert_subset hf
      (M.subset_closure _ (sdiff_subset.trans hB.subset_ground)).trans ?_
    rw [subset_sdiff]; rw [and_iff_left hXss.2.symm]
    apply closure_subset_ground
  exact hB.exchange_base_of_notMem_closure he fcl

@[deprecated (since := "2026-06-03")]
alias IsBase.compl_closure_diff_singleton_isCocircuit :=
  IsBase.compl_closure_sdiff_singleton_isCocircuit

/--
lemma `isCocircuit_iff_minimal_compl_nonspanning'` / 引理 `isCocircuit_iff_minimal_compl_nonspanning'`

English:
lemma isCocircuit_iff_minimal_compl_nonspanning'
  proof: by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h => h.1)
    (fun X hX => ⟨X inter M.E, inter_subset_left, by rwa [sdiff_inter_self_eq_sdiff],
      inter_subset_right⟩)

中文:
引理 isCocircuit_iff_minimal_compl_nonspanning'
  证明: by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h => h.1)
    (fun X hX => ⟨X inter M.E, inter_subset_left, by rwa [sdiff_inter_self_eq_sdiff],
      inter_subset_right⟩)

Depends on / 依赖: inter_subset_left, inter_subset_right, isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_minimal_of_imp_of_forall, sdiff_inter_self_eq_sdiff
-/
lemma isCocircuit_iff_minimal_compl_nonspanning' :
    M.IsCocircuit K ↔ Minimal (fun X => ¬ M.Spanning (M.E \ X) ∧ X subseteq M.E) K := by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h => h.1)
    (fun X hX => ⟨X inter M.E, inter_subset_left, by rwa [sdiff_inter_self_eq_sdiff],
      inter_subset_right⟩)

/--
lemma `IsCircuit.inter_isCocircuit_ne_singleton` / 引理 `IsCircuit.inter_isCocircuit_ne_singleton`

English:
lemma IsCircuit.inter_isCocircuit_ne_singleton
  given: (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
  proof: by
  intro he
  have heC : e in C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (sdiff_singleton_ssubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  

中文:
引理 是Circuit.inter_isCocircuit_ne_singleton
  条件: (hC : M.是Circuit C) (hK : M.IsCocircuit K)
  证明: by
  intro he
  have heC : e in C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (sdiff_singleton_ssubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  

Depends on / 依赖: M.closure_subset_closure, closure_eq, closure_subset_closure, closure_uni, hKe.closure_eq, he.symm.subset, insert_eq_of_mem, isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not, nth_rw, sdiff_sdiff_eq_sdiff_union, sdiff_singleton_ssubset, simp_rw, singleton_union, spanning_iff_ground_subset_closure, subset, subset_union_left, union_assoc
-/
lemma IsCircuit.inter_isCocircuit_ne_singleton (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    C inter K != {e} := by
  intro he
  have heC : e in C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (sdiff_singleton_ssubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  nth_rw 1 [← hKe.closure_eq, sdiff_sdiff_eq_sdiff_union]
  · refine (M.closure_subset_closure (subset_union_left (t := C))).trans ?_
    rw [union_assoc]; rw [singleton_union]; rw [insert_eq_of_mem heC]; rw [← closure_union_congr_right
      (hC.closure_sdiff_singleton_eq e)]; rw [union_eq_self_of_subset_right]
    rw [← he]; rw [sdiff_self_inter]
    exact sdiff_subset_sdiff_left hC.subset_ground
  rw [← he]
  exact inter_subset_left.trans hC.subset_ground

/--
lemma `IsCircuit.isCocircuit_inter_nontrivial` / 引理 `IsCircuit.isCocircuit_inter_nontrivial`

English:
lemma IsCircuit.isCocircuit_inter_nontrivial
  statement: (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
  proof: by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK

中文:
引理 是Circuit.isCocircuit_inter_nontrivial
  结论: (hC : M.是Circuit C) (hK : M.IsCocircuit K)
  证明: by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK

Depends on / 依赖: hC.inter_isCocircuit_ne_singleton, inter_isCocircuit_ne_singleton, nontrivial_iff_ne_singleton
-/
lemma IsCircuit.isCocircuit_inter_nontrivial (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
    (hCK : (C inter K).Nonempty) : (C inter K).Nontrivial := by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK

/--
lemma `IsCircuit.isCocircuit_disjoint_or_nontrivial_inter` / 引理 `IsCircuit.isCocircuit_disjoint_or_nontrivial_inter`

English:
lemma IsCircuit.isCocircuit_disjoint_or_nontrivial_inter
  statement: (hC : M.IsCircuit C)
  proof: by
  rw [or_iff_not_imp_left]; rw [disjoint_iff_inter_eq_empty]; rw [← ne_eq]; rw [← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK

中文:
引理 是Circuit.isCocircuit_disjoint_or_nontrivial_inter
  结论: (hC : M.是Circuit C)
  证明: by
  rw [or_iff_not_imp_left]; rw [disjoint_iff_inter_eq_empty]; rw [← ne_eq]; rw [← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK

Depends on / 依赖: disjoint_iff_inter_eq_empty, hC.isCocircuit_inter_nontrivial, isCocircuit_inter_nontrivial, ne_eq, nonempty_iff_ne_empty, or_iff_not_imp_left
-/
lemma IsCircuit.isCocircuit_disjoint_or_nontrivial_inter (hC : M.IsCircuit C)
    (hK : M.IsCocircuit K) : Disjoint C K ∨ (C inter K).Nontrivial := by
  rw [or_iff_not_imp_left]; rw [disjoint_iff_inter_eq_empty]; rw [← ne_eq]; rw [← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK

/--
lemma `dual_rankPos_iff_exists_isCircuit` / 引理 `dual_rankPos_iff_exists_isCircuit`

English:
lemma dual_rankPos_iff_exists_isCircuit
  statement: M✶.RankPos ↔ exists C, M.IsCircuit C
  proof: by
  rw [rankPos_iff]; rw [dual_isBase_iff]; rw [sdiff_empty]; rw [not_iff_comm]; rw [not_exists]; rw [← ground_indep_iff_isBase]; rw [indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ => h C, fun h C hC => h C hC.subset_ground hC⟩

中文:
引理 dual_rankPos_iff_存在_isCircuit
  结论: M✶.RankPos ↔ 存在 C, M.是Circuit C
  证明: by
  rw [rankPos_iff]; rw [dual_isBase_iff]; rw [sdiff_empty]; rw [not_iff_comm]; rw [not_exists]; rw [← ground_indep_iff_isBase]; rw [indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ => h C, fun h C hC => h C hC.subset_ground hC⟩

Depends on / 依赖: dual_isBase_iff, ground_indep_iff_isBase, hC.subset_ground, indep_iff_forall_subset_not_isCircuit, not_exists, not_iff_comm, rankPos_iff, sdiff_empty, subset_ground
-/
lemma dual_rankPos_iff_exists_isCircuit : M✶.RankPos ↔ exists C, M.IsCircuit C := by
  rw [rankPos_iff]; rw [dual_isBase_iff]; rw [sdiff_empty]; rw [not_iff_comm]; rw [not_exists]; rw [← ground_indep_iff_isBase]; rw [indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ => h C, fun h C hC => h C hC.subset_ground hC⟩

/--
lemma `IsCircuit.dual_rankPos` / 引理 `IsCircuit.dual_rankPos`

English:
lemma IsCircuit.dual_rankPos
  given: (hC : M.IsCircuit C)
  statement: M✶.RankPos
  proof: dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩

中文:
引理 是Circuit.dual_rankPos
  条件: (hC : M.是Circuit C)
  结论: M✶.RankPos
  证明: dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩

Depends on / 依赖: dual_rankPos_iff_exists_isCircuit, dual_rankPos_iff_exists_isCircuit.mpr
-/
lemma IsCircuit.dual_rankPos (hC : M.IsCircuit C) : M✶.RankPos :=
  dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩

/--
lemma `exists_isCircuit` / 引理 `exists_isCircuit`

English:
lemma exists_isCircuit
  given: [RankPos M✶]
  statement: exists C, M.IsCircuit C
  proof: dual_rankPos_iff_exists_isCircuit.1 (by assumption)

中文:
引理 存在_isCircuit
  条件: [RankPos M✶]
  结论: 存在 C, M.是Circuit C
  证明: dual_rankPos_iff_exists_isCircuit.1 (by assumption)

Depends on / 依赖: dual_rankPos_iff_exists_isCircuit
-/
lemma exists_isCircuit [RankPos M✶] : exists C, M.IsCircuit C :=
  dual_rankPos_iff_exists_isCircuit.1 (by assumption)

/--
lemma `rankPos_iff_exists_isCocircuit` / 引理 `rankPos_iff_exists_isCocircuit`

English:
lemma rankPos_iff_exists_isCocircuit
  statement: M.RankPos ↔ exists K, M.IsCocircuit K
  proof: by
  rw [← dual_dual M]; rw [dual_rankPos_iff_exists_isCircuit]; rw [dual_dual M]

中文:
引理 rankPos_iff_存在_isCocircuit
  结论: M.RankPos ↔ 存在 K, M.IsCocircuit K
  证明: by
  rw [← dual_dual M]; rw [dual_rankPos_iff_exists_isCircuit]; rw [dual_dual M]

Depends on / 依赖: dual_dual, dual_rankPos_iff_exists_isCircuit
-/
lemma rankPos_iff_exists_isCocircuit : M.RankPos ↔ exists K, M.IsCocircuit K := by
  rw [← dual_dual M]; rw [dual_rankPos_iff_exists_isCircuit]; rw [dual_dual M]

/--
Definition of `fundCocircuit` / `fundCocircuit` 的定义

English:
definition fundCocircuit
  signature: (M : Matroid α) (e : α) (B : Set α)
  body: M✶.fundCircuit e (M✶.E \ B)

中文:
定义 fundCocircuit
  签名: (M : 拟阵 α) (e : α) (B : 集合 α)
  定义体: M✶.fundCircuit e (M✶.E \ B)

Depends on / 依赖: fundCircuit
-/
def fundCocircuit (M : Matroid α) (e : α) (B : Set α) := M✶.fundCircuit e (M✶.E \ B)

/--
lemma `fundCocircuit_isCocircuit` / 引理 `fundCocircuit_isCocircuit`

English:
lemma fundCocircuit_isCocircuit
  given: (he : e in B) (hB : M.IsBase B)
  proof: by
  apply hB.compl_isBase_dual.indep.fundCircuit_isCircuit _ (by simp [he])
  rw [hB.compl_isBase_dual.closure_eq]; rw [dual_ground]
  exact hB.subset_ground he

中文:
引理 fundCocircuit_isCocircuit
  条件: (he : e in B) (hB : M.IsBase B)
  证明: by
  apply hB.compl_isBase_dual.indep.fundCircuit_isCircuit _ (by simp [he])
  rw [hB.compl_isBase_dual.closure_eq]; rw [dual_ground]
  exact hB.subset_ground he

Depends on / 依赖: closure_eq, compl_isBase_dual, dual_ground, fundCircuit_isCircuit, hB.compl_isBase_dual.closure_eq, hB.compl_isBase_dual.indep.fundCircuit_isCircuit, hB.subset_ground, subset_ground
-/
lemma fundCocircuit_isCocircuit (he : e in B) (hB : M.IsBase B) :
M.IsCocircuit M.fundCocircuit e B := by
  apply hB.compl_isBase_dual.indep.fundCircuit_isCircuit _ (by simp [he])
  rw [hB.compl_isBase_dual.closure_eq]; rw [dual_ground]
  exact hB.subset_ground he

/--
lemma `mem_fundCocircuit` / 引理 `mem_fundCocircuit`

English:
lemma mem_fundCocircuit
  given: (M : Matroid α) (e : α) (B : Set α)
  statement: e in M.fundCocircuit e B
  proof: mem_insert _ _

中文:
引理 mem_fundCocircuit
  条件: (M : 拟阵 α) (e : α) (B : 集合 α)
  结论: e in M.fundCocircuit e B
  证明: mem_insert _ _

Depends on / 依赖: mem_insert
-/
lemma mem_fundCocircuit (M : Matroid α) (e : α) (B : Set α) : e in M.fundCocircuit e B :=
  mem_insert _ _

/--
lemma `fundCocircuit_subset_insert_compl` / 引理 `fundCocircuit_subset_insert_compl`

English:
lemma fundCocircuit_subset_insert_compl
  given: (M : Matroid α) (e : α) (B : Set α)
  proof: fundCircuit_subset_insert ..

中文:
引理 fundCocircuit_subset_insert_compl
  条件: (M : 拟阵 α) (e : α) (B : 集合 α)
  证明: fundCircuit_subset_insert ..

Depends on / 依赖: fundCircuit_subset_insert
-/
lemma fundCocircuit_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) :
    M.fundCocircuit e B subseteq insert e (M.E \ B) :=
  fundCircuit_subset_insert ..

/--
lemma `fundCocircuit_inter_eq` / 引理 `fundCocircuit_inter_eq`

English:
lemma fundCocircuit_inter_eq
  given: (M : Matroid α) {B : Set α} (he : e in B)
  proof: by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocircuit _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocircuit_subset_insert_compl _ _)).trans ?_
  simp +contextual

中文:
引理 fundCocircuit_inter_eq
  条件: (M : 拟阵 α) {B : 集合 α} (he : e in B)
  证明: by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocircuit _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocircuit_subset_insert_compl _ _)).trans ?_
  simp +contextual

Depends on / 依赖: M.fundCocircuit_subset_insert_compl, M.mem_fundCocircuit, contextual, fundCocircuit_subset_insert_compl, inter_subset_inter_left, mem_fundCocircuit, singleton_subset_iff, subset_antisymm
-/
lemma fundCocircuit_inter_eq (M : Matroid α) {B : Set α} (he : e in B) :
    (M.fundCocircuit e B) inter B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocircuit _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocircuit_subset_insert_compl _ _)).trans ?_
  simp +contextual

/--
lemma `fundCocircuit_eq_of_notMem_ground` / 引理 `fundCocircuit_eq_of_notMem_ground`

English:
lemma fundCocircuit_eq_of_notMem_ground
  given: (X : Set α) (he : e ∉ M.E)
  proof: by
  rwa [fundCocircuit, fundCircuit_eq_of_notMem_ground]

中文:
引理 fundCocircuit_eq_of_notMem_ground
  条件: (X : 集合 α) (he : e ∉ M.E)
  证明: by
  rwa [fundCocircuit, fundCircuit_eq_of_notMem_ground]

Depends on / 依赖: fundCircuit_eq_of_notMem_ground, fundCocircuit
-/
lemma fundCocircuit_eq_of_notMem_ground (X : Set α) (he : e ∉ M.E) :
    M.fundCocircuit e X = {e} := by
  rwa [fundCocircuit, fundCircuit_eq_of_notMem_ground]

/--
lemma `fundCocircuit_eq_of_notMem` / 引理 `fundCocircuit_eq_of_notMem`

English:
lemma fundCocircuit_eq_of_notMem
  given: (M : Matroid α) (heX : e ∉ X)
  statement: M.fundCocircuit e X = {e}
  proof: by
  by_cases he : e in M.E
  · rw [fundCocircuit, fundCircuit_eq_of_mem]
    exact ⟨he, heX⟩
  rw [fundCocircuit_eq_of_notMem_ground _ he]

中文:
引理 fundCocircuit_eq_of_notMem
  条件: (M : 拟阵 α) (heX : e ∉ X)
  结论: M.fundCocircuit e X = {e}
  证明: by
  by_cases he : e in M.E
  · rw [fundCocircuit, fundCircuit_eq_of_mem]
    exact ⟨he, heX⟩
  rw [fundCocircuit_eq_of_notMem_ground _ he]

Depends on / 依赖: fundCircuit_eq_of_mem, fundCocircuit, fundCocircuit_eq_of_notMem_ground
-/
lemma fundCocircuit_eq_of_notMem (M : Matroid α) (heX : e ∉ X) : M.fundCocircuit e X = {e} := by
  by_cases he : e in M.E
  · rw [fundCocircuit, fundCircuit_eq_of_mem]
    exact ⟨he, heX⟩
  rw [fundCocircuit_eq_of_notMem_ground _ he]

/--
lemma `Indep.exists_isCocircuit_inter_eq_mem` / 引理 `Indep.exists_isCocircuit_inter_eq_mem`

English:
lemma Indep.exists_isCocircuit_inter_eq_mem
  given: (hI : M.Indep I) (heI : e in I)
  proof: by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_isCocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff]; rw [subset_inter_iff]; rw [singleton_subset_iff]; rw [and_iff_right
    (mem_fundCocircuit _ _ _)]; rw [singleton_subset_iff]; rw [and_iff_left

中文:
引理 Indep.存在_isCocircuit_inter_eq_mem
  条件: (hI : M.Indep I) (heI : e in I)
  证明: by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_isCocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff]; rw [subset_inter_iff]; rw [singleton_subset_iff]; rw [and_iff_right
    (mem_fundCocircuit _ _ _)]; rw [singleton_subset_iff]; rw [and_iff_left

Depends on / 依赖: M.fundCocircuit, M.fundCocircuit_inter_eq, and_iff_left, and_iff_right, exists_isBase_superset, fundCocircuit, fundCocircuit_inter_eq, fundCocircuit_isCocircuit, hI.exists_isBase_superset, inter_subset_inter_right, mem_fundCocircuit, singleton_subset_iff, subset_antisymm_iff, subset_inter_iff
-/
lemma Indep.exists_isCocircuit_inter_eq_mem (hI : M.Indep I) (heI : e in I) :
    exists K, M.IsCocircuit K ∧ K inter I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_isCocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff]; rw [subset_inter_iff]; rw [singleton_subset_iff]; rw [and_iff_right
    (mem_fundCocircuit _ _ _)]; rw [singleton_subset_iff]; rw [and_iff_left heI]; rw [← M.fundCocircuit_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB

/--
lemma `IsBase.mem_fundCocircuit_iff_mem_fundCircuit` / 引理 `IsBase.mem_fundCocircuit_iff_mem_fundCircuit`

English:
lemma IsBase.mem_fundCocircuit_iff_mem_fundCircuit
  given: {e f : α} (hB : M.IsBase B)
  proof: by
  -- By symmetry and duality, it suffices to show the implication in one direction.
  suffices aux : forall {N : Matroid α} {B' : Set α} (hB' : N.IsBase B') {e f},
      e in N.fundCocircuit f B' -> f in N.fundCircuit e B' from
⟨fun h => aux hB h, fun h => aux hB.compl_isBase_dual by
      simpa 

中文:
引理 IsBase.mem_fundCocircuit_iff_mem_fundCircuit
  条件: {e f : α} (hB : M.IsBase B)
  证明: by
  -- By symmetry and duality, it suffices to show the implication in one direction.
  suffices aux : forall {N : Matroid α} {B' : Set α} (hB' : N.IsBase B') {e f},
      e in N.fundCocircuit f B' -> f in N.fundCircuit e B' from
⟨fun h => aux hB h, fun h => aux hB.compl_isBase_dual by
      simpa 
-/
lemma IsBase.mem_fundCocircuit_iff_mem_fundCircuit {e f : α} (hB : M.IsBase B) :
    e in M.fundCocircuit f B ↔ f in M.fundCircuit e B := by
  -- By symmetry and duality, it suffices to show the implication in one direction.
  suffices aux : forall {N : Matroid α} {B' : Set α} (hB' : N.IsBase B') {e f},
      e in N.fundCocircuit f B' -> f in N.fundCircuit e B' from
⟨fun h => aux hB h, fun h => aux hB.compl_isBase_dual by
      simpa [fundCocircuit, inter_eq_self_of_subset_right hB.subset_ground]⟩
  clear! B M e f
  intro M B hB e f he
  -- discharge the various degenerate cases.
  obtain rfl | hne := eq_or_ne e f
  · simp [mem_fundCircuit]
  have hB' : M✶.IsBase (M✶.E \ B) := hB.compl_isBase_dual
obtain hfE | hfE := em' f in M.E
  · rw [fundCocircuit, fundCircuit_eq_of_notMem_ground (by simpa)] at he
    contradiction
obtain hfB | hfB := em' f in B
  · rw [fundCocircuit, fundCircuit_eq_of_mem (by simp [hfE, hfB])] at he
    contradiction
  obtain ⟨heE, heB⟩ : e in M.E \ B := by
    simpa [hne] using (M.fundCocircuit_subset_insert_compl f B) he
  -- Use basis exchange to argue the equivalence.
  rw [fundCocircuit]; rw [hB'.indep.mem_fundCircuit_iff (by rwa [hB'.closure_eq]) (by simp [hfB])] at he
  rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) heB]
  have hB' : M.IsBase (M.E \ (insert f (M✶.E \ B) \ {e})) :=
    (hB'.exchange_isBase_of_indep' ⟨heE, heB⟩ (by simp [hfE, hfB]) he).compl_isBase_of_dual
  refine hB'.indep.subset ?_
  simp only [dual_ground, sdiff_singleton_subset_iff]
  rw [sdiff_sdiff_right]; rw [inter_eq_self_of_subset_right (by simpa)]; rw [union_singleton]; rw [insert_comm]; rw [← union_singleton (s := M.E \ B)]; rw [← sdiff_sdiff]; rw [sdiff_sdiff_cancel_left hB.subset_ground]
  simp [hfB]

end IsCocircuit

end Matroid
