/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Tactic.TFAE

/-!
# Matroid loops and coloops

## Loops
A 'loop' of a matroid `M` is an element `e` satisfying one of the following equivalent conditions:
* `e ∈ M.closure ∅`;
* `{e}` is dependent in `M`;
* `{e}` is a circuit of `M`;
* no base of `M` contains `e`.

In many mathematical contexts, loops can be thought of as 'trivial' or 'zero' elements;
For linearly representable matroids, they correspond to the zero vector,
and for graphic matroids, they correspond to edges incident with just one vertex (aka 'loops').
As trivial as they are, loops can be created from matroids with no loops by taking minors or duals,
so in many contexts it is unreasonable to simply forbid loops from appearing.
For `M : Matroid α`, this file defines a set `Matroid.loops M : Set α`,
as well as predicates `Matroid.IsLoop M : α → Prop` and `Matroid.IsNonloop M : α → Prop`,
and provides API for interacting with them.

## Coloops
The dual notion of a loop is a 'coloop'. Geometrically, these can be thought of elements that are
skew to the remainder of the matroid. Coloops in graphic matroids are 'bridge' edges of the graph,
and coloops in linearly representable matroids are vectors not spanned by the other vectors
in the matroid.
Coloops also have many equivalent definitions in abstract matroid language;
a coloop is an element of `M.E` if any of the following equivalent conditions holds :
* `e` is a loop of `M✶`;
* `{e}` is a cocircuit of `M`;
* `e` is in no circuit of `M`;
* `e` is in every base of `M`;
* for all `X ⊆ M.E`, `e ∈ X ↔ e ∈ M.closure X`,
* `M.E \ {e}` is nonspanning.

## Main Declarations
For `M` : Matroid `α`:
* `M.loops` is the set `M.closure ∅`.
* `M.IsLoop e` means that `e : α` is a loop of `M`, defined as the statement `e ∈ M.loops`.
* `M.isLoop_tfae` gives a number of properties that are equivalent to `IsLoop`.
* `M.IsNonloop e` means that `e ∈ M.E`, but `e` is not a loop of `M`.
* `M.IsColoop e ` means that `e` is a loop of `M✶`.
* `M.coloops` is the set of coloops of `M✶`.
* `M.isColoop_tfae` gives a number of properties that are equivalent to `IsColoop`.
* `M.Loopless` is a typeclass meaning `M` has no loops.
* `M.removeLoops` is the matroid obtained from `M` by restricting to its set of nonloop elements.
-/

@[expose] public section

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set

namespace Matroid

/--
Definition of `loops` / `loops` 的定义

English:
definition loops
  signature: (M : Matroid α)
  body: M.closure ∅

@[aesop unsafe 20% (rule_sets := [Matroid])]

中文:
定义 loops
  签名: (M : 拟阵 α)
  定义体: M.closure ∅

@[aesop unsafe 20% (rule_sets := [Matroid])]

Depends on / 依赖: M.closure, closure
-/
def loops (M : Matroid α) := M.closure ∅

@[aesop unsafe 20% (rule_sets := [Matroid])]
/--
lemma `loops_subset_ground` / 引理 `loops_subset_ground`

English:
lemma loops_subset_ground
  given: (M : Matroid α)
  statement: M.loops subseteq M.E
  proof: M.closure_subset_ground ∅

中文:
引理 loops_subset_ground
  条件: (M : 拟阵 α)
  结论: M.loops subseteq M.E
  证明: M.closure_subset_ground ∅

Depends on / 依赖: M.closure_subset_ground, closure_subset_ground
-/
lemma loops_subset_ground (M : Matroid α) : M.loops subseteq M.E :=
  M.closure_subset_ground ∅

/--
Definition of `IsLoop` / `IsLoop` 的定义

English:
definition IsLoop
  signature: (M : Matroid α) (e : α)
  body: e in M.loops

中文:
定义 IsLoop
  签名: (M : 拟阵 α) (e : α)
  定义体: e in M.loops

Depends on / 依赖: M.loops
-/
def IsLoop (M : Matroid α) (e : α) : Prop := e in M.loops

/--
lemma `isLoop_iff` / 引理 `isLoop_iff`

English:
lemma isLoop_iff
  statement: M.IsLoop e ↔ e in M.loops
  proof: Iff.rfl

中文:
引理 isLoop_iff
  结论: M.IsLoop e ↔ e in M.loops
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isLoop_iff : M.IsLoop e ↔ e in M.loops := Iff.rfl

/--
lemma `closure_empty` / 引理 `closure_empty`

English:
lemma closure_empty
  given: (M : Matroid α)
  statement: M.closure ∅ = M.loops
  proof: rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]

中文:
引理 closure_empty
  条件: (M : 拟阵 α)
  结论: M.closure ∅ = M.loops
  证明: rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
-/
lemma closure_empty (M : Matroid α) : M.closure ∅ = M.loops := rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
/--
lemma `IsLoop.mem_ground` / 引理 `IsLoop.mem_ground`

English:
lemma IsLoop.mem_ground
  given: (he : M.IsLoop e)
  statement: e in M.E
  proof: closure_subset_ground M ∅ he

中文:
引理 IsLoop.mem_ground
  条件: (he : M.IsLoop e)
  结论: e in M.E
  证明: closure_subset_ground M ∅ he

Depends on / 依赖: closure_subset_ground
-/
lemma IsLoop.mem_ground (he : M.IsLoop e) : e in M.E :=
  closure_subset_ground M ∅ he

/--
lemma `isLoop_tfae` / 引理 `isLoop_tfae`

English:
lemma isLoop_tfae
  given: (M : Matroid α) (e : α)
  statement: List.TFAE [
  proof: by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e),
    isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]
  tfae_have 2 ↔ 4 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e)]
  tfae_have 4 ↔ 5 := by
    simp only [dep_iff, singleton_subset_iff, mem_sdiff, forall_and]
    refine ⟨fun h => ⟨fun _ _ => h.2, fun B hB heB => h.1 (hB.indep.subset (by simpa))⟩,
      fun h => ⟨fun hi => ?_, h.1 _ M.exists_isBase.choose_spec⟩⟩
    obtain ⟨B, hB, heB⟩ := hi.exists_isBase_superset
    exact h.2 _ hB (by simpa using heB)
  tfae_finish

@[simp]

中文:
引理 isLoop_tfae
  条件: (M : 拟阵 α) (e : α)
  结论: 列表.TFAE [
  证明: by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e),
    isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]
  tfae_have 2 ↔ 4 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e)]
  tfae_have 4 ↔ 5 := by
    simp only [dep_iff, singleton_subset_iff, mem_sdiff, forall_and]
    refine ⟨fun h => ⟨fun _ _ => h.2, fun B hB heB => h.1 (hB.indep.subset (by simpa))⟩,
      fun h => ⟨fun hi => ?_, h.1 _ M.exists_isBase.choose_spec⟩⟩
    obtain ⟨B, hB, heB⟩ := hi.exists_isBase_superset
    exact h.2 _ hB (by simpa using heB)
  tfae_finish

@[simp]

Depends on / 依赖: Iff.rfl, M.empty_indep.mem_closure_iff_of_notMem, M.exists_isBase.choose_spec, choose_spec, dep_iff, empty_indep, exists_isBase, forall_and, hB.indep.subset, isCircuit_def, mem_closure_iff_of_notMem, mem_sdiff, minimal_iff_forall_ssubset, notMem_empty, singleton_subset_iff, ssubset_singleton_iff, subset, tfae_have
-/
lemma isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [
    M.IsLoop e,
    e in M.closure ∅,
    M.IsCircuit {e},
    M.Dep {e},
    forall ⦃B⦄, M.IsBase B -> e in M.E \ B] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e),
    isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]
  tfae_have 2 ↔ 4 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e)]
  tfae_have 4 ↔ 5 := by
    simp only [dep_iff, singleton_subset_iff, mem_sdiff, forall_and]
    refine ⟨fun h => ⟨fun _ _ => h.2, fun B hB heB => h.1 (hB.indep.subset (by simpa))⟩,
      fun h => ⟨fun hi => ?_, h.1 _ M.exists_isBase.choose_spec⟩⟩
    obtain ⟨B, hB, heB⟩ := hi.exists_isBase_superset
    exact h.2 _ hB (by simpa using heB)
  tfae_finish

@[simp]
/--
lemma `singleton_dep` / 引理 `singleton_dep`

English:
lemma singleton_dep
  statement: M.Dep {e} ↔ M.IsLoop e
  proof: (M.isLoop_tfae e).out 3 0

alias ⟨_, IsLoop.dep⟩ := singleton_dep

中文:
引理 singleton_dep
  结论: M.Dep {e} ↔ M.IsLoop e
  证明: (M.isLoop_tfae e).out 3 0

alias ⟨_, IsLoop.dep⟩ := singleton_dep

Depends on / 依赖: M.isLoop_tfae, isLoop_tfae
-/
lemma singleton_dep : M.Dep {e} ↔ M.IsLoop e :=
  (M.isLoop_tfae e).out 3 0

alias ⟨_, IsLoop.dep⟩ := singleton_dep

/--
lemma `singleton_not_indep` / 引理 `singleton_not_indep`

English:
lemma singleton_not_indep
  given: (he : e in M.E := by aesop_mat)
  statement: ¬ M.Indep {e} ↔ M.IsLoop e
  proof: by
  rw [← singleton_dep]; rw [← not_indep_iff]

@[simp]

中文:
引理 singleton_not_indep
  条件: (he : e in M.E := by aesop_mat)
  结论: ¬ M.Indep {e} ↔ M.IsLoop e
  证明: by
  rw [← singleton_dep]; rw [← not_indep_iff]

@[simp]

Depends on / 依赖: IsLoop, M.Indep, M.IsLoop, aesop_mat, not_indep_iff, singleton_dep
-/
lemma singleton_not_indep (he : e in M.E := by aesop_mat) : ¬ M.Indep {e} ↔ M.IsLoop e := by
  rw [← singleton_dep]; rw [← not_indep_iff]

@[simp]
/--
lemma `singleton_isCircuit` / 引理 `singleton_isCircuit`

English:
lemma singleton_isCircuit
  statement: M.IsCircuit {e} ↔ M.IsLoop e
  proof: (M.isLoop_tfae e).out 2 0

alias ⟨_, IsLoop.isCircuit⟩ := singleton_isCircuit

中文:
引理 singleton_isCircuit
  结论: M.是Circuit {e} ↔ M.IsLoop e
  证明: (M.isLoop_tfae e).out 2 0

alias ⟨_, IsLoop.isCircuit⟩ := singleton_isCircuit

Depends on / 依赖: M.isLoop_tfae, isLoop_tfae
-/
lemma singleton_isCircuit : M.IsCircuit {e} ↔ M.IsLoop e :=
  (M.isLoop_tfae e).out 2 0

alias ⟨_, IsLoop.isCircuit⟩ := singleton_isCircuit

/--
lemma `isLoop_iff_forall_mem_compl_isBase` / 引理 `isLoop_iff_forall_mem_compl_isBase`

English:
lemma isLoop_iff_forall_mem_compl_isBase
  statement: M.IsLoop e ↔ forall B, M.IsBase B -> e in M.E \ B
  proof: (M.isLoop_tfae e).out 0 4

中文:
引理 isLoop_iff_对任意_mem_compl_isBase
  结论: M.IsLoop e ↔ 对任意 B, M.IsBase B -> e in M.E \ B
  证明: (M.isLoop_tfae e).out 0 4

Depends on / 依赖: M.isLoop_tfae, isLoop_tfae
-/
lemma isLoop_iff_forall_mem_compl_isBase : M.IsLoop e ↔ forall B, M.IsBase B -> e in M.E \ B :=
  (M.isLoop_tfae e).out 0 4

/--
lemma `isLoop_iff_forall_notMem_isBase` / 引理 `isLoop_iff_forall_notMem_isBase`

English:
lemma isLoop_iff_forall_notMem_isBase
  given: (he : e in M.E := by aesop_mat)
  proof: by
  simp_rw [isLoop_iff_forall_mem_compl_isBase, mem_sdiff, and_iff_right he]

中文:
引理 isLoop_iff_对任意_notMem_isBase
  条件: (he : e in M.E := by aesop_mat)
  证明: by
  simp_rw [isLoop_iff_forall_mem_compl_isBase, mem_sdiff, and_iff_right he]

Depends on / 依赖: IsBase, IsLoop, M.IsBase, M.IsLoop, aesop_mat, and_iff_right, isLoop_iff_forall_mem_compl_isBase, mem_sdiff, simp_rw
-/
lemma isLoop_iff_forall_notMem_isBase (he : e in M.E := by aesop_mat) :
    M.IsLoop e ↔ forall B, M.IsBase B -> e ∉ B := by
  simp_rw [isLoop_iff_forall_mem_compl_isBase, mem_sdiff, and_iff_right he]

/--
lemma `IsLoop.mem_closure` / 引理 `IsLoop.mem_closure`

English:
lemma IsLoop.mem_closure
  given: (he : M.IsLoop e) (X : Set α)
  statement: e in M.closure X
  proof: M.closure_mono (empty_subset _) he

中文:
引理 IsLoop.mem_closure
  条件: (he : M.IsLoop e) (X : 集合 α)
  结论: e in M.closure X
  证明: M.closure_mono (empty_subset _) he

Depends on / 依赖: M.closure_mono, closure_mono, empty_subset
-/
lemma IsLoop.mem_closure (he : M.IsLoop e) (X : Set α) : e in M.closure X :=
  M.closure_mono (empty_subset _) he

/--
lemma `IsLoop.mem_of_isFlat` / 引理 `IsLoop.mem_of_isFlat`

English:
lemma IsLoop.mem_of_isFlat
  given: (he : M.IsLoop e) {F : Set α} (hF : M.IsFlat F)
  statement: e in F
  proof: hF.closure ▸ he.mem_closure F

中文:
引理 IsLoop.mem_of_isFlat
  条件: (he : M.IsLoop e) {F : 集合 α} (hF : M.是平坦 F)
  结论: e in F
  证明: hF.closure ▸ he.mem_closure F

Depends on / 依赖: closure, hF.closure, he.mem_closure, mem_closure
-/
lemma IsLoop.mem_of_isFlat (he : M.IsLoop e) {F : Set α} (hF : M.IsFlat F) : e in F :=
  hF.closure ▸ he.mem_closure F

/--
lemma `IsFlat.loops_subset` / 引理 `IsFlat.loops_subset`

English:
lemma IsFlat.loops_subset
  given: (hF : M.IsFlat F)
  statement: M.loops subseteq F
  proof: fun _ he => IsLoop.mem_of_isFlat he hF

中文:
引理 是平坦.loops_subset
  条件: (hF : M.是平坦 F)
  结论: M.loops subseteq F
  证明: fun _ he => IsLoop.mem_of_isFlat he hF

Depends on / 依赖: IsLoop, IsLoop.mem_of_isFlat, mem_of_isFlat
-/
lemma IsFlat.loops_subset (hF : M.IsFlat F) : M.loops subseteq F :=
  fun _ he => IsLoop.mem_of_isFlat he hF

/--
lemma `IsLoop.dep_of_mem` / 引理 `IsLoop.dep_of_mem`

English:
lemma IsLoop.dep_of_mem
  given: (he : M.IsLoop e) (h : e in X) (hXE : X subseteq M.E := by aesop_mat)
  statement: M.Dep X
  proof: he.dep.superset (singleton_subset_iff.mpr h) hXE

中文:
引理 IsLoop.dep_of_mem
  条件: (he : M.IsLoop e) (h : e in X) (hXE : X subseteq M.E := by aesop_mat)
  结论: M.Dep X
  证明: he.dep.superset (singleton_subset_iff.mpr h) hXE

Depends on / 依赖: M.Dep, aesop_mat, he.dep.superset, singleton_subset_iff, singleton_subset_iff.mpr, superset
-/
lemma IsLoop.dep_of_mem (he : M.IsLoop e) (h : e in X) (hXE : X subseteq M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE

/--
lemma `IsLoop.not_indep_of_mem` / 引理 `IsLoop.not_indep_of_mem`

English:
lemma IsLoop.not_indep_of_mem
  given: (he : M.IsLoop e) (h : e in X)
  statement: ¬M.Indep X
  proof: fun hX => he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

中文:
引理 IsLoop.not_indep_of_mem
  条件: (he : M.IsLoop e) (h : e in X)
  结论: ¬M.Indep X
  证明: fun hX => he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

Depends on / 依赖: hX.subset, he.dep.not_indep, not_indep, singleton_subset_iff, singleton_subset_iff.mpr, subset
-/
lemma IsLoop.not_indep_of_mem (he : M.IsLoop e) (h : e in X) : ¬M.Indep X :=
  fun hX => he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

/--
lemma `IsLoop.notMem_of_indep` / 引理 `IsLoop.notMem_of_indep`

English:
lemma IsLoop.notMem_of_indep
  given: (he : M.IsLoop e) (hI : M.Indep I)
  statement: e ∉ I
  proof: fun h => he.not_indep_of_mem h hI

中文:
引理 IsLoop.notMem_of_indep
  条件: (he : M.IsLoop e) (hI : M.Indep I)
  结论: e ∉ I
  证明: fun h => he.not_indep_of_mem h hI

Depends on / 依赖: he.not_indep_of_mem, not_indep_of_mem
-/
lemma IsLoop.notMem_of_indep (he : M.IsLoop e) (hI : M.Indep I) : e ∉ I :=
  fun h => he.not_indep_of_mem h hI

/--
lemma `IsLoop.eq_of_isCircuit_mem` / 引理 `IsLoop.eq_of_isCircuit_mem`

English:
lemma IsLoop.eq_of_isCircuit_mem
  given: (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e in C)
  statement: C = {e}
  proof: by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

中文:
引理 IsLoop.eq_of_isCircuit_mem
  条件: (he : M.IsLoop e) (hC : M.是Circuit C) (h : e in C)
  结论: C = {e}
  证明: by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

Depends on / 依赖: eq_of_subset_isCircuit, he.isCircuit.eq_of_subset_isCircuit, isCircuit, singleton_subset_iff, singleton_subset_iff.mpr
-/
lemma IsLoop.eq_of_isCircuit_mem (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e in C) : C = {e} := by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

/--
lemma `Indep.disjoint_loops` / 引理 `Indep.disjoint_loops`

English:
lemma Indep.disjoint_loops
  given: (hI : M.Indep I)
  statement: Disjoint I M.loops
  proof: by_contra fun h =>
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.notMem_of_indep he hI heI

中文:
引理 Indep.disjoint_loops
  条件: (hI : M.Indep I)
  结论: Disjoint I M.loops
  证明: by_contra fun h =>
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.notMem_of_indep he hI heI

Depends on / 依赖: IsLoop, IsLoop.notMem_of_indep, notMem_of_indep, not_disjoint_iff, not_disjoint_iff.mp
-/
lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I M.loops :=
  by_contra fun h =>
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.notMem_of_indep he hI heI

/--
lemma `Indep.eq_empty_of_subset_loops` / 引理 `Indep.eq_empty_of_subset_loops`

English:
lemma Indep.eq_empty_of_subset_loops
  given: (hI : M.Indep I) (h : I subseteq M.loops)
  statement: I = ∅
  proof: eq_empty_iff_forall_notMem.mpr fun _ he => IsLoop.notMem_of_indep (h he) hI he

@[simp]

中文:
引理 Indep.eq_empty_of_subset_loops
  条件: (hI : M.Indep I) (h : I subseteq M.loops)
  结论: I = ∅
  证明: eq_empty_iff_forall_notMem.mpr fun _ he => IsLoop.notMem_of_indep (h he) hI he

@[simp]

Depends on / 依赖: IsLoop, IsLoop.notMem_of_indep, eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem.mpr, notMem_of_indep
-/
lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I subseteq M.loops) : I = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ he => IsLoop.notMem_of_indep (h he) hI he

@[simp]
/--
lemma `isBasis_loops_iff` / 引理 `isBasis_loops_iff`

English:
lemma isBasis_loops_iff
  statement: M.IsBasis I M.loops ↔ I = ∅
  proof: ⟨fun h => h.indep.eq_empty_of_subset_loops h.subset,
    by simp +contextual [closure_empty]⟩

中文:
引理 isBasis_loops_iff
  结论: M.是基 I M.loops ↔ I = ∅
  证明: ⟨fun h => h.indep.eq_empty_of_subset_loops h.subset,
    by simp +contextual [closure_empty]⟩

Depends on / 依赖: closure_empty, contextual, eq_empty_of_subset_loops, h.indep.eq_empty_of_subset_loops, h.subset, subset
-/
lemma isBasis_loops_iff : M.IsBasis I M.loops ↔ I = ∅ :=
  ⟨fun h => h.indep.eq_empty_of_subset_loops h.subset,
    by simp +contextual [closure_empty]⟩

/--
lemma `closure_eq_loops_of_subset` / 引理 `closure_eq_loops_of_subset`

English:
lemma closure_eq_loops_of_subset
  given: (h : X subseteq M.loops)
  statement: M.closure X = M.loops
  proof: (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

中文:
引理 closure_eq_loops_of_subset
  条件: (h : X subseteq M.loops)
  结论: M.closure X = M.loops
  证明: (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

Depends on / 依赖: M.closure_mono, antisymm, closure_mono, closure_subset_closure_of_subset_closure, empty_subset
-/
lemma closure_eq_loops_of_subset (h : X subseteq M.loops) : M.closure X = M.loops :=
  (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

/--
lemma `isBasis_iff_empty_of_subset_loops` / 引理 `isBasis_iff_empty_of_subset_loops`

English:
lemma isBasis_iff_empty_of_subset_loops
  given: (hX : X subseteq M.loops)
  statement: M.IsBasis I X ↔ I = ∅
  proof: by
  refine ⟨fun h => ?_, by rintro rfl; simpa⟩
  have := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using this

中文:
引理 isBasis_iff_empty_of_subset_loops
  条件: (hX : X subseteq M.loops)
  结论: M.是基 I X ↔ I = ∅
  证明: by
  refine ⟨fun h => ?_, by rintro rfl; simpa⟩
  have := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using this

Depends on / 依赖: closure_eq_loops_of_subset, h.isBasis_closure_right, isBasis_closure_right
-/
lemma isBasis_iff_empty_of_subset_loops (hX : X subseteq M.loops) : M.IsBasis I X ↔ I = ∅ := by
  refine ⟨fun h => ?_, by rintro rfl; simpa⟩
  have := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using this

/--
lemma `IsLoop.closure` / 引理 `IsLoop.closure`

English:
lemma IsLoop.closure
  given: (he : M.IsLoop e)
  statement: M.closure {e} = M.loops
  proof: closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

中文:
引理 IsLoop.closure
  条件: (he : M.IsLoop e)
  结论: M.closure {e} = M.loops
  证明: closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

Depends on / 依赖: closure_eq_loops_of_subset, singleton_subset_iff, singleton_subset_iff.mpr
-/
lemma IsLoop.closure (he : M.IsLoop e) : M.closure {e} = M.loops :=
  closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

/--
lemma `isLoop_iff_closure_eq_loops_and_mem_ground` / 引理 `isLoop_iff_closure_eq_loops_and_mem_ground`

English:
lemma isLoop_iff_closure_eq_loops_and_mem_ground
  proof: ⟨h.closure, h.mem_ground⟩
  mpr h := by
    rw [isLoop_iff]; rw [← closure_empty]; rw [← singleton_subset_iff]; rw [← closure_subset_closure_iff_subset_closure]; rw [h.1]; rw [loops]

中文:
引理 isLoop_iff_closure_eq_loops_and_mem_ground
  证明: ⟨h.closure, h.mem_ground⟩
  mpr h := by
    rw [isLoop_iff]; rw [← closure_empty]; rw [← singleton_subset_iff]; rw [← closure_subset_closure_iff_subset_closure]; rw [h.1]; rw [loops]

Depends on / 依赖: closure, h.closure, h.mem_ground, mem_ground
-/
lemma isLoop_iff_closure_eq_loops_and_mem_ground :
    M.IsLoop e ↔ M.closure {e} = M.loops ∧ e in M.E where
  mp h := ⟨h.closure, h.mem_ground⟩
  mpr h := by
    rw [isLoop_iff]; rw [← closure_empty]; rw [← singleton_subset_iff]; rw [← closure_subset_closure_iff_subset_closure]; rw [h.1]; rw [loops]

/--
lemma `isLoop_iff_closure_eq_loops` / 引理 `isLoop_iff_closure_eq_loops`

English:
lemma isLoop_iff_closure_eq_loops
  given: (he : e in M.E := by aesop_mat)
  proof: by
  rw [isLoop_iff_closure_eq_loops_and_mem_ground]; rw [and_iff_left he]

@[simp]

中文:
引理 isLoop_iff_closure_eq_loops
  条件: (he : e in M.E := by aesop_mat)
  证明: by
  rw [isLoop_iff_closure_eq_loops_and_mem_ground]; rw [and_iff_left he]

@[simp]

Depends on / 依赖: IsLoop, M.IsLoop, M.closure, M.loops, aesop_mat, and_iff_left, closure, isLoop_iff_closure_eq_loops_and_mem_ground
-/
lemma isLoop_iff_closure_eq_loops (he : e in M.E := by aesop_mat) :
    M.IsLoop e ↔ M.closure {e} = M.loops := by
  rw [isLoop_iff_closure_eq_loops_and_mem_ground]; rw [and_iff_left he]

@[simp]
/--
lemma `closure_loops` / 引理 `closure_loops`

English:
lemma closure_loops
  given: (M : Matroid α)
  statement: M.closure M.loops = M.loops
  proof: M.closure_closure ∅

@[simp]

中文:
引理 closure_loops
  条件: (M : 拟阵 α)
  结论: M.closure M.loops = M.loops
  证明: M.closure_closure ∅

@[simp]

Depends on / 依赖: M.closure_closure, closure_closure
-/
lemma closure_loops (M : Matroid α) : M.closure M.loops = M.loops :=
  M.closure_closure ∅

@[simp]
/--
lemma `closure_union_loops_eq` / 引理 `closure_union_loops_eq`

English:
lemma closure_union_loops_eq
  given: (M : Matroid α) (X : Set α)
  proof: by
  rw [← closure_empty]; rw [closure_union_closure_right_eq]; rw [union_empty]

@[simp]

中文:
引理 closure_union_loops_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  rw [← closure_empty]; rw [closure_union_closure_right_eq]; rw [union_empty]

@[simp]

Depends on / 依赖: closure_empty, closure_union_closure_right_eq, union_empty
-/
lemma closure_union_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X union M.loops) = M.closure X := by
  rw [← closure_empty]; rw [closure_union_closure_right_eq]; rw [union_empty]

@[simp]
/--
lemma `closure_loops_union_eq` / 引理 `closure_loops_union_eq`

English:
lemma closure_loops_union_eq
  given: (M : Matroid α) (X : Set α)
  proof: by
  simp [union_comm]

中文:
引理 closure_loops_union_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  simp [union_comm]

Depends on / 依赖: union_comm
-/
lemma closure_loops_union_eq (M : Matroid α) (X : Set α) :
    M.closure (M.loops union X) = M.closure X := by
  simp [union_comm]

/--
lemma `closure_sdiff_loops_eq` / 引理 `closure_sdiff_loops_eq`

English:
lemma closure_sdiff_loops_eq
  given: (M : Matroid α) (X : Set α)
  proof: by
  rw [← M.closure_union_loops_eq (X \ M.loops)]; rw [sdiff_union_self]; rw [← closure_empty]; rw [closure_union_closure_right_eq]; rw [union_empty]

@[deprecated (since := "2026-06-03")] alias closure_diff_loops_eq := closure_sdiff_loops_eq

中文:
引理 closure_sdiff_loops_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  rw [← M.closure_union_loops_eq (X \ M.loops)]; rw [sdiff_union_self]; rw [← closure_empty]; rw [closure_union_closure_right_eq]; rw [union_empty]

@[deprecated (since := "2026-06-03")] alias closure_diff_loops_eq := closure_sdiff_loops_eq

Depends on / 依赖: Quotient, Quotient.liftOn, liftOn
-/
@[simp] lemma closure_sdiff_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X \ M.loops) = M.closure X := by
  rw [← M.closure_union_loops_eq (X \ M.loops)]; rw [sdiff_union_self]; rw [← closure_empty]; rw [closure_union_closure_right_eq]; rw [union_empty]

@[deprecated (since := "2026-06-03")] alias closure_diff_loops_eq := closure_sdiff_loops_eq

/--
lemma `restrict_loops_eq'` / 引理 `restrict_loops_eq'`

English:
lemma restrict_loops_eq'
  given: (M : Matroid α) (R : Set α)
  proof: by
  rw [← closure_empty]; rw [← closure_empty]; rw [restrict_closure_eq']; rw [empty_inter]

中文:
引理 restrict_loops_eq'
  条件: (M : 拟阵 α) (R : 集合 α)
  证明: by
  rw [← closure_empty]; rw [← closure_empty]; rw [restrict_closure_eq']; rw [empty_inter]

Depends on / 依赖: closure_empty, empty_inter, restrict_closure_eq
-/
lemma restrict_loops_eq' (M : Matroid α) (R : Set α) :
    (M ↾ R).loops = (M.loops inter R) union (R \ M.E) := by
  rw [← closure_empty]; rw [← closure_empty]; rw [restrict_closure_eq']; rw [empty_inter]

/--
lemma `restrict_loops_eq` / 引理 `restrict_loops_eq`

English:
lemma restrict_loops_eq
  given: {R : Set α} (hR : R subseteq M.E)
  statement: (M ↾ R).loops = M.loops inter R
  proof: by
  rw [restrict_loops_eq']; rw [sdiff_eq_empty.2 hR]; rw [union_empty]

@[simp]

中文:
引理 restrict_loops_eq
  条件: {R : 集合 α} (hR : R subseteq M.E)
  结论: (M ↾ R).loops = M.loops inter R
  证明: by
  rw [restrict_loops_eq']; rw [sdiff_eq_empty.2 hR]; rw [union_empty]

@[simp]

Depends on / 依赖: restrict_loops_eq, sdiff_eq_empty, union_empty
-/
lemma restrict_loops_eq {R : Set α} (hR : R subseteq M.E) : (M ↾ R).loops = M.loops inter R := by
  rw [restrict_loops_eq']; rw [sdiff_eq_empty.2 hR]; rw [union_empty]

@[simp]
/--
lemma `restrict_isLoop_iff` / 引理 `restrict_isLoop_iff`

English:
lemma restrict_isLoop_iff
  given: {R : Set α}
  statement: (M ↾ R).IsLoop e ↔ e in R ∧ (M.IsLoop e ∨ e ∉ M.E)
  proof: by
  simp only [isLoop_iff, restrict_closure_eq', empty_inter, mem_union, mem_inter_iff, mem_sdiff,
    ← closure_empty]
  tauto

中文:
引理 restrict_isLoop_iff
  条件: {R : 集合 α}
  结论: (M ↾ R).IsLoop e ↔ e in R ∧ (M.IsLoop e ∨ e ∉ M.E)
  证明: by
  simp only [isLoop_iff, restrict_closure_eq', empty_inter, mem_union, mem_inter_iff, mem_sdiff,
    ← closure_empty]
  tauto

Depends on / 依赖: closure_empty, empty_inter, isLoop_iff, mem_inter_iff, mem_sdiff, mem_union, restrict_closure_eq
-/
lemma restrict_isLoop_iff {R : Set α} : (M ↾ R).IsLoop e ↔ e in R ∧ (M.IsLoop e ∨ e ∉ M.E) := by
  simp only [isLoop_iff, restrict_closure_eq', empty_inter, mem_union, mem_inter_iff, mem_sdiff,
    ← closure_empty]
  tauto

/--
lemma `IsRestriction.isLoop_iff` / 引理 `IsRestriction.isLoop_iff`

English:
lemma IsRestriction.isLoop_iff
  given: (hNM : N <=r M)
  statement: N.IsLoop e ↔ e in N.E ∧ M.IsLoop e
  proof: by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE => (heE (hR heR)).elim

中文:
引理 IsRestriction.isLoop_iff
  条件: (hNM : N <=r M)
  结论: N.IsLoop e ↔ e in N.E ∧ M.IsLoop e
  证明: by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE => (heE (hR heR)).elim

Depends on / 依赖: and_congr_right_iff, or_iff_left_iff_imp, restrict_ground_eq, restrict_isLoop_iff
-/
lemma IsRestriction.isLoop_iff (hNM : N <=r M) : N.IsLoop e ↔ e in N.E ∧ M.IsLoop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE => (heE (hR heR)).elim

/--
lemma `IsLoop.of_isRestriction` / 引理 `IsLoop.of_isRestriction`

English:
lemma IsLoop.of_isRestriction
  given: (he : N.IsLoop e) (hNM : N <=r M)
  statement: M.IsLoop e
  proof: ((hNM.isLoop_iff).1 he).2

中文:
引理 IsLoop.of_isRestriction
  条件: (he : N.IsLoop e) (hNM : N <=r M)
  结论: M.IsLoop e
  证明: ((hNM.isLoop_iff).1 he).2

Depends on / 依赖: hNM.isLoop_iff, isLoop_iff
-/
lemma IsLoop.of_isRestriction (he : N.IsLoop e) (hNM : N <=r M) : M.IsLoop e :=
  ((hNM.isLoop_iff).1 he).2

/--
lemma `IsLoop.isLoop_isRestriction` / 引理 `IsLoop.isLoop_isRestriction`

English:
lemma IsLoop.isLoop_isRestriction
  given: (he : M.IsLoop e) (hNM : N <=r M) (heN : e in N.E)
  statement: N.IsLoop e
  proof: (hNM.isLoop_iff).2 ⟨heN, he⟩

@[simp]

中文:
引理 IsLoop.isLoop_isRestriction
  条件: (he : M.IsLoop e) (hNM : N <=r M) (heN : e in N.E)
  结论: N.IsLoop e
  证明: (hNM.isLoop_iff).2 ⟨heN, he⟩

@[simp]

Depends on / 依赖: hNM.isLoop_iff, isLoop_iff
-/
lemma IsLoop.isLoop_isRestriction (he : M.IsLoop e) (hNM : N <=r M) (heN : e in N.E) : N.IsLoop e :=
  (hNM.isLoop_iff).2 ⟨heN, he⟩

@[simp]
/--
lemma `map_loops` / 引理 `map_loops`

English:
lemma map_loops
  given: {f : α -> β} {hf : InjOn f M.E}
  statement: (M.map f hf).loops = f '' M.loops
  proof: by
  simp [loops]

@[simp]

中文:
引理 map_loops
  条件: {f : α -> β} {hf : 单射限制 f M.E}
  结论: (M.map f hf).loops = f '' M.loops
  证明: by
  simp [loops]

@[simp]
-/
lemma map_loops {f : α -> β} {hf : InjOn f M.E} : (M.map f hf).loops = f '' M.loops := by
  simp [loops]

@[simp]
/--
lemma `map_isLoop_iff` / 引理 `map_isLoop_iff`

English:
lemma map_isLoop_iff
  given: {f : α -> β} {hf : InjOn f M.E} (he : e in M.E := by aesop_mat)
  proof: by
  rw [isLoop_iff]; rw [map_loops]; rw [hf.mem_image_iff M.loops_subset_ground he]; rw [isLoop_iff]

@[simp]

中文:
引理 map_isLoop_iff
  条件: {f : α -> β} {hf : 单射限制 f M.E} (he : e in M.E := by aesop_mat)
  证明: by
  rw [isLoop_iff]; rw [map_loops]; rw [hf.mem_image_iff M.loops_subset_ground he]; rw [isLoop_iff]

@[simp]

Depends on / 依赖: IsLoop, M.IsLoop, M.loops_subset_ground, M.map, aesop_mat, hf.mem_image_iff, isLoop_iff, loops_subset_ground, map_loops, mem_image_iff
-/
lemma map_isLoop_iff {f : α -> β} {hf : InjOn f M.E} (he : e in M.E := by aesop_mat) :
    (M.map f hf).IsLoop (f e) ↔ M.IsLoop e := by
  rw [isLoop_iff]; rw [map_loops]; rw [hf.mem_image_iff M.loops_subset_ground he]; rw [isLoop_iff]

@[simp]
/--
lemma `mapEmbedding_isLoop_iff` / 引理 `mapEmbedding_isLoop_iff`

English:
lemma mapEmbedding_isLoop_iff
  given: {f : α ↪ β}
  statement: (M.mapEmbedding f).IsLoop (f e) ↔ M.IsLoop e
  proof: by
  simp [mapEmbedding, isLoop_iff, isLoop_iff, map_closure_eq, preimage_empty, ← closure_empty]

@[simp]

中文:
引理 mapEmbedding_isLoop_iff
  条件: {f : α ↪ β}
  结论: (M.mapEmbedding f).IsLoop (f e) ↔ M.IsLoop e
  证明: by
  simp [mapEmbedding, isLoop_iff, isLoop_iff, map_closure_eq, preimage_empty, ← closure_empty]

@[simp]

Depends on / 依赖: closure_empty, isLoop_iff, mapEmbedding, map_closure_eq, preimage_empty
-/
lemma mapEmbedding_isLoop_iff {f : α ↪ β} : (M.mapEmbedding f).IsLoop (f e) ↔ M.IsLoop e := by
  simp [mapEmbedding, isLoop_iff, isLoop_iff, map_closure_eq, preimage_empty, ← closure_empty]

@[simp]
/--
lemma `comap_loops` / 引理 `comap_loops`

English:
lemma comap_loops
  given: {M : Matroid β} {f : α -> β}
  statement: (M.comap f).loops = f ⁻¹' M.loops
  proof: by
  rw [loops]; rw [comap_closure_eq]; rw [image_empty]; rw [loops]

@[simp]

中文:
引理 comap_loops
  条件: {M : 拟阵 β} {f : α -> β}
  结论: (M.comap f).loops = f ⁻¹' M.loops
  证明: by
  rw [loops]; rw [comap_closure_eq]; rw [image_empty]; rw [loops]

@[simp]

Depends on / 依赖: Quotient, Quotient.lift.decidablePred, comap_closure_eq, decidablePred, image_empty
-/
lemma comap_loops {M : Matroid β} {f : α -> β} : (M.comap f).loops = f ⁻¹' M.loops := by
  rw [loops]; rw [comap_closure_eq]; rw [image_empty]; rw [loops]

@[simp]
/--
lemma `comap_isLoop_iff` / 引理 `comap_isLoop_iff`

English:
lemma comap_isLoop_iff
  given: {M : Matroid β} {f : α -> β}
  statement: (M.comap f).IsLoop e ↔ M.IsLoop (f e)
  proof: by
  simp [isLoop_iff]

@[simp]

中文:
引理 comap_isLoop_iff
  条件: {M : 拟阵 β} {f : α -> β}
  结论: (M.comap f).IsLoop e ↔ M.IsLoop (f e)
  证明: by
  simp [isLoop_iff]

@[simp]

Depends on / 依赖: Quotient, Quotient.lift, decidablePred, isLoop_iff
-/
lemma comap_isLoop_iff {M : Matroid β} {f : α -> β} : (M.comap f).IsLoop e ↔ M.IsLoop (f e) := by
  simp [isLoop_iff]

@[simp]
/--
lemma `loopyOn_isLoop_iff` / 引理 `loopyOn_isLoop_iff`

English:
lemma loopyOn_isLoop_iff
  given: {E : Set α}
  statement: (loopyOn E).IsLoop e ↔ e in E
  proof: by
  simp [isLoop_iff, loops]

中文:
引理 loopyOn_isLoop_iff
  条件: {E : 集合 α}
  结论: (loopyOn E).IsLoop e ↔ e in E
  证明: by
  simp [isLoop_iff, loops]

Depends on / 依赖: isLoop_iff
-/
lemma loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e in E := by
  simp [isLoop_iff, loops]

/--
lemma `eq_loopyOn_iff_loops` / 引理 `eq_loopyOn_iff_loops`

English:
lemma eq_loopyOn_iff_loops
  given: {E : Set α}
  statement: M = loopyOn E ↔ M.loops = E ∧ M.E = E where
  proof: by rw [h, loops]; simp
  mpr | ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']

中文:
引理 eq_loopyOn_iff_loops
  条件: {E : 集合 α}
  结论: M = loopyOn E ↔ M.loops = E ∧ M.E = E where
  证明: by rw [h, loops]; simp
  mpr | ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']

Depends on / 依赖: closure_empty_eq_ground_iff
-/
lemma eq_loopyOn_iff_loops {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E where
  mp h := by rw [h, loops]; simp
  mpr | ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']

/--
lemma `restrict_subset_loops_eq` / 引理 `restrict_subset_loops_eq`

English:
lemma restrict_subset_loops_eq
  given: (hX : X subseteq M.loops)
  statement: M ↾ X = loopyOn X
  proof: by
  rw [eq_loopyOn_iff_loops]; rw [restrict_loops_eq']; rw [inter_eq_self_of_subset_right hX]; rw [union_eq_self_of_subset_right sdiff_subset]; rw [and_iff_left M.restrict_ground_eq]

@[simp]

中文:
引理 restrict_subset_loops_eq
  条件: (hX : X subseteq M.loops)
  结论: M ↾ X = loopyOn X
  证明: by
  rw [eq_loopyOn_iff_loops]; rw [restrict_loops_eq']; rw [inter_eq_self_of_subset_right hX]; rw [union_eq_self_of_subset_right sdiff_subset]; rw [and_iff_left M.restrict_ground_eq]

@[simp]

Depends on / 依赖: M.restrict_ground_eq, and_iff_left, eq_loopyOn_iff_loops, inter_eq_self_of_subset_right, restrict_ground_eq, restrict_loops_eq, sdiff_subset, union_eq_self_of_subset_right
-/
lemma restrict_subset_loops_eq (hX : X subseteq M.loops) : M ↾ X = loopyOn X := by
  rw [eq_loopyOn_iff_loops]; rw [restrict_loops_eq']; rw [inter_eq_self_of_subset_right hX]; rw [union_eq_self_of_subset_right sdiff_subset]; rw [and_iff_left M.restrict_ground_eq]

@[simp]
/--
lemma `freeOn_not_isLoop` / 引理 `freeOn_not_isLoop`

English:
lemma freeOn_not_isLoop
  given: (E : Set α) (e : α)
  statement: ¬ (freeOn E).IsLoop e
  proof: by
  simp [isLoop_iff, loops]

@[simp]

中文:
引理 freeOn_not_isLoop
  条件: (E : 集合 α) (e : α)
  结论: ¬ (freeOn E).IsLoop e
  证明: by
  simp [isLoop_iff, loops]

@[simp]

Depends on / 依赖: isLoop_iff
-/
lemma freeOn_not_isLoop (E : Set α) (e : α) : ¬ (freeOn E).IsLoop e := by
  simp [isLoop_iff, loops]

@[simp]
/--
lemma `uniqueBaseOn_isLoop_iff` / 引理 `uniqueBaseOn_isLoop_iff`

English:
lemma uniqueBaseOn_isLoop_iff
  given: {I E : Set α}
  statement: (uniqueBaseOn I E).IsLoop e ↔ e in E \ I
  proof: by
  simp [isLoop_iff, loops]

中文:
引理 uniqueBaseOn_isLoop_iff
  条件: {I E : 集合 α}
  结论: (uniqueBaseOn I E).IsLoop e ↔ e in E \ I
  证明: by
  simp [isLoop_iff, loops]

Depends on / 依赖: isLoop_iff
-/
lemma uniqueBaseOn_isLoop_iff {I E : Set α} : (uniqueBaseOn I E).IsLoop e ↔ e in E \ I := by
  simp [isLoop_iff, loops]

/--
lemma `eq_loopyOn_iff_loops_eq` / 引理 `eq_loopyOn_iff_loops_eq`

English:
lemma eq_loopyOn_iff_loops_eq
  given: {E : Set α}
  statement: M = loopyOn E ↔ M.loops = E ∧ M.E = E
  proof: ⟨fun h => by simp [h, loops],
  fun ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

中文:
引理 eq_loopyOn_iff_loops_eq
  条件: {E : 集合 α}
  结论: M = loopyOn E ↔ M.loops = E ∧ M.E = E
  证明: ⟨fun h => by simp [h, loops],
  fun ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

Depends on / 依赖: closure_empty_eq_ground_iff
-/
lemma eq_loopyOn_iff_loops_eq {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E :=
  ⟨fun h => by simp [h, loops],
  fun ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

section IsNonloop

/-- `M.IsNonloop e` means that `e` is an element of `M.E` but not a loop of `M`. -/
@[mk_iff]
/--
Definition of `IsNonloop` / `IsNonloop` 的定义

English:
structure IsNonloop
  parameters: (M : Matroid α) (e : α)
  axioms and operations (2):
    - not_isLoop : ¬ M.IsLoop e
    - mem_ground : e in M.E

中文:
结构 是Nonloop
  参数: (M : 拟阵 α) (e : α)
  公理与运算 (2 个):
    - not_isLoop : ¬ M.IsLoop e
    - mem_ground : e in M.E

Depends on / 依赖: IsNonloop, IsNonloop.mem_ground, Matroid, mem_ground
-/
structure IsNonloop (M : Matroid α) (e : α) : Prop where
  not_isLoop : ¬ M.IsLoop e
  mem_ground : e in M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsNonloop.mem_ground

/--
lemma `IsLoop.not_isNonloop` / 引理 `IsLoop.not_isNonloop`

English:
lemma IsLoop.not_isNonloop
  given: (he : M.IsLoop e)
  statement: ¬M.IsNonloop e
  proof: fun h => h.not_isLoop he

中文:
引理 IsLoop.not_isNonloop
  条件: (he : M.IsLoop e)
  结论: ¬M.是Nonloop e
  证明: fun h => h.not_isLoop he

Depends on / 依赖: h.not_isLoop, not_isLoop
-/
lemma IsLoop.not_isNonloop (he : M.IsLoop e) : ¬M.IsNonloop e :=
  fun h => h.not_isLoop he

/--
lemma `compl_loops_eq` / 引理 `compl_loops_eq`

English:
lemma compl_loops_eq
  given: (M : Matroid α)
  statement: M.E \ M.loops = {e | M.IsNonloop e}
  proof: by
  simp [Set.ext_iff, isNonloop_iff, and_comm, isLoop_iff]

中文:
引理 compl_loops_eq
  条件: (M : 拟阵 α)
  结论: M.E \ M.loops = {e | M.是Nonloop e}
  证明: by
  simp [Set.ext_iff, isNonloop_iff, and_comm, isLoop_iff]

Depends on / 依赖: Set.ext_iff, and_comm, ext_iff, isLoop_iff, isNonloop_iff
-/
lemma compl_loops_eq (M : Matroid α) : M.E \ M.loops = {e | M.IsNonloop e} := by
  simp [Set.ext_iff, isNonloop_iff, and_comm, isLoop_iff]

/--
lemma `isNonloop_of_not_isLoop` / 引理 `isNonloop_of_not_isLoop`

English:
lemma isNonloop_of_not_isLoop
  given: (he : e in M.E := by aesop_mat) (h : ¬ M.IsLoop e)
  statement: M.IsNonloop e
  proof: ⟨h,he⟩

中文:
引理 isNonloop_of_not_isLoop
  条件: (he : e in M.E := by aesop_mat) (h : ¬ M.IsLoop e)
  结论: M.是Nonloop e
  证明: ⟨h,he⟩

Depends on / 依赖: IsLoop, IsNonloop, M.IsLoop, M.IsNonloop, aesop_mat
-/
lemma isNonloop_of_not_isLoop (he : e in M.E := by aesop_mat) (h : ¬ M.IsLoop e) : M.IsNonloop e :=
  ⟨h,he⟩

/--
lemma `isLoop_of_not_isNonloop` / 引理 `isLoop_of_not_isNonloop`

English:
lemma isLoop_of_not_isNonloop
  given: (he : e in M.E := by aesop_mat) (h : ¬ M.IsNonloop e)
  proof: by
  rwa [isNonloop_iff, and_iff_left he, not_not] at h

@[simp]

中文:
引理 isLoop_of_not_isNonloop
  条件: (he : e in M.E := by aesop_mat) (h : ¬ M.是Nonloop e)
  证明: by
  rwa [isNonloop_iff, and_iff_left he, not_not] at h

@[simp]

Depends on / 依赖: IsLoop, IsNonloop, M.IsLoop, M.IsNonloop, aesop_mat, and_iff_left, isNonloop_iff, not_not
-/
lemma isLoop_of_not_isNonloop (he : e in M.E := by aesop_mat) (h : ¬ M.IsNonloop e) :
    M.IsLoop e := by
  rwa [isNonloop_iff, and_iff_left he, not_not] at h

@[simp]
/--
lemma `not_isLoop_iff` / 引理 `not_isLoop_iff`

English:
lemma not_isLoop_iff
  given: (he : e in M.E := by aesop_mat)
  statement: ¬M.IsLoop e ↔ M.IsNonloop e
  proof: ⟨fun h => ⟨h, he⟩, IsNonloop.not_isLoop⟩

@[simp]

中文:
引理 not_isLoop_iff
  条件: (he : e in M.E := by aesop_mat)
  结论: ¬M.IsLoop e ↔ M.是Nonloop e
  证明: ⟨fun h => ⟨h, he⟩, IsNonloop.not_isLoop⟩

@[simp]

Depends on / 依赖: IsLoop, IsNonloop, IsNonloop.not_isLoop, M.IsLoop, M.IsNonloop, aesop_mat, not_isLoop
-/
lemma not_isLoop_iff (he : e in M.E := by aesop_mat) : ¬M.IsLoop e ↔ M.IsNonloop e :=
  ⟨fun h => ⟨h, he⟩, IsNonloop.not_isLoop⟩

@[simp]
/--
lemma `not_isNonloop_iff` / 引理 `not_isNonloop_iff`

English:
lemma not_isNonloop_iff
  given: (he : e in M.E := by aesop_mat)
  statement: ¬M.IsNonloop e ↔ M.IsLoop e
  proof: by
  rw [← not_isLoop_iff]; rw [not_not]

中文:
引理 not_isNonloop_iff
  条件: (he : e in M.E := by aesop_mat)
  结论: ¬M.是Nonloop e ↔ M.IsLoop e
  证明: by
  rw [← not_isLoop_iff]; rw [not_not]

Depends on / 依赖: IsLoop, IsNonloop, M.IsLoop, M.IsNonloop, aesop_mat, not_isLoop_iff, not_not
-/
lemma not_isNonloop_iff (he : e in M.E := by aesop_mat) : ¬M.IsNonloop e ↔ M.IsLoop e := by
  rw [← not_isLoop_iff]; rw [not_not]

/--
lemma `isNonloop_iff_mem_compl_loops` / 引理 `isNonloop_iff_mem_compl_loops`

English:
lemma isNonloop_iff_mem_compl_loops
  statement: M.IsNonloop e ↔ e in M.E \ M.loops
  proof: by
  rw [isNonloop_iff]; rw [IsLoop]; rw [and_comm]; rw [mem_sdiff]

中文:
引理 isNonloop_iff_mem_compl_loops
  结论: M.是Nonloop e ↔ e in M.E \ M.loops
  证明: by
  rw [isNonloop_iff]; rw [IsLoop]; rw [and_comm]; rw [mem_sdiff]

Depends on / 依赖: IsLoop, and_comm, isNonloop_iff, mem_sdiff
-/
lemma isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e in M.E \ M.loops := by
  rw [isNonloop_iff]; rw [IsLoop]; rw [and_comm]; rw [mem_sdiff]

/--
lemma `setOfPred_isNonloop_eq` / 引理 `setOfPred_isNonloop_eq`

English:
lemma setOfPred_isNonloop_eq
  given: (M : Matroid α)
  statement: {e | M.IsNonloop e} = M.E \ M.loops
  proof: Set.ext (fun _ => isNonloop_iff_mem_compl_loops)

@[deprecated (since := "2026-07-09")]
alias setOf_isNonloop_eq := setOfPred_isNonloop_eq

中文:
引理 setOfPred_isNonloop_eq
  条件: (M : 拟阵 α)
  结论: {e | M.是Nonloop e} = M.E \ M.loops
  证明: Set.ext (fun _ => isNonloop_iff_mem_compl_loops)

@[deprecated (since := "2026-07-09")]
alias setOf_isNonloop_eq := setOfPred_isNonloop_eq

Depends on / 依赖: Set.ext, isNonloop_iff_mem_compl_loops
-/
lemma setOfPred_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.loops :=
  Set.ext (fun _ => isNonloop_iff_mem_compl_loops)

@[deprecated (since := "2026-07-09")]
alias setOf_isNonloop_eq := setOfPred_isNonloop_eq

/--
lemma `not_isNonloop_iff_closure` / 引理 `not_isNonloop_iff_closure`

English:
lemma not_isNonloop_iff_closure
  statement: ¬ M.IsNonloop e ↔ M.closure {e} = M.loops
  proof: by
  by_cases he : e in M.E
  · simp [isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he, loops,
    (show ¬ M.IsNonloop e from fun h => he h.mem_ground)]

中文:
引理 not_isNonloop_iff_closure
  结论: ¬ M.是Nonloop e ↔ M.closure {e} = M.loops
  证明: by
  by_cases he : e in M.E
  · simp [isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he, loops,
    (show ¬ M.IsNonloop e from fun h => he h.mem_ground)]

Depends on / 依赖: IsNonloop, M.IsNonloop, closure_inter_ground, h.mem_ground, isLoop_iff_closure_eq_loops_and_mem_ground, mem_ground, singleton_inter_eq_empty
-/
lemma not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.loops := by
  by_cases he : e in M.E
  · simp [isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he, loops,
    (show ¬ M.IsNonloop e from fun h => he h.mem_ground)]

/--
lemma `isLoop_or_isNonloop` / 引理 `isLoop_or_isNonloop`

English:
lemma isLoop_or_isNonloop
  given: (M : Matroid α) (e : α) (he : e in M.E := by aesop_mat)
  proof: by
  rw [isNonloop_iff]; rw [and_iff_left he]; apply em

@[simp]

中文:
引理 isLoop_or_isNonloop
  条件: (M : 拟阵 α) (e : α) (he : e in M.E := by aesop_mat)
  证明: by
  rw [isNonloop_iff]; rw [and_iff_left he]; apply em

@[simp]

Depends on / 依赖: IsLoop, IsNonloop, M.IsLoop, M.IsNonloop, aesop_mat, and_iff_left, isNonloop_iff
-/
lemma isLoop_or_isNonloop (M : Matroid α) (e : α) (he : e in M.E := by aesop_mat) :
    M.IsLoop e ∨ M.IsNonloop e := by
  rw [isNonloop_iff]; rw [and_iff_left he]; apply em

@[simp]
/--
lemma `indep_singleton` / 引理 `indep_singleton`

English:
lemma indep_singleton
  statement: M.Indep {e} ↔ M.IsNonloop e
  proof: by
  rw [isNonloop_iff]; rw [← singleton_dep]; rw [dep_iff]; rw [not_and]; rw [not_imp_not]; rw [singleton_subset_iff]
  exact ⟨fun h => ⟨fun _ => h, singleton_subset_iff.mp h.subset_ground⟩, fun h => h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton

中文:
引理 indep_singleton
  结论: M.Indep {e} ↔ M.是Nonloop e
  证明: by
  rw [isNonloop_iff]; rw [← singleton_dep]; rw [dep_iff]; rw [not_and]; rw [not_imp_not]; rw [singleton_subset_iff]
  exact ⟨fun h => ⟨fun _ => h, singleton_subset_iff.mp h.subset_ground⟩, fun h => h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton

Depends on / 依赖: dep_iff, h.subset_ground, isNonloop_iff, not_and, not_imp_not, singleton_dep, singleton_subset_iff, singleton_subset_iff.mp, subset_ground
-/
lemma indep_singleton : M.Indep {e} ↔ M.IsNonloop e := by
  rw [isNonloop_iff]; rw [← singleton_dep]; rw [dep_iff]; rw [not_and]; rw [not_imp_not]; rw [singleton_subset_iff]
  exact ⟨fun h => ⟨fun _ => h, singleton_subset_iff.mp h.subset_ground⟩, fun h => h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton

/--
lemma `Indep.isNonloop_of_mem` / 引理 `Indep.isNonloop_of_mem`

English:
lemma Indep.isNonloop_of_mem
  given: (hI : M.Indep I) (h : e in I)
  statement: M.IsNonloop e
  proof: by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he => (he.notMem_of_indep hI) h

中文:
引理 Indep.isNonloop_of_mem
  条件: (hI : M.Indep I) (h : e in I)
  结论: M.是Nonloop e
  证明: by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he => (he.notMem_of_indep hI) h

Depends on / 依赖: hI.subset_ground, he.notMem_of_indep, notMem_of_indep, not_isLoop_iff, subset_ground
-/
lemma Indep.isNonloop_of_mem (hI : M.Indep I) (h : e in I) : M.IsNonloop e := by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he => (he.notMem_of_indep hI) h

/--
lemma `IsNonloop.exists_mem_isBase` / 引理 `IsNonloop.exists_mem_isBase`

English:
lemma IsNonloop.exists_mem_isBase
  given: (he : M.IsNonloop e)
  statement: exists B, M.IsBase B ∧ e in B
  proof: by
  simpa using (indep_singleton.2 he).exists_isBase_superset

中文:
引理 是Nonloop.存在_mem_isBase
  条件: (he : M.是Nonloop e)
  结论: 存在 B, M.IsBase B ∧ e in B
  证明: by
  simpa using (indep_singleton.2 he).exists_isBase_superset

Depends on / 依赖: exists_isBase_superset, indep_singleton
-/
lemma IsNonloop.exists_mem_isBase (he : M.IsNonloop e) : exists B, M.IsBase B ∧ e in B := by
  simpa using (indep_singleton.2 he).exists_isBase_superset

/--
lemma `IsCocircuit.isNonloop_of_mem` / 引理 `IsCocircuit.isNonloop_of_mem`

English:
lemma IsCocircuit.isNonloop_of_mem
  given: {K : Set α} (hK : M.IsCocircuit K) (he : e in K)
  proof: by
  rw [← not_isLoop_iff (hK.subset_ground he)]; rw [← singleton_isCircuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.isCocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl

中文:
引理 IsCocircuit.isNonloop_of_mem
  条件: {K : 集合 α} (hK : M.IsCocircuit K) (he : e in K)
  证明: by
  rw [← not_isLoop_iff (hK.subset_ground he)]; rw [← singleton_isCircuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.isCocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl

Depends on / 依赖: exists_ne, hK.subset_ground, isCocircuit_inter_nontrivial, not_isLoop_iff, singleton_isCircuit, subset_ground
-/
lemma IsCocircuit.isNonloop_of_mem {K : Set α} (hK : M.IsCocircuit K) (he : e in K) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff (hK.subset_ground he)]; rw [← singleton_isCircuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.isCocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl

/--
lemma `IsCircuit.isNonloop_of_mem` / 引理 `IsCircuit.isNonloop_of_mem`

English:
lemma IsCircuit.isNonloop_of_mem
  given: (hC : M.IsCircuit C) (hC' : C.Nontrivial) (he : e in C)
  proof: isNonloop_of_not_isLoop (hC.subset_ground he)
    (fun hL => by simp [hL.eq_of_isCircuit_mem hC he] at hC')

中文:
引理 是Circuit.isNonloop_of_mem
  条件: (hC : M.是Circuit C) (hC' : C.非平凡) (he : e in C)
  证明: isNonloop_of_not_isLoop (hC.subset_ground he)
    (fun hL => by simp [hL.eq_of_isCircuit_mem hC he] at hC')

Depends on / 依赖: eq_of_isCircuit_mem, hC.subset_ground, hL.eq_of_isCircuit_mem, isNonloop_of_not_isLoop, subset_ground
-/
lemma IsCircuit.isNonloop_of_mem (hC : M.IsCircuit C) (hC' : C.Nontrivial) (he : e in C) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop (hC.subset_ground he)
    (fun hL => by simp [hL.eq_of_isCircuit_mem hC he] at hC')

/--
lemma `IsCircuit.isNonloop_of_mem_of_one_lt_card` / 引理 `IsCircuit.isNonloop_of_mem_of_one_lt_card`

English:
lemma IsCircuit.isNonloop_of_mem_of_one_lt_card
  statement: (hC : M.IsCircuit C) (h : 1 < C.encard)
  proof: by
  refine isNonloop_of_not_isLoop (hC.subset_ground he) (fun hlp => ?_)
  rw [hlp.eq_of_isCircuit_mem hC he]; rw [encard_singleton] at h
  exact h.ne rfl

中文:
引理 是Circuit.isNonloop_of_mem_of_one_lt_card
  结论: (hC : M.是Circuit C) (h : 1 < C.encard)
  证明: by
  refine isNonloop_of_not_isLoop (hC.subset_ground he) (fun hlp => ?_)
  rw [hlp.eq_of_isCircuit_mem hC he]; rw [encard_singleton] at h
  exact h.ne rfl

Depends on / 依赖: encard_singleton, eq_of_isCircuit_mem, h.ne, hC.subset_ground, hlp.eq_of_isCircuit_mem, isNonloop_of_not_isLoop, subset_ground
-/
lemma IsCircuit.isNonloop_of_mem_of_one_lt_card (hC : M.IsCircuit C) (h : 1 < C.encard)
    (he : e in C) : M.IsNonloop e := by
  refine isNonloop_of_not_isLoop (hC.subset_ground he) (fun hlp => ?_)
  rw [hlp.eq_of_isCircuit_mem hC he]; rw [encard_singleton] at h
  exact h.ne rfl

/--
lemma `isNonloop_of_notMem_closure` / 引理 `isNonloop_of_notMem_closure`

English:
lemma isNonloop_of_notMem_closure
  given: (h : e ∉ M.closure X) (he : e in M.E := by aesop_mat)
  proof: isNonloop_of_not_isLoop he (fun hel => h (hel.mem_closure X))

中文:
引理 isNonloop_of_notMem_closure
  条件: (h : e ∉ M.closure X) (he : e in M.E := by aesop_mat)
  证明: isNonloop_of_not_isLoop he (fun hel => h (hel.mem_closure X))

Depends on / 依赖: IsNonloop, M.IsNonloop, aesop_mat, hel.mem_closure, isNonloop_of_not_isLoop, mem_closure
-/
lemma isNonloop_of_notMem_closure (h : e ∉ M.closure X) (he : e in M.E := by aesop_mat) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop he (fun hel => h (hel.mem_closure X))

/--
lemma `isNonloop_iff_notMem_loops` / 引理 `isNonloop_iff_notMem_loops`

English:
lemma isNonloop_iff_notMem_loops
  given: (he : e in M.E := by aesop_mat)
  proof: by
  rw [isNonloop_iff]; rw [isLoop_iff]; rw [and_iff_left he]

中文:
引理 isNonloop_iff_notMem_loops
  条件: (he : e in M.E := by aesop_mat)
  证明: by
  rw [isNonloop_iff]; rw [isLoop_iff]; rw [and_iff_left he]

Depends on / 依赖: IsNonloop, M.IsNonloop, M.loops, aesop_mat, and_iff_left, isLoop_iff, isNonloop_iff
-/
lemma isNonloop_iff_notMem_loops (he : e in M.E := by aesop_mat) :
    M.IsNonloop e ↔ e ∉ M.loops := by
  rw [isNonloop_iff]; rw [isLoop_iff]; rw [and_iff_left he]

/--
lemma `IsNonloop.mem_closure_singleton` / 引理 `IsNonloop.mem_closure_singleton`

English:
lemma IsNonloop.mem_closure_singleton
  given: (he : M.IsNonloop e) (hef : e in M.closure {f})
  proof: by
  rw [← union_empty {_}]; rw [singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_notMem_loops he.mem_ground).1 he⟩).1

中文:
引理 是Nonloop.mem_closure_singleton
  条件: (he : M.是Nonloop e) (hef : e in M.closure {f})
  证明: by
  rw [← union_empty {_}]; rw [singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_notMem_loops he.mem_ground).1 he⟩).1

Depends on / 依赖: M.closure_exchange, closure_exchange, he.mem_ground, isNonloop_iff_notMem_loops, mem_ground, singleton_union, union_empty
-/
lemma IsNonloop.mem_closure_singleton (he : M.IsNonloop e) (hef : e in M.closure {f}) :
    f in M.closure {e} := by
  rw [← union_empty {_}]; rw [singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_notMem_loops he.mem_ground).1 he⟩).1

/--
lemma `IsNonloop.mem_closure_comm` / 引理 `IsNonloop.mem_closure_comm`

English:
lemma IsNonloop.mem_closure_comm
  given: (he : M.IsNonloop e) (hf : M.IsNonloop f)
  proof: ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

中文:
引理 是Nonloop.mem_closure_comm
  条件: (he : M.是Nonloop e) (hf : M.是Nonloop f)
  证明: ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

Depends on / 依赖: he.mem_closure_singleton, hf.mem_closure_singleton, mem_closure_singleton
-/
lemma IsNonloop.mem_closure_comm (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    f in M.closure {e} ↔ e in M.closure {f} :=
  ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

/--
lemma `IsNonloop.isNonloop_of_mem_closure` / 引理 `IsNonloop.isNonloop_of_mem_closure`

English:
lemma IsNonloop.isNonloop_of_mem_closure
  given: (he : M.IsNonloop e) (hef : e in M.closure {f})
  proof: by
  rw [isNonloop_iff]; rw [and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff] at *; convert! hef using 1
  obtain (hf | hf) := em (f in M.E)
  · rw [← closure_loops, ← insert_eq_of_mem (h hf), closure_insert_congr_right M.closure_loops,
      insert_empty_eq]
  rw [eq_comm]; rw [← closure_inter_ground]; rw [inter_comm]; rw [inter_singleton_eq_empty.mpr hf]; rw [loops]

中文:
引理 是Nonloop.isNonloop_of_mem_closure
  条件: (he : M.是Nonloop e) (hef : e in M.closure {f})
  证明: by
  rw [isNonloop_iff]; rw [and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff] at *; convert! hef using 1
  obtain (hf | hf) := em (f in M.E)
  · rw [← closure_loops, ← insert_eq_of_mem (h hf), closure_insert_congr_right M.closure_loops,
      insert_empty_eq]
  rw [eq_comm]; rw [← closure_inter_ground]; rw [inter_comm]; rw [inter_singleton_eq_empty.mpr hf]; rw [loops]

Depends on / 依赖: M.closure_loops, and_comm, closure_insert_congr_right, closure_inter_ground, closure_loops, convert, eq_comm, he.not_isLoop, insert_empty_eq, insert_eq_of_mem, inter_comm, inter_singleton_eq_empty, inter_singleton_eq_empty.mpr, isLoop_iff, isNonloop_iff, not_isLoop
-/
lemma IsNonloop.isNonloop_of_mem_closure (he : M.IsNonloop e) (hef : e in M.closure {f}) :
    M.IsNonloop f := by
  rw [isNonloop_iff]; rw [and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff] at *; convert! hef using 1
  obtain (hf | hf) := em (f in M.E)
  · rw [← closure_loops, ← insert_eq_of_mem (h hf), closure_insert_congr_right M.closure_loops,
      insert_empty_eq]
  rw [eq_comm]; rw [← closure_inter_ground]; rw [inter_comm]; rw [inter_singleton_eq_empty.mpr hf]; rw [loops]

/--
lemma `IsNonloop.closure_eq_of_mem_closure` / 引理 `IsNonloop.closure_eq_of_mem_closure`

English:
lemma IsNonloop.closure_eq_of_mem_closure
  given: (he : M.IsNonloop e) (hef : e in M.closure {f})
  proof: by
  rw [← closure_closure _ {f}]; rw [← insert_eq_of_mem hef]; rw [closure_insert_closure_eq_closure_insert]; rw [← closure_closure _ {e}]; rw [← insert_eq_of_mem (he.mem_closure_singleton hef)]; rw [closure_insert_closure_eq_closure_insert]; rw [pair_comm]

中文:
引理 是Nonloop.closure_eq_of_mem_closure
  条件: (he : M.是Nonloop e) (hef : e in M.closure {f})
  证明: by
  rw [← closure_closure _ {f}]; rw [← insert_eq_of_mem hef]; rw [closure_insert_closure_eq_closure_insert]; rw [← closure_closure _ {e}]; rw [← insert_eq_of_mem (he.mem_closure_singleton hef)]; rw [closure_insert_closure_eq_closure_insert]; rw [pair_comm]

Depends on / 依赖: closure_closure, closure_insert_closure_eq_closure_insert, he.mem_closure_singleton, insert_eq_of_mem, mem_closure_singleton, pair_comm
-/
lemma IsNonloop.closure_eq_of_mem_closure (he : M.IsNonloop e) (hef : e in M.closure {f}) :
    M.closure {e} = M.closure {f} := by
  rw [← closure_closure _ {f}]; rw [← insert_eq_of_mem hef]; rw [closure_insert_closure_eq_closure_insert]; rw [← closure_closure _ {e}]; rw [← insert_eq_of_mem (he.mem_closure_singleton hef)]; rw [closure_insert_closure_eq_closure_insert]; rw [pair_comm]

/--
lemma `IsNonloop.closure_eq_closure_iff_isCircuit_of_ne` / 引理 `IsNonloop.closure_eq_closure_iff_isCircuit_of_ne`

English:
lemma IsNonloop.closure_eq_closure_iff_isCircuit_of_ne
  given: (he : M.IsNonloop e) (hef : e != f)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hf := he.isNonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_right he.mem_ground]; rw [singleton_subset_iff]; rw [and_iff_left hf.mem_ground]
    suffices ¬ M.Indep {e, f} by simpa [pair_sdiff_left hef, hf, pair_sdiff_right hef, he]
    rw [Indep.insert_indep_iff_of_notMem (by simpa) (by simpa)]
    simp [← h, mem_closure_self _ _ he.mem_ground]
  have hclosure := (h.closure_sdiff_singleton_eq e).trans
    (h.closure_sdiff_singleton_eq f).symm
  rwa [pair_sdiff_left hef, pair_sdiff_right hef, eq_comm] at hclosure

中文:
引理 是Nonloop.closure_eq_closure_iff_isCircuit_of_ne
  条件: (he : M.是Nonloop e) (hef : e != f)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hf := he.isNonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_right he.mem_ground]; rw [singleton_subset_iff]; rw [and_iff_left hf.mem_ground]
    suffices ¬ M.Indep {e, f} by simpa [pair_sdiff_left hef, hf, pair_sdiff_right hef, he]
    rw [Indep.insert_indep_iff_of_notMem (by simpa) (by simpa)]
    simp [← h, mem_closure_self _ _ he.mem_ground]
  have hclosure := (h.closure_sdiff_singleton_eq e).trans
    (h.closure_sdiff_singleton_eq f).symm
  rwa [pair_sdiff_left hef, pair_sdiff_right hef, eq_comm] at hclosure

Depends on / 依赖: Indep.insert_indep_iff_of_notMem, M.Indep, M.mem_closure_self, and_iff_left, and_iff_right, dep_iff, he.isNonloop_of_mem_closure, he.mem_ground, hf.mem_ground, insert_indep_iff_of_notMem, insert_subset_iff, isCircuit_iff_dep_forall_sdiff_singleton_indep, isNonloop_of_mem_closure, mem_closure_self, mem_ground, pair_sdiff_left, pair_sdiff_right, singleton_subset_iff
-/
lemma IsNonloop.closure_eq_closure_iff_isCircuit_of_ne (he : M.IsNonloop e) (hef : e != f) :
    M.closure {e} = M.closure {f} ↔ M.IsCircuit {e, f} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hf := he.isNonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [isCircuit_iff_dep_forall_sdiff_singleton_indep]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_right he.mem_ground]; rw [singleton_subset_iff]; rw [and_iff_left hf.mem_ground]
    suffices ¬ M.Indep {e, f} by simpa [pair_sdiff_left hef, hf, pair_sdiff_right hef, he]
    rw [Indep.insert_indep_iff_of_notMem (by simpa) (by simpa)]
    simp [← h, mem_closure_self _ _ he.mem_ground]
  have hclosure := (h.closure_sdiff_singleton_eq e).trans
    (h.closure_sdiff_singleton_eq f).symm
  rwa [pair_sdiff_left hef, pair_sdiff_right hef, eq_comm] at hclosure

/--
lemma `IsNonloop.closure_eq_closure_iff_eq_or_dep` / 引理 `IsNonloop.closure_eq_closure_iff_eq_or_dep`

English:
lemma IsNonloop.closure_eq_closure_iff_eq_or_dep
  given: (he : M.IsNonloop e) (hf : M.IsNonloop f)
  proof: by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_isCircuit_of_ne hne, or_iff_right hne,
    isCircuit_iff_dep_forall_sdiff_singleton_indep, dep_iff, insert_subset_iff,
    singleton_subset_iff, and_iff_left hf.mem_ground, and_iff_left he.mem_ground,
    and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_sdiff_left hne, indep_singleton]
  rwa [pair_sdiff_right hne, indep_singleton]

中文:
引理 是Nonloop.closure_eq_closure_iff_eq_or_dep
  条件: (he : M.是Nonloop e) (hf : M.是Nonloop f)
  证明: by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_isCircuit_of_ne hne, or_iff_right hne,
    isCircuit_iff_dep_forall_sdiff_singleton_indep, dep_iff, insert_subset_iff,
    singleton_subset_iff, and_iff_left hf.mem_ground, and_iff_left he.mem_ground,
    and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_sdiff_left hne, indep_singleton]
  rwa [pair_sdiff_right hne, indep_singleton]

Depends on / 依赖: Or.inl, and_iff_left, and_iff_left_iff_imp, closure_eq_closure_iff_isCircuit_of_ne, dep_iff, eq_or_ne, he.closure_eq_closure_iff_isCircuit_of_ne, he.mem_ground, hf.mem_ground, iff_of_true, indep_singleton, insert_subset_iff, isCircuit_iff_dep_forall_sdiff_singleton_indep, mem_ground, or_iff_right, pair_sdiff_left, pair_sdiff_right, simp_rw, singleton_subset_iff
-/
lemma IsNonloop.closure_eq_closure_iff_eq_or_dep (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_isCircuit_of_ne hne, or_iff_right hne,
    isCircuit_iff_dep_forall_sdiff_singleton_indep, dep_iff, insert_subset_iff,
    singleton_subset_iff, and_iff_left hf.mem_ground, and_iff_left he.mem_ground,
    and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_sdiff_left hne, indep_singleton]
  rwa [pair_sdiff_right hne, indep_singleton]

/--
lemma `exists_isNonloop` / 引理 `exists_isNonloop`

English:
lemma exists_isNonloop
  given: (M : Matroid α) [RankPos M]
  statement: exists e, M.IsNonloop e
  proof: let ⟨_, hB⟩ := M.exists_isBase
  ⟨_, hB.indep.isNonloop_of_mem hB.nonempty.some_mem⟩

中文:
引理 存在_isNonloop
  条件: (M : 拟阵 α) [RankPos M]
  结论: 存在 e, M.是Nonloop e
  证明: let ⟨_, hB⟩ := M.exists_isBase
  ⟨_, hB.indep.isNonloop_of_mem hB.nonempty.some_mem⟩

Depends on / 依赖: M.exists_isBase, exists_isBase, hB.indep.isNonloop_of_mem, hB.nonempty.some_mem, isNonloop_of_mem, nonempty, some_mem
-/
lemma exists_isNonloop (M : Matroid α) [RankPos M] : exists e, M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  ⟨_, hB.indep.isNonloop_of_mem hB.nonempty.some_mem⟩

/--
lemma `IsNonloop.rankPos` / 引理 `IsNonloop.rankPos`

English:
lemma IsNonloop.rankPos
  given: (h : M.IsNonloop e)
  statement: M.RankPos
  proof: h.indep.rankPos_of_nonempty (singleton_nonempty e)

@[simp]

中文:
引理 是Nonloop.rankPos
  条件: (h : M.是Nonloop e)
  结论: M.RankPos
  证明: h.indep.rankPos_of_nonempty (singleton_nonempty e)

@[simp]

Depends on / 依赖: h.indep.rankPos_of_nonempty, rankPos_of_nonempty, singleton_nonempty
-/
lemma IsNonloop.rankPos (h : M.IsNonloop e) : M.RankPos :=
  h.indep.rankPos_of_nonempty (singleton_nonempty e)

@[simp]
/--
lemma `restrict_isNonloop_iff` / 引理 `restrict_isNonloop_iff`

English:
lemma restrict_isNonloop_iff
  given: {R : Set α}
  statement: (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e in R
  proof: by
  rw [← indep_singleton]; rw [restrict_indep_iff]; rw [singleton_subset_iff]; rw [indep_singleton]

中文:
引理 restrict_isNonloop_iff
  条件: {R : 集合 α}
  结论: (M ↾ R).是Nonloop e ↔ M.是Nonloop e ∧ e in R
  证明: by
  rw [← indep_singleton]; rw [restrict_indep_iff]; rw [singleton_subset_iff]; rw [indep_singleton]

Depends on / 依赖: indep_singleton, restrict_indep_iff, singleton_subset_iff
-/
lemma restrict_isNonloop_iff {R : Set α} : (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e in R := by
  rw [← indep_singleton]; rw [restrict_indep_iff]; rw [singleton_subset_iff]; rw [indep_singleton]

/--
lemma `IsNonloop.of_restrict` / 引理 `IsNonloop.of_restrict`

English:
lemma IsNonloop.of_restrict
  given: {R : Set α} (h : (M ↾ R).IsNonloop e)
  statement: M.IsNonloop e
  proof: (restrict_isNonloop_iff.1 h).1

中文:
引理 是Nonloop.of_restrict
  条件: {R : 集合 α} (h : (M ↾ R).是Nonloop e)
  结论: M.是Nonloop e
  证明: (restrict_isNonloop_iff.1 h).1

Depends on / 依赖: restrict_isNonloop_iff
-/
lemma IsNonloop.of_restrict {R : Set α} (h : (M ↾ R).IsNonloop e) : M.IsNonloop e :=
  (restrict_isNonloop_iff.1 h).1

/--
lemma `IsNonloop.of_isRestriction` / 引理 `IsNonloop.of_isRestriction`

English:
lemma IsNonloop.of_isRestriction
  given: (h : N.IsNonloop e) (hNM : N <=r M)
  statement: M.IsNonloop e
  proof: by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

中文:
引理 是Nonloop.of_isRestriction
  条件: (h : N.是Nonloop e) (hNM : N <=r M)
  结论: M.是Nonloop e
  证明: by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

Depends on / 依赖: h.of_restrict, of_restrict
-/
lemma IsNonloop.of_isRestriction (h : N.IsNonloop e) (hNM : N <=r M) : M.IsNonloop e := by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

/--
lemma `isNonloop_iff_restrict_of_mem` / 引理 `isNonloop_iff_restrict_of_mem`

English:
lemma isNonloop_iff_restrict_of_mem
  given: {R : Set α} (he : e in R)
  proof: ⟨fun h => restrict_isNonloop_iff.2 ⟨h, he⟩, fun h => h.of_restrict⟩

@[simp]

中文:
引理 isNonloop_iff_restrict_of_mem
  条件: {R : 集合 α} (he : e in R)
  证明: ⟨fun h => restrict_isNonloop_iff.2 ⟨h, he⟩, fun h => h.of_restrict⟩

@[simp]

Depends on / 依赖: h.of_restrict, of_restrict, restrict_isNonloop_iff
-/
lemma isNonloop_iff_restrict_of_mem {R : Set α} (he : e in R) :
    M.IsNonloop e ↔ (M ↾ R).IsNonloop e :=
  ⟨fun h => restrict_isNonloop_iff.2 ⟨h, he⟩, fun h => h.of_restrict⟩

@[simp]
/--
lemma `comap_isNonloop_iff` / 引理 `comap_isNonloop_iff`

English:
lemma comap_isNonloop_iff
  given: {M : Matroid β} {f : α -> β}
  proof: by
  rw [← indep_singleton]; rw [comap_indep_iff]; rw [image_singleton]; rw [indep_singleton]; rw [and_iff_left (injOn_singleton _ _)]

@[simp]

中文:
引理 comap_isNonloop_iff
  条件: {M : 拟阵 β} {f : α -> β}
  证明: by
  rw [← indep_singleton]; rw [comap_indep_iff]; rw [image_singleton]; rw [indep_singleton]; rw [and_iff_left (injOn_singleton _ _)]

@[simp]

Depends on / 依赖: and_iff_left, comap_indep_iff, image_singleton, indep_singleton, injOn_singleton
-/
lemma comap_isNonloop_iff {M : Matroid β} {f : α -> β} :
    (M.comap f).IsNonloop e ↔ M.IsNonloop (f e) := by
  rw [← indep_singleton]; rw [comap_indep_iff]; rw [image_singleton]; rw [indep_singleton]; rw [and_iff_left (injOn_singleton _ _)]

@[simp]
/--
lemma `freeOn_isNonloop_iff` / 引理 `freeOn_isNonloop_iff`

English:
lemma freeOn_isNonloop_iff
  given: {E : Set α}
  statement: (freeOn E).IsNonloop e ↔ e in E
  proof: by
  rw [← indep_singleton]; rw [freeOn_indep_iff]; rw [singleton_subset_iff]

@[simp]

中文:
引理 freeOn_isNonloop_iff
  条件: {E : 集合 α}
  结论: (freeOn E).是Nonloop e ↔ e in E
  证明: by
  rw [← indep_singleton]; rw [freeOn_indep_iff]; rw [singleton_subset_iff]

@[simp]

Depends on / 依赖: freeOn_indep_iff, indep_singleton, singleton_subset_iff
-/
lemma freeOn_isNonloop_iff {E : Set α} : (freeOn E).IsNonloop e ↔ e in E := by
  rw [← indep_singleton]; rw [freeOn_indep_iff]; rw [singleton_subset_iff]

@[simp]
/--
lemma `uniqueBaseOn_isNonloop_iff` / 引理 `uniqueBaseOn_isNonloop_iff`

English:
lemma uniqueBaseOn_isNonloop_iff
  given: {I E : Set α}
  proof: by
  rw [← indep_singleton]; rw [uniqueBaseOn_indep_iff']; rw [singleton_subset_iff]

中文:
引理 uniqueBaseOn_isNonloop_iff
  条件: {I E : 集合 α}
  证明: by
  rw [← indep_singleton]; rw [uniqueBaseOn_indep_iff']; rw [singleton_subset_iff]

Depends on / 依赖: indep_singleton, singleton_subset_iff, uniqueBaseOn_indep_iff
-/
lemma uniqueBaseOn_isNonloop_iff {I E : Set α} :
    (uniqueBaseOn I E).IsNonloop e ↔ e in I inter E := by
  rw [← indep_singleton]; rw [uniqueBaseOn_indep_iff']; rw [singleton_subset_iff]

/--
lemma `IsNonloop.exists_mem_isCocircuit` / 引理 `IsNonloop.exists_mem_isCocircuit`

English:
lemma IsNonloop.exists_mem_isCocircuit
  given: (he : M.IsNonloop e)
  statement: exists K, M.IsCocircuit K ∧ e in K
  proof: by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]

中文:
引理 是Nonloop.存在_mem_isCocircuit
  条件: (he : M.是Nonloop e)
  结论: 存在 K, M.IsCocircuit K ∧ e in K
  证明: by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]

Depends on / 依赖: exists_mem_isBase, fundCocircuit_isCocircuit, he.exists_mem_isBase, mem_fundCocircuit
-/
lemma IsNonloop.exists_mem_isCocircuit (he : M.IsNonloop e) : exists K, M.IsCocircuit K ∧ e in K := by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]
/--
lemma `closure_inter_setOfPred_isNonloop_eq` / 引理 `closure_inter_setOfPred_isNonloop_eq`

English:
lemma closure_inter_setOfPred_isNonloop_eq
  given: (M : Matroid α) (X : Set α)
  proof: by
  rw [setOfPred_isNonloop_eq]; rw [← inter_sdiff_assoc]; rw [closure_sdiff_loops_eq]; rw [closure_inter_ground]

@[deprecated (since := "2026-07-09")]
alias closure_inter_setOf_isNonloop_eq := closure_inter_setOfPred_isNonloop_eq

中文:
引理 closure_inter_setOfPred_isNonloop_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  rw [setOfPred_isNonloop_eq]; rw [← inter_sdiff_assoc]; rw [closure_sdiff_loops_eq]; rw [closure_inter_ground]

@[deprecated (since := "2026-07-09")]
alias closure_inter_setOf_isNonloop_eq := closure_inter_setOfPred_isNonloop_eq

Depends on / 依赖: closure_inter_ground, closure_sdiff_loops_eq, inter_sdiff_assoc, setOfPred_isNonloop_eq
-/
lemma closure_inter_setOfPred_isNonloop_eq (M : Matroid α) (X : Set α) :
    M.closure (X inter {e | M.IsNonloop e}) = M.closure X := by
  rw [setOfPred_isNonloop_eq]; rw [← inter_sdiff_assoc]; rw [closure_sdiff_loops_eq]; rw [closure_inter_ground]

@[deprecated (since := "2026-07-09")]
alias closure_inter_setOf_isNonloop_eq := closure_inter_setOfPred_isNonloop_eq

end IsNonloop

section IsColoop

variable {B K : Set α}

/--
Definition of `IsColoop` / `IsColoop` 的定义

English:
definition IsColoop
  signature: (M : Matroid α) (e : α)
  body: M✶.IsLoop e

中文:
定义 IsColoop
  签名: (M : 拟阵 α) (e : α)
  定义体: M✶.IsLoop e

Depends on / 依赖: IsLoop
-/
def IsColoop (M : Matroid α) (e : α) : Prop := M✶.IsLoop e

/--
Definition of `coloops` / `coloops` 的定义

English:
definition coloops
  signature: (M : Matroid α)
  body: M✶.loops

@[aesop unsafe 20% (rule_sets := [Matroid])]

中文:
定义 coloops
  签名: (M : 拟阵 α)
  定义体: M✶.loops

@[aesop unsafe 20% (rule_sets := [Matroid])]
-/
def coloops (M : Matroid α) := M✶.loops

@[aesop unsafe 20% (rule_sets := [Matroid])]
/--
lemma `IsColoop.mem_ground` / 引理 `IsColoop.mem_ground`

English:
lemma IsColoop.mem_ground
  given: (he : M.IsColoop e)
  statement: e in M.E
  proof: @IsLoop.mem_ground α (M✶) e he

@[aesop unsafe 20% (rule_sets := [Matroid])]

中文:
引理 IsColoop.mem_ground
  条件: (he : M.IsColoop e)
  结论: e in M.E
  证明: @IsLoop.mem_ground α (M✶) e he

@[aesop unsafe 20% (rule_sets := [Matroid])]

Depends on / 依赖: IsLoop, IsLoop.mem_ground, mem_ground
-/
lemma IsColoop.mem_ground (he : M.IsColoop e) : e in M.E :=
  @IsLoop.mem_ground α (M✶) e he

@[aesop unsafe 20% (rule_sets := [Matroid])]
/--
lemma `coloops_subset_ground` / 引理 `coloops_subset_ground`

English:
lemma coloops_subset_ground
  given: (M : Matroid α)
  statement: M.coloops subseteq M.E
  proof: fun _ => IsColoop.mem_ground

中文:
引理 coloops_subset_ground
  条件: (M : 拟阵 α)
  结论: M.coloops subseteq M.E
  证明: fun _ => IsColoop.mem_ground

Depends on / 依赖: IsColoop, IsColoop.mem_ground, mem_ground
-/
lemma coloops_subset_ground (M : Matroid α) : M.coloops subseteq M.E :=
  fun _ => IsColoop.mem_ground

/--
lemma `isColoop_iff_mem_coloops` / 引理 `isColoop_iff_mem_coloops`

English:
lemma isColoop_iff_mem_coloops
  statement: M.IsColoop e ↔ e in M.coloops
  proof: Iff.rfl

@[simp]

中文:
引理 isColoop_iff_mem_coloops
  结论: M.IsColoop e ↔ e in M.coloops
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma isColoop_iff_mem_coloops : M.IsColoop e ↔ e in M.coloops := Iff.rfl

@[simp]
/--
lemma `dual_loops` / 引理 `dual_loops`

English:
lemma dual_loops
  statement: M✶.loops = M.coloops
  proof: rfl

@[simp]

中文:
引理 dual_loops
  结论: M✶.loops = M.coloops
  证明: rfl

@[simp]
-/
lemma dual_loops : M✶.loops = M.coloops := rfl

@[simp]
/--
lemma `dual_coloops` / 引理 `dual_coloops`

English:
lemma dual_coloops
  statement: M✶.coloops = M.loops
  proof: by
  rw [coloops]; rw [dual_dual]

中文:
引理 dual_coloops
  结论: M✶.coloops = M.loops
  证明: by
  rw [coloops]; rw [dual_dual]

Depends on / 依赖: coloops, dual_dual
-/
lemma dual_coloops : M✶.coloops = M.loops := by
  rw [coloops]; rw [dual_dual]

/--
lemma `IsColoop.dual_isLoop` / 引理 `IsColoop.dual_isLoop`

English:
lemma IsColoop.dual_isLoop
  given: (he : M.IsColoop e)
  statement: M✶.IsLoop e
  proof: he

中文:
引理 IsColoop.dual_isLoop
  条件: (he : M.IsColoop e)
  结论: M✶.IsLoop e
  证明: he
-/
lemma IsColoop.dual_isLoop (he : M.IsColoop e) : M✶.IsLoop e :=
  he

/--
lemma `IsColoop.isCocircuit` / 引理 `IsColoop.isCocircuit`

English:
lemma IsColoop.isCocircuit
  given: (he : M.IsColoop e)
  statement: M.IsCocircuit {e}
  proof: IsLoop.isCircuit he

中文:
引理 IsColoop.isCocircuit
  条件: (he : M.IsColoop e)
  结论: M.IsCocircuit {e}
  证明: IsLoop.isCircuit he

Depends on / 依赖: IsLoop, IsLoop.isCircuit, isCircuit
-/
lemma IsColoop.isCocircuit (he : M.IsColoop e) : M.IsCocircuit {e} :=
  IsLoop.isCircuit he

/--
lemma `IsLoop.dual_isColoop` / 引理 `IsLoop.dual_isColoop`

English:
lemma IsLoop.dual_isColoop
  given: (he : M.IsLoop e)
  statement: M✶.IsColoop e
  proof: by rwa [IsColoop, dual_dual]

@[simp]

中文:
引理 IsLoop.dual_isColoop
  条件: (he : M.IsLoop e)
  结论: M✶.IsColoop e
  证明: by rwa [IsColoop, dual_dual]

@[simp]

Depends on / 依赖: IsColoop, dual_dual
-/
lemma IsLoop.dual_isColoop (he : M.IsLoop e) : M✶.IsColoop e := by rwa [IsColoop, dual_dual]

@[simp]
/--
lemma `dual_isColoop_iff_isLoop` / 引理 `dual_isColoop_iff_isLoop`

English:
lemma dual_isColoop_iff_isLoop
  statement: M✶.IsColoop e ↔ M.IsLoop e
  proof: ⟨fun h => by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_isColoop⟩

@[simp]

中文:
引理 dual_isColoop_iff_isLoop
  结论: M✶.IsColoop e ↔ M.IsLoop e
  证明: ⟨fun h => by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_isColoop⟩

@[simp]

Depends on / 依赖: IsLoop, IsLoop.dual_isColoop, dual_dual, dual_isColoop, dual_isLoop, h.dual_isLoop
-/
lemma dual_isColoop_iff_isLoop : M✶.IsColoop e ↔ M.IsLoop e :=
  ⟨fun h => by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_isColoop⟩

@[simp]
/--
lemma `dual_isLoop_iff_isColoop` / 引理 `dual_isLoop_iff_isColoop`

English:
lemma dual_isLoop_iff_isColoop
  statement: M✶.IsLoop e ↔ M.IsColoop e
  proof: ⟨fun h => by rw [← dual_dual M]; exact h.dual_isColoop, IsColoop.dual_isLoop⟩

中文:
引理 dual_isLoop_iff_isColoop
  结论: M✶.IsLoop e ↔ M.IsColoop e
  证明: ⟨fun h => by rw [← dual_dual M]; exact h.dual_isColoop, IsColoop.dual_isLoop⟩

Depends on / 依赖: IsColoop, IsColoop.dual_isLoop, dual_dual, dual_isColoop, dual_isLoop, h.dual_isColoop
-/
lemma dual_isLoop_iff_isColoop : M✶.IsLoop e ↔ M.IsColoop e :=
  ⟨fun h => by rw [← dual_dual M]; exact h.dual_isColoop, IsColoop.dual_isLoop⟩

/--
lemma `singleton_isCocircuit` / 引理 `singleton_isCocircuit`

English:
lemma singleton_isCocircuit
  statement: M.IsCocircuit {e} ↔ M.IsColoop e
  proof: by
  simp

中文:
引理 singleton_isCocircuit
  结论: M.IsCocircuit {e} ↔ M.IsColoop e
  证明: by
  simp
-/
lemma singleton_isCocircuit : M.IsCocircuit {e} ↔ M.IsColoop e := by
  simp

/--
lemma `isColoop_tfae` / 引理 `isColoop_tfae`

English:
lemma isColoop_tfae
  given: (M : Matroid α) (e : α)
  statement: List.TFAE [
  proof: by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 1 ↔ 3 := singleton_isCocircuit.symm
  tfae_have 1 ↔ 4 := by
    simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase]
    refine ⟨fun h B hB => ?_, fun h B hB => h hB.compl_isBase_of_dual⟩
    obtain ⟨-, heB : e in B⟩ := by simpa using h (M.E \ B) hB.compl_isBase_dual
    assumption
  tfae_have 3 -> 5 := fun h =>
    ⟨fun C hC heC => hC.inter_isCocircuit_ne_singleton h (e := e) (by simpa), h.subset_ground rfl⟩
  tfae_have 5 -> 4 := by
    refine fun ⟨h, heE⟩ B hB => by_contra fun heB => ?_
    rw [← hB.closure_eq] at heE
    obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heB).1 heE
    exact h hC heC
  tfae_have 5 ↔ 6 := by
    refine ⟨fun h X => ⟨fun heX => by_contra fun heX' => ?_, fun heX => M.mem_closure_of_mem' heX h.2⟩,
fun h => ⟨fun C hC heC => ?_, M.closure_subset_ground _ (h {e}).2 rfl⟩⟩
    · obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heX').1 heX
      exact h.1 hC heC
    · simpa [hC.mem_closure_sdiff_singleton_of_mem heC] using h (C \ {e})
  tfae_have 1 ↔ 7 := by
    wlog he : e in M.E
· exact iff_of_false (fun h => he h.mem_ground) by simp [he, M.ground_spanning]
    rw [spanning_iff_compl_coindep sdiff_subset]; rw [← dual_isLoop_iff_isColoop]; rw [← singleton_dep]; rw [sdiff_sdiff_cancel_left (by simpa)]; rw [← not_indep_iff (by simpa)]
  tfae_finish

中文:
引理 isColoop_tfae
  条件: (M : 拟阵 α) (e : α)
  结论: 列表.TFAE [
  证明: by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 1 ↔ 3 := singleton_isCocircuit.symm
  tfae_have 1 ↔ 4 := by
    simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase]
    refine ⟨fun h B hB => ?_, fun h B hB => h hB.compl_isBase_of_dual⟩
    obtain ⟨-, heB : e in B⟩ := by simpa using h (M.E \ B) hB.compl_isBase_dual
    assumption
  tfae_have 3 -> 5 := fun h =>
    ⟨fun C hC heC => hC.inter_isCocircuit_ne_singleton h (e := e) (by simpa), h.subset_ground rfl⟩
  tfae_have 5 -> 4 := by
    refine fun ⟨h, heE⟩ B hB => by_contra fun heB => ?_
    rw [← hB.closure_eq] at heE
    obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heB).1 heE
    exact h hC heC
  tfae_have 5 ↔ 6 := by
    refine ⟨fun h X => ⟨fun heX => by_contra fun heX' => ?_, fun heX => M.mem_closure_of_mem' heX h.2⟩,
fun h => ⟨fun C hC heC => ?_, M.closure_subset_ground _ (h {e}).2 rfl⟩⟩
    · obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heX').1 heX
      exact h.1 hC heC
    · simpa [hC.mem_closure_sdiff_singleton_of_mem heC] using h (C \ {e})
  tfae_have 1 ↔ 7 := by
    wlog he : e in M.E
· exact iff_of_false (fun h => he h.mem_ground) by simp [he, M.ground_spanning]
    rw [spanning_iff_compl_coindep sdiff_subset]; rw [← dual_isLoop_iff_isColoop]; rw [← singleton_dep]; rw [sdiff_sdiff_cancel_left (by simpa)]; rw [← not_indep_iff (by simpa)]
  tfae_finish

Depends on / 依赖: Iff.rfl, compl_isBase_dual, compl_isBase_of_dual, dual_isLoop_iff_isColoop, h.subset_ground, hB.compl_isBase_dual, hB.compl_isBase_of_dual, hC.inter_isCocircuit_ne_singleton, inter_isCocircuit_ne_singleton, isLoop_iff_forall_mem_compl_isBase, simp_rw, singleton_isCocircuit, singleton_isCocircuit.symm, subset_ground, tfae_have
-/
lemma isColoop_tfae (M : Matroid α) (e : α) : List.TFAE [
    M.IsColoop e,
    e in M.coloops,
    M.IsCocircuit {e},
    forall ⦃B⦄, M.IsBase B -> e in B,
    (forall ⦃C⦄, M.IsCircuit C -> e ∉ C) ∧ e in M.E,
    forall X, e in M.closure X ↔ e in X,
    ¬ M.Spanning (M.E \ {e}) ] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 1 ↔ 3 := singleton_isCocircuit.symm
  tfae_have 1 ↔ 4 := by
    simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase]
    refine ⟨fun h B hB => ?_, fun h B hB => h hB.compl_isBase_of_dual⟩
    obtain ⟨-, heB : e in B⟩ := by simpa using h (M.E \ B) hB.compl_isBase_dual
    assumption
  tfae_have 3 -> 5 := fun h =>
    ⟨fun C hC heC => hC.inter_isCocircuit_ne_singleton h (e := e) (by simpa), h.subset_ground rfl⟩
  tfae_have 5 -> 4 := by
    refine fun ⟨h, heE⟩ B hB => by_contra fun heB => ?_
    rw [← hB.closure_eq] at heE
    obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heB).1 heE
    exact h hC heC
  tfae_have 5 ↔ 6 := by
    refine ⟨fun h X => ⟨fun heX => by_contra fun heX' => ?_, fun heX => M.mem_closure_of_mem' heX h.2⟩,
fun h => ⟨fun C hC heC => ?_, M.closure_subset_ground _ (h {e}).2 rfl⟩⟩
    · obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heX').1 heX
      exact h.1 hC heC
    · simpa [hC.mem_closure_sdiff_singleton_of_mem heC] using h (C \ {e})
  tfae_have 1 ↔ 7 := by
    wlog he : e in M.E
· exact iff_of_false (fun h => he h.mem_ground) by simp [he, M.ground_spanning]
    rw [spanning_iff_compl_coindep sdiff_subset]; rw [← dual_isLoop_iff_isColoop]; rw [← singleton_dep]; rw [sdiff_sdiff_cancel_left (by simpa)]; rw [← not_indep_iff (by simpa)]
  tfae_finish

/--
lemma `isColoop_iff_forall_mem_isBase` / 引理 `isColoop_iff_forall_mem_isBase`

English:
lemma isColoop_iff_forall_mem_isBase
  statement: M.IsColoop e ↔ forall ⦃B⦄, M.IsBase B -> e in B
  proof: (M.isColoop_tfae e).out 0 3

中文:
引理 isColoop_iff_对任意_mem_isBase
  结论: M.IsColoop e ↔ 对任意 ⦃B⦄, M.IsBase B -> e in B
  证明: (M.isColoop_tfae e).out 0 3

Depends on / 依赖: M.isColoop_tfae, isColoop_tfae
-/
lemma isColoop_iff_forall_mem_isBase : M.IsColoop e ↔ forall ⦃B⦄, M.IsBase B -> e in B :=
  (M.isColoop_tfae e).out 0 3

/--
lemma `IsBase.mem_of_isColoop` / 引理 `IsBase.mem_of_isColoop`

English:
lemma IsBase.mem_of_isColoop
  given: (hB : M.IsBase B) (he : M.IsColoop e)
  statement: e in B
  proof: isColoop_iff_forall_mem_isBase.mp he hB

中文:
引理 IsBase.mem_of_isColoop
  条件: (hB : M.IsBase B) (he : M.IsColoop e)
  结论: e in B
  证明: isColoop_iff_forall_mem_isBase.mp he hB

Depends on / 依赖: isColoop_iff_forall_mem_isBase, isColoop_iff_forall_mem_isBase.mp
-/
lemma IsBase.mem_of_isColoop (hB : M.IsBase B) (he : M.IsColoop e) : e in B :=
  isColoop_iff_forall_mem_isBase.mp he hB

/--
lemma `IsColoop.mem_of_isBase` / 引理 `IsColoop.mem_of_isBase`

English:
lemma IsColoop.mem_of_isBase
  given: (he : M.IsColoop e) (hB : M.IsBase B)
  statement: e in B
  proof: isColoop_iff_forall_mem_isBase.mp he hB

中文:
引理 IsColoop.mem_of_isBase
  条件: (he : M.IsColoop e) (hB : M.IsBase B)
  结论: e in B
  证明: isColoop_iff_forall_mem_isBase.mp he hB

Depends on / 依赖: isColoop_iff_forall_mem_isBase, isColoop_iff_forall_mem_isBase.mp
-/
lemma IsColoop.mem_of_isBase (he : M.IsColoop e) (hB : M.IsBase B) : e in B :=
  isColoop_iff_forall_mem_isBase.mp he hB

/--
lemma `IsBase.coloops_subset` / 引理 `IsBase.coloops_subset`

English:
lemma IsBase.coloops_subset
  given: (hB : M.IsBase B)
  statement: M.coloops subseteq B
  proof: fun _ he => IsColoop.mem_of_isBase he hB

中文:
引理 IsBase.coloops_subset
  条件: (hB : M.IsBase B)
  结论: M.coloops subseteq B
  证明: fun _ he => IsColoop.mem_of_isBase he hB

Depends on / 依赖: IsColoop, IsColoop.mem_of_isBase, mem_of_isBase
-/
lemma IsBase.coloops_subset (hB : M.IsBase B) : M.coloops subseteq B :=
  fun _ he => IsColoop.mem_of_isBase he hB

/--
lemma `IsColoop.isNonloop` / 引理 `IsColoop.isNonloop`

English:
lemma IsColoop.isNonloop
  given: (h : M.IsColoop e)
  statement: M.IsNonloop e
  proof: let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((isColoop_iff_forall_mem_isBase.mp h) hB)

中文:
引理 IsColoop.isNonloop
  条件: (h : M.IsColoop e)
  结论: M.是Nonloop e
  证明: let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((isColoop_iff_forall_mem_isBase.mp h) hB)

Depends on / 依赖: M.exists_isBase, exists_isBase, hB.indep.isNonloop_of_mem, isColoop_iff_forall_mem_isBase, isColoop_iff_forall_mem_isBase.mp, isNonloop_of_mem
-/
lemma IsColoop.isNonloop (h : M.IsColoop e) : M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((isColoop_iff_forall_mem_isBase.mp h) hB)

/--
lemma `IsLoop.not_isColoop` / 引理 `IsLoop.not_isColoop`

English:
lemma IsLoop.not_isColoop
  given: (h : M.IsLoop e)
  statement: ¬M.IsColoop e
  proof: by
  rw [← dual_isLoop_iff_isColoop]; rw [← dual_dual M, dual_isLoop_iff_isColoop] at h
  exact h.isNonloop.not_isLoop

中文:
引理 IsLoop.not_isColoop
  条件: (h : M.IsLoop e)
  结论: ¬M.IsColoop e
  证明: by
  rw [← dual_isLoop_iff_isColoop]; rw [← dual_dual M, dual_isLoop_iff_isColoop] at h
  exact h.isNonloop.not_isLoop

Depends on / 依赖: dual_dual, dual_isLoop_iff_isColoop, h.isNonloop.not_isLoop, isNonloop, not_isLoop
-/
lemma IsLoop.not_isColoop (h : M.IsLoop e) : ¬M.IsColoop e := by
  rw [← dual_isLoop_iff_isColoop]; rw [← dual_dual M, dual_isLoop_iff_isColoop] at h
  exact h.isNonloop.not_isLoop

/--
lemma `IsColoop.notMem_isCircuit` / 引理 `IsColoop.notMem_isCircuit`

English:
lemma IsColoop.notMem_isCircuit
  given: (he : M.IsColoop e) (hC : M.IsCircuit C)
  statement: e ∉ C
  proof: fun h => (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he

中文:
引理 IsColoop.notMem_isCircuit
  条件: (he : M.IsColoop e) (hC : M.是Circuit C)
  结论: e ∉ C
  证明: fun h => (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he

Depends on / 依赖: hC.isCocircuit.isNonloop_of_mem, isCocircuit, isNonloop_of_mem, not_isLoop
-/
lemma IsColoop.notMem_isCircuit (he : M.IsColoop e) (hC : M.IsCircuit C) : e ∉ C :=
  fun h => (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he

/--
lemma `IsCircuit.disjoint_coloops` / 引理 `IsCircuit.disjoint_coloops`

English:
lemma IsCircuit.disjoint_coloops
  given: (hC : M.IsCircuit C)
  statement: Disjoint C M.coloops
  proof: disjoint_right.2 fun _ he => IsColoop.notMem_isCircuit he hC

中文:
引理 是Circuit.disjoint_coloops
  条件: (hC : M.是Circuit C)
  结论: Disjoint C M.coloops
  证明: disjoint_right.2 fun _ he => IsColoop.notMem_isCircuit he hC

Depends on / 依赖: IsColoop, IsColoop.notMem_isCircuit, disjoint_right, notMem_isCircuit
-/
lemma IsCircuit.disjoint_coloops (hC : M.IsCircuit C) : Disjoint C M.coloops :=
disjoint_right.2 fun _ he => IsColoop.notMem_isCircuit he hC

/--
lemma `isColoop_iff_forall_notMem_isCircuit` / 引理 `isColoop_iff_forall_notMem_isCircuit`

English:
lemma isColoop_iff_forall_notMem_isCircuit
  given: (he : e in M.E := by aesop_mat)
  proof: by
  simp_rw [(M.isColoop_tfae e).out 0 4, and_iff_left he]

中文:
引理 isColoop_iff_对任意_notMem_isCircuit
  条件: (he : e in M.E := by aesop_mat)
  证明: by
  simp_rw [(M.isColoop_tfae e).out 0 4, and_iff_left he]

Depends on / 依赖: IsCircuit, IsColoop, M.IsCircuit, M.IsColoop, M.isColoop_tfae, aesop_mat, and_iff_left, isColoop_tfae, simp_rw
-/
lemma isColoop_iff_forall_notMem_isCircuit (he : e in M.E := by aesop_mat) :
    M.IsColoop e ↔ forall ⦃C⦄, M.IsCircuit C -> e ∉ C := by
  simp_rw [(M.isColoop_tfae e).out 0 4, and_iff_left he]

/--
lemma `isColoop_iff_forall_mem_compl_isCircuit` / 引理 `isColoop_iff_forall_mem_compl_isCircuit`

English:
lemma isColoop_iff_forall_mem_compl_isCircuit
  given: [RankPos M✶]
  proof: by
  by_cases he : e in M.E
  · simp [isColoop_iff_forall_notMem_isCircuit, he]
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  exact iff_of_false (fun h => he h.mem_ground) fun h => he (h C hC).1

中文:
引理 isColoop_iff_对任意_mem_compl_isCircuit
  条件: [RankPos M✶]
  证明: by
  by_cases he : e in M.E
  · simp [isColoop_iff_forall_notMem_isCircuit, he]
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  exact iff_of_false (fun h => he h.mem_ground) fun h => he (h C hC).1

Depends on / 依赖: M.exists_isCircuit, exists_isCircuit, h.mem_ground, iff_of_false, isColoop_iff_forall_notMem_isCircuit, mem_ground
-/
lemma isColoop_iff_forall_mem_compl_isCircuit [RankPos M✶] :
    M.IsColoop e ↔ forall C, M.IsCircuit C -> e in M.E \ C := by
  by_cases he : e in M.E
  · simp [isColoop_iff_forall_notMem_isCircuit, he]
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  exact iff_of_false (fun h => he h.mem_ground) fun h => he (h C hC).1

/--
lemma `IsCircuit.not_isColoop_of_mem` / 引理 `IsCircuit.not_isColoop_of_mem`

English:
lemma IsCircuit.not_isColoop_of_mem
  given: (hC : M.IsCircuit C) (heC : e in C)
  statement: ¬ M.IsColoop e
  proof: fun h => h.notMem_isCircuit hC heC

中文:
引理 是Circuit.not_isColoop_of_mem
  条件: (hC : M.是Circuit C) (heC : e in C)
  结论: ¬ M.IsColoop e
  证明: fun h => h.notMem_isCircuit hC heC

Depends on / 依赖: h.notMem_isCircuit, notMem_isCircuit
-/
lemma IsCircuit.not_isColoop_of_mem (hC : M.IsCircuit C) (heC : e in C) : ¬ M.IsColoop e :=
  fun h => h.notMem_isCircuit hC heC

/--
lemma `isColoop_iff_forall_mem_closure_iff_mem` / 引理 `isColoop_iff_forall_mem_closure_iff_mem`

English:
lemma isColoop_iff_forall_mem_closure_iff_mem
  statement: M.IsColoop e ↔ (forall X, e in M.closure X ↔ e in X)
  proof: (M.isColoop_tfae e).out 0 5

中文:
引理 isColoop_iff_对任意_mem_closure_iff_mem
  结论: M.IsColoop e ↔ (对任意 X, e in M.closure X ↔ e in X)
  证明: (M.isColoop_tfae e).out 0 5

Depends on / 依赖: M.isColoop_tfae, isColoop_tfae
-/
lemma isColoop_iff_forall_mem_closure_iff_mem : M.IsColoop e ↔ (forall X, e in M.closure X ↔ e in X) :=
  (M.isColoop_tfae e).out 0 5

/--
lemma `isColoop_iff_forall_mem_closure_iff_mem'` / 引理 `isColoop_iff_forall_mem_closure_iff_mem'`

English:
lemma isColoop_iff_forall_mem_closure_iff_mem'
  proof: by
  refine ⟨fun h => ⟨fun X _ => isColoop_iff_forall_mem_closure_iff_mem.1 h X, h.mem_ground⟩,
    fun ⟨h, he⟩ => isColoop_iff_forall_mem_closure_iff_mem.2 fun X => ?_⟩
  rw [← closure_inter_ground]; rw [h _ inter_subset_right]; rw [mem_inter_iff]; rw [and_iff_left he]

中文:
引理 isColoop_iff_对任意_mem_closure_iff_mem'
  证明: by
  refine ⟨fun h => ⟨fun X _ => isColoop_iff_forall_mem_closure_iff_mem.1 h X, h.mem_ground⟩,
    fun ⟨h, he⟩ => isColoop_iff_forall_mem_closure_iff_mem.2 fun X => ?_⟩
  rw [← closure_inter_ground]; rw [h _ inter_subset_right]; rw [mem_inter_iff]; rw [and_iff_left he]

Depends on / 依赖: and_iff_left, closure_inter_ground, h.mem_ground, inter_subset_right, isColoop_iff_forall_mem_closure_iff_mem, mem_ground, mem_inter_iff
-/
lemma isColoop_iff_forall_mem_closure_iff_mem' :
    M.IsColoop e ↔ (forall X, X subseteq M.E -> (e in M.closure X ↔ e in X)) ∧ e in M.E := by
  refine ⟨fun h => ⟨fun X _ => isColoop_iff_forall_mem_closure_iff_mem.1 h X, h.mem_ground⟩,
    fun ⟨h, he⟩ => isColoop_iff_forall_mem_closure_iff_mem.2 fun X => ?_⟩
  rw [← closure_inter_ground]; rw [h _ inter_subset_right]; rw [mem_inter_iff]; rw [and_iff_left he]

/--
lemma `IsColoop.mem_closure_iff_mem` / 引理 `IsColoop.mem_closure_iff_mem`

English:
lemma IsColoop.mem_closure_iff_mem
  given: (he : M.IsColoop e)
  statement: e in M.closure X ↔ e in X
  proof: (isColoop_iff_forall_mem_closure_iff_mem.1 he) X

中文:
引理 IsColoop.mem_closure_iff_mem
  条件: (he : M.IsColoop e)
  结论: e in M.closure X ↔ e in X
  证明: (isColoop_iff_forall_mem_closure_iff_mem.1 he) X

Depends on / 依赖: isColoop_iff_forall_mem_closure_iff_mem
-/
lemma IsColoop.mem_closure_iff_mem (he : M.IsColoop e) : e in M.closure X ↔ e in X :=
  (isColoop_iff_forall_mem_closure_iff_mem.1 he) X

/--
lemma `IsColoop.mem_of_mem_closure` / 引理 `IsColoop.mem_of_mem_closure`

English:
lemma IsColoop.mem_of_mem_closure
  given: (he : M.IsColoop e) (heX : e in M.closure X)
  statement: e in X
  proof: he.mem_closure_iff_mem.1 heX

中文:
引理 IsColoop.mem_of_mem_closure
  条件: (he : M.IsColoop e) (heX : e in M.closure X)
  结论: e in X
  证明: he.mem_closure_iff_mem.1 heX

Depends on / 依赖: he.mem_closure_iff_mem, mem_closure_iff_mem
-/
lemma IsColoop.mem_of_mem_closure (he : M.IsColoop e) (heX : e in M.closure X) : e in X :=
  he.mem_closure_iff_mem.1 heX

/--
lemma `isColoop_iff_sdiff_not_spanning` / 引理 `isColoop_iff_sdiff_not_spanning`

English:
lemma isColoop_iff_sdiff_not_spanning
  statement: M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e})
  proof: (M.isColoop_tfae e).out 0 6

@[deprecated (since := "2026-06-03")]
alias isColoop_iff_diff_not_spanning := isColoop_iff_sdiff_not_spanning

alias ⟨IsColoop.sdiff_not_spanning, _⟩ := isColoop_iff_sdiff_not_spanning

中文:
引理 isColoop_iff_sdiff_not_spanning
  结论: M.IsColoop e ↔ ¬ M.生成 (M.E \ {e})
  证明: (M.isColoop_tfae e).out 0 6

@[deprecated (since := "2026-06-03")]
alias isColoop_iff_diff_not_spanning := isColoop_iff_sdiff_not_spanning

alias ⟨IsColoop.sdiff_not_spanning, _⟩ := isColoop_iff_sdiff_not_spanning

Depends on / 依赖: M.isColoop_tfae, isColoop_tfae
-/
lemma isColoop_iff_sdiff_not_spanning : M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e}) :=
  (M.isColoop_tfae e).out 0 6

@[deprecated (since := "2026-06-03")]
alias isColoop_iff_diff_not_spanning := isColoop_iff_sdiff_not_spanning

alias ⟨IsColoop.sdiff_not_spanning, _⟩ := isColoop_iff_sdiff_not_spanning

/--
lemma `isColoop_iff_sdiff_closure` / 引理 `isColoop_iff_sdiff_closure`

English:
lemma isColoop_iff_sdiff_closure
  statement: M.IsColoop e ↔ M.closure (M.E \ {e}) != M.E
  proof: by
  rw [isColoop_iff_sdiff_not_spanning]; rw [spanning_iff_closure_eq]

@[deprecated (since := "2026-06-03")] alias isColoop_iff_diff_closure := isColoop_iff_sdiff_closure

中文:
引理 isColoop_iff_sdiff_closure
  结论: M.IsColoop e ↔ M.closure (M.E \ {e}) != M.E
  证明: by
  rw [isColoop_iff_sdiff_not_spanning]; rw [spanning_iff_closure_eq]

@[deprecated (since := "2026-06-03")] alias isColoop_iff_diff_closure := isColoop_iff_sdiff_closure

Depends on / 依赖: isColoop_iff_sdiff_not_spanning, spanning_iff_closure_eq
-/
lemma isColoop_iff_sdiff_closure : M.IsColoop e ↔ M.closure (M.E \ {e}) != M.E := by
  rw [isColoop_iff_sdiff_not_spanning]; rw [spanning_iff_closure_eq]

@[deprecated (since := "2026-06-03")] alias isColoop_iff_diff_closure := isColoop_iff_sdiff_closure

/--
lemma `isColoop_iff_notMem_closure_compl` / 引理 `isColoop_iff_notMem_closure_compl`

English:
lemma isColoop_iff_notMem_closure_compl
  given: (he : e in M.E := by aesop_mat)
  proof: by
  rw [isColoop_iff_sdiff_closure]; rw [not_iff_not]
  refine ⟨fun h => by rwa [h], fun h => (M.closure_subset_ground _).antisymm fun x hx => ?_⟩
  obtain (rfl | hne) := eq_or_ne x e
  · assumption
  exact M.subset_closure (M.E \ {e}) sdiff_subset (show x in M.E \ {e} from ⟨hx, hne⟩)

中文:
引理 isColoop_iff_notMem_closure_compl
  条件: (he : e in M.E := by aesop_mat)
  证明: by
  rw [isColoop_iff_sdiff_closure]; rw [not_iff_not]
  refine ⟨fun h => by rwa [h], fun h => (M.closure_subset_ground _).antisymm fun x hx => ?_⟩
  obtain (rfl | hne) := eq_or_ne x e
  · assumption
  exact M.subset_closure (M.E \ {e}) sdiff_subset (show x in M.E \ {e} from ⟨hx, hne⟩)

Depends on / 依赖: IsColoop, M.IsColoop, M.closure, M.closure_subset_ground, M.subset_closure, aesop_mat, antisymm, closure, closure_subset_ground, eq_or_ne, isColoop_iff_sdiff_closure, not_iff_not, sdiff_subset, subset_closure
-/
lemma isColoop_iff_notMem_closure_compl (he : e in M.E := by aesop_mat) :
    M.IsColoop e ↔ e ∉ M.closure (M.E \ {e}) := by
  rw [isColoop_iff_sdiff_closure]; rw [not_iff_not]
  refine ⟨fun h => by rwa [h], fun h => (M.closure_subset_ground _).antisymm fun x hx => ?_⟩
  obtain (rfl | hne) := eq_or_ne x e
  · assumption
  exact M.subset_closure (M.E \ {e}) sdiff_subset (show x in M.E \ {e} from ⟨hx, hne⟩)

/--
lemma `IsBase.isColoop_iff_forall_notMem_fundCircuit` / 引理 `IsBase.isColoop_iff_forall_notMem_fundCircuit`

English:
lemma IsBase.isColoop_iff_forall_notMem_fundCircuit
  given: (hB : M.IsBase B) (he : e in B)
  proof: by
  refine ⟨fun h x hx heC => (h.notMem_isCircuit <| hB.fundCircuit_isCircuit hx.1 hx.2) heC,
    fun h => ?_⟩
  have h' : M.E \ {e} subseteq M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x != e⟩
    obtain (hx | hx) := em (x in B)
    · exact M.subset_closure (B \ {e}) (sdiff_subset.trans hB.subset_ground) ⟨hx, hne⟩
    have h_cct := (hB.fundCircuit_isCircuit hxE hx).mem_closure_sdiff_singleton_of_mem
      (M.mem_fundCircuit x B)
    refine (M.closure_subset_closure (subset_sdiff_singleton ?_ ?_)) h_cct
    · simpa using fundCircuit_subset_insert ..
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [isColoop_iff_notMem_closure_compl (hB.subset_ground he)]
exact notMem_subset (M.closure_subset_closure_of_subset_closure h')
    hB.indep.notMem_closure_sdiff_of_mem he

中文:
引理 IsBase.isColoop_iff_对任意_notMem_fundCircuit
  条件: (hB : M.IsBase B) (he : e in B)
  证明: by
  refine ⟨fun h x hx heC => (h.notMem_isCircuit <| hB.fundCircuit_isCircuit hx.1 hx.2) heC,
    fun h => ?_⟩
  have h' : M.E \ {e} subseteq M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x != e⟩
    obtain (hx | hx) := em (x in B)
    · exact M.subset_closure (B \ {e}) (sdiff_subset.trans hB.subset_ground) ⟨hx, hne⟩
    have h_cct := (hB.fundCircuit_isCircuit hxE hx).mem_closure_sdiff_singleton_of_mem
      (M.mem_fundCircuit x B)
    refine (M.closure_subset_closure (subset_sdiff_singleton ?_ ?_)) h_cct
    · simpa using fundCircuit_subset_insert ..
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [isColoop_iff_notMem_closure_compl (hB.subset_ground he)]
exact notMem_subset (M.closure_subset_closure_of_subset_closure h')
    hB.indep.notMem_closure_sdiff_of_mem he

Depends on / 依赖: M.closure, M.closure_subset_closure, M.mem_fundCircuit, M.subset_closure, closure, closure_subset_closure, fundCircuit_isCircuit, h.notMem_isCircuit, hB.fundCircuit_isCircuit, hB.subset_ground, h_cct, mem_closure_sdiff_singleton_of_mem, mem_fundCircuit, notMem_isCircuit, sdiff_subset, sdiff_subset.trans, subset_closure, subset_ground, subset_sdiff_singleton, subseteq
-/
lemma IsBase.isColoop_iff_forall_notMem_fundCircuit (hB : M.IsBase B) (he : e in B) :
    M.IsColoop e ↔ forall x in M.E \ B, e ∉ M.fundCircuit x B := by
  refine ⟨fun h x hx heC => (h.notMem_isCircuit <| hB.fundCircuit_isCircuit hx.1 hx.2) heC,
    fun h => ?_⟩
  have h' : M.E \ {e} subseteq M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x != e⟩
    obtain (hx | hx) := em (x in B)
    · exact M.subset_closure (B \ {e}) (sdiff_subset.trans hB.subset_ground) ⟨hx, hne⟩
    have h_cct := (hB.fundCircuit_isCircuit hxE hx).mem_closure_sdiff_singleton_of_mem
      (M.mem_fundCircuit x B)
    refine (M.closure_subset_closure (subset_sdiff_singleton ?_ ?_)) h_cct
    · simpa using fundCircuit_subset_insert ..
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [isColoop_iff_notMem_closure_compl (hB.subset_ground he)]
exact notMem_subset (M.closure_subset_closure_of_subset_closure h')
    hB.indep.notMem_closure_sdiff_of_mem he

/--
lemma `IsBasis'.inter_coloops_subset` / 引理 `IsBasis'.inter_coloops_subset`

English:
lemma IsBasis'.inter_coloops_subset
  given: (hIX : M.IsBasis' I X)
  statement: X inter M.coloops subseteq I
  proof: by
  intro e ⟨heX, (heI : M.IsColoop e)⟩
  rwa [← heI.mem_closure_iff_mem, hIX.isBasis_closure_right.closure_eq_right,
    heI.mem_closure_iff_mem]

中文:
引理 是基'.inter_coloops_subset
  条件: (hIX : M.是基' I X)
  结论: X inter M.coloops subseteq I
  证明: by
  intro e ⟨heX, (heI : M.IsColoop e)⟩
  rwa [← heI.mem_closure_iff_mem, hIX.isBasis_closure_right.closure_eq_right,
    heI.mem_closure_iff_mem]
-/
lemma IsBasis'.inter_coloops_subset (hIX : M.IsBasis' I X) : X inter M.coloops subseteq I := by
  intro e ⟨heX, (heI : M.IsColoop e)⟩
  rwa [← heI.mem_closure_iff_mem, hIX.isBasis_closure_right.closure_eq_right,
    heI.mem_closure_iff_mem]

/--
lemma `IsBasis.inter_coloops_subset` / 引理 `IsBasis.inter_coloops_subset`

English:
lemma IsBasis.inter_coloops_subset
  given: (hIX : M.IsBasis I X)
  statement: X inter M.coloops subseteq I
  proof: hIX.isBasis'.inter_coloops_subset

中文:
引理 是基.inter_coloops_subset
  条件: (hIX : M.是基 I X)
  结论: X inter M.coloops subseteq I
  证明: hIX.isBasis'.inter_coloops_subset

Depends on / 依赖: hIX.isBasis, inter_coloops_subset, isBasis
-/
lemma IsBasis.inter_coloops_subset (hIX : M.IsBasis I X) : X inter M.coloops subseteq I :=
  hIX.isBasis'.inter_coloops_subset

/--
lemma `exists_mem_isCircuit_of_not_isColoop` / 引理 `exists_mem_isCircuit_of_not_isColoop`

English:
lemma exists_mem_isCircuit_of_not_isColoop
  given: (heE : e in M.E) (he : ¬ M.IsColoop e)
  proof: by
  simp only [isColoop_iff_forall_mem_isBase, not_forall, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp]

中文:
引理 存在_mem_isCircuit_of_not_isColoop
  条件: (heE : e in M.E) (he : ¬ M.IsColoop e)
  证明: by
  simp only [isColoop_iff_forall_mem_isBase, not_forall, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp]

Depends on / 依赖: M.fundCircuit, exists_prop, fundCircuit, fundCircuit_isCircuit, hB.fundCircuit_isCircuit, isColoop_iff_forall_mem_isBase, not_forall
-/
lemma exists_mem_isCircuit_of_not_isColoop (heE : e in M.E) (he : ¬ M.IsColoop e) :
    exists C, M.IsCircuit C ∧ e in C := by
  simp only [isColoop_iff_forall_mem_isBase, not_forall, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp]
/--
lemma `closure_inter_coloops_eq` / 引理 `closure_inter_coloops_eq`

English:
lemma closure_inter_coloops_eq
  given: (M : Matroid α) (X : Set α)
  proof: by
  simp_rw [Set.ext_iff, mem_inter_iff, ← isColoop_iff_mem_coloops, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

中文:
引理 closure_inter_coloops_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  simp_rw [Set.ext_iff, mem_inter_iff, ← isColoop_iff_mem_coloops, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

Depends on / 依赖: Set.ext_iff, and_congr_left_iff, ext_iff, he.mem_closure_iff_mem, isColoop_iff_mem_coloops, mem_closure_iff_mem, mem_inter_iff, simp_rw
-/
lemma closure_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure X inter M.coloops = X inter M.coloops := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← isColoop_iff_mem_coloops, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

/--
lemma `closure_inter_eq_of_subset_coloops` / 引理 `closure_inter_eq_of_subset_coloops`

English:
lemma closure_inter_eq_of_subset_coloops
  given: (X : Set α) (hK : K subseteq M.coloops)
  proof: by
  nth_rw 1 [← inter_eq_self_of_subset_right hK]
  rw [← inter_assoc]; rw [closure_inter_coloops_eq]; rw [inter_assoc]; rw [inter_eq_self_of_subset_right hK]

中文:
引理 closure_inter_eq_of_subset_coloops
  条件: (X : 集合 α) (hK : K subseteq M.coloops)
  证明: by
  nth_rw 1 [← inter_eq_self_of_subset_right hK]
  rw [← inter_assoc]; rw [closure_inter_coloops_eq]; rw [inter_assoc]; rw [inter_eq_self_of_subset_right hK]

Depends on / 依赖: closure_inter_coloops_eq, inter_assoc, inter_eq_self_of_subset_right, nth_rw
-/
lemma closure_inter_eq_of_subset_coloops (X : Set α) (hK : K subseteq M.coloops) :
     M.closure X inter K = X inter K := by
  nth_rw 1 [← inter_eq_self_of_subset_right hK]
  rw [← inter_assoc]; rw [closure_inter_coloops_eq]; rw [inter_assoc]; rw [inter_eq_self_of_subset_right hK]

/--
lemma `closure_union_eq_of_subset_coloops` / 引理 `closure_union_eq_of_subset_coloops`

English:
lemma closure_union_eq_of_subset_coloops
  given: (X : Set α) (hK : K subseteq M.coloops)
  proof: by
  rw [← closure_union_closure_left_eq]; rw [subset_antisymm_iff]; rw [and_iff_left (M.subset_closure _)]; rw [← sdiff_eq_empty]; rw [eq_empty_iff_forall_notMem]
  refine fun e ⟨hecl, he⟩ => he (.inl ?_)
  obtain ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_exists_isCircuit he).1 hecl
  rw [← singleton_union]; rw [← union_assoc]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [(hC.disjoint_coloops.mono_right hK).sdiff_eq_left]; rw [singleton_union] at hCss
exact M.closure_subset_closure_of_subset_closure (by simpa)
    hC.mem_closure_sdiff_singleton_of_mem heC

中文:
引理 closure_union_eq_of_subset_coloops
  条件: (X : 集合 α) (hK : K subseteq M.coloops)
  证明: by
  rw [← closure_union_closure_left_eq]; rw [subset_antisymm_iff]; rw [and_iff_left (M.subset_closure _)]; rw [← sdiff_eq_empty]; rw [eq_empty_iff_forall_notMem]
  refine fun e ⟨hecl, he⟩ => he (.inl ?_)
  obtain ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_exists_isCircuit he).1 hecl
  rw [← singleton_union]; rw [← union_assoc]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [(hC.disjoint_coloops.mono_right hK).sdiff_eq_left]; rw [singleton_union] at hCss
exact M.closure_subset_closure_of_subset_closure (by simpa)
    hC.mem_closure_sdiff_singleton_of_mem heC

Depends on / 依赖: M.closure_subset_closure_of_subset_closure, M.subset_closure, and_iff_left, closure_subset_closure_of_subset_closure, closure_union_closure_left_eq, disjoint_coloops, eq_empty_iff_forall_notMem, hC.disjoint_coloops.mono_right, mem_closure_iff_exists_isCircuit, mono_right, sdiff_eq_empty, sdiff_eq_left, sdiff_subset_iff, singleton_union, subset_antisymm_iff, subset_closure, union_assoc, union_comm
-/
lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K subseteq M.coloops) :
    M.closure (X union K) = M.closure X union K := by
  rw [← closure_union_closure_left_eq]; rw [subset_antisymm_iff]; rw [and_iff_left (M.subset_closure _)]; rw [← sdiff_eq_empty]; rw [eq_empty_iff_forall_notMem]
  refine fun e ⟨hecl, he⟩ => he (.inl ?_)
  obtain ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_exists_isCircuit he).1 hecl
  rw [← singleton_union]; rw [← union_assoc]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [(hC.disjoint_coloops.mono_right hK).sdiff_eq_left]; rw [singleton_union] at hCss
exact M.closure_subset_closure_of_subset_closure (by simpa)
    hC.mem_closure_sdiff_singleton_of_mem heC

/--
lemma `closure_insert_isColoop_eq` / 引理 `closure_insert_isColoop_eq`

English:
lemma closure_insert_isColoop_eq
  given: (X : Set α) (he : M.IsColoop e)
  proof: by
  rw [← union_singleton]; rw [closure_union_eq_of_subset_coloops _ (by simpa)]; rw [union_singleton]

中文:
引理 closure_insert_isColoop_eq
  条件: (X : 集合 α) (he : M.IsColoop e)
  证明: by
  rw [← union_singleton]; rw [closure_union_eq_of_subset_coloops _ (by simpa)]; rw [union_singleton]

Depends on / 依赖: closure_union_eq_of_subset_coloops, union_singleton
-/
lemma closure_insert_isColoop_eq (X : Set α) (he : M.IsColoop e) :
    M.closure (insert e X) = insert e (M.closure X) := by
  rw [← union_singleton]; rw [closure_union_eq_of_subset_coloops _ (by simpa)]; rw [union_singleton]

/--
lemma `closure_eq_of_subset_coloops` / 引理 `closure_eq_of_subset_coloops`

English:
lemma closure_eq_of_subset_coloops
  given: (hK : K subseteq M.coloops)
  statement: M.closure K = K union M.loops
  proof: by
  rw [← empty_union K]; rw [closure_union_eq_of_subset_coloops _ hK]; rw [empty_union]; rw [union_comm]; rw [closure_empty]

中文:
引理 closure_eq_of_subset_coloops
  条件: (hK : K subseteq M.coloops)
  结论: M.closure K = K union M.loops
  证明: by
  rw [← empty_union K]; rw [closure_union_eq_of_subset_coloops _ hK]; rw [empty_union]; rw [union_comm]; rw [closure_empty]

Depends on / 依赖: closure_empty, closure_union_eq_of_subset_coloops, empty_union, union_comm
-/
lemma closure_eq_of_subset_coloops (hK : K subseteq M.coloops) : M.closure K = K union M.loops := by
  rw [← empty_union K]; rw [closure_union_eq_of_subset_coloops _ hK]; rw [empty_union]; rw [union_comm]; rw [closure_empty]

/--
lemma `closure_sdiff_eq_of_subset_coloops` / 引理 `closure_sdiff_eq_of_subset_coloops`

English:
lemma closure_sdiff_eq_of_subset_coloops
  given: (X : Set α) (hK : K subseteq M.coloops)
  proof: by
  nth_rw 2 [← inter_union_sdiff X K]
  rw [union_comm]; rw [closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK)]; rw [union_sdiff_distrib]; rw [sdiff_eq_empty.mpr inter_subset_right]; rw [union_empty]; rw [eq_comm]; rw [sdiff_eq_self_iff_disjoint]; rw [disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [IsColoop.mem_closure_iff_mem (hK heK)] at heX
  exact heX.2 heK

@[deprecated (since := "2026-06-03")]
alias closure_diff_eq_of_subset_coloops := closure_sdiff_eq_of_subset_coloops

中文:
引理 closure_sdiff_eq_of_subset_coloops
  条件: (X : 集合 α) (hK : K subseteq M.coloops)
  证明: by
  nth_rw 2 [← inter_union_sdiff X K]
  rw [union_comm]; rw [closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK)]; rw [union_sdiff_distrib]; rw [sdiff_eq_empty.mpr inter_subset_right]; rw [union_empty]; rw [eq_comm]; rw [sdiff_eq_self_iff_disjoint]; rw [disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [IsColoop.mem_closure_iff_mem (hK heK)] at heX
  exact heX.2 heK

@[deprecated (since := "2026-06-03")]
alias closure_diff_eq_of_subset_coloops := closure_sdiff_eq_of_subset_coloops

Depends on / 依赖: IsColoop, IsColoop.mem_closure_iff_mem, closure_union_eq_of_subset_coloops, disjoint_iff_forall_ne, eq_comm, inter_subset_right, inter_subset_right.trans, inter_union_sdiff, mem_closure_iff_mem, nth_rw, sdiff_eq_empty, sdiff_eq_empty.mpr, sdiff_eq_self_iff_disjoint, union_comm, union_empty, union_sdiff_distrib
-/
lemma closure_sdiff_eq_of_subset_coloops (X : Set α) (hK : K subseteq M.coloops) :
    M.closure (X \ K) = M.closure X \ K := by
  nth_rw 2 [← inter_union_sdiff X K]
  rw [union_comm]; rw [closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK)]; rw [union_sdiff_distrib]; rw [sdiff_eq_empty.mpr inter_subset_right]; rw [union_empty]; rw [eq_comm]; rw [sdiff_eq_self_iff_disjoint]; rw [disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [IsColoop.mem_closure_iff_mem (hK heK)] at heX
  exact heX.2 heK

@[deprecated (since := "2026-06-03")]
alias closure_diff_eq_of_subset_coloops := closure_sdiff_eq_of_subset_coloops

/--
lemma `closure_disjoint_of_disjoint_of_subset_coloops` / 引理 `closure_disjoint_of_disjoint_of_subset_coloops`

English:
lemma closure_disjoint_of_disjoint_of_subset_coloops
  given: (hXK : Disjoint X K) (hK : K subseteq M.coloops)
  proof: by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]

中文:
引理 closure_disjoint_of_disjoint_of_subset_coloops
  条件: (hXK : Disjoint X K) (hK : K subseteq M.coloops)
  证明: by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]

Depends on / 依赖: closure_inter_eq_of_subset_coloops, disjoint_iff_inter_eq_empty
-/
lemma closure_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K subseteq M.coloops) :
    Disjoint (M.closure X) K := by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]

/--
lemma `closure_disjoint_coloops_of_disjoint_coloops` / 引理 `closure_disjoint_coloops_of_disjoint_coloops`

English:
lemma closure_disjoint_coloops_of_disjoint_coloops
  given: (hX : Disjoint X (M.coloops))
  proof: closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

中文:
引理 closure_disjoint_coloops_of_disjoint_coloops
  条件: (hX : Disjoint X (M.coloops))
  证明: closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, closure_disjoint_of_disjoint_of_subset_coloops
-/
lemma closure_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M.coloops)) :
    Disjoint (M.closure X) M.coloops :=
  closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

/--
lemma `closure_union_coloops_eq` / 引理 `closure_union_coloops_eq`

English:
lemma closure_union_coloops_eq
  given: (M : Matroid α) (X : Set α)
  proof: closure_union_eq_of_subset_coloops _ Subset.rfl

中文:
引理 closure_union_coloops_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: closure_union_eq_of_subset_coloops _ Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, closure_union_eq_of_subset_coloops
-/
lemma closure_union_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure (X union M.coloops) = M.closure X union M.coloops :=
  closure_union_eq_of_subset_coloops _ Subset.rfl

/--
lemma `IsColoop.notMem_closure_of_notMem` / 引理 `IsColoop.notMem_closure_of_notMem`

English:
lemma IsColoop.notMem_closure_of_notMem
  given: (he : M.IsColoop e) (hX : e ∉ X)
  statement: e ∉ M.closure X
  proof: mt he.mem_closure_iff_mem.mp hX

中文:
引理 IsColoop.notMem_closure_of_notMem
  条件: (he : M.IsColoop e) (hX : e ∉ X)
  结论: e ∉ M.closure X
  证明: mt he.mem_closure_iff_mem.mp hX

Depends on / 依赖: he.mem_closure_iff_mem.mp, mem_closure_iff_mem
-/
lemma IsColoop.notMem_closure_of_notMem (he : M.IsColoop e) (hX : e ∉ X) : e ∉ M.closure X :=
  mt he.mem_closure_iff_mem.mp hX

/--
lemma `IsColoop.insert_indep_of_indep` / 引理 `IsColoop.insert_indep_of_indep`

English:
lemma IsColoop.insert_indep_of_indep
  given: (he : M.IsColoop e) (hI : M.Indep I)
  proof: by
  refine (em (e in I)).elim (fun h => by rwa [insert_eq_of_mem h]) fun h => ?_
  rw [← hI.notMem_closure_iff_of_notMem h]
  exact he.notMem_closure_of_notMem h

中文:
引理 IsColoop.insert_indep_of_indep
  条件: (he : M.IsColoop e) (hI : M.Indep I)
  证明: by
  refine (em (e in I)).elim (fun h => by rwa [insert_eq_of_mem h]) fun h => ?_
  rw [← hI.notMem_closure_iff_of_notMem h]
  exact he.notMem_closure_of_notMem h

Depends on / 依赖: hI.notMem_closure_iff_of_notMem, he.notMem_closure_of_notMem, insert_eq_of_mem, notMem_closure_iff_of_notMem, notMem_closure_of_notMem
-/
lemma IsColoop.insert_indep_of_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := by
  refine (em (e in I)).elim (fun h => by rwa [insert_eq_of_mem h]) fun h => ?_
  rw [← hI.notMem_closure_iff_of_notMem h]
  exact he.notMem_closure_of_notMem h

/--
lemma `union_indep_iff_indep_of_subset_coloops` / 引理 `union_indep_iff_indep_of_subset_coloops`

English:
lemma union_indep_iff_indep_of_subset_coloops
  given: (hK : K subseteq M.coloops)
  proof: by
  refine ⟨fun h => h.subset subset_union_left, fun h => ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he => IsColoop.mem_of_isBase he hB))

中文:
引理 union_indep_iff_indep_of_subset_coloops
  条件: (hK : K subseteq M.coloops)
  证明: by
  refine ⟨fun h => h.subset subset_union_left, fun h => ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he => IsColoop.mem_of_isBase he hB))

Depends on / 依赖: IsColoop, IsColoop.mem_of_isBase, exists_isBase_superset, h.exists_isBase_superset, h.subset, hB.indep.subset, hK.trans, mem_of_isBase, subset, subset_union_left, union_subset
-/
lemma union_indep_iff_indep_of_subset_coloops (hK : K subseteq M.coloops) :
    M.Indep (I union K) ↔ M.Indep I := by
  refine ⟨fun h => h.subset subset_union_left, fun h => ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he => IsColoop.mem_of_isBase he hB))

/--
lemma `sdiff_indep_iff_indep_of_subset_coloops` / 引理 `sdiff_indep_iff_indep_of_subset_coloops`

English:
lemma sdiff_indep_iff_indep_of_subset_coloops
  given: (hK : K subseteq M.coloops)
  proof: by
  rw [← union_indep_iff_indep_of_subset_coloops hK]; rw [sdiff_union_self]; rw [union_indep_iff_indep_of_subset_coloops hK]

@[deprecated (since := "2026-06-03")]
alias diff_indep_iff_indep_of_subset_coloops := sdiff_indep_iff_indep_of_subset_coloops

@[simp]

中文:
引理 sdiff_indep_iff_indep_of_subset_coloops
  条件: (hK : K subseteq M.coloops)
  证明: by
  rw [← union_indep_iff_indep_of_subset_coloops hK]; rw [sdiff_union_self]; rw [union_indep_iff_indep_of_subset_coloops hK]

@[deprecated (since := "2026-06-03")]
alias diff_indep_iff_indep_of_subset_coloops := sdiff_indep_iff_indep_of_subset_coloops

@[simp]

Depends on / 依赖: sdiff_union_self, union_indep_iff_indep_of_subset_coloops
-/
lemma sdiff_indep_iff_indep_of_subset_coloops (hK : K subseteq M.coloops) :
    M.Indep (I \ K) ↔ M.Indep I := by
  rw [← union_indep_iff_indep_of_subset_coloops hK]; rw [sdiff_union_self]; rw [union_indep_iff_indep_of_subset_coloops hK]

@[deprecated (since := "2026-06-03")]
alias diff_indep_iff_indep_of_subset_coloops := sdiff_indep_iff_indep_of_subset_coloops

@[simp]
/--
lemma `union_coloops_indep_iff` / 引理 `union_coloops_indep_iff`

English:
lemma union_coloops_indep_iff
  statement: M.Indep (I union M.coloops) ↔ M.Indep I
  proof: union_indep_iff_indep_of_subset_coloops Subset.rfl

@[simp]

中文:
引理 union_coloops_indep_iff
  结论: M.Indep (I union M.coloops) ↔ M.Indep I
  证明: union_indep_iff_indep_of_subset_coloops Subset.rfl

@[simp]

Depends on / 依赖: Subset, Subset.rfl, union_indep_iff_indep_of_subset_coloops
-/
lemma union_coloops_indep_iff : M.Indep (I union M.coloops) ↔ M.Indep I :=
  union_indep_iff_indep_of_subset_coloops Subset.rfl

@[simp]
/--
lemma `sdiff_coloops_indep_iff` / 引理 `sdiff_coloops_indep_iff`

English:
lemma sdiff_coloops_indep_iff
  statement: M.Indep (I \ M.coloops) ↔ M.Indep I
  proof: sdiff_indep_iff_indep_of_subset_coloops Subset.rfl

@[deprecated (since := "2026-06-03")] alias diff_coloops_indep_iff := sdiff_coloops_indep_iff

中文:
引理 sdiff_coloops_indep_iff
  结论: M.Indep (I \ M.coloops) ↔ M.Indep I
  证明: sdiff_indep_iff_indep_of_subset_coloops Subset.rfl

@[deprecated (since := "2026-06-03")] alias diff_coloops_indep_iff := sdiff_coloops_indep_iff

Depends on / 依赖: Subset, Subset.rfl, sdiff_indep_iff_indep_of_subset_coloops
-/
lemma sdiff_coloops_indep_iff : M.Indep (I \ M.coloops) ↔ M.Indep I :=
  sdiff_indep_iff_indep_of_subset_coloops Subset.rfl

@[deprecated (since := "2026-06-03")] alias diff_coloops_indep_iff := sdiff_coloops_indep_iff

/--
lemma `coloops_indep` / 引理 `coloops_indep`

English:
lemma coloops_indep
  given: (M : Matroid α)
  statement: M.Indep M.coloops
  proof: by
  rw [← empty_union M.coloops]; rw [union_coloops_indep_iff]
  exact M.empty_indep

中文:
引理 coloops_indep
  条件: (M : 拟阵 α)
  结论: M.Indep M.coloops
  证明: by
  rw [← empty_union M.coloops]; rw [union_coloops_indep_iff]
  exact M.empty_indep

Depends on / 依赖: M.coloops, M.empty_indep, coloops, empty_indep, empty_union, union_coloops_indep_iff
-/
lemma coloops_indep (M : Matroid α) : M.Indep M.coloops := by
  rw [← empty_union M.coloops]; rw [union_coloops_indep_iff]
  exact M.empty_indep

/--
lemma `restrict_isColoop_iff` / 引理 `restrict_isColoop_iff`

English:
lemma restrict_isColoop_iff
  given: {R : Set α} (hRE : R subseteq M.E)
  proof: by
  wlog heR : e in R
  · exact iff_of_false (fun h => heR h.mem_ground) fun h => heR h.2
  rw [isColoop_iff_forall_notMem_isCircuit heR]; rw [mem_closure_iff_exists_isCircuit (by simp)]
  simp only [restrict_isCircuit_iff hRE, insert_sdiff_singleton]
  aesop

中文:
引理 restrict_isColoop_iff
  条件: {R : 集合 α} (hRE : R subseteq M.E)
  证明: by
  wlog heR : e in R
  · exact iff_of_false (fun h => heR h.mem_ground) fun h => heR h.2
  rw [isColoop_iff_forall_notMem_isCircuit heR]; rw [mem_closure_iff_exists_isCircuit (by simp)]
  simp only [restrict_isCircuit_iff hRE, insert_sdiff_singleton]
  aesop

Depends on / 依赖: h.mem_ground, iff_of_false, insert_sdiff_singleton, isColoop_iff_forall_notMem_isCircuit, mem_closure_iff_exists_isCircuit, mem_ground, restrict_isCircuit_iff
-/
lemma restrict_isColoop_iff {R : Set α} (hRE : R subseteq M.E) :
    (M ↾ R).IsColoop e ↔ e ∉ M.closure (R \ {e}) ∧ e in R := by
  wlog heR : e in R
  · exact iff_of_false (fun h => heR h.mem_ground) fun h => heR h.2
  rw [isColoop_iff_forall_notMem_isCircuit heR]; rw [mem_closure_iff_exists_isCircuit (by simp)]
  simp only [restrict_isCircuit_iff hRE, insert_sdiff_singleton]
  aesop

/--
lemma `ext_indep_disjoint_loops_coloops` / 引理 `ext_indep_disjoint_loops_coloops`

English:
lemma ext_indep_disjoint_loops_coloops
  statement: {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
  proof: by
  refine ext_indep hE fun I hI => ?_
  rw [← sdiff_coloops_indep_iff]; rw [← @sdiff_coloops_indep_iff _ M₂]; rw [← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.loops))
  · rw [h _ (sdiff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left sdiff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩) ?_
  rw [isLoop_iff]; rw [hl]; rw [← isLoop_iff] at hel
  rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩

中文:
引理 ext_indep_disjoint_loops_coloops
  结论: {M₁ M₂ : 拟阵 α} (hE : M₁.E = M₂.E)
  证明: by
  refine ext_indep hE fun I hI => ?_
  rw [← sdiff_coloops_indep_iff]; rw [← @sdiff_coloops_indep_iff _ M₂]; rw [← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.loops))
  · rw [h _ (sdiff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left sdiff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩) ?_
  rw [isLoop_iff]; rw [hl]; rw [← isLoop_iff] at hel
  rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩

Depends on / 依赖: Disjoint, IsLoop, disjoint_of_subset_left, disjoint_sdiff_left, disjoint_union_right, ext_indep, hel.not_indep_of_mem, hel.not_isColoop, iff_of_false, isLoop_iff, not_disjoint_iff_nonempty_inter, not_disjoint_iff_nonempty_inter.mp, not_indep_of_mem, not_isColoop, sdiff_coloops_indep_iff, sdiff_subset, sdiff_subset.trans
-/
lemma ext_indep_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.loops = M₂.loops) (hc : M₁.coloops = M₂.coloops)
    (h : forall I, I subseteq M₁.E -> Disjoint I (M₁.loops union M₁.coloops) -> (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine ext_indep hE fun I hI => ?_
  rw [← sdiff_coloops_indep_iff]; rw [← @sdiff_coloops_indep_iff _ M₂]; rw [← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.loops))
  · rw [h _ (sdiff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left sdiff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩) ?_
  rw [isLoop_iff]; rw [hl]; rw [← isLoop_iff] at hel
  rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩

end IsColoop

section Loopless

/-- A Matroid is `Loopless` if it has no loop -/
@[mk_iff]
/--
Definition of `Loopless` / `Loopless` 的定义

English:
class Loopless
  parameters: (M : Matroid α)
  axioms and operations (1):
    - loops_eq_empty : M.loops = ∅

中文:
类 无环
  参数: (M : 拟阵 α)
  公理与运算 (1 个):
    - loops_eq_empty : M.loops = ∅
-/
class Loopless (M : Matroid α) : Prop where
  loops_eq_empty : M.loops = ∅

@[simp]
/--
lemma `loops_eq_empty` / 引理 `loops_eq_empty`

English:
lemma loops_eq_empty
  given: (M : Matroid α) [Loopless M]
  statement: M.loops = ∅
  proof: ‹Loopless M›.loops_eq_empty

中文:
引理 loops_eq_empty
  条件: (M : 拟阵 α) [无环 M]
  结论: M.loops = ∅
  证明: ‹Loopless M›.loops_eq_empty

Depends on / 依赖: Loopless, loops_eq_empty
-/
lemma loops_eq_empty (M : Matroid α) [Loopless M] : M.loops = ∅ :=
  ‹Loopless M›.loops_eq_empty

/--
lemma `isNonloop_of_loopless` / 引理 `isNonloop_of_loopless`

English:
lemma isNonloop_of_loopless
  given: [Loopless M] (he : e in M.E := by aesop_mat)
  proof: by
  rw [← not_isLoop_iff]; rw [isLoop_iff]; rw [loops_eq_empty]
  exact notMem_empty _

中文:
引理 isNonloop_of_loopless
  条件: [无环 M] (he : e in M.E := by aesop_mat)
  证明: by
  rw [← not_isLoop_iff]; rw [isLoop_iff]; rw [loops_eq_empty]
  exact notMem_empty _

Depends on / 依赖: IsNonloop, M.IsNonloop, aesop_mat, isLoop_iff, loops_eq_empty, notMem_empty, not_isLoop_iff
-/
lemma isNonloop_of_loopless [Loopless M] (he : e in M.E := by aesop_mat) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff]; rw [isLoop_iff]; rw [loops_eq_empty]
  exact notMem_empty _

/--
lemma `subsingleton_indep` / 引理 `subsingleton_indep`

English:
lemma subsingleton_indep
  given: [M.Loopless] (hI : I.Subsingleton) (hIE : I subseteq M.E := by aesop_mat)
  proof: by
  obtain rfl | ⟨x, rfl⟩ := hI.eq_empty_or_singleton
  · simp
  simpa using M.isNonloop_of_loopless

中文:
引理 subsingleton_indep
  条件: [M.无环] (hI : I.子单例) (hIE : I subseteq M.E := by aesop_mat)
  证明: by
  obtain rfl | ⟨x, rfl⟩ := hI.eq_empty_or_singleton
  · simp
  simpa using M.isNonloop_of_loopless

Depends on / 依赖: M.Indep, M.isNonloop_of_loopless, aesop_mat, eq_empty_or_singleton, hI.eq_empty_or_singleton, isNonloop_of_loopless
-/
lemma subsingleton_indep [M.Loopless] (hI : I.Subsingleton) (hIE : I subseteq M.E := by aesop_mat) :
    M.Indep I := by
  obtain rfl | ⟨x, rfl⟩ := hI.eq_empty_or_singleton
  · simp
  simpa using M.isNonloop_of_loopless

/--
lemma `not_isLoop` / 引理 `not_isLoop`

English:
lemma not_isLoop
  given: (M : Matroid α) [Loopless M] (e : α)
  statement: ¬ M.IsLoop e
  proof: fun h => (isNonloop_of_loopless (e := e)).not_isLoop h

中文:
引理 not_isLoop
  条件: (M : 拟阵 α) [无环 M] (e : α)
  结论: ¬ M.IsLoop e
  证明: fun h => (isNonloop_of_loopless (e := e)).not_isLoop h

Depends on / 依赖: isNonloop_of_loopless, not_isLoop
-/
lemma not_isLoop (M : Matroid α) [Loopless M] (e : α) : ¬ M.IsLoop e :=
  fun h => (isNonloop_of_loopless (e := e)).not_isLoop h

/--
lemma `loopless_iff_forall_isNonloop` / 引理 `loopless_iff_forall_isNonloop`

English:
lemma loopless_iff_forall_isNonloop
  statement: M.Loopless ↔ forall e in M.E, M.IsNonloop e
  proof: ⟨fun _ _ he => isNonloop_of_loopless he,
    fun h => ⟨subset_empty_iff.1 (fun e (he : M.IsLoop e) => (h e he.mem_ground).not_isLoop he)⟩⟩

中文:
引理 loopless_iff_对任意_isNonloop
  结论: M.无环 ↔ 对任意 e in M.E, M.是Nonloop e
  证明: ⟨fun _ _ he => isNonloop_of_loopless he,
    fun h => ⟨subset_empty_iff.1 (fun e (he : M.IsLoop e) => (h e he.mem_ground).not_isLoop he)⟩⟩

Depends on / 依赖: IsLoop, M.IsLoop, he.mem_ground, isNonloop_of_loopless, mem_ground, not_isLoop, subset_empty_iff
-/
lemma loopless_iff_forall_isNonloop : M.Loopless ↔ forall e in M.E, M.IsNonloop e :=
  ⟨fun _ _ he => isNonloop_of_loopless he,
    fun h => ⟨subset_empty_iff.1 (fun e (he : M.IsLoop e) => (h e he.mem_ground).not_isLoop he)⟩⟩

/--
lemma `loopless_iff_forall_not_isLoop` / 引理 `loopless_iff_forall_not_isLoop`

English:
lemma loopless_iff_forall_not_isLoop
  statement: M.Loopless ↔ forall e in M.E, ¬ M.IsLoop e
  proof: ⟨fun _ e _ => M.not_isLoop e,
    fun h => loopless_iff_forall_isNonloop.2 fun e he => (not_isLoop_iff he).1 (h e he)⟩

中文:
引理 loopless_iff_对任意_not_isLoop
  结论: M.无环 ↔ 对任意 e in M.E, ¬ M.IsLoop e
  证明: ⟨fun _ e _ => M.not_isLoop e,
    fun h => loopless_iff_forall_isNonloop.2 fun e he => (not_isLoop_iff he).1 (h e he)⟩

Depends on / 依赖: M.not_isLoop, loopless_iff_forall_isNonloop, not_isLoop, not_isLoop_iff
-/
lemma loopless_iff_forall_not_isLoop : M.Loopless ↔ forall e in M.E, ¬ M.IsLoop e :=
  ⟨fun _ e _ => M.not_isLoop e,
    fun h => loopless_iff_forall_isNonloop.2 fun e he => (not_isLoop_iff he).1 (h e he)⟩

/--
lemma `loopless_iff_forall_isCircuit` / 引理 `loopless_iff_forall_isCircuit`

English:
lemma loopless_iff_forall_isCircuit
  statement: M.Loopless ↔ forall C, M.IsCircuit C -> C.Nontrivial
  proof: by
  suffices (exists x in M.E, M.IsLoop x) ↔ exists x, M.IsCircuit x ∧ x.Subsingleton by
    rw [loopless_iff_forall_not_isLoop]
    contrapose!
    exact this
  refine ⟨fun ⟨e, _, he⟩ => ⟨{e}, he.isCircuit, by simp⟩, fun ⟨C, hC, hCs⟩ => ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_isCircuit.1 hC).mem_ground, singleton_isCircuit.1 hC⟩

中文:
引理 loopless_iff_对任意_isCircuit
  结论: M.无环 ↔ 对任意 C, M.是Circuit C -> C.非平凡
  证明: by
  suffices (exists x in M.E, M.IsLoop x) ↔ exists x, M.IsCircuit x ∧ x.Subsingleton by
    rw [loopless_iff_forall_not_isLoop]
    contrapose!
    exact this
  refine ⟨fun ⟨e, _, he⟩ => ⟨{e}, he.isCircuit, by simp⟩, fun ⟨C, hC, hCs⟩ => ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_isCircuit.1 hC).mem_ground, singleton_isCircuit.1 hC⟩

Depends on / 依赖: IsCircuit, IsLoop, M.IsCircuit, M.IsLoop, Subsingleton, contrapose, eq_empty_or_singleton, hC.nonempty, hCs.eq_empty_or_singleton, he.isCircuit, isCircuit, loopless_iff_forall_not_isLoop, mem_ground, nonempty, singleton_isCircuit, x.Subsingleton
-/
lemma loopless_iff_forall_isCircuit : M.Loopless ↔ forall C, M.IsCircuit C -> C.Nontrivial := by
  suffices (exists x in M.E, M.IsLoop x) ↔ exists x, M.IsCircuit x ∧ x.Subsingleton by
    rw [loopless_iff_forall_not_isLoop]
    contrapose!
    exact this
  refine ⟨fun ⟨e, _, he⟩ => ⟨{e}, he.isCircuit, by simp⟩, fun ⟨C, hC, hCs⟩ => ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_isCircuit.1 hC).mem_ground, singleton_isCircuit.1 hC⟩

/--
lemma `Loopless.ground_eq` / 引理 `Loopless.ground_eq`

English:
lemma Loopless.ground_eq
  given: (M : Matroid α) [Loopless M]
  statement: M.E = {e | M.IsNonloop e}
  proof: Set.ext fun _ => ⟨fun he => isNonloop_of_loopless he, IsNonloop.mem_ground⟩

中文:
引理 无环.ground_eq
  条件: (M : 拟阵 α) [无环 M]
  结论: M.E = {e | M.是Nonloop e}
  证明: Set.ext fun _ => ⟨fun he => isNonloop_of_loopless he, IsNonloop.mem_ground⟩

Depends on / 依赖: IsNonloop, IsNonloop.mem_ground, Set.ext, isNonloop_of_loopless, mem_ground
-/
lemma Loopless.ground_eq (M : Matroid α) [Loopless M] : M.E = {e | M.IsNonloop e} :=
  Set.ext fun _ => ⟨fun he => isNonloop_of_loopless he, IsNonloop.mem_ground⟩

/--
lemma `IsRestriction.loopless` / 引理 `IsRestriction.loopless`

English:
lemma IsRestriction.loopless
  given: [M.Loopless] (hR : N <=r M)
  statement: N.Loopless
  proof: by
  obtain ⟨R, hR, rfl⟩ := hR
  rw [loopless_iff]; rw [restrict_loops_eq hR]; rw [M.loops_eq_empty]; rw [empty_inter]

中文:
引理 IsRestriction.loopless
  条件: [M.无环] (hR : N <=r M)
  结论: N.无环
  证明: by
  obtain ⟨R, hR, rfl⟩ := hR
  rw [loopless_iff]; rw [restrict_loops_eq hR]; rw [M.loops_eq_empty]; rw [empty_inter]

Depends on / 依赖: M.loops_eq_empty, empty_inter, loopless_iff, loops_eq_empty, restrict_loops_eq
-/
lemma IsRestriction.loopless [M.Loopless] (hR : N <=r M) : N.Loopless := by
  obtain ⟨R, hR, rfl⟩ := hR
  rw [loopless_iff]; rw [restrict_loops_eq hR]; rw [M.loops_eq_empty]; rw [empty_inter]

instance {M : Matroid α} [M.Nonempty] [Loopless M] : RankPos M :=
  M.ground_nonempty.elim fun _ he => (isNonloop_of_loopless he).rankPos

/--
lemma `loopyOn_isLoopless_iff` / 引理 `loopyOn_isLoopless_iff`

English:
lemma loopyOn_isLoopless_iff
  given: {E : Set α}
  statement: Loopless (loopyOn E) ↔ E = ∅
  proof: by
  simp [loopless_iff_forall_not_isLoop, eq_empty_iff_forall_notMem]

中文:
引理 loopyOn_isLoopless_iff
  条件: {E : 集合 α}
  结论: 无环 (loopyOn E) ↔ E = ∅
  证明: by
  simp [loopless_iff_forall_not_isLoop, eq_empty_iff_forall_notMem]
-/
@[simp] lemma loopyOn_isLoopless_iff {E : Set α} : Loopless (loopyOn E) ↔ E = ∅ := by
  simp [loopless_iff_forall_not_isLoop, eq_empty_iff_forall_notMem]

/--
Definition of `removeLoops` / `removeLoops` 的定义

English:
definition removeLoops
  signature: (M : Matroid α)
  body: M ↾ {e | M.IsNonloop e}

中文:
定义 removeLoops
  签名: (M : 拟阵 α)
  定义体: M ↾ {e | M.IsNonloop e}

Depends on / 依赖: IsNonloop, M.IsNonloop
-/
def removeLoops (M : Matroid α) : Matroid α := M ↾ {e | M.IsNonloop e}

/--
lemma `removeLoops_eq_restrict` / 引理 `removeLoops_eq_restrict`

English:
lemma removeLoops_eq_restrict
  given: (M : Matroid α)
  statement: M.removeLoops = M ↾ {e | M.IsNonloop e}
  proof: rfl

中文:
引理 removeLoops_eq_restrict
  条件: (M : 拟阵 α)
  结论: M.removeLoops = M ↾ {e | M.是Nonloop e}
  证明: rfl
-/
lemma removeLoops_eq_restrict (M : Matroid α) : M.removeLoops = M ↾ {e | M.IsNonloop e} := rfl

/--
lemma `removeLoops_ground_eq` / 引理 `removeLoops_ground_eq`

English:
lemma removeLoops_ground_eq
  given: (M : Matroid α)
  statement: M.removeLoops.E = {e | M.IsNonloop e}
  proof: rfl

中文:
引理 removeLoops_ground_eq
  条件: (M : 拟阵 α)
  结论: M.removeLoops.E = {e | M.是Nonloop e}
  证明: rfl
-/
lemma removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.IsNonloop e} := rfl

/--
Instance `removeLoops_loopless` / 实例 `removeLoops_loopless`

English:
instance removeLoops_loopless
  signature: (M : Matroid α)
  body: by
  simp [loopless_iff_forall_isNonloop, removeLoops]

@[simp]

中文:
实例 removeLoops_loopless
  签名: (M : 拟阵 α)
  定义体: by
  simp [loopless_iff_forall_isNonloop, removeLoops]

@[simp]

Depends on / 依赖: loopless_iff_forall_isNonloop, removeLoops
-/
instance removeLoops_loopless (M : Matroid α) : Loopless M.removeLoops := by
  simp [loopless_iff_forall_isNonloop, removeLoops]

@[simp]
/--
lemma `removeLoops_eq_self` / 引理 `removeLoops_eq_self`

English:
lemma removeLoops_eq_self
  given: (M : Matroid α) [Loopless M]
  statement: M.removeLoops = M
  proof: by
  rw [removeLoops]; rw [← Loopless.ground_eq]; rw [restrict_ground_eq_self]

中文:
引理 removeLoops_eq_self
  条件: (M : 拟阵 α) [无环 M]
  结论: M.removeLoops = M
  证明: by
  rw [removeLoops]; rw [← Loopless.ground_eq]; rw [restrict_ground_eq_self]

Depends on / 依赖: Loopless, Loopless.ground_eq, ground_eq, removeLoops, restrict_ground_eq_self
-/
lemma removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M := by
  rw [removeLoops]; rw [← Loopless.ground_eq]; rw [restrict_ground_eq_self]

/--
lemma `removeLoops_eq_self_iff` / 引理 `removeLoops_eq_self_iff`

English:
lemma removeLoops_eq_self_iff
  statement: M.removeLoops = M ↔ M.Loopless
  proof: by
  refine ⟨fun h => ?_, fun h => M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance

中文:
引理 removeLoops_eq_self_iff
  结论: M.removeLoops = M ↔ M.无环
  证明: by
  refine ⟨fun h => ?_, fun h => M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance

Depends on / 依赖: M.removeLoops_eq_self, infer_instance, removeLoops_eq_self
-/
lemma removeLoops_eq_self_iff : M.removeLoops = M ↔ M.Loopless := by
  refine ⟨fun h => ?_, fun h => M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance

/--
lemma `removeLoops_isRestriction` / 引理 `removeLoops_isRestriction`

English:
lemma removeLoops_isRestriction
  given: (M : Matroid α)
  statement: M.removeLoops <=r M
  proof: restrict_isRestriction _ _ (fun _ h => IsNonloop.mem_ground h)

中文:
引理 removeLoops_isRestriction
  条件: (M : 拟阵 α)
  结论: M.removeLoops <=r M
  证明: restrict_isRestriction _ _ (fun _ h => IsNonloop.mem_ground h)

Depends on / 依赖: IsNonloop, IsNonloop.mem_ground, mem_ground, restrict_isRestriction
-/
lemma removeLoops_isRestriction (M : Matroid α) : M.removeLoops <=r M :=
  restrict_isRestriction _ _ (fun _ h => IsNonloop.mem_ground h)

/--
lemma `eq_restrict_removeLoops` / 引理 `eq_restrict_removeLoops`

English:
lemma eq_restrict_removeLoops
  given: (M : Matroid α)
  statement: M.removeLoops ↾ M.E = M
  proof: by
  rw [removeLoops]; rw [ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE => ⟨ fun hI => hI.1.1, fun hI => ⟨⟨hI,fun e heI => hI.isNonloop_of_mem heI⟩, hIE⟩⟩

@[simp]

中文:
引理 eq_restrict_removeLoops
  条件: (M : 拟阵 α)
  结论: M.removeLoops ↾ M.E = M
  证明: by
  rw [removeLoops]; rw [ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE => ⟨ fun hI => hI.1.1, fun hI => ⟨⟨hI,fun e heI => hI.isNonloop_of_mem heI⟩, hIE⟩⟩

@[simp]

Depends on / 依赖: ext_iff_indep, hI.isNonloop_of_mem, isNonloop_of_mem, removeLoops, restrict_ground_eq, restrict_indep_iff, true_and
-/
lemma eq_restrict_removeLoops (M : Matroid α) : M.removeLoops ↾ M.E = M := by
  rw [removeLoops]; rw [ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE => ⟨ fun hI => hI.1.1, fun hI => ⟨⟨hI,fun e heI => hI.isNonloop_of_mem heI⟩, hIE⟩⟩

@[simp]
/--
lemma `removeLoops_indep_eq` / 引理 `removeLoops_indep_eq`

English:
lemma removeLoops_indep_eq
  statement: M.removeLoops.Indep = M.Indep
  proof: by
  ext I
  rw [removeLoops_eq_restrict]; rw [restrict_indep_iff]; rw [and_iff_left_iff_imp]
  exact fun h e => h.isNonloop_of_mem

@[simp]

中文:
引理 removeLoops_indep_eq
  结论: M.removeLoops.Indep = M.Indep
  证明: by
  ext I
  rw [removeLoops_eq_restrict]; rw [restrict_indep_iff]; rw [and_iff_left_iff_imp]
  exact fun h e => h.isNonloop_of_mem

@[simp]

Depends on / 依赖: and_iff_left_iff_imp, h.isNonloop_of_mem, isNonloop_of_mem, removeLoops_eq_restrict, restrict_indep_iff
-/
lemma removeLoops_indep_eq : M.removeLoops.Indep = M.Indep := by
  ext I
  rw [removeLoops_eq_restrict]; rw [restrict_indep_iff]; rw [and_iff_left_iff_imp]
  exact fun h e => h.isNonloop_of_mem

@[simp]
/--
lemma `removeLoops_isBasis'_eq` / 引理 `removeLoops_isBasis'_eq`

English:
lemma removeLoops_isBasis'_eq
  statement: M.removeLoops.IsBasis' = M.IsBasis'
  proof: by
  ext
  simp [IsBasis']

中文:
引理 removeLoops_isBasis'_eq
  结论: M.removeLoops.是基' = M.是基'
  证明: by
  ext
  simp [IsBasis']

Depends on / 依赖: IsBasis
-/
lemma removeLoops_isBasis'_eq : M.removeLoops.IsBasis' = M.IsBasis' := by
  ext
  simp [IsBasis']

/--
lemma `removeLoops_isBase_eq` / 引理 `removeLoops_isBase_eq`

English:
lemma removeLoops_isBase_eq
  statement: M.removeLoops.IsBase = M.IsBase
  proof: by
  ext B
  rw [isBase_iff_maximal_indep]; rw [removeLoops_indep_eq]; rw [isBase_iff_maximal_indep]

@[simp]

中文:
引理 removeLoops_isBase_eq
  结论: M.removeLoops.IsBase = M.IsBase
  证明: by
  ext B
  rw [isBase_iff_maximal_indep]; rw [removeLoops_indep_eq]; rw [isBase_iff_maximal_indep]

@[simp]
-/
@[simp] lemma removeLoops_isBase_eq : M.removeLoops.IsBase = M.IsBase := by
  ext B
  rw [isBase_iff_maximal_indep]; rw [removeLoops_indep_eq]; rw [isBase_iff_maximal_indep]

@[simp]
/--
lemma `removeLoops_isNonloop_eq` / 引理 `removeLoops_isNonloop_eq`

English:
lemma removeLoops_isNonloop_eq
  statement: M.removeLoops.IsNonloop = M.IsNonloop
  proof: by
  ext e
  rw [removeLoops_eq_restrict]; rw [restrict_isNonloop_iff]; rw [mem_ofPred]; rw [and_self]

中文:
引理 removeLoops_isNonloop_eq
  结论: M.removeLoops.是Nonloop = M.是Nonloop
  证明: by
  ext e
  rw [removeLoops_eq_restrict]; rw [restrict_isNonloop_iff]; rw [mem_ofPred]; rw [and_self]

Depends on / 依赖: and_self, mem_ofPred, removeLoops_eq_restrict, restrict_isNonloop_iff
-/
lemma removeLoops_isNonloop_eq : M.removeLoops.IsNonloop = M.IsNonloop := by
  ext e
  rw [removeLoops_eq_restrict]; rw [restrict_isNonloop_iff]; rw [mem_ofPred]; rw [and_self]

/--
lemma `IsNonloop.removeLoops_isNonloop` / 引理 `IsNonloop.removeLoops_isNonloop`

English:
lemma IsNonloop.removeLoops_isNonloop
  given: (he : M.IsNonloop e)
  statement: M.removeLoops.IsNonloop e
  proof: by
  simpa

中文:
引理 是Nonloop.removeLoops_isNonloop
  条件: (he : M.是Nonloop e)
  结论: M.removeLoops.是Nonloop e
  证明: by
  simpa
-/
lemma IsNonloop.removeLoops_isNonloop (he : M.IsNonloop e) : M.removeLoops.IsNonloop e := by
  simpa

/--
lemma `removeLoops_idem` / 引理 `removeLoops_idem`

English:
lemma removeLoops_idem
  given: (M : Matroid α)
  statement: M.removeLoops.removeLoops = M.removeLoops
  proof: by
  simp

中文:
引理 removeLoops_idem
  条件: (M : 拟阵 α)
  结论: M.removeLoops.removeLoops = M.removeLoops
  证明: by
  simp
-/
lemma removeLoops_idem (M : Matroid α) : M.removeLoops.removeLoops = M.removeLoops := by
  simp

/--
lemma `removeLoops_restrict_eq_restrict` / 引理 `removeLoops_restrict_eq_restrict`

English:
lemma removeLoops_restrict_eq_restrict
  given: (hX : X subseteq {e | M.IsNonloop e})
  proof: by
  rwa [removeLoops_eq_restrict, restrict_restrict_eq]

@[simp]

中文:
引理 removeLoops_restrict_eq_restrict
  条件: (hX : X subseteq {e | M.是Nonloop e})
  证明: by
  rwa [removeLoops_eq_restrict, restrict_restrict_eq]

@[simp]

Depends on / 依赖: removeLoops_eq_restrict, restrict_restrict_eq
-/
lemma removeLoops_restrict_eq_restrict (hX : X subseteq {e | M.IsNonloop e}) :
    M.removeLoops ↾ X = M ↾ X := by
  rwa [removeLoops_eq_restrict, restrict_restrict_eq]

@[simp]
/--
lemma `restrict_univ_removeLoops_eq` / 引理 `restrict_univ_removeLoops_eq`

English:
lemma restrict_univ_removeLoops_eq
  statement: (M ↾ univ).removeLoops = M.removeLoops
  proof: by
  rw [removeLoops_eq_restrict]; rw [restrict_restrict_eq _ (subset_univ _)]; rw [removeLoops_eq_restrict]
  simp

中文:
引理 restrict_univ_removeLoops_eq
  结论: (M ↾ univ).removeLoops = M.removeLoops
  证明: by
  rw [removeLoops_eq_restrict]; rw [restrict_restrict_eq _ (subset_univ _)]; rw [removeLoops_eq_restrict]
  simp

Depends on / 依赖: removeLoops_eq_restrict, restrict_restrict_eq, subset_univ
-/
lemma restrict_univ_removeLoops_eq : (M ↾ univ).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_restrict]; rw [restrict_restrict_eq _ (subset_univ _)]; rw [removeLoops_eq_restrict]
  simp

/--
lemma `IsRestriction.isRestriction_removeLoops` / 引理 `IsRestriction.isRestriction_removeLoops`

English:
lemma IsRestriction.isRestriction_removeLoops
  given: (hNM : N <=r M) [N.Loopless]
  statement: N <=r M.removeLoops
  proof: by
  obtain ⟨R, hR, rfl⟩ := hNM.exists_eq_restrict
  exact IsRestriction.of_subset M fun e heR => ((M ↾ R).isNonloop_of_loopless heR).of_restrict

中文:
引理 IsRestriction.isRestriction_removeLoops
  条件: (hNM : N <=r M) [N.无环]
  结论: N <=r M.removeLoops
  证明: by
  obtain ⟨R, hR, rfl⟩ := hNM.exists_eq_restrict
  exact IsRestriction.of_subset M fun e heR => ((M ↾ R).isNonloop_of_loopless heR).of_restrict

Depends on / 依赖: IsRestriction, IsRestriction.of_subset, exists_eq_restrict, hNM.exists_eq_restrict, isNonloop_of_loopless, of_restrict, of_subset
-/
lemma IsRestriction.isRestriction_removeLoops (hNM : N <=r M) [N.Loopless] : N <=r M.removeLoops := by
  obtain ⟨R, hR, rfl⟩ := hNM.exists_eq_restrict
  exact IsRestriction.of_subset M fun e heR => ((M ↾ R).isNonloop_of_loopless heR).of_restrict

/--
lemma `removeLoops_mono_isRestriction` / 引理 `removeLoops_mono_isRestriction`

English:
lemma removeLoops_mono_isRestriction
  given: (hNM : N <=r M)
  statement: N.removeLoops <=r M.removeLoops
  proof: ((removeLoops_isRestriction _).trans hNM).isRestriction_removeLoops

中文:
引理 removeLoops_mono_isRestriction
  条件: (hNM : N <=r M)
  结论: N.removeLoops <=r M.removeLoops
  证明: ((removeLoops_isRestriction _).trans hNM).isRestriction_removeLoops

Depends on / 依赖: isRestriction_removeLoops, removeLoops_isRestriction
-/
lemma removeLoops_mono_isRestriction (hNM : N <=r M) : N.removeLoops <=r M.removeLoops :=
  ((removeLoops_isRestriction _).trans hNM).isRestriction_removeLoops

end Loopless

end Matroid
