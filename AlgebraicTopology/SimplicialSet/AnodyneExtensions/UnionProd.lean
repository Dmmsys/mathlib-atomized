/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# A pairing for the pushout-product of a horn inclusion and a boundary inclusion

Let `l : Fin (m + 2)` and `n : ℕ`. In this file, we construct a regular pairing
for the subcomplex `unionProd Λ[m + 1, l] ∂Δ[n]` of `Δ[m + 1] ⊗ Δ[n]`. It follows
immediately that the inclusion of the union of `Λ[m + 1, l] ⊗ Δ[n]` and
`Δ[m + 1] ⊗ ∂Δ[n]` in `Δ[m + 1] ⊗ Δ[n]` is a (strong) anodyne extension
(which is inner when `l ≠ 0` and `l ≠ Fin.last _`).

The main construction works only when `l ≠ Fin.last _`, i.e. `l = k.castSucc`
for `k : Fin (m + 1)`: the remaining case is obtained using symmetries and
the case `k = 0`.

In order to do the case of `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]` for `k : Fin (m + 1)`,
we follow the proof by Sean Moss. Let us consider a nondegenerate `d`-simplex `x` of
`Δ[m + 1] ⊗ Δ[n]` which does not belong to `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`.
`x` can be thought as a "walk" on the vertices `{0, ..., m + 1} × {0, ..., n}`
of `Δ[m + 1] ⊗ Δ[n]` (this is actually a strictly monotone map
`Fin (d + 1) → Fin (m + 2) × Fin (n + 1)`).
The condition that `x` does not belong to `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
translates by saying that `x` reaches all the rows
(see the lemma `prodStdSimplex.pairingCore.mem_range_right`)
and all the columns expect the `k.castSucc`-th
(see the lemma `prodStdSimplex.pairingCore.mem_range_left`). This puts
constraints for each `i` on the vector from `x i` to `x (i + 1)`:
it has to be `(0, 1)`, `(1,0)`, `(1,1)`, `(2, 0)` or `(2, 1)` (the last two
cases may appear only if the `k.castSucc`-th column is skipped).
We introduce a predicate `IsIndex` taking `x` and `l : Fin (d + 1)` as arguments
and which is satisfied if `l` is the smallest `i` such that `x l` is
in the `k.succ` column, `l ≠ 0`, and the vector from `x (l.pred _)` to `x l`
is exactly `(1, 0)`.

The type (I) simplices for the pairing are those `x` such that there exists `l`
such that the predicate `IsIndex` hold. The corresponding type (II) simplex
is obtained by removing `x (l.pred _)` from the walk.


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

namespace prodStdSimplex

variable {m : Nat} {k : Fin (m + 1)} {n : Nat}
  (x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N) {d : Nat}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `objEquiv_apply_fst'` / 引理 `objEquiv_apply_fst'`

English:
lemma objEquiv_apply_fst'
  given: (hd : x.dim = d) (i : Fin (d + 1))
  proof: rfl

#adaptation_note

中文:
引理 objEquiv_apply_fst'
  条件: (hd : x.dim = d) (i : 有限集 (d + 1))
  证明: rfl

#adaptation_note
-/
lemma objEquiv_apply_fst' (hd : x.dim = d) (i : Fin (d + 1)) :
    dsimp% ((objEquiv (x.cast hd).simplex) i).1 = (x.cast hd).simplex.1 i := rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `objEquiv_apply_snd'` / 引理 `objEquiv_apply_snd'`

English:
lemma objEquiv_apply_snd'
  given: (hd : x.dim = d) (i : Fin (d + 1))
  proof: rfl

中文:
引理 objEquiv_apply_snd'
  条件: (hd : x.dim = d) (i : 有限集 (d + 1))
  证明: rfl
-/
lemma objEquiv_apply_snd' (hd : x.dim = d) (i : Fin (d + 1)) :
    dsimp% ((objEquiv (x.cast hd).simplex) i).2 = (x.cast hd).simplex.2 i := rfl

namespace pairingCore

section

variable (hd : x.dim = d)

/--
Definition of `IsIndex` / `IsIndex` 的定义

English:
definition IsIndex
  signature: : Fin (d + 1) -> Prop
  body: Fin.cases False (fun l =>
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
    (x.cast hd).simplex.1 l.succ = k.succ ∧
    (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc)

@[simp]

中文:
定义 IsIndex
  签名: : 有限集 (d + 1) -> 命题
  定义体: Fin.cases False (fun l =>
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
    (x.cast hd).simplex.1 l.succ = k.succ ∧
    (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc)

@[simp]

Depends on / 依赖: Fin.cases, castSucc, k.castSucc, k.succ, l.castSucc, l.succ, simplex, x.cast
-/
def IsIndex : Fin (d + 1) -> Prop :=
  Fin.cases False (fun l =>
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
    (x.cast hd).simplex.1 l.succ = k.succ ∧
    (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc)

@[simp]
/--
lemma `isIndex_zero` / 引理 `isIndex_zero`

English:
lemma isIndex_zero
  statement: IsIndex x hd 0 ↔ False
  proof: Iff.rfl

中文:
引理 isIndex_zero
  结论: IsIndex x hd 0 ↔ 假
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isIndex_zero : IsIndex x hd 0 ↔ False := Iff.rfl

/--
lemma `isIndex_succ` / 引理 `isIndex_succ`

English:
lemma isIndex_succ
  given: (l : Fin d)
  proof: Iff.rfl

中文:
引理 isIndex_succ
  条件: (l : 有限集 d)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isIndex_succ (l : Fin d) :
    IsIndex x hd l.succ ↔
      (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
      (x.cast hd).simplex.1 l.succ = k.succ ∧
      (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc := Iff.rfl

/--
lemma `mem_range_left` / 引理 `mem_range_left`

English:
lemma mem_range_left
  given: (i : Fin (m + 2)) (hi : i != k.castSucc)
  proof: by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range] at this
  tauto

中文:
引理 mem_range_left
  条件: (i : 有限集 (m + 2)) (hi : i != k.castSucc)
  证明: by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range] at this
  tauto

Depends on / 依赖: Subcomplex, Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range, mem_unionProd_iff, notMem, x.notMem
-/
lemma mem_range_left (i : Fin (m + 2)) (hi : i != k.castSucc) :
    i in Set.range (x.cast hd).simplex.1 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range] at this
  tauto

/--
lemma `mem_range_right` / 引理 `mem_range_right`

English:
lemma mem_range_right
  given: (i : Fin (n + 1))
  proof: by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range] at this
  tauto

中文:
引理 mem_range_right
  条件: (i : 有限集 (n + 1))
  证明: by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range] at this
  tauto

Depends on / 依赖: Subcomplex, Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range, mem_unionProd_iff, notMem, x.notMem
-/
lemma mem_range_right (i : Fin (n + 1)) :
    i in Set.range (x.cast hd).simplex.2 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range] at this
  tauto

/--
Definition of `finset` / `finset` 的定义

English:
definition finset
  signature: : Finset (Fin (d + 1))
  body: { l : Fin (d + 1) | (x.cast hd).simplex.1 l = k.succ }

@[simp]

中文:
定义 finset
  签名: : 有限集 (有限集 (d + 1))
  定义体: { l : Fin (d + 1) | (x.cast hd).simplex.1 l = k.succ }

@[simp]

Depends on / 依赖: k.succ, simplex, x.cast
-/
noncomputable def finset : Finset (Fin (d + 1)) :=
  { l : Fin (d + 1) | (x.cast hd).simplex.1 l = k.succ }

@[simp]
/--
lemma `mem_finset_iff` / 引理 `mem_finset_iff`

English:
lemma mem_finset_iff
  given: (l : Fin (d + 1))
  proof: by
  simp [finset]

中文:
引理 mem_finset_iff
  条件: (l : 有限集 (d + 1))
  证明: by
  simp [finset]

Depends on / 依赖: finset
-/
lemma mem_finset_iff (l : Fin (d + 1)) :
    dsimp% l in finset x hd ↔ (x.cast hd).simplex.1 l = k.succ := by
  simp [finset]

/--
lemma `nonempty_finset` / 引理 `nonempty_finset`

English:
lemma nonempty_finset
  statement: (finset x hd).Nonempty
  proof: by
  obtain ⟨i, hi⟩ := mem_range_left x hd k.succ (by grind)
  exact ⟨i, by simpa using hi⟩

中文:
引理 nonempty_finset
  结论: (finset x hd).非空
  证明: by
  obtain ⟨i, hi⟩ := mem_range_left x hd k.succ (by grind)
  exact ⟨i, by simpa using hi⟩

Depends on / 依赖: k.succ, mem_range_left
-/
lemma nonempty_finset : (finset x hd).Nonempty := by
  obtain ⟨i, hi⟩ := mem_range_left x hd k.succ (by grind)
  exact ⟨i, by simpa using hi⟩

/--
Definition of `min` / `min` 的定义

English:
definition min
  signature: : Fin (d + 1)
  body: (finset x hd).min' (nonempty_finset x hd)

中文:
定义 最小值
  签名: : 有限集 (d + 1)
  定义体: (finset x hd).min' (nonempty_finset x hd)

Depends on / 依赖: finset, nonempty_finset
-/
noncomputable def min : Fin (d + 1) := (finset x hd).min' (nonempty_finset x hd)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `simplex_fst_min` / 引理 `simplex_fst_min`

English:
lemma simplex_fst_min
  statement: dsimp% (x.cast hd).simplex.1 (min x hd) = k.succ
  proof: by
  rw [← mem_finset_iff]
  apply Finset.min'_mem

中文:
引理 simplex_fst_min
  结论: dsimp% (x.cast hd).simplex.1 (最小值 x hd) = k.succ
  证明: by
  rw [← mem_finset_iff]
  apply Finset.min'_mem

Depends on / 依赖: Finset, Finset.min, _mem, mem_finset_iff
-/
lemma simplex_fst_min : dsimp% (x.cast hd).simplex.1 (min x hd) = k.succ := by
  rw [← mem_finset_iff]
  apply Finset.min'_mem

set_option backward.isDefEq.respectTransparency false in
/--
lemma `simplex_fst_le_castSucc_iff` / 引理 `simplex_fst_le_castSucc_iff`

English:
lemma simplex_fst_le_castSucc_iff
  given: (i : Fin (d + 1))
  proof: by
  contrapose!
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | h := h.lt_or_eq
    · by_contra! h'
      have := stdSimplex.monotone_apply (x.cast hd).simplex.1 h'.le
      dsimp at this
      rw [simplex_fst_min]; rw [← not_lt] at this
      tauto
    

中文:
引理 simplex_fst_le_castSucc_iff
  条件: (i : 有限集 (d + 1))
  证明: by
  contrapose!
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | h := h.lt_or_eq
    · by_contra! h'
      have := stdSimplex.monotone_apply (x.cast hd).simplex.1 h'.le
      dsimp at this
      rw [simplex_fst_min]; rw [← not_lt] at this
      tauto
    

Depends on / 依赖: Fin.castSucc_lt_iff_succ_le, Finset, Finset.min, castSucc_lt_iff_succ_le, contrapose, h.lt_or_eq, h.symm, lt_or_eq, monotone_apply, not_lt, simplex, simplex_fst_min, stdSimplex, stdSimplex.monotone_apply, x.cast
-/
lemma simplex_fst_le_castSucc_iff (i : Fin (d + 1)) :
    dsimp% (x.cast hd).simplex.1 i <= k.castSucc ↔ i < min x hd := by
  contrapose!
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | h := h.lt_or_eq
    · by_contra! h'
      have := stdSimplex.monotone_apply (x.cast hd).simplex.1 h'.le
      dsimp at this
      rw [simplex_fst_min]; rw [← not_lt] at this
      tauto
    · exact Finset.min'_le _ _ (by simpa using h.symm)
  · rw [Fin.castSucc_lt_iff_succ_le, ← simplex_fst_min x hd]
    exact stdSimplex.monotone_apply _ h

end

namespace IsIndex

section

variable {x} {hd : x.dim = d} {l : Fin d} (hl : IsIndex x hd l.succ)

include hl

/--
lemma `simplex_fst_castSucc` / 引理 `simplex_fst_castSucc`

English:
lemma simplex_fst_castSucc
  proof: hl.1

中文:
引理 simplex_fst_castSucc
  证明: hl.1
-/
lemma simplex_fst_castSucc :
    dsimp% (x.cast hd).simplex.1 l.castSucc = k.castSucc := hl.1

/--
lemma `simplex_fst_succ` / 引理 `simplex_fst_succ`

English:
lemma simplex_fst_succ
  proof: hl.2.1

中文:
引理 simplex_fst_succ
  证明: hl.2.1
-/
lemma simplex_fst_succ :
    dsimp% (x.cast hd).simplex.1 l.succ = k.succ := hl.2.1

/--
lemma `simplex_snd_succ` / 引理 `simplex_snd_succ`

English:
lemma simplex_snd_succ
  proof: hl.2.2

中文:
引理 simplex_snd_succ
  证明: hl.2.2
-/
lemma simplex_snd_succ :
    dsimp% (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc := hl.2.2

/--
lemma `succ_le_simplex_fst_iff` / 引理 `succ_le_simplex_fst_iff`

English:
lemma succ_le_simplex_fst_iff
  given: (i : Fin (d + 1))
  proof: by
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · by_contra!
    rw [← not_lt] at hi
    apply hi
    rw [← Fin.le_castSucc_iff] at this ⊢
    conv_rhs => rw [← hl.simplex_fst_castSucc]
    exact stdSimplex.monotone_apply _ this
  · rw [← hl.simplex_fst_succ]
    exact stdSimplex.monotone_apply _ hi

中文:
引理 succ_le_simplex_fst_iff
  条件: (i : 有限集 (d + 1))
  证明: by
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · by_contra!
    rw [← not_lt] at hi
    apply hi
    rw [← Fin.le_castSucc_iff] at this ⊢
    conv_rhs => rw [← hl.simplex_fst_castSucc]
    exact stdSimplex.monotone_apply _ this
  · rw [← hl.simplex_fst_succ]
    exact stdSimplex.monotone_apply _ hi

Depends on / 依赖: Fin.le_castSucc_iff, conv_rhs, hl.simplex_fst_castSucc, hl.simplex_fst_succ, le_castSucc_iff, monotone_apply, not_lt, simplex_fst_castSucc, simplex_fst_succ, stdSimplex, stdSimplex.monotone_apply
-/
lemma succ_le_simplex_fst_iff (i : Fin (d + 1)) :
    dsimp% k.succ <= (x.cast hd).simplex.1 i ↔ l.succ <= i := by
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · by_contra!
    rw [← not_lt] at hi
    apply hi
    rw [← Fin.le_castSucc_iff] at this ⊢
    conv_rhs => rw [← hl.simplex_fst_castSucc]
    exact stdSimplex.monotone_apply _ this
  · rw [← hl.simplex_fst_succ]
    exact stdSimplex.monotone_apply _ hi

/--
lemma `simplex_fst_le_castSucc_iff` / 引理 `simplex_fst_le_castSucc_iff`

English:
lemma simplex_fst_le_castSucc_iff
  given: (i : Fin (d + 1))
  proof: by
  rw [Fin.le_castSucc_iff]; rw [← not_le]; rw [hl.succ_le_simplex_fst_iff]; rw [not_le]

中文:
引理 simplex_fst_le_castSucc_iff
  条件: (i : 有限集 (d + 1))
  证明: by
  rw [Fin.le_castSucc_iff]; rw [← not_le]; rw [hl.succ_le_simplex_fst_iff]; rw [not_le]

Depends on / 依赖: Fin.le_castSucc_iff, hl.succ_le_simplex_fst_iff, le_castSucc_iff, not_le, succ_le_simplex_fst_iff
-/
lemma simplex_fst_le_castSucc_iff (i : Fin (d + 1)) :
    dsimp% (x.cast hd).simplex.1 i <= k.castSucc ↔ i < l.succ := by
  rw [Fin.le_castSucc_iff]; rw [← not_le]; rw [hl.succ_le_simplex_fst_iff]; rw [not_le]

/--
lemma `min_eq` / 引理 `min_eq`

English:
lemma min_eq
  statement: min x hd = l.succ
  proof: le_antisymm (Finset.min'_le _ _ (by simpa using hl.simplex_fst_succ))
    ((Finset.le_min'_iff _ _ ).2 (fun i hi => by
      rw [mem_finset_iff] at hi
      simp [← hl.succ_le_simplex_fst_iff, ← hi]))

中文:
引理 min_eq
  结论: 最小值 x hd = l.succ
  证明: le_antisymm (Finset.min'_le _ _ (by simpa using hl.simplex_fst_succ))
    ((Finset.le_min'_iff _ _ ).2 (fun i hi => by
      rw [mem_finset_iff] at hi
      simp [← hl.succ_le_simplex_fst_iff, ← hi]))

Depends on / 依赖: Finset, Finset.le_min, Finset.min, _iff, hl.simplex_fst_succ, hl.succ_le_simplex_fst_iff, le_antisymm, le_min, mem_finset_iff, simplex_fst_succ, succ_le_simplex_fst_iff
-/
lemma min_eq : min x hd = l.succ :=
  le_antisymm (Finset.min'_le _ _ (by simpa using hl.simplex_fst_succ))
    ((Finset.le_min'_iff _ _ ).2 (fun i hi => by
      rw [mem_finset_iff] at hi
      simp [← hl.succ_le_simplex_fst_iff, ← hi]))

/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  given: {l' : Fin d} (hl' : IsIndex x hd l'.succ)
  statement: l = l'
  proof: by
  rw [← Fin.succ_inj]; rw [← hl.min_eq]; rw [hl'.min_eq]

中文:
引理 unique
  条件: {l' : 有限集 d} (hl' : IsIndex x hd l'.succ)
  结论: l = l'
  证明: by
  rw [← Fin.succ_inj]; rw [← hl.min_eq]; rw [hl'.min_eq]

Depends on / 依赖: Fin.succ_inj, hl.min_eq, min_eq, succ_inj
-/
lemma unique {l' : Fin d} (hl' : IsIndex x hd l'.succ) : l = l' := by
  rw [← Fin.succ_inj]; rw [← hl.min_eq]; rw [hl'.min_eq]

end

section

variable {x} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

set_option backward.isDefEq.respectTransparency.types false in
/-- The type (II) simplex obtained as a face of a type (I) simplex. -/
@[simps -isSimp]
/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: :
  body: d
  simplex := (Δ[m + 1] otimes Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ (x.cast hd).nonDegenerate _
  notMem := by
    dsimp
    -- `simp? [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range,
    -- mem_horn_iff_notMem_range,stdSimplex.δ_apply]` says:
    s

中文:
缩写 δ
  签名: :
  定义体: d
  simplex := (Δ[m + 1] otimes Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ (x.cast hd).nonDegenerate _
  notMem := by
    dsimp
    -- `simp? [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range,
    -- mem_horn_iff_notMem_range,stdSimplex.δ_apply]` says:
    s
-/
noncomputable abbrev δ :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N where
  dim := d
  simplex := (Δ[m + 1] otimes Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ (x.cast hd).nonDegenerate _
  notMem := by
    dsimp
    -- `simp? [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range,
    -- mem_horn_iff_notMem_range,stdSimplex.δ_apply]` says:
    simp only [Subcomplex.mem_unionProd_iff, prod_δ_snd, mem_boundary_iff_notMem_range,
      Set.mem_range, stdSimplex.δ_apply, not_exists, prod_δ_fst, mem_horn_iff_notMem_range,
      ne_eq, exists_prop, not_or, not_forall, Decidable.not_not, not_and]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · obtain ⟨i, hi⟩ := mem_range_right x hd j
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · refine ⟨l, ?_⟩
        rw [Fin.succAbove_castSucc_self]; rw [← hi]; rw [← hl.simplex_snd_succ]
        rfl
      · exact ⟨_, hi⟩
    · obtain ⟨i, hi⟩ := mem_range_left x hd j hj
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · exact (hj (by rw [← hi, hl.simplex_fst_castSucc])).elim
      · exact ⟨_, hi⟩

end

end IsIndex

variable (k n) in
/--
Definition of `Type₁` / `Type₁` 的定义

English:
structure Type₁
  parameters: where
  axioms and operations (5):
    - x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N
    - d : Nat
    - hd : x.dim = d + 1
    - index : Fin (d + 1)
    - isIndex : IsIndex x hd index.succ

中文:
结构 Type₁
  参数: where
  公理与运算 (5 个):
    - x : (子复形.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N
    - d : 自然数
    - hd : x.dim = d + 1
    - index : 有限集 (d + 1)
    - isIndex : IsIndex x hd index.succ
-/
structure Type₁ where
  /-- the nondegenerate simplex -/
  x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N
  /-- the dimension of the 1-codimensional face -/
  d : Nat
  hd : x.dim = d + 1
  /-- the index attached to the corresponding type (II) simplex -/
  index : Fin (d + 1)
  isIndex : IsIndex x hd index.succ

variable {x} in
/-- Constructor for `Type₁ k n`. -/
@[simps]
/--
Definition of `IsIndex.type₁` / `IsIndex.type₁` 的定义

English:
definition IsIndex.type₁
  signature: {hd : x.dim = d + 1} {i : Fin (d + 1)}
  body: x
  d := d
  hd := hd
  index := i
  isIndex := h

中文:
定义 IsIndex.type₁
  签名: {hd : x.dim = d + 1} {i : 有限集 (d + 1)}
  定义体: x
  d := d
  hd := hd
  index := i
  isIndex := h
-/
def IsIndex.type₁ {hd : x.dim = d + 1} {i : Fin (d + 1)}
    (h : IsIndex x hd i.succ) : Type₁.{u} k n where
  x := x
  d := d
  hd := hd
  index := i
  isIndex := h

namespace Type₁

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: {s t : Type₁.{u} k n}
  proof: by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have hs := s.isIndex.min_eq
  have ht := t.isIndex.min_eq
  obtain ⟨x, d, hd, l, isIndex⟩ := s
  obtain ⟨y, d', hd', l', isIndex'⟩ := t
  subst h
  obtain rfl : d = d' := by grind
  obtain rfl : l = l' := by grind
  dsimp

中文:
引理 ext_iff
  条件: {s t : Type₁.{u} k n}
  证明: by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have hs := s.isIndex.min_eq
  have ht := t.isIndex.min_eq
  obtain ⟨x, d, hd, l, isIndex⟩ := s
  obtain ⟨y, d', hd', l', isIndex'⟩ := t
  subst h
  obtain rfl : d = d' := by grind
  obtain rfl : l = l' := by grind
  dsimp

Depends on / 依赖: isIndex, min_eq, s.isIndex.min_eq, t.isIndex.min_eq
-/
lemma ext_iff {s t : Type₁.{u} k n} :
    s = t ↔ s.x = t.x := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have hs := s.isIndex.min_eq
  have ht := t.isIndex.min_eq
  obtain ⟨x, d, hd, l, isIndex⟩ := s
  obtain ⟨y, d', hd', l', isIndex'⟩ := t
  subst h
  obtain rfl : d = d' := by grind
  obtain rfl : l = l' := by grind
  dsimp

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: (s : Type₁.{u} k n)
  body: s.isIndex.δ

中文:
缩写 δ
  签名: (s : Type₁.{u} k n)
  定义体: s.isIndex.δ

Depends on / 依赖: isIndex, s.isIndex
-/
noncomputable abbrev δ (s : Type₁.{u} k n) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N :=
  s.isIndex.δ

end Type₁

/--
Definition of `IsType₂` / `IsType₂` 的定义

English:
definition IsType₂
  signature: : Prop
  body: forall (d : Nat) (hd : x.dim = d) (l : Fin (d + 1)), ¬ IsIndex x hd l

中文:
定义 IsType₂
  签名: : 命题
  定义体: forall (d : Nat) (hd : x.dim = d) (l : Fin (d + 1)), ¬ IsIndex x hd l

Depends on / 依赖: IsIndex, x.dim
-/
def IsType₂ : Prop :=
  forall (d : Nat) (hd : x.dim = d) (l : Fin (d + 1)), ¬ IsIndex x hd l

namespace IsType₂

variable (hx : IsType₂ x) {d : Nat} (hd : x.dim = d)

/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: (i : Fin (d + 2))
  body: if i = (min x hd).castSucc
  then ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩
  else objEquiv (x.cast hd).simplex ((min x hd).predAbove i)

@[simp]

中文:
定义 φ
  签名: (i : 有限集 (d + 2))
  定义体: if i = (min x hd).castSucc
  then ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩
  else objEquiv (x.cast hd).simplex ((min x hd).predAbove i)

@[simp]

Depends on / 依赖: castSucc, k.castSucc, objEquiv, predAbove, simplex, x.cast
-/
noncomputable def φ (i : Fin (d + 2)) : Fin (m + 2) × Fin (n + 1) :=
  if i = (min x hd).castSucc
  then ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩
  else objEquiv (x.cast hd).simplex ((min x hd).predAbove i)

@[simp]
/--
lemma `φ_castSucc` / 引理 `φ_castSucc`

English:
lemma φ_castSucc
  proof: by
  simp [φ]

@[simp]

中文:
引理 φ_castSucc
  证明: by
  simp [φ]

@[simp]
-/
lemma φ_castSucc :
    φ x hd (min x hd).castSucc = ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩ := by
  simp [φ]

@[simp]
/--
lemma `φ_succAbove` / 引理 `φ_succAbove`

English:
lemma φ_succAbove
  given: (i : Fin (d + 1))
  proof: by
  simp [φ]

中文:
引理 φ_succAbove
  条件: (i : 有限集 (d + 1))
  证明: by
  simp [φ]
-/
lemma φ_succAbove (i : Fin (d + 1)) :
    φ x hd ((min x hd).castSucc.succAbove i) =
      objEquiv (x.cast hd).simplex i := by
  simp [φ]

/--
lemma `φ_of_ne` / 引理 `φ_of_ne`

English:
lemma φ_of_ne
  given: (i : Fin (d + 2)) (hi : i != (min x hd).castSucc)
  proof: if_neg hi

中文:
引理 φ_of_ne
  条件: (i : 有限集 (d + 2)) (hi : i != (最小值 x hd).castSucc)
  证明: if_neg hi

Depends on / 依赖: if_neg
-/
lemma φ_of_ne (i : Fin (d + 2)) (hi : i != (min x hd).castSucc) :
    φ x hd i = objEquiv (x.cast hd).simplex ((min x hd).predAbove i) :=
  if_neg hi

/--
lemma `φ_of_lt` / 引理 `φ_of_lt`

English:
lemma φ_of_lt
  given: (i : Fin (d + 2)) (hi : i < (min x hd).castSucc)
  proof: by
  rw [φ_of_ne _ _ _ hi.ne]; rw [Fin.predAbove_of_le_castSucc _ _ hi.le]

中文:
引理 φ_of_lt
  条件: (i : 有限集 (d + 2)) (hi : i < (最小值 x hd).castSucc)
  证明: by
  rw [φ_of_ne _ _ _ hi.ne]; rw [Fin.predAbove_of_le_castSucc _ _ hi.le]

Depends on / 依赖: Fin.predAbove_of_le_castSucc, hi.le, hi.ne, predAbove_of_le_castSucc
-/
lemma φ_of_lt (i : Fin (d + 2)) (hi : i < (min x hd).castSucc) :
    φ x hd i = objEquiv (x.cast hd).simplex (i.castPred (by grind)) := by
  rw [φ_of_ne _ _ _ hi.ne]; rw [Fin.predAbove_of_le_castSucc _ _ hi.le]

/--
lemma `φ_of_gt` / 引理 `φ_of_gt`

English:
lemma φ_of_gt
  given: (i : Fin (d + 2)) (hi : (min x hd).castSucc < i)
  proof: by
  rw [φ_of_ne _ _ _ hi.ne']; rw [Fin.predAbove_of_castSucc_lt _ _ hi]

中文:
引理 φ_of_gt
  条件: (i : 有限集 (d + 2)) (hi : (最小值 x hd).castSucc < i)
  证明: by
  rw [φ_of_ne _ _ _ hi.ne']; rw [Fin.predAbove_of_castSucc_lt _ _ hi]

Depends on / 依赖: Fin.predAbove_of_castSucc_lt, hi.ne, predAbove_of_castSucc_lt
-/
lemma φ_of_gt (i : Fin (d + 2)) (hi : (min x hd).castSucc < i) :
    φ x hd i = objEquiv (x.cast hd).simplex (i.pred (by aesop)) := by
  rw [φ_of_ne _ _ _ hi.ne']; rw [Fin.predAbove_of_castSucc_lt _ _ hi]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `φ_succ_snd` / 引理 `φ_succ_snd`

English:
lemma φ_succ_snd
  statement: (φ x hd (min x hd).succ).2 = (φ x hd (min x hd).castSucc).2
  proof: by
  have := φ_succAbove x hd (min x hd)
  simp_all [φ_castSucc]

中文:
引理 φ_succ_snd
  结论: (φ x hd (最小值 x hd).succ).2 = (φ x hd (最小值 x hd).castSucc).2
  证明: by
  have := φ_succAbove x hd (min x hd)
  simp_all [φ_castSucc]
-/
lemma φ_succ_snd : (φ x hd (min x hd).succ).2 = (φ x hd (min x hd).castSucc).2 := by
  have := φ_succAbove x hd (min x hd)
  simp_all [φ_castSucc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `φ_succ_fst` / 引理 `φ_succ_fst`

English:
lemma φ_succ_fst
  statement: (φ x hd (min x hd).succ).1 = k.succ
  proof: by
  have := φ_succAbove x hd (min x hd)
  simp_all [simplex_fst_min x hd]

中文:
引理 φ_succ_fst
  结论: (φ x hd (最小值 x hd).succ).1 = k.succ
  证明: by
  have := φ_succAbove x hd (min x hd)
  simp_all [simplex_fst_min x hd]

Depends on / 依赖: simplex_fst_min
-/
lemma φ_succ_fst : (φ x hd (min x hd).succ).1 = k.succ := by
  have := φ_succAbove x hd (min x hd)
  simp_all [simplex_fst_min x hd]

variable {x}

include hx in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `strictMono_φ` / 引理 `strictMono_φ`

English:
lemma strictMono_φ
  statement: StrictMono (φ x hd)
  proof: by
  have hx' := (prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain hi | rfl | hi := lt_trichotomy i (min x hd)
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
    rw [φ_of_lt _ _ _ (b

中文:
引理 strictMono_φ
  结论: 严格递增 (φ x hd)
  证明: by
  have hx' := (prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain hi | rfl | hi := lt_trichotomy i (min x hd)
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
    rw [φ_of_lt _ _ _ (b

Depends on / 依赖: Fin.castPred_castSucc, Fin.castSucc_lt_iff_succ_le, Fin.castSucc_succ, Fin.eq_castSucc_of_ne_last, Fin.lt_def, Fin.ne_last_of_lt, Fin.strictMono_iff_lt_succ, castPred_castSucc, castSucc_lt_iff_succ_le, castSucc_succ, eq_castSucc_of_ne_last, hi.lt_or_eq, lt_def, lt_or_eq, lt_trichotomy, ne_last_of_lt, nonDegenerate, nonDegenerate_iff_strictMono_objEquiv, prodStdSimplex, prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv
-/
lemma strictMono_φ : StrictMono (φ x hd) := by
  have hx' := (prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain hi | rfl | hi := lt_trichotomy i (min x hd)
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
    rw [φ_of_lt _ _ _ (by grind)]; rw [Fin.castPred_castSucc]
    rw [Fin.castSucc_lt_iff_succ_le] at hi
    obtain hi | hi := hi.lt_or_eq
    · rw [φ_of_lt _ _ _ (by grind)]
      exact hx' (Fin.lt_def.2 (by dsimp; grind))
    · rw [← Fin.castSucc_succ, hi, φ_castSucc]
      refine lt_of_le_of_ne ⟨?_, ?_⟩ ?_
      · dsimp
        rw [simplex_fst_le_castSucc_iff]
        grind
      · exact stdSimplex.monotone_apply _
          (by dsimp; rw [← hi]; exact Fin.castSucc_le_succ i)
      · intro h
        rw [Prod.ext_iff] at h
        dsimp at h
        obtain ⟨h₁, h₂⟩ := h
        apply hx _ hd i.succ
        rw [isIndex_succ]
        refine ⟨h₁, ?_, by aesop⟩
        have := φ_succAbove x hd (min x hd)
        rw [Fin.succAbove_castSucc_self] at this
        rw [← φ_succ_fst x hd]; rw [this]; rw [hi]
        dsimp
  · exact Prod.lt_of_lt_of_le (by simp) (by simp)
  · rw [φ_of_gt _ _ _ (by grind), φ_of_gt _ _ _ (by grind)]
    exact hx' (by grind)

/--
Definition of `simplex` / `simplex` 的定义

English:
abbreviation simplex
  signature: : (Δ[m + 1] otimes Δ[n]) _⦋d + 1⦌
  body: (objEquiv.{u}.symm ⟨φ x hd, (hx.strictMono_φ hd).monotone⟩)

@[simp]

中文:
缩写 simplex
  签名: : (Δ[m + 1] otimes Δ[n]) _⦋d + 1⦌
  定义体: (objEquiv.{u}.symm ⟨φ x hd, (hx.strictMono_φ hd).monotone⟩)

@[simp]

Depends on / 依赖: hx.strictMono_, monotone, objEquiv
-/
noncomputable abbrev simplex : (Δ[m + 1] otimes Δ[n]) _⦋d + 1⦌ :=
  (objEquiv.{u}.symm ⟨φ x hd, (hx.strictMono_φ hd).monotone⟩)

@[simp]
/--
lemma `simplex_fst_apply` / 引理 `simplex_fst_apply`

English:
lemma simplex_fst_apply
  given: (i : Fin (d + 2))
  proof: rfl

@[simp]

中文:
引理 simplex_fst_apply
  条件: (i : 有限集 (d + 2))
  证明: rfl

@[simp]
-/
lemma simplex_fst_apply (i : Fin (d + 2)) :
    (hx.simplex hd).1 i = (φ x hd i).1 := rfl

@[simp]
/--
lemma `simplex_snd_apply` / 引理 `simplex_snd_apply`

English:
lemma simplex_snd_apply
  given: (i : Fin (d + 2))
  proof: rfl

中文:
引理 simplex_snd_apply
  条件: (i : 有限集 (d + 2))
  证明: rfl
-/
lemma simplex_snd_apply (i : Fin (d + 2)) :
    (hx.simplex hd).2 i = (φ x hd i).2 := rfl

/--
lemma `simplex_mem_nonDegenerate` / 引理 `simplex_mem_nonDegenerate`

English:
lemma simplex_mem_nonDegenerate
  proof: by
  rw [nonDegenerate_iff_strictMono_objEquiv]; rw [Equiv.apply_symm_apply]
  exact hx.strictMono_φ hd

中文:
引理 simplex_mem_nonDegenerate
  证明: by
  rw [nonDegenerate_iff_strictMono_objEquiv]; rw [Equiv.apply_symm_apply]
  exact hx.strictMono_φ hd

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, hx.strictMono_, nonDegenerate_iff_strictMono_objEquiv
-/
lemma simplex_mem_nonDegenerate :
    hx.simplex hd in (Δ[m + 1] otimes Δ[n]).nonDegenerate (d + 1) := by
  rw [nonDegenerate_iff_strictMono_objEquiv]; rw [Equiv.apply_symm_apply]
  exact hx.strictMono_φ hd

/--
lemma `δ_simplex` / 引理 `δ_simplex`

English:
lemma δ_simplex
  proof: by
  apply objEquiv.injective
  ext i : 2
  dsimp only [simplex]
  rw [objEquiv_δ_apply]; rw [Equiv.apply_symm_apply]; rw [OrderHom.coe_mk]; rw [φ_succAbove]

中文:
引理 δ_simplex
  证明: by
  apply objEquiv.injective
  ext i : 2
  dsimp only [simplex]
  rw [objEquiv_δ_apply]; rw [Equiv.apply_symm_apply]; rw [OrderHom.coe_mk]; rw [φ_succAbove]

Depends on / 依赖: Equiv.apply_symm_apply, OrderHom, OrderHom.coe_mk, apply_symm_apply, coe_mk, injective, objEquiv, objEquiv.injective, simplex
-/
lemma δ_simplex :
    (Δ[m + 1] otimes Δ[n]).δ (min x hd).castSucc (hx.simplex hd) = (x.cast hd).simplex := by
  apply objEquiv.injective
  ext i : 2
  dsimp only [simplex]
  rw [objEquiv_δ_apply]; rw [Equiv.apply_symm_apply]; rw [OrderHom.coe_mk]; rw [φ_succAbove]

/--
lemma `notMem_simplex` / 引理 `notMem_simplex`

English:
lemma notMem_simplex
  proof: by
  refine fun h => (x.cast hd).notMem ?_
  rw [← hx.δ_simplex hd]
  exact (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).map
    (SimplexCategory.δ (min x hd).castSucc).op h

中文:
引理 notMem_simplex
  证明: by
  refine fun h => (x.cast hd).notMem ?_
  rw [← hx.δ_simplex hd]
  exact (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).map
    (SimplexCategory.δ (min x hd).castSucc).op h

Depends on / 依赖: SimplexCategory, Subcomplex, Subcomplex.unionProd, castSucc, k.castSucc, notMem, unionProd, x.cast
-/
lemma notMem_simplex :
    hx.simplex hd ∉ (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).obj _ := by
  refine fun h => (x.cast hd).notMem ?_
  rw [← hx.δ_simplex hd]
  exact (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).map
    (SimplexCategory.δ (min x hd).castSucc).op h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The type (I) simplex reconstructed from a type (II) simplex. -/
@[simps]
/--
Definition of `type₁` / `type₁` 的定义

English:
definition type₁
  signature: : Type₁ k n where
  body: Subcomplex.N.mk (hx.simplex hd) (hx.simplex_mem_nonDegenerate hd)
      (hx.notMem_simplex hd)
  d := d
  hd := rfl
  index := min x hd
  isIndex := by simp [isIndex_succ]

中文:
定义 type₁
  签名: : Type₁ k n where
  定义体: Subcomplex.N.mk (hx.simplex hd) (hx.simplex_mem_nonDegenerate hd)
      (hx.notMem_simplex hd)
  d := d
  hd := rfl
  index := min x hd
  isIndex := by simp [isIndex_succ]

Depends on / 依赖: Subcomplex, Subcomplex.N.mk, hx.notMem_simplex, hx.simplex, hx.simplex_mem_nonDegenerate, isIndex, isIndex_succ, notMem_simplex, simplex, simplex_mem_nonDegenerate
-/
noncomputable def type₁ : Type₁ k n where
  x :=
    Subcomplex.N.mk (hx.simplex hd) (hx.simplex_mem_nonDegenerate hd)
      (hx.notMem_simplex hd)
  d := d
  hd := rfl
  index := min x hd
  isIndex := by simp [isIndex_succ]

end IsType₂

namespace IsIndex

variable {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `min_δ` / 引理 `min_δ`

English:
lemma min_δ
  statement: min (d := d) hl.δ rfl = l
  proof: by
  refine le_antisymm (Finset.min'_le _ _ ?_)
    (Finset.le_min' _ _ _ (fun y hy => ?_))
  · simp only [mem_finset_iff]
    simp only [Monoidal.tensorObj_obj, S.cast_dim, S.cast_simplex_rfl, prod_δ_fst,
      stdSimplex.δ_apply, Fin.succAbove_castSucc_self]
    exact hl.simplex_fst_succ
  · simp 

中文:
引理 min_δ
  结论: 最小值 (d := d) hl.δ rfl = l
  证明: by
  refine le_antisymm (Finset.min'_le _ _ ?_)
    (Finset.le_min' _ _ _ (fun y hy => ?_))
  · simp only [mem_finset_iff]
    simp only [Monoidal.tensorObj_obj, S.cast_dim, S.cast_simplex_rfl, prod_δ_fst,
      stdSimplex.δ_apply, Fin.succAbove_castSucc_self]
    exact hl.simplex_fst_succ
  · simp 

Depends on / 依赖: Fin.succAbove_castSucc_self, Fin.succAbove_of_castSucc_lt, Finset, Finset.le_min, Finset.min, Monoidal, Monoidal.tensorObj_obj, S.cast_dim, S.cast_simplex_rfl, cast_dim, cast_simplex_rfl, hl.simplex_fst_succ, hl.succ_le_simp, le_antisymm, le_min, mem_finset_iff, simplex_fst_succ, stdSimplex, succAbove_castSucc_self, succAbove_of_castSucc_lt
-/
lemma min_δ : min (d := d) hl.δ rfl = l := by
  refine le_antisymm (Finset.min'_le _ _ ?_)
    (Finset.le_min' _ _ _ (fun y hy => ?_))
  · simp only [mem_finset_iff]
    simp only [Monoidal.tensorObj_obj, S.cast_dim, S.cast_simplex_rfl, prod_δ_fst,
      stdSimplex.δ_apply, Fin.succAbove_castSucc_self]
    exact hl.simplex_fst_succ
  · simp only [mem_finset_iff, Monoidal.tensorObj_obj, S.cast_dim,
      S.cast_simplex_rfl, prod_δ_fst, stdSimplex.δ_apply] at hy
    by_contra!
    rw [Fin.succAbove_of_castSucc_lt _ _ (by grind)] at hy
    grind [(hl.succ_le_simplex_fst_iff y.castSucc).1 hy.symm.le]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isType₂_δ` / 引理 `isType₂_δ`

English:
lemma isType₂_δ
  statement: IsType₂ hl.δ
  proof: by
  intro _ rfl t ht
  dsimp at t ht
  obtain ⟨t, rfl⟩ := Fin.eq_succ_of_ne_zero (i := t) (fun h => by simp [h] at ht)
  obtain rfl : l = t.succ := by rw [← ht.min_eq, hl.min_δ]
  refine ((prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate t.castSucc.castSucc_lt

中文:
引理 isType₂_δ
  结论: IsType₂ hl.δ
  证明: by
  intro _ rfl t ht
  dsimp at t ht
  obtain ⟨t, rfl⟩ := Fin.eq_succ_of_ne_zero (i := t) (fun h => by simp [h] at ht)
  obtain rfl : l = t.succ := by rw [← ht.min_eq, hl.min_δ]
  refine ((prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate t.castSucc.castSucc_lt

Depends on / 依赖: Fin.eq_succ_of_ne_zero, castSucc, castSucc_lt_succ, eq_succ_of_ne_zero, hl.min_, ht.min_eq, isIndex_succ, min_eq, nonDegenerate, nonDegenerate_iff_strictMono_objEquiv, prodStdSimplex, prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv, stdSimplex, t.castSucc.castSucc_lt_succ, t.succ, x.cast
-/
lemma isType₂_δ : IsType₂ hl.δ := by
  intro _ rfl t ht
  dsimp at t ht
  obtain ⟨t, rfl⟩ := Fin.eq_succ_of_ne_zero (i := t) (fun h => by simp [h] at ht)
  obtain rfl : l = t.succ := by rw [← ht.min_eq, hl.min_δ]
  refine ((prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate t.castSucc.castSucc_lt_succ).ne ?_
  simp only [isIndex_succ] at hl ht
  dsimp [stdSimplex.δ_apply] at hl ht ⊢
  aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {x} in
/--
lemma `eq_of_isType₂_δ` / 引理 `eq_of_isType₂_δ`

English:
lemma eq_of_isType₂_δ
  statement: {u : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
  proof: by
  obtain rfl : u.dim = d := congr_arg S.dim hu'
  rw [S.ext_iff] at hu'
  obtain hi | rfl | hi := lt_trichotomy i l.castSucc
  · obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := l) (by grind)
    refine (hu _ rfl l.succ ?_).elim
    simp [isIndex_succ, S.cast_simplex_rfl, hu', stdSimplex.δ_apply,


中文:
引理 eq_of_isType₂_δ
  结论: {u : (子复形.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
  证明: by
  obtain rfl : u.dim = d := congr_arg S.dim hu'
  rw [S.ext_iff] at hu'
  obtain hi | rfl | hi := lt_trichotomy i l.castSucc
  · obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := l) (by grind)
    refine (hu _ rfl l.succ ?_).elim
    simp [isIndex_succ, S.cast_simplex_rfl, hu', stdSimplex.δ_apply,


Depends on / 依赖: Fin.eq_succ_of_ne_zero, Fin.succAbove_of_lt_succ, Or.inl, S.cast_simplex_rfl, S.dim, S.ext_iff, castSucc, cast_simplex_rfl, congr_arg, eq_succ_of_ne_zero, ext_iff, hl.simplex_fst_castSucc, hl.simplex_fst_succ, hl.simplex_snd_succ, isIndex_succ, l.castSucc, l.succ, lt_trichotomy, simplex_fst_castSucc, simplex_fst_succ
-/
lemma eq_of_isType₂_δ {u : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (hu : IsType₂ u) (i : Fin (d + 2))
    (hu' : S.mk u.simplex = S.mk (((Δ[m + 1] otimes Δ[n])).δ i (x.cast hd).simplex)) :
    i = l.castSucc ∨ i = l.succ := by
  obtain rfl : u.dim = d := congr_arg S.dim hu'
  rw [S.ext_iff] at hu'
  obtain hi | rfl | hi := lt_trichotomy i l.castSucc
  · obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := l) (by grind)
    refine (hu _ rfl l.succ ?_).elim
    simp [isIndex_succ, S.cast_simplex_rfl, hu', stdSimplex.δ_apply,
      Fin.succAbove_of_lt_succ i l.castSucc hi,
      Fin.succAbove_of_lt_succ i l.succ (by grind), dsimp% hl.simplex_fst_succ,
      dsimp% hl.simplex_snd_succ, dsimp% hl.simplex_fst_castSucc]
  · exact Or.inl rfl
  · obtain rfl | hi := (Fin.castSucc_lt_iff_succ_le.1 hi).eq_or_lt
    · exact Or.inr rfl
    · obtain ⟨l, rfl⟩ := Fin.eq_castSucc_of_ne_last (x := l) (by grind)
      refine (hu _ rfl l.succ ?_).elim
      simp [isIndex_succ, hu', stdSimplex.δ_apply,
        Fin.succAbove_of_castSucc_lt i l.castSucc (by grind),
        Fin.succAbove_of_castSucc_lt i l.succ (by grind),
        dsimp% hl.simplex_fst_castSucc, dsimp% hl.simplex_snd_succ,
        dsimp% hl.simplex_fst_succ]

end IsIndex

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsType₂.type₁_eq_of_δ_eq` / 引理 `IsType₂.type₁_eq_of_δ_eq`

English:
lemma IsType₂.type₁_eq_of_δ_eq
  proof: by
  subst hst hd
  rw [Type₁.ext_iff]; rw [Subcomplex.N.ext_iff]; rw [N.ext_iff]
  rw [← s.x.toS.cast_eq_self s.hd]; rw [S.ext_iff']
  refine ⟨rfl, objEquiv.injective ?_⟩
  ext i : 2
  change φ s.δ rfl i = _
  by_cases! hi : i = s.index.castSucc
  · subst hi
    conv_lhs => rw [← s.isIndex.min_δ]
 

中文:
引理 IsType₂.type₁_eq_of_δ_eq
  证明: by
  subst hst hd
  rw [Type₁.ext_iff]; rw [Subcomplex.N.ext_iff]; rw [N.ext_iff]
  rw [← s.x.toS.cast_eq_self s.hd]; rw [S.ext_iff']
  refine ⟨rfl, objEquiv.injective ?_⟩
  ext i : 2
  change φ s.δ rfl i = _
  by_cases! hi : i = s.index.castSucc
  · subst hi
    conv_lhs => rw [← s.isIndex.min_δ]
 

Depends on / 依赖: Fin.succAbove_castSucc_self, N.ext_iff, S.ext_iff, Subcomplex, Subcomplex.N.ext_iff, castSucc, cast_eq_self, conv_lhs, ext_iff, injective, isIndex, objEquiv, objEquiv.injective, s.hd, s.index.castSucc, s.index.castSucc.succAbove, s.isIndex.min_, s.isIndex.simplex_fst_castSucc, s.x.cast, s.x.toS.cast_eq_self
-/
lemma IsType₂.type₁_eq_of_δ_eq
    {t : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (ht : IsType₂ t) (s : Type₁.{u} k n) (hst : s.δ = t) {d : Nat} (hd : t.dim = d) :
    ht.type₁ hd = s := by
  subst hst hd
  rw [Type₁.ext_iff]; rw [Subcomplex.N.ext_iff]; rw [N.ext_iff]
  rw [← s.x.toS.cast_eq_self s.hd]; rw [S.ext_iff']
  refine ⟨rfl, objEquiv.injective ?_⟩
  ext i : 2
  change φ s.δ rfl i = _
  by_cases! hi : i = s.index.castSucc
  · subst hi
    conv_lhs => rw [← s.isIndex.min_δ]
    dsimp
    rw [φ_castSucc]
    ext : 1
    · simp [← s.isIndex.simplex_fst_castSucc]
      rfl
    · change (s.x.cast s.hd).simplex.2
        (s.index.castSucc.succAbove (min s.δ rfl)) = _
      rw [s.isIndex.min_δ]; rw [Fin.succAbove_castSucc_self]
      exact s.isIndex.simplex_snd_succ -- defeq abuse
  · rw [← s.isIndex.min_δ] at hi
    rw [φ_of_ne _ rfl _ hi]
    change objEquiv (s.x.cast s.hd).simplex
      (s.index.castSucc.succAbove ((min s.δ rfl).predAbove i)) = _
    congr 1
    rw [← s.isIndex.min_δ]
    exact Fin.succAbove_predAbove hi -- `simp [hi]` should work but doesn't

/--
lemma `Type₁.isType₂_δ` / 引理 `Type₁.isType₂_δ`

English:
lemma Type₁.isType₂_δ
  given: (s : Type₁.{u} k n)
  statement: IsType₂ s.δ
  proof: s.isIndex.isType₂_δ

中文:
引理 Type₁.isType₂_δ
  条件: (s : Type₁.{u} k n)
  结论: IsType₂ s.δ
  证明: s.isIndex.isType₂_δ

Depends on / 依赖: isIndex, s.isIndex.isType
-/
lemma Type₁.isType₂_δ (s : Type₁.{u} k n) : IsType₂ s.δ :=
  s.isIndex.isType₂_δ

variable {x} in
/--
lemma `IsIndex.δ_injective` / 引理 `IsIndex.δ_injective`

English:
lemma IsIndex.δ_injective
  proof: by
  have h₁ := hl.isType₂_δ.type₁_eq_of_δ_eq hl'.type₁ h.symm rfl
  have h₂ := hl.isType₂_δ.type₁_eq_of_δ_eq hl.type₁ rfl rfl
  exact congr_arg Type₁.x (h₂.symm.trans h₁)

中文:
引理 IsIndex.δ_injective
  证明: by
  have h₁ := hl.isType₂_δ.type₁_eq_of_δ_eq hl'.type₁ h.symm rfl
  have h₂ := hl.isType₂_δ.type₁_eq_of_δ_eq hl.type₁ rfl rfl
  exact congr_arg Type₁.x (h₂.symm.trans h₁)

Depends on / 依赖: congr_arg, h.symm, hl.isType, hl.type, symm.trans
-/
lemma IsIndex.δ_injective
    {d : Nat} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)
    {y : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    {d' : Nat} {hd' : y.dim = d' + 1} {l' : Fin (d' + 1)} (hl' : IsIndex y hd' l'.succ)
    (h : hl.δ = hl'.δ) :
    x = y := by
  have h₁ := hl.isType₂_δ.type₁_eq_of_δ_eq hl'.type₁ h.symm rfl
  have h₂ := hl.isType₂_δ.type₁_eq_of_δ_eq hl.type₁ rfl rfl
  exact congr_arg Type₁.x (h₂.symm.trans h₁)

end pairingCore

open pairingCore

/-- The underlying structure which gives a pairing for
`Subcomplex.unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`. -/
@[simps]
/--
Definition of `pairingCore` / `pairingCore` 的定义

English:
definition pairingCore
  signature: {m : Nat} (k : Fin (m + 1)) (n : Nat)
  body: Type₁.{u} k n
  dim s := s.d
  simplex s := (s.x.cast s.hd).simplex
  index s := s.index.castSucc
  nonDegenerate₁ s := (s.x.cast s.hd).nonDegenerate
  nonDegenerate₂ s := s.isIndex.δ.nonDegenerate
  notMem₁ s := (s.x.cast s.hd).notMem
  notMem₂ s := s.isIndex.δ.notMem
  injective_type₁' {s t} h := 

中文:
定义 pairingCore
  签名: {m : 自然数} (k : 有限集 (m + 1)) (n : 自然数)
  定义体: Type₁.{u} k n
  dim s := s.d
  simplex s := (s.x.cast s.hd).simplex
  index s := s.index.castSucc
  nonDegenerate₁ s := (s.x.cast s.hd).nonDegenerate
  nonDegenerate₂ s := s.isIndex.δ.nonDegenerate
  notMem₁ s := (s.x.cast s.hd).notMem
  notMem₂ s := s.isIndex.δ.notMem
  injective_type₁' {s t} h := 
-/
noncomputable def pairingCore {m : Nat} (k : Fin (m + 1)) (n : Nat) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).PairingCore where
  ι := Type₁.{u} k n
  dim s := s.d
  simplex s := (s.x.cast s.hd).simplex
  index s := s.index.castSucc
  nonDegenerate₁ s := (s.x.cast s.hd).nonDegenerate
  nonDegenerate₂ s := s.isIndex.δ.nonDegenerate
  notMem₁ s := (s.x.cast s.hd).notMem
  notMem₂ s := s.isIndex.δ.notMem
  injective_type₁' {s t} h := by
    rw [Type₁.ext_iff]; rw [Subcomplex.N.ext_iff]; rw [N.ext_iff]
    rwa [← s.x.toS.cast_eq_self s.hd, ← t.x.toS.cast_eq_self t.hd]
  injective_type₂' {s t} h := by
    replace h : s.δ = t.δ := by rwa [Subcomplex.N.ext_iff, N.ext_iff]
    generalize hs : s.δ = u
    have hu' : IsType₂ u := by simpa only [hs] using s.isType₂_δ
    rw [← hu'.type₁_eq_of_δ_eq _ hs rfl]; rw [hu'.type₁_eq_of_δ_eq _ (h.symm.trans hs) rfl]
  type₁_ne_type₂' s t hst := by
    replace hst : s.x = t.isIndex.δ := by
      rwa [Subcomplex.N.ext_iff, N.ext_iff, ← s.x.cast_eq_self s.hd]
    have := t.isIndex.isType₂_δ
    rw [← hst] at this
    exact this _ _ _ s.isIndex
  surjective' x := by
    by_cases hx : IsType₂ x
    · generalize hd : x.dim = d
      refine ⟨hx.type₁ hd, Or.inr ?_⟩
      rw [S.ext_iff']
      exact ⟨hd, (hx.δ_simplex hd).symm⟩
    · simp only [IsType₂, not_forall, not_not] at hx
      obtain ⟨_ | d, hd, i, hx⟩ := hx
      · fin_cases i
        simp at hx
      · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by rintro rfl; simp at hx)
        refine ⟨{ x := x, d := d, hd := hd, index := i, isIndex := hx }, Or.inl ?_⟩
        dsimp
        rw [S.ext_iff']
        exact ⟨hd, rfl⟩

@[simp]
/--
lemma `type₁_pairingCore` / 引理 `type₁_pairingCore`

English:
lemma type₁_pairingCore
  statement: {m : Nat} (k : Fin (m + 1)) {n : Nat}
  proof: Subcomplex.N.cast_eq_self _ s.hd

中文:
引理 type₁_pairingCore
  结论: {m : 自然数} (k : 有限集 (m + 1)) {n : 自然数}
  证明: Subcomplex.N.cast_eq_self _ s.hd

Depends on / 依赖: Subcomplex, Subcomplex.N.cast_eq_self, cast_eq_self, s.hd
-/
lemma type₁_pairingCore {m : Nat} (k : Fin (m + 1)) {n : Nat}
    (s : Type₁.{u} k n) :
    (pairingCore k n).type₁ s = s.x :=
  Subcomplex.N.cast_eq_self _ s.hd

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `weakRankFunction` / `weakRankFunction` 的定义

English:
definition weakRankFunction
  signature: {m : Nat} (k : Fin (m + 1)) (n : Nat)
  body: (finset s.x rfl).card
  lt := by
    intro ⟨s, d, hds, is, hs⟩ ⟨t, d', hdt, it, ht⟩ ⟨h₁, h₂⟩ h₃
    obtain ⟨ds, s, hs₁, hs₂, rfl⟩ := Subcomplex.N.mk_surjective s
    obtain ⟨dt, t, ht₁, ht₂, rfl⟩ := Subcomplex.N.mk_surjective t
    obtain rfl : d = d' := h₃
    obtain rfl : ds = d + 1 := hds
    obt

中文:
定义 weakRankFunction
  签名: {m : 自然数} (k : 有限集 (m + 1)) (n : 自然数)
  定义体: (finset s.x rfl).card
  lt := by
    intro ⟨s, d, hds, is, hs⟩ ⟨t, d', hdt, it, ht⟩ ⟨h₁, h₂⟩ h₃
    obtain ⟨ds, s, hs₁, hs₂, rfl⟩ := Subcomplex.N.mk_surjective s
    obtain ⟨dt, t, ht₁, ht₂, rfl⟩ := Subcomplex.N.mk_surjective t
    obtain rfl : d = d' := h₃
    obtain rfl : ds = d + 1 := hds
    obt

Depends on / 依赖: finset
-/
noncomputable def weakRankFunction {m : Nat} (k : Fin (m + 1)) (n : Nat) :
    (pairingCore.{u} k n).WeakRankFunction Nat where
  rank s := (finset s.x rfl).card
  lt := by
    intro ⟨s, d, hds, is, hs⟩ ⟨t, d', hdt, it, ht⟩ ⟨h₁, h₂⟩ h₃
    obtain ⟨ds, s, hs₁, hs₂, rfl⟩ := Subcomplex.N.mk_surjective s
    obtain ⟨dt, t, ht₁, ht₂, rfl⟩ := Subcomplex.N.mk_surjective t
    obtain rfl : d = d' := h₃
    obtain rfl : ds = d + 1 := hds
    obtain rfl : dt = d + 1 := hdt
    simp only [ne_eq, pairingCore_ι, Type₁.ext_iff] at h₁
    obtain ⟨f, hf, hδ⟩ := N.le_iff_exists_mono.1 h₂.le
    dsimp at f hf
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl | rfl := ht.eq_of_isType₂_δ hs.isType₂_δ i (by
      rw [S.ext_iff']
      exact ⟨rfl, hδ.symm⟩)
    · refine (h₁ (hs.δ_injective ht ?_)).elim
      rw [Subcomplex.N.ext_iff]; rw [N.ext_iff]; rw [S.ext_iff']
      exact ⟨rfl, hδ.symm⟩
    · let Ss := finset (Subcomplex.N.mk s hs₁ hs₂) rfl
      let St := finset (Subcomplex.N.mk t ht₁ ht₂) rfl
      let Sδ := finset hs.δ rfl
      replace hδ (i : Fin (d + 1)) :
          s.1 (is.castSucc.succAbove i) = t.1 (it.succ.succAbove i) :=
        DFunLike.congr_fun (congr_arg Prod.fst hδ.symm) i
      have hSs (i : Fin (d + 1)) : i in Sδ ↔ is.castSucc.succAbove i in Ss := by
        simp [Sδ, Ss, stdSimplex.δ_apply]
      have hSt (i : Fin (d + 1)) : i in Sδ ↔ it.succ.succAbove i in St := by
        simp [Sδ, St, stdSimplex.δ_apply, hδ]
      suffices Ss.card = Sδ.card ∧ St.card = Sδ.card + 1 by grind
      constructor
      · suffices Ss = Finset.image is.castSucc.succAbove Sδ by
          rw [this]
          exact Finset.card_image_of_injective _ Fin.succAbove_right_injective
        ext i
        obtain rfl | ⟨i, rfl⟩ := is.castSucc.eq_self_or_eq_succAbove i
        · have : is.castSucc ∉ Ss := fun h => by
            have : s.1 is.castSucc <= k.castSucc := by
              simpa using (hs.simplex_fst_le_castSucc_iff is.castSucc).2 (by simp)
            simp_all [Ss]
          simpa
        · simp [hSs]
      · suffices St = Finset.image it.succ.succAbove Sδ union {it.succ} by
          rw [this]; rw [Finset.card_union_of_disjoint (by simp)]; rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective]; rw [Finset.card_singleton]
        ext i
        obtain rfl | ⟨i, rfl⟩ := it.succ.eq_self_or_eq_succAbove i
        · have : it.succ in St := by
            simpa [St, mem_finset_iff] using ht.simplex_fst_succ
          simp [hSt, this]
        · simp [hSt]

instance {m : Nat} (k : Fin (m + 1)) (n : Nat) :
    (pairingCore.{u} k n).IsRegular :=
  (weakRankFunction.{u} k n).isRegular

instance {m : Nat} (k : Fin m) (n : Nat) :
    (pairingCore.{u} k.succ n).IsInner where
  ne_zero (s : Type₁ k.succ n) h := by
    have : s.index = 0 := by rwa [← Fin.castSucc_eq_zero_iff]
    have hs : IsIndex s.x s.hd (Fin.succ 0) := by simpa [this] using s.isIndex
    obtain ⟨i, hi⟩ := mem_range_left s.x s.hd 0 (fun h => by simp [Fin.ext_iff] at h)
    have := stdSimplex.monotone_apply (s.x.cast s.hd).simplex.1 i.zero_le
    have h₁ := hs.simplex_fst_castSucc
    dsimp only [Fin.castSucc_zero] at h₁
    simp [h₁, hi] at this
  ne_last x := by
    dsimp [pairingCore]
    simp

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `pairing` / `pairing` 的定义

English:
definition pairing
  signature: {m : Nat} (k : Fin (m + 2)) (n : Nat)
  body: if hk : k = Fin.last (m + 1) then
    (pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso
      (((stdSimplex.opIso _).symm otimesᵢ (stdSimplex.opIso _).symm) ≪≫
        Functor.Monoidal.μIso opFunctor _ _) (by
          dsimp
          rw [hk]; rw [Subcomplex.preimage_comp]; rw [Subcomplex.preimage_

中文:
定义 pairing
  签名: {m : 自然数} (k : 有限集 (m + 2)) (n : 自然数)
  定义体: if hk : k = Fin.last (m + 1) then
    (pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso
      (((stdSimplex.opIso _).symm otimesᵢ (stdSimplex.opIso _).symm) ≪≫
        Functor.Monoidal.μIso opFunctor _ _) (by
          dsimp
          rw [hk]; rw [Subcomplex.preimage_comp]; rw [Subcomplex.preimage_

Depends on / 依赖: Fin.last, Fin.rev_zero, Functor, Functor.Monoidal, Monoidal, Subcomplex, Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd, Subcomplex.preimage_unionProd, castPred, k.castPred, opFunctor, op_boundary, op_horn, pairing, pairing.op.ofIso, pairingCore, preimage_comp, preimage_op_unionProd, preimage_unionProd
-/
noncomputable def pairing {m : Nat} (k : Fin (m + 2)) (n : Nat) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).Pairing :=
  if hk : k = Fin.last (m + 1) then
    (pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso
      (((stdSimplex.opIso _).symm otimesᵢ (stdSimplex.opIso _).symm) ≪≫
        Functor.Monoidal.μIso opFunctor _ _) (by
          dsimp
          rw [hk]; rw [Subcomplex.preimage_comp]; rw [Subcomplex.preimage_op_unionProd]; rw [Subcomplex.preimage_unionProd]; rw [op_boundary]; rw [op_horn]; rw [Fin.rev_zero])
  else
    (pairingCore.{u} (k.castPred hk) n).pairing

/--
lemma `pairing_castSucc` / 引理 `pairing_castSucc`

English:
lemma pairing_castSucc
  given: {m : Nat} (k : Fin (m + 1)) (n : Nat)
  proof: dif_neg (by grind)

中文:
引理 pairing_castSucc
  条件: {m : 自然数} (k : 有限集 (m + 1)) (n : 自然数)
  证明: dif_neg (by grind)

Depends on / 依赖: dif_neg
-/
lemma pairing_castSucc {m : Nat} (k : Fin (m + 1)) (n : Nat) :
    pairing.{u} k.castSucc n = (pairingCore.{u} k n).pairing :=
  dif_neg (by grind)

set_option backward.isDefEq.respectTransparency.types false in
instance {m : Nat} (k : Fin (m + 2)) (n : Nat) :
    (pairing.{u} k n).IsRegular := by
  by_cases! hk : k = Fin.last (m + 1)
  · subst hk
    dsimp only [pairing]
    rw [dif_pos rfl]
    infer_instance
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    rw [pairing_castSucc]
    infer_instance

instance {m : Nat} (k : Fin m) (n : Nat) :
    (pairing.{u} k.castSucc.succ n).IsInner := by
  simp only [← Fin.castSucc_succ, pairing_castSucc]
  infer_instance

end prodStdSimplex

end SSet
