/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Generators for Boolean algebras

In this file, we provide an alternative constructor for Boolean algebras.

A set of *Boolean generators* in a compactly generated complete lattice is a subset `S` such that

* the elements of `S` are all atoms, and
* the set `S` satisfies an atomicity condition:
  any compact element below the supremum of a subset `s` of generators
  is equal to the supremum of a subset of `s`.

## Main declarations

* `IsCompactlyGenerated.BooleanGenerators`:
  the predicate described above.
* `IsCompactlyGenerated.BooleanGenerators.complementedLattice_of_sSup_eq_top`:
  if `S` generates the entire lattice, then it is complemented.
* `IsCompactlyGenerated.BooleanGenerators.distribLatticeOfSSupEqTop`:
  if `S` generates the entire lattice, then it is distributive.
* `IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop`:
  if `S` generates the entire lattice, then it is a Boolean algebra.

-/

@[expose] public section

namespace IsCompactlyGenerated

open CompleteLattice

variable {α : Type*} [CompleteLattice α]

/--
Definition of `BooleanGenerators` / `BooleanGenerators` 的定义

English:
structure BooleanGenerators
  parameters: (S : Set α)
  axioms and operations (2):
    - isAtom : forall I in S, IsAtom I
    - finitelyAtomistic : forall (s : Finset α) (a : α), ↑s subseteq S -> IsCompactElement a -> a <= s.sup id -> exists t subseteq s, a = t.sup id

中文:
结构 布尔eanGenerators
  参数: (S : 集合 α)
  公理与运算 (2 个):
    - isAtom : 对任意 I in S, IsAtom I
    - finitelyAtomistic : 对任意 (s : 有限集 α) (a : α), ↑s subseteq S -> IsCompactElement a -> a <= s.上确界 id -> 存在 t subseteq s, a = t.上确界 id
-/
structure BooleanGenerators (S : Set α) : Prop where
  /-- The elements in a collection of Boolean generators are all atoms. -/
  isAtom : forall I in S, IsAtom I
  /-- The elements in a collection of Boolean generators satisfy an atomicity condition:
  any compact element below the supremum of a finite subset `s` of generators
  is equal to the supremum of a subset of `s`. -/
  finitelyAtomistic : forall (s : Finset α) (a : α),
      ↑s subseteq S -> IsCompactElement a -> a <= s.sup id -> exists t subseteq s, a = t.sup id

namespace BooleanGenerators

variable {S : Set α}

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: (hS : BooleanGenerators S) {T : Set α} (hTS : T subseteq S)
  statement: BooleanGenerators T where
  proof: hS.isAtom I (hTS hI)
  finitelyAtomistic := fun s a hs => hS.finitelyAtomistic s a (le_trans hs hTS)

中文:
引理 mono
  条件: (hS : 布尔eanGenerators S) {T : 集合 α} (hTS : T subseteq S)
  结论: 布尔eanGenerators T where
  证明: hS.isAtom I (hTS hI)
  finitelyAtomistic := fun s a hs => hS.finitelyAtomistic s a (le_trans hs hTS)

Depends on / 依赖: hS.isAtom, isAtom
-/
lemma mono (hS : BooleanGenerators S) {T : Set α} (hTS : T subseteq S) : BooleanGenerators T where
  isAtom I hI := hS.isAtom I (hTS hI)
  finitelyAtomistic := fun s a hs => hS.finitelyAtomistic s a (le_trans hs hTS)

variable [IsCompactlyGenerated α]

/--
lemma `atomistic` / 引理 `atomistic`

English:
lemma atomistic
  given: (hS : BooleanGenerators S) (a : α) (ha : a <= sSup S)
  statement: exists T subseteq S, a = sSup T
  proof: by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq a
  have aux : forall b : α, IsCompactElement b -> b <= sSup S -> exists T subseteq S, b = sSup T := by
    intro b hb hbS
    obtain ⟨s, hs₁, hs₂⟩ := (isCompactElement_iff_exists_le_sSup_of_le_sSup α b).1 hb S hbS
    obtain ⟨t, ht, rf

中文:
引理 atomistic
  条件: (hS : 布尔eanGenerators S) (a : α) (ha : a <= sSup S)
  结论: 存在 T subseteq S, a = sSup T
  证明: by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq a
  have aux : forall b : α, IsCompactElement b -> b <= sSup S -> exists T subseteq S, b = sSup T := by
    intro b hb hbS
    obtain ⟨s, hs₁, hs₂⟩ := (isCompactElement_iff_exists_le_sSup_of_le_sSup α b).1 hb S hbS
    obtain ⟨t, ht, rf

Depends on / 依赖: Finset, Finset.coe_subset, Finset.sup_id_eq_sSup, IsCompactElement, IsCompactlyGenerated, IsCompactlyGenerated.exists_sSup_eq, Set.Subset.trans, Subset, coe_subset, exists_sSup_eq, finitelyAtomistic, hS.finitelyAtomistic, isCompactElement_iff_exists_le_sSup_of_le_sSup, subseteq, sup_id_eq_sSup
-/
lemma atomistic (hS : BooleanGenerators S) (a : α) (ha : a <= sSup S) : exists T subseteq S, a = sSup T := by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq a
  have aux : forall b : α, IsCompactElement b -> b <= sSup S -> exists T subseteq S, b = sSup T := by
    intro b hb hbS
    obtain ⟨s, hs₁, hs₂⟩ := (isCompactElement_iff_exists_le_sSup_of_le_sSup α b).1 hb S hbS
    obtain ⟨t, ht, rfl⟩ := hS.finitelyAtomistic s b hs₁ hb hs₂
    refine ⟨t, ?_, Finset.sup_id_eq_sSup t⟩
    refine Set.Subset.trans ?_ hs₁
    simpa only [Finset.coe_subset] using ht
  choose T hT₁ hT₂ using aux
  use sSup {T c h₁ h₂ | (c in C) (h₁ : IsCompactElement c) (h₂ : c <= sSup S)}
  constructor
  · apply _root_.sSup_le
    rintro _ ⟨c, -, h₁, h₂, rfl⟩
    apply hT₁
  · apply le_antisymm
    · apply _root_.sSup_le
      intro c hc
      rw [hT₂ c (hC _ hc) ((le_sSup hc).trans ha)]
      apply sSup_le_sSup
      apply _root_.le_sSup
      use c, hc, hC _ hc, (le_sSup hc).trans ha
    · simp only [Set.sSup_eq_sUnion, sSup_le_iff, Set.mem_sUnion, Set.mem_ofPred_eq,
        forall_exists_index, and_imp]
      rintro a T b hbC hb hbS rfl haT
      apply (le_sSup haT).trans
      rw [← hT₂]
      exact le_sSup hbC

/--
lemma `isAtomistic_of_sSup_eq_top` / 引理 `isAtomistic_of_sSup_eq_top`

English:
lemma isAtomistic_of_sSup_eq_top
  given: (hS : BooleanGenerators S) (h : sSup S = ⊤)
  proof: by
  refine CompleteLattice.isAtomistic_iff.2 fun a => ?_
  obtain ⟨s, hs, hs'⟩ := hS.atomistic a (h ▸ le_top)
  exact ⟨s, hs', fun I hI => hS.isAtom I (hs hI)⟩

中文:
引理 isAtomistic_of_sSup_eq_top
  条件: (hS : 布尔eanGenerators S) (h : sSup S = ⊤)
  证明: by
  refine CompleteLattice.isAtomistic_iff.2 fun a => ?_
  obtain ⟨s, hs, hs'⟩ := hS.atomistic a (h ▸ le_top)
  exact ⟨s, hs', fun I hI => hS.isAtom I (hs hI)⟩

Depends on / 依赖: CompleteLattice, CompleteLattice.isAtomistic_iff, atomistic, hS.atomistic, hS.isAtom, isAtom, isAtomistic_iff, le_top
-/
lemma isAtomistic_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    IsAtomistic α := by
  refine CompleteLattice.isAtomistic_iff.2 fun a => ?_
  obtain ⟨s, hs, hs'⟩ := hS.atomistic a (h ▸ le_top)
  exact ⟨s, hs', fun I hI => hS.isAtom I (hs hI)⟩

/--
lemma `mem_of_isAtom_of_le_sSup_atoms` / 引理 `mem_of_isAtom_of_le_sSup_atoms`

English:
lemma mem_of_isAtom_of_le_sSup_atoms
  statement: (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
  proof: by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a haS
  obtain rfl | ⟨a, haT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at ha
    exact (ha.1 rfl).elim
  suffices sSup T = a from this ▸ hT haT
  have : a <= sSup T := le_sSup haT
  rwa [ha.le_iff_eq, eq_comm] at this
  exact (hS.isAtom a (hT haT)

中文:
引理 mem_of_isAtom_of_le_sSup_atoms
  结论: (hS : 布尔eanGenerators S) (a : α) (ha : IsAtom a)
  证明: by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a haS
  obtain rfl | ⟨a, haT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at ha
    exact (ha.1 rfl).elim
  suffices sSup T = a from this ▸ hT haT
  have : a <= sSup T := le_sSup haT
  rwa [ha.le_iff_eq, eq_comm] at this
  exact (hS.isAtom a (hT haT)

Depends on / 依赖: T.eq_empty_or_nonempty, atomistic, eq_comm, eq_empty_or_nonempty, hS.atomistic, hS.isAtom, ha.le_iff_eq, isAtom, le_iff_eq, le_sSup, sSup_empty
-/
lemma mem_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
    (haS : a <= sSup S) : a in S := by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a haS
  obtain rfl | ⟨a, haT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at ha
    exact (ha.1 rfl).elim
  suffices sSup T = a from this ▸ hT haT
  have : a <= sSup T := le_sSup haT
  rwa [ha.le_iff_eq, eq_comm] at this
  exact (hS.isAtom a (hT haT)).1

/--
lemma `sSup_inter` / 引理 `sSup_inter`

English:
lemma sSup_inter
  given: (hS : BooleanGenerators S) {T₁ T₂ : Set α} (hT₁ : T₁ subseteq S) (hT₂ : T₂ subseteq S)
  proof: by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup Set.inter_subset_left
    · apply sSup_le_sSup Set.inter_subset_right
  obtain ⟨X, hX, hX'⟩ := hS.atomistic (sSup T₁ ⊓ sSup T₂) (inf_le_left.trans (sSup_le_sSup hT₁))
  rw [hX']
  apply _root_.sSup_le
  intro I hI
  apply _root_.le_sSu

中文:
引理 sSup_inter
  条件: (hS : 布尔eanGenerators S) {T₁ T₂ : 集合 α} (hT₁ : T₁ subseteq S) (hT₂ : T₂ subseteq S)
  证明: by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup Set.inter_subset_left
    · apply sSup_le_sSup Set.inter_subset_right
  obtain ⟨X, hX, hX'⟩ := hS.atomistic (sSup T₁ ⊓ sSup T₂) (inf_le_left.trans (sSup_le_sSup hT₁))
  rw [hX']
  apply _root_.sSup_le
  intro I hI
  apply _root_.le_sSu

Depends on / 依赖: Set.inter_subset_left, Set.inter_subset_right, _root_, _root_.le_sSup, _root_.sSup_le, atomistic, ge.trans, hS.atomistic, hS.mono, inf_le_left, inf_le_left.trans, inter_subset_left, inter_subset_right, isAtom, le_antisymm, le_inf, le_sSup, mem_of_isAtom_of_le_sSup_atoms, sSup_le, sSup_le_sSup
-/
lemma sSup_inter (hS : BooleanGenerators S) {T₁ T₂ : Set α} (hT₁ : T₁ subseteq S) (hT₂ : T₂ subseteq S) :
    sSup (T₁ inter T₂) = (sSup T₁) ⊓ (sSup T₂) := by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup Set.inter_subset_left
    · apply sSup_le_sSup Set.inter_subset_right
  obtain ⟨X, hX, hX'⟩ := hS.atomistic (sSup T₁ ⊓ sSup T₂) (inf_le_left.trans (sSup_le_sSup hT₁))
  rw [hX']
  apply _root_.sSup_le
  intro I hI
  apply _root_.le_sSup
  constructor
  · apply (hS.mono hT₁).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_left)
  · apply (hS.mono hT₂).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_right)

/-- A lattice generated by Boolean generators is a distributive lattice. -/
@[instance_reducible]
/--
Definition of `distribLatticeOfSSupEqTop` / `distribLatticeOfSSupEqTop` 的定义

English:
definition distribLatticeOfSSupEqTop
  signature: (hS : BooleanGenerators S) (h : sSup S = ⊤)
  body: by
    obtain ⟨Ta, hTa, rfl⟩ := hS.atomistic a (h ▸ le_top)
    obtain ⟨Tb, hTb, rfl⟩ := hS.atomistic b (h ▸ le_top)
    obtain ⟨Tc, hTc, rfl⟩ := hS.atomistic c (h ▸ le_top)
    apply le_of_eq
    rw [← sSup_union]; rw [← sSup_union]; rw [← hS.sSup_inter hTb hTc]; rw [← hS.sSup_inter]; rw [← sSup_un

中文:
定义 distribLatticeOfSSupEqTop
  签名: (hS : 布尔eanGenerators S) (h : sSup S = ⊤)
  定义体: by
    obtain ⟨Ta, hTa, rfl⟩ := hS.atomistic a (h ▸ le_top)
    obtain ⟨Tb, hTb, rfl⟩ := hS.atomistic b (h ▸ le_top)
    obtain ⟨Tc, hTc, rfl⟩ := hS.atomistic c (h ▸ le_top)
    apply le_of_eq
    rw [← sSup_union]; rw [← sSup_union]; rw [← hS.sSup_inter hTb hTc]; rw [← hS.sSup_inter]; rw [← sSup_un

Depends on / 依赖: Set.mem_inter_iff, Set.mem_union, Set.union_subset_iff, all_goals, atomistic, hS.atomistic, hS.sSup_inter, le_of_eq, le_top, mem_inter_iff, mem_union, on_goal, sSup_inter, sSup_union, union_subset_iff
-/
def distribLatticeOfSSupEqTop (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    DistribLattice α where
  le_sup_inf a b c := by
    obtain ⟨Ta, hTa, rfl⟩ := hS.atomistic a (h ▸ le_top)
    obtain ⟨Tb, hTb, rfl⟩ := hS.atomistic b (h ▸ le_top)
    obtain ⟨Tc, hTc, rfl⟩ := hS.atomistic c (h ▸ le_top)
    apply le_of_eq
    rw [← sSup_union]; rw [← sSup_union]; rw [← hS.sSup_inter hTb hTc]; rw [← hS.sSup_inter]; rw [← sSup_union]
    on_goal 1 => congr 1; ext
    all_goals
      simp only [Set.union_subset_iff, Set.mem_inter_iff, Set.mem_union]
      tauto

@[deprecated (since := "2026-07-18")]
alias distribLattice_of_sSup_eq_top := distribLatticeOfSSupEqTop

/--
lemma `complementedLattice_of_sSup_eq_top` / 引理 `complementedLattice_of_sSup_eq_top`

English:
lemma complementedLattice_of_sSup_eq_top
  given: (hS : BooleanGenerators S) (h : sSup S = ⊤)
  proof: by
  let _i := hS.distribLatticeOfSSupEqTop h
  have _i₁ := isAtomistic_of_sSup_eq_top hS h
  apply complementedLattice_of_isAtomistic

中文:
引理 complementedLattice_of_sSup_eq_top
  条件: (hS : 布尔eanGenerators S) (h : sSup S = ⊤)
  证明: by
  let _i := hS.distribLatticeOfSSupEqTop h
  have _i₁ := isAtomistic_of_sSup_eq_top hS h
  apply complementedLattice_of_isAtomistic

Depends on / 依赖: complementedLattice_of_isAtomistic, distribLatticeOfSSupEqTop, hS.distribLatticeOfSSupEqTop, isAtomistic_of_sSup_eq_top
-/
lemma complementedLattice_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    ComplementedLattice α := by
  let _i := hS.distribLatticeOfSSupEqTop h
  have _i₁ := isAtomistic_of_sSup_eq_top hS h
  apply complementedLattice_of_isAtomistic

/-- A compactly generated complete lattice generated by Boolean generators is a Boolean algebra. -/
@[instance_reducible]
noncomputable
/--
Definition of `booleanAlgebraOfSSupEqTop` / `booleanAlgebraOfSSupEqTop` 的定义

English:
definition booleanAlgebraOfSSupEqTop
  signature: (hS : BooleanGenerators S) (h : sSup S = ⊤)
  body: let _i := hS.distribLatticeOfSSupEqTop h
  have := hS.complementedLattice_of_sSup_eq_top h
  DistribLattice.booleanAlgebraOfComplemented α

@[deprecated (since := "2026-07-18")]
alias booleanAlgebra_of_sSup_eq_top := booleanAlgebraOfSSupEqTop

中文:
定义 booleanAlgebraOfSSupEqTop
  签名: (hS : 布尔eanGenerators S) (h : sSup S = ⊤)
  定义体: let _i := hS.distribLatticeOfSSupEqTop h
  have := hS.complementedLattice_of_sSup_eq_top h
  DistribLattice.booleanAlgebraOfComplemented α

@[deprecated (since := "2026-07-18")]
alias booleanAlgebra_of_sSup_eq_top := booleanAlgebraOfSSupEqTop

Depends on / 依赖: DistribLattice, DistribLattice.booleanAlgebraOfComplemented, booleanAlgebraOfComplemented, complementedLattice_of_sSup_eq_top, distribLatticeOfSSupEqTop, hS.complementedLattice_of_sSup_eq_top, hS.distribLatticeOfSSupEqTop
-/
def booleanAlgebraOfSSupEqTop (hS : BooleanGenerators S) (h : sSup S = ⊤) : BooleanAlgebra α :=
  let _i := hS.distribLatticeOfSSupEqTop h
  have := hS.complementedLattice_of_sSup_eq_top h
  DistribLattice.booleanAlgebraOfComplemented α

@[deprecated (since := "2026-07-18")]
alias booleanAlgebra_of_sSup_eq_top := booleanAlgebraOfSSupEqTop

/--
lemma `sSup_le_sSup_iff_of_atoms` / 引理 `sSup_le_sSup_iff_of_atoms`

English:
lemma sSup_le_sSup_iff_of_atoms
  given: (hS : BooleanGenerators S) (X Y : Set α) (hX : X subseteq S) (hY : Y subseteq S)
  proof: by
  refine ⟨?_, sSup_le_sSup⟩
  intro h a ha
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup ha).trans h)
  exact (hS.mono hX).isAtom a ha

中文:
引理 sSup_le_sSup_iff_of_atoms
  条件: (hS : 布尔eanGenerators S) (X Y : 集合 α) (hX : X subseteq S) (hY : Y subseteq S)
  证明: by
  refine ⟨?_, sSup_le_sSup⟩
  intro h a ha
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup ha).trans h)
  exact (hS.mono hX).isAtom a ha

Depends on / 依赖: hS.mono, isAtom, le_sSup, mem_of_isAtom_of_le_sSup_atoms, sSup_le_sSup
-/
lemma sSup_le_sSup_iff_of_atoms (hS : BooleanGenerators S) (X Y : Set α) (hX : X subseteq S) (hY : Y subseteq S) :
    sSup X <= sSup Y ↔ X subseteq Y := by
  refine ⟨?_, sSup_le_sSup⟩
  intro h a ha
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup ha).trans h)
  exact (hS.mono hX).isAtom a ha

/--
lemma `eq_atoms_of_sSup_eq_top` / 引理 `eq_atoms_of_sSup_eq_top`

English:
lemma eq_atoms_of_sSup_eq_top
  given: (hS : BooleanGenerators S) (h : sSup S = ⊤)
  proof: by
  apply le_antisymm
  · exact hS.isAtom
  intro a ha
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ ha (sSup_le_sSup hT)

中文:
引理 eq_atoms_of_sSup_eq_top
  条件: (hS : 布尔eanGenerators S) (h : sSup S = ⊤)
  证明: by
  apply le_antisymm
  · exact hS.isAtom
  intro a ha
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ ha (sSup_le_sSup hT)

Depends on / 依赖: atomistic, h.ge, hS.atomistic, hS.isAtom, hS.mem_of_isAtom_of_le_sSup_atoms, isAtom, le_antisymm, le_top, le_top.trans, mem_of_isAtom_of_le_sSup_atoms, sSup_le_sSup
-/
lemma eq_atoms_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    S = {a : α | IsAtom a} := by
  apply le_antisymm
  · exact hS.isAtom
  intro a ha
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ ha (sSup_le_sSup hT)

end BooleanGenerators

end IsCompactlyGenerated
