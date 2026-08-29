/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser
-/
module

public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.ModularLattice
public import Mathlib.Tactic.FinCases

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `Finset.SupIndep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `sSupIndep s`: a set of elements are supremum independent.
* `iSupIndep f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `Finset.supIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.sSupIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.iSupIndep_iff_pairwiseDisjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `Finset.SupIndep.pairwiseDisjoint`
  * `sSupIndep.pairwiseDisjoint`
  * `iSupIndep.pairwiseDisjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/

@[expose] public section


variable {α β ι ι' : Type*}

/-! ### On lattices with a bottom element, via `Finset.sup` -/


namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

/--
Definition of `SupIndep` / `SupIndep` 的定义

English:
definition SupIndep
  signature: (s : Finset ι) (f : ι -> α)
  body: forall ⦃t⦄, t subseteq s -> forall ⦃i⦄, i in s -> i ∉ t -> Disjoint (f i) (t.sup f)

中文:
定义 SupIndep
  签名: (s : 有限集 ι) (f : ι -> α)
  定义体: forall ⦃t⦄, t subseteq s -> forall ⦃i⦄, i in s -> i ∉ t -> Disjoint (f i) (t.sup f)

Depends on / 依赖: Disjoint, subseteq, t.sup
-/
def SupIndep (s : Finset ι) (f : ι -> α) : Prop :=
  forall ⦃t⦄, t subseteq s -> forall ⦃i⦄, i in s -> i ∉ t -> Disjoint (f i) (t.sup f)

variable {s t : Finset ι} {f g : ι -> α} {i : ι}

/--
theorem `supIndep_iff_disjoint_erase` / 定理 `supIndep_iff_disjoint_erase`

English:
theorem supIndep_iff_disjoint_erase
  given: [DecidableEq ι]
  proof: ⟨fun hs _ hi => hs (erase_subset _ _) hi (notMem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

中文:
定理 supIndep_iff_disjoint_erase
  条件: [DecidableEq ι]
  证明: ⟨fun hs _ hi => hs (erase_subset _ _) hi (notMem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.sup_eq_bot_iff, MvPolynomial, MvPolynomial.eq_zero_iff, WithBot, WithBot.coe_ne_bot, coe_ne_bot, eq_zero_iff, erase_subset, forall_congr, mem_erase, mem_support_iff, mono_right, ne_of_mem_of_not_mem, notMem_erase, not_not, sup_eq_bot_iff, sup_mono
-/
theorem supIndep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ forall i in s, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs _ hi => hs (erase_subset _ _) hi (notMem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: ι] [DecidableEq α] : Decidable (SupIndep s f)
  body: have : forall i, Decidable (Disjoint (f i) ((s.erase i).sup f)) := fun _ =>
    decidable_of_iff _ disjoint_iff.symm
  decidable_of_iff _ supIndep_iff_disjoint_erase.symm

中文:
实例 [DecidableEq
  签名: ι] [DecidableEq α] : 可判定 (SupIndep s f)
  定义体: have : forall i, Decidable (Disjoint (f i) ((s.erase i).sup f)) := fun _ =>
    decidable_of_iff _ disjoint_iff.symm
  decidable_of_iff _ supIndep_iff_disjoint_erase.symm

Depends on / 依赖: Decidable, Disjoint, Finset, Finset.sup_empty, decidable_of_iff, disjoint_iff, disjoint_iff.symm, s.erase, supIndep_iff_disjoint_erase, supIndep_iff_disjoint_erase.symm, sup_empty, support_zero, weightedTotalDegree
-/
instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) :=
  have : forall i, Decidable (Disjoint (f i) ((s.erase i).sup f)) := fun _ =>
    decidable_of_iff _ disjoint_iff.symm
  decidable_of_iff _ supIndep_iff_disjoint_erase.symm

/--
theorem `SupIndep.subset` / 定理 `SupIndep.subset`

English:
theorem SupIndep.subset
  given: (ht : t.SupIndep f) (h : s subseteq t)
  statement: s.SupIndep f
  proof: fun _ hu _ hi =>
  ht (hu.trans h) (h hi)

中文:
定理 SupIndep.subset
  条件: (ht : t.SupIndep f) (h : s subseteq t)
  结论: s.SupIndep f
  证明: fun _ hu _ hi =>
  ht (hu.trans h) (h hi)
-/
theorem SupIndep.subset (ht : t.SupIndep f) (h : s subseteq t) : s.SupIndep f := fun _ hu _ hi =>
  ht (hu.trans h) (h hi)

/--
lemma `SupIndep.mono` / 引理 `SupIndep.mono`

English:
lemma SupIndep.mono
  given: (hf : s.SupIndep f) (h : forall i in s, g i <= f i)
  statement: s.SupIndep g
  proof: fun _ ht j hj htj => (hf ht hj htj).mono (h j hj) (sup_mono_fun fun b a => h b (ht a))

@[simp, grind ←]

中文:
引理 SupIndep.mono
  条件: (hf : s.SupIndep f) (h : 对任意 i in s, g i <= f i)
  结论: s.SupIndep g
  证明: fun _ ht j hj htj => (hf ht hj htj).mono (h j hj) (sup_mono_fun fun b a => h b (ht a))

@[simp, grind ←]

Depends on / 依赖: sup_mono_fun
-/
lemma SupIndep.mono (hf : s.SupIndep f) (h : forall i in s, g i <= f i) : s.SupIndep g :=
  fun _ ht j hj htj => (hf ht hj htj).mono (h j hj) (sup_mono_fun fun b a => h b (ht a))

@[simp, grind ←]
/--
theorem `supIndep_empty` / 定理 `supIndep_empty`

English:
theorem supIndep_empty
  given: (f : ι -> α)
  statement: (∅ : Finset ι).SupIndep f
  proof: fun _ _ a ha =>
  (notMem_empty a ha).elim

@[simp, grind ←]

中文:
定理 supIndep_empty
  条件: (f : ι -> α)
  结论: (∅ : 有限集 ι).SupIndep f
  证明: fun _ _ a ha =>
  (notMem_empty a ha).elim

@[simp, grind ←]
-/
theorem supIndep_empty (f : ι -> α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha =>
  (notMem_empty a ha).elim

@[simp, grind ←]
/--
theorem `supIndep_singleton` / 定理 `supIndep_singleton`

English:
theorem supIndep_singleton
  given: (i : ι) (f : ι -> α)
  statement: ({i} : Finset ι).SupIndep f
  proof: fun s hs j hji hj => by
    rw [eq_empty_of_ssubset_singleton ⟨hs]; rw [fun h => hj (h hji)⟩]; rw [sup_empty]
    exact disjoint_bot_right

中文:
定理 supIndep_singleton
  条件: (i : ι) (f : ι -> α)
  结论: ({i} : 有限集 ι).SupIndep f
  证明: fun s hs j hji hj => by
    rw [eq_empty_of_ssubset_singleton ⟨hs]; rw [fun h => hj (h hji)⟩]; rw [sup_empty]
    exact disjoint_bot_right

Depends on / 依赖: disjoint_bot_right, eq_empty_of_ssubset_singleton, sup_empty
-/
theorem supIndep_singleton (i : ι) (f : ι -> α) : ({i} : Finset ι).SupIndep f :=
  fun s hs j hji hj => by
    rw [eq_empty_of_ssubset_singleton ⟨hs]; rw [fun h => hj (h hji)⟩]; rw [sup_empty]
    exact disjoint_bot_right

/--
theorem `SupIndep.pairwiseDisjoint` / 定理 `SupIndep.pairwiseDisjoint`

English:
theorem SupIndep.pairwiseDisjoint
  given: (hs : s.SupIndep f)
  statement: (s : Set ι).PairwiseDisjoint f
  proof: fun _ ha _ hb hab =>
sup_singleton.subst hs (singleton_subset_iff.2 hb) ha notMem_singleton.2 hab

中文:
定理 SupIndep.pairwiseDisjoint
  条件: (hs : s.SupIndep f)
  结论: (s : 集合 ι).PairwiseDisjoint f
  证明: fun _ ha _ hb hab =>
sup_singleton.subst hs (singleton_subset_iff.2 hb) ha notMem_singleton.2 hab

Depends on / 依赖: notMem_singleton, singleton_subset_iff, sup_singleton, sup_singleton.subst
-/
theorem SupIndep.pairwiseDisjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f :=
  fun _ ha _ hb hab =>
sup_singleton.subst hs (singleton_subset_iff.2 hb) ha notMem_singleton.2 hab

/--
theorem `SupIndep.le_sup_iff` / 定理 `SupIndep.le_sup_iff`

English:
theorem SupIndep.le_sup_iff
  given: (hs : s.SupIndep f) (hts : t subseteq s) (hi : i in s) (hf : forall i, f i != ⊥)
  proof: by
  refine ⟨fun h => ?_, le_sup⟩
  by_contra hit
  exact hf i (disjoint_self.1 <| (hs hts hi hit).mono_right h)

中文:
定理 SupIndep.le_sup_iff
  条件: (hs : s.SupIndep f) (hts : t subseteq s) (hi : i in s) (hf : 对任意 i, f i != ⊥)
  证明: by
  refine ⟨fun h => ?_, le_sup⟩
  by_contra hit
  exact hf i (disjoint_self.1 <| (hs hts hi hit).mono_right h)

Depends on / 依赖: disjoint_self, le_sup, mono_right
-/
theorem SupIndep.le_sup_iff (hs : s.SupIndep f) (hts : t subseteq s) (hi : i in s) (hf : forall i, f i != ⊥) :
    f i <= t.sup f ↔ i in t := by
  refine ⟨fun h => ?_, le_sup⟩
  by_contra hit
  exact hf i (disjoint_self.1 <| (hs hts hi hit).mono_right h)

/--
theorem `SupIndep.antitone_fun` / 定理 `SupIndep.antitone_fun`

English:
theorem SupIndep.antitone_fun
  given: {g : ι -> α} (hle : forall x in s, f x <= g x) (h : s.SupIndep g)
  proof: fun _t hts i his hit =>
(h hts his hit).mono (hle i his) Finset.sup_mono_fun fun x hx => hle x hts hx

中文:
定理 SupIndep.antitone_fun
  条件: {g : ι -> α} (hle : 对任意 x in s, f x <= g x) (h : s.SupIndep g)
  证明: fun _t hts i his hit =>
(h hts his hit).mono (hle i his) Finset.sup_mono_fun fun x hx => hle x hts hx
-/
theorem SupIndep.antitone_fun {g : ι -> α} (hle : forall x in s, f x <= g x) (h : s.SupIndep g) :
    s.SupIndep f := fun _t hts i his hit =>
(h hts his hit).mono (hle i his) Finset.sup_mono_fun fun x hx => hle x hts hx

/--
theorem `SupIndep.image` / 定理 `SupIndep.image`

English:
theorem SupIndep.image
  statement: [DecidableEq ι] {s : Finset ι'} {g : ι' -> ι}
  proof: by
  intro t ht i hi hit
  rcases subset_image_iff.mp ht with ⟨t, hts, rfl⟩
  rcases mem_image.mp hi with ⟨i, his, rfl⟩
  rw [sup_image]
  exact hs hts his (hit <| mem_image_of_mem _ ·)

中文:
定理 SupIndep.像
  结论: [DecidableEq ι] {s : 有限集 ι'} {g : ι' -> ι}
  证明: by
  intro t ht i hi hit
  rcases subset_image_iff.mp ht with ⟨t, hts, rfl⟩
  rcases mem_image.mp hi with ⟨i, his, rfl⟩
  rw [sup_image]
  exact hs hts his (hit <| mem_image_of_mem _ ·)
-/
protected theorem SupIndep.image [DecidableEq ι] {s : Finset ι'} {g : ι' -> ι}
    (hs : s.SupIndep (f ∘ g)) : (s.image g).SupIndep f := by
  intro t ht i hi hit
  rcases subset_image_iff.mp ht with ⟨t, hts, rfl⟩
  rcases mem_image.mp hi with ⟨i, his, rfl⟩
  rw [sup_image]
  exact hs hts his (hit <| mem_image_of_mem _ ·)

/--
theorem `supIndep_map` / 定理 `supIndep_map`

English:
theorem supIndep_map
  given: {s : Finset ι'} {g : ι' ↪ ι}
  statement: (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g)
  proof: by
  refine ⟨fun hs t ht i hi hit => ?_, fun hs => ?_⟩
  · rw [← sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact hs.image

@[simp]

中文:
定理 supIndep_map
  条件: {s : 有限集 ι'} {g : ι' ↪ ι}
  结论: (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g)
  证明: by
  refine ⟨fun hs t ht i hi hit => ?_, fun hs => ?_⟩
  · rw [← sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact hs.image

@[simp]

Depends on / 依赖: classical, hs.image, map_eq_image, map_subset_map, mem_map, sup_map
-/
theorem supIndep_map {s : Finset ι'} {g : ι' ↪ ι} : (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g) := by
  refine ⟨fun hs t ht i hi hit => ?_, fun hs => ?_⟩
  · rw [← sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact hs.image

@[simp]
/--
theorem `supIndep_pair` / 定理 `supIndep_pair`

English:
theorem supIndep_pair
  given: [DecidableEq ι] {i j : ι} (hij : i != j)
  proof: by
  suffices Disjoint (f i) (f j) -> Disjoint (f j) ((Finset.erase {i, j} j).sup f) by
    simpa [supIndep_iff_disjoint_erase, hij]
  rw [pair_comm]
  simp [hij.symm, disjoint_comm]

中文:
定理 supIndep_pair
  条件: [DecidableEq ι] {i j : ι} (hij : i != j)
  证明: by
  suffices Disjoint (f i) (f j) -> Disjoint (f j) ((Finset.erase {i, j} j).sup f) by
    simpa [supIndep_iff_disjoint_erase, hij]
  rw [pair_comm]
  simp [hij.symm, disjoint_comm]

Depends on / 依赖: Disjoint, Finset, Finset.erase, disjoint_comm, hij.symm, pair_comm, supIndep_iff_disjoint_erase
-/
theorem supIndep_pair [DecidableEq ι] {i j : ι} (hij : i != j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) := by
  suffices Disjoint (f i) (f j) -> Disjoint (f j) ((Finset.erase {i, j} j).sup f) by
    simpa [supIndep_iff_disjoint_erase, hij]
  rw [pair_comm]
  simp [hij.symm, disjoint_comm]

/--
theorem `supIndep_univ_bool` / 定理 `supIndep_univ_bool`

English:
theorem supIndep_univ_bool
  given: (f : Bool -> α)
  proof: haveI : true != false := by simp only [Ne, not_false_iff, reduceCtorEq]
  (supIndep_pair this).trans disjoint_comm

@[simp]

中文:
定理 supIndep_univ_bool
  条件: (f : 布尔值 -> α)
  证明: haveI : true != false := by simp only [Ne, not_false_iff, reduceCtorEq]
  (supIndep_pair this).trans disjoint_comm

@[simp]

Depends on / 依赖: disjoint_comm, not_false_iff, reduceCtorEq, supIndep_pair
-/
theorem supIndep_univ_bool (f : Bool -> α) :
    (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  haveI : true != false := by simp only [Ne, not_false_iff, reduceCtorEq]
  (supIndep_pair this).trans disjoint_comm

@[simp]
/--
theorem `supIndep_univ_fin_two` / 定理 `supIndep_univ_fin_two`

English:
theorem supIndep_univ_fin_two
  given: (f : Fin 2 -> α)
  proof: have : (0 : Fin 2) != 1 := by simp
  supIndep_pair this

@[simp]

中文:
定理 supIndep_univ_fin_two
  条件: (f : 有限集 2 -> α)
  证明: have : (0 : Fin 2) != 1 := by simp
  supIndep_pair this

@[simp]

Depends on / 依赖: supIndep_pair
-/
theorem supIndep_univ_fin_two (f : Fin 2 -> α) :
    (Finset.univ : Finset (Fin 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  have : (0 : Fin 2) != 1 := by simp
  supIndep_pair this

@[simp]
/--
theorem `supIndep_attach` / 定理 `supIndep_attach`

English:
theorem supIndep_attach
  statement: (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f
  proof: by
  simpa [Finset.attach_map_val] using! (supIndep_map (s := s.attach) (g := .subtype _)).symm

alias ⟨_, SupIndep.attach⟩ := supIndep_attach

中文:
定理 supIndep_attach
  结论: (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f
  证明: by
  simpa [Finset.attach_map_val] using! (supIndep_map (s := s.attach) (g := .subtype _)).symm

alias ⟨_, SupIndep.attach⟩ := supIndep_attach

Depends on / 依赖: Finset, Finset.attach_map_val, attach, attach_map_val, s.attach, subtype, supIndep_map
-/
theorem supIndep_attach : (s.attach.SupIndep fun a => f a) ↔ s.SupIndep f := by
  simpa [Finset.attach_map_val] using! (supIndep_map (s := s.attach) (g := .subtype _)).symm

alias ⟨_, SupIndep.attach⟩ := supIndep_attach

end Lattice

section IsModularLattice

variable [Lattice α] [IsModularLattice α] [OrderBot α] {s : Finset ι} {f : ι -> α}

/--
theorem `SupIndep.biUnion` / 定理 `SupIndep.biUnion`

English:
theorem SupIndep.biUnion
  statement: [DecidableEq ι] {s : Finset ι'} {g : ι' -> Finset ι} {f : ι -> α}
  proof: by
  classical
  intro a ha b hb hab
  obtain ⟨i', hi', hb⟩ := mem_biUnion.mp hb
  let t := s.erase i'
  let u := (g i').erase b
apply Disjoint.mono_right calc
    a.sup f <= (t.biUnion g union u).sup f := by grind
    _ <= (t.sup fun i => (g i).sup f) ⊔ (u.sup f) := by grind
  symm
  apply Disjoint.disjoint_sup_left_of_disjoint_sup_right
  · exact (supIndep_iff_disjoint_erase.mp (hg i' hi') b hb).symm
  · rw [← sup_singleton (f := f) (b := b), ← sup_union, show u union {b} = g i' by grind]
    exact (supIndep_iff_disjoint_erase.mp hs i' hi').symm

中文:
定理 SupIndep.biUnion
  结论: [DecidableEq ι] {s : 有限集 ι'} {g : ι' -> 有限集 ι} {f : ι -> α}
  证明: by
  classical
  intro a ha b hb hab
  obtain ⟨i', hi', hb⟩ := mem_biUnion.mp hb
  let t := s.erase i'
  let u := (g i').erase b
apply Disjoint.mono_right calc
    a.sup f <= (t.biUnion g union u).sup f := by grind
    _ <= (t.sup fun i => (g i).sup f) ⊔ (u.sup f) := by grind
  symm
  apply Disjoint.disjoint_sup_left_of_disjoint_sup_right
  · exact (supIndep_iff_disjoint_erase.mp (hg i' hi') b hb).symm
  · rw [← sup_singleton (f := f) (b := b), ← sup_union, show u union {b} = g i' by grind]
    exact (supIndep_iff_disjoint_erase.mp hs i' hi').symm
-/
protected theorem SupIndep.biUnion [DecidableEq ι] {s : Finset ι'} {g : ι' -> Finset ι} {f : ι -> α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : forall i' in s, (g i').SupIndep f) :
    (s.biUnion g).SupIndep f := by
  classical
  intro a ha b hb hab
  obtain ⟨i', hi', hb⟩ := mem_biUnion.mp hb
  let t := s.erase i'
  let u := (g i').erase b
apply Disjoint.mono_right calc
    a.sup f <= (t.biUnion g union u).sup f := by grind
    _ <= (t.sup fun i => (g i).sup f) ⊔ (u.sup f) := by grind
  symm
  apply Disjoint.disjoint_sup_left_of_disjoint_sup_right
  · exact (supIndep_iff_disjoint_erase.mp (hg i' hi') b hb).symm
  · rw [← sup_singleton (f := f) (b := b), ← sup_union, show u union {b} = g i' by grind]
    exact (supIndep_iff_disjoint_erase.mp hs i' hi').symm

/--
theorem `SupIndep.sup` / 定理 `SupIndep.sup`

English:
theorem SupIndep.sup
  statement: [DecidableEq ι] {s : Finset ι'} {g : ι' -> Finset ι} {f : ι -> α}
  proof: by
  rw [sup_eq_biUnion]
  exact hs.biUnion hg

中文:
定理 SupIndep.上确界
  结论: [DecidableEq ι] {s : 有限集 ι'} {g : ι' -> 有限集 ι} {f : ι -> α}
  证明: by
  rw [sup_eq_biUnion]
  exact hs.biUnion hg
-/
protected theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' -> Finset ι} {f : ι -> α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : forall i' in s, (g i').SupIndep f) :
    (s.sup g).SupIndep f := by
  rw [sup_eq_biUnion]
  exact hs.biUnion hg

/--
theorem `SupIndep.sigma` / 定理 `SupIndep.sigma`

English:
theorem SupIndep.sigma
  statement: {β : ι -> Type*} {s : Finset ι} {g : forall i, Finset (β i)}
  proof: by
  classical
  rw [Finset.sigma_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · simpa [Finset.supIndep_map] using! hg

中文:
定理 SupIndep.sigma
  结论: {β : ι -> 类型} {s : 有限集 ι} {g : 对任意 i, 有限集 (β i)}
  证明: by
  classical
  rw [Finset.sigma_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · simpa [Finset.supIndep_map] using! hg
-/
protected theorem SupIndep.sigma {β : ι -> Type*} {s : Finset ι} {g : forall i, Finset (β i)}
    {f : Sigma β -> α} (hs : s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩)
    (hg : forall i in s, (g i).SupIndep fun b => f ⟨i, b⟩) : (s.sigma g).SupIndep f := by
  classical
  rw [Finset.sigma_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · simpa [Finset.supIndep_map] using! hg

/--
theorem `SupIndep.product` / 定理 `SupIndep.product`

English:
theorem SupIndep.product
  statement: {s : Finset ι} {t : Finset ι'} {f : ι × ι' -> α}
  proof: by
  classical
  rw [Finset.product_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · exact fun i' hi' => (ht.mono fun i hi => Finset.le_sup (f := fun i' => f (i', i)) hi').image

中文:
定理 SupIndep.product
  结论: {s : 有限集 ι} {t : 有限集 ι'} {f : ι × ι' -> α}
  证明: by
  classical
  rw [Finset.product_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · exact fun i' hi' => (ht.mono fun i hi => Finset.le_sup (f := fun i' => f (i', i)) hi').image
-/
protected theorem SupIndep.product {s : Finset ι} {t : Finset ι'} {f : ι × ι' -> α}
    (hs : s.SupIndep fun i => t.sup fun i' => f (i, i'))
    (ht : t.SupIndep fun i' => s.sup fun i => f (i, i')) : (s ×ˢ t).SupIndep f := by
  classical
  rw [Finset.product_eq_biUnion]
  apply Finset.SupIndep.biUnion
  · simpa using! hs
  · exact fun i' hi' => (ht.mono fun i hi => Finset.le_sup (f := fun i' => f (i', i)) hi').image

/--
theorem `SupIndep.disjoint_sup_sup` / 定理 `SupIndep.disjoint_sup_sup`

English:
theorem SupIndep.disjoint_sup_sup
  statement: {s : Finset ι} {f : ι -> α} {u v : Finset ι}
  proof: by
  classical
  induction u using Finset.induction generalizing v with
  | empty => simp
  | insert x u hx ih =>
    grind [= SupIndep, Disjoint.disjoint_sup_left_of_disjoint_sup_right]

中文:
定理 SupIndep.disjoint_sup_sup
  结论: {s : 有限集 ι} {f : ι -> α} {u v : 有限集 ι}
  证明: by
  classical
  induction u using Finset.induction generalizing v with
  | empty => simp
  | insert x u hx ih =>
    grind [= SupIndep, Disjoint.disjoint_sup_left_of_disjoint_sup_right]
-/
protected theorem SupIndep.disjoint_sup_sup {s : Finset ι} {f : ι -> α} {u v : Finset ι}
    (hs : s.SupIndep f) (hu : u subseteq s) (hv : v subseteq s) (huv : Disjoint u v) :
    Disjoint (u.sup f) (v.sup f) := by
  classical
  induction u using Finset.induction generalizing v with
  | empty => simp
  | insert x u hx ih =>
    grind [= SupIndep, Disjoint.disjoint_sup_left_of_disjoint_sup_right]

/--
theorem `supIndep_sigma_iff'` / 定理 `supIndep_sigma_iff'`

English:
theorem supIndep_sigma_iff'
  statement: {β : ι -> Type*} {s : Finset ι} {g : forall i, Finset (β i)}
  proof: by
  classical
  refine ⟨fun h => ⟨fun t _ i _ _ => ?_, fun i _ t _ j _ _ => ?_⟩, fun h => h.1.sigma h.2⟩
  · let u := (g i).map (Function.Embedding.sigmaMk i)
    let v := t.biUnion (fun j => (g j).map (Function.Embedding.sigmaMk j))
    suffices Disjoint (u.sup f) (v.sup f) by simpa only [sup_map, sup_biUnion, u, v]
    apply SupIndep.disjoint_sup_sup h <;> grind [disjoint_left]
  · suffices Disjoint (f ⟨i, j⟩) ((t.image fun b => ⟨i, b⟩).sup f) by simpa only [sup_image]
    grind [= SupIndep]

中文:
定理 supIndep_sigma_iff'
  结论: {β : ι -> 类型} {s : 有限集 ι} {g : 对任意 i, 有限集 (β i)}
  证明: by
  classical
  refine ⟨fun h => ⟨fun t _ i _ _ => ?_, fun i _ t _ j _ _ => ?_⟩, fun h => h.1.sigma h.2⟩
  · let u := (g i).map (Function.Embedding.sigmaMk i)
    let v := t.biUnion (fun j => (g j).map (Function.Embedding.sigmaMk j))
    suffices Disjoint (u.sup f) (v.sup f) by simpa only [sup_map, sup_biUnion, u, v]
    apply SupIndep.disjoint_sup_sup h <;> grind [disjoint_left]
  · suffices Disjoint (f ⟨i, j⟩) ((t.image fun b => ⟨i, b⟩).sup f) by simpa only [sup_image]
    grind [= SupIndep]

Depends on / 依赖: Disjoint, Embedding, Function, Function.Embedding.sigmaMk, SupIndep, SupIndep.disjoint_sup_sup, biUnion, classical, disjoint_left, disjoint_sup_sup, sigmaMk, sup_biUnion, sup_image, sup_map, t.biUnion, t.image, u.sup, v.sup
-/
theorem supIndep_sigma_iff' {β : ι -> Type*} {s : Finset ι} {g : forall i, Finset (β i)}
    {f : Sigma β -> α} : (s.sigma g).SupIndep f ↔ (s.SupIndep fun i => (g i).sup fun b => f ⟨i, b⟩)
      ∧ forall i in s, (g i).SupIndep fun b => f ⟨i, b⟩ := by
  classical
  refine ⟨fun h => ⟨fun t _ i _ _ => ?_, fun i _ t _ j _ _ => ?_⟩, fun h => h.1.sigma h.2⟩
  · let u := (g i).map (Function.Embedding.sigmaMk i)
    let v := t.biUnion (fun j => (g j).map (Function.Embedding.sigmaMk j))
    suffices Disjoint (u.sup f) (v.sup f) by simpa only [sup_map, sup_biUnion, u, v]
    apply SupIndep.disjoint_sup_sup h <;> grind [disjoint_left]
  · suffices Disjoint (f ⟨i, j⟩) ((t.image fun b => ⟨i, b⟩).sup f) by simpa only [sup_image]
    grind [= SupIndep]

/--
theorem `supIndep_product_iff` / 定理 `supIndep_product_iff`

English:
theorem supIndep_product_iff
  given: {s : Finset ι} {t : Finset ι'} {f : ι × ι' -> α}
  proof: by
  classical
  refine ⟨fun h => ⟨fun u _ i _ _ => ?_, fun u _ i _ _ => ?_⟩, fun h => h.1.product h.2⟩
  · suffices Disjoint ((t.image ((i, ·))).sup f) ((u ×ˢ t).sup f) by
      simpa only [sup_image, sup_product_left]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]
  · suffices Disjoint ((s.image ((·, i))).sup f) ((s ×ˢ u).sup f) by
      simpa only [sup_image, sup_product_right]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]

中文:
定理 supIndep_product_iff
  条件: {s : 有限集 ι} {t : 有限集 ι'} {f : ι × ι' -> α}
  证明: by
  classical
  refine ⟨fun h => ⟨fun u _ i _ _ => ?_, fun u _ i _ _ => ?_⟩, fun h => h.1.product h.2⟩
  · suffices Disjoint ((t.image ((i, ·))).sup f) ((u ×ˢ t).sup f) by
      simpa only [sup_image, sup_product_left]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]
  · suffices Disjoint ((s.image ((·, i))).sup f) ((s ×ˢ u).sup f) by
      simpa only [sup_image, sup_product_right]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]

Depends on / 依赖: Disjoint, Finset, Finset.SupIndep.disjoint_sup_sup, SupIndep, classical, disjoint_left, disjoint_sup_sup, product, product_eq_sprod, s.image, sup_image, sup_product_left, sup_product_right, t.image
-/
theorem supIndep_product_iff {s : Finset ι} {t : Finset ι'} {f : ι × ι' -> α} :
    (s.product t).SupIndep f ↔ (s.SupIndep fun i => t.sup fun i' => f (i, i'))
      ∧ t.SupIndep fun i' => s.sup fun i => f (i, i') := by
  classical
  refine ⟨fun h => ⟨fun u _ i _ _ => ?_, fun u _ i _ _ => ?_⟩, fun h => h.1.product h.2⟩
  · suffices Disjoint ((t.image ((i, ·))).sup f) ((u ×ˢ t).sup f) by
      simpa only [sup_image, sup_product_left]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]
  · suffices Disjoint ((s.image ((·, i))).sup f) ((s ×ˢ u).sup f) by
      simpa only [sup_image, sup_product_right]
    grind [Finset.SupIndep.disjoint_sup_sup, = product_eq_sprod, = disjoint_left]

/--
theorem `SupIndep.union` / 定理 `SupIndep.union`

English:
theorem SupIndep.union
  statement: [DecidableEq ι] {s t : Finset ι} {f : ι -> α}
  proof: by
  rw [show s union t = ({s]; rw [t} : Finset _).biUnion id by simp]
  grind [SupIndep.biUnion, supIndep_pair]

中文:
定理 SupIndep.union
  结论: [DecidableEq ι] {s t : 有限集 ι} {f : ι -> α}
  证明: by
  rw [show s union t = ({s]; rw [t} : Finset _).biUnion id by simp]
  grind [SupIndep.biUnion, supIndep_pair]
-/
protected theorem SupIndep.union [DecidableEq ι] {s t : Finset ι} {f : ι -> α}
    (hs : s.SupIndep f) (ht : t.SupIndep f) (h : Disjoint (s.sup f) (t.sup f)) :
    (s union t).SupIndep f := by
  rw [show s union t = ({s]; rw [t} : Finset _).biUnion id by simp]
  grind [SupIndep.biUnion, supIndep_pair]

/--
theorem `SupIndep.insert` / 定理 `SupIndep.insert`

English:
theorem SupIndep.insert
  statement: [DecidableEq ι] {i : ι} {s : Finset ι} {f : ι -> α}
  proof: by
  grind [insert_eq, SupIndep.union, sup_singleton]

中文:
定理 SupIndep.insert
  结论: [DecidableEq ι] {i : ι} {s : 有限集 ι} {f : ι -> α}
  证明: by
  grind [insert_eq, SupIndep.union, sup_singleton]
-/
protected theorem SupIndep.insert [DecidableEq ι] {i : ι} {s : Finset ι} {f : ι -> α}
    (hs : s.SupIndep f) (h : Disjoint (f i) (s.sup f)) : (insert i s).SupIndep f := by
  grind [insert_eq, SupIndep.union, sup_singleton]

end IsModularLattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι -> α}

/--
theorem `supIndep_iff_pairwiseDisjoint` / 定理 `supIndep_iff_pairwiseDisjoint`

English:
theorem supIndep_iff_pairwiseDisjoint
  statement: s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f
  proof: ⟨SupIndep.pairwiseDisjoint, fun hs _ ht _ hi hit =>
    Finset.disjoint_sup_right.2 fun _ hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.supIndep⟩ := supIndep_iff_pairwiseDisjoint

中文:
定理 supIndep_iff_pairwiseDisjoint
  结论: s.SupIndep f ↔ (s : 集合 ι).PairwiseDisjoint f
  证明: ⟨SupIndep.pairwiseDisjoint, fun hs _ ht _ hi hit =>
    Finset.disjoint_sup_right.2 fun _ hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.supIndep⟩ := supIndep_iff_pairwiseDisjoint

Depends on / 依赖: Finset, Finset.disjoint_sup_right, SupIndep, SupIndep.pairwiseDisjoint, disjoint_sup_right, ne_of_mem_of_not_mem, pairwiseDisjoint
-/
theorem supIndep_iff_pairwiseDisjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwiseDisjoint, fun hs _ ht _ hi hit =>
    Finset.disjoint_sup_right.2 fun _ hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.supIndep⟩ := supIndep_iff_pairwiseDisjoint

end DistribLattice

end Finset

/-! ### On complete lattices via `sSup` -/

section CompleteLattice
variable [CompleteLattice α]

open Set Function

/--
Definition of `sSupIndep` / `sSupIndep` 的定义

English:
definition sSupIndep
  signature: (s : Set α)
  body: forall ⦃a⦄, a in s -> Disjoint a (sSup (s \ {a}))

中文:
定义 sSupIndep
  签名: (s : 集合 α)
  定义体: forall ⦃a⦄, a in s -> Disjoint a (sSup (s \ {a}))

Depends on / 依赖: Disjoint
-/
def sSupIndep (s : Set α) : Prop :=
  forall ⦃a⦄, a in s -> Disjoint a (sSup (s \ {a}))

variable {s : Set α} (hs : sSupIndep s)

@[simp]
/--
theorem `sSupIndep_empty` / 定理 `sSupIndep_empty`

English:
theorem sSupIndep_empty
  statement: sSupIndep (∅ : Set α)
  proof: fun x hx =>
  (Set.notMem_empty x hx).elim

include hs in

中文:
定理 sSupIndep_empty
  结论: sSupIndep (∅ : 集合 α)
  证明: fun x hx =>
  (Set.notMem_empty x hx).elim

include hs in
-/
theorem sSupIndep_empty : sSupIndep (∅ : Set α) := fun x hx =>
  (Set.notMem_empty x hx).elim

include hs in
/--
theorem `sSupIndep.mono` / 定理 `sSupIndep.mono`

English:
theorem sSupIndep.mono
  given: {t : Set α} (hst : t subseteq s)
  statement: sSupIndep t
  proof: fun _ ha =>
  (hs (hst ha)).mono_right (sSup_le_sSup (sdiff_subset_sdiff_left hst))

include hs in

中文:
定理 sSupIndep.mono
  条件: {t : 集合 α} (hst : t subseteq s)
  结论: sSupIndep t
  证明: fun _ ha =>
  (hs (hst ha)).mono_right (sSup_le_sSup (sdiff_subset_sdiff_left hst))

include hs in
-/
theorem sSupIndep.mono {t : Set α} (hst : t subseteq s) : sSupIndep t := fun _ ha =>
  (hs (hst ha)).mono_right (sSup_le_sSup (sdiff_subset_sdiff_left hst))

include hs in
/--
theorem `sSupIndep.pairwiseDisjoint` / 定理 `sSupIndep.pairwiseDisjoint`

English:
theorem sSupIndep.pairwiseDisjoint
  statement: s.PairwiseDisjoint id
  proof: fun _ hx y hy h =>
  disjoint_sSup_right (hs hx) ((mem_sdiff y).mpr ⟨hy, h.symm⟩)

中文:
定理 sSupIndep.pairwiseDisjoint
  结论: s.PairwiseDisjoint id
  证明: fun _ hx y hy h =>
  disjoint_sSup_right (hs hx) ((mem_sdiff y).mpr ⟨hy, h.symm⟩)
-/
theorem sSupIndep.pairwiseDisjoint : s.PairwiseDisjoint id := fun _ hx y hy h =>
  disjoint_sSup_right (hs hx) ((mem_sdiff y).mpr ⟨hy, h.symm⟩)

/--
theorem `sSupIndep_singleton` / 定理 `sSupIndep_singleton`

English:
theorem sSupIndep_singleton
  given: (a : α)
  statement: sSupIndep ({a} : Set α)
  proof: fun i hi => by
  simp_all

中文:
定理 sSupIndep_singleton
  条件: (a : α)
  结论: sSupIndep ({a} : 集合 α)
  证明: fun i hi => by
  simp_all
-/
theorem sSupIndep_singleton (a : α) : sSupIndep ({a} : Set α) := fun i hi => by
  simp_all

/--
theorem `sSupIndep_pair` / 定理 `sSupIndep_pair`

English:
theorem sSupIndep_pair
  given: {a b : α} (hab : a != b)
  proof: by
  constructor
  · intro h
    exact h.pairwiseDisjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert! h using 1
      simp [hab, sSup_singleton]
    · convert! h.symm using 1
      simp [hab, sSup_singleton]

include hs in

中文:
定理 sSupIndep_pair
  条件: {a b : α} (hab : a != b)
  证明: by
  constructor
  · intro h
    exact h.pairwiseDisjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert! h using 1
      simp [hab, sSup_singleton]
    · convert! h.symm using 1
      simp [hab, sSup_singleton]

include hs in

Depends on / 依赖: convert, h.pairwiseDisjoint, h.symm, mem_insert, mem_insert_of_mem, mem_singleton, pairwiseDisjoint, sSup_singleton
-/
theorem sSupIndep_pair {a b : α} (hab : a != b) :
    sSupIndep ({a, b} : Set α) ↔ Disjoint a b := by
  constructor
  · intro h
    exact h.pairwiseDisjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert! h using 1
      simp [hab, sSup_singleton]
    · convert! h.symm using 1
      simp [hab, sSup_singleton]

include hs in
/--
theorem `sSupIndep.disjoint_sSup` / 定理 `sSupIndep.disjoint_sSup`

English:
theorem sSupIndep.disjoint_sSup
  given: {x : α} {y : Set α} (hx : x in s) (hy : y subseteq s) (hxy : x ∉ y)
  proof: by
  have := (hs.mono <| insert_subset_iff.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_sdiff_of_mem _ (mem_singleton _)]; rw [sdiff_singleton_eq_self hxy] at this
  exact this

中文:
定理 sSupIndep.disjoint_sSup
  条件: {x : α} {y : 集合 α} (hx : x in s) (hy : y subseteq s) (hxy : x ∉ y)
  证明: by
  have := (hs.mono <| insert_subset_iff.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_sdiff_of_mem _ (mem_singleton _)]; rw [sdiff_singleton_eq_self hxy] at this
  exact this

Depends on / 依赖: hs.mono, insert_sdiff_of_mem, insert_subset_iff, insert_subset_iff.mpr, mem_insert, mem_singleton, sdiff_singleton_eq_self
-/
theorem sSupIndep.disjoint_sSup {x : α} {y : Set α} (hx : x in s) (hy : y subseteq s) (hxy : x ∉ y) :
    Disjoint x (sSup y) := by
  have := (hs.mono <| insert_subset_iff.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_sdiff_of_mem _ (mem_singleton _)]; rw [sdiff_singleton_eq_self hxy] at this
  exact this

/--
Definition of `iSupIndep` / `iSupIndep` 的定义

English:
definition iSupIndep
  signature: {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι -> α)
  body: forall i : ι, Disjoint (t i) (⨆ (j) (_ : j != i), t j)

中文:
定义 iSupIndep
  签名: {ι : 类型层*} {α : 类型} [完备格 α] (t : ι -> α)
  定义体: forall i : ι, Disjoint (t i) (⨆ (j) (_ : j != i), t j)

Depends on / 依赖: Disjoint
-/
def iSupIndep {ι : Sort*} {α : Type*} [CompleteLattice α] (t : ι -> α) : Prop :=
  forall i : ι, Disjoint (t i) (⨆ (j) (_ : j != i), t j)

/--
theorem `sSupIndep_iff` / 定理 `sSupIndep_iff`

English:
theorem sSupIndep_iff
  given: {α : Type*} [CompleteLattice α] (s : Set α)
  proof: by
  simp_rw [iSupIndep, sSupIndep, SetCoe.forall, sSup_eq_iSup]
  refine forall₂_congr fun a ha => ?_
  simp [iSup_subtype, iSup_and]

中文:
定理 sSupIndep_iff
  条件: {α : 类型} [完备格 α] (s : 集合 α)
  证明: by
  simp_rw [iSupIndep, sSupIndep, SetCoe.forall, sSup_eq_iSup]
  refine forall₂_congr fun a ha => ?_
  simp [iSup_subtype, iSup_and]

Depends on / 依赖: SetCoe, SetCoe.forall, iSupIndep, iSup_and, iSup_subtype, sSupIndep, sSup_eq_iSup, simp_rw
-/
theorem sSupIndep_iff {α : Type*} [CompleteLattice α] (s : Set α) :
    sSupIndep s ↔ iSupIndep ((↑) : s -> α) := by
  simp_rw [iSupIndep, sSupIndep, SetCoe.forall, sSup_eq_iSup]
  refine forall₂_congr fun a ha => ?_
  simp [iSup_subtype, iSup_and]

variable {t : ι -> α} (ht : iSupIndep t)

/--
theorem `iSupIndep_def` / 定理 `iSupIndep_def`

English:
theorem iSupIndep_def
  statement: iSupIndep t ↔ forall i, Disjoint (t i) (⨆ (j) (_ : j != i), t j)
  proof: Iff.rfl

中文:
定理 iSupIndep_def
  结论: iSupIndep t ↔ 对任意 i, Disjoint (t i) (⨆ (j) (_ : j != i), t j)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem iSupIndep_def : iSupIndep t ↔ forall i, Disjoint (t i) (⨆ (j) (_ : j != i), t j) :=
  Iff.rfl

/--
theorem `iSupIndep_def'` / 定理 `iSupIndep_def'`

English:
theorem iSupIndep_def'
  statement: iSupIndep t ↔ forall i, Disjoint (t i) (sSup (t '' { j | j != i }))
  proof: by
  simp_rw [sSup_image]
  rfl

中文:
定理 iSupIndep_def'
  结论: iSupIndep t ↔ 对任意 i, Disjoint (t i) (sSup (t '' { j | j != i }))
  证明: by
  simp_rw [sSup_image]
  rfl

Depends on / 依赖: sSup_image, simp_rw
-/
theorem iSupIndep_def' : iSupIndep t ↔ forall i, Disjoint (t i) (sSup (t '' { j | j != i })) := by
  simp_rw [sSup_image]
  rfl

/--
theorem `iSupIndep_def''` / 定理 `iSupIndep_def''`

English:
theorem iSupIndep_def''
  proof: by
  rw [iSupIndep_def']
  aesop

@[simp]

中文:
定理 iSupIndep_def''
  证明: by
  rw [iSupIndep_def']
  aesop

@[simp]

Depends on / 依赖: iSupIndep_def
-/
theorem iSupIndep_def'' :
    iSupIndep t ↔ forall i, Disjoint (t i) (sSup { a | exists j != i, t j = a }) := by
  rw [iSupIndep_def']
  aesop

@[simp]
/--
theorem `iSupIndep_subsingleton` / 定理 `iSupIndep_subsingleton`

English:
theorem iSupIndep_subsingleton
  given: [Subsingleton ι] (t : ι -> α)
  statement: iSupIndep t
  proof: fun i => by simp [← Subsingleton.elim i]

include ht in

中文:
定理 iSupIndep_subsingleton
  条件: [子单例 ι] (t : ι -> α)
  结论: iSupIndep t
  证明: fun i => by simp [← Subsingleton.elim i]

include ht in

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem iSupIndep_subsingleton [Subsingleton ι] (t : ι -> α) : iSupIndep t :=
  fun i => by simp [← Subsingleton.elim i]

include ht in
/--
theorem `iSupIndep.pairwiseDisjoint` / 定理 `iSupIndep.pairwiseDisjoint`

English:
theorem iSupIndep.pairwiseDisjoint
  statement: Pairwise (Disjoint on t)
  proof: fun x y h =>
  disjoint_sSup_right (ht x) ⟨y, iSup_pos h.symm⟩

中文:
定理 iSupIndep.pairwiseDisjoint
  结论: 两两 (Disjoint on t)
  证明: fun x y h =>
  disjoint_sSup_right (ht x) ⟨y, iSup_pos h.symm⟩
-/
theorem iSupIndep.pairwiseDisjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_sSup_right (ht x) ⟨y, iSup_pos h.symm⟩

/--
theorem `iSupIndep.mono` / 定理 `iSupIndep.mono`

English:
theorem iSupIndep.mono
  given: {s t : ι -> α} (hs : iSupIndep s) (hst : t <= s)
  statement: iSupIndep t
  proof: fun i => (hs i).mono (hst i) iSup₂_mono fun j _ => hst j

中文:
定理 iSupIndep.mono
  条件: {s t : ι -> α} (hs : iSupIndep s) (hst : t <= s)
  结论: iSupIndep t
  证明: fun i => (hs i).mono (hst i) iSup₂_mono fun j _ => hst j
-/
theorem iSupIndep.mono {s t : ι -> α} (hs : iSupIndep s) (hst : t <= s) : iSupIndep t :=
fun i => (hs i).mono (hst i) iSup₂_mono fun j _ => hst j

/--
theorem `iSupIndep.comp` / 定理 `iSupIndep.comp`

English:
theorem iSupIndep.comp
  statement: {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep t)
  proof: fun i =>
(ht (f i)).mono_right by
    refine (iSup_mono fun i => ?_).trans (iSup_comp_le _ f)
    exact iSup_const_mono hf.ne

中文:
定理 iSupIndep.comp
  结论: {ι ι' : 类型层*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep t)
  证明: fun i =>
(ht (f i)).mono_right by
    refine (iSup_mono fun i => ?_).trans (iSup_comp_le _ f)
    exact iSup_const_mono hf.ne
-/
theorem iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep t)
    (hf : Injective f) : iSupIndep (t ∘ f) := fun i =>
(ht (f i)).mono_right by
    refine (iSup_mono fun i => ?_).trans (iSup_comp_le _ f)
    exact iSup_const_mono hf.ne

/--
theorem `iSupIndep.comp'` / 定理 `iSupIndep.comp'`

English:
theorem iSupIndep.comp'
  statement: {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep <| t ∘ f)
  proof: by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.iSup_comp]
  exact (ht i').mono_right (biSup_mono fun j' hij => mt (congr_arg f) hij)

中文:
定理 iSupIndep.comp'
  结论: {ι ι' : 类型层*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep <| t ∘ f)
  证明: by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.iSup_comp]
  exact (ht i').mono_right (biSup_mono fun j' hij => mt (congr_arg f) hij)

Depends on / 依赖: biSup_mono, congr_arg, hf.iSup_comp, iSup_comp, mono_right
-/
theorem iSupIndep.comp' {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι} (ht : iSupIndep <| t ∘ f)
    (hf : Surjective f) : iSupIndep t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.iSup_comp]
  exact (ht i').mono_right (biSup_mono fun j' hij => mt (congr_arg f) hij)

/--
theorem `iSupIndep.sSupIndep_range` / 定理 `iSupIndep.sSupIndep_range`

English:
theorem iSupIndep.sSupIndep_range
  given: (ht : iSupIndep t)
  statement: sSupIndep range t
  proof: by
  rw [sSupIndep_iff]
  rw [← coe_comp_rangeFactorization t] at ht
  exact ht.comp' rangeFactorization_surjective

@[simp]

中文:
定理 iSupIndep.sSupIndep_range
  条件: (ht : iSupIndep t)
  结论: sSupIndep range t
  证明: by
  rw [sSupIndep_iff]
  rw [← coe_comp_rangeFactorization t] at ht
  exact ht.comp' rangeFactorization_surjective

@[simp]

Depends on / 依赖: coe_comp_rangeFactorization, ht.comp, rangeFactorization_surjective, sSupIndep_iff
-/
theorem iSupIndep.sSupIndep_range (ht : iSupIndep t) : sSupIndep range t := by
  rw [sSupIndep_iff]
  rw [← coe_comp_rangeFactorization t] at ht
  exact ht.comp' rangeFactorization_surjective

@[simp]
/--
theorem `iSupIndep_ne_bot` / 定理 `iSupIndep_ne_bot`

English:
theorem iSupIndep_ne_bot
  proof: by
  refine ⟨fun h => ?_, fun h => h.comp Subtype.val_injective⟩
  simp only [iSupIndep_def] at h ⊢
  intro i
  cases eq_or_ne (t i) ⊥ with
  | inl hi => simp [hi]
  | inr hi => ?_
  convert! h ⟨i, hi⟩
  have : forall j, ⨆ (_ : t j = ⊥), t j = ⊥ := fun j => by simp only [iSup_eq_bot, imp_self]
  rw [iSup_split _ (fun j => t j = ⊥)]; rw [iSup_subtype]
  simp only [iSup_comm (ι' := _ != i), this, ne_eq, sup_of_le_right, Subtype.mk.injEq, iSup_bot,
    bot_le]

中文:
定理 iSupIndep_ne_bot
  证明: by
  refine ⟨fun h => ?_, fun h => h.comp Subtype.val_injective⟩
  simp only [iSupIndep_def] at h ⊢
  intro i
  cases eq_or_ne (t i) ⊥ with
  | inl hi => simp [hi]
  | inr hi => ?_
  convert! h ⟨i, hi⟩
  have : forall j, ⨆ (_ : t j = ⊥), t j = ⊥ := fun j => by simp only [iSup_eq_bot, imp_self]
  rw [iSup_split _ (fun j => t j = ⊥)]; rw [iSup_subtype]
  simp only [iSup_comm (ι' := _ != i), this, ne_eq, sup_of_le_right, Subtype.mk.injEq, iSup_bot,
    bot_le]

Depends on / 依赖: Subtype, Subtype.mk.injEq, Subtype.val_injective, bot_le, convert, eq_or_ne, h.comp, iSupIndep_def, iSup_bot, iSup_comm, iSup_eq_bot, iSup_split, iSup_subtype, imp_self, ne_eq, sup_of_le_right, val_injective
-/
theorem iSupIndep_ne_bot :
    iSupIndep (fun i : {i // t i != ⊥} => t i) ↔ iSupIndep t := by
  refine ⟨fun h => ?_, fun h => h.comp Subtype.val_injective⟩
  simp only [iSupIndep_def] at h ⊢
  intro i
  cases eq_or_ne (t i) ⊥ with
  | inl hi => simp [hi]
  | inr hi => ?_
  convert! h ⟨i, hi⟩
  have : forall j, ⨆ (_ : t j = ⊥), t j = ⊥ := fun j => by simp only [iSup_eq_bot, imp_self]
  rw [iSup_split _ (fun j => t j = ⊥)]; rw [iSup_subtype]
  simp only [iSup_comm (ι' := _ != i), this, ne_eq, sup_of_le_right, Subtype.mk.injEq, iSup_bot,
    bot_le]

/--
theorem `iSupIndep.injOn` / 定理 `iSupIndep.injOn`

English:
theorem iSupIndep.injOn
  given: (ht : iSupIndep t)
  statement: InjOn t {i | t i != ⊥}
  proof: by
  rintro i _ j (hj : t j != ⊥) h
  by_contra! contra
  apply hj
  suffices t j <= ⨆ (k) (_ : k != i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j != i := Ne.symm contra
  -- Porting note: needs explicit `f`
  exact le_iSup₂ (f := fun x _ => t x) j contra

中文:
定理 iSupIndep.injOn
  条件: (ht : iSupIndep t)
  结论: 单射限制 t {i | t i != ⊥}
  证明: by
  rintro i _ j (hj : t j != ⊥) h
  by_contra! contra
  apply hj
  suffices t j <= ⨆ (k) (_ : k != i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j != i := Ne.symm contra
  -- Porting note: needs explicit `f`
  exact le_iSup₂ (f := fun x _ => t x) j contra

Depends on / 依赖: Ne.symm, contra, disjoint_self, mono_right, replace
-/
theorem iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i != ⊥} := by
  rintro i _ j (hj : t j != ⊥) h
  by_contra! contra
  apply hj
  suffices t j <= ⨆ (k) (_ : k != i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j != i := Ne.symm contra
  -- Porting note: needs explicit `f`
  exact le_iSup₂ (f := fun x _ => t x) j contra

/--
lemma `iSupIndep.injOn_iInf` / 引理 `iSupIndep.injOn_iInf`

English:
lemma iSupIndep.injOn_iInf
  given: {β : ι -> Type*} (t : (i : ι) -> β i -> α) (ht : forall i, iSupIndep (t i))
  proof: by
  intro b₁ hb₁ b₂ hb₂ h_eq
  beta_reduce at h_eq
  by_contra h_ne
  obtain ⟨i, hi⟩ : exists i, b₁ i != b₂ i := Function.ne_iff.mp h_ne
  have := calc
    ⨅ i, t i (b₁ i) <= t i (b₁ i) ⊓ t i (b₂ i) := le_inf (iInf_le ..) (h_eq ▸ iInf_le ..)
    _ = ⊥ := (ht i (b₁ i) |>.mono_right <| le_iSup₂_of_le (b₂ i) hi.symm le_rfl).eq_bot
  simp_all

中文:
引理 iSupIndep.injOn_iInf
  条件: {β : ι -> 类型} (t : (i : ι) -> β i -> α) (ht : 对任意 i, iSupIndep (t i))
  证明: by
  intro b₁ hb₁ b₂ hb₂ h_eq
  beta_reduce at h_eq
  by_contra h_ne
  obtain ⟨i, hi⟩ : exists i, b₁ i != b₂ i := Function.ne_iff.mp h_ne
  have := calc
    ⨅ i, t i (b₁ i) <= t i (b₁ i) ⊓ t i (b₂ i) := le_inf (iInf_le ..) (h_eq ▸ iInf_le ..)
    _ = ⊥ := (ht i (b₁ i) |>.mono_right <| le_iSup₂_of_le (b₂ i) hi.symm le_rfl).eq_bot
  simp_all

Depends on / 依赖: Function, Function.ne_iff.mp, beta_reduce, eq_bot, h_eq, h_ne, hi.symm, iInf_le, le_inf, le_rfl, mono_right, ne_iff
-/
lemma iSupIndep.injOn_iInf {β : ι -> Type*} (t : (i : ι) -> β i -> α) (ht : forall i, iSupIndep (t i)) :
    InjOn (fun b : (i : ι) -> β i => ⨅ i, t i (b i)) {b | ⨅ i, t i (b i) != ⊥} := by
  intro b₁ hb₁ b₂ hb₂ h_eq
  beta_reduce at h_eq
  by_contra h_ne
  obtain ⟨i, hi⟩ : exists i, b₁ i != b₂ i := Function.ne_iff.mp h_ne
  have := calc
    ⨅ i, t i (b₁ i) <= t i (b₁ i) ⊓ t i (b₂ i) := le_inf (iInf_le ..) (h_eq ▸ iInf_le ..)
    _ = ⊥ := (ht i (b₁ i) |>.mono_right <| le_iSup₂_of_le (b₂ i) hi.symm le_rfl).eq_bot
  simp_all

/--
theorem `iSupIndep.injective` / 定理 `iSupIndep.injective`

English:
theorem iSupIndep.injective
  given: (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥)
  statement: Injective t
  proof: by
  suffices univ = {i | t i != ⊥} by simpa [← this] using ht.injOn
  simp_all

中文:
定理 iSupIndep.injective
  条件: (ht : iSupIndep t) (h_ne_bot : 对任意 i, t i != ⊥)
  结论: 单射 t
  证明: by
  suffices univ = {i | t i != ⊥} by simpa [← this] using ht.injOn
  simp_all

Depends on / 依赖: ht.injOn
-/
theorem iSupIndep.injective (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥) : Injective t := by
  suffices univ = {i | t i != ⊥} by simpa [← this] using ht.injOn
  simp_all

/--
theorem `iSupIndep_pair` / 定理 `iSupIndep_pair`

English:
theorem iSupIndep_pair
  given: {i j : ι} (hij : i != j) (huniv : forall k, k = i ∨ k = j)
  proof: by
  constructor
  · exact fun h => h.pairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine h.mono_right (iSup_le fun i => iSup_le fun hi => Eq.le ?_)
      rw [(huniv i).resolve_left hi]
    · refine h.symm.mono_right (iSup_le fun j => iSup_le fun hj => Eq.le ?_)
      rw [(huniv j).resolve_right hj]

@[simp]

中文:
定理 iSupIndep_pair
  条件: {i j : ι} (hij : i != j) (huniv : 对任意 k, k = i ∨ k = j)
  证明: by
  constructor
  · exact fun h => h.pairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine h.mono_right (iSup_le fun i => iSup_le fun hi => Eq.le ?_)
      rw [(huniv i).resolve_left hi]
    · refine h.symm.mono_right (iSup_le fun j => iSup_le fun hj => Eq.le ?_)
      rw [(huniv j).resolve_right hj]

@[simp]

Depends on / 依赖: Eq.le, h.mono_right, h.pairwiseDisjoint, h.symm.mono_right, iSup_le, mono_right, pairwiseDisjoint, resolve_left, resolve_right
-/
theorem iSupIndep_pair {i j : ι} (hij : i != j) (huniv : forall k, k = i ∨ k = j) :
    iSupIndep t ↔ Disjoint (t i) (t j) := by
  constructor
  · exact fun h => h.pairwiseDisjoint hij
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine h.mono_right (iSup_le fun i => iSup_le fun hi => Eq.le ?_)
      rw [(huniv i).resolve_left hi]
    · refine h.symm.mono_right (iSup_le fun j => iSup_le fun hj => Eq.le ?_)
      rw [(huniv j).resolve_right hj]

@[simp]
/--
lemma `iSup_fin_three` / 引理 `iSup_fin_three`

English:
lemma iSup_fin_three
  given: {α : Type*} [CompleteLattice α] {f : Fin 3 -> α}
  proof: by
  suffices ⨆ i in Finset.univ, f i = f 0 ⊔ f 1 ⊔ f 2 by simp [← this]
  rw [← Finset.sup_eq_iSup]; rw [show (Finset.univ : Finset (Fin 3)) = {0]; rw [1]; rw [2} from rfl]
  simp [sup_assoc]

中文:
引理 iSup_fin_three
  条件: {α : 类型} [完备格 α] {f : 有限集 3 -> α}
  证明: by
  suffices ⨆ i in Finset.univ, f i = f 0 ⊔ f 1 ⊔ f 2 by simp [← this]
  rw [← Finset.sup_eq_iSup]; rw [show (Finset.univ : Finset (Fin 3)) = {0]; rw [1]; rw [2} from rfl]
  simp [sup_assoc]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, Finset.univ, sup_assoc, sup_eq_iSup
-/
lemma iSup_fin_three {α : Type*} [CompleteLattice α] {f : Fin 3 -> α} :
    ⨆ i, f i = f 0 ⊔ f 1 ⊔ f 2 := by
  suffices ⨆ i in Finset.univ, f i = f 0 ⊔ f 1 ⊔ f 2 by simp [← this]
  rw [← Finset.sup_eq_iSup]; rw [show (Finset.univ : Finset (Fin 3)) = {0]; rw [1]; rw [2} from rfl]
  simp [sup_assoc]

/--
lemma `iSupIndep_fin_three` / 引理 `iSupIndep_fin_three`

English:
lemma iSupIndep_fin_three
  given: {α : Type*} [CompleteLattice α] {f : Fin 3 -> α}
  proof: by
  rw [iSupIndep_def]; rw [sup_comm (f 2) (f 0)]
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun ⟨h₀, h₁, h₂⟩ i => ?_⟩
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · fin_cases i <;> simpa

中文:
引理 iSupIndep_fin_three
  条件: {α : 类型} [完备格 α] {f : 有限集 3 -> α}
  证明: by
  rw [iSupIndep_def]; rw [sup_comm (f 2) (f 0)]
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun ⟨h₀, h₁, h₂⟩ i => ?_⟩
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · fin_cases i <;> simpa

Depends on / 依赖: fin_cases, iSupIndep_def, sup_comm
-/
lemma iSupIndep_fin_three {α : Type*} [CompleteLattice α] {f : Fin 3 -> α} :
    iSupIndep f ↔
      Disjoint (f 0) (f 1 ⊔ f 2) ∧
      Disjoint (f 1) (f 2 ⊔ f 0) ∧
      Disjoint (f 2) (f 0 ⊔ f 1) := by
  rw [iSupIndep_def]; rw [sup_comm (f 2) (f 0)]
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun ⟨h₀, h₁, h₂⟩ i => ?_⟩
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · fin_cases i <;> simpa

/--
theorem `iSupIndep.map_orderIso` / 定理 `iSupIndep.map_orderIso`

English:
theorem iSupIndep.map_orderIso
  statement: {ι : Sort*} {α β : Type*} [CompleteLattice α]
  proof: fun i => ((ha i).map_orderIso f).mono_right (f.monotone.le_map_iSup₂ _)

@[simp]

中文:
定理 iSupIndep.map_orderIso
  结论: {ι : 类型层*} {α β : 类型} [完备格 α]
  证明: fun i => ((ha i).map_orderIso f).mono_right (f.monotone.le_map_iSup₂ _)

@[simp]

Depends on / 依赖: DirectSum, _root_, _root_.DirectSum.coeLinearMap_eq_dfinsuppSum, coeLinearMap_eq_dfinsuppSum, f.monotone.le_map_iSup, map_orderIso, mono_right, monotone
-/
theorem iSupIndep.map_orderIso {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι -> α} (ha : iSupIndep a) : iSupIndep (f ∘ a) :=
  fun i => ((ha i).map_orderIso f).mono_right (f.monotone.le_map_iSup₂ _)

@[simp]
/--
theorem `iSupIndep_map_orderIso_iff` / 定理 `iSupIndep_map_orderIso_iff`

English:
theorem iSupIndep_map_orderIso_iff
  statement: {ι : Sort*} {α β : Type*} [CompleteLattice α]
  proof: ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩

中文:
定理 iSupIndep_map_orderIso_iff
  结论: {ι : 类型层*} {α β : 类型} [完备格 α]
  证明: ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩

Depends on / 依赖: comp_eq_id, congr_arg, f.left_inv.comp_eq_id, f.symm, h.map_orderIso, left_inv, map_orderIso
-/
theorem iSupIndep_map_orderIso_iff {ι : Sort*} {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSupIndep (f ∘ a) ↔ iSupIndep a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_orderIso f.symm,
    fun h => h.map_orderIso f⟩

/--
theorem `iSupIndep.disjoint_biSup` / 定理 `iSupIndep.disjoint_biSup`

English:
theorem iSupIndep.disjoint_biSup
  statement: {ι : Type*} {α : Type*} [CompleteLattice α] {t : ι -> α}
  proof: Disjoint.mono_right (biSup_mono fun _ hi => (ne_of_mem_of_not_mem hi hx :)) (ht x)

中文:
定理 iSupIndep.disjoint_biSup
  结论: {ι : 类型} {α : 类型} [完备格 α] {t : ι -> α}
  证明: Disjoint.mono_right (biSup_mono fun _ hi => (ne_of_mem_of_not_mem hi hx :)) (ht x)

Depends on / 依赖: Disjoint, Disjoint.mono_right, biSup_mono, mono_right, ne_of_mem_of_not_mem
-/
theorem iSupIndep.disjoint_biSup {ι : Type*} {α : Type*} [CompleteLattice α] {t : ι -> α}
    (ht : iSupIndep t) {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i in y, t i) :=
  Disjoint.mono_right (biSup_mono fun _ hi => (ne_of_mem_of_not_mem hi hx :)) (ht x)

/--
lemma `iSupIndep.of_coe_Iic_comp` / 引理 `iSupIndep.of_coe_Iic_comp`

English:
lemma iSupIndep.of_coe_Iic_comp
  statement: {ι : Sort*} {a : α} {t : ι -> Set.Iic a}
  proof: by
  intro i x
  specialize ht i
  simp_rw [Function.comp_apply, ← Set.Iic.coe_iSup] at ht
  exact @ht x

中文:
引理 iSupIndep.of_coe_Iic_comp
  结论: {ι : 类型层*} {a : α} {t : ι -> 集合.左无界右闭区间 a}
  证明: by
  intro i x
  specialize ht i
  simp_rw [Function.comp_apply, ← Set.Iic.coe_iSup] at ht
  exact @ht x

Depends on / 依赖: Function, Function.comp_apply, Set.Iic.coe_iSup, coe_iSup, comp_apply, simp_rw, specialize
-/
lemma iSupIndep.of_coe_Iic_comp {ι : Sort*} {a : α} {t : ι -> Set.Iic a}
    (ht : iSupIndep ((↑) ∘ t : ι -> α)) : iSupIndep t := by
  intro i x
  specialize ht i
  simp_rw [Function.comp_apply, ← Set.Iic.coe_iSup] at ht
  exact @ht x

/--
theorem `iSupIndep_comp_coe_iff_supIndep` / 定理 `iSupIndep_comp_coe_iff_supIndep`

English:
theorem iSupIndep_comp_coe_iff_supIndep
  given: {s : Finset ι} {f : ι -> α}
  proof: by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine Subtype.forall.trans (forall₂_congr fun a b => ?_)
    rw [Finset.sup_eq_iSup]
    congr! 1
    refine iSup_subtype.trans ?_
    congr! 1
    simp [iSup_and, @iSup_comm _ (_ in s)]

alias ⟨iSupIndep.supIndep, Finset.SupIndep.independent⟩ := iSupIndep_comp_coe_iff_supIndep

中文:
定理 iSupIndep_comp_coe_iff_supIndep
  条件: {s : 有限集 ι} {f : ι -> α}
  证明: by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine Subtype.forall.trans (forall₂_congr fun a b => ?_)
    rw [Finset.sup_eq_iSup]
    congr! 1
    refine iSup_subtype.trans ?_
    congr! 1
    simp [iSup_and, @iSup_comm _ (_ in s)]

alias ⟨iSupIndep.supIndep, Finset.SupIndep.independent⟩ := iSupIndep_comp_coe_iff_supIndep

Depends on / 依赖: Finset, Finset.supIndep_iff_disjoint_erase, Finset.sup_eq_iSup, Subtype, Subtype.forall.trans, classical, iSup_and, iSup_comm, iSup_subtype, iSup_subtype.trans, supIndep_iff_disjoint_erase, sup_eq_iSup
-/
theorem iSupIndep_comp_coe_iff_supIndep {s : Finset ι} {f : ι -> α} :
    iSupIndep (f ∘ ((↑) : s -> ι)) ↔ s.SupIndep f := by
  classical
    rw [Finset.supIndep_iff_disjoint_erase]
    refine Subtype.forall.trans (forall₂_congr fun a b => ?_)
    rw [Finset.sup_eq_iSup]
    congr! 1
    refine iSup_subtype.trans ?_
    congr! 1
    simp [iSup_and, @iSup_comm _ (_ in s)]

alias ⟨iSupIndep.supIndep, Finset.SupIndep.independent⟩ := iSupIndep_comp_coe_iff_supIndep

/--
theorem `iSupIndep.supIndep'` / 定理 `iSupIndep.supIndep'`

English:
theorem iSupIndep.supIndep'
  given: {f : ι -> α} (s : Finset ι) (h : iSupIndep f)
  statement: s.SupIndep f
  proof: iSupIndep.supIndep (h.comp Subtype.coe_injective)

中文:
定理 iSupIndep.supIndep'
  条件: {f : ι -> α} (s : 有限集 ι) (h : iSupIndep f)
  结论: s.SupIndep f
  证明: iSupIndep.supIndep (h.comp Subtype.coe_injective)

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, h.comp, iSupIndep, iSupIndep.supIndep, supIndep
-/
theorem iSupIndep.supIndep' {f : ι -> α} (s : Finset ι) (h : iSupIndep f) : s.SupIndep f :=
  iSupIndep.supIndep (h.comp Subtype.coe_injective)

/--
theorem `iSupIndep_iff_supIndep_univ` / 定理 `iSupIndep_iff_supIndep_univ`

English:
theorem iSupIndep_iff_supIndep_univ
  given: [Fintype ι] {f : ι -> α}
  proof: by
  classical
    simp [Finset.supIndep_iff_disjoint_erase, iSupIndep, Finset.sup_eq_iSup]

alias ⟨iSupIndep.sup_indep_univ, Finset.SupIndep.iSupIndep_of_univ⟩ := iSupIndep_iff_supIndep_univ

中文:
定理 iSupIndep_iff_supIndep_univ
  条件: [有限类型 ι] {f : ι -> α}
  证明: by
  classical
    simp [Finset.supIndep_iff_disjoint_erase, iSupIndep, Finset.sup_eq_iSup]

alias ⟨iSupIndep.sup_indep_univ, Finset.SupIndep.iSupIndep_of_univ⟩ := iSupIndep_iff_supIndep_univ

Depends on / 依赖: Finset, Finset.supIndep_iff_disjoint_erase, Finset.sup_eq_iSup, classical, iSupIndep, supIndep_iff_disjoint_erase, sup_eq_iSup
-/
theorem iSupIndep_iff_supIndep_univ [Fintype ι] {f : ι -> α} :
    iSupIndep f ↔ Finset.univ.SupIndep f := by
  classical
    simp [Finset.supIndep_iff_disjoint_erase, iSupIndep, Finset.sup_eq_iSup]

alias ⟨iSupIndep.sup_indep_univ, Finset.SupIndep.iSupIndep_of_univ⟩ := iSupIndep_iff_supIndep_univ

/--
lemma `iSupIndep.le_iff_eq_of_iSup_eq_top` / 引理 `iSupIndep.le_iff_eq_of_iSup_eq_top`

English:
lemma iSupIndep.le_iff_eq_of_iSup_eq_top
  statement: [IsModularLattice α] {f g : ι -> α}
  proof: by
  refine ⟨fun h₃ => funext fun i => ?_, le_of_eq⟩
  replace h₁ : Disjoint (⨆ (j) (_ : j != i), f j) (g i) :=
    Disjoint.mono_left (iSup₂_mono fun j _ => h₃ j) (h₁ i).symm
  replace h₂ : Codisjoint (f i) (⨆ (j) (_ : j != i), f j) := by
    rw [codisjoint_iff]; rw [← iSup_split_single f i]; rw [h₂]
  exact (le_iff_eq_of_codisjoint_of_disjoint h₂ h₁).mp (h₃ i)

中文:
引理 iSupIndep.le_iff_eq_of_iSup_eq_top
  结论: [是Modular格 α] {f g : ι -> α}
  证明: by
  refine ⟨fun h₃ => funext fun i => ?_, le_of_eq⟩
  replace h₁ : Disjoint (⨆ (j) (_ : j != i), f j) (g i) :=
    Disjoint.mono_left (iSup₂_mono fun j _ => h₃ j) (h₁ i).symm
  replace h₂ : Codisjoint (f i) (⨆ (j) (_ : j != i), f j) := by
    rw [codisjoint_iff]; rw [← iSup_split_single f i]; rw [h₂]
  exact (le_iff_eq_of_codisjoint_of_disjoint h₂ h₁).mp (h₃ i)

Depends on / 依赖: Codisjoint, Disjoint, Disjoint.mono_left, codisjoint_iff, iSup_split_single, le_iff_eq_of_codisjoint_of_disjoint, le_of_eq, mono_left, replace
-/
lemma iSupIndep.le_iff_eq_of_iSup_eq_top [IsModularLattice α] {f g : ι -> α}
    (h₁ : iSupIndep g) (h₂ : iSup f = ⊤) :
    f <= g ↔ f = g := by
  refine ⟨fun h₃ => funext fun i => ?_, le_of_eq⟩
  replace h₁ : Disjoint (⨆ (j) (_ : j != i), f j) (g i) :=
    Disjoint.mono_left (iSup₂_mono fun j _ => h₃ j) (h₁ i).symm
  replace h₂ : Codisjoint (f i) (⨆ (j) (_ : j != i), f j) := by
    rw [codisjoint_iff]; rw [← iSup_split_single f i]; rw [h₂]
  exact (le_iff_eq_of_codisjoint_of_disjoint h₂ h₁).mp (h₃ i)

/--
lemma `iSupIndep.disjoint_biSup_biSup'` / 引理 `iSupIndep.disjoint_biSup_biSup'`

English:
lemma iSupIndep.disjoint_biSup_biSup'
  statement: [IsModularLattice α]
  proof: by
  suffices forall (s : Finset ι) (hst : Disjoint ↑s t), Disjoint (⨆ i in s, f i) (⨆ i in t, f i) by
    specialize this hs.toFinset
    aesop
  clear! s
  intro s hst
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simp
  | insert j s₀ hj ih =>
    have hjt : j ∉ t := by aesop
    replace hst : Disjoint ↑s₀ (insert j t) := by aesop
    replace ih : Disjoint (⨆ i in s₀, f i) (f j ⊔ ⨆ i in t, f i) := by
      specialize ih hst
      rwa [iSup_insert] at ih
    have : Disjoint (f j) ((⨆ i in t, f i) ⊔ (⨆ i in (s₀ : Set ι), f i)) := by
      rw [← iSup_union]
exact disjoint_biSup hf by aesop
    rw [s₀.iSup_insert j f]; rw [disjoint_comm]; rw [sup_comm]
    exact disjoint_sup_right_of_disjoint_sup_right ih this

中文:
引理 iSupIndep.disjoint_biSup_biSup'
  结论: [是Modular格 α]
  证明: by
  suffices forall (s : Finset ι) (hst : Disjoint ↑s t), Disjoint (⨆ i in s, f i) (⨆ i in t, f i) by
    specialize this hs.toFinset
    aesop
  clear! s
  intro s hst
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simp
  | insert j s₀ hj ih =>
    have hjt : j ∉ t := by aesop
    replace hst : Disjoint ↑s₀ (insert j t) := by aesop
    replace ih : Disjoint (⨆ i in s₀, f i) (f j ⊔ ⨆ i in t, f i) := by
      specialize ih hst
      rwa [iSup_insert] at ih
    have : Disjoint (f j) ((⨆ i in t, f i) ⊔ (⨆ i in (s₀ : Set ι), f i)) := by
      rw [← iSup_union]
exact disjoint_biSup hf by aesop
    rw [s₀.iSup_insert j f]; rw [disjoint_comm]; rw [sup_comm]
    exact disjoint_sup_right_of_disjoint_sup_right ih this

Depends on / 依赖: Disjoint, Finset, Finset.induction_on, classical, generalizing, hs.toFinset, iSup_insert, induction_on, insert, replace, specialize, toFinset
-/
lemma iSupIndep.disjoint_biSup_biSup' [IsModularLattice α]
    {f : ι -> α} {s t : Set ι} (hf : iSupIndep f) (hst : Disjoint s t) (hs : s.Finite) :
    Disjoint (⨆ i in s, f i) (⨆ i in t, f i) := by
  suffices forall (s : Finset ι) (hst : Disjoint ↑s t), Disjoint (⨆ i in s, f i) (⨆ i in t, f i) by
    specialize this hs.toFinset
    aesop
  clear! s
  intro s hst
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simp
  | insert j s₀ hj ih =>
    have hjt : j ∉ t := by aesop
    replace hst : Disjoint ↑s₀ (insert j t) := by aesop
    replace ih : Disjoint (⨆ i in s₀, f i) (f j ⊔ ⨆ i in t, f i) := by
      specialize ih hst
      rwa [iSup_insert] at ih
    have : Disjoint (f j) ((⨆ i in t, f i) ⊔ (⨆ i in (s₀ : Set ι), f i)) := by
      rw [← iSup_union]
exact disjoint_biSup hf by aesop
    rw [s₀.iSup_insert j f]; rw [disjoint_comm]; rw [sup_comm]
    exact disjoint_sup_right_of_disjoint_sup_right ih this

/--
lemma `iSupIndep.mem_of_biSup_eq_top` / 引理 `iSupIndep.mem_of_biSup_eq_top`

English:
lemma iSupIndep.mem_of_biSup_eq_top
  statement: {f : ι -> α} {s : Set ι}
  proof: by
  by_contra contra
replace h₁ : Disjoint (f i) (⨆ i in s, f i) := (h₁ i).mono_right biSup_mono by aesop
  aesop

中文:
引理 iSupIndep.mem_of_biSup_eq_top
  结论: {f : ι -> α} {s : 集合 ι}
  证明: by
  by_contra contra
replace h₁ : Disjoint (f i) (⨆ i in s, f i) := (h₁ i).mono_right biSup_mono by aesop
  aesop

Depends on / 依赖: Disjoint, biSup_mono, contra, mono_right, replace
-/
lemma iSupIndep.mem_of_biSup_eq_top {f : ι -> α} {s : Set ι}
    (h₁ : iSupIndep f) (h₂ : ⨆ i in s, f i = ⊤) {i : ι} (hi : f i != ⊥) :
    i in s := by
  by_contra contra
replace h₁ : Disjoint (f i) (⨆ i in s, f i) := (h₁ i).mono_right biSup_mono by aesop
  aesop

end CompleteLattice

section Frame
variable [Order.Frame α]

/--
theorem `sSupIndep_iff_pairwiseDisjoint` / 定理 `sSupIndep_iff_pairwiseDisjoint`

English:
theorem sSupIndep_iff_pairwiseDisjoint
  given: {s : Set α}
  statement: sSupIndep s ↔ s.PairwiseDisjoint id
  proof: ⟨sSupIndep.pairwiseDisjoint, fun hs _ hi =>
disjoint_sSup_iff.2 fun _ hj => hs hi hj.1 Ne.symm hj.2⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.sSupIndep⟩ := sSupIndep_iff_pairwiseDisjoint

中文:
定理 sSupIndep_iff_pairwiseDisjoint
  条件: {s : 集合 α}
  结论: sSupIndep s ↔ s.PairwiseDisjoint id
  证明: ⟨sSupIndep.pairwiseDisjoint, fun hs _ hi =>
disjoint_sSup_iff.2 fun _ hj => hs hi hj.1 Ne.symm hj.2⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.sSupIndep⟩ := sSupIndep_iff_pairwiseDisjoint

Depends on / 依赖: Ne.symm, disjoint_sSup_iff, pairwiseDisjoint, sSupIndep, sSupIndep.pairwiseDisjoint
-/
theorem sSupIndep_iff_pairwiseDisjoint {s : Set α} : sSupIndep s ↔ s.PairwiseDisjoint id :=
  ⟨sSupIndep.pairwiseDisjoint, fun hs _ hi =>
disjoint_sSup_iff.2 fun _ hj => hs hi hj.1 Ne.symm hj.2⟩

alias ⟨_, _root_.Set.PairwiseDisjoint.sSupIndep⟩ := sSupIndep_iff_pairwiseDisjoint

open scoped Function in -- required for scoped `on` notation
/--
theorem `iSupIndep_iff_pairwiseDisjoint` / 定理 `iSupIndep_iff_pairwiseDisjoint`

English:
theorem iSupIndep_iff_pairwiseDisjoint
  given: {f : ι -> α}
  statement: iSupIndep f ↔ Pairwise (Disjoint on f)
  proof: ⟨iSupIndep.pairwiseDisjoint, fun hs _ =>
    disjoint_iSup_iff.2 fun _ => disjoint_iSup_iff.2 fun hij => hs hij.symm⟩

中文:
定理 iSupIndep_iff_pairwiseDisjoint
  条件: {f : ι -> α}
  结论: iSupIndep f ↔ 两两 (Disjoint on f)
  证明: ⟨iSupIndep.pairwiseDisjoint, fun hs _ =>
    disjoint_iSup_iff.2 fun _ => disjoint_iSup_iff.2 fun hij => hs hij.symm⟩

Depends on / 依赖: disjoint_iSup_iff, hij.symm, iSupIndep, iSupIndep.pairwiseDisjoint, pairwiseDisjoint
-/
theorem iSupIndep_iff_pairwiseDisjoint {f : ι -> α} : iSupIndep f ↔ Pairwise (Disjoint on f) :=
  ⟨iSupIndep.pairwiseDisjoint, fun hs _ =>
    disjoint_iSup_iff.2 fun _ => disjoint_iSup_iff.2 fun hij => hs hij.symm⟩

end Frame
