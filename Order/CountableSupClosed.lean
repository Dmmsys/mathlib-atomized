/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.SupClosed

import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Bounds.Lattice

/-!
# Sets closed under countable join/meet

This file defines predicates for sets closed under countable supremum and dually for countable
infimum.

## Main declarations

* `CountableSupClosed`: Predicate for a set to be closed under countable supremum.
* `CountableInfClosed`: Predicate for a set to be closed under countable infimum.
* `countableSupClosure`: countable Sup-closure. Smallest countable sup-closed set containing
  a given set.
* `countableInfClosure`: countable Inf-closure. Smallest countable inf-closed set containing
  a given set.

## Implementation notes

The list of properties in this file is copied and adapted from the file about `SupClosed`.
We should keep these files in sync.

-/

public section

variable {ι : Sort*} {α β : Type*} {S : Set (Set α)} {s t : Set α} {a b : α}

section Set
open Set

/--
Definition of `CountableSupClosed` / `CountableSupClosed` 的定义

English:
structure CountableSupClosed
  parameters: [LE α] (s : Set α)
  axioms and operations (1):
    - isLUB_mem : forall t subseteq s, t.Nonempty -> t.Countable -> forall x, IsLUB t x -> x in s

中文:
结构 CountableSupClosed
  参数: [LE α] (s : Set α)
  公理与运算 (1 个):
    - isLUB_mem : 对任意 t subseteq s, t.Nonempty -> t.Countable -> 对任意 x, IsLUB t x -> x in s
-/
structure CountableSupClosed [LE α] (s : Set α) : Prop where
  isLUB_mem : forall t subseteq s, t.Nonempty -> t.Countable -> forall x, IsLUB t x -> x in s

/-- A set `s` is closed under countable infimum if for every nonempty countable subset of `s`, any
greatest lower bound of that subset is in `s`. -/
@[to_dual existing]
/--
Definition of `CountableInfClosed` / `CountableInfClosed` 的定义

English:
structure CountableInfClosed
  parameters: [LE α] (s : Set α)
  axioms and operations (1):
    - isGLB_mem : forall t subseteq s, t.Nonempty -> t.Countable -> forall x, IsGLB t x -> x in s

中文:
结构 CountableInfClosed
  参数: [LE α] (s : Set α)
  公理与运算 (1 个):
    - isGLB_mem : 对任意 t subseteq s, t.Nonempty -> t.Countable -> 对任意 x, IsGLB t x -> x in s
-/
structure CountableInfClosed [LE α] (s : Set α) : Prop where
  isGLB_mem : forall t subseteq s, t.Nonempty -> t.Countable -> forall x, IsGLB t x -> x in s

@[to_dual]
/--
lemma `CountableSupClosed.iSup_mem` / 引理 `CountableSupClosed.iSup_mem`

English:
lemma CountableSupClosed.iSup_mem
  statement: [CompleteLattice α] [Countable ι] [Nonempty ι]
  proof: by
  let i₀ := Nonempty.some (α := ι) inferInstance
  exact hs.isLUB_mem (range A) (by simp [range]; grind) ⟨A i₀, by simp⟩ (countable_range A) _
    isLUB_iSup

@[to_dual]

中文:
引理 CountableSupClosed.iSup_mem
  结论: [CompleteLattice α] [Countable ι] [Nonempty ι]
  证明: by
  let i₀ := Nonempty.some (α := ι) inferInstance
  exact hs.isLUB_mem (range A) (by simp [range]; grind) ⟨A i₀, by simp⟩ (countable_range A) _
    isLUB_iSup

@[to_dual]

Depends on / 依赖: Nonempty, Nonempty.some, countable_range, hs.isLUB_mem, isLUB_iSup, isLUB_mem
-/
lemma CountableSupClosed.iSup_mem [CompleteLattice α] [Countable ι] [Nonempty ι]
    (hs : CountableSupClosed s) {A : ι -> α} (hA : forall n, A n in s) :
    ⨆ n, A n in s := by
  let i₀ := Nonempty.some (α := ι) inferInstance
  exact hs.isLUB_mem (range A) (by simp [range]; grind) ⟨A i₀, by simp⟩ (countable_range A) _
    isLUB_iSup

@[to_dual]
/--
lemma `CountableSupClosed.of_iSup_mem` / 引理 `CountableSupClosed.of_iSup_mem`

English:
lemma CountableSupClosed.of_iSup_mem
  statement: [CompleteLattice α]
  proof: by
    obtain ⟨f, rfl⟩ := hAc.exists_eq_range hA_ne
    rw [(IsLUB.unique hx isLUB_iSup : x = ⨆ n]; rw [f n)]
    exact hs f (by grind)

@[to_dual]

中文:
引理 CountableSupClosed.of_iSup_mem
  结论: [CompleteLattice α]
  证明: by
    obtain ⟨f, rfl⟩ := hAc.exists_eq_range hA_ne
    rw [(IsLUB.unique hx isLUB_iSup : x = ⨆ n]; rw [f n)]
    exact hs f (by grind)

@[to_dual]

Depends on / 依赖: IsLUB.unique, exists_eq_range, hA_ne, hAc.exists_eq_range, isLUB_iSup, unique
-/
lemma CountableSupClosed.of_iSup_mem [CompleteLattice α]
    (hs : forall A : Nat -> α, (forall n, A n in s) -> ⨆ n, A n in s) :
    CountableSupClosed s where
  isLUB_mem A hAs hA_ne hAc x hx := by
    obtain ⟨f, rfl⟩ := hAc.exists_eq_range hA_ne
    rw [(IsLUB.unique hx isLUB_iSup : x = ⨆ n]; rw [f n)]
    exact hs f (by grind)

@[to_dual]
/--
lemma `CountableSupClosed.sSup_mem` / 引理 `CountableSupClosed.sSup_mem`

English:
lemma CountableSupClosed.sSup_mem
  statement: [CompleteLattice α] (hs : CountableSupClosed s)
  proof: by
  rw [sSup_eq_iSup']
  have : Countable A := hA_c
  have : Nonempty A := nonempty_coe_sort.mpr hA_ne
  exact hs.iSup_mem fun a => hA a a.2

@[to_dual]

中文:
引理 CountableSupClosed.sSup_mem
  结论: [CompleteLattice α] (hs : CountableSupClosed s)
  证明: by
  rw [sSup_eq_iSup']
  have : Countable A := hA_c
  have : Nonempty A := nonempty_coe_sort.mpr hA_ne
  exact hs.iSup_mem fun a => hA a a.2

@[to_dual]

Depends on / 依赖: Countable, Nonempty, hA_c, hA_ne, hs.iSup_mem, iSup_mem, nonempty_coe_sort, nonempty_coe_sort.mpr, sSup_eq_iSup
-/
lemma CountableSupClosed.sSup_mem [CompleteLattice α] (hs : CountableSupClosed s)
    {A : Set α} (hA_c : A.Countable) (hA_ne : A.Nonempty) (hA : forall a in A, a in s) :
    sSup A in s := by
  rw [sSup_eq_iSup']
  have : Countable A := hA_c
  have : Nonempty A := nonempty_coe_sort.mpr hA_ne
  exact hs.iSup_mem fun a => hA a a.2

@[to_dual]
/--
lemma `CountableSupClosed.supClosed` / 引理 `CountableSupClosed.supClosed`

English:
lemma CountableSupClosed.supClosed
  given: [SemilatticeSup α] (hs : CountableSupClosed s)
  proof: fun a ha b hb => hs.isLUB_mem {a, b} (by grind) (by simp) (by simp) _ isLUB_pair

@[to_dual (attr := simp)]

中文:
引理 CountableSupClosed.supClosed
  条件: [SemilatticeSup α] (hs : CountableSupClosed s)
  证明: fun a ha b hb => hs.isLUB_mem {a, b} (by grind) (by simp) (by simp) _ isLUB_pair

@[to_dual (attr := simp)]
-/
protected lemma CountableSupClosed.supClosed [SemilatticeSup α] (hs : CountableSupClosed s) :
    SupClosed s := fun a ha b hb => hs.isLUB_mem {a, b} (by grind) (by simp) (by simp) _ isLUB_pair

@[to_dual (attr := simp)]
/--
lemma `CountableSupClosed.singleton` / 引理 `CountableSupClosed.singleton`

English:
lemma CountableSupClosed.singleton
  given: [PartialOrder α] {x : α}
  proof: by
    have h_eq : s = {x} := by
      ext y
      simp_all only [subset_singleton_iff, mem_singleton_iff]
      refine ⟨hs_subset y, ?_⟩
      rintro rfl
      obtain ⟨z, hzs⟩ := hs_ne
      rwa [hs_subset z hzs] at hzs
    simp_all only [subset_refl, singleton_nonempty, countable_singleton, mem_si

中文:
引理 CountableSupClosed.singleton
  条件: [PartialOrder α] {x : α}
  证明: by
    have h_eq : s = {x} := by
      ext y
      simp_all only [subset_singleton_iff, mem_singleton_iff]
      refine ⟨hs_subset y, ?_⟩
      rintro rfl
      obtain ⟨z, hzs⟩ := hs_ne
      rwa [hs_subset z hzs] at hzs
    simp_all only [subset_refl, singleton_nonempty, countable_singleton, mem_si
-/
protected lemma CountableSupClosed.singleton [PartialOrder α] {x : α} :
    CountableSupClosed ({x} : Set α) where
  isLUB_mem s hs_subset hs_ne _ y hy := by
    have h_eq : s = {x} := by
      ext y
      simp_all only [subset_singleton_iff, mem_singleton_iff]
      refine ⟨hs_subset y, ?_⟩
      rintro rfl
      obtain ⟨z, hzs⟩ := hs_ne
      rwa [hs_subset z hzs] at hzs
    simp_all only [subset_refl, singleton_nonempty, countable_singleton, mem_singleton_iff]
    exact IsLUB.unique hy isLUB_singleton

@[to_dual (attr := simp)]
/--
lemma `CountableSupClosed.univ` / 引理 `CountableSupClosed.univ`

English:
lemma CountableSupClosed.univ
  given: [LE α]
  proof: by simp

@[to_dual (attr := simp)]

中文:
引理 CountableSupClosed.univ
  条件: [LE α]
  证明: by simp

@[to_dual (attr := simp)]
-/
protected lemma CountableSupClosed.univ [LE α] :
    CountableSupClosed (univ : Set α) where
  isLUB_mem _ _ _ _ _ _ := by simp

@[to_dual (attr := simp)]
/--
lemma `CountableSupClosed.empty` / 引理 `CountableSupClosed.empty`

English:
lemma CountableSupClosed.empty
  given: [LE α]
  proof: by simp_all

@[to_dual]

中文:
引理 CountableSupClosed.empty
  条件: [LE α]
  证明: by simp_all

@[to_dual]
-/
protected lemma CountableSupClosed.empty [LE α] :
    CountableSupClosed (∅ : Set α) where
  isLUB_mem _ _ _ _ _ _ := by simp_all

@[to_dual]
/--
lemma `CountableSupClosed.inter` / 引理 `CountableSupClosed.inter`

English:
lemma CountableSupClosed.inter
  statement: [LE α]
  proof: ⟨hs.isLUB_mem A (hAst.trans Set.inter_subset_left) hA_ne hAc x hx,
      ht.isLUB_mem A (hAst.trans Set.inter_subset_right) hA_ne hAc x hx⟩

@[to_dual]

中文:
引理 CountableSupClosed.inter
  结论: [LE α]
  证明: ⟨hs.isLUB_mem A (hAst.trans Set.inter_subset_left) hA_ne hAc x hx,
      ht.isLUB_mem A (hAst.trans Set.inter_subset_right) hA_ne hAc x hx⟩

@[to_dual]
-/
protected lemma CountableSupClosed.inter [LE α]
    (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s inter t) where
  isLUB_mem A hAst hA_ne hAc x hx :=
    ⟨hs.isLUB_mem A (hAst.trans Set.inter_subset_left) hA_ne hAc x hx,
      ht.isLUB_mem A (hAst.trans Set.inter_subset_right) hA_ne hAc x hx⟩

@[to_dual]
/--
lemma `CountableSupClosed.sInter` / 引理 `CountableSupClosed.sInter`

English:
lemma CountableSupClosed.sInter
  given: [LE α] (hS : forall s in S, CountableSupClosed s)
  proof: by
    simp only [subset_sInter_iff, mem_sInter] at hAS ⊢
    exact fun s hs => (hS s hs).isLUB_mem A (hAS s hs) hA_ne hAc x hx

@[to_dual]

中文:
引理 CountableSupClosed.sInter
  条件: [LE α] (hS : 对任意 s in S, CountableSupClosed s)
  证明: by
    simp only [subset_sInter_iff, mem_sInter] at hAS ⊢
    exact fun s hs => (hS s hs).isLUB_mem A (hAS s hs) hA_ne hAc x hx

@[to_dual]
-/
protected lemma CountableSupClosed.sInter [LE α] (hS : forall s in S, CountableSupClosed s) :
    CountableSupClosed (⋂₀ S) where
  isLUB_mem A hAS hA_ne hAc x hx := by
    simp only [subset_sInter_iff, mem_sInter] at hAS ⊢
    exact fun s hs => (hS s hs).isLUB_mem A (hAS s hs) hA_ne hAc x hx

@[to_dual]
/--
lemma `CountableSupClosed.iInter` / 引理 `CountableSupClosed.iInter`

English:
lemma CountableSupClosed.iInter
  statement: [LE α]
  proof: .sInter forall_mem_range.2 hf

@[to_dual]

中文:
引理 CountableSupClosed.iInter
  结论: [LE α]
  证明: .sInter forall_mem_range.2 hf

@[to_dual]
-/
protected lemma CountableSupClosed.iInter [LE α]
    {f : ι -> Set α} (hf : forall i, CountableSupClosed (f i)) :
    CountableSupClosed (⋂ i, f i) :=
.sInter forall_mem_range.2 hf

@[to_dual]
/--
lemma `CountableSupClosed.directedOn` / 引理 `CountableSupClosed.directedOn`

English:
lemma CountableSupClosed.directedOn
  given: [SemilatticeSup α] (hs : CountableSupClosed s)
  proof: hs.supClosed.directedOn

@[to_dual]

中文:
引理 CountableSupClosed.directedOn
  条件: [SemilatticeSup α] (hs : CountableSupClosed s)
  证明: hs.supClosed.directedOn

@[to_dual]
-/
protected lemma CountableSupClosed.directedOn [SemilatticeSup α] (hs : CountableSupClosed s) :
    DirectedOn (· <= ·) s := hs.supClosed.directedOn

@[to_dual]
/--
lemma `CountableSupClosed.prod` / 引理 `CountableSupClosed.prod`

English:
lemma CountableSupClosed.prod
  statement: [Preorder α] [Preorder β]
  proof: by
    intro (x, y) hxy
    rw [isLUB_prod] at hxy
    exact ⟨hs.isLUB_mem (Prod.fst '' A) (by grind) (by simpa) (hAc.image Prod.fst) _ hxy.1,
      ht.isLUB_mem (Prod.snd '' A) (by grind) (by simpa) (hAc.image Prod.snd) _ hxy.2⟩

中文:
引理 CountableSupClosed.prod
  结论: [Preorder α] [Preorder β]
  证明: by
    intro (x, y) hxy
    rw [isLUB_prod] at hxy
    exact ⟨hs.isLUB_mem (Prod.fst '' A) (by grind) (by simpa) (hAc.image Prod.fst) _ hxy.1,
      ht.isLUB_mem (Prod.snd '' A) (by grind) (by simpa) (hAc.image Prod.snd) _ hxy.2⟩
-/
protected lemma CountableSupClosed.prod [Preorder α] [Preorder β]
    {t : Set β} (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ×ˢ t) where
  isLUB_mem A hAst hA_ne hAc := by
    intro (x, y) hxy
    rw [isLUB_prod] at hxy
    exact ⟨hs.isLUB_mem (Prod.fst '' A) (by grind) (by simpa) (hAc.image Prod.fst) _ hxy.1,
      ht.isLUB_mem (Prod.snd '' A) (by grind) (by simpa) (hAc.image Prod.snd) _ hxy.2⟩

end Set

section Finset
variable {ι : Type*} {f : ι -> α} {t : Finset ι}

@[to_dual]
/--
lemma `CountableSupClosed.finsetSup'_mem` / 引理 `CountableSupClosed.finsetSup'_mem`

English:
lemma CountableSupClosed.finsetSup'_mem
  statement: [SemilatticeSup α]
  proof: hs.supClosed.finsetSup'_mem ht

@[to_dual]

中文:
引理 CountableSupClosed.finsetSup'_mem
  结论: [SemilatticeSup α]
  证明: hs.supClosed.finsetSup'_mem ht

@[to_dual]

Depends on / 依赖: _mem, finsetSup, hs.supClosed.finsetSup, supClosed
-/
lemma CountableSupClosed.finsetSup'_mem [SemilatticeSup α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (forall i in t, f i in s) -> t.sup' ht f in s :=
  hs.supClosed.finsetSup'_mem ht

@[to_dual]
/--
lemma `CountableSupClosed.finsetSup_mem` / 引理 `CountableSupClosed.finsetSup_mem`

English:
lemma CountableSupClosed.finsetSup_mem
  statement: [SemilatticeSup α] [OrderBot α]
  proof: Finset.sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

中文:
引理 CountableSupClosed.finsetSup_mem
  结论: [SemilatticeSup α] [OrderBot α]
  证明: Finset.sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

Depends on / 依赖: Finset, Finset.sup, _eq_sup, _mem, finsetSup, hs.finsetSup
-/
lemma CountableSupClosed.finsetSup_mem [SemilatticeSup α] [OrderBot α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (forall i in t, f i in s) -> t.sup f in s :=
  Finset.sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset

open OrderDual

/--
lemma `countableSupClosed_preimage_toDual` / 引理 `countableSupClosed_preimage_toDual`

English:
lemma countableSupClosed_preimage_toDual
  given: [LE α] {s : Set αᵒᵈ}
  proof: ⟨fun h => ⟨h.isLUB_mem⟩, fun h => ⟨h.isGLB_mem⟩⟩

中文:
引理 countableSupClosed_preimage_toDual
  条件: [LE α] {s : Set αᵒᵈ}
  证明: ⟨fun h => ⟨h.isLUB_mem⟩, fun h => ⟨h.isGLB_mem⟩⟩
-/
@[to_dual (attr := simp)] lemma countableSupClosed_preimage_toDual [LE α] {s : Set αᵒᵈ} :
    CountableSupClosed (toDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h => ⟨h.isLUB_mem⟩, fun h => ⟨h.isGLB_mem⟩⟩

/--
lemma `countableSupClosed_preimage_ofDual` / 引理 `countableSupClosed_preimage_ofDual`

English:
lemma countableSupClosed_preimage_ofDual
  given: [LE α] {s : Set α}
  proof: ⟨fun h => ⟨h.isLUB_mem⟩, fun h => ⟨h.isGLB_mem⟩⟩

@[to_dual] alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

中文:
引理 countableSupClosed_preimage_ofDual
  条件: [LE α] {s : Set α}
  证明: ⟨fun h => ⟨h.isLUB_mem⟩, fun h => ⟨h.isGLB_mem⟩⟩

@[to_dual] alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual
-/
@[to_dual (attr := simp)] lemma countableSupClosed_preimage_ofDual [LE α] {s : Set α} :
    CountableSupClosed (ofDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h => ⟨h.isLUB_mem⟩, fun h => ⟨h.isGLB_mem⟩⟩

@[to_dual] alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

/-! ### Closure -/

section Preorder

variable [Preorder α]

/-- Every set generates a set closed under countable supremum. -/
@[to_dual /-- Every set generates a set closed under countable infimum. -/]
/--
Definition of `countableSupClosure` / `countableSupClosure` 的定义

English:
definition countableSupClosure
  signature: : ClosureOperator (Set α)
  body: .ofPred
  (fun s => {a | exists (A : Set α) (_ : A subseteq s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a})
  CountableSupClosed
  (fun s x hxs => ⟨{x}, by simp; grind, by simp, by simp, by simp⟩)
  (fun s => by
    constructor
    intro A hA hA_ne hAc x hx
    choose B hB hB_ne hBc hB_lub using 

中文:
定义 countableSupClosure
  签名: : ClosureOperator (Set α)
  定义体: .ofPred
  (fun s => {a | exists (A : Set α) (_ : A subseteq s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a})
  CountableSupClosed
  (fun s x hxs => ⟨{x}, by simp; grind, by simp, by simp, by simp⟩)
  (fun s => by
    constructor
    intro A hA hA_ne hAc x hx
    choose B hB hB_ne hBc hB_lub using 

Depends on / 依赖: ofPred
-/
def countableSupClosure : ClosureOperator (Set α) := .ofPred
  (fun s => {a | exists (A : Set α) (_ : A subseteq s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a})
  CountableSupClosed
  (fun s x hxs => ⟨{x}, by simp; grind, by simp, by simp, by simp⟩)
  (fun s => by
    constructor
    intro A hA hA_ne hAc x hx
    choose B hB hB_ne hBc hB_lub using hA
    refine ⟨⋃ a : A, B a.2, by simp; grind, ?_, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hA_ne
      simp
      grind
    · have : Countable A := Set.countable_coe_iff.mpr hAc
      exact Set.countable_iUnion fun a => hBc a.2
    · have : Nonempty A := Set.nonempty_coe_sort.mpr hA_ne
      rw [← isLUB_iUnion_iff_of_isLUB (u := fun a : A => a.1) (fun a => hB_lub a.2)]
      simpa)
  (fun s t (hst : s subseteq t) ht a ⟨A, hAs, hA_ne, hA_c, hA_lub⟩ =>
    ht.isLUB_mem A (hAs.trans hst) hA_ne hA_c _ hA_lub)

/--
lemma `subset_countableSupClosure` / 引理 `subset_countableSupClosure`

English:
lemma subset_countableSupClosure
  proof: countableSupClosure.le_closure _

@[to_dual countableInfClosure_min]

中文:
引理 subset_countableSupClosure
  证明: countableSupClosure.le_closure _

@[to_dual countableInfClosure_min]
-/
@[to_dual (attr := simp)] lemma subset_countableSupClosure :
    s subseteq countableSupClosure s := countableSupClosure.le_closure _

@[to_dual countableInfClosure_min]
/--
lemma `countableSupClosure_min` / 引理 `countableSupClosure_min`

English:
lemma countableSupClosure_min
  given: (hst : s subseteq t) (ht : CountableSupClosed t)
  proof: countableSupClosure.closure_min hst ht

中文:
引理 countableSupClosure_min
  条件: (hst : s subseteq t) (ht : CountableSupClosed t)
  证明: countableSupClosure.closure_min hst ht

Depends on / 依赖: closure_min, countableSupClosure, countableSupClosure.closure_min
-/
lemma countableSupClosure_min (hst : s subseteq t) (ht : CountableSupClosed t) :
    countableSupClosure s subseteq t := countableSupClosure.closure_min hst ht

/--
lemma `countableSupClosed_countableSupClosure` / 引理 `countableSupClosed_countableSupClosure`

English:
lemma countableSupClosed_countableSupClosure
  proof: countableSupClosure.isClosed_closure _

@[to_dual (attr := gcongr)]

中文:
引理 countableSupClosed_countableSupClosure
  证明: countableSupClosure.isClosed_closure _

@[to_dual (attr := gcongr)]
-/
@[to_dual (attr := simp)] lemma countableSupClosed_countableSupClosure :
    CountableSupClosed (countableSupClosure s) := countableSupClosure.isClosed_closure _

@[to_dual (attr := gcongr)]
/--
lemma `countableSupClosure_mono` / 引理 `countableSupClosure_mono`

English:
lemma countableSupClosure_mono
  statement: Monotone (countableSupClosure : Set α -> Set α)
  proof: countableSupClosure.mono

中文:
引理 countableSupClosure_mono
  结论: Monotone (countableSupClosure : Set α -> Set α)
  证明: countableSupClosure.mono

Depends on / 依赖: countableSupClosure, countableSupClosure.mono
-/
lemma countableSupClosure_mono : Monotone (countableSupClosure : Set α -> Set α) :=
  countableSupClosure.mono

/--
lemma `countableSupClosure_eq_self` / 引理 `countableSupClosure_eq_self`

English:
lemma countableSupClosure_eq_self
  proof: countableSupClosure.isClosed_iff.symm

@[to_dual]
alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

@[to_dual]

中文:
引理 countableSupClosure_eq_self
  证明: countableSupClosure.isClosed_iff.symm

@[to_dual]
alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

@[to_dual]
-/
@[to_dual (attr := simp)] lemma countableSupClosure_eq_self :
    countableSupClosure s = s ↔ CountableSupClosed s := countableSupClosure.isClosed_iff.symm

@[to_dual]
alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

@[to_dual]
/--
lemma `countableSupClosure_idem` / 引理 `countableSupClosure_idem`

English:
lemma countableSupClosure_idem
  given: (s : Set α)
  proof: countableSupClosure.idempotent _

@[to_dual]

中文:
引理 countableSupClosure_idem
  条件: (s : Set α)
  证明: countableSupClosure.idempotent _

@[to_dual]

Depends on / 依赖: countableSupClosure, countableSupClosure.idempotent, idempotent
-/
lemma countableSupClosure_idem (s : Set α) :
    countableSupClosure (countableSupClosure s) = countableSupClosure s :=
  countableSupClosure.idempotent _

@[to_dual]
/--
lemma `countableSupClosure_eq_sInter` / 引理 `countableSupClosure_eq_sInter`

English:
lemma countableSupClosure_eq_sInter
  given: (s : Set α)
  proof: by
  have : CountableSupClosed (⋂₀ {t | s subseteq t ∧ CountableSupClosed t}) := by
    constructor
    simp only [Set.subset_sInter_iff, Set.mem_ofPred_eq, and_imp, Set.mem_sInter]
    intro t ht ht_ne ht_c x hx t' hst' ht'
    exact ht'.isLUB_mem t (ht t' hst' ht') ht_ne ht_c x hx
  refine le_anti

中文:
引理 countableSupClosure_eq_sInter
  条件: (s : Set α)
  证明: by
  have : CountableSupClosed (⋂₀ {t | s subseteq t ∧ CountableSupClosed t}) := by
    constructor
    simp only [Set.subset_sInter_iff, Set.mem_ofPred_eq, and_imp, Set.mem_sInter]
    intro t ht ht_ne ht_c x hx t' hst' ht'
    exact ht'.isLUB_mem t (ht t' hst' ht') ht_ne ht_c x hx
  refine le_anti

Depends on / 依赖: CountableSupClosed, Set.mem_ofPred_eq, Set.mem_sInter, Set.sInter_subset_of_mem, Set.subset_sInter_iff, and_imp, countableSupClosed_countableSupClosure, countableSupClosure_min, ht_c, ht_ne, isLUB_mem, le_antisymm, mem_ofPred_eq, mem_sInter, sInter_subset_of_mem, subset_countableSupClosure, subset_sInter_iff, subseteq
-/
lemma countableSupClosure_eq_sInter (s : Set α) :
    countableSupClosure s = ⋂₀ {t | s subseteq t ∧ CountableSupClosed t} := by
  have : CountableSupClosed (⋂₀ {t | s subseteq t ∧ CountableSupClosed t}) := by
    constructor
    simp only [Set.subset_sInter_iff, Set.mem_ofPred_eq, and_imp, Set.mem_sInter]
    intro t ht ht_ne ht_c x hx t' hst' ht'
    exact ht'.isLUB_mem t (ht t' hst' ht') ht_ne ht_c x hx
  refine le_antisymm (countableSupClosure_min (by grind) (by grind)) (Set.sInter_subset_of_mem ?_)
  exact ⟨subset_countableSupClosure, countableSupClosed_countableSupClosure⟩

@[to_dual]
/--
lemma `mem_countableSupClosure_iff` / 引理 `mem_countableSupClosure_iff`

English:
lemma mem_countableSupClosure_iff
  proof: by rfl

中文:
引理 mem_countableSupClosure_iff
  证明: by rfl
-/
lemma mem_countableSupClosure_iff :
    a in countableSupClosure s ↔
      exists (A : Set α) (_ : A subseteq s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a := by rfl

/--
lemma `countableSupClosure_univ` / 引理 `countableSupClosure_univ`

English:
lemma countableSupClosure_univ
  proof: by simp

中文:
引理 countableSupClosure_univ
  证明: by simp
-/
@[to_dual (attr := simp)] lemma countableSupClosure_univ :
    countableSupClosure (Set.univ : Set α) = Set.univ := by simp

/--
lemma `countableSupClosure_empty` / 引理 `countableSupClosure_empty`

English:
lemma countableSupClosure_empty
  proof: by simp

中文:
引理 countableSupClosure_empty
  证明: by simp
-/
@[to_dual (attr := simp)] lemma countableSupClosure_empty :
    countableSupClosure (∅ : Set α) = ∅ := by simp

/--
lemma `upperBounds_countableSupClosure` / 引理 `upperBounds_countableSupClosure`

English:
lemma upperBounds_countableSupClosure
  given: (s : Set α)
  proof: (upperBounds_mono_set subset_countableSupClosure).antisymm by
    intro a ha b hb
    rw [mem_countableSupClosure_iff] at hb
    obtain ⟨t, hts, ht_ne, ht_c, ht_lub⟩ := hb
    have hat : a in upperBounds t := fun x hx => ha (hts hx)
    exact (isLUB_le_iff ht_lub).mpr hat

中文:
引理 upperBounds_countableSupClosure
  条件: (s : Set α)
  证明: (upperBounds_mono_set subset_countableSupClosure).antisymm by
    intro a ha b hb
    rw [mem_countableSupClosure_iff] at hb
    obtain ⟨t, hts, ht_ne, ht_c, ht_lub⟩ := hb
    have hat : a in upperBounds t := fun x hx => ha (hts hx)
    exact (isLUB_le_iff ht_lub).mpr hat
-/
@[to_dual (attr := simp)] lemma upperBounds_countableSupClosure (s : Set α) :
    upperBounds (countableSupClosure s) = upperBounds s :=
(upperBounds_mono_set subset_countableSupClosure).antisymm by
    intro a ha b hb
    rw [mem_countableSupClosure_iff] at hb
    obtain ⟨t, hts, ht_ne, ht_c, ht_lub⟩ := hb
    have hat : a in upperBounds t := fun x hx => ha (hts hx)
    exact (isLUB_le_iff ht_lub).mpr hat

/--
lemma `isLUB_countableSupClosure` / 引理 `isLUB_countableSupClosure`

English:
lemma isLUB_countableSupClosure
  proof: by simp [IsLUB]

中文:
引理 isLUB_countableSupClosure
  证明: by simp [IsLUB]
-/
@[to_dual (attr := simp)] lemma isLUB_countableSupClosure :
    IsLUB (countableSupClosure s) a ↔ IsLUB s a := by simp [IsLUB]

/--
lemma `countableSupClosure_prod` / 引理 `countableSupClosure_prod`

English:
lemma countableSupClosure_prod
  statement: [Preorder β]
  proof: le_antisymm (countableSupClosure_min
(Set.prod_mono subset_countableSupClosure subset_countableSupClosure)
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_countableSupClosure_iff] at ha hb ⊢
      obtain 

中文:
引理 countableSupClosure_prod
  结论: [Preorder β]
  证明: le_antisymm (countableSupClosure_min
(Set.prod_mono subset_countableSupClosure subset_countableSupClosure)
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_countableSupClosure_iff] at ha hb ⊢
      obtain 
-/
@[to_dual (attr := simp)] lemma countableSupClosure_prod [Preorder β]
    (s : Set α) (t : Set β) :
    countableSupClosure (s ×ˢ t) = countableSupClosure s ×ˢ countableSupClosure t :=
  le_antisymm (countableSupClosure_min
(Set.prod_mono subset_countableSupClosure subset_countableSupClosure)
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_countableSupClosure_iff] at ha hb ⊢
      obtain ⟨u, hu, hu_ne, hu_c, hu_lub⟩ := ha
      obtain ⟨v, hv, hv_ne, hv_c, hv_lub⟩ := hb
      refine ⟨u ×ˢ v, by grind, by simp [hu_ne, hv_ne], hu_c.prod hv_c, ?_⟩
      exact IsLUB.prod hu_ne hv_ne hu_lub hv_lub

end Preorder

@[to_dual]
/--
lemma `mem_countableSupClosure_iff_iSup` / 引理 `mem_countableSupClosure_iff_iSup`

English:
lemma mem_countableSupClosure_iff_iSup
  given: [CompleteLattice α]
  proof: by
  suffices countableSupClosure s = {a | exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a} by simp [this]
  have h_csc : CountableSupClosed {a | exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a} := by
    refine .of_iSup_mem fun A hA => ?_
    choose B hB hB_eq using hA
    ref

中文:
引理 mem_countableSupClosure_iff_iSup
  条件: [CompleteLattice α]
  证明: by
  suffices countableSupClosure s = {a | exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a} by simp [this]
  have h_csc : CountableSupClosed {a | exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a} := by
    refine .of_iSup_mem fun A hA => ?_
    choose B hB hB_eq using hA
    ref

Depends on / 依赖: CountableSupClosed, Nat.unpair, countableSupClosure, countableSupClosure_min, hB_eq, h_csc, iSup_unpair, le_antisymm, of_iSup_mem, unpair
-/
lemma mem_countableSupClosure_iff_iSup [CompleteLattice α] :
    a in countableSupClosure s ↔ exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a := by
  suffices countableSupClosure s = {a | exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a} by simp [this]
  have h_csc : CountableSupClosed {a | exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a} := by
    refine .of_iSup_mem fun A hA => ?_
    choose B hB hB_eq using hA
    refine ⟨fun n => B (Nat.unpair n).1 (Nat.unpair n).2, fun _ => hB _ _, ?_⟩
    simp [iSup_unpair, ← hB_eq]
  refine le_antisymm (countableSupClosure_min ?_ h_csc) ?_
  · exact fun a ha => ⟨fun _ => a, by simp [ha]⟩
  · rintro _ ⟨u, hus, rfl⟩
    exact countableSupClosed_countableSupClosure.iSup_mem fun n => subset_countableSupClosure (hus n)

/--
lemma `supClosed_countableSupClosure` / 引理 `supClosed_countableSupClosure`

English:
lemma supClosed_countableSupClosure
  given: [SemilatticeSup α]
  proof: countableSupClosed_countableSupClosure.supClosed

中文:
引理 supClosed_countableSupClosure
  条件: [SemilatticeSup α]
  证明: countableSupClosed_countableSupClosure.supClosed
-/
@[to_dual (attr := simp)] lemma supClosed_countableSupClosure [SemilatticeSup α] :
    SupClosed (countableSupClosure s) :=
  countableSupClosed_countableSupClosure.supClosed

/--
lemma `countableSupClosure_singleton` / 引理 `countableSupClosure_singleton`

English:
lemma countableSupClosure_singleton
  given: [PartialOrder α] {x : α}
  proof: by simp

@[to_dual]

中文:
引理 countableSupClosure_singleton
  条件: [PartialOrder α] {x : α}
  证明: by simp

@[to_dual]
-/
@[to_dual (attr := simp)] lemma countableSupClosure_singleton [PartialOrder α] {x : α} :
    countableSupClosure {x} = {x} := by simp

@[to_dual]
/--
lemma `sup_mem_countableSupClosure` / 引理 `sup_mem_countableSupClosure`

English:
lemma sup_mem_countableSupClosure
  given: [SemilatticeSup α] (ha : a in s) (hb : b in s)
  proof: supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

@[to_dual]

中文:
引理 sup_mem_countableSupClosure
  条件: [SemilatticeSup α] (ha : a in s) (hb : b in s)
  证明: supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

@[to_dual]

Depends on / 依赖: subset_countableSupClosure, supClosed_countableSupClosure
-/
lemma sup_mem_countableSupClosure [SemilatticeSup α] (ha : a in s) (hb : b in s) :
    a ⊔ b in countableSupClosure s :=
  supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

@[to_dual]
/--
lemma `iSup_mem_countableSupClosure` / 引理 `iSup_mem_countableSupClosure`

English:
lemma iSup_mem_countableSupClosure
  statement: [CompleteLattice α] [Countable ι] [Nonempty ι] {A : ι -> α}
  proof: countableSupClosed_countableSupClosure.iSup_mem (fun n => subset_countableSupClosure (hA n))

@[to_dual]

中文:
引理 iSup_mem_countableSupClosure
  结论: [CompleteLattice α] [Countable ι] [Nonempty ι] {A : ι -> α}
  证明: countableSupClosed_countableSupClosure.iSup_mem (fun n => subset_countableSupClosure (hA n))

@[to_dual]

Depends on / 依赖: countableSupClosed_countableSupClosure, countableSupClosed_countableSupClosure.iSup_mem, iSup_mem, subset_countableSupClosure
-/
lemma iSup_mem_countableSupClosure [CompleteLattice α] [Countable ι] [Nonempty ι] {A : ι -> α}
    (hA : forall n, A n in s) :
    ⨆ n, A n in countableSupClosure s :=
  countableSupClosed_countableSupClosure.iSup_mem (fun n => subset_countableSupClosure (hA n))

@[to_dual]
/--
lemma `finsetSup'_mem_countableSupClosure` / 引理 `finsetSup'_mem_countableSupClosure`

English:
lemma finsetSup'_mem_countableSupClosure
  statement: {ι : Type*} [SemilatticeSup α]
  proof: supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi => subset_countableSupClosure hf _ hi

中文:
引理 finsetSup'_mem_countableSupClosure
  结论: {ι : 类型} [SemilatticeSup α]
  证明: supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi => subset_countableSupClosure hf _ hi

Depends on / 依赖: _mem, finsetSup, subset_countableSupClosure, supClosed_countableSupClosure, supClosed_countableSupClosure.finsetSup
-/
lemma finsetSup'_mem_countableSupClosure {ι : Type*} [SemilatticeSup α]
    {t : Finset ι} (ht : t.Nonempty) {f : ι -> α}
    (hf : forall i in t, f i in s) : t.sup' ht f in countableSupClosure s :=
supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi => subset_countableSupClosure hf _ hi

/-- If a set is closed under binary suprema, then its countable infimum closure is also closed under
binary suprema. -/
@[to_dual
/-- If a set is closed under binary infima, then its countable supremum closure is also closed under
binary infima. -/]
/--
lemma `SupClosed.countableInfClosure` / 引理 `SupClosed.countableInfClosure`

English:
lemma SupClosed.countableInfClosure
  given: [Order.Coframe α] (hs : SupClosed s)
  proof: by
  rintro a ha b hb
  rw [mem_countableInfClosure_iff_iInf] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iInf_sup_iInf]
  refine ⟨fun n => t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n => ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpai

中文:
引理 SupClosed.countableInfClosure
  条件: [Order.Coframe α] (hs : SupClosed s)
  证明: by
  rintro a ha b hb
  rw [mem_countableInfClosure_iff_iInf] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iInf_sup_iInf]
  refine ⟨fun n => t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n => ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpai
-/
protected lemma SupClosed.countableInfClosure [Order.Coframe α] (hs : SupClosed s) :
    SupClosed (countableInfClosure s) := by
  rintro a ha b hb
  rw [mem_countableInfClosure_iff_iInf] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iInf_sup_iInf]
  refine ⟨fun n => t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n => ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iInf_unpair (f := (fun n m => t n ⊔ u m)), iInf_prod']
