/-
Copyright (c) 2023 Yaël Dillies, Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
module

public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Closure
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Sets closed under join/meet

This file defines predicates for sets closed under `⊔` and shows that each set in a join-semilattice
generates a join-closed set and that a semilattice where every directed set has a least upper bound
is automatically complete. All dually for `⊓`.

## Main declarations

* `SupClosed`: Predicate for a set to be closed under join (`a ∈ s` and `b ∈ s` imply `a ⊔ b ∈ s`).
* `InfClosed`: Predicate for a set to be closed under meet (`a ∈ s` and `b ∈ s` imply `a ⊓ b ∈ s`).
* `IsSublattice`: Predicate for a set to be closed under meet and join.
* `supClosure`: Sup-closure. Smallest sup-closed set containing a given set.
* `infClosure`: Inf-closure. Smallest inf-closed set containing a given set.
* `latticeClosure`: Smallest sublattice containing a given set.
* `SemilatticeSup.toCompleteSemilatticeSup`: A join-semilattice where every sup-closed set has a
  least upper bound is automatically complete.
* `SemilatticeInf.toCompleteSemilatticeInf`: A meet-semilattice where every inf-closed set has a
  greatest lower bound is automatically complete.
-/

@[expose] public section

variable {ι : Sort*} {F α β : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β]

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι -> Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
@[to_dual /-- A set `s` is *inf-closed* if `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/]
/--
Definition of `SupClosed` / `SupClosed` 的定义

English:
definition SupClosed
  signature: (s : Set α)
  body: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> a ⊔ b in s

中文:
定义 SupClosed
  签名: (s : 集合 α)
  定义体: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> a ⊔ b in s
-/
def SupClosed (s : Set α) : Prop := forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> a ⊔ b in s

/--
lemma `supClosed_empty` / 引理 `supClosed_empty`

English:
lemma supClosed_empty
  statement: SupClosed (∅ : Set α)
  proof: by simp [SupClosed]

中文:
引理 supClosed_empty
  结论: SupClosed (∅ : 集合 α)
  证明: by simp [SupClosed]
-/
@[to_dual (attr := simp)] lemma supClosed_empty : SupClosed (∅ : Set α) := by simp [SupClosed]
/--
lemma `supClosed_singleton` / 引理 `supClosed_singleton`

English:
lemma supClosed_singleton
  statement: SupClosed ({a} : Set α)
  proof: by simp [SupClosed]

中文:
引理 supClosed_singleton
  结论: SupClosed ({a} : 集合 α)
  证明: by simp [SupClosed]
-/
@[to_dual (attr := simp)] lemma supClosed_singleton : SupClosed ({a} : Set α) := by simp [SupClosed]

/--
lemma `supClosed_univ` / 引理 `supClosed_univ`

English:
lemma supClosed_univ
  statement: SupClosed (univ : Set α)
  proof: by simp [SupClosed]

@[to_dual]

中文:
引理 supClosed_univ
  结论: SupClosed (univ : 集合 α)
  证明: by simp [SupClosed]

@[to_dual]
-/
@[to_dual (attr := simp)] lemma supClosed_univ : SupClosed (univ : Set α) := by simp [SupClosed]

@[to_dual]
/--
lemma `SupClosed.inter` / 引理 `SupClosed.inter`

English:
lemma SupClosed.inter
  given: (hs : SupClosed s) (ht : SupClosed t)
  statement: SupClosed (s inter t)
  proof: fun _a ha _b hb => ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]

中文:
引理 SupClosed.inter
  条件: (hs : SupClosed s) (ht : SupClosed t)
  结论: SupClosed (s inter t)
  证明: fun _a ha _b hb => ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]
-/
lemma SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s inter t) :=
  fun _a ha _b hb => ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]
/--
lemma `supClosed_sInter` / 引理 `supClosed_sInter`

English:
lemma supClosed_sInter
  given: (hS : forall s in S, SupClosed s)
  statement: SupClosed (⋂₀ S)
  proof: fun _a ha _b hb _s hs => hS _ hs (ha _ hs) (hb _ hs)

@[to_dual]

中文:
引理 supClosed_s整数er
  条件: (hS : 对任意 s in S, SupClosed s)
  结论: SupClosed (⋂₀ S)
  证明: fun _a ha _b hb _s hs => hS _ hs (ha _ hs) (hb _ hs)

@[to_dual]
-/
lemma supClosed_sInter (hS : forall s in S, SupClosed s) : SupClosed (⋂₀ S) :=
  fun _a ha _b hb _s hs => hS _ hs (ha _ hs) (hb _ hs)

@[to_dual]
/--
lemma `supClosed_iInter` / 引理 `supClosed_iInter`

English:
lemma supClosed_iInter
  given: (hf : forall i, SupClosed (f i))
  statement: SupClosed (⋂ i, f i)
  proof: supClosed_sInter forall_mem_range.2 hf

@[to_dual InfClosed.codirectedOn]

中文:
引理 supClosed_i整数er
  条件: (hf : 对任意 i, SupClosed (f i))
  结论: SupClosed (⋂ i, f i)
  证明: supClosed_sInter forall_mem_range.2 hf

@[to_dual InfClosed.codirectedOn]

Depends on / 依赖: forall_mem_range, supClosed_sInter
-/
lemma supClosed_iInter (hf : forall i, SupClosed (f i)) : SupClosed (⋂ i, f i) :=
supClosed_sInter forall_mem_range.2 hf

@[to_dual InfClosed.codirectedOn]
/--
lemma `SupClosed.directedOn` / 引理 `SupClosed.directedOn`

English:
lemma SupClosed.directedOn
  given: (hs : SupClosed s)
  statement: DirectedOn (· <= ·) s
  proof: fun _a ha _b hb => ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

@[to_dual]

中文:
引理 SupClosed.directedOn
  条件: (hs : SupClosed s)
  结论: DirectedOn (· <= ·) s
  证明: fun _a ha _b hb => ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

@[to_dual]

Depends on / 依赖: le_sup_left, le_sup_right
-/
lemma SupClosed.directedOn (hs : SupClosed s) : DirectedOn (· <= ·) s :=
  fun _a ha _b hb => ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

@[to_dual]
/--
lemma `IsUpperSet.supClosed` / 引理 `IsUpperSet.supClosed`

English:
lemma IsUpperSet.supClosed
  given: (hs : IsUpperSet s)
  statement: SupClosed s
  proof: fun _a _ _b => hs le_sup_right

@[to_dual]

中文:
引理 是上集.supClosed
  条件: (hs : 是上集 s)
  结论: SupClosed s
  证明: fun _a _ _b => hs le_sup_right

@[to_dual]

Depends on / 依赖: le_sup_right
-/
lemma IsUpperSet.supClosed (hs : IsUpperSet s) : SupClosed s := fun _a _ _b => hs le_sup_right

@[to_dual]
/--
lemma `SupClosed.preimage` / 引理 `SupClosed.preimage`

English:
lemma SupClosed.preimage
  given: [FunLike F β α] [SupHomClass F β α] (hs : SupClosed s) (f : F)
  proof: fun a ha b hb => by simpa [map_sup] using hs ha hb

@[to_dual]

中文:
引理 SupClosed.原像
  条件: [函数状 F β α] [并态射类 F β α] (hs : SupClosed s) (f : F)
  证明: fun a ha b hb => by simpa [map_sup] using hs ha hb

@[to_dual]

Depends on / 依赖: map_sup
-/
lemma SupClosed.preimage [FunLike F β α] [SupHomClass F β α] (hs : SupClosed s) (f : F) :
    SupClosed (f ⁻¹' s) :=
  fun a ha b hb => by simpa [map_sup] using hs ha hb

@[to_dual]
/--
lemma `SupClosed.image` / 引理 `SupClosed.image`

English:
lemma SupClosed.image
  given: [FunLike F α β] [SupHomClass F α β] (hs : SupClosed s) (f : F)
  proof: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_sup]
exact Set.mem_image_of_mem _ hs ha hb

@[to_dual]

中文:
引理 SupClosed.像
  条件: [函数状 F α β] [并态射类 F α β] (hs : SupClosed s) (f : F)
  证明: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_sup]
exact Set.mem_image_of_mem _ hs ha hb

@[to_dual]

Depends on / 依赖: Set.mem_image_of_mem, map_sup, mem_image_of_mem
-/
lemma SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs : SupClosed s) (f : F) :
    SupClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_sup]
exact Set.mem_image_of_mem _ hs ha hb

@[to_dual]
/--
lemma `supClosed_range` / 引理 `supClosed_range`

English:
lemma supClosed_range
  given: [FunLike F α β] [SupHomClass F α β] (f : F)
  statement: SupClosed (Set.range f)
  proof: by
  simpa using supClosed_univ.image f

@[to_dual]

中文:
引理 supClosed_range
  条件: [函数状 F α β] [并态射类 F α β] (f : F)
  结论: SupClosed (集合.range f)
  证明: by
  simpa using supClosed_univ.image f

@[to_dual]

Depends on / 依赖: supClosed_univ, supClosed_univ.image
-/
lemma supClosed_range [FunLike F α β] [SupHomClass F α β] (f : F) : SupClosed (Set.range f) := by
  simpa using supClosed_univ.image f

@[to_dual]
/--
lemma `SupClosed.prod` / 引理 `SupClosed.prod`

English:
lemma SupClosed.prod
  given: {t : Set β} (hs : SupClosed s) (ht : SupClosed t)
  statement: SupClosed (s ×ˢ t)
  proof: fun _a ha _b hb => ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]

中文:
引理 SupClosed.乘积
  条件: {t : 集合 β} (hs : SupClosed s) (ht : SupClosed t)
  结论: SupClosed (s ×ˢ t)
  证明: fun _a ha _b hb => ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]
-/
lemma SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ×ˢ t) :=
  fun _a ha _b hb => ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]
/--
lemma `supClosed_pi` / 引理 `supClosed_pi`

English:
lemma supClosed_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, SemilatticeSup (α i)] {s : Set ι}
  proof: fun _a ha _b hb _i hi => ht _ hi (ha _ hi) (hb _ hi)

@[to_dual]

中文:
引理 supClosed_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, SemilatticeSup (α i)] {s : 集合 ι}
  证明: fun _a ha _b hb _i hi => ht _ hi (ha _ hi) (hb _ hi)

@[to_dual]
-/
lemma supClosed_pi {ι : Type*} {α : ι -> Type*} [forall i, SemilatticeSup (α i)] {s : Set ι}
    {t : forall i, Set (α i)} (ht : forall i in s, SupClosed (t i)) : SupClosed (s.pi t) :=
  fun _a ha _b hb _i hi => ht _ hi (ha _ hi) (hb _ hi)

@[to_dual]
/--
lemma `SupClosed.insert_upperBounds` / 引理 `SupClosed.insert_upperBounds`

English:
lemma SupClosed.insert_upperBounds
  given: {s : Set α} {a : α} (hs : SupClosed s) (ha : a in upperBounds s)
  proof: by
  rw [SupClosed]
  aesop

@[to_dual]

中文:
引理 SupClosed.insert_upperBounds
  条件: {s : 集合 α} {a : α} (hs : SupClosed s) (ha : a in upperBounds s)
  证明: by
  rw [SupClosed]
  aesop

@[to_dual]

Depends on / 依赖: SupClosed
-/
lemma SupClosed.insert_upperBounds {s : Set α} {a : α} (hs : SupClosed s) (ha : a in upperBounds s) :
    SupClosed (insert a s) := by
  rw [SupClosed]
  aesop

@[to_dual]
/--
lemma `SupClosed.insert_lowerBounds` / 引理 `SupClosed.insert_lowerBounds`

English:
lemma SupClosed.insert_lowerBounds
  given: {s : Set α} {a : α} (h : SupClosed s) (ha : a in lowerBounds s)
  proof: by
  rw [SupClosed]
  have ha' : forall b in s, a <= b := fun _ a => ha a
  aesop

中文:
引理 SupClosed.insert_lowerBounds
  条件: {s : 集合 α} {a : α} (h : SupClosed s) (ha : a in lowerBounds s)
  证明: by
  rw [SupClosed]
  have ha' : forall b in s, a <= b := fun _ a => ha a
  aesop

Depends on / 依赖: SupClosed
-/
lemma SupClosed.insert_lowerBounds {s : Set α} {a : α} (h : SupClosed s) (ha : a in lowerBounds s) :
    SupClosed (insert a s) := by
  rw [SupClosed]
  have ha' : forall b in s, a <= b := fun _ a => ha a
  aesop

end Set

section Finset
variable {ι : Type*} {f : ι -> α} {s : Set α} {t : Finset ι} {a : α}
open Finset

@[to_dual]
/--
lemma `SupClosed.finsetSup'_mem` / 引理 `SupClosed.finsetSup'_mem`

English:
lemma SupClosed.finsetSup'_mem
  given: (hs : SupClosed s) (ht : t.Nonempty)
  proof: sup'_induction _ _ hs

@[to_dual]

中文:
引理 SupClosed.finsetSup'_mem
  条件: (hs : SupClosed s) (ht : t.非空)
  证明: sup'_induction _ _ hs

@[to_dual]

Depends on / 依赖: _induction
-/
lemma SupClosed.finsetSup'_mem (hs : SupClosed s) (ht : t.Nonempty) :
    (forall i in t, f i in s) -> t.sup' ht f in s :=
  sup'_induction _ _ hs

@[to_dual]
/--
lemma `SupClosed.finsetSup_mem` / 引理 `SupClosed.finsetSup_mem`

English:
lemma SupClosed.finsetSup_mem
  given: [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty)
  proof: sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

中文:
引理 SupClosed.finsetSup_mem
  条件: [有底序 α] (hs : SupClosed s) (ht : t.非空)
  证明: sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

Depends on / 依赖: _eq_sup, _mem, finsetSup, hs.finsetSup
-/
lemma SupClosed.finsetSup_mem [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty) :
    (forall i in t, f i in s) -> t.sup f in s :=
  sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset
end SemilatticeSup

open Finset OrderDual

section Lattice
variable {ι : Sort*} [Lattice α] [Lattice β] {S : Set (Set α)} {f : ι -> Set α} {s t : Set α} {a : α}

open Set

/--
Definition of `IsSublattice` / `IsSublattice` 的定义

English:
structure IsSublattice
  parameters: (s : Set α)
  axioms and operations (2):
    - supClosed : SupClosed s
    - infClosed : InfClosed s

中文:
结构 是子格
  参数: (s : 集合 α)
  公理与运算 (2 个):
    - supClosed : SupClosed s
    - infClosed : InfClosed s

Depends on / 依赖: IsSublattice, IsSublattice.mk, infClosed, supClosed
-/
structure IsSublattice (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

attribute [to_dual existing] IsSublattice.infClosed
attribute [to_dual self (reorder := supClosed infClosed)] IsSublattice.mk

/--
lemma `isSublattice_empty` / 引理 `isSublattice_empty`

English:
lemma isSublattice_empty
  statement: IsSublattice (∅ : Set α)
  proof: ⟨supClosed_empty, infClosed_empty⟩

中文:
引理 isSublattice_empty
  结论: 是子格 (∅ : 集合 α)
  证明: ⟨supClosed_empty, infClosed_empty⟩
-/
@[simp] lemma isSublattice_empty : IsSublattice (∅ : Set α) := ⟨supClosed_empty, infClosed_empty⟩
/--
lemma `isSublattice_singleton` / 引理 `isSublattice_singleton`

English:
lemma isSublattice_singleton
  statement: IsSublattice ({a} : Set α)
  proof: ⟨supClosed_singleton, infClosed_singleton⟩

中文:
引理 isSublattice_singleton
  结论: 是子格 ({a} : 集合 α)
  证明: ⟨supClosed_singleton, infClosed_singleton⟩
-/
@[simp] lemma isSublattice_singleton : IsSublattice ({a} : Set α) :=
  ⟨supClosed_singleton, infClosed_singleton⟩

/--
lemma `isSublattice_univ` / 引理 `isSublattice_univ`

English:
lemma isSublattice_univ
  statement: IsSublattice (Set.univ : Set α)
  proof: ⟨supClosed_univ, infClosed_univ⟩

中文:
引理 isSublattice_univ
  结论: 是子格 (集合.univ : 集合 α)
  证明: ⟨supClosed_univ, infClosed_univ⟩
-/
@[simp] lemma isSublattice_univ : IsSublattice (Set.univ : Set α) :=
  ⟨supClosed_univ, infClosed_univ⟩

/--
lemma `IsSublattice.inter` / 引理 `IsSublattice.inter`

English:
lemma IsSublattice.inter
  given: (hs : IsSublattice s) (ht : IsSublattice t)
  statement: IsSublattice (s inter t)
  proof: ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

中文:
引理 是子格.inter
  条件: (hs : 是子格 s) (ht : 是子格 t)
  结论: 是子格 (s inter t)
  证明: ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
-/
lemma IsSublattice.inter (hs : IsSublattice s) (ht : IsSublattice t) : IsSublattice (s inter t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

/--
lemma `isSublattice_sInter` / 引理 `isSublattice_sInter`

English:
lemma isSublattice_sInter
  given: (hS : forall s in S, IsSublattice s)
  statement: IsSublattice (⋂₀ S)
  proof: ⟨supClosed_sInter fun _s hs => (hS _ hs).1, infClosed_sInter fun _s hs => (hS _ hs).2⟩

中文:
引理 isSublattice_s整数er
  条件: (hS : 对任意 s in S, 是子格 s)
  结论: 是子格 (⋂₀ S)
  证明: ⟨supClosed_sInter fun _s hs => (hS _ hs).1, infClosed_sInter fun _s hs => (hS _ hs).2⟩

Depends on / 依赖: infClosed_sInter, supClosed_sInter
-/
lemma isSublattice_sInter (hS : forall s in S, IsSublattice s) : IsSublattice (⋂₀ S) :=
  ⟨supClosed_sInter fun _s hs => (hS _ hs).1, infClosed_sInter fun _s hs => (hS _ hs).2⟩

/--
lemma `isSublattice_iInter` / 引理 `isSublattice_iInter`

English:
lemma isSublattice_iInter
  given: (hf : forall i, IsSublattice (f i))
  statement: IsSublattice (⋂ i, f i)
  proof: ⟨supClosed_iInter fun _i => (hf _).1, infClosed_iInter fun _i => (hf _).2⟩

中文:
引理 isSublattice_i整数er
  条件: (hf : 对任意 i, 是子格 (f i))
  结论: 是子格 (⋂ i, f i)
  证明: ⟨supClosed_iInter fun _i => (hf _).1, infClosed_iInter fun _i => (hf _).2⟩

Depends on / 依赖: infClosed_iInter, supClosed_iInter
-/
lemma isSublattice_iInter (hf : forall i, IsSublattice (f i)) : IsSublattice (⋂ i, f i) :=
  ⟨supClosed_iInter fun _i => (hf _).1, infClosed_iInter fun _i => (hf _).2⟩

/--
lemma `IsSublattice.preimage` / 引理 `IsSublattice.preimage`

English:
lemma IsSublattice.preimage
  statement: [FunLike F β α] [LatticeHomClass F β α]
  proof: ⟨hs.1.preimage _, hs.2.preimage _⟩

中文:
引理 是子格.原像
  结论: [函数状 F β α] [格态射类 F β α]
  证明: ⟨hs.1.preimage _, hs.2.preimage _⟩

Depends on / 依赖: preimage
-/
lemma IsSublattice.preimage [FunLike F β α] [LatticeHomClass F β α]
    (hs : IsSublattice s) (f : F) :
    IsSublattice (f ⁻¹' s) := ⟨hs.1.preimage _, hs.2.preimage _⟩

/--
lemma `IsSublattice.image` / 引理 `IsSublattice.image`

English:
lemma IsSublattice.image
  given: [FunLike F α β] [LatticeHomClass F α β] (hs : IsSublattice s) (f : F)
  proof: ⟨hs.1.image _, hs.2.image _⟩

中文:
引理 是子格.像
  条件: [函数状 F α β] [格态射类 F α β] (hs : 是子格 s) (f : F)
  证明: ⟨hs.1.image _, hs.2.image _⟩
-/
lemma IsSublattice.image [FunLike F α β] [LatticeHomClass F α β] (hs : IsSublattice s) (f : F) :
    IsSublattice (f '' s) := ⟨hs.1.image _, hs.2.image _⟩

/--
lemma `IsSublattice_range` / 引理 `IsSublattice_range`

English:
lemma IsSublattice_range
  given: [FunLike F α β] [LatticeHomClass F α β] (f : F)
  proof: ⟨supClosed_range _, infClosed_range _⟩

中文:
引理 IsSublattice_range
  条件: [函数状 F α β] [格态射类 F α β] (f : F)
  证明: ⟨supClosed_range _, infClosed_range _⟩

Depends on / 依赖: infClosed_range, supClosed_range
-/
lemma IsSublattice_range [FunLike F α β] [LatticeHomClass F α β] (f : F) :
    IsSublattice (Set.range f) :=
  ⟨supClosed_range _, infClosed_range _⟩

/--
lemma `IsSublattice.prod` / 引理 `IsSublattice.prod`

English:
lemma IsSublattice.prod
  given: {t : Set β} (hs : IsSublattice s) (ht : IsSublattice t)
  proof: ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

中文:
引理 是子格.乘积
  条件: {t : 集合 β} (hs : 是子格 s) (ht : 是子格 t)
  证明: ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
-/
lemma IsSublattice.prod {t : Set β} (hs : IsSublattice s) (ht : IsSublattice t) :
    IsSublattice (s ×ˢ t) := ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

/--
lemma `isSublattice_pi` / 引理 `isSublattice_pi`

English:
lemma isSublattice_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, Lattice (α i)] {s : Set ι}
  proof: ⟨supClosed_pi fun _i hi => (ht _ hi).1, infClosed_pi fun _i hi => (ht _ hi).2⟩

中文:
引理 isSublattice_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, 格 (α i)] {s : 集合 ι}
  证明: ⟨supClosed_pi fun _i hi => (ht _ hi).1, infClosed_pi fun _i hi => (ht _ hi).2⟩

Depends on / 依赖: infClosed_pi, supClosed_pi
-/
lemma isSublattice_pi {ι : Type*} {α : ι -> Type*} [forall i, Lattice (α i)] {s : Set ι}
    {t : forall i, Set (α i)} (ht : forall i in s, IsSublattice (t i)) : IsSublattice (s.pi t) :=
  ⟨supClosed_pi fun _i hi => (ht _ hi).1, infClosed_pi fun _i hi => (ht _ hi).2⟩

/--
lemma `supClosed_preimage_toDual` / 引理 `supClosed_preimage_toDual`

English:
lemma supClosed_preimage_toDual
  given: {s : Set αᵒᵈ}
  proof: Iff.rfl

中文:
引理 supClosed_preimage_toDual
  条件: {s : 集合 αᵒᵈ}
  证明: Iff.rfl
-/
@[to_dual (attr := simp)] lemma supClosed_preimage_toDual {s : Set αᵒᵈ} :
    SupClosed (toDual ⁻¹' s) ↔ InfClosed s := Iff.rfl

/--
lemma `supClosed_preimage_ofDual` / 引理 `supClosed_preimage_ofDual`

English:
lemma supClosed_preimage_ofDual
  given: {s : Set α}
  proof: Iff.rfl

中文:
引理 supClosed_preimage_ofDual
  条件: {s : 集合 α}
  证明: Iff.rfl
-/
@[to_dual (attr := simp)] lemma supClosed_preimage_ofDual {s : Set α} :
    SupClosed (ofDual ⁻¹' s) ↔ InfClosed s := Iff.rfl

/--
lemma `isSublattice_preimage_toDual` / 引理 `isSublattice_preimage_toDual`

English:
lemma isSublattice_preimage_toDual
  given: {s : Set αᵒᵈ}
  proof: ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

中文:
引理 isSublattice_preimage_toDual
  条件: {s : 集合 αᵒᵈ}
  证明: ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
-/
@[simp] lemma isSublattice_preimage_toDual {s : Set αᵒᵈ} :
    IsSublattice (toDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/--
lemma `isSublattice_preimage_ofDual` / 引理 `isSublattice_preimage_ofDual`

English:
lemma isSublattice_preimage_ofDual
  proof: ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[to_dual] alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, IsSublattice.dual⟩ := isSublattice_preimage_ofDual
alias ⟨_, IsSublattice.of_dual⟩ := isSublattice_preimage_toDual

中文:
引理 isSublattice_preimage_ofDual
  证明: ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[to_dual] alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, IsSublattice.dual⟩ := isSublattice_preimage_ofDual
alias ⟨_, IsSublattice.of_dual⟩ := isSublattice_preimage_toDual
-/
@[simp] lemma isSublattice_preimage_ofDual :
    IsSublattice (ofDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[to_dual] alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, IsSublattice.dual⟩ := isSublattice_preimage_ofDual
alias ⟨_, IsSublattice.of_dual⟩ := isSublattice_preimage_toDual

end Lattice

section LinearOrder
variable [LinearOrder α]

/--
lemma `LinearOrder.supClosed` / 引理 `LinearOrder.supClosed`

English:
lemma LinearOrder.supClosed
  given: (s : Set α)
  statement: SupClosed s
  proof: fun a ha b hb => by cases le_total a b <;> simp [*]

中文:
引理 线性序.supClosed
  条件: (s : 集合 α)
  结论: SupClosed s
  证明: fun a ha b hb => by cases le_total a b <;> simp [*]
-/
@[to_dual (attr := simp)] protected lemma LinearOrder.supClosed (s : Set α) : SupClosed s :=
  fun a ha b hb => by cases le_total a b <;> simp [*]

/--
lemma `LinearOrder.isSublattice` / 引理 `LinearOrder.isSublattice`

English:
lemma LinearOrder.isSublattice
  given: (s : Set α)
  statement: IsSublattice s
  proof: ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩

中文:
引理 线性序.isSublattice
  条件: (s : 集合 α)
  结论: 是子格 s
  证明: ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩
-/
@[simp] protected lemma LinearOrder.isSublattice (s : Set α) : IsSublattice s :=
  ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩

end LinearOrder

/-! ## Closure -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[to_dual (attr := simps! isClosed)
/-- Every set in a meet-semilattice generates a set closed under meet. -/]
/--
Definition of `supClosure` / `supClosure` 的定义

English:
definition supClosure
  signature: : ClosureOperator (Set α)
  body: .ofPred
  (fun s => {a | exists (t : Finset α) (ht : t.Nonempty), ↑t subseteq s ∧ t.sup' ht id = a})
  SupClosed
  (fun s a ha => ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, sup'_union h

中文:
定义 supClosure
  签名: : 闭包算子 (集合 α)
  定义体: .ofPred
  (fun s => {a | exists (t : Finset α) (ht : t.Nonempty), ↑t subseteq s ∧ t.sup' ht id = a})
  SupClosed
  (fun s a ha => ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, sup'_union h

Depends on / 依赖: ofPred
-/
def supClosure : ClosureOperator (Set α) := .ofPred
  (fun s => {a | exists (t : Finset α) (ht : t.Nonempty), ↑t subseteq s ∧ t.sup' ht id = a})
  SupClosed
  (fun s a ha => ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, sup'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetSup'_mem ht fun i hi => hs <| hts hi)

@[to_dual (attr := simp)]
/--
lemma `subset_supClosure` / 引理 `subset_supClosure`

English:
lemma subset_supClosure
  given: {s : Set α}
  statement: s subseteq supClosure s
  proof: supClosure.le_closure _

@[to_dual (attr := simp)]

中文:
引理 subset_supClosure
  条件: {s : 集合 α}
  结论: s subseteq supClosure s
  证明: supClosure.le_closure _

@[to_dual (attr := simp)]

Depends on / 依赖: le_closure, supClosure, supClosure.le_closure
-/
lemma subset_supClosure {s : Set α} : s subseteq supClosure s := supClosure.le_closure _

@[to_dual (attr := simp)]
/--
lemma `supClosed_supClosure` / 引理 `supClosed_supClosure`

English:
lemma supClosed_supClosure
  statement: SupClosed (supClosure s)
  proof: supClosure.isClosed_closure _

@[to_dual]

中文:
引理 supClosed_supClosure
  结论: SupClosed (supClosure s)
  证明: supClosure.isClosed_closure _

@[to_dual]

Depends on / 依赖: isClosed_closure, supClosure, supClosure.isClosed_closure
-/
lemma supClosed_supClosure : SupClosed (supClosure s) := supClosure.isClosed_closure _

@[to_dual]
/--
lemma `supClosure_mono` / 引理 `supClosure_mono`

English:
lemma supClosure_mono
  statement: Monotone (supClosure : Set α -> Set α)
  proof: supClosure.monotone

@[to_dual (attr := simp)]

中文:
引理 supClosure_mono
  结论: 递增 (supClosure : 集合 α -> 集合 α)
  证明: supClosure.monotone

@[to_dual (attr := simp)]

Depends on / 依赖: monotone, supClosure, supClosure.monotone
-/
lemma supClosure_mono : Monotone (supClosure : Set α -> Set α) := supClosure.monotone

@[to_dual (attr := simp)]
/--
lemma `supClosure_eq_self` / 引理 `supClosure_eq_self`

English:
lemma supClosure_eq_self
  statement: supClosure s = s ↔ SupClosed s
  proof: supClosure.isClosed_iff.symm

@[to_dual] alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

@[to_dual]

中文:
引理 supClosure_eq_self
  结论: supClosure s = s ↔ SupClosed s
  证明: supClosure.isClosed_iff.symm

@[to_dual] alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

@[to_dual]

Depends on / 依赖: isClosed_iff, supClosure, supClosure.isClosed_iff.symm
-/
lemma supClosure_eq_self : supClosure s = s ↔ SupClosed s := supClosure.isClosed_iff.symm

@[to_dual] alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

@[to_dual]
/--
lemma `supClosure_idem` / 引理 `supClosure_idem`

English:
lemma supClosure_idem
  given: (s : Set α)
  statement: supClosure (supClosure s) = supClosure s
  proof: supClosure.idempotent _

中文:
引理 supClosure_idem
  条件: (s : 集合 α)
  结论: supClosure (supClosure s) = supClosure s
  证明: supClosure.idempotent _

Depends on / 依赖: idempotent, supClosure, supClosure.idempotent
-/
lemma supClosure_idem (s : Set α) : supClosure (supClosure s) = supClosure s :=
  supClosure.idempotent _

/--
lemma `supClosure_empty` / 引理 `supClosure_empty`

English:
lemma supClosure_empty
  statement: supClosure (∅ : Set α) = ∅
  proof: by simp

中文:
引理 supClosure_empty
  结论: supClosure (∅ : 集合 α) = ∅
  证明: by simp
-/
@[to_dual (attr := simp)] lemma supClosure_empty : supClosure (∅ : Set α) = ∅ := by simp
/--
lemma `supClosure_singleton` / 引理 `supClosure_singleton`

English:
lemma supClosure_singleton
  statement: supClosure {a} = {a}
  proof: by simp
@[to_dual (attr := simp)]

中文:
引理 supClosure_singleton
  结论: supClosure {a} = {a}
  证明: by simp
@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] lemma supClosure_singleton : supClosure {a} = {a} := by simp
@[to_dual (attr := simp)]
/--
lemma `supClosure_univ` / 引理 `supClosure_univ`

English:
lemma supClosure_univ
  statement: supClosure (Set.univ : Set α) = Set.univ
  proof: by simp

@[to_dual (attr := simp)]

中文:
引理 supClosure_univ
  结论: supClosure (集合.univ : 集合 α) = 集合.univ
  证明: by simp

@[to_dual (attr := simp)]
-/
lemma supClosure_univ : supClosure (Set.univ : Set α) = Set.univ := by simp

@[to_dual (attr := simp)]
/--
lemma `upperBounds_supClosure` / 引理 `upperBounds_supClosure`

English:
lemma upperBounds_supClosure
  given: (s : Set α)
  statement: upperBounds (supClosure s) = upperBounds s
  proof: (upperBounds_mono_set subset_supClosure).antisymm by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
exact sup'_le _ _ fun b hb => ha hts hb

@[to_dual (attr := simp)]

中文:
引理 upperBounds_supClosure
  条件: (s : 集合 α)
  结论: upperBounds (supClosure s) = upperBounds s
  证明: (upperBounds_mono_set subset_supClosure).antisymm by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
exact sup'_le _ _ fun b hb => ha hts hb

@[to_dual (attr := simp)]

Depends on / 依赖: antisymm, subset_supClosure, upperBounds_mono_set
-/
lemma upperBounds_supClosure (s : Set α) : upperBounds (supClosure s) = upperBounds s :=
(upperBounds_mono_set subset_supClosure).antisymm by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
exact sup'_le _ _ fun b hb => ha hts hb

@[to_dual (attr := simp)]
/--
lemma `isLUB_supClosure` / 引理 `isLUB_supClosure`

English:
lemma isLUB_supClosure
  statement: IsLUB (supClosure s) a ↔ IsLUB s a
  proof: by simp [IsLUB]

@[to_dual]

中文:
引理 isLUB_supClosure
  结论: IsLUB (supClosure s) a ↔ IsLUB s a
  证明: by simp [IsLUB]

@[to_dual]
-/
lemma isLUB_supClosure : IsLUB (supClosure s) a ↔ IsLUB s a := by simp [IsLUB]

@[to_dual]
/--
lemma `sup_mem_supClosure` / 引理 `sup_mem_supClosure`

English:
lemma sup_mem_supClosure
  given: (ha : a in s) (hb : b in s)
  statement: a ⊔ b in supClosure s
  proof: supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

@[to_dual]

中文:
引理 sup_mem_supClosure
  条件: (ha : a in s) (hb : b in s)
  结论: a ⊔ b in supClosure s
  证明: supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

@[to_dual]

Depends on / 依赖: subset_supClosure, supClosed_supClosure
-/
lemma sup_mem_supClosure (ha : a in s) (hb : b in s) : a ⊔ b in supClosure s :=
  supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

@[to_dual]
/--
lemma `finsetSup'_mem_supClosure` / 引理 `finsetSup'_mem_supClosure`

English:
lemma finsetSup'_mem_supClosure
  statement: {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι -> α}
  proof: supClosed_supClosure.finsetSup'_mem _ fun _i hi => subset_supClosure hf _ hi

@[to_dual infClosure_min]

中文:
引理 finsetSup'_mem_supClosure
  结论: {ι : 类型} {t : 有限集 ι} (ht : t.非空) {f : ι -> α}
  证明: supClosed_supClosure.finsetSup'_mem _ fun _i hi => subset_supClosure hf _ hi

@[to_dual infClosure_min]
-/
lemma finsetSup'_mem_supClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι -> α}
    (hf : forall i in t, f i in s) : t.sup' ht f in supClosure s :=
supClosed_supClosure.finsetSup'_mem _ fun _i hi => subset_supClosure hf _ hi

@[to_dual infClosure_min]
/--
lemma `supClosure_min` / 引理 `supClosure_min`

English:
lemma supClosure_min
  statement: s subseteq t -> SupClosed t -> supClosure s subseteq t
  proof: supClosure.closure_min

中文:
引理 supClosure_min
  结论: s subseteq t -> SupClosed t -> supClosure s subseteq t
  证明: supClosure.closure_min

Depends on / 依赖: closure_min, supClosure, supClosure.closure_min
-/
lemma supClosure_min : s subseteq t -> SupClosed t -> supClosure s subseteq t := supClosure.closure_min

/-- The semilattice generated by a finite set is finite. -/
@[to_dual /-- The semilattice generated by a finite set is finite. -/]
/--
lemma `Set.Finite.supClosure` / 引理 `Set.Finite.supClosure`

English:
lemma Set.Finite.supClosure
  given: (hs : s.Finite)
  statement: (supClosure s).Finite
  proof: by
  lift s to Finset α using hs
  classical
  refine ({t in s.powerset | t.Nonempty}.attach.image
    fun t => t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.me

中文:
引理 集合.有限.supClosure
  条件: (hs : s.有限)
  结论: (supClosure s).有限
  证明: by
  lift s to Finset α using hs
  classical
  refine ({t in s.powerset | t.Nonempty}.attach.image
    fun t => t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.me
-/
protected lemma Set.Finite.supClosure (hs : s.Finite) : (supClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine ({t in s.powerset | t.Nonempty}.attach.image
    fun t => t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

/--
lemma `supClosure_prod` / 引理 `supClosure_prod`

English:
lemma supClosure_prod
  given: (s : Set α) (t : Set β)
  proof: le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) <|
    supClosed_supClosure.prod supClosed_supClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus 

中文:
引理 supClosure_prod
  条件: (s : 集合 α) (t : 集合 β)
  证明: le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) <|
    supClosed_supClosure.prod supClosed_supClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus 
-/
@[to_dual (attr := simp)] lemma supClosure_prod (s : Set α) (t : Set β) :
    supClosure (s ×ˢ t) = supClosure s ×ˢ supClosure t :=
  le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) <|
    supClosed_supClosure.prod supClosed_supClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prodMk_sup'_sup']

end SemilatticeSup

section Lattice
variable [Lattice α] [Lattice β] {s t : Set α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
/--
Definition of `latticeClosure` / `latticeClosure` 的定义

English:
definition latticeClosure
  signature: : ClosureOperator (Set α)
  body: .ofCompletePred IsSublattice fun _ => isSublattice_sInter

中文:
定义 latticeClosure
  签名: : 闭包算子 (集合 α)
  定义体: .ofCompletePred IsSublattice fun _ => isSublattice_sInter

Depends on / 依赖: IsSublattice, isSublattice_sInter, ofCompletePred
-/
def latticeClosure : ClosureOperator (Set α) :=
  .ofCompletePred IsSublattice fun _ => isSublattice_sInter

/--
lemma `subset_latticeClosure` / 引理 `subset_latticeClosure`

English:
lemma subset_latticeClosure
  statement: s subseteq latticeClosure s
  proof: latticeClosure.le_closure _

中文:
引理 subset_latticeClosure
  结论: s subseteq latticeClosure s
  证明: latticeClosure.le_closure _
-/
@[simp] lemma subset_latticeClosure : s subseteq latticeClosure s := latticeClosure.le_closure _

/--
lemma `isSublattice_latticeClosure` / 引理 `isSublattice_latticeClosure`

English:
lemma isSublattice_latticeClosure
  statement: IsSublattice (latticeClosure s)
  proof: latticeClosure.isClosed_closure _

中文:
引理 isSublattice_latticeClosure
  结论: 是子格 (latticeClosure s)
  证明: latticeClosure.isClosed_closure _
-/
@[simp] lemma isSublattice_latticeClosure : IsSublattice (latticeClosure s) :=
  latticeClosure.isClosed_closure _

/--
lemma `latticeClosure_min` / 引理 `latticeClosure_min`

English:
lemma latticeClosure_min
  statement: s subseteq t -> IsSublattice t -> latticeClosure s subseteq t
  proof: latticeClosure.closure_min

@[to_dual self (reorder := sup inf)]

中文:
引理 latticeClosure_min
  结论: s subseteq t -> 是子格 t -> latticeClosure s subseteq t
  证明: latticeClosure.closure_min

@[to_dual self (reorder := sup inf)]

Depends on / 依赖: closure_min, latticeClosure, latticeClosure.closure_min
-/
lemma latticeClosure_min : s subseteq t -> IsSublattice t -> latticeClosure s subseteq t :=
  latticeClosure.closure_min

@[to_dual self (reorder := sup inf)]
/--
lemma `latticeClosure_sup_inf_induction` / 引理 `latticeClosure_sup_inf_induction`

English:
lemma latticeClosure_sup_inf_induction
  statement: (p : (a : α) -> a in latticeClosure s -> Prop)
  proof: by
  have h : IsSublattice { a : α | exists has : a in latticeClosure s, p a has } := {
    supClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.supClosed has hbs, sup a has b hbs hpa hpb⟩
    infClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosur

中文:
引理 latticeClosure_sup_inf_induction
  结论: (p : (a : α) -> a in latticeClosure s -> 命题)
  证明: by
  have h : IsSublattice { a : α | exists has : a in latticeClosure s, p a has } := {
    supClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.supClosed has hbs, sup a has b hbs hpa hpb⟩
    infClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosur

Depends on / 依赖: IsSublattice, choose_spec, infClosed, isSublattice_latticeClosure, isSublattice_latticeClosure.infClosed, isSublattice_latticeClosure.supClosed, latticeClosure, latticeClosure_min, subset_latticeClosure, supClosed
-/
lemma latticeClosure_sup_inf_induction (p : (a : α) -> a in latticeClosure s -> Prop)
    (mem : forall (a : α) (has : a in s), p a (subset_latticeClosure has))
    (sup : forall (a : α) (has : a in latticeClosure s) (b : α) (hbs : b in latticeClosure s),
      p a has -> p b hbs -> p (a ⊔ b) (isSublattice_latticeClosure.supClosed has hbs))
    (inf : forall (a : α) (has : a in latticeClosure s) (b : α) (hbs : b in latticeClosure s),
      p a has -> p b hbs -> p (a ⊓ b) (isSublattice_latticeClosure.infClosed has hbs))
    {a : α} (has : a in latticeClosure s) :
    p a has := by
  have h : IsSublattice { a : α | exists has : a in latticeClosure s, p a has } := {
    supClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.supClosed has hbs, sup a has b hbs hpa hpb⟩
    infClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.infClosed has hbs, inf a has b hbs hpa hpb⟩ }
  refine (latticeClosure_min (fun a ha => ?_) h has).choose_spec
  exact ⟨subset_latticeClosure ha, mem a ha⟩

/--
lemma `latticeClosure_mono` / 引理 `latticeClosure_mono`

English:
lemma latticeClosure_mono
  statement: Monotone (latticeClosure : Set α -> Set α)
  proof: latticeClosure.monotone

中文:
引理 latticeClosure_mono
  结论: 递增 (latticeClosure : 集合 α -> 集合 α)
  证明: latticeClosure.monotone

Depends on / 依赖: latticeClosure, latticeClosure.monotone, monotone
-/
lemma latticeClosure_mono : Monotone (latticeClosure : Set α -> Set α) := latticeClosure.monotone

/--
lemma `latticeClosure_eq_self` / 引理 `latticeClosure_eq_self`

English:
lemma latticeClosure_eq_self
  statement: latticeClosure s = s ↔ IsSublattice s
  proof: latticeClosure.isClosed_iff.symm

alias ⟨_, IsSublattice.latticeClosure_eq⟩ := latticeClosure_eq_self

中文:
引理 latticeClosure_eq_self
  结论: latticeClosure s = s ↔ 是子格 s
  证明: latticeClosure.isClosed_iff.symm

alias ⟨_, IsSublattice.latticeClosure_eq⟩ := latticeClosure_eq_self
-/
@[simp] lemma latticeClosure_eq_self : latticeClosure s = s ↔ IsSublattice s :=
  latticeClosure.isClosed_iff.symm

alias ⟨_, IsSublattice.latticeClosure_eq⟩ := latticeClosure_eq_self

/--
lemma `latticeClosure_idem` / 引理 `latticeClosure_idem`

English:
lemma latticeClosure_idem
  given: (s : Set α)
  statement: latticeClosure (latticeClosure s) = latticeClosure s
  proof: latticeClosure.idempotent _

中文:
引理 latticeClosure_idem
  条件: (s : 集合 α)
  结论: latticeClosure (latticeClosure s) = latticeClosure s
  证明: latticeClosure.idempotent _

Depends on / 依赖: idempotent, latticeClosure, latticeClosure.idempotent
-/
lemma latticeClosure_idem (s : Set α) : latticeClosure (latticeClosure s) = latticeClosure s :=
  latticeClosure.idempotent _

/--
lemma `latticeClosure_empty` / 引理 `latticeClosure_empty`

English:
lemma latticeClosure_empty
  statement: latticeClosure (∅ : Set α) = ∅
  proof: by simp

中文:
引理 latticeClosure_empty
  结论: latticeClosure (∅ : 集合 α) = ∅
  证明: by simp
-/
@[simp] lemma latticeClosure_empty : latticeClosure (∅ : Set α) = ∅ := by simp
/--
lemma `latticeClosure_singleton` / 引理 `latticeClosure_singleton`

English:
lemma latticeClosure_singleton
  given: (a : α)
  statement: latticeClosure {a} = {a}
  proof: by simp

中文:
引理 latticeClosure_singleton
  条件: (a : α)
  结论: latticeClosure {a} = {a}
  证明: by simp
-/
@[simp] lemma latticeClosure_singleton (a : α) : latticeClosure {a} = {a} := by simp
/--
lemma `latticeClosure_univ` / 引理 `latticeClosure_univ`

English:
lemma latticeClosure_univ
  statement: latticeClosure (Set.univ : Set α) = Set.univ
  proof: by simp

@[to_dual self (reorder := map_sup map_inf)]

中文:
引理 latticeClosure_univ
  结论: latticeClosure (集合.univ : 集合 α) = 集合.univ
  证明: by simp

@[to_dual self (reorder := map_sup map_inf)]
-/
@[simp] lemma latticeClosure_univ : latticeClosure (Set.univ : Set α) = Set.univ := by simp

@[to_dual self (reorder := map_sup map_inf)]
/--
lemma `image_latticeClosure` / 引理 `image_latticeClosure`

English:
lemma image_latticeClosure
  statement: (s : Set α) (f : α -> β)
  proof: by
  simp only [subset_antisymm_iff, Set.image_subset_iff]
  constructor <;> apply latticeClosure_sup_inf_induction
· exact fun a ha => subset_latticeClosure Set.mem_image_of_mem _ ha
  · rintro a - b - ha hb
    simpa [map_sup] using isSublattice_latticeClosure.supClosed ha hb
  · rintro a - b - ha

中文:
引理 image_latticeClosure
  结论: (s : 集合 α) (f : α -> β)
  证明: by
  simp only [subset_antisymm_iff, Set.image_subset_iff]
  constructor <;> apply latticeClosure_sup_inf_induction
· exact fun a ha => subset_latticeClosure Set.mem_image_of_mem _ ha
  · rintro a - b - ha hb
    simpa [map_sup] using isSublattice_latticeClosure.supClosed ha hb
  · rintro a - b - ha

Depends on / 依赖: Set.image_mono, Set.image_subset_iff, Set.mem_image_of_mem, image_mono, image_subset_iff, infClosed, isSublattice_latticeClosure, isSublattice_latticeClosure.infClosed, isSublattice_latticeClosure.supClosed, latticeClosure_sup_inf_induction, map_inf, map_sup, mem_image_of_mem, subset_antisymm_iff, subset_latticeClosure, supClosed
-/
lemma image_latticeClosure (s : Set α) (f : α -> β)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b) :
    f '' latticeClosure s = latticeClosure (f '' s) := by
  simp only [subset_antisymm_iff, Set.image_subset_iff]
  constructor <;> apply latticeClosure_sup_inf_induction
· exact fun a ha => subset_latticeClosure Set.mem_image_of_mem _ ha
  · rintro a - b - ha hb
    simpa [map_sup] using isSublattice_latticeClosure.supClosed ha hb
  · rintro a - b - ha hb
    simpa [map_inf] using isSublattice_latticeClosure.infClosed ha hb
  · exact Set.image_mono subset_latticeClosure
  · rintro _ - _ - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊔ b, isSublattice_latticeClosure.supClosed ha hb, map_sup ..⟩
  · rintro _ - _ - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊓ b, isSublattice_latticeClosure.infClosed ha hb, map_inf ..⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofDual_preimage_latticeClosure` / 引理 `ofDual_preimage_latticeClosure`

English:
lemma ofDual_preimage_latticeClosure
  given: (s : Set α)
  proof: by
  ext
  simp [latticeClosure, (Equiv.Set.congr toDual).surjective.forall, Equiv.image_eq_preimage_symm]

@[to_dual self (reorder := map_sup map_inf)]

中文:
引理 ofDual_preimage_latticeClosure
  条件: (s : 集合 α)
  证明: by
  ext
  simp [latticeClosure, (Equiv.Set.congr toDual).surjective.forall, Equiv.image_eq_preimage_symm]

@[to_dual self (reorder := map_sup map_inf)]

Depends on / 依赖: Equiv.Set.congr, Equiv.image_eq_preimage_symm, image_eq_preimage_symm, latticeClosure, surjective, surjective.forall, toDual
-/
lemma ofDual_preimage_latticeClosure (s : Set α) :
    ofDual ⁻¹' latticeClosure s = latticeClosure (ofDual ⁻¹' s) := by
  ext
  simp [latticeClosure, (Equiv.Set.congr toDual).surjective.forall, Equiv.image_eq_preimage_symm]

@[to_dual self (reorder := map_sup map_inf)]
/--
lemma `image_latticeClosure'` / 引理 `image_latticeClosure'`

English:
lemma image_latticeClosure'
  statement: (s : Set α) (f : α -> β)
  proof: by
  simpa only [Set.image_comp, Equiv.image_symm_eq_preimage, ← ofDual_preimage_latticeClosure]
    using! image_latticeClosure s (ofDual.symm ∘ f) map_sup map_inf

中文:
引理 image_latticeClosure'
  结论: (s : 集合 α) (f : α -> β)
  证明: by
  simpa only [Set.image_comp, Equiv.image_symm_eq_preimage, ← ofDual_preimage_latticeClosure]
    using! image_latticeClosure s (ofDual.symm ∘ f) map_sup map_inf

Depends on / 依赖: Equiv.image_symm_eq_preimage, Set.image_comp, image_comp, image_latticeClosure, image_symm_eq_preimage, map_inf, map_sup, ofDual, ofDual.symm, ofDual_preimage_latticeClosure
-/
lemma image_latticeClosure' (s : Set α) (f : α -> β)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊓ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊔ f b) :
    f '' latticeClosure s = latticeClosure (f '' s) := by
  simpa only [Set.image_comp, Equiv.image_symm_eq_preimage, ← ofDual_preimage_latticeClosure]
    using! image_latticeClosure s (ofDual.symm ∘ f) map_sup map_inf

end Lattice

section DistribLattice
variable [DistribLattice α] [DistribLattice β] {s : Set α}

@[to_dual]
/--
lemma `SupClosed.infClosure` / 引理 `SupClosed.infClosure`

English:
lemma SupClosed.infClosure
  given: (hs : SupClosed s)
  statement: SupClosed (infClosure s)
  proof: by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi => hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[to_dual (attr := simp)]

中文:
引理 SupClosed.infClosure
  条件: (hs : SupClosed s)
  结论: SupClosed (infClosure s)
  证明: by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi => hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[to_dual (attr := simp)]
-/
protected lemma SupClosed.infClosure (hs : SupClosed s) : SupClosed (infClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi => hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[to_dual (attr := simp)]
/--
lemma `supClosure_infClosure` / 引理 `supClosure_infClosure`

English:
lemma supClosure_infClosure
  given: (s : Set α)
  statement: supClosure (infClosure s) = latticeClosure s
  proof: le_antisymm (supClosure_min (infClosure_min subset_latticeClosure isSublattice_latticeClosure.2)
    isSublattice_latticeClosure.1) <| latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩

中文:
引理 supClosure_infClosure
  条件: (s : 集合 α)
  结论: supClosure (infClosure s) = latticeClosure s
  证明: le_antisymm (supClosure_min (infClosure_min subset_latticeClosure isSublattice_latticeClosure.2)
    isSublattice_latticeClosure.1) <| latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩

Depends on / 依赖: infClosed_infClosure, infClosed_infClosure.supClosure, infClosure_min, isSublattice_latticeClosure, latticeClosure_min, le_antisymm, subset_infClosure, subset_infClosure.trans, subset_latticeClosure, subset_supClosure, supClosed_supClosure, supClosure, supClosure_min
-/
lemma supClosure_infClosure (s : Set α) : supClosure (infClosure s) = latticeClosure s :=
  le_antisymm (supClosure_min (infClosure_min subset_latticeClosure isSublattice_latticeClosure.2)
    isSublattice_latticeClosure.1) <| latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩

/--
lemma `Set.Finite.latticeClosure` / 引理 `Set.Finite.latticeClosure`

English:
lemma Set.Finite.latticeClosure
  given: (hs : s.Finite)
  statement: (latticeClosure s).Finite
  proof: by
  rw [← supClosure_infClosure]; exact hs.infClosure.supClosure

中文:
引理 集合.有限.latticeClosure
  条件: (hs : s.有限)
  结论: (latticeClosure s).有限
  证明: by
  rw [← supClosure_infClosure]; exact hs.infClosure.supClosure

Depends on / 依赖: hs.infClosure.supClosure, infClosure, supClosure, supClosure_infClosure
-/
lemma Set.Finite.latticeClosure (hs : s.Finite) : (latticeClosure s).Finite := by
  rw [← supClosure_infClosure]; exact hs.infClosure.supClosure

/--
lemma `latticeClosure_prod` / 引理 `latticeClosure_prod`

English:
lemma latticeClosure_prod
  given: (s : Set α) (t : Set β)
  proof: by
  simp_rw [← supClosure_infClosure]; simp

中文:
引理 latticeClosure_prod
  条件: (s : 集合 α) (t : 集合 β)
  证明: by
  simp_rw [← supClosure_infClosure]; simp
-/
@[simp] lemma latticeClosure_prod (s : Set α) (t : Set β) :
    latticeClosure (s ×ˢ t) = latticeClosure s ×ˢ latticeClosure t := by
  simp_rw [← supClosure_infClosure]; simp

end DistribLattice

/-- A join-semilattice where every sup-closed set has a least upper bound is automatically complete.
-/
@[to_dual (attr := instance_reducible) /--
A meet-semilattice where every inf-closed set has a greatest lower bound is automatically
complete. -/]
/--
Definition of `SemilatticeSup.toCompleteSemilatticeSup` / `SemilatticeSup.toCompleteSemilatticeSup` 的定义

English:
definition SemilatticeSup.toCompleteSemilatticeSup
  signature: [SemilatticeSup α] (sSup : Set α -> α)
  body: fun s => sSup (supClosure s)
isLUB_sSup _ := isLUB_supClosure.mp h _ supClosed_supClosure

中文:
定义 SemilatticeSup.toCompleteSemilatticeSup
  签名: [SemilatticeSup α] (sSup : 集合 α -> α)
  定义体: fun s => sSup (supClosure s)
isLUB_sSup _ := isLUB_supClosure.mp h _ supClosed_supClosure

Depends on / 依赖: supClosure
-/
def SemilatticeSup.toCompleteSemilatticeSup [SemilatticeSup α] (sSup : Set α -> α)
    (h : forall s, SupClosed s -> IsLUB s (sSup s)) : CompleteSemilatticeSup α where
  sSup := fun s => sSup (supClosure s)
isLUB_sSup _ := isLUB_supClosure.mp h _ supClosed_supClosure

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] {f : ι -> α} {s t : Set α}

@[to_dual]
/--
lemma `SupClosed.iSup_mem_of_nonempty` / 引理 `SupClosed.iSup_mem_of_nonempty`

English:
lemma SupClosed.iSup_mem_of_nonempty
  statement: [Finite ι] [Nonempty ι] (hs : SupClosed s)
  proof: by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down]; rw [← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ => hf _

@[to_dual]

中文:
引理 SupClosed.iSup_mem_of_nonempty
  结论: [有限 ι] [非空 ι] (hs : SupClosed s)
  证明: by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down]; rw [← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ => hf _

@[to_dual]

Depends on / 依赖: Finset, Finset.sup, Finset.univ_nonempty, _mem, _univ_eq_ciSup, finsetSup, hs.finsetSup, iSup_plift_down, nonempty_fintype, univ_nonempty
-/
lemma SupClosed.iSup_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : SupClosed s)
    (hf : forall i, f i in s) : ⨆ i, f i in s := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down]; rw [← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ => hf _

@[to_dual]
/--
lemma `SupClosed.sSup_mem_of_nonempty` / 引理 `SupClosed.sSup_mem_of_nonempty`

English:
lemma SupClosed.sSup_mem_of_nonempty
  statement: (hs : SupClosed s) (ht : t.Finite) (ht' : t.Nonempty)
  proof: by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

中文:
引理 SupClosed.sSup_mem_of_nonempty
  结论: (hs : SupClosed s) (ht : t.有限) (ht' : t.非空)
  证明: by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

Depends on / 依赖: hs.iSup_mem_of_nonempty, ht.to_subtype, iSup_mem_of_nonempty, sSup_eq_iSup, to_subtype
-/
lemma SupClosed.sSup_mem_of_nonempty (hs : SupClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t subseteq s) : sSup t in s := by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

end ConditionallyCompleteLattice

section BooleanAlgebra
variable [BooleanAlgebra α] {s : Set α}

/--
lemma `compl_image_latticeClosure` / 引理 `compl_image_latticeClosure`

English:
lemma compl_image_latticeClosure
  given: (s : Set α)
  proof: image_latticeClosure' s _ compl_sup_distrib (fun _ _ => compl_inf)

中文:
引理 compl_image_latticeClosure
  条件: (s : 集合 α)
  证明: image_latticeClosure' s _ compl_sup_distrib (fun _ _ => compl_inf)

Depends on / 依赖: compl_inf, compl_sup_distrib, image_latticeClosure
-/
lemma compl_image_latticeClosure (s : Set α) :
    compl '' latticeClosure s = latticeClosure (compl '' s) :=
  image_latticeClosure' s _ compl_sup_distrib (fun _ _ => compl_inf)

/--
lemma `compl_image_latticeClosure_eq_of_compl_image_eq_self` / 引理 `compl_image_latticeClosure_eq_of_compl_image_eq_self`

English:
lemma compl_image_latticeClosure_eq_of_compl_image_eq_self
  given: (hs : compl '' s = s)
  proof: compl_image_latticeClosure s ▸ hs.symm ▸ rfl

中文:
引理 compl_image_latticeClosure_eq_of_compl_image_eq_self
  条件: (hs : compl '' s = s)
  证明: compl_image_latticeClosure s ▸ hs.symm ▸ rfl

Depends on / 依赖: compl_image_latticeClosure, hs.symm
-/
lemma compl_image_latticeClosure_eq_of_compl_image_eq_self (hs : compl '' s = s) :
    compl '' latticeClosure s = latticeClosure s :=
  compl_image_latticeClosure s ▸ hs.symm ▸ rfl

end BooleanAlgebra

variable [CompleteLattice α] {f : ι -> α} {s t : Set α}

@[to_dual]
/--
lemma `SupClosed.biSup_mem_of_nonempty` / 引理 `SupClosed.biSup_mem_of_nonempty`

English:
lemma SupClosed.biSup_mem_of_nonempty
  statement: {ι : Type*} {t : Set ι} {f : ι -> α} (hs : SupClosed s)
  proof: by
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

@[to_dual]

中文:
引理 SupClosed.biSup_mem_of_nonempty
  结论: {ι : 类型} {t : 集合 ι} {f : ι -> α} (hs : SupClosed s)
  证明: by
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

@[to_dual]

Depends on / 依赖: hs.sSup_mem_of_nonempty, ht.image, sSup_image, sSup_mem_of_nonempty
-/
lemma SupClosed.biSup_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι -> α} (hs : SupClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : forall i in t, f i in s) : ⨆ i in t, f i in s := by
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

@[to_dual]
/--
lemma `SupClosed.iSup_mem` / 引理 `SupClosed.iSup_mem`

English:
lemma SupClosed.iSup_mem
  given: [Finite ι] (hs : SupClosed s) (hbot : ⊥ in s) (hf : forall i, f i in s)
  proof: by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

@[to_dual]

中文:
引理 SupClosed.iSup_mem
  条件: [有限 ι] (hs : SupClosed s) (hbot : ⊥ in s) (hf : 对任意 i, f i in s)
  证明: by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

@[to_dual]

Depends on / 依赖: hs.iSup_mem_of_nonempty, iSup_mem_of_nonempty, iSup_of_empty, isEmpty_or_nonempty
-/
lemma SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hbot : ⊥ in s) (hf : forall i, f i in s) :
    ⨆ i, f i in s := by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

@[to_dual]
/--
lemma `SupClosed.sSup_mem` / 引理 `SupClosed.sSup_mem`

English:
lemma SupClosed.sSup_mem
  given: (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ in s) (hts : t subseteq s)
  proof: by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

@[to_dual]

中文:
引理 SupClosed.sSup_mem
  条件: (hs : SupClosed s) (ht : t.有限) (hbot : ⊥ in s) (hts : t subseteq s)
  证明: by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

@[to_dual]

Depends on / 依赖: hs.iSup_mem, ht.to_subtype, iSup_mem, sSup_eq_iSup, to_subtype
-/
lemma SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ in s) (hts : t subseteq s) :
    sSup t in s := by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

@[to_dual]
/--
lemma `SupClosed.biSup_mem` / 引理 `SupClosed.biSup_mem`

English:
lemma SupClosed.biSup_mem
  statement: {ι : Type*} {t : Set ι} {f : ι -> α} (hs : SupClosed s)
  proof: by
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)

中文:
引理 SupClosed.biSup_mem
  结论: {ι : 类型} {t : 集合 ι} {f : ι -> α} (hs : SupClosed s)
  证明: by
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)

Depends on / 依赖: hs.sSup_mem, ht.image, sSup_image, sSup_mem
-/
lemma SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι -> α} (hs : SupClosed s)
    (ht : t.Finite) (hbot : ⊥ in s) (hf : forall i in t, f i in s) : ⨆ i in t, f i in s := by
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)
