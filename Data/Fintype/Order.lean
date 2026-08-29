/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Set.Finite.Basic -- shake: keep (IsAtomic α), cf. lean#13417
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Atoms

import Mathlib.Data.Finite.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Order structures on finite types

This file provides order instances on fintypes.

## Computable instances

On a `Fintype`, we can construct
* an `OrderBot` from `SemilatticeInf`.
* an `OrderTop` from `SemilatticeSup`.
* a `BoundedOrder` from `Lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `sSup` and `sInf` use `Set.toFinset`
and set membership is undecidable in general.

On a `Fintype`, we can promote:
* a `Lattice` to a `CompleteLattice`.
* a `DistribLattice` to a `CompleteDistribLattice`.
* a `LinearOrder` to a `CompleteLinearOrder`.
* a `BooleanAlgebra` to a `CompleteAtomicBooleanAlgebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `Fin.completeLinearOrder`
* `Bool.completeLinearOrder`
* `Bool.completeBooleanAlgebra`
-/

public section


open Finset

namespace Fintype

variable {ι α : Type*} [Fintype ι] [Fintype α]

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/--
Definition of `toOrderBot` / `toOrderBot` 的定义

English:
abbreviation toOrderBot
  signature: [SemilatticeInf α]
  body: univ.inf' univ_nonempty id
bot_le a := inf'_le _ mem_univ a

中文:
缩写 toOrderBot
  签名: [SemilatticeInf α]
  定义体: univ.inf' univ_nonempty id
bot_le a := inf'_le _ mem_univ a

Depends on / 依赖: Terminates, _of_not_terminates, _of_terminates, length, length_cons, terminates_cons_iff, univ.inf, univ_nonempty
-/
abbrev toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
bot_le a := inf'_le _ mem_univ a

-- See note [reducible non-instances]
/--
Definition of `toOrderTop` / `toOrderTop` 的定义

English:
abbreviation toOrderTop
  signature: [SemilatticeSup α]
  body: univ.sup' univ_nonempty id
le_top a := le_sup' id mem_univ a

中文:
缩写 toOrderTop
  签名: [SemilatticeSup α]
  定义体: univ.sup' univ_nonempty id
le_top a := le_sup' id mem_univ a

Depends on / 依赖: univ.sup, univ_nonempty
-/
abbrev toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
le_top a := le_sup' id mem_univ a

-- See note [reducible non-instances]
/--
Definition of `toBoundedOrder` / `toBoundedOrder` 的定义

English:
abbreviation toBoundedOrder
  signature: [Lattice α]
  body: { toOrderBot α, toOrderTop α with }

中文:
缩写 toBoundedOrder
  签名: [格 α]
  定义体: { toOrderBot α, toOrderTop α with }

Depends on / 依赖: toOrderBot, toOrderTop
-/
abbrev toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }

end Nonempty

section BoundedOrder

variable (α)

open scoped Classical in
-- See note [reducible non-instances]
/--
Definition of `toCompleteLattice` / `toCompleteLattice` 的定义

English:
abbreviation toCompleteLattice
  signature: [Lattice α] [BoundedOrder α]
  body: ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  isLUB_sSup s := Set.coe_toFinset s ▸ Finset.isLUB_sup_id
  isGLB_sInf s := Set.coe_toFinset s ▸ Finset.isGLB_inf_id

中文:
缩写 toCompleteLattice
  签名: [格 α] [有界序 α]
  定义体: ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  isLUB_sSup s := Set.coe_toFinset s ▸ Finset.isLUB_sup_id
  isGLB_sInf s := Set.coe_toFinset s ▸ Finset.isGLB_inf_id

Depends on / 依赖: Lattice
-/
noncomputable abbrev toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where
  __ := ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  isLUB_sSup s := Set.coe_toFinset s ▸ Finset.isLUB_sup_id
  isGLB_sInf s := Set.coe_toFinset s ▸ Finset.isGLB_inf_id

attribute [local instance] toCompleteLattice in
-- See note [reducible non-instances]
/--
Definition of `toCompleteDistribLatticeMinimalAxioms` / `toCompleteDistribLatticeMinimalAxioms` 的定义

English:
abbreviation toCompleteDistribLatticeMinimalAxioms
  signature: [DistribLattice α] [BoundedOrder α]
  body: fun a s => by
    convert! (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert! (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl

中文:
缩写 toCompleteDistribLatticeMinimalAxioms
  签名: [Distrib格 α] [有界序 α]
  定义体: fun a s => by
    convert! (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert! (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl

Depends on / 依赖: Finset, Finset.inf_eq_iInf, Finset.inf_sup_distrib_left, Finset.sup_eq_iSup, Finset.sup_inf_distrib_left, Set.mem_toFinset, convert, inf_eq_iInf, inf_sSup_le_iSup_inf, inf_sup_distrib_left, mem_toFinset, s.toFinset, simp_rw, sup_eq_iSup, sup_inf_distrib_left, toFinset
-/
noncomputable abbrev toCompleteDistribLatticeMinimalAxioms [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice.MinimalAxioms α where
  iInf_sup_le_sup_sInf := fun a s => by
    convert! (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert! (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl

attribute [local instance] toCompleteLattice in
-- See note [reducible non-instances]
/--
Definition of `toCompleteDistribLattice` / `toCompleteDistribLattice` 的定义

English:
abbreviation toCompleteDistribLattice
  signature: [DistribLattice α] [BoundedOrder α]
  body: .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)

中文:
缩写 toCompleteDistribLattice
  签名: [Distrib格 α] [有界序 α]
  定义体: .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)

Depends on / 依赖: ofMinimalAxioms, toCompleteDistribLatticeMinimalAxioms
-/
noncomputable abbrev toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α := .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)

-- See note [reducible non-instances]
/--
Definition of `toCompleteLinearOrder` / `toCompleteLinearOrder` 的定义

English:
abbreviation toCompleteLinearOrder
  body: { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra _ with }

中文:
缩写 toCompleteLinearOrder
  定义体: { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra _ with }

Depends on / 依赖: LinearOrder, LinearOrder.toBiheytingAlgebra, Terminates, _of_not_terminates, _of_terminates, forall_not_of_not_exists, length, length_le_iff, s.Terminates, toBiheytingAlgebra, toCompleteLattice
-/
noncomputable abbrev toCompleteLinearOrder
    [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra _ with }

-- See note [reducible non-instances]
/--
Definition of `toCompleteBooleanAlgebra` / `toCompleteBooleanAlgebra` 的定义

English:
abbreviation toCompleteBooleanAlgebra
  signature: [BooleanAlgebra α]
  body: ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α

中文:
缩写 toComplete布尔eanAlgebra
  签名: [布尔代数 α]
  定义体: ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α

Depends on / 依赖: BooleanAlgebra
-/
noncomputable abbrev toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α

-- See note [reducible non-instances]
/--
Definition of `toCompleteAtomicBooleanAlgebra` / `toCompleteAtomicBooleanAlgebra` 的定义

English:
abbreviation toCompleteAtomicBooleanAlgebra
  signature: [BooleanAlgebra α]
  body: (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

中文:
缩写 toCompleteAtomic布尔eanAlgebra
  签名: [布尔代数 α]
  定义体: (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

Depends on / 依赖: toCompleteAtomicBooleanAlgebra, toCompleteBooleanAlgebra
-/
noncomputable abbrev toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra α :=
  (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/--
Definition of `toCompleteLatticeOfNonempty` / `toCompleteLatticeOfNonempty` 的定义

English:
abbreviation toCompleteLatticeOfNonempty
  signature: [Lattice α]
  body: @toCompleteLattice _ _ _ toBoundedOrder α

中文:
缩写 toCompleteLatticeOfNonempty
  签名: [格 α]
  定义体: @toCompleteLattice _ _ _ toBoundedOrder α

Depends on / 依赖: toBoundedOrder, toCompleteLattice
-/
noncomputable abbrev toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α :=
@toCompleteLattice _ _ _ toBoundedOrder α

-- See note [reducible non-instances]
/--
Definition of `toCompleteLinearOrderOfNonempty` / `toCompleteLinearOrderOfNonempty` 的定义

English:
abbreviation toCompleteLinearOrderOfNonempty
  signature: [LinearOrder α]
  body: @toCompleteLinearOrder _ _ _ toBoundedOrder α

中文:
缩写 toCompleteLinearOrderOfNonempty
  签名: [线性序 α]
  定义体: @toCompleteLinearOrder _ _ _ toBoundedOrder α

Depends on / 依赖: toBoundedOrder, toCompleteLinearOrder
-/
noncomputable abbrev toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α :=
@toCompleteLinearOrder _ _ _ toBoundedOrder α

end Nonempty

end Fintype


/--
Instance `Fin.completeLinearOrder` / 实例 `Fin.completeLinearOrder`

English:
instance Fin.completeLinearOrder
  signature: {n : Nat} [NeZero n]
  body: Fintype.toCompleteLinearOrder _

中文:
实例 有限集.completeLinearOrder
  签名: {n : 自然数} [NeZero n]
  定义体: Fintype.toCompleteLinearOrder _

Depends on / 依赖: Fintype, Fintype.toCompleteLinearOrder, toCompleteLinearOrder
-/
noncomputable instance Fin.completeLinearOrder {n : Nat} [NeZero n] : CompleteLinearOrder (Fin n) :=
  Fintype.toCompleteLinearOrder _

/--
Instance `Bool.completeBooleanAlgebra` / 实例 `Bool.completeBooleanAlgebra`

English:
instance Bool.completeBooleanAlgebra
  signature: : CompleteBooleanAlgebra Bool
  body: Fintype.toCompleteBooleanAlgebra _

中文:
实例 布尔值.complete布尔eanAlgebra
  签名: : 完备布尔代数 布尔值
  定义体: Fintype.toCompleteBooleanAlgebra _

Depends on / 依赖: Fintype, Fintype.toCompleteBooleanAlgebra, toCompleteBooleanAlgebra
-/
noncomputable instance Bool.completeBooleanAlgebra : CompleteBooleanAlgebra Bool :=
  Fintype.toCompleteBooleanAlgebra _

/--
Instance `Bool.completeLinearOrder` / 实例 `Bool.completeLinearOrder`

English:
instance Bool.completeLinearOrder
  signature: : CompleteLinearOrder Bool where
  body: Fintype.toCompleteLattice _
  __ : BiheytingAlgebra Bool := inferInstance
  __ : LinearOrder Bool := inferInstance

中文:
实例 布尔值.completeLinearOrder
  签名: : 完备线性序 布尔值 where
  定义体: Fintype.toCompleteLattice _
  __ : BiheytingAlgebra Bool := inferInstance
  __ : LinearOrder Bool := inferInstance

Depends on / 依赖: Fintype, Fintype.toCompleteLattice, toCompleteLattice
-/
noncomputable instance Bool.completeLinearOrder : CompleteLinearOrder Bool where
  __ := Fintype.toCompleteLattice _
  __ : BiheytingAlgebra Bool := inferInstance
  __ : LinearOrder Bool := inferInstance

/--
Instance `Bool.completeAtomicBooleanAlgebra` / 实例 `Bool.completeAtomicBooleanAlgebra`

English:
instance Bool.completeAtomicBooleanAlgebra
  signature: : CompleteAtomicBooleanAlgebra Bool
  body: Fintype.toCompleteAtomicBooleanAlgebra _

中文:
实例 布尔值.completeAtomic布尔eanAlgebra
  签名: : 余mpleteAtomic布尔ean代数 布尔值
  定义体: Fintype.toCompleteAtomicBooleanAlgebra _

Depends on / 依赖: Fintype, Fintype.toCompleteAtomicBooleanAlgebra, toCompleteAtomicBooleanAlgebra
-/
noncomputable instance Bool.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Bool :=
  Fintype.toCompleteAtomicBooleanAlgebra _

/-! ### Directed Orders -/

section DirectedOrders

variable {ι : Sort*} {α : Type*} {r : α -> α -> Prop} [IsTrans α r] {γ : Type*} [Nonempty γ]
  {f : γ -> α} [Finite ι]

/--
theorem `Directed.finite_set_le` / 定理 `Directed.finite_set_le`

English:
theorem Directed.finite_set_le
  given: (D : Directed r f) {s : Set γ} (hs : s.Finite)
  proof: by
  convert! D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]

中文:
定理 Directed.finite_set_le
  条件: (D : Directed r f) {s : 集合 γ} (hs : s.有限)
  证明: by
  convert! D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]

Depends on / 依赖: D.finset_le, Finite, Set.Finite.mem_toFinset, convert, finset_le, hs.toFinset, mem_toFinset, toFinset
-/
theorem Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) :
    exists z, forall i in s, r (f i) (f z) := by
  convert! D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]

/--
lemma `Directed.finite_le` / 引理 `Directed.finite_le`

English:
lemma Directed.finite_le
  statement: {ι κ : Sort*} [Nonempty ι] [Finite κ] {f : ι -> α} (hf : Directed r f)
  proof: by
  simpa using
    (hf.comp_of_surjective PLift.down_surjective).finite_set_le (Set.finite_range (PLift.up ∘ g))

中文:
引理 Directed.finite_le
  结论: {ι κ : 类型层*} [非空 ι] [有限 κ] {f : ι -> α} (hf : Directed r f)
  证明: by
  simpa using
    (hf.comp_of_surjective PLift.down_surjective).finite_set_le (Set.finite_range (PLift.up ∘ g))

Depends on / 依赖: PLift.down_surjective, PLift.up, Set.finite_range, comp_of_surjective, down_surjective, finite_range, finite_set_le, hf.comp_of_surjective
-/
lemma Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finite κ] {f : ι -> α} (hf : Directed r f)
    (g : κ -> ι) : exists z, forall i, r (f (g i)) (f z) := by
  simpa using
    (hf.comp_of_surjective PLift.down_surjective).finite_set_le (Set.finite_range (PLift.up ∘ g))

variable [Nonempty α] [Preorder α]

/--
theorem `Finite.exists_le` / 定理 `Finite.exists_le`

English:
theorem Finite.exists_le
  given: [IsDirectedOrder α] (f : ι -> α)
  statement: exists M, forall i, f i <= M
  proof: directed_id.finite_le _

中文:
定理 有限.存在_le
  条件: [IsDirectedOrder α] (f : ι -> α)
  结论: 存在 M, 对任意 i, f i <= M
  证明: directed_id.finite_le _

Depends on / 依赖: directed_id, directed_id.finite_le, finite_le
-/
theorem Finite.exists_le [IsDirectedOrder α] (f : ι -> α) : exists M, forall i, f i <= M :=
  directed_id.finite_le _

/--
theorem `Finite.exists_ge` / 定理 `Finite.exists_ge`

English:
theorem Finite.exists_ge
  given: [IsCodirectedOrder α] (f : ι -> α)
  statement: exists M, forall i, M <= f i
  proof: directed_id.finite_le (r := (· >= ·)) _

中文:
定理 有限.存在_ge
  条件: [IsCodirectedOrder α] (f : ι -> α)
  结论: 存在 M, 对任意 i, M <= f i
  证明: directed_id.finite_le (r := (· >= ·)) _

Depends on / 依赖: directed_id, directed_id.finite_le, finite_le
-/
theorem Finite.exists_ge [IsCodirectedOrder α] (f : ι -> α) : exists M, forall i, M <= f i :=
  directed_id.finite_le (r := (· >= ·)) _

/--
theorem `Set.Finite.exists_le` / 定理 `Set.Finite.exists_le`

English:
theorem Set.Finite.exists_le
  given: [IsDirectedOrder α] {s : Set α} (hs : s.Finite)
  proof: directed_id.finite_set_le hs

中文:
定理 集合.有限.存在_le
  条件: [IsDirectedOrder α] {s : 集合 α} (hs : s.有限)
  证明: directed_id.finite_set_le hs

Depends on / 依赖: directed_id, directed_id.finite_set_le, finite_set_le
-/
theorem Set.Finite.exists_le [IsDirectedOrder α] {s : Set α} (hs : s.Finite) :
    exists M, forall i in s, i <= M :=
  directed_id.finite_set_le hs

/--
theorem `Set.Finite.exists_ge` / 定理 `Set.Finite.exists_ge`

English:
theorem Set.Finite.exists_ge
  given: [IsCodirectedOrder α] {s : Set α} (hs : s.Finite)
  proof: directed_id.finite_set_le (r := (· >= ·)) hs

@[simp]

中文:
定理 集合.有限.存在_ge
  条件: [IsCodirectedOrder α] {s : 集合 α} (hs : s.有限)
  证明: directed_id.finite_set_le (r := (· >= ·)) hs

@[simp]

Depends on / 依赖: directed_id, directed_id.finite_set_le, finite_set_le
-/
theorem Set.Finite.exists_ge [IsCodirectedOrder α] {s : Set α} (hs : s.Finite) :
    exists M, forall i in s, M <= i :=
  directed_id.finite_set_le (r := (· >= ·)) hs

@[simp]
/--
theorem `Finite.bddAbove_range` / 定理 `Finite.bddAbove_range`

English:
theorem Finite.bddAbove_range
  given: [IsDirectedOrder α] (f : ι -> α)
  statement: BddAbove (Set.range f)
  proof: by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

@[simp]

中文:
定理 有限.bddAbove_range
  条件: [IsDirectedOrder α] (f : ι -> α)
  结论: BddAbove (集合.range f)
  证明: by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

@[simp]

Depends on / 依赖: Finite, Finite.exists_le, exists_le
-/
theorem Finite.bddAbove_range [IsDirectedOrder α] (f : ι -> α) : BddAbove (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

@[simp]
/--
theorem `Finite.bddBelow_range` / 定理 `Finite.bddBelow_range`

English:
theorem Finite.bddBelow_range
  given: [IsCodirectedOrder α] (f : ι -> α)
  statement: BddBelow (Set.range f)
  proof: by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

中文:
定理 有限.bddBelow_range
  条件: [IsCodirectedOrder α] (f : ι -> α)
  结论: BddBelow (集合.range f)
  证明: by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

Depends on / 依赖: Finite, Finite.exists_ge, exists_ge
-/
theorem Finite.bddBelow_range [IsCodirectedOrder α] (f : ι -> α) : BddBelow (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

end DirectedOrders

section
variable {ι : Sort*} {α : Type*} [CompleteLattice α] {s : Set α} {a : α} {f : ι -> α}

/--
lemma `le_iSup_iff_of_directed` / 引理 `le_iSup_iff_of_directed`

English:
lemma le_iSup_iff_of_directed
  given: [Nonempty ι] [Finite ι] (hf : Directed (· <= ·) f)
  proof: by obtain ⟨i, hi⟩ := hf.finite_le id; exact ⟨i, ha.trans iSup_le hi⟩
  mpr := by rintro ⟨i, hai⟩; exact le_iSup_of_le i hai

中文:
引理 le_iSup_iff_of_directed
  条件: [非空 ι] [有限 ι] (hf : Directed (· <= ·) f)
  证明: by obtain ⟨i, hi⟩ := hf.finite_le id; exact ⟨i, ha.trans iSup_le hi⟩
  mpr := by rintro ⟨i, hai⟩; exact le_iSup_of_le i hai

Depends on / 依赖: finite_le, ha.trans, hf.finite_le, iSup_le, le_iSup_of_le
-/
lemma le_iSup_iff_of_directed [Nonempty ι] [Finite ι] (hf : Directed (· <= ·) f) :
    a <= ⨆ i, f i ↔ exists i, a <= f i where
mp ha := by obtain ⟨i, hi⟩ := hf.finite_le id; exact ⟨i, ha.trans iSup_le hi⟩
  mpr := by rintro ⟨i, hai⟩; exact le_iSup_of_le i hai

/--
lemma `le_sSup_iff_of_directedOn` / 引理 `le_sSup_iff_of_directedOn`

English:
lemma le_sSup_iff_of_directedOn
  given: (hs : s.Nonempty) (hs' : s.Finite) (hs'' : DirectedOn (· <= ·) s)
  proof: by
  have := hs.to_subtype
  have := hs'.to_subtype
  simp [sSup_eq_iSup', le_iSup_iff_of_directed hs''.directed_val]

中文:
引理 le_sSup_iff_of_directedOn
  条件: (hs : s.非空) (hs' : s.有限) (hs'' : DirectedOn (· <= ·) s)
  证明: by
  have := hs.to_subtype
  have := hs'.to_subtype
  simp [sSup_eq_iSup', le_iSup_iff_of_directed hs''.directed_val]

Depends on / 依赖: directed_val, hs.to_subtype, le_iSup_iff_of_directed, sSup_eq_iSup, to_subtype
-/
lemma le_sSup_iff_of_directedOn (hs : s.Nonempty) (hs' : s.Finite) (hs'' : DirectedOn (· <= ·) s) :
    a <= sSup s ↔ exists b in s, a <= b := by
  have := hs.to_subtype
  have := hs'.to_subtype
  simp [sSup_eq_iSup', le_iSup_iff_of_directed hs''.directed_val]

end

namespace Set
variable {ι : Sort*} {α : Type*} {S : Set (Set α)} {s : Set α} {f : ι -> Set α}

/--
lemma `subset_iUnion_iff_of_directed` / 引理 `subset_iUnion_iff_of_directed`

English:
lemma subset_iUnion_iff_of_directed
  given: [Nonempty ι] [Finite ι] (hf : Directed (· <= ·) f)
  proof: le_iSup_iff_of_directed hf

中文:
引理 subset_iUnion_iff_of_directed
  条件: [非空 ι] [有限 ι] (hf : Directed (· <= ·) f)
  证明: le_iSup_iff_of_directed hf

Depends on / 依赖: le_iSup_iff_of_directed
-/
lemma subset_iUnion_iff_of_directed [Nonempty ι] [Finite ι] (hf : Directed (· <= ·) f) :
    s subseteq ⋃ i, f i ↔ exists i, s subseteq f i := le_iSup_iff_of_directed hf

/--
lemma `subset_sUnion_iff_of_directed` / 引理 `subset_sUnion_iff_of_directed`

English:
lemma subset_sUnion_iff_of_directed
  statement: (hS : S.Nonempty) (hS' : S.Finite)
  proof: le_sSup_iff_of_directedOn hS hS' hS''

中文:
引理 subset_sUnion_iff_of_directed
  结论: (hS : S.非空) (hS' : S.有限)
  证明: le_sSup_iff_of_directedOn hS hS' hS''

Depends on / 依赖: le_sSup_iff_of_directedOn
-/
lemma subset_sUnion_iff_of_directed (hS : S.Nonempty) (hS' : S.Finite)
    (hS'' : DirectedOn (· <= ·) S) : s subseteq sSup S ↔ exists t in S, s subseteq t :=
  le_sSup_iff_of_directedOn hS hS' hS''

end Set

/-!
### Suprema and infima over finite types

We state simplified versions of `le_ciSup_if_le` and `ciSup_mono` when the indexing type
is finite. This avoids having to explicitly use `Finite.bddAbove_range`.

Similarly for `ciInf`.
-/

section ciSup

namespace Finite

section CCL

variable {α ι ι' : Type*} [Finite ι] [Finite ι'] [ConditionallyCompleteLattice α]

/--
lemma `le_ciSup_of_le` / 引理 `le_ciSup_of_le`

English:
lemma le_ciSup_of_le
  given: {a : α} {f : ι -> α} (c : ι) (h : a <= f c)
  statement: a <= iSup f
  proof: _root_.le_ciSup_of_le (bddAbove_range f) c h

中文:
引理 le_ciSup_of_le
  条件: {a : α} {f : ι -> α} (c : ι) (h : a <= f c)
  结论: a <= iSup f
  证明: _root_.le_ciSup_of_le (bddAbove_range f) c h

Depends on / 依赖: _root_, _root_.le_ciSup_of_le, bddAbove_range, le_ciSup_of_le
-/
lemma le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : a <= f c) : a <= iSup f :=
  _root_.le_ciSup_of_le (bddAbove_range f) c h

/--
lemma `ciInf_le_of_le` / 引理 `ciInf_le_of_le`

English:
lemma ciInf_le_of_le
  given: {a : α} {f : ι -> α} (c : ι) (h : f c <= a)
  statement: iInf f <= a
  proof: _root_.ciInf_le_of_le (bddBelow_range f) c h

中文:
引理 ciInf_le_of_le
  条件: {a : α} {f : ι -> α} (c : ι) (h : f c <= a)
  结论: iInf f <= a
  证明: _root_.ciInf_le_of_le (bddBelow_range f) c h

Depends on / 依赖: _root_, _root_.ciInf_le_of_le, bddBelow_range, ciInf_le_of_le
-/
lemma ciInf_le_of_le {a : α} {f : ι -> α} (c : ι) (h : f c <= a) : iInf f <= a :=
  _root_.ciInf_le_of_le (bddBelow_range f) c h

/--
lemma `ciSup_mono` / 引理 `ciSup_mono`

English:
lemma ciSup_mono
  given: {f g : ι -> α} (H : forall (x : ι), f x <= g x)
  statement: iSup f <= iSup g
  proof: _root_.ciSup_mono (bddAbove_range g) H

中文:
引理 ciSup_mono
  条件: {f g : ι -> α} (H : 对任意 (x : ι), f x <= g x)
  结论: iSup f <= iSup g
  证明: _root_.ciSup_mono (bddAbove_range g) H

Depends on / 依赖: _root_, _root_.ciSup_mono, bddAbove_range, ciSup_mono
-/
lemma ciSup_mono {f g : ι -> α} (H : forall (x : ι), f x <= g x) : iSup f <= iSup g :=
  _root_.ciSup_mono (bddAbove_range g) H

/--
lemma `ciInf_mono` / 引理 `ciInf_mono`

English:
lemma ciInf_mono
  given: {f g : ι -> α} (H : forall (x : ι), f x <= g x)
  statement: iInf f <= iInf g
  proof: _root_.ciInf_mono (bddBelow_range f) H

中文:
引理 ciInf_mono
  条件: {f g : ι -> α} (H : 对任意 (x : ι), f x <= g x)
  结论: iInf f <= iInf g
  证明: _root_.ciInf_mono (bddBelow_range f) H

Depends on / 依赖: _root_, _root_.ciInf_mono, bddBelow_range, ciInf_mono
-/
lemma ciInf_mono {f g : ι -> α} (H : forall (x : ι), f x <= g x) : iInf f <= iInf g :=
  _root_.ciInf_mono (bddBelow_range f) H

/--
lemma `le_ciSup` / 引理 `le_ciSup`

English:
lemma le_ciSup
  given: (f : ι -> α) (i : ι)
  statement: f i <= ⨆ j, f j
  proof: le_ciSup_of_le i le_rfl

中文:
引理 le_ciSup
  条件: (f : ι -> α) (i : ι)
  结论: f i <= ⨆ j, f j
  证明: le_ciSup_of_le i le_rfl

Depends on / 依赖: le_ciSup_of_le, le_rfl
-/
lemma le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j :=
  le_ciSup_of_le i le_rfl

/--
lemma `ciInf_le` / 引理 `ciInf_le`

English:
lemma ciInf_le
  given: (f : ι -> α) (i : ι)
  statement: ⨅ j, f j <= f i
  proof: le_ciSup (α := αᵒᵈ) f i

中文:
引理 ciInf_le
  条件: (f : ι -> α) (i : ι)
  结论: ⨅ j, f j <= f i
  证明: le_ciSup (α := αᵒᵈ) f i

Depends on / 依赖: le_ciSup
-/
lemma ciInf_le (f : ι -> α) (i : ι) : ⨅ j, f j <= f i :=
  le_ciSup (α := αᵒᵈ) f i

/--
lemma `ciSup_sup` / 引理 `ciSup_sup`

English:
lemma ciSup_sup
  given: [Nonempty ι] {f : ι -> α} {a : α}
  proof: by
refine le_antisymm (sup_le ?_ ?_) ciSup_le fun i => sup_le_sup_right (le_ciSup f i) a
  · exact ciSup_le fun i => le_ciSup_of_le i le_sup_left
  · exact le_ciSup_of_le (Classical.arbitrary ι) le_sup_right

中文:
引理 ciSup_sup
  条件: [非空 ι] {f : ι -> α} {a : α}
  证明: by
refine le_antisymm (sup_le ?_ ?_) ciSup_le fun i => sup_le_sup_right (le_ciSup f i) a
  · exact ciSup_le fun i => le_ciSup_of_le i le_sup_left
  · exact le_ciSup_of_le (Classical.arbitrary ι) le_sup_right

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, ciSup_le, le_antisymm, le_ciSup, le_ciSup_of_le, le_sup_left, le_sup_right, sup_le, sup_le_sup_right
-/
lemma ciSup_sup [Nonempty ι] {f : ι -> α} {a : α} :
    (⨆ i, f i) ⊔ a = ⨆ i, f i ⊔ a := by
refine le_antisymm (sup_le ?_ ?_) ciSup_le fun i => sup_le_sup_right (le_ciSup f i) a
  · exact ciSup_le fun i => le_ciSup_of_le i le_sup_left
  · exact le_ciSup_of_le (Classical.arbitrary ι) le_sup_right

/--
lemma `ciInf_inf` / 引理 `ciInf_inf`

English:
lemma ciInf_inf
  given: [Nonempty ι] {f : ι -> α} {a : α}
  proof: ciSup_sup (α := αᵒᵈ) ..

中文:
引理 ciInf_inf
  条件: [非空 ι] {f : ι -> α} {a : α}
  证明: ciSup_sup (α := αᵒᵈ) ..

Depends on / 依赖: ciSup_sup
-/
lemma ciInf_inf [Nonempty ι] {f : ι -> α} {a : α} :
    (⨅ i, f i) ⊓ a = ⨅ i, f i ⊓ a :=
  ciSup_sup (α := αᵒᵈ) ..

/--
lemma `ciSup_prod` / 引理 `ciSup_prod`

English:
lemma ciSup_prod
  given: (f : ι × ι' -> α)
  proof: _root_.ciSup_prod (bddAbove_range f)

中文:
引理 ciSup_prod
  条件: (f : ι × ι' -> α)
  证明: _root_.ciSup_prod (bddAbove_range f)

Depends on / 依赖: _root_, _root_.ciSup_prod, bddAbove_range, ciSup_prod
-/
lemma ciSup_prod (f : ι × ι' -> α) :
    ⨆ a, f a = ⨆ i, ⨆ i', f (i, i') :=
  _root_.ciSup_prod (bddAbove_range f)

/--
lemma `ciInf_prod` / 引理 `ciInf_prod`

English:
lemma ciInf_prod
  given: (f : ι × ι' -> α)
  proof: ciSup_prod (α := αᵒᵈ) f

中文:
引理 ciInf_prod
  条件: (f : ι × ι' -> α)
  证明: ciSup_prod (α := αᵒᵈ) f

Depends on / 依赖: ciSup_prod
-/
lemma ciInf_prod (f : ι × ι' -> α) :
    ⨅ a, f a = ⨅ i, ⨅ i', f (i, i') :=
  ciSup_prod (α := αᵒᵈ) f

end CCL

section CCLO

variable {α β ι : Type*} [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLattice β]
  [Finite ι] [Nonempty ι]

/--
lemma `map_iSup_of_monotoneOn` / 引理 `map_iSup_of_monotoneOn`

English:
lemma map_iSup_of_monotoneOn
  statement: {s : Set α} {f : ι -> α} {g : α -> β} (hg : MonotoneOn g s)
  proof: by
  obtain ⟨j, hj⟩ : exists j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite
  rw [← hj]
exact le_antisymm (le_ciSup_of_le j le_rfl)
    ciSup_le fun i => hg (hs i) (hs j) (hj ▸ le_ciSup f i)

中文:
引理 map_iSup_of_monotoneOn
  结论: {s : 集合 α} {f : ι -> α} {g : α -> β} (hg : MonotoneOn g s)
  证明: by
  obtain ⟨j, hj⟩ : exists j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite
  rw [← hj]
exact le_antisymm (le_ciSup_of_le j le_rfl)
    ciSup_le fun i => hg (hs i) (hs j) (hj ▸ le_ciSup f i)

Depends on / 依赖: Terminates, _of_not_terminates, _of_terminates, ciSup_le, exists_eq_ciSup_of_finite, le_antisymm, le_ciSup, le_ciSup_of_le, le_rfl, length, length_map, s.map, terminates_map_iff
-/
lemma map_iSup_of_monotoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : MonotoneOn g s)
    (hs : forall i, f i in s) :
    g (⨆ i, f i) = ⨆ i, g (f i) := by
  obtain ⟨j, hj⟩ : exists j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite
  rw [← hj]
exact le_antisymm (le_ciSup_of_le j le_rfl)
    ciSup_le fun i => hg (hs i) (hs j) (hj ▸ le_ciSup f i)

/--
lemma `map_iInf_of_monotoneOn` / 引理 `map_iInf_of_monotoneOn`

English:
lemma map_iInf_of_monotoneOn
  statement: {s : Set α} {f : ι -> α} {g : α -> β} (hg : MonotoneOn g s)
  proof: map_iSup_of_monotoneOn (α := αᵒᵈ) (β := βᵒᵈ) (fun _ hi _ hj h => hg hj hi h) hs

中文:
引理 map_iInf_of_monotoneOn
  结论: {s : 集合 α} {f : ι -> α} {g : α -> β} (hg : MonotoneOn g s)
  证明: map_iSup_of_monotoneOn (α := αᵒᵈ) (β := βᵒᵈ) (fun _ hi _ hj h => hg hj hi h) hs

Depends on / 依赖: map_iSup_of_monotoneOn
-/
lemma map_iInf_of_monotoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : MonotoneOn g s)
    (hs : forall i, f i in s) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (α := αᵒᵈ) (β := βᵒᵈ) (fun _ hi _ hj h => hg hj hi h) hs

/--
lemma `map_iSup_of_antitoneOn` / 引理 `map_iSup_of_antitoneOn`

English:
lemma map_iSup_of_antitoneOn
  statement: {s : Set α} {f : ι -> α} {g : α -> β} (hg : AntitoneOn g s)
  proof: map_iSup_of_monotoneOn (β := βᵒᵈ) hg hs

中文:
引理 map_iSup_of_antitoneOn
  结论: {s : 集合 α} {f : ι -> α} {g : α -> β} (hg : AntitoneOn g s)
  证明: map_iSup_of_monotoneOn (β := βᵒᵈ) hg hs

Depends on / 依赖: map_iSup_of_monotoneOn
-/
lemma map_iSup_of_antitoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : AntitoneOn g s)
    (hs : forall i, f i in s) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (β := βᵒᵈ) hg hs

/--
lemma `map_iInf_of_antitoneOn` / 引理 `map_iInf_of_antitoneOn`

English:
lemma map_iInf_of_antitoneOn
  statement: {s : Set α} {f : ι -> α} {g : α -> β} (hg : AntitoneOn g s)
  proof: map_iInf_of_monotoneOn (β := βᵒᵈ) hg hs

中文:
引理 map_iInf_of_antitoneOn
  结论: {s : 集合 α} {f : ι -> α} {g : α -> β} (hg : AntitoneOn g s)
  证明: map_iInf_of_monotoneOn (β := βᵒᵈ) hg hs

Depends on / 依赖: map_iInf_of_monotoneOn
-/
lemma map_iInf_of_antitoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : AntitoneOn g s)
    (hs : forall i, f i in s) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotoneOn (β := βᵒᵈ) hg hs

/--
lemma `map_iSup_of_monotone` / 引理 `map_iSup_of_monotone`

English:
lemma map_iSup_of_monotone
  given: (f : ι -> α) {g : α -> β} (hg : Monotone g)
  proof: map_iSup_of_monotoneOn (monotoneOn_univ.mpr hg) (fun i => Set.mem_univ (f i))

中文:
引理 map_iSup_of_monotone
  条件: (f : ι -> α) {g : α -> β} (hg : 递增 g)
  证明: map_iSup_of_monotoneOn (monotoneOn_univ.mpr hg) (fun i => Set.mem_univ (f i))

Depends on / 依赖: Set.mem_univ, map_iSup_of_monotoneOn, mem_univ, monotoneOn_univ, monotoneOn_univ.mpr
-/
lemma map_iSup_of_monotone (f : ι -> α) {g : α -> β} (hg : Monotone g) :
    g (⨆ i, f i) = ⨆ i, g (f i) :=
  map_iSup_of_monotoneOn (monotoneOn_univ.mpr hg) (fun i => Set.mem_univ (f i))

/--
lemma `map_iInf_of_monotone` / 引理 `map_iInf_of_monotone`

English:
lemma map_iInf_of_monotone
  given: (f : ι -> α) {g : α -> β} (hg : Monotone g)
  proof: map_iSup_of_monotone (α := αᵒᵈ) (β := βᵒᵈ) f fun _ _ h => hg h

中文:
引理 map_iInf_of_monotone
  条件: (f : ι -> α) {g : α -> β} (hg : 递增 g)
  证明: map_iSup_of_monotone (α := αᵒᵈ) (β := βᵒᵈ) f fun _ _ h => hg h

Depends on / 依赖: map_iSup_of_monotone
-/
lemma map_iInf_of_monotone (f : ι -> α) {g : α -> β} (hg : Monotone g) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (α := αᵒᵈ) (β := βᵒᵈ) f fun _ _ h => hg h

/--
lemma `map_iSup_of_antitone` / 引理 `map_iSup_of_antitone`

English:
lemma map_iSup_of_antitone
  given: (f : ι -> α) {g : α -> β} (hg : Antitone g)
  proof: map_iSup_of_monotone (β := βᵒᵈ) f hg

中文:
引理 map_iSup_of_antitone
  条件: (f : ι -> α) {g : α -> β} (hg : 递减 g)
  证明: map_iSup_of_monotone (β := βᵒᵈ) f hg

Depends on / 依赖: map_iSup_of_monotone
-/
lemma map_iSup_of_antitone (f : ι -> α) {g : α -> β} (hg : Antitone g) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (β := βᵒᵈ) f hg

/--
lemma `map_iInf_of_antitone` / 引理 `map_iInf_of_antitone`

English:
lemma map_iInf_of_antitone
  given: (f : ι -> α) {g : α -> β} (hg : Antitone g)
  proof: map_iInf_of_monotone (β := βᵒᵈ) f hg

中文:
引理 map_iInf_of_antitone
  条件: (f : ι -> α) {g : α -> β} (hg : 递减 g)
  证明: map_iInf_of_monotone (β := βᵒᵈ) f hg

Depends on / 依赖: map_iInf_of_monotone
-/
lemma map_iInf_of_antitone (f : ι -> α) {g : α -> β} (hg : Antitone g) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotone (β := βᵒᵈ) f hg

end CCLO

end Finite

end ciSup
