/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.LatticeIntervals

/-!
# Lattice structures on the type of nonnegative elements

-/

@[expose] public section
assert_not_exists Ring
assert_not_exists IsOrderedMonoid

open Set

variable {α : Type*}

namespace Nonneg

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [Preorder α] {a : α}
  body: inferInstanceAs OrderBot (Ici a)

中文:
实例 orderBot
  签名: [预序 α] {a : α}
  定义体: inferInstanceAs OrderBot (Ici a)

Depends on / 依赖: OrderBot
-/
instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a <= x } :=
inferInstanceAs OrderBot (Ici a)

/--
theorem `bot_eq` / 定理 `bot_eq`

English:
theorem bot_eq
  given: [Preorder α] {a : α}
  statement: (⊥ : { x : α // a <= x }) = ⟨a, le_rfl⟩
  proof: rfl

中文:
定理 bot_eq
  条件: [预序 α] {a : α}
  结论: (⊥ : { x : α // a <= x }) = ⟨a, le_rfl⟩
  证明: rfl
-/
theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a <= x }) = ⟨a, le_rfl⟩ :=
  rfl

/--
Instance `noMaxOrder` / 实例 `noMaxOrder`

English:
instance noMaxOrder
  signature: [PartialOrder α] [NoMaxOrder α] {a : α}
  body: inferInstanceAs NoMaxOrder (Ici a)

中文:
实例 noMaxOrder
  签名: [偏序 α] [NoMax序 α] {a : α}
  定义体: inferInstanceAs NoMaxOrder (Ici a)

Depends on / 依赖: NoMaxOrder
-/
instance noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a <= x } :=
inferInstanceAs NoMaxOrder (Ici a)

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α] {a : α}
  body: inferInstanceAs SemilatticeSup (Ici a)

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α] {a : α}
  定义体: inferInstanceAs SemilatticeSup (Ici a)

Depends on / 依赖: SemilatticeSup
-/
instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a <= x } :=
inferInstanceAs SemilatticeSup (Ici a)

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α] {a : α}
  body: inferInstanceAs SemilatticeInf (Ici a)

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α] {a : α}
  定义体: inferInstanceAs SemilatticeInf (Ici a)

Depends on / 依赖: SemilatticeInf
-/
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a <= x } :=
inferInstanceAs SemilatticeInf (Ici a)

/--
Instance `distribLattice` / 实例 `distribLattice`

English:
instance distribLattice
  signature: [DistribLattice α] {a : α}
  body: inferInstanceAs DistribLattice (Ici a)

中文:
实例 distribLattice
  签名: [Distrib格 α] {a : α}
  定义体: inferInstanceAs DistribLattice (Ici a)

Depends on / 依赖: DistribLattice
-/
instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a <= x } :=
inferInstanceAs DistribLattice (Ici a)

/--
Instance `instDenselyOrdered` / 实例 `instDenselyOrdered`

English:
instance instDenselyOrdered
  signature: [Preorder α] [DenselyOrdered α] {a : α}
  body: inferInstanceAs DenselyOrdered (Ici a)

中文:
实例 instDenselyOrdered
  签名: [预序 α] [稠密序 α] {a : α}
  定义体: inferInstanceAs DenselyOrdered (Ici a)

Depends on / 依赖: DenselyOrdered
-/
instance instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a <= x } :=
inferInstanceAs DenselyOrdered (Ici a)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
  body: -- TODO: missing `Inhabited (Ici a)` instance
  haveI : Inhabited (Ici a) := ⟨a, le_rfl⟩
inferInstanceAs ConditionallyCompleteLinearOrder (Ici a)

中文:
缩写 noncomputable
  签名: abbrev conditionallyCompleteLinearOrder [条件完备线性序 α]
  定义体: -- TODO: missing `Inhabited (Ici a)` instance
  haveI : Inhabited (Ici a) := ⟨a, le_rfl⟩
inferInstanceAs ConditionallyCompleteLinearOrder (Ici a)
-/
protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a <= x } :=
  -- TODO: missing `Inhabited (Ici a)` instance
  haveI : Inhabited (Ici a) := ⟨a, le_rfl⟩
inferInstanceAs ConditionallyCompleteLinearOrder (Ici a)


set_option backward.isDefEq.respectTransparency false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev conditionallyCompleteLinearOrderBot
  body: { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a]; rw [le_rfl⟩⟩]; simp [bot_eq] }

中文:
缩写 noncomputable
  签名: abbrev conditionallyCompleteLinearOrderBot
  定义体: { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a]; rw [le_rfl⟩⟩]; simp [bot_eq] }
-/
protected noncomputable abbrev conditionallyCompleteLinearOrderBot
    [ConditionallyCompleteLinearOrder α] (a : α) :
    ConditionallyCompleteLinearOrderBot { x : α // a <= x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a]; rw [le_rfl⟩⟩]; simp [bot_eq] }

end Nonneg
