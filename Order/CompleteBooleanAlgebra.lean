/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.Order.Directed
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Frames, completely distributive lattices and complete Boolean algebras

In this file we define and provide API for (co)frames, completely distributive lattices and
complete Boolean algebras.

We distinguish two different distributivity properties:
1. `inf_iSup_eq : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i` (finite `⊓` distributes over infinite `⨆`).
  This is required by `Frame`, `CompleteDistribLattice`, and `CompleteBooleanAlgebra`
  (`Coframe`, etc., require the dual property).
2. `iInf_iSup_eq : (⨅ i, ⨆ j, f i j) = ⨆ s, ⨅ i, f i (s i)`
  (infinite `⨅` distributes over infinite `⨆`).
  This stronger property is called "completely distributive",
  and is required by `CompletelyDistribLattice` and `CompleteAtomicBooleanAlgebra`.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Complete distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompletelyDistribLattice`: Completely distributive lattices: A complete lattice whose
  `⨅` and `⨆` satisfy `iInf_iSup_eq`.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompleteAtomicBooleanAlgebra`: Complete atomic Boolean algebra:
  A complete Boolean algebra which is additionally completely distributive.
  (This implies that it's (co)atom(ist)ic.)

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

@[expose] public section

open Function Set

universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

/-- Structure containing the minimal axioms required to check that an order is a frame. Do NOT use,
except for implementing `Order.Frame` via `Order.Frame.ofMinimalAxioms`.

This structure omits the `himp`, `compl` fields, which can be recovered using
`Order.Frame.ofMinimalAxioms`. -/
/-
**Order.Frame.MinimalAxioms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order.Frame`。
形式化陈述：(α : Type u) → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the minimal axioms required to check that an order is a fra
me. Do NOT use,
except for implementing `Order.Frame` via `Order.Frame.ofMinimalAxioms`.

This structure omits the `himp`, `compl` fields, which can be recovered using
`Order.Frame.ofMinimalAxioms`.
-/
structure Order.Frame.MinimalAxioms (α : Type u) [CompleteLattice α] where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

/-- Structure containing the minimal axioms required to check that an order is a coframe. Do NOT
use, except for implementing `Order.Coframe` via `Order.Coframe.ofMinimalAxioms`.

This structure omits the `sdiff`, `hnot` fields, which can be recovered using
`Order.Coframe.ofMinimalAxioms`. -/
@[to_dual Frame.MinimalAxioms]
/-
**Order.Coframe.MinimalAxioms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order.Coframe`。
形式化陈述：(α : Type u) → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the minimal axioms required to check that an order is a cof
rame. Do NOT
use, except for implementing `Order.Coframe` via `Order.Coframe.ofMinimalAxioms`
.

This structure omits the `sdiff`, `hnot` fields, which can be recovered using
`Order.Coframe.ofMinimalAxioms`.
-/
structure Order.Coframe.MinimalAxioms (α : Type u) [CompleteLattice α] where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
/-
**Order.Frame** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distribut
es over `⨆`.
-/
class Order.Frame (α : Type*) extends CompleteLattice α, HeytingAlgebra α where

set_option linter.translate.warnInvalid false in
/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
@[to_dual]
/-
**Order.Coframe** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a com
plete lattice
whose `⊔` distributes over `⨅`.
-/
class Order.Coframe (α : Type*) extends CompleteLattice α, CoheytingAlgebra α where

open Order

/-- `⊓` distributes over `⨆`. -/
@[to_dual /-- `⊔` distributes over `⨅`. -/]
/-
**inf_sSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ b in s, a ⊓ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `gc_inf_himp`：gc_inf_himp : GaloisConnection (a ⊓ ·) (a ⇨ ·)

--- 原说明 ---
`⊓` distributes over `⨆`.
-/
theorem inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  gc_inf_himp.l_sSup

/-- Structure containing the minimal axioms required to check that an order is a complete
distributive lattice. Do NOT use, except for implementing `CompleteDistribLattice` via
`CompleteDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be recovered using
`CompleteDistribLattice.ofMinimalAxioms`. -/
/-
**CompleteDistribLattice.MinimalAxioms** 是 Mathlib 中的一个归纳类型，位于命名空间 `CompleteDist
ribLattice`。
形式化陈述：(α : Type u) → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the minimal axioms required to check that an order is a com
plete
distributive lattice. Do NOT use, except for implementing `CompleteDistribLattic
e` via
`CompleteDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be r
ecovered using
`CompleteDistribLattice.ofMinimalAxioms`.
-/
structure CompleteDistribLattice.MinimalAxioms (α : Type u) [CompleteLattice α] extends
    toFrame : Frame.MinimalAxioms α, toCoframe : Coframe.MinimalAxioms α where

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Frame`. -/
add_decl_doc CompleteDistribLattice.MinimalAxioms.toFrame

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Coframe`. -/
add_decl_doc CompleteDistribLattice.MinimalAxioms.toCoframe

/-- A complete distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
/-
**CompleteDistribLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete distributive lattice is a complete lattice whose `⊔` and `⊓` respecti
vely
distribute over `⨅` and `⨆`.
-/
class CompleteDistribLattice (α : Type*) extends Frame α, Coframe α, BiheytingAlgebra α

attribute [to_dual existing] CompleteDistribLattice.toFrame

/-- Structure containing the minimal axioms required to check that an order is a completely
distributive. Do NOT use, except for implementing `CompletelyDistribLattice` via
`CompletelyDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be recovered using
`CompletelyDistribLattice.ofMinimalAxioms`. -/
/-
**CompletelyDistribLattice.MinimalAxioms** 是 Mathlib 中的一个归纳类型，位于命名空间 `Completely
DistribLattice`。
形式化陈述：(α : Type u) → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure containing the minimal axioms required to check that an order is a com
pletely
distributive. Do NOT use, except for implementing `CompletelyDistribLattice` via
`CompletelyDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be r
ecovered using
`CompletelyDistribLattice.ofMinimalAxioms`.
-/
structure CompletelyDistribLattice.MinimalAxioms (α : Type u) [CompleteLattice α] where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

/-- A completely distributive lattice is a complete lattice whose `⨅` and `⨆`
distribute over each other. -/
/-
**CompletelyDistribLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A completely distributive lattice is a complete lattice whose `⨅` and `⨆`
distribute over each other.
-/
class CompletelyDistribLattice (α : Type u) extends CompleteLattice α, BiheytingAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)
/-
**le_iInf_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iInf_iSup [CompleteLattice α] {f : forall a, κ a -> α} : (⨆ g : forall 
a, κ a, ⨅ a, f a (g a)) <= ⨅ a, ⨆ b, f a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem le_iInf_iSup [CompleteLattice α] {f : ∀ a, κ a → α} :
    (⨆ g : ∀ a, κ a, ⨅ a, f a (g a)) ≤ ⨅ a, ⨆ b, f a b :=
  iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)
/-
**iSup_iInf_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_iInf_le [CompleteLattice α] {f : forall a, κ a -> α} : ⨆ a, ⨅ b, f a 
b <= ⨅ g : forall a, κ a, ⨆ a, f a (g a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf_iSup`：le_iInf_iSup [CompleteLattice α] {f : forall a, κ a -> α} 
: (⨆ g : forall a, κ a, ⨅ a, f a (g a)) <= ⨅ a, ⨆ b, f a b
-/
lemma iSup_iInf_le [CompleteLattice α] {f : ∀ a, κ a → α} :
    ⨆ a, ⨅ b, f a b ≤ ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  le_iInf_iSup (α := αᵒᵈ)

namespace Order.Frame.MinimalAxioms
variable (s : Set α) (a b : α)

section
variable [CompleteLattice α] (minAx : MinimalAxioms α)
include minAx

@[to_dual]
/-
**Order.Frame.MinimalAxioms.inf_sSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order.Frame.M
inimalAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma inf_sSup_eq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  le_antisymm (minAx.inf_sSup_le_iSup_inf _ _) iSup_inf_le_inf_sSup

@[to_dual]
/-
**Order.Frame.MinimalAxioms.sSup_inf_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order.Frame.M
inimalAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using inf_sSup_eq s b minAx

@[to_dual]
/-
**Order.Frame.MinimalAxioms.iSup_inf_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order.Frame.M
inimalAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, minAx.sSup_inf_eq, iSup_range]

@[to_dual]
/-
**Order.Frame.MinimalAxioms.inf_iSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `Order.Frame.M
inimalAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

@[to_dual]
/-
**Order.Frame.MinimalAxioms.inf_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Order.Frame.Mini
malAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) :
    (a ⊓ ⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, a ⊓ f i j := by
  simp only [minAx.inf_iSup_eq]

end

/-- The `Order.Frame.MinimalAxioms` element corresponding to a frame. -/
@[to_dual /-- The `Order.Coframe.MinimalAxioms` element corresponding to a frame. -/]
/-
**Order.Frame.MinimalAxioms.of** 是 Mathlib 中的一个定理，位于命名空间 `Order.Frame.MinimalAxi
oms`。
形式化陈述：of [Frame α] : MinimalAxioms α where __
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_sSup_eq`：inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ 
b in s, a ⊓ b

--- 原说明 ---
The `Order.Frame.MinimalAxioms` element corresponding to a frame.
-/
theorem of [Frame α] : MinimalAxioms α where
  __ := ‹Frame α›
  inf_sSup_le_iSup_inf a s := _root_.inf_sSup_eq.le

end MinimalAxioms

/-- Construct a frame instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}` and `aᶜ := a ⇨ ⊥`. -/
-- See note [reducible non-instances]
/-
**Order.Frame.ofMinimalAxioms** 是 Mathlib 中的一个定义，位于命名空间 `Order.Frame`。
形式化陈述：{α : Type u} → [inst : CompleteLattice α] → Order.Frame.MinimalAxioms α → 
Order.Frame α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) : Frame α where
  compl a := sSup {c | c ⊓ a ≤ ⊥}
  himp a b := sSup {c | c ⊓ a ≤ b}
  le_himp_iff _ b c :=
    ⟨fun h ↦ (inf_le_inf_right _ h).trans (by simp [minAx.sSup_inf_eq]), fun h ↦ le_sSup h⟩
  himp_bot _ := rfl

end Order.Frame

namespace Order.Coframe

/-- Construct a coframe instance using the minimal amount of work needed.

This sets `a \ b := sInf {c | a ≤ b ⊔ c}` and `￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
@[to_dual existing]
/-
**Order.Coframe.ofMinimalAxioms** 是 Mathlib 中的一个定义，位于命名空间 `Order.Coframe`。
形式化陈述：{α : Type u} → [inst : CompleteLattice α] → Order.Coframe.MinimalAxioms α 
→ Order.Coframe α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) : Coframe α where
  hnot a := sInf {c | ⊤ ≤ a ⊔ c}
  sdiff a b := sInf {c | a ≤ b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h ↦ (sup_le_sup_left h _).trans' (by simp [minAx.sup_sInf_eq]), fun h ↦ sInf_le h⟩
  top_sdiff _ := rfl

end Order.Coframe

namespace CompleteDistribLattice.MinimalAxioms

/-- The `CompleteDistribLattice.MinimalAxioms` element corresponding to a complete distrib lattice.
-/
/-
**CompleteDistribLattice.MinimalAxioms.of** 是 Mathlib 中的一个定理，位于命名空间 `CompleteDis
tribLattice.MinimalAxioms`。
形式化陈述：∀ {α : Type u} [inst : CompleteDistribLattice α], CompleteDistribLattice.M
inimalAxioms α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_sSup_eq`：inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ 
b in s, a ⊓ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `sup_sInf_eq`：∀ {α : Type u} [inst : Order.Coframe α] {s : Set α} {a : α}
, a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b

--- 原说明 ---
The `CompleteDistribLattice.MinimalAxioms` element corresponding to a complete d
istrib lattice.
-/
theorem of [CompleteDistribLattice α] : MinimalAxioms α where
  __ := ‹CompleteDistribLattice α›
  inf_sSup_le_iSup_inf a s := inf_sSup_eq.le
  iInf_sup_le_sup_sInf a s := sup_sInf_eq.ge

variable [CompleteLattice α] (minAx : MinimalAxioms α)

end MinimalAxioms

/-- Construct a complete distrib lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
/-
**CompleteDistribLattice.ofMinimalAxioms** 是 Mathlib 中的一个定义，位于命名空间 `CompleteDist
ribLattice`。
形式化陈述：{α : Type u} → [inst : CompleteLattice α] → CompleteDistribLattice.Minimal
Axioms α → CompleteDistribLattice α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteDistribLattice.MinimalAxioms.toFrame`：∀ {α : Type u} [inst : Com
pleteLattice α], CompleteDistribLattice.MinimalAxioms α → Order.Frame.MinimalAxi
oms α
· 使用定理 `CompleteDistribLattice.MinimalAxioms.toCoframe`：∀ {α : Type u} [inst : C
ompleteLattice α], CompleteDistribLattice.MinimalAxioms α → Order.Coframe.Minima
lAxioms α
· 使用定理 `Order.Coframe.sdiff_le_iff`：∀ {α : Type u_1} [self : Order.Coframe α] (a
 b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `Order.Coframe.top_sdiff`：∀ {α : Type u_1} [self : Order.Coframe α] (a : 
α), ⊤ \ a = ￢a
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompleteDistribLattice α where
  __ := Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

end CompleteDistribLattice

namespace CompletelyDistribLattice.MinimalAxioms

/-
**CompletelyDistribLattice.MinimalAxioms.iInf_iSup_eq'** 是 Mathlib 中的一个引理，位于命名空间
 `CompletelyDistribLattice.MinimalAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iInf_iSup_eq' [CompleteLattice α] (minAx : MinimalAxioms α) (f : ∀ a, κ a → α) :
    ⨅ i, ⨆ j, f i j = ⨆ g : ∀ i, κ i, ⨅ i, f i (g i) := by
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := minAx.iInf_iSup_eq _
    _ ≤ _ := iSup_le fun g => by
      refine le_trans ?_ <| le_iSup _ fun a => Classical.choose (g ⟨_, a, rfl⟩).2
      refine le_iInf fun a => le_trans (iInf_le _ ⟨range (f a), a, rfl⟩) ?_
      rw [← Classical.choose_spec (g ⟨_, a, rfl⟩).2]

@[to_dual existing iInf_iSup_eq']
/-
**CompletelyDistribLattice.MinimalAxioms.iSup_iInf_eq** 是 Mathlib 中的一个引理，位于命名空间 
`CompletelyDistribLattice.MinimalAxioms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iSup_iInf_eq [CompleteLattice α] (minAx : MinimalAxioms α) (f : ∀ i, κ i → α) :
    ⨆ i, ⨅ j, f i j = ⨅ g : ∀ i, κ i, ⨆ i, f i (g i) := by
  refine le_antisymm iSup_iInf_le ?_
  rw [minAx.iInf_iSup_eq']
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : ∃ a, ∀ b, ∃ f, ∃ h : a = g f, h ▸ b = f (g f) := by
    by_contra! h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a)
  refine le_iInf fun b => ?_
  obtain ⟨h, rfl, rfl⟩ := ha b
  exact iInf_le _ _

/-- Turn minimal axioms for `CompletelyDistribLattice` into minimal axioms for
`CompleteDistribLattice`. -/
/-
**CompletelyDistribLattice.MinimalAxioms.toCompleteDistribLattice** 是 Mathlib 中的
一个定理，位于命名空间 `CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：∀ {α : Type u} [inst : CompleteLattice α],   CompletelyDistribLattice.Mini
malAxioms α → CompleteDistribLattice.MinimalAxioms α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `iInf_ulift`：∀ {α : Type u_1} {ι : Type u_8} [inst : InfSet α] (f : ULift
.{u_9, u_8} ι → α), ⨅ i, f i = ⨅ i, f { down := i }
· 使用定理 `iInf_bool_eq`：∀ {α : Type u_1} [inst : CompleteLattice α] {f : Bool → α}
, ⨅ b, f b = f true ⊓ f false
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iSup_unique`：iSup_unique [Unique ι] (f : ι -> α) : ⨆ i, f i = f default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CompletelyDistribLattice.MinimalAxioms.iInf_iSup_eq`：∀ {α : Type u} [ins
t : CompleteLattice α],   CompletelyDistribLattice.MinimalAxioms α →     ∀ {ι : 
Type u} {κ : ι → Type u} (f : (a : ι) → κ…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `_private.Mathlib.Order.CompleteBooleanAlgebra.0.CompletelyDistribLattice
.MinimalAxioms.iSup_iInf_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst
 : CompleteLattice α],   CompletelyDistribLattice.MinimalAxioms α → ∀ (f : (i : 
ι) → κ i …
· 使用定理 `iSup_ulift`：∀ {α : Type u_1} {ι : Type u_8} [inst : SupSet α] (f : ULift
.{u_9, u_8} ι → α), ⨆ i, f i = ⨆ i, f { down := i }
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
· 使用定理 `iInf_unique`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
[inst_1 : Unique ι] (f : ι → α), ⨅ i, f i = f default
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a

--- 原说明 ---
Turn minimal axioms for `CompletelyDistribLattice` into minimal axioms for
`CompleteDistribLattice`.
-/
theorem toCompleteDistribLattice [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompleteDistribLattice.MinimalAxioms α where
  inf_sSup_le_iSup_inf a s := by
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ ≤ _ := by
        simp only [minAx.iInf_iSup_eq, iInf_ulift, iInf_bool_eq, iSup_le_iff]
        exact fun x ↦ le_biSup _ (x (.up false)).2
  iInf_sup_le_sup_sInf a s := by
    calc
      _ ≤ ⨆ i : ULift.{u} Bool, ⨅ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by
        simp only [minAx.iSup_iInf_eq, iSup_ulift, iSup_bool_eq, le_iInf_iff]
        exact fun x ↦ biInf_le _ (x (.up false)).2
      _ = _ := by simp [sInf_eq_iInf', iInf_unique, iSup_bool_eq]

/-- The `CompletelyDistribLattice.MinimalAxioms` element corresponding to a frame. -/
/-
**CompletelyDistribLattice.MinimalAxioms.of** 是 Mathlib 中的一个定理，位于命名空间 `Completel
yDistribLattice.MinimalAxioms`。
形式化陈述：∀ {α : Type u} [inst : CompletelyDistribLattice α], CompletelyDistribLatti
ce.MinimalAxioms α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyDistribLattice.iInf_iSup_eq`：∀ {α : Type u} [self : Completely
DistribLattice α] {ι : Type u} {κ : ι → Type u} (f : (a : ι) → κ a → α),   ⨅ a, 
⨆ b, f a b = ⨆ g, ⨅ a, f a …

--- 原说明 ---
The `CompletelyDistribLattice.MinimalAxioms` element corresponding to a frame.
-/
theorem of [CompletelyDistribLattice α] : MinimalAxioms α := { ‹CompletelyDistribLattice α› with }

end MinimalAxioms

/-- Construct a completely distributive lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
/-
**CompletelyDistribLattice.ofMinimalAxioms** 是 Mathlib 中的一个定义，位于命名空间 `Completely
DistribLattice`。
形式化陈述：{α : Type u} → [inst : CompleteLattice α] → CompletelyDistribLattice.Minim
alAxioms α → CompletelyDistribLattice α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompletelyDistribLattice α := fast_instance%
  { CompleteDistribLattice.ofMinimalAxioms minAx.toCompleteDistribLattice, minAx with }

end CompletelyDistribLattice

@[to_dual]
/-
**iInf_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : CompletelyDistribLat
tice α] {f : (a : ι) → κ a → α},   ⨅ a, ⨆ b, f a b = ⨆ g, ⨅ a, f a (g a)
参数：a : ι；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.CompleteBooleanAlgebra.0.CompletelyDistribLattice
.MinimalAxioms.iInf_iSup_eq'`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [ins
t : CompleteLattice α],   CompletelyDistribLattice.MinimalAxioms α → ∀ (f : (a :
 ι) → κ a …
· 使用定理 `CompletelyDistribLattice.MinimalAxioms.of`：∀ {α : Type u} [inst : Comple
telyDistribLattice α], CompletelyDistribLattice.MinimalAxioms α
-/
theorem iInf_iSup_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a) :=
  CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq' _
/-
**biSup_iInter_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompletelyDistribLattice α] {ι : Type u_1} {κ : Typ
e u_2} [hκ : Nonempty κ] {f : ι → α},   Pairwise (Function.onFun Disjoint f) → ∀
 (s : κ → Set ι), ⨆ i ∈ ⋂ j, s j, f i = ⨅ j, ⨆ i ∈ s j, f i
参数：Function.onFun Disjoint f；s : κ → Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_iSup_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : Comp
letelyDistribLattice α] {f : (a : ι) → κ a → α},   ⨅ a, ⨆ b, f a b = ⨆ g, ⨅ a, f
 a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem biSup_iInter_of_pairwise_disjoint [CompletelyDistribLattice α] {ι κ : Type*}
    [hκ : Nonempty κ] {f : ι → α} (h : Pairwise (Disjoint on f)) (s : κ → Set ι) :
    (⨆ i ∈ (⋂ j, s j), f i) = ⨅ j, (⨆ i ∈ s j, f i) := by
  rcases hκ with ⟨j⟩
  simp_rw [iInf_iSup_eq, mem_iInter]
  refine le_antisymm
    (iSup₂_le fun i hi ↦ le_iSup₂_of_le (fun _ ↦ i) hi (le_iInf fun _ ↦ le_rfl))
    (iSup₂_le fun I hI ↦ ?_)
  by_cases! H : ∀ k, I k = I j
  · exact le_iSup₂_of_le (I j) (fun k ↦ (H k) ▸ (hI k)) (iInf_le _ _)
  · rcases H with ⟨k, hk⟩
    calc ⨅ l, f (I l)
    _ ≤ f (I k) ⊓ f (I j) := le_inf (iInf_le _ _) (iInf_le _ _)
    _ = ⊥ := (h hk).eq_bot
    _ ≤ _ := bot_le
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompletelyDistribLattice.toCompleteDistribLattice
    [CompletelyDistribLattice α] : CompleteDistribLattice α where
  __ := ‹CompletelyDistribLattice α›

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteLinearOrder.toCompletelyDistribLattice [CompleteLinearOrder α] :
    CompletelyDistribLattice α where
  __ := ‹CompleteLinearOrder α›
  iInf_iSup_eq {α β} g := by
    let lhs := ⨅ a, ⨆ b, g a b
    let rhs := ⨆ h : ∀ a, β a, ⨅ a, g a (h a)
    suffices lhs ≤ rhs from le_antisymm this le_iInf_iSup
    if h : ∃ x, rhs < x ∧ x < lhs then
      rcases h with ⟨x, hr, hl⟩
      suffices rhs ≥ x from nomatch not_lt.2 this hr
      have : ∀ a, ∃ b, x < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_not_ge fun h =>
            lt_irrefl x (lt_of_lt_of_le hl (le_trans (iInf_le _ a) h))
      choose f hf using this
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => le_of_lt (hf a)
    else
      refine le_of_not_gt fun hrl : rhs < lhs => not_le_of_gt hrl ?_
      replace h : ∀ x, x ≤ rhs ∨ lhs ≤ x := by
        simpa only [not_exists, not_and_or, not_or, not_lt] using h
      have : ∀ a, ∃ b, rhs < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_lt_of_le hrl (iInf_le _ a)
      choose f hf using this
      have : ∀ a, lhs ≤ g a (f a) := fun a =>
        (h (g a (f a))).resolve_left (by simpa using hf a)
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => this _

section Frame

variable [Frame α] {s t : Set α} {a b c d : α}

/-
**OrderDual.instCoframe** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAxioms.Com
pleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：OrderDual.instCoframe : Coframe αᵒᵈ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instCoframe : Coframe αᵒᵈ where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual]
/-
**sSup_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {s : Set α} {b : α}, sSup s ⊓ b = ⨆ 
a ∈ s, a ⊓ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `inf_sSup_eq`：inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ 
b in s, a ⊓ b
-/
theorem sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

@[to_dual]
/-
**iSup_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (f : ι → α) (a : α), (⨆
 i, f i) ⊓ a = ⨆ i, f i ⊓ a
参数：f : ι → α；a : α；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `sSup_inf_eq`：∀ {α : Type u} [inst : Order.Frame α] {s : Set α} {b : α}, 
sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]

@[to_dual]
/-
**inf_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (a : α) (f : ι → α), a 
⊓ ⨆ i, f i = ⨆ i, a ⊓ f i
参数：a : α；f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_inf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (f : ι →
 α) (a : α), (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
-/
theorem inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) :
    (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a := by
  simp only [iSup_inf_eq]

@[to_dual]
/-
**inf_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) :
    (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j := by
  simp only [inf_iSup_eq]

@[to_dual iSup_sdiff_eq]
/-
**himp_iInf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a : α} {f : ι → α}, a 
⇨ ⨅ x, f x = ⨅ x, a ⇨ f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem himp_iInf_eq {f : ι → α} : a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x :=
  eq_of_forall_le_iff fun b => by simp

@[to_dual sdiff_iInf_eq]
/-
**iSup_himp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a : α} {f : ι → α}, (⨆
 x, f x) ⇨ a = ⨅ x, f x ⇨ a
参数：⨆ x, f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_iSup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (a : α) 
(f : ι → α), a ⊓ ⨆ i, f i = ⨆ i, a ⊓ f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_himp_eq {f : ι → α} : (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a :=
  eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

@[deprecated (since := "2026-07-30")] alias sdiff_iSup_eq := sdiff_iInf_eq

@[to_dual]
/-
**iSup_inf_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {ι' : Type u_2} {f : 
ι → α} {g : ι' → α},   (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ i, f i.1 ⊓ g i.2
参数：⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_inf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (f : ι →
 α) (a : α), (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inf_iSup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (a : α) 
(f : ι → α), a ⊓ ⨆ i, f i = ⨆ i, a ⊓ f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_inf_iSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

@[to_dual]
/-
**biSup_inf_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {ι' : Type u_2} {f : 
ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'},   (⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j = 
⨆ p ∈ s ×ˢ t, f p.1 ⊓ g p.2
参数：⨆ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `iSup_inf_iSup`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {ι' 
: Type u_2} {f : ι → α} {g : ι' → α},   (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ i, f i.1 ⊓ g i
.2
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem biSup_inf_biSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

@[to_dual]
/-
**sSup_inf_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {s t : Set α}, sSup s ⊓ sSup t = ⨆ p
 ∈ s ×ˢ t, p.1 ⊓ p.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `biSup_inf_biSup`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {ι
' : Type u_2} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'},   (⨆ i ∈ s, f i
) ⊓ ⨆…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

@[to_dual]
/-
**biSup_inter_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {f : ι → α},   Pairwi
se (Function.onFun Disjoint f) → ∀ (s t : Set ι), ⨆ i ∈ s ∩ t, f i = (⨆ i ∈ s, f
 i) ⊓ ⨆ i ∈ t, f i
参数：Function.onFun Disjoint f；s t : Set ι；⨆ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `biSup_inf_biSup`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {ι
' : Type u_2} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'},   (⨆ i ∈ s, f i
) ⊓ ⨆…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem biSup_inter_of_pairwise_disjoint {ι : Type*} {f : ι → α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⨆ i ∈ (s ∩ t), f i) = (⨆ i ∈ s, f i) ⊓ (⨆ i ∈ t, f i) := by
  rw [biSup_inf_biSup]
  refine le_antisymm
    (iSup₂_le fun i ⟨his, hit⟩ ↦ le_iSup₂_of_le ⟨i, i⟩ ⟨his, hit⟩ (le_inf le_rfl le_rfl))
    (iSup₂_le fun ⟨i, j⟩ ⟨his, hjs⟩ ↦ ?_)
  by_cases hij : i = j
  · exact le_iSup₂_of_le i ⟨his, hij ▸ hjs⟩ inf_le_left
  · simp [h hij |>.eq_bot]

@[to_dual]
/-
**iSup_disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a : α} {f : ι → α},   
Disjoint (⨆ i, f i) a ↔ ∀ (i : ι), Disjoint (f i) a
参数：⨆ i, f i；i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_inf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (f : ι →
 α) (a : α), (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

@[to_dual]
/-
**disjoint_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a : α} {f : ι → α},   
Disjoint a (⨆ i, f i) ↔ ∀ (i : ι), Disjoint a (f i)
参数：⨆ i, f i；i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_disjoint_iff`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] {a
 : α} {f : ι → α},   Disjoint (⨆ i, f i) a ↔ ∀ (i : ι), Disjoint (f i) a
-/
theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

@[to_dual]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]

@[to_dual]
/-
**disjoint_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]

@[to_dual]
/-
**sSup_disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {a : α} {s : Set α}, Disjoint (sSup 
s) a ↔ ∀ b ∈ s, Disjoint b a
参数：sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sSup_inf_eq`：∀ {α : Type u} [inst : Order.Frame α] {s : Set α} {b : α}, 
sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

@[to_dual]
/-
**disjoint_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {a : α} {s : Set α}, Disjoint a (sSu
p s) ↔ ∀ b ∈ s, Disjoint a b
参数：sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sSup_disjoint_iff`：∀ {α : Type u} [inst : Order.Frame α] {a : α} {s : Se
t α}, Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a
-/
theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

@[to_dual]
/-
**iSup_inf_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} [inst_1 : Preorder ι]
 [IsDirectedOrder ι] {f g : ι → α},   Monotone f → Monotone g → ⨆ i, f i ⊓ g i =
 (⨆ i, f i) ⊓ ⨆ i, g i
参数：⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_iSup_inf_iSup`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattic
e α] (f g : ι → α), ⨆ i, f i ⊓ g i ≤ (⨆ i, f i) ⊓ ⨆ i, g i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_inf_iSup`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} {ι' 
: Type u_2} {f : ι → α} {g : ι' → α},   (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ i, f i.1 ⊓ g i
.2
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
-/
theorem iSup_inf_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

@[to_dual]
/-
**iSup_inf_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_1} [inst_1 : Preorder ι]
 [IsCodirectedOrder ι] {f g : ι → α},   Antitone f → Antitone g → ⨆ i, f i ⊓ g i
 = (⨆ i, f i) ⊓ ⨆ i, g i
参数：⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_inf_of_monotone`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_
1} [inst_1 : Preorder ι] [IsDirectedOrder ι] {f g : ι → α},   Monotone f → Monot
one g → ⨆ …
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem iSup_inf_of_antitone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left
/-
**himp_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {a b : α}, a ⇨ b = sSup {w | w ⊓ a ≤
 b}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_himp`：isGreatest_himp [GeneralizedHeytingAlgebra α] (a b : α)
 : IsGreatest {w | w ⊓ a <= b} (a ⇨ b)
-/
theorem himp_eq_sSup : a ⇨ b = sSup {w | w ⊓ a ≤ b} :=
  (isGreatest_himp a b).isLUB.sSup_eq.symm
/-
**compl_eq_sSup_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {a : α}, aᶜ = sSup {w | Disjoint w a
}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_compl`：isGreatest_compl [HeytingAlgebra α] (a : α) : IsGreate
st {w | Disjoint w a} (aᶜ)
-/
theorem compl_eq_sSup_disjoint : aᶜ = sSup {w | Disjoint w a} :=
  (isGreatest_compl a).isLUB.sSup_eq.symm
/-
**himp_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Frame α] {a b c : α}, a ⇨ b ≤ c ↔ ∀ (d : α), 
d ⊓ a ≤ b → d ≤ c
参数：d : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq_sSup`：∀ {α : Type u} [inst : Order.Frame α] {a b : α}, a ⇨ b = s
Sup {w | w ⊓ a ≤ b}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma himp_le_iff : a ⇨ b ≤ c ↔ ∀ d, d ⊓ a ≤ b → d ≤ c := by simp [himp_eq_sSup]

-- see Note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Order.Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]
/-
**Prod.instFrame** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAxioms.CompleteDi
stribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：Prod.instFrame [Frame β] : Frame (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instFrame [Frame β] : Frame (α × β) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra
/-
**Pi.instFrame** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAxioms.CompleteDist
ribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：Pi.instFrame {ι : Type*} {π : ι -> Type*} [forall i, Frame (π i)] : Frame 
(forall i, π i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instFrame {ι : Type*} {π : ι → Type*} [∀ i, Frame (π i)] : Frame (∀ i, π i) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b c d : α}

@[to_dual existing]
/-
**OrderDual.instFrame** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAxioms.Compl
eteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：OrderDual.instFrame : Frame αᵒᵈ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instFrame : Frame αᵒᵈ where
  __ := instCompleteLattice
  __ := instHeytingAlgebra
/-
**sdiff_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Coframe α] {a b : α}, a \ b = sInf {w | a ≤ b
 ⊔ w}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGLB.sInf_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : S
et α} {a : α}, IsGLB s a → sInf s = a
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `isLeast_sdiff`：isLeast_sdiff [GeneralizedCoheytingAlgebra α] (a b : α) :
 IsLeast {w | a <= b ⊔ w} (a \ b)
-/
theorem sdiff_eq_sInf : a \ b = sInf {w | a ≤ b ⊔ w} :=
  (isLeast_sdiff a b).isGLB.sInf_eq.symm
/-
**hnot_eq_sInf_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Coframe α] {a : α}, ￢a = sInf {w | Codisjoint
 a w}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGLB.sInf_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : S
et α} {a : α}, IsGLB s a → sInf s = a
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `isLeast_hnot`：isLeast_hnot [CoheytingAlgebra α] (a : α) : IsLeast {w | C
odisjoint a w} (￢a)
-/
theorem hnot_eq_sInf_codisjoint : ￢a = sInf {w | Codisjoint a w} :=
  (isLeast_hnot a).isGLB.sInf_eq.symm
/-
**le_sdiff_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Order.Coframe α] {a b c : α}, a ≤ b \ c ↔ ∀ (d : α)
, b ≤ c ⊔ d → a ≤ d
参数：d : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq_sInf`：∀ {α : Type u} [inst : Order.Coframe α] {a b : α}, a \ b 
= sInf {w | a ≤ b ⊔ w}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_sdiff_iff : a ≤ b \ c ↔ ∀ d, b ≤ c ⊔ d → a ≤ d := by simp [sdiff_eq_sInf]

@[to_dual existing]
/-
**Prod.instCoframe** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAxioms.Complete
DistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：Prod.instCoframe [Coframe β] : Coframe (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instCoframe [Coframe β] : Coframe (α × β) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual existing]
/-
**Pi.instCoframe** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAxioms.CompleteDi
stribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms`。
形式化陈述：Pi.instCoframe {ι : Type*} {π : ι -> Type*} [forall i, Coframe (π i)] : Co
frame (forall i, π i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCoframe {ι : Type*} {π : ι → Type*} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

end Coframe

section CompleteDistribLattice

/-
**OrderDual.instCompleteDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Mi
nimalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.Minima
lAxioms`。
形式化陈述：OrderDual.instCompleteDistribLattice [CompleteDistribLattice α] : Complete
DistribLattice αᵒᵈ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instCompleteDistribLattice [CompleteDistribLattice α] :
    CompleteDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe
/-
**Prod.instCompleteDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Minimal
Axioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxio
ms`。
形式化陈述：Prod.instCompleteDistribLattice [CompleteDistribLattice α] [CompleteDistri
bLattice β] : CompleteDistribLattice (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instCompleteDistribLattice [CompleteDistribLattice α] [CompleteDistribLattice β] :
    CompleteDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe
/-
**Pi.instCompleteDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAx
ioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms
`。
形式化陈述：Pi.instCompleteDistribLattice {ι : Type*} {π : ι -> Type*} [forall i, Comp
leteDistribLattice (π i)] : CompleteDistribLattice (forall i, π i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCompleteDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe

end CompleteDistribLattice

section CompletelyDistribLattice

/-
**OrderDual.instCompletelyDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.
MinimalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.Mini
malAxioms`。
形式化陈述：OrderDual.instCompletelyDistribLattice [CompletelyDistribLattice α] : Comp
letelyDistribLattice αᵒᵈ where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iInf_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : Comp
letelyDistribLattice α] {f : (a : ι) → κ a → α},   ⨆ a, ⨅ b, f a b = ⨅ g, ⨆ a, f
 a…
-/
instance OrderDual.instCompletelyDistribLattice [CompletelyDistribLattice α] :
    CompletelyDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)
/-
**Prod.instCompletelyDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Minim
alAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAx
ioms`。
形式化陈述：Prod.instCompletelyDistribLattice [CompletelyDistribLattice α] [Completely
DistribLattice β] : CompletelyDistribLattice (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instCompletelyDistribLattice [CompletelyDistribLattice α]
    [CompletelyDistribLattice β] : CompletelyDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]
/-
**Pi.instCompletelyDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Minimal
Axioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxio
ms`。
形式化陈述：Pi.instCompletelyDistribLattice {ι : Type*} {π : ι -> Type*} [forall i, Co
mpletelyDistribLattice (π i)] : CompletelyDistribLattice (forall i, π i) where _
_
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCompletelyDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompletelyDistribLattice (π i)] : CompletelyDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

end CompletelyDistribLattice

/--
A complete Boolean algebra is a Boolean algebra that is also a complete distributive lattice.

It is only completely distributive if it is also atomic.
-/
-- We do not directly extend `CompleteDistribLattice` to avoid having the `hnot` field
/-
**CompleteBooleanAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class CompleteBooleanAlgebra (α) extends CompleteLattice α, BooleanAlgebra α

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteBooleanAlgebra.toCompleteDistribLattice
    [CompleteBooleanAlgebra α] : CompleteDistribLattice α where
  __ := ‹CompleteBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra
/-
**Prod.instCompleteBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Minimal
Axioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxio
ms`。
形式化陈述：Prod.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] [CompleteBoolea
nAlgebra β] : CompleteBooleanAlgebra (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] [CompleteBooleanAlgebra β] :
    CompleteBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice
/-
**Pi.instCompleteBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.MinimalAx
ioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxioms
`。
形式化陈述：Pi.instCompleteBooleanAlgebra {ι : Type*} {π : ι -> Type*} [forall i, Comp
leteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (forall i, π i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCompleteBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (∀ i, π i) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice
/-
**OrderDual.instCompleteBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Mi
nimalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.Minima
lAxioms`。
形式化陈述：OrderDual.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] : Complete
BooleanAlgebra αᵒᵈ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] :
    CompleteBooleanAlgebra αᵒᵈ where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {s : Set α} {f : ι → α}

/-
**compl_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α] {f : ι → α},
 (iInf f)ᶜ = ⨆ i, (f i)ᶜ
参数：iInf f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `compl_le_of_compl_le`：compl_le_of_compl_le (h : yᶜ <= x) : xᶜ <= y
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem compl_iInf : (iInf f)ᶜ = ⨆ i, (f i)ᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (Compl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)
/-
**compl_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α] {f : ι → α},
 (iSup f)ᶜ = ⨅ i, (f i)ᶜ
参数：iSup f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_iSup : (iSup f)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_injective (by simp [compl_iInf])
/-
**compl_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α}, (sInf s)ᶜ = 
⨆ i ∈ s, iᶜ
参数：sInf s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_sInf : (sInf s)ᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]
/-
**compl_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α}, (sSup s)ᶜ = 
⨅ i ∈ s, iᶜ
参数：sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_sSup : (sSup s)ᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]
/-
**compl_sInf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α}, (sInf s)ᶜ = 
sSup (compl '' s)
参数：sInf s；compl '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `compl_sInf`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α}
, (sInf s)ᶜ = ⨆ i ∈ s, iᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
theorem compl_sInf' : (sInf s)ᶜ = sSup (Compl.compl '' s) :=
  compl_sInf.trans sSup_image.symm
/-
**compl_sSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α}, (sSup s)ᶜ = 
sInf (compl '' s)
参数：sSup s；compl '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `compl_sSup`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α}
, (sSup s)ᶜ = ⨅ i ∈ s, iᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem compl_sSup' : (sSup s)ᶜ = sInf (Compl.compl '' s) :=
  compl_sSup.trans sInf_image.symm

section symmDiff

open scoped symmDiff

/-- The symmetric difference of two `iSup`s is at most the `iSup` of the symmetric differences. -/
/-
**iSup_symmDiff_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α] {f g : ι → α
},   symmDiff (⨆ i, f i) (⨆ i, g i) ≤ ⨆ i, symmDiff (f i) (g i)
参数：⨆ i, f i；⨆ i, g i；f i；g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `le_symmDiff_sup_right`：le_symmDiff_sup_right (a b : α) : a <= (a ∆ b) ⊔ 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a

--- 原说明 ---
The symmetric difference of two `iSup`s is at most the `iSup` of the symmetric d
ifferences.
-/
theorem iSup_symmDiff_iSup_le {g : ι → α} : (⨆ i, f i) ∆ (⨆ i, g i) ≤ ⨆ i, ((f i) ∆ (g i)) := by
  simp_rw [symmDiff_le_iff, ← iSup_sup_eq]
  exact ⟨iSup_mono fun i ↦ sup_comm (g i) _ ▸ le_symmDiff_sup_right ..,
    iSup_mono fun i ↦ sup_comm (f i) _ ▸ symmDiff_comm (f i) _ ▸ le_symmDiff_sup_right ..⟩
/-
**iSup_symmDiff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α] {f : ι → α} 
[Nonempty ι] {a : α},   symmDiff (⨆ i, f i) a ≤ ⨆ i, symmDiff (f i) a
参数：⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `iSup_symmDiff_iSup_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBoole
anAlgebra α] {f g : ι → α},   symmDiff (⨆ i, f i) (⨆ i, g i) ≤ ⨆ i, symmDiff (f 
i) (g i)
-/
theorem iSup_symmDiff_le [Nonempty ι] {a : α} : (⨆ i, f i) ∆ a ≤ ⨆ i, f i ∆ a := by
  simpa [iSup_const] using iSup_symmDiff_iSup_le (g := fun _ : ι ↦ a)
/-
**symmDiff_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α] {f : ι → α} 
[Nonempty ι] {a : α},   symmDiff a (⨆ i, f i) ≤ ⨆ i, symmDiff a (f i)
参数：⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_symmDiff_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlg
ebra α] {f : ι → α} [Nonempty ι] {a : α},   symmDiff (⨆ i, f i) a ≤ ⨆ i, symmDif
f (f i…
-/
theorem symmDiff_iSup_le [Nonempty ι] {a : α} : a ∆ (⨆ i, f i) ≤ ⨆ i, a ∆ f i := by
  simpa [symmDiff_comm] using iSup_symmDiff_le (a := a)
/-
**sSup_symmDiff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α},   s.Nonempty
 → ∀ {a : α}, symmDiff (sSup s) a ≤ sSup ((fun x => symmDiff x a) '' s)
参数：sSup s；(fun x => symmDiff x a) '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `iSup_symmDiff_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlg
ebra α] {f : ι → α} [Nonempty ι] {a : α},   symmDiff (⨆ i, f i) a ≤ ⨆ i, symmDif
f (f i…
-/
theorem sSup_symmDiff_le (hs : s.Nonempty) {a : α} : sSup s ∆ a ≤ sSup ((· ∆ a) '' s) := by
  rw [sSup_image', sSup_eq_iSup']
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  exact iSup_symmDiff_le
/-
**symmDiff_sSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : Set α},   s.Nonempty
 → ∀ {a : α}, symmDiff a (sSup s) ≤ sSup ((fun x => symmDiff a x) '' s)
参数：sSup s；(fun x => symmDiff a x) '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `sSup_symmDiff_le`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : 
Set α},   s.Nonempty → ∀ {a : α}, symmDiff (sSup s) a ≤ sSup ((fun x => symmDiff
 x a) …
-/
theorem symmDiff_sSup_le (hs : s.Nonempty) {a : α} : a ∆ sSup s ≤ sSup ((a ∆ ·) '' s) := by
  simpa [symmDiff_comm] using sSup_symmDiff_le (a := a) hs
/-
**sSup_symmDiff_sSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s t : Set α},   s.Nonemp
ty → t.Nonempty → symmDiff (sSup s) (sSup t) ≤ sSup (Set.image2 (fun x1 x2 => sy
mmDiff x1 x2) s t)
参数：sSup s；sSup t；Set.image2 (fun x1 x2 => symmDiff x1 x2) s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_image2`：sSup_image2 {f : β -> γ -> α} {s : Set β} {t : Set γ} : sSu
p (image2 f s t) = ⨆ (a in s) (b in t), f a b
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `sSup_symmDiff_le`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : 
Set α},   s.Nonempty → ∀ {a : α}, symmDiff (sSup s) a ≤ sSup ((fun x => symmDiff
 x a) …
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `symmDiff_sSup_le`：∀ {α : Type u} [inst : CompleteBooleanAlgebra α] {s : 
Set α},   s.Nonempty → ∀ {a : α}, symmDiff a (sSup s) ≤ sSup ((fun x => symmDiff
 a x) …
-/
theorem sSup_symmDiff_sSup_le {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup s ∆ sSup t ≤ sSup (image2 (· ∆ ·) s t) := by
  rw [sSup_image2]
  calc
  _ ≤ ⨆ a ∈ s, a ∆ sSup t := by simpa [sSup_image] using sSup_symmDiff_le hs
  _ ≤ _ := iSup_mono fun a ↦ iSup_mono fun _ ↦ by simpa [sSup_image] using symmDiff_sSup_le ht

/-- A `biSup` version of `iSup_symmDiff_iSup_le`. -/
/-
**biSup_symmDiff_biSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α] {p : ι → Pro
p} {f g : (i : ι) → p i → α},   symmDiff (⨆ i, ⨆ (h : p i), f i h) (⨆ i, ⨆ (h : 
p i), g i h) ≤ ⨆ i, ⨆ (h : p i), symmDiff (f i h) (g i h)
参数：i : ι；⨆ i, ⨆ (h : p i), f i h；⨆ i, ⨆ (h : p i), g i h；h : p i；f i h；g i h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `iSup_symmDiff_iSup_le`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBoole
anAlgebra α] {f g : ι → α},   symmDiff (⨆ i, f i) (⨆ i, g i) ≤ ⨆ i, symmDiff (f 
i) (g i)
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g

--- 原说明 ---
A `biSup` version of `iSup_symmDiff_iSup_le`.
-/
theorem biSup_symmDiff_biSup_le {p : ι → Prop} {f g : (i : ι) → p i → α} :
    (⨆ i, ⨆ (h : p i), f i h) ∆ (⨆ i, ⨆ (h : p i), g i h) ≤
    ⨆ i, ⨆ (h : p i), ((f i h) ∆ (g i h)) :=
  le_trans iSup_symmDiff_iSup_le <| iSup_mono fun _ ↦ iSup_symmDiff_iSup_le

end symmDiff

end CompleteBooleanAlgebra

/--
A complete atomic Boolean algebra is a complete Boolean algebra
that is also completely distributive.

We take iSup_iInf_eq as the definition here,
and prove later on that this implies atomicity.
-/
-- We do not directly extend `CompletelyDistribLattice` to avoid having the `hnot` field
/-
**CompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class CompleteAtomicBooleanAlgebra (α : Type u) extends CompleteBooleanAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteAtomicBooleanAlgebra.toCompletelyDistribLattice
    [CompleteAtomicBooleanAlgebra α] : CompletelyDistribLattice α where
  __ := ‹CompleteAtomicBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra
/-
**Prod.instCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.M
inimalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.Minim
alAxioms`。
形式化陈述：Prod.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α] [Co
mpleteAtomicBooleanAlgebra β] : CompleteAtomicBooleanAlgebra (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α]
    [CompleteAtomicBooleanAlgebra β] : CompleteAtomicBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompletelyDistribLattice
/-
**Pi.instCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Min
imalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.Minimal
Axioms`。
形式化陈述：Pi.instCompleteAtomicBooleanAlgebra {ι : Type*} {π : ι -> Type*} [forall i
, CompleteAtomicBooleanAlgebra (π i)] : CompleteAtomicBooleanAlgebra (forall i, 
π i) where __
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instCompleteAtomicBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteAtomicBooleanAlgebra (π i)] : CompleteAtomicBooleanAlgebra (∀ i, π i) where
  __ := Pi.instCompleteBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]
/-
**OrderDual.instCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Fr
ame.MinimalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.
MinimalAxioms`。
形式化陈述：OrderDual.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α
] : CompleteAtomicBooleanAlgebra αᵒᵈ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra αᵒᵈ where
  __ := instCompleteBooleanAlgebra
  __ := instCompletelyDistribLattice
/-
**Prop.instCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.M
inimalAxioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.Minim
alAxioms`。
形式化陈述：Prop.instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Prop 
where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ
-/
instance Prop.instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.instBooleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]
/-
**Prop.instCompleteBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Order.Frame.Minimal
Axioms.CompleteDistribLattice.MinimalAxioms.CompletelyDistribLattice.MinimalAxio
ms`。
形式化陈述：Prop.instCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prop.instCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop := inferInstance

section lift

/-- Pullback an `Order.Frame.MinimalAxioms` along an injection. -/
@[to_dual /-- Pullback an `Order.Coframe.MinimalAxioms` along a function. -/]
/-
**Function.frameMinimalAxioms** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : CompleteLattice α] [inst_1 : CompleteL
attice β],   Order.Frame.MinimalAxioms β →     ∀ (f : α → β),       (∀ {x y : α}
, f x ≤ f y ↔ x ≤ y) →         (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) → (∀ (s : Se
t α), f (sSup s) = ⨆ a ∈ s, f a) → Order.Frame.MinimalAxioms α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀
 (s : Set α), f (sSup s) = ⨆ a ∈ s, f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `_private.Mathlib.Order.CompleteBooleanAlgebra.0.Order.Frame.MinimalAxiom
s.inf_iSup₂_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : CompleteLa
ttice α],   Order.Frame.MinimalAxioms α → ∀ {f : (i : ι) → κ i → α} (a : α),…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)

--- 原说明 ---
Pullback an `Order.Frame.MinimalAxioms` along an injection.
-/
protected theorem Function.frameMinimalAxioms [CompleteLattice α] [CompleteLattice β]
    (minAx : Frame.MinimalAxioms β) (f : α → β)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) : Frame.MinimalAxioms α where
  inf_sSup_le_iSup_inf a s := by
    rw [← le, ← sSup_image, map_inf, map_sSup s, minAx.inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

@[to_dual (attr := deprecated (since := "2026-07-30"))]
alias Function.Injective.frameMinimalAxioms := Function.frameMinimalAxioms

-- See note [reducible non-instances]
/-- Pullback an `Order.Frame` along an injection. -/
/-
**Function.Injective.frame** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : Top α]
 →                   [inst_7 : Bot α] →                     [inst_8 : Compl α] →
                       [inst_9 : HImp α] →                         [inst_10 : Or
der.Frame β] →                           (f : α → β) →                          
   Function.Injective f →                               (∀ {x y : α}, f x ≤ f y 
↔ x ≤ y) →                                 (∀ {x y : α}, f x < f y ↔ x < y) →   
                                (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →          
                           (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →               
                        (∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →            
                             (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) →       
                                    f ⊤ = ⊤ →                                   
          f ⊥ = ⊥ →                                               (∀ (a : α), f 
aᶜ = (f a)ᶜ) →                                                 (∀ (a b : α), f (
a ⇨ b) = f a ⇨ f b) → Order.Frame α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a；∀ (a : α), f 
aᶜ = (f a)ᶜ；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingAlgebra.himp_bot`：∀ {α : Type u_4} [self : HeytingAlgebra α] (a :
 α), a ⇨ ⊥ = aᶜ

--- 原说明 ---
Pullback an `Order.Frame` along an injection.
-/
protected abbrev Function.Injective.frame [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [Compl α] [HImp α] [Frame β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : Frame α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp

-- See note [reducible non-instances]
/-- Pullback an `Order.Coframe` along an injection. -/
/-
**Function.Injective.coframe** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : Top α]
 →                   [inst_7 : Bot α] →                     [inst_8 : HNot α] → 
                      [inst_9 : SDiff α] →                         [inst_10 : Or
der.Coframe β] →                           (f : α → β) →                        
     Function.Injective f →                               (∀ {x y : α}, f x ≤ f 
y ↔ x ≤ y) →                                 (∀ {x y : α}, f x < f y ↔ x < y) → 
                                  (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →        
                             (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →             
                          (∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →          
                               (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) →     
                                      f ⊤ = ⊤ →                                 
            f ⊥ = ⊥ →                                               (∀ (a : α), 
f (￢a) = ￢f a) →                                                 (∀ (a b : α), f
 (a \ b) = f a \ f b) → Order.Coframe α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a；∀ (a : α), f 
(￢a) = ￢f a；∀ (a b : α), f (a \ b) = f a \ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : CoheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a

--- 原说明 ---
Pullback an `Order.Coframe` along an injection.
-/
protected abbrev Function.Injective.coframe [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HNot α] [SDiff α] [Coframe β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : Coframe α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

/-- Pullback a `CompleteDistribLattice.MinimalAxioms` along an injection. -/
/-
**Function.completeDistribLatticeMinimalAxioms** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : CompleteLattice α] [inst_1 : CompleteL
attice β],   CompleteDistribLattice.MinimalAxioms β →     ∀ (f : α → β),       (
∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →         (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →
           (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →             (∀ (s : Set α), f 
(sSup s) = ⨆ a ∈ s, f a) →               (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f
 a) → CompleteDistribLattice.MinimalAxioms α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ (a b : α), f (a ⊔ b) = f a ⊔ f b；∀
 (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a；∀ (s 
: Set α), f (sInf s) = ⨅ a ∈ s, f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.frameMinimalAxioms`：∀ {α : Type u} {β : Type v} [inst : Complet
eLattice α] [inst_1 : CompleteLattice β],   Order.Frame.MinimalAxioms β →     ∀ 
(f : α → β),     …
· 使用定理 `CompleteDistribLattice.MinimalAxioms.toFrame`：∀ {α : Type u} [inst : Com
pleteLattice α], CompleteDistribLattice.MinimalAxioms α → Order.Frame.MinimalAxi
oms α
· 使用定理 `Function.coframeMinimalAxioms`：∀ {α : Type u} {β : Type v} [inst : Compl
eteLattice α] [inst_1 : CompleteLattice β],   Order.Coframe.MinimalAxioms β →   
  ∀ (f : α → β),   …
· 使用定理 `CompleteDistribLattice.MinimalAxioms.toCoframe`：∀ {α : Type u} [inst : C
ompleteLattice α], CompleteDistribLattice.MinimalAxioms α → Order.Coframe.Minima
lAxioms α

--- 原说明 ---
Pullback a `CompleteDistribLattice.MinimalAxioms` along an injection.
-/
protected theorem Function.completeDistribLatticeMinimalAxioms
    [CompleteLattice α] [CompleteLattice β]
    (minAx : CompleteDistribLattice.MinimalAxioms β) (f : α → β)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) :
    CompleteDistribLattice.MinimalAxioms α where
  __ := f.frameMinimalAxioms minAx.toFrame le map_inf map_sSup
  __ := f.coframeMinimalAxioms minAx.toCoframe le map_sup map_sInf

@[deprecated (since := "2026-07-30")]
alias Function.Injective.completeDistribLatticeMinimalAxioms :=
  Function.completeDistribLatticeMinimalAxioms

-- See note [reducible non-instances]
/-- Pullback a `CompleteDistribLattice` along an injection. -/
/-
**Function.Injective.completeDistribLattice** 是 Mathlib 中的一个定义，位于命名空间 `Function.
Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : Top α]
 →                   [inst_7 : Bot α] →                     [inst_8 : Compl α] →
                       [inst_9 : HImp α] →                         [inst_10 : HN
ot α] →                           [inst_11 : SDiff α] →                         
    [inst_12 : CompleteDistribLattice β] →                               (f : α 
→ β) →                                 Function.Injective f →                   
                (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →                              
       (∀ {x y : α}, f x < f y ↔ x < y) →                                       
(∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                                         (
∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →                                           
(∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →                                    
         (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) →                           
                    f ⊤ = ⊤ →                                                 f 
⊥ = ⊥ →                                                   (∀ (a : α), f aᶜ = (f 
a)ᶜ) →                                                     (∀ (a b : α), f (a ⇨ 
b) = f a ⇨ f b) →                                                       (∀ (a : 
α), f (￢a) = ￢f a) →                                                         (∀ 
(a b : α), f (a \ b) = f a \ f b) → CompleteDistribLattice α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a；∀ (a : α), f 
aᶜ = (f a)ᶜ；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b；∀ (a : α), f (￢a) = ￢f a；∀ (a b :
 α), f (a \ b) = f a \ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Coframe.sdiff_le_iff`：∀ {α : Type u_1} [self : Order.Coframe α] (a
 b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `Order.Coframe.top_sdiff`：∀ {α : Type u_1} [self : Order.Coframe α] (a : 
α), ⊤ \ a = ￢a

--- 原说明 ---
Pullback a `CompleteDistribLattice` along an injection.
-/
protected abbrev Function.Injective.completeDistribLattice [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompleteDistribLattice β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteDistribLattice α where
  __ := hf.frame f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp
  __ := hf.coframe f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_hnot map_sdiff

/-- Pullback a `CompletelyDistribLattice.MinimalAxioms` along an injection. -/
/-
**Function.Injective.completelyDistribLatticeMinimalAxioms** 是 Mathlib 中的一个定理，位于
命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : CompleteLattice α] [inst_1 : CompleteL
attice β],   CompletelyDistribLattice.MinimalAxioms β →     ∀ (f : α → β),      
 Function.Injective f →         (∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →    
       (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) → CompletelyDistribLattice.Min
imalAxioms α
参数：f : α → β；∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) 
= ⨅ a ∈ s, f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Order.CompleteBooleanAlgebra.0.CompletelyDistribLattice
.MinimalAxioms.iInf_iSup_eq'`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [ins
t : CompleteLattice α],   CompletelyDistribLattice.MinimalAxioms α → ∀ (f : (a :
 ι) → κ a …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullback a `CompletelyDistribLattice.MinimalAxioms` along an injection.
-/
protected theorem Function.Injective.completelyDistribLatticeMinimalAxioms
    [CompleteLattice α] [CompleteLattice β]
    (minAx : CompletelyDistribLattice.MinimalAxioms β) (f : α → β) (hf : Injective f)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) :
    CompletelyDistribLattice.MinimalAxioms α where
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      minAx.iInf_iSup_eq']

-- See note [reducible non-instances]
/-- Pullback a `CompletelyDistribLattice` along an injection. -/
/-
**Function.Injective.completelyDistribLattice** 是 Mathlib 中的一个定义，位于命名空间 `Functio
n.Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : Top α]
 →                   [inst_7 : Bot α] →                     [inst_8 : Compl α] →
                       [inst_9 : HImp α] →                         [inst_10 : HN
ot α] →                           [inst_11 : SDiff α] →                         
    [inst_12 : CompletelyDistribLattice β] →                               (f : 
α → β) →                                 Function.Injective f →                 
                  (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →                            
         (∀ {x y : α}, f x < f y ↔ x < y) →                                     
  (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                                        
 (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →                                         
  (∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →                                  
           (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) →                         
                      f ⊤ = ⊤ →                                                 
f ⊥ = ⊥ →                                                   (∀ (a : α), f aᶜ = (
f a)ᶜ) →                                                     (∀ (a b : α), f (a 
⇨ b) = f a ⇨ f b) →                                                       (∀ (a 
: α), f (￢a) = ￢f a) →                                                         (
∀ (a b : α), f (a \ b) = f a \ f b) →                                           
                CompletelyDistribLattice α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a；∀ (a : α), f 
aᶜ = (f a)ᶜ；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b；∀ (a : α), f (￢a) = ￢f a；∀ (a b :
 α), f (a \ b) = f a \ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingAlgebra.sdiff_le_iff`：∀ {α : Type u_4} [self : BiheytingAlgebra
 α] (a b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `BiheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : BiheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a

--- 原说明 ---
Pullback a `CompletelyDistribLattice` along an injection.
-/
protected abbrev Function.Injective.completelyDistribLattice [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompletelyDistribLattice β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompletelyDistribLattice α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.biheytingAlgebra f
    le lt map_sup map_inf map_top map_bot map_compl map_hnot map_himp map_sdiff
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

-- See note [reducible non-instances]
/-- Pullback a `CompleteBooleanAlgebra` along an injection. -/
/-
**Function.Injective.completeBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Function.
Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : Top α]
 →                   [inst_7 : Bot α] →                     [inst_8 : Compl α] →
                       [inst_9 : HImp α] →                         [inst_10 : SD
iff α] →                           [inst_11 : CompleteBooleanAlgebra β] →       
                      (f : α → β) →                               Function.Injec
tive f →                                 (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →     
                              (∀ {x y : α}, f x < f y ↔ x < y) →                
                     (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                     
                  (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →                        
                 (∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →                   
                        (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) →            
                                 f ⊤ = ⊤ →                                      
         f ⊥ = ⊥ →                                                 (∀ (a : α), f
 aᶜ = (f a)ᶜ) →                                                   (∀ (a b : α), 
f (a ⇨ b) = f a ⇨ f b) →                                                     (∀ 
(a b : α), f (a \ b) = f a \ f b) → CompleteBooleanAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a；∀ (a : α), f 
aᶜ = (f a)ᶜ；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b；∀ (a b : α), f (a \ b) = f a \ f 
b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ

--- 原说明 ---
Pullback a `CompleteBooleanAlgebra` along an injection.
-/
protected abbrev Function.Injective.completeBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [SDiff α]
    [CompleteBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

-- See note [reducible non-instances]
/-- Pullback a `CompleteAtomicBooleanAlgebra` along an injection. -/
/-
**Function.Injective.completeAtomicBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Fun
ction.Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
SupSet α] →               [inst_5 : InfSet α] →                 [inst_6 : Top α]
 →                   [inst_7 : Bot α] →                     [inst_8 : Compl α] →
                       [inst_9 : HImp α] →                         [inst_10 : HN
ot α] →                           [inst_11 : SDiff α] →                         
    [inst_12 : CompleteAtomicBooleanAlgebra β] →                               (
f : α → β) →                                 Function.Injective f →             
                      (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →                        
             (∀ {x y : α}, f x < f y ↔ x < y) →                                 
      (∀ (a b : α), f (a ⊔ b) = f a ⊔ f b) →                                    
     (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) →                                     
      (∀ (s : Set α), f (sSup s) = ⨆ a ∈ s, f a) →                              
               (∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a) →                     
                          f ⊤ = ⊤ →                                             
    f ⊥ = ⊥ →                                                   (∀ (a : α), f aᶜ
 = (f a)ᶜ) →                                                     (∀ (a b : α), f
 (a ⇨ b) = f a ⇨ f b) →                                                       (∀
 (a : α), f (￢a) = ￢f a) →                                                      
   (∀ (a b : α), f (a \ b) = f a \ f b) →                                       
                    CompleteAtomicBooleanAlgebra α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b；∀ (s : Set α), 
f (sSup s) = ⨆ a ∈ s, f a；∀ (s : Set α), f (sInf s) = ⨅ a ∈ s, f a；∀ (a : α), f 
aᶜ = (f a)ᶜ；∀ (a b : α), f (a ⇨ b) = f a ⇨ f b；∀ (a : α), f (￢a) = ￢f a；∀ (a b :
 α), f (a \ b) = f a \ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ
· 使用定理 `CompletelyDistribLattice.iInf_iSup_eq`：∀ {α : Type u} [self : Completely
DistribLattice α] {ι : Type u} {κ : ι → Type u} (f : (a : ι) → κ a → α),   ⨅ a, 
⨆ b, f a b = ⨆ g, ⨅ a, f a …

--- 原说明 ---
Pullback a `CompleteAtomicBooleanAlgebra` along an injection.
-/
protected abbrev Function.Injective.completeAtomicBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompleteAtomicBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteAtomicBooleanAlgebra α where
  __ := hf.completelyDistribLattice f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp map_hnot map_sdiff
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `Frame` across an `Equiv`. -/
/-
**Equiv.frame** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [Order.Frame β] → Order.Frame α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Frame` across an `Equiv`.
-/
protected abbrev frame [Frame β] : Frame α := by
  let completeLattice := e.completeLattice
  let heytingAlgebra := e.heytingAlgebra
  apply e.injective.frame <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `Coframe` across an `Equiv`. -/
/-
**Equiv.coframe** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [Order.Coframe β] → Order.Coframe α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Coframe` across an `Equiv`.
-/
protected abbrev coframe [Coframe β] : Coframe α := by
  let completeLattice := e.completeLattice
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.coframe <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteDistribLattice` across an `Equiv`. -/
/-
**Equiv.completeDistribLattice** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [CompleteDistribLattice β] → Complet
eDistribLattice α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CompleteDistribLattice` across an `Equiv`.
-/
protected abbrev completeDistribLattice [CompleteDistribLattice β] : CompleteDistribLattice α := by
  let completeLattice := e.completeLattice
  let biheytingAlgebra := e.biheytingAlgebra
  apply e.injective.completeDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompletelyDistribLattice` across an `Equiv`. -/
/-
**Equiv.completelyDistribLattice** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [CompletelyDistribLattice β] → Compl
etelyDistribLattice α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CompletelyDistribLattice` across an `Equiv`.
-/
protected abbrev completelyDistribLattice [CompletelyDistribLattice β] :
    CompletelyDistribLattice α := by
  let completeDistribLattice := e.completeDistribLattice
  apply e.injective.completelyDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteBooleanAlgebra` across an `Equiv`. -/
/-
**Equiv.completeBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [CompleteBooleanAlgebra β] → Complet
eBooleanAlgebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CompleteBooleanAlgebra` across an `Equiv`.
-/
protected abbrev completeBooleanAlgebra [CompleteBooleanAlgebra β] : CompleteBooleanAlgebra α := by
  let completeLattice := e.completeLattice
  let booleanAlgebra := e.booleanAlgebra
  apply e.injective.completeBooleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteAtomicBooleanAlgebra` across an `Equiv`. -/
/-
**Equiv.completeAtomicBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [CompleteAtomicBooleanAlgebra β] → C
ompleteAtomicBooleanAlgebra α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CompleteAtomicBooleanAlgebra` across an `Equiv`.
-/
protected abbrev completeAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra β] :
    CompleteAtomicBooleanAlgebra α := by
  let completeBooleanAlgebra := e.completeBooleanAlgebra
  apply e.injective.completeAtomicBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1})

/-
**PUnit.instCompleteBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `PUnit`。
形式化陈述：CompleteBooleanAlgebra PUnit.{u_1 + 1}
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ
-/
instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra PUnit where
/-
**PUnit.instCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `PUnit`。
形式化陈述：CompleteAtomicBooleanAlgebra PUnit.{u_1 + 1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra PUnit where
  iInf_iSup_eq _ := rfl

@[to_dual (attr := simp)]
/-
**PUnit.sSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：∀ (s : Set PUnit.{u + 1}), sSup s = PUnit.unit
参数：s : Set PUnit.{u + 1}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_eq : sSup s = unit :=
  rfl

end PUnit

