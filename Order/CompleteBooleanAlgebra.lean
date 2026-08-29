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

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι -> Sort w'}

/--
Definition of `Order.Frame.MinimalAxioms` / `Order.Frame.MinimalAxioms` 的定义

English:
structure Order.Frame.MinimalAxioms
  parameters: (α : Type u) [CompleteLattice α]
  axioms and operations (1):
    - inf_sSup_le_iSup_inf((a : α) (s : Set α)) : a ⊓ sSup s <= ⨆ b in s, a ⊓ b

中文:
结构 Order.框架.MinimalAxioms
  参数: (α : 类型u) [完备格 α]
  公理与运算 (1 个):
    - inf_sSup_le_iSup_inf((a : α) (s : 集合 α)) : a ⊓ sSup s <= ⨆ b in s, a ⊓ b
-/
structure Order.Frame.MinimalAxioms (α : Type u) [CompleteLattice α] where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s <= ⨆ b in s, a ⊓ b

/-- Structure containing the minimal axioms required to check that an order is a coframe. Do NOT
use, except for implementing `Order.Coframe` via `Order.Coframe.ofMinimalAxioms`.

This structure omits the `sdiff`, `hnot` fields, which can be recovered using
`Order.Coframe.ofMinimalAxioms`. -/
@[to_dual Frame.MinimalAxioms]
/--
Definition of `Order.Coframe.MinimalAxioms` / `Order.Coframe.MinimalAxioms` 的定义

English:
structure Order.Coframe.MinimalAxioms
  parameters: (α : Type u) [CompleteLattice α]
  axioms and operations (1):
    - iInf_sup_le_sup_sInf((a : α) (s : Set α)) : ⨅ b in s, a ⊔ b <= a ⊔ sInf s

中文:
结构 Order.余frame.MinimalAxioms
  参数: (α : 类型u) [完备格 α]
  公理与运算 (1 个):
    - iInf_sup_le_sup_sInf((a : α) (s : 集合 α)) : ⨅ b in s, a ⊔ b <= a ⊔ sInf s
-/
structure Order.Coframe.MinimalAxioms (α : Type u) [CompleteLattice α] where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b in s, a ⊔ b <= a ⊔ sInf s

/--
Definition of `Order.Frame` / `Order.Frame` 的定义

English:
class Order.Frame
  parameters: (α : Type*)
  extends: CompleteLattice α, HeytingAlgebra α
  (no additional axioms)

中文:
类 Order.框架
  参数: (α : 类型)
  继承: 完备格 α, Heyting代数 α
  (无附加公理)
-/
class Order.Frame (α : Type*) extends CompleteLattice α, HeytingAlgebra α where

set_option linter.translate.warnInvalid false in
/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
@[to_dual]
/--
Definition of `Order.Coframe` / `Order.Coframe` 的定义

English:
class Order.Coframe
  parameters: (α : Type*)
  extends: CompleteLattice α, CoheytingAlgebra α
  (no additional axioms)

中文:
类 Order.余frame
  参数: (α : 类型)
  继承: 完备格 α, 余heyting代数 α
  (无附加公理)
-/
class Order.Coframe (α : Type*) extends CompleteLattice α, CoheytingAlgebra α where

open Order

/-- `⊓` distributes over `⨆`. -/
@[to_dual /-- `⊔` distributes over `⨅`. -/]
/--
theorem `inf_sSup_eq` / 定理 `inf_sSup_eq`

English:
theorem inf_sSup_eq
  given: [Frame α] {s : Set α} {a : α}
  statement: a ⊓ sSup s = ⨆ b in s, a ⊓ b
  proof: gc_inf_himp.l_sSup

中文:
定理 inf_sSup_eq
  条件: [框架 α] {s : 集合 α} {a : α}
  结论: a ⊓ sSup s = ⨆ b in s, a ⊓ b
  证明: gc_inf_himp.l_sSup

Depends on / 依赖: gc_inf_himp, gc_inf_himp.l_sSup, l_sSup
-/
theorem inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ b in s, a ⊓ b :=
  gc_inf_himp.l_sSup

/--
Definition of `CompleteDistribLattice.MinimalAxioms` / `CompleteDistribLattice.MinimalAxioms` 的定义

English:
structure CompleteDistribLattice.MinimalAxioms
  parameters: (α : Type u) [CompleteLattice α]
  (no additional axioms)

中文:
结构 完备分配格.MinimalAxioms
  参数: (α : 类型u) [完备格 α]
  (无附加公理)
-/
structure CompleteDistribLattice.MinimalAxioms (α : Type u) [CompleteLattice α] extends
    toFrame : Frame.MinimalAxioms α, toCoframe : Coframe.MinimalAxioms α where

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Frame`. -/
add_decl_doc CompleteDistribLattice.MinimalAxioms.toFrame

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Coframe`. -/
add_decl_doc CompleteDistribLattice.MinimalAxioms.toCoframe

/--
Definition of `CompleteDistribLattice` / `CompleteDistribLattice` 的定义

English:
class CompleteDistribLattice
  parameters: (α : Type*)
  extends: Frame α, Coframe α, BiheytingAlgebra α
  (no additional axioms)

中文:
类 完备分配格
  参数: (α : 类型)
  继承: 框架 α, 余frame α, Biheyting代数 α
  (无附加公理)
-/
class CompleteDistribLattice (α : Type*) extends Frame α, Coframe α, BiheytingAlgebra α

attribute [to_dual existing] CompleteDistribLattice.toFrame

/--
Definition of `CompletelyDistribLattice.MinimalAxioms` / `CompletelyDistribLattice.MinimalAxioms` 的定义

English:
structure CompletelyDistribLattice.MinimalAxioms
  parameters: (α : Type u) [CompleteLattice α]
  axioms and operations (1):
    - iInf_iSup_eq({ι : Type u} {κ : ι -> Type u} (f : forall a, κ a -> α)) : (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a)

中文:
结构 余mpletelyDistrib格.MinimalAxioms
  参数: (α : 类型u) [完备格 α]
  公理与运算 (1 个):
    - iInf_iSup_eq({ι : 类型u} {κ : ι -> 类型u} (f : 对任意 a, κ a -> α)) : (⨅ a, ⨆ b, f a b) = ⨆ g : 对任意 a, κ a, ⨅ a, f a (g a)
-/
structure CompletelyDistribLattice.MinimalAxioms (α : Type u) [CompleteLattice α] where
  protected iInf_iSup_eq {ι : Type u} {κ : ι -> Type u} (f : forall a, κ a -> α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a)

/--
Definition of `CompletelyDistribLattice` / `CompletelyDistribLattice` 的定义

English:
class CompletelyDistribLattice
  parameters: (α : Type u)
  extends: CompleteLattice α, BiheytingAlgebra α
  axioms and operations (1):
    - iInf_iSup_eq({ι : Type u} {κ : ι -> Type u} (f : forall a, κ a -> α)) : (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a)

中文:
类 余mpletelyDistrib格
  参数: (α : 类型u)
  继承: 完备格 α, Biheyting代数 α
  公理与运算 (1 个):
    - iInf_iSup_eq({ι : 类型u} {κ : ι -> 类型u} (f : 对任意 a, κ a -> α)) : (⨅ a, ⨆ b, f a b) = ⨆ g : 对任意 a, κ a, ⨅ a, f a (g a)
-/
class CompletelyDistribLattice (α : Type u) extends CompleteLattice α, BiheytingAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι -> Type u} (f : forall a, κ a -> α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a)

/--
theorem `le_iInf_iSup` / 定理 `le_iInf_iSup`

English:
theorem le_iInf_iSup
  given: [CompleteLattice α] {f : forall a, κ a -> α}
  proof: iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

中文:
定理 le_iInf_iSup
  条件: [完备格 α] {f : 对任意 a, κ a -> α}
  证明: iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

Depends on / 依赖: iInf_le, iSup_le, le_iInf, le_iSup, le_trans
-/
theorem le_iInf_iSup [CompleteLattice α] {f : forall a, κ a -> α} :
    (⨆ g : forall a, κ a, ⨅ a, f a (g a)) <= ⨅ a, ⨆ b, f a b :=
  iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

/--
lemma `iSup_iInf_le` / 引理 `iSup_iInf_le`

English:
lemma iSup_iInf_le
  given: [CompleteLattice α] {f : forall a, κ a -> α}
  proof: le_iInf_iSup (α := αᵒᵈ)

中文:
引理 iSup_iInf_le
  条件: [完备格 α] {f : 对任意 a, κ a -> α}
  证明: le_iInf_iSup (α := αᵒᵈ)

Depends on / 依赖: le_iInf_iSup
-/
lemma iSup_iInf_le [CompleteLattice α] {f : forall a, κ a -> α} :
    ⨆ a, ⨅ b, f a b <= ⨅ g : forall a, κ a, ⨆ a, f a (g a) :=
  le_iInf_iSup (α := αᵒᵈ)

namespace Order.Frame.MinimalAxioms
variable (s : Set α) (a b : α)

section
variable [CompleteLattice α] (minAx : MinimalAxioms α)
include minAx

@[to_dual]
/--
lemma `inf_sSup_eq` / 引理 `inf_sSup_eq`

English:
lemma inf_sSup_eq
  statement: a ⊓ sSup s = ⨆ b in s, a ⊓ b
  proof: le_antisymm (minAx.inf_sSup_le_iSup_inf _ _) iSup_inf_le_inf_sSup

@[to_dual]

中文:
引理 inf_sSup_eq
  结论: a ⊓ sSup s = ⨆ b in s, a ⊓ b
  证明: le_antisymm (minAx.inf_sSup_le_iSup_inf _ _) iSup_inf_le_inf_sSup

@[to_dual]
-/
private lemma inf_sSup_eq : a ⊓ sSup s = ⨆ b in s, a ⊓ b :=
  le_antisymm (minAx.inf_sSup_le_iSup_inf _ _) iSup_inf_le_inf_sSup

@[to_dual]
/--
lemma `sSup_inf_eq` / 引理 `sSup_inf_eq`

English:
lemma sSup_inf_eq
  statement: sSup s ⊓ b = ⨆ a in s, a ⊓ b
  proof: by
  simpa only [inf_comm] using inf_sSup_eq s b minAx

@[to_dual]

中文:
引理 sSup_inf_eq
  结论: sSup s ⊓ b = ⨆ a in s, a ⊓ b
  证明: by
  simpa only [inf_comm] using inf_sSup_eq s b minAx

@[to_dual]
-/
private lemma sSup_inf_eq : sSup s ⊓ b = ⨆ a in s, a ⊓ b := by
  simpa only [inf_comm] using inf_sSup_eq s b minAx

@[to_dual]
/--
lemma `iSup_inf_eq` / 引理 `iSup_inf_eq`

English:
lemma iSup_inf_eq
  given: (f : ι -> α) (a : α)
  statement: (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
  proof: by
  rw [iSup]; rw [minAx.sSup_inf_eq]; rw [iSup_range]

@[to_dual]

中文:
引理 iSup_inf_eq
  条件: (f : ι -> α) (a : α)
  结论: (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
  证明: by
  rw [iSup]; rw [minAx.sSup_inf_eq]; rw [iSup_range]

@[to_dual]
-/
private lemma iSup_inf_eq (f : ι -> α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup]; rw [minAx.sSup_inf_eq]; rw [iSup_range]

@[to_dual]
/--
lemma `inf_iSup_eq` / 引理 `inf_iSup_eq`

English:
lemma inf_iSup_eq
  given: (a : α) (f : ι -> α)
  statement: (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i
  proof: by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

@[to_dual]

中文:
引理 inf_iSup_eq
  条件: (a : α) (f : ι -> α)
  结论: (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i
  证明: by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

@[to_dual]
-/
private lemma inf_iSup_eq (a : α) (f : ι -> α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

@[to_dual]
/--
lemma `inf_iSup₂_eq` / 引理 `inf_iSup₂_eq`

English:
lemma inf_iSup₂_eq
  given: {f : forall i, κ i -> α} (a : α)
  proof: by
  simp only [minAx.inf_iSup_eq]

中文:
引理 inf_iSup₂_eq
  条件: {f : 对任意 i, κ i -> α} (a : α)
  证明: by
  simp only [minAx.inf_iSup_eq]
-/
private lemma inf_iSup₂_eq {f : forall i, κ i -> α} (a : α) :
    (a ⊓ ⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, a ⊓ f i j := by
  simp only [minAx.inf_iSup_eq]

end

/-- The `Order.Frame.MinimalAxioms` element corresponding to a frame. -/
@[to_dual /-- The `Order.Coframe.MinimalAxioms` element corresponding to a frame. -/]
/--
theorem `of` / 定理 `of`

English:
theorem of
  given: [Frame α]
  statement: MinimalAxioms α where
  proof: ‹Frame α›
  inf_sSup_le_iSup_inf a s := _root_.inf_sSup_eq.le

中文:
定理 of
  条件: [框架 α]
  结论: MinimalAxioms α where
  证明: ‹Frame α›
  inf_sSup_le_iSup_inf a s := _root_.inf_sSup_eq.le
-/
theorem of [Frame α] : MinimalAxioms α where
  __ := ‹Frame α›
  inf_sSup_le_iSup_inf a s := _root_.inf_sSup_eq.le

end MinimalAxioms

-- See note [reducible non-instances]
/--
Definition of `ofMinimalAxioms` / `ofMinimalAxioms` 的定义

English:
abbreviation ofMinimalAxioms
  signature: [CompleteLattice α] (minAx : MinimalAxioms α)
  body: sSup {c | c ⊓ a <= ⊥}
  himp a b := sSup {c | c ⊓ a <= b}
  le_himp_iff _ b c :=
    ⟨fun h => (inf_le_inf_right _ h).trans (by simp [minAx.sSup_inf_eq]), fun h => le_sSup h⟩
  himp_bot _ := rfl

中文:
缩写 ofMinimalAxioms
  签名: [完备格 α] (minAx : MinimalAxioms α)
  定义体: sSup {c | c ⊓ a <= ⊥}
  himp a b := sSup {c | c ⊓ a <= b}
  le_himp_iff _ b c :=
    ⟨fun h => (inf_le_inf_right _ h).trans (by simp [minAx.sSup_inf_eq]), fun h => le_sSup h⟩
  himp_bot _ := rfl
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) : Frame α where
  compl a := sSup {c | c ⊓ a <= ⊥}
  himp a b := sSup {c | c ⊓ a <= b}
  le_himp_iff _ b c :=
    ⟨fun h => (inf_le_inf_right _ h).trans (by simp [minAx.sSup_inf_eq]), fun h => le_sSup h⟩
  himp_bot _ := rfl

end Order.Frame

namespace Order.Coframe

/-- Construct a coframe instance using the minimal amount of work needed.

This sets `a \ b := sInf {c | a ≤ b ⊔ c}` and `￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
@[to_dual existing]
/--
Definition of `ofMinimalAxioms` / `ofMinimalAxioms` 的定义

English:
abbreviation ofMinimalAxioms
  signature: [CompleteLattice α] (minAx : MinimalAxioms α)
  body: sInf {c | ⊤ <= a ⊔ c}
  sdiff a b := sInf {c | a <= b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h => (sup_le_sup_left h _).trans' (by simp [minAx.sup_sInf_eq]), fun h => sInf_le h⟩
  top_sdiff _ := rfl

中文:
缩写 ofMinimalAxioms
  签名: [完备格 α] (minAx : MinimalAxioms α)
  定义体: sInf {c | ⊤ <= a ⊔ c}
  sdiff a b := sInf {c | a <= b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h => (sup_le_sup_left h _).trans' (by simp [minAx.sup_sInf_eq]), fun h => sInf_le h⟩
  top_sdiff _ := rfl
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) : Coframe α where
  hnot a := sInf {c | ⊤ <= a ⊔ c}
  sdiff a b := sInf {c | a <= b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h => (sup_le_sup_left h _).trans' (by simp [minAx.sup_sInf_eq]), fun h => sInf_le h⟩
  top_sdiff _ := rfl

end Order.Coframe

namespace CompleteDistribLattice.MinimalAxioms

/--
theorem `of` / 定理 `of`

English:
theorem of
  given: [CompleteDistribLattice α]
  statement: MinimalAxioms α where
  proof: ‹CompleteDistribLattice α›
  inf_sSup_le_iSup_inf a s := inf_sSup_eq.le
  iInf_sup_le_sup_sInf a s := sup_sInf_eq.ge

中文:
定理 of
  条件: [完备分配格 α]
  结论: MinimalAxioms α where
  证明: ‹CompleteDistribLattice α›
  inf_sSup_le_iSup_inf a s := inf_sSup_eq.le
  iInf_sup_le_sup_sInf a s := sup_sInf_eq.ge

Depends on / 依赖: CompleteDistribLattice
-/
theorem of [CompleteDistribLattice α] : MinimalAxioms α where
  __ := ‹CompleteDistribLattice α›
  inf_sSup_le_iSup_inf a s := inf_sSup_eq.le
  iInf_sup_le_sup_sInf a s := sup_sInf_eq.ge

variable [CompleteLattice α] (minAx : MinimalAxioms α)

end MinimalAxioms

-- See note [reducible non-instances]
/--
Definition of `ofMinimalAxioms` / `ofMinimalAxioms` 的定义

English:
abbreviation ofMinimalAxioms
  signature: [CompleteLattice α] (minAx : MinimalAxioms α)
  body: Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

中文:
缩写 ofMinimalAxioms
  签名: [完备格 α] (minAx : MinimalAxioms α)
  定义体: Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

Depends on / 依赖: Frame.ofMinimalAxioms, minAx.toFrame, ofMinimalAxioms, toFrame
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompleteDistribLattice α where
  __ := Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

end CompleteDistribLattice

namespace CompletelyDistribLattice.MinimalAxioms

/--
lemma `iInf_iSup_eq'` / 引理 `iInf_iSup_eq'`

English:
lemma iInf_iSup_eq'
  given: [CompleteLattice α] (minAx : MinimalAxioms α) (f : forall a, κ a -> α)
  proof: by
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := minAx.iInf_iSup_eq _
    _ <= _ := iSup_le fun g => by
refine le_trans ?_ le_iSup _ fun a => Classical.choose (g ⟨_,

中文:
引理 iInf_iSup_eq'
  条件: [完备格 α] (minAx : MinimalAxioms α) (f : 对任意 a, κ a -> α)
  证明: by
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := minAx.iInf_iSup_eq _
    _ <= _ := iSup_le fun g => by
refine le_trans ?_ le_iSup _ fun a => Classical.choose (g ⟨_,
-/
private lemma iInf_iSup_eq' [CompleteLattice α] (minAx : MinimalAxioms α) (f : forall a, κ a -> α) :
    ⨅ i, ⨆ j, f i j = ⨆ g : forall i, κ i, ⨅ i, f i (g i) := by
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := minAx.iInf_iSup_eq _
    _ <= _ := iSup_le fun g => by
refine le_trans ?_ le_iSup _ fun a => Classical.choose (g ⟨_, a, rfl⟩).2
      refine le_iInf fun a => le_trans (iInf_le _ ⟨range (f a), a, rfl⟩) ?_
      rw [← Classical.choose_spec (g ⟨_]; rw [a]; rw [rfl⟩).2]

@[to_dual existing iInf_iSup_eq']
/--
lemma `iSup_iInf_eq` / 引理 `iSup_iInf_eq`

English:
lemma iSup_iInf_eq
  given: [CompleteLattice α] (minAx : MinimalAxioms α) (f : forall i, κ i -> α)
  proof: by
  refine le_antisymm iSup_iInf_le ?_
  rw [minAx.iInf_iSup_eq']
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : exists a, forall b, exists f, exists h : a = g f, h ▸ b = f (g f) := by
    by_contra! h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a

中文:
引理 iSup_iInf_eq
  条件: [完备格 α] (minAx : MinimalAxioms α) (f : 对任意 i, κ i -> α)
  证明: by
  refine le_antisymm iSup_iInf_le ?_
  rw [minAx.iInf_iSup_eq']
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : exists a, forall b, exists f, exists h : a = g f, h ▸ b = f (g f) := by
    by_contra! h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a
-/
private lemma iSup_iInf_eq [CompleteLattice α] (minAx : MinimalAxioms α) (f : forall i, κ i -> α) :
    ⨆ i, ⨅ j, f i j = ⨅ g : forall i, κ i, ⨆ i, f i (g i) := by
  refine le_antisymm iSup_iInf_le ?_
  rw [minAx.iInf_iSup_eq']
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : exists a, forall b, exists f, exists h : a = g f, h ▸ b = f (g f) := by
    by_contra! h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a)
  refine le_iInf fun b => ?_
  obtain ⟨h, rfl, rfl⟩ := ha b
  exact iInf_le _ _

/--
theorem `toCompleteDistribLattice` / 定理 `toCompleteDistribLattice`

English:
theorem toCompleteDistribLattice
  given: [CompleteLattice α] (minAx : MinimalAxioms α)
  proof: by
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ <= _ := by
        simp only [minAx.iInf_iSup_eq, iIn

中文:
定理 toCompleteDistribLattice
  条件: [完备格 α] (minAx : MinimalAxioms α)
  证明: by
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ <= _ := by
        simp only [minAx.iInf_iSup_eq, iIn

Depends on / 依赖: iInf_bool_eq, iInf_iSup_eq, iInf_sup_le_sup_sInf, iInf_ulift, iSup_le_iff, iSup_unique, le_biSup, minAx.iInf_iSup_eq, sSup_eq_iSup
-/
theorem toCompleteDistribLattice [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompleteDistribLattice.MinimalAxioms α where
  inf_sSup_le_iSup_inf a s := by
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ <= _ := by
        simp only [minAx.iInf_iSup_eq, iInf_ulift, iInf_bool_eq, iSup_le_iff]
        exact fun x => le_biSup _ (x (.up false)).2
  iInf_sup_le_sup_sInf a s := by
    calc
      _ <= ⨆ i : ULift.{u} Bool, ⨅ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by
        simp only [minAx.iSup_iInf_eq, iSup_ulift, iSup_bool_eq, le_iInf_iff]
        exact fun x => biInf_le _ (x (.up false)).2
      _ = _ := by simp [sInf_eq_iInf', iInf_unique, iSup_bool_eq]

/--
theorem `of` / 定理 `of`

English:
theorem of
  given: [CompletelyDistribLattice α]
  statement: MinimalAxioms α
  proof: { ‹CompletelyDistribLattice α› with }

中文:
定理 of
  条件: [余mpletelyDistrib格 α]
  结论: MinimalAxioms α
  证明: { ‹CompletelyDistribLattice α› with }

Depends on / 依赖: CompletelyDistribLattice
-/
theorem of [CompletelyDistribLattice α] : MinimalAxioms α := { ‹CompletelyDistribLattice α› with }

end MinimalAxioms

-- See note [reducible non-instances]
/--
Definition of `ofMinimalAxioms` / `ofMinimalAxioms` 的定义

English:
abbreviation ofMinimalAxioms
  signature: [CompleteLattice α] (minAx : MinimalAxioms α)
  body: fast_instance%
  { CompleteDistribLattice.ofMinimalAxioms minAx.toCompleteDistribLattice, minAx with }

中文:
缩写 ofMinimalAxioms
  签名: [完备格 α] (minAx : MinimalAxioms α)
  定义体: fast_instance%
  { CompleteDistribLattice.ofMinimalAxioms minAx.toCompleteDistribLattice, minAx with }

Depends on / 依赖: fast_instance
-/
abbrev ofMinimalAxioms [CompleteLattice α] (minAx : MinimalAxioms α) :
    CompletelyDistribLattice α := fast_instance%
  { CompleteDistribLattice.ofMinimalAxioms minAx.toCompleteDistribLattice, minAx with }

end CompletelyDistribLattice

@[to_dual]
/--
theorem `iInf_iSup_eq` / 定理 `iInf_iSup_eq`

English:
theorem iInf_iSup_eq
  given: [CompletelyDistribLattice α] {f : forall a, κ a -> α}
  proof: CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq' _

中文:
定理 iInf_iSup_eq
  条件: [余mpletelyDistrib格 α] {f : 对任意 a, κ a -> α}
  证明: CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq' _

Depends on / 依赖: CompletelyDistribLattice, CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq, MinimalAxioms, iInf_iSup_eq
-/
theorem iInf_iSup_eq [CompletelyDistribLattice α] {f : forall a, κ a -> α} :
    (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a) :=
  CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq' _

/--
theorem `biSup_iInter_of_pairwise_disjoint` / 定理 `biSup_iInter_of_pairwise_disjoint`

English:
theorem biSup_iInter_of_pairwise_disjoint
  statement: [CompletelyDistribLattice α] {ι κ : Type*}
  proof: by
  rcases hκ with ⟨j⟩
  simp_rw [iInf_iSup_eq, mem_iInter]
  refine le_antisymm
    (iSup₂_le fun i hi => le_iSup₂_of_le (fun _ => i) hi (le_iInf fun _ => le_rfl))
    (iSup₂_le fun I hI => ?_)
  by_cases! H : forall k, I k = I j
  · exact le_iSup₂_of_le (I j) (fun k => (H k) ▸ (hI k)) (iInf_le _ 

中文:
定理 biSup_i整数er_of_pairwise_disjoint
  结论: [余mpletelyDistrib格 α] {ι κ : 类型}
  证明: by
  rcases hκ with ⟨j⟩
  simp_rw [iInf_iSup_eq, mem_iInter]
  refine le_antisymm
    (iSup₂_le fun i hi => le_iSup₂_of_le (fun _ => i) hi (le_iInf fun _ => le_rfl))
    (iSup₂_le fun I hI => ?_)
  by_cases! H : forall k, I k = I j
  · exact le_iSup₂_of_le (I j) (fun k => (H k) ▸ (hI k)) (iInf_le _ 

Depends on / 依赖: bot_le, eq_bot, iInf_iSup_eq, iInf_le, le_antisymm, le_iInf, le_inf, le_rfl, mem_iInter, simp_rw
-/
theorem biSup_iInter_of_pairwise_disjoint [CompletelyDistribLattice α] {ι κ : Type*}
    [hκ : Nonempty κ] {f : ι -> α} (h : Pairwise (Disjoint on f)) (s : κ -> Set ι) :
    (⨆ i in (⋂ j, s j), f i) = ⨅ j, (⨆ i in s j, f i) := by
  rcases hκ with ⟨j⟩
  simp_rw [iInf_iSup_eq, mem_iInter]
  refine le_antisymm
    (iSup₂_le fun i hi => le_iSup₂_of_le (fun _ => i) hi (le_iInf fun _ => le_rfl))
    (iSup₂_le fun I hI => ?_)
  by_cases! H : forall k, I k = I j
  · exact le_iSup₂_of_le (I j) (fun k => (H k) ▸ (hI k)) (iInf_le _ _)
  · rcases H with ⟨k, hk⟩
    calc ⨅ l, f (I l)
    _ <= f (I k) ⊓ f (I j) := le_inf (iInf_le _ _) (iInf_le _ _)
    _ = ⊥ := (h hk).eq_bot
    _ <= _ := bot_le

instance (priority := 100) CompletelyDistribLattice.toCompleteDistribLattice
    [CompletelyDistribLattice α] : CompleteDistribLattice α where
  __ := ‹CompletelyDistribLattice α›

-- See note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toCompletelyDistribLattice [CompleteLinearOrder α] :
    CompletelyDistribLattice α where
  __ := ‹CompleteLinearOrder α›
  iInf_iSup_eq {α β} g := by
    let lhs := ⨅ a, ⨆ b, g a b
    let rhs := ⨆ h : forall a, β a, ⨅ a, g a (h a)
    suffices lhs <= rhs from le_antisymm this le_iInf_iSup
    if h : exists x, rhs < x ∧ x < lhs then
      rcases h with ⟨x, hr, hl⟩
      suffices rhs >= x from nomatch not_lt.2 this hr
      have : forall a, exists b, x < g a b := fun a =>
lt_iSup_iff.1 lt_of_not_ge fun h =>
            lt_irrefl x (lt_of_lt_of_le hl (le_trans (iInf_le _ a) h))
      choose f hf using this
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => le_of_lt (hf a)
    else
      refine le_of_not_gt fun hrl : rhs < lhs => not_le_of_gt hrl ?_
      replace h : forall x, x <= rhs ∨ lhs <= x := by
        simpa only [not_exists, not_and_or, not_or, not_lt] using h
      have : forall a, exists b, rhs < g a b := fun a =>
lt_iSup_iff.1 lt_of_lt_of_le hrl (iInf_le _ a)
      choose f hf using this
      have : forall a, lhs <= g a (f a) := fun a =>
        (h (g a (f a))).resolve_left (by simpa using hf a)
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => this _

section Frame

variable [Frame α] {s t : Set α} {a b c d : α}

/--
Instance `OrderDual.instCoframe` / 实例 `OrderDual.instCoframe`

English:
instance OrderDual.instCoframe
  signature: : Coframe αᵒᵈ where
  body: instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual]

中文:
实例 OrderDual.instCoframe
  签名: : 余frame αᵒᵈ where
  定义体: instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual]

Depends on / 依赖: instCompleteLattice
-/
instance OrderDual.instCoframe : Coframe αᵒᵈ where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual]
/--
theorem `sSup_inf_eq` / 定理 `sSup_inf_eq`

English:
theorem sSup_inf_eq
  statement: sSup s ⊓ b = ⨆ a in s, a ⊓ b
  proof: by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

@[to_dual]

中文:
定理 sSup_inf_eq
  结论: sSup s ⊓ b = ⨆ a in s, a ⊓ b
  证明: by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

@[to_dual]

Depends on / 依赖: CochainComplex, CochainComplex.of, d_comp_d, inf_comm, inf_sSup_eq, resolution
-/
theorem sSup_inf_eq : sSup s ⊓ b = ⨆ a in s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

@[to_dual]
/--
theorem `iSup_inf_eq` / 定理 `iSup_inf_eq`

English:
theorem iSup_inf_eq
  given: (f : ι -> α) (a : α)
  statement: (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
  proof: by
  rw [iSup]; rw [sSup_inf_eq]; rw [iSup_range]

@[to_dual]

中文:
定理 iSup_inf_eq
  条件: (f : ι -> α) (a : α)
  结论: (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
  证明: by
  rw [iSup]; rw [sSup_inf_eq]; rw [iSup_range]

@[to_dual]

Depends on / 依赖: iSup_range, sSup_inf_eq
-/
theorem iSup_inf_eq (f : ι -> α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup]; rw [sSup_inf_eq]; rw [iSup_range]

@[to_dual]
/--
theorem `inf_iSup_eq` / 定理 `inf_iSup_eq`

English:
theorem inf_iSup_eq
  given: (a : α) (f : ι -> α)
  statement: (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i
  proof: by
  simpa only [inf_comm] using iSup_inf_eq f a

@[to_dual]

中文:
定理 inf_iSup_eq
  条件: (a : α) (f : ι -> α)
  结论: (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i
  证明: by
  simpa only [inf_comm] using iSup_inf_eq f a

@[to_dual]

Depends on / 依赖: iSup_inf_eq, inf_comm
-/
theorem inf_iSup_eq (a : α) (f : ι -> α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a

@[to_dual]
/--
theorem `iSup₂_inf_eq` / 定理 `iSup₂_inf_eq`

English:
theorem iSup₂_inf_eq
  given: {f : forall i, κ i -> α} (a : α)
  proof: by
  simp only [iSup_inf_eq]

@[to_dual]

中文:
定理 iSup₂_inf_eq
  条件: {f : 对任意 i, κ i -> α} (a : α)
  证明: by
  simp only [iSup_inf_eq]

@[to_dual]

Depends on / 依赖: iSup_inf_eq
-/
theorem iSup₂_inf_eq {f : forall i, κ i -> α} (a : α) :
    (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a := by
  simp only [iSup_inf_eq]

@[to_dual]
/--
theorem `inf_iSup₂_eq` / 定理 `inf_iSup₂_eq`

English:
theorem inf_iSup₂_eq
  given: {f : forall i, κ i -> α} (a : α)
  proof: by
  simp only [inf_iSup_eq]

@[to_dual iSup_sdiff_eq]

中文:
定理 inf_iSup₂_eq
  条件: {f : 对任意 i, κ i -> α} (a : α)
  证明: by
  simp only [inf_iSup_eq]

@[to_dual iSup_sdiff_eq]

Depends on / 依赖: inf_iSup_eq
-/
theorem inf_iSup₂_eq {f : forall i, κ i -> α} (a : α) :
    (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j := by
  simp only [inf_iSup_eq]

@[to_dual iSup_sdiff_eq]
/--
theorem `himp_iInf_eq` / 定理 `himp_iInf_eq`

English:
theorem himp_iInf_eq
  given: {f : ι -> α}
  statement: a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x
  proof: eq_of_forall_le_iff fun b => by simp

@[to_dual sdiff_iInf_eq]

中文:
定理 himp_iInf_eq
  条件: {f : ι -> α}
  结论: a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x
  证明: eq_of_forall_le_iff fun b => by simp

@[to_dual sdiff_iInf_eq]

Depends on / 依赖: eq_of_forall_le_iff
-/
theorem himp_iInf_eq {f : ι -> α} : a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x :=
  eq_of_forall_le_iff fun b => by simp

@[to_dual sdiff_iInf_eq]
/--
theorem `iSup_himp_eq` / 定理 `iSup_himp_eq`

English:
theorem iSup_himp_eq
  given: {f : ι -> α}
  statement: (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a
  proof: eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

@[deprecated (since := "2026-07-30")] alias sdiff_iSup_eq := sdiff_iInf_eq

@[to_dual]

中文:
定理 iSup_himp_eq
  条件: {f : ι -> α}
  结论: (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a
  证明: eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

@[deprecated (since := "2026-07-30")] alias sdiff_iSup_eq := sdiff_iInf_eq

@[to_dual]

Depends on / 依赖: eq_of_forall_le_iff, inf_iSup_eq
-/
theorem iSup_himp_eq {f : ι -> α} : (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a :=
  eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

@[deprecated (since := "2026-07-30")] alias sdiff_iSup_eq := sdiff_iInf_eq

@[to_dual]
/--
theorem `iSup_inf_iSup` / 定理 `iSup_inf_iSup`

English:
theorem iSup_inf_iSup
  given: {ι ι' : Type*} {f : ι -> α} {g : ι' -> α}
  proof: by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

@[to_dual]

中文:
定理 iSup_inf_iSup
  条件: {ι ι' : 类型} {f : ι -> α} {g : ι' -> α}
  证明: by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

@[to_dual]

Depends on / 依赖: iSup_inf_eq, iSup_prod, inf_iSup_eq, simp_rw
-/
theorem iSup_inf_iSup {ι ι' : Type*} {f : ι -> α} {g : ι' -> α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

@[to_dual]
/--
theorem `biSup_inf_biSup` / 定理 `biSup_inf_biSup`

English:
theorem biSup_inf_biSup
  given: {ι ι' : Type*} {f : ι -> α} {g : ι' -> α} {s : Set ι} {t : Set ι'}
  proof: by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

@[to_dual]

中文:
定理 biSup_inf_biSup
  条件: {ι ι' : 类型} {f : ι -> α} {g : ι' -> α} {s : 集合 ι} {t : 集合 ι'}
  证明: by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

@[to_dual]

Depends on / 依赖: Equiv.Set.prod, Equiv.surjective, iSup_congr, iSup_inf_iSup, iSup_subtype, surjective
-/
theorem biSup_inf_biSup {ι ι' : Type*} {f : ι -> α} {g : ι' -> α} {s : Set ι} {t : Set ι'} :
    ((⨆ i in s, f i) ⊓ ⨆ j in t, g j) = ⨆ p in s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

@[to_dual]
/--
theorem `sSup_inf_sSup` / 定理 `sSup_inf_sSup`

English:
theorem sSup_inf_sSup
  statement: sSup s ⊓ sSup t = ⨆ p in s ×ˢ t, (p : α × α).1 ⊓ p.2
  proof: by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

@[to_dual]

中文:
定理 sSup_inf_sSup
  结论: sSup s ⊓ sSup t = ⨆ p in s ×ˢ t, (p : α × α).1 ⊓ p.2
  证明: by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

@[to_dual]

Depends on / 依赖: biSup_inf_biSup, sSup_eq_iSup
-/
theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p in s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

@[to_dual]
/--
theorem `biSup_inter_of_pairwise_disjoint` / 定理 `biSup_inter_of_pairwise_disjoint`

English:
theorem biSup_inter_of_pairwise_disjoint
  statement: {ι : Type*} {f : ι -> α}
  proof: by
  rw [biSup_inf_biSup]
  refine le_antisymm
    (iSup₂_le fun i ⟨his, hit⟩ => le_iSup₂_of_le ⟨i, i⟩ ⟨his, hit⟩ (le_inf le_rfl le_rfl))
    (iSup₂_le fun ⟨i, j⟩ ⟨his, hjs⟩ => ?_)
  by_cases hij : i = j
  · exact le_iSup₂_of_le i ⟨his, hij ▸ hjs⟩ inf_le_left
  · simp [h hij |>.eq_bot]

@[to_dual]

中文:
定理 biSup_inter_of_pairwise_disjoint
  结论: {ι : 类型} {f : ι -> α}
  证明: by
  rw [biSup_inf_biSup]
  refine le_antisymm
    (iSup₂_le fun i ⟨his, hit⟩ => le_iSup₂_of_le ⟨i, i⟩ ⟨his, hit⟩ (le_inf le_rfl le_rfl))
    (iSup₂_le fun ⟨i, j⟩ ⟨his, hjs⟩ => ?_)
  by_cases hij : i = j
  · exact le_iSup₂_of_le i ⟨his, hij ▸ hjs⟩ inf_le_left
  · simp [h hij |>.eq_bot]

@[to_dual]

Depends on / 依赖: biSup_inf_biSup, eq_bot, inf_le_left, le_antisymm, le_inf, le_rfl
-/
theorem biSup_inter_of_pairwise_disjoint {ι : Type*} {f : ι -> α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⨆ i in (s inter t), f i) = (⨆ i in s, f i) ⊓ (⨆ i in t, f i) := by
  rw [biSup_inf_biSup]
  refine le_antisymm
    (iSup₂_le fun i ⟨his, hit⟩ => le_iSup₂_of_le ⟨i, i⟩ ⟨his, hit⟩ (le_inf le_rfl le_rfl))
    (iSup₂_le fun ⟨i, j⟩ ⟨his, hjs⟩ => ?_)
  by_cases hij : i = j
  · exact le_iSup₂_of_le i ⟨his, hij ▸ hjs⟩ inf_le_left
  · simp [h hij |>.eq_bot]

@[to_dual]
/--
theorem `iSup_disjoint_iff` / 定理 `iSup_disjoint_iff`

English:
theorem iSup_disjoint_iff
  given: {f : ι -> α}
  statement: Disjoint (⨆ i, f i) a ↔ forall i, Disjoint (f i) a
  proof: by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

@[to_dual]

中文:
定理 iSup_disjoint_iff
  条件: {f : ι -> α}
  结论: Disjoint (⨆ i, f i) a ↔ 对任意 i, Disjoint (f i) a
  证明: by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

@[to_dual]

Depends on / 依赖: disjoint_iff, iSup_eq_bot, iSup_inf_eq
-/
theorem iSup_disjoint_iff {f : ι -> α} : Disjoint (⨆ i, f i) a ↔ forall i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

@[to_dual]
/--
theorem `disjoint_iSup_iff` / 定理 `disjoint_iSup_iff`

English:
theorem disjoint_iSup_iff
  given: {f : ι -> α}
  statement: Disjoint a (⨆ i, f i) ↔ forall i, Disjoint a (f i)
  proof: by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

@[to_dual]

中文:
定理 disjoint_iSup_iff
  条件: {f : ι -> α}
  结论: Disjoint a (⨆ i, f i) ↔ 对任意 i, Disjoint a (f i)
  证明: by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

@[to_dual]

Depends on / 依赖: disjoint_comm, iSup_disjoint_iff
-/
theorem disjoint_iSup_iff {f : ι -> α} : Disjoint a (⨆ i, f i) ↔ forall i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

@[to_dual]
/--
theorem `iSup₂_disjoint_iff` / 定理 `iSup₂_disjoint_iff`

English:
theorem iSup₂_disjoint_iff
  given: {f : forall i, κ i -> α}
  proof: by
  simp_rw [iSup_disjoint_iff]

@[to_dual]

中文:
定理 iSup₂_disjoint_iff
  条件: {f : 对任意 i, κ i -> α}
  证明: by
  simp_rw [iSup_disjoint_iff]

@[to_dual]

Depends on / 依赖: iSup_disjoint_iff, simp_rw
-/
theorem iSup₂_disjoint_iff {f : forall i, κ i -> α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ forall i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]

@[to_dual]
/--
theorem `disjoint_iSup₂_iff` / 定理 `disjoint_iSup₂_iff`

English:
theorem disjoint_iSup₂_iff
  given: {f : forall i, κ i -> α}
  proof: by
  simp_rw [disjoint_iSup_iff]

@[to_dual]

中文:
定理 disjoint_iSup₂_iff
  条件: {f : 对任意 i, κ i -> α}
  证明: by
  simp_rw [disjoint_iSup_iff]

@[to_dual]

Depends on / 依赖: disjoint_iSup_iff, simp_rw
-/
theorem disjoint_iSup₂_iff {f : forall i, κ i -> α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ forall i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]

@[to_dual]
/--
theorem `sSup_disjoint_iff` / 定理 `sSup_disjoint_iff`

English:
theorem sSup_disjoint_iff
  given: {s : Set α}
  statement: Disjoint (sSup s) a ↔ forall b in s, Disjoint b a
  proof: by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

@[to_dual]

中文:
定理 sSup_disjoint_iff
  条件: {s : 集合 α}
  结论: Disjoint (sSup s) a ↔ 对任意 b in s, Disjoint b a
  证明: by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

@[to_dual]

Depends on / 依赖: disjoint_iff, iSup_eq_bot, sSup_inf_eq
-/
theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ forall b in s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

@[to_dual]
/--
theorem `disjoint_sSup_iff` / 定理 `disjoint_sSup_iff`

English:
theorem disjoint_sSup_iff
  given: {s : Set α}
  statement: Disjoint a (sSup s) ↔ forall b in s, Disjoint a b
  proof: by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

@[to_dual]

中文:
定理 disjoint_sSup_iff
  条件: {s : 集合 α}
  结论: Disjoint a (sSup s) ↔ 对任意 b in s, Disjoint a b
  证明: by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

@[to_dual]

Depends on / 依赖: disjoint_comm, sSup_disjoint_iff
-/
theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ forall b in s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

@[to_dual]
/--
theorem `iSup_inf_of_monotone` / 定理 `iSup_inf_of_monotone`

English:
theorem iSup_inf_of_monotone
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> α}
  proof: by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· <= ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

@[to_dual]

中文:
定理 iSup_inf_of_monotone
  结论: {ι : 类型} [预序 ι] [IsDirectedOrder ι] {f g : ι -> α}
  证明: by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· <= ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

@[to_dual]

Depends on / 依赖: antisymm, directed_of, iSup_inf_iSup, iSup_mono, inf_le_inf, le_iSup_inf_iSup
-/
theorem iSup_inf_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> α}
    (hf : Monotone f) (hg : Monotone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· <= ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

@[to_dual]
/--
theorem `iSup_inf_of_antitone` / 定理 `iSup_inf_of_antitone`

English:
theorem iSup_inf_of_antitone
  statement: {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> α}
  proof: @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

中文:
定理 iSup_inf_of_antitone
  结论: {ι : 类型} [预序 ι] [IsCodirectedOrder ι] {f g : ι -> α}
  证明: @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

Depends on / 依赖: dual_left, hf.dual_left, hg.dual_left, iSup_inf_of_monotone
-/
theorem iSup_inf_of_antitone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> α}
    (hf : Antitone f) (hg : Antitone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

/--
theorem `himp_eq_sSup` / 定理 `himp_eq_sSup`

English:
theorem himp_eq_sSup
  statement: a ⇨ b = sSup {w | w ⊓ a <= b}
  proof: (isGreatest_himp a b).isLUB.sSup_eq.symm

中文:
定理 himp_eq_sSup
  结论: a ⇨ b = sSup {w | w ⊓ a <= b}
  证明: (isGreatest_himp a b).isLUB.sSup_eq.symm

Depends on / 依赖: isGreatest_himp, isLUB.sSup_eq.symm, sSup_eq
-/
theorem himp_eq_sSup : a ⇨ b = sSup {w | w ⊓ a <= b} :=
  (isGreatest_himp a b).isLUB.sSup_eq.symm

/--
theorem `compl_eq_sSup_disjoint` / 定理 `compl_eq_sSup_disjoint`

English:
theorem compl_eq_sSup_disjoint
  statement: aᶜ = sSup {w | Disjoint w a}
  proof: (isGreatest_compl a).isLUB.sSup_eq.symm

中文:
定理 compl_eq_sSup_disjoint
  结论: aᶜ = sSup {w | Disjoint w a}
  证明: (isGreatest_compl a).isLUB.sSup_eq.symm

Depends on / 依赖: isGreatest_compl, isLUB.sSup_eq.symm, sSup_eq
-/
theorem compl_eq_sSup_disjoint : aᶜ = sSup {w | Disjoint w a} :=
  (isGreatest_compl a).isLUB.sSup_eq.symm

/--
lemma `himp_le_iff` / 引理 `himp_le_iff`

English:
lemma himp_le_iff
  statement: a ⇨ b <= c ↔ forall d, d ⊓ a <= b -> d <= c
  proof: by simp [himp_eq_sSup]

中文:
引理 himp_le_iff
  结论: a ⇨ b <= c ↔ 对任意 d, d ⊓ a <= b -> d <= c
  证明: by simp [himp_eq_sSup]

Depends on / 依赖: himp_eq_sSup
-/
lemma himp_le_iff : a ⇨ b <= c ↔ forall d, d ⊓ a <= b -> d <= c := by simp [himp_eq_sSup]

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) Order.Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair]; rw [← sSup_pair]; rw [inf_sSup_eq]; rw [← sSup_image]; rw [image_pair]

/--
Instance `Prod.instFrame` / 实例 `Prod.instFrame`

English:
instance Prod.instFrame
  signature: [Frame β]
  body: instCompleteLattice
  __ := instHeytingAlgebra

中文:
实例 积类型.instFrame
  签名: [框架 β]
  定义体: instCompleteLattice
  __ := instHeytingAlgebra

Depends on / 依赖: instCompleteLattice
-/
instance Prod.instFrame [Frame β] : Frame (α × β) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

/--
Instance `Pi.instFrame` / 实例 `Pi.instFrame`

English:
instance Pi.instFrame
  signature: {ι : Type*} {π : ι -> Type*} [forall i, Frame (π i)]
  body: instCompleteLattice
  __ := instHeytingAlgebra

中文:
实例 依赖函数类型.instFrame
  签名: {ι : 类型} {π : ι -> 类型} [对任意 i, 框架 (π i)]
  定义体: instCompleteLattice
  __ := instHeytingAlgebra

Depends on / 依赖: instCompleteLattice
-/
instance Pi.instFrame {ι : Type*} {π : ι -> Type*} [forall i, Frame (π i)] : Frame (forall i, π i) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b c d : α}

@[to_dual existing]
/--
Instance `OrderDual.instFrame` / 实例 `OrderDual.instFrame`

English:
instance OrderDual.instFrame
  signature: : Frame αᵒᵈ where
  body: instCompleteLattice
  __ := instHeytingAlgebra

中文:
实例 OrderDual.instFrame
  签名: : 框架 αᵒᵈ where
  定义体: instCompleteLattice
  __ := instHeytingAlgebra

Depends on / 依赖: instCompleteLattice
-/
instance OrderDual.instFrame : Frame αᵒᵈ where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

/--
theorem `sdiff_eq_sInf` / 定理 `sdiff_eq_sInf`

English:
theorem sdiff_eq_sInf
  statement: a \ b = sInf {w | a <= b ⊔ w}
  proof: (isLeast_sdiff a b).isGLB.sInf_eq.symm

中文:
定理 sdiff_eq_sInf
  结论: a \ b = sInf {w | a <= b ⊔ w}
  证明: (isLeast_sdiff a b).isGLB.sInf_eq.symm

Depends on / 依赖: isGLB.sInf_eq.symm, isLeast_sdiff, sInf_eq
-/
theorem sdiff_eq_sInf : a \ b = sInf {w | a <= b ⊔ w} :=
  (isLeast_sdiff a b).isGLB.sInf_eq.symm

/--
theorem `hnot_eq_sInf_codisjoint` / 定理 `hnot_eq_sInf_codisjoint`

English:
theorem hnot_eq_sInf_codisjoint
  statement: ￢a = sInf {w | Codisjoint a w}
  proof: (isLeast_hnot a).isGLB.sInf_eq.symm

中文:
定理 hnot_eq_sInf_codisjoint
  结论: ￢a = sInf {w | Codisjoint a w}
  证明: (isLeast_hnot a).isGLB.sInf_eq.symm

Depends on / 依赖: isGLB.sInf_eq.symm, isLeast_hnot, sInf_eq
-/
theorem hnot_eq_sInf_codisjoint : ￢a = sInf {w | Codisjoint a w} :=
  (isLeast_hnot a).isGLB.sInf_eq.symm

/--
lemma `le_sdiff_iff` / 引理 `le_sdiff_iff`

English:
lemma le_sdiff_iff
  statement: a <= b \ c ↔ forall d, b <= c ⊔ d -> a <= d
  proof: by simp [sdiff_eq_sInf]

@[to_dual existing]

中文:
引理 le_sdiff_iff
  结论: a <= b \ c ↔ 对任意 d, b <= c ⊔ d -> a <= d
  证明: by simp [sdiff_eq_sInf]

@[to_dual existing]

Depends on / 依赖: sdiff_eq_sInf
-/
lemma le_sdiff_iff : a <= b \ c ↔ forall d, b <= c ⊔ d -> a <= d := by simp [sdiff_eq_sInf]

@[to_dual existing]
/--
Instance `Prod.instCoframe` / 实例 `Prod.instCoframe`

English:
instance Prod.instCoframe
  signature: [Coframe β]
  body: instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual existing]

中文:
实例 积类型.instCoframe
  签名: [余frame β]
  定义体: instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual existing]

Depends on / 依赖: instCompleteLattice
-/
instance Prod.instCoframe [Coframe β] : Coframe (α × β) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

@[to_dual existing]
/--
Instance `Pi.instCoframe` / 实例 `Pi.instCoframe`

English:
instance Pi.instCoframe
  signature: {ι : Type*} {π : ι -> Type*} [forall i, Coframe (π i)]
  body: instCompleteLattice
  __ := instCoheytingAlgebra

中文:
实例 依赖函数类型.instCoframe
  签名: {ι : 类型} {π : ι -> 类型} [对任意 i, 余frame (π i)]
  定义体: instCompleteLattice
  __ := instCoheytingAlgebra

Depends on / 依赖: instCompleteLattice
-/
instance Pi.instCoframe {ι : Type*} {π : ι -> Type*} [forall i, Coframe (π i)] : Coframe (forall i, π i) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra

end Coframe

section CompleteDistribLattice

/--
Instance `OrderDual.instCompleteDistribLattice` / 实例 `OrderDual.instCompleteDistribLattice`

English:
instance OrderDual.instCompleteDistribLattice
  signature: [CompleteDistribLattice α]
  body: instFrame
  __ := instCoframe

中文:
实例 OrderDual.instCompleteDistribLattice
  签名: [完备分配格 α]
  定义体: instFrame
  __ := instCoframe

Depends on / 依赖: instFrame
-/
instance OrderDual.instCompleteDistribLattice [CompleteDistribLattice α] :
    CompleteDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe

/--
Instance `Prod.instCompleteDistribLattice` / 实例 `Prod.instCompleteDistribLattice`

English:
instance Prod.instCompleteDistribLattice
  signature: [CompleteDistribLattice α] [CompleteDistribLattice β]
  body: instFrame
  __ := instCoframe

中文:
实例 积类型.instCompleteDistribLattice
  签名: [完备分配格 α] [完备分配格 β]
  定义体: instFrame
  __ := instCoframe

Depends on / 依赖: instFrame
-/
instance Prod.instCompleteDistribLattice [CompleteDistribLattice α] [CompleteDistribLattice β] :
    CompleteDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe

/--
Instance `Pi.instCompleteDistribLattice` / 实例 `Pi.instCompleteDistribLattice`

English:
instance Pi.instCompleteDistribLattice
  signature: {ι : Type*} {π : ι -> Type*}
  body: instFrame
  __ := instCoframe

中文:
实例 依赖函数类型.instCompleteDistribLattice
  签名: {ι : 类型} {π : ι -> 类型}
  定义体: instFrame
  __ := instCoframe

Depends on / 依赖: instFrame
-/
instance Pi.instCompleteDistribLattice {ι : Type*} {π : ι -> Type*}
    [forall i, CompleteDistribLattice (π i)] : CompleteDistribLattice (forall i, π i) where
  __ := instFrame
  __ := instCoframe

end CompleteDistribLattice

section CompletelyDistribLattice

/--
Instance `OrderDual.instCompletelyDistribLattice` / 实例 `OrderDual.instCompletelyDistribLattice`

English:
instance OrderDual.instCompletelyDistribLattice
  signature: [CompletelyDistribLattice α]
  body: instFrame
  __ := instCoframe
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)

中文:
实例 OrderDual.instCompletelyDistribLattice
  签名: [余mpletelyDistrib格 α]
  定义体: instFrame
  __ := instCoframe
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)

Depends on / 依赖: instFrame
-/
instance OrderDual.instCompletelyDistribLattice [CompletelyDistribLattice α] :
    CompletelyDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)

/--
Instance `Prod.instCompletelyDistribLattice` / 实例 `Prod.instCompletelyDistribLattice`

English:
instance Prod.instCompletelyDistribLattice
  signature: [CompletelyDistribLattice α]
  body: instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]

中文:
实例 积类型.instCompletelyDistribLattice
  签名: [余mpletelyDistrib格 α]
  定义体: instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]

Depends on / 依赖: instFrame
-/
instance Prod.instCompletelyDistribLattice [CompletelyDistribLattice α]
    [CompletelyDistribLattice β] : CompletelyDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]

/--
Instance `Pi.instCompletelyDistribLattice` / 实例 `Pi.instCompletelyDistribLattice`

English:
instance Pi.instCompletelyDistribLattice
  signature: {ι : Type*} {π : ι -> Type*}
  body: instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

中文:
实例 依赖函数类型.instCompletelyDistribLattice
  签名: {ι : 类型} {π : ι -> 类型}
  定义体: instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

Depends on / 依赖: instFrame
-/
instance Pi.instCompletelyDistribLattice {ι : Type*} {π : ι -> Type*}
    [forall i, CompletelyDistribLattice (π i)] : CompletelyDistribLattice (forall i, π i) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

end CompletelyDistribLattice

-- We do not directly extend `CompleteDistribLattice` to avoid having the `hnot` field
/--
Definition of `CompleteBooleanAlgebra` / `CompleteBooleanAlgebra` 的定义

English:
class CompleteBooleanAlgebra
  parameters: (α)
  extends: CompleteLattice α, BooleanAlgebra α
  (no additional axioms)

中文:
类 完备布尔代数
  参数: (α)
  继承: 完备格 α, 布尔代数 α
  (无附加公理)
-/
class CompleteBooleanAlgebra (α) extends CompleteLattice α, BooleanAlgebra α

-- See note [lower instance priority]
instance (priority := 100) CompleteBooleanAlgebra.toCompleteDistribLattice
    [CompleteBooleanAlgebra α] : CompleteDistribLattice α where
  __ := ‹CompleteBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra

/--
Instance `Prod.instCompleteBooleanAlgebra` / 实例 `Prod.instCompleteBooleanAlgebra`

English:
instance Prod.instCompleteBooleanAlgebra
  signature: [CompleteBooleanAlgebra α] [CompleteBooleanAlgebra β]
  body: instBooleanAlgebra
  __ := instCompleteDistribLattice

中文:
实例 积类型.instComplete布尔eanAlgebra
  签名: [完备布尔代数 α] [完备布尔代数 β]
  定义体: instBooleanAlgebra
  __ := instCompleteDistribLattice

Depends on / 依赖: instBooleanAlgebra
-/
instance Prod.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] [CompleteBooleanAlgebra β] :
    CompleteBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

/--
Instance `Pi.instCompleteBooleanAlgebra` / 实例 `Pi.instCompleteBooleanAlgebra`

English:
instance Pi.instCompleteBooleanAlgebra
  signature: {ι : Type*} {π : ι -> Type*}
  body: instBooleanAlgebra
  __ := instCompleteDistribLattice

中文:
实例 依赖函数类型.instComplete布尔eanAlgebra
  签名: {ι : 类型} {π : ι -> 类型}
  定义体: instBooleanAlgebra
  __ := instCompleteDistribLattice

Depends on / 依赖: instBooleanAlgebra
-/
instance Pi.instCompleteBooleanAlgebra {ι : Type*} {π : ι -> Type*}
    [forall i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (forall i, π i) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

/--
Instance `OrderDual.instCompleteBooleanAlgebra` / 实例 `OrderDual.instCompleteBooleanAlgebra`

English:
instance OrderDual.instCompleteBooleanAlgebra
  signature: [CompleteBooleanAlgebra α]
  body: instBooleanAlgebra
  __ := instCompleteDistribLattice

中文:
实例 OrderDual.instComplete布尔eanAlgebra
  签名: [完备布尔代数 α]
  定义体: instBooleanAlgebra
  __ := instCompleteDistribLattice

Depends on / 依赖: instBooleanAlgebra
-/
instance OrderDual.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] :
    CompleteBooleanAlgebra αᵒᵈ where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {s : Set α} {f : ι -> α}

/--
theorem `compl_iInf` / 定理 `compl_iInf`

English:
theorem compl_iInf
  statement: (iInf f)ᶜ = ⨆ i, (f i)ᶜ
  proof: le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (Compl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)

中文:
定理 compl_iInf
  结论: (iInf f)ᶜ = ⨆ i, (f i)ᶜ
  证明: le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (Compl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)

Depends on / 依赖: Compl.compl, compl_le_compl, compl_le_of_compl_le, iInf_le, iSup_le, le_antisymm, le_iInf, le_iSup
-/
theorem compl_iInf : (iInf f)ᶜ = ⨆ i, (f i)ᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (Compl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)

/--
theorem `compl_iSup` / 定理 `compl_iSup`

English:
theorem compl_iSup
  statement: (iSup f)ᶜ = ⨅ i, (f i)ᶜ
  proof: compl_injective (by simp [compl_iInf])

中文:
定理 compl_iSup
  结论: (iSup f)ᶜ = ⨅ i, (f i)ᶜ
  证明: compl_injective (by simp [compl_iInf])

Depends on / 依赖: compl_iInf, compl_injective
-/
theorem compl_iSup : (iSup f)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_injective (by simp [compl_iInf])

/--
theorem `compl_sInf` / 定理 `compl_sInf`

English:
theorem compl_sInf
  statement: (sInf s)ᶜ = ⨆ i in s, iᶜ
  proof: by simp only [sInf_eq_iInf, compl_iInf]

中文:
定理 compl_sInf
  结论: (sInf s)ᶜ = ⨆ i in s, iᶜ
  证明: by simp only [sInf_eq_iInf, compl_iInf]

Depends on / 依赖: compl_iInf, sInf_eq_iInf
-/
theorem compl_sInf : (sInf s)ᶜ = ⨆ i in s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]

/--
theorem `compl_sSup` / 定理 `compl_sSup`

English:
theorem compl_sSup
  statement: (sSup s)ᶜ = ⨅ i in s, iᶜ
  proof: by simp only [sSup_eq_iSup, compl_iSup]

中文:
定理 compl_sSup
  结论: (sSup s)ᶜ = ⨅ i in s, iᶜ
  证明: by simp only [sSup_eq_iSup, compl_iSup]

Depends on / 依赖: compl_iSup, sSup_eq_iSup
-/
theorem compl_sSup : (sSup s)ᶜ = ⨅ i in s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]

/--
theorem `compl_sInf'` / 定理 `compl_sInf'`

English:
theorem compl_sInf'
  statement: (sInf s)ᶜ = sSup (Compl.compl '' s)
  proof: compl_sInf.trans sSup_image.symm

中文:
定理 compl_sInf'
  结论: (sInf s)ᶜ = sSup (补集.compl '' s)
  证明: compl_sInf.trans sSup_image.symm

Depends on / 依赖: compl_sInf, compl_sInf.trans, sSup_image, sSup_image.symm
-/
theorem compl_sInf' : (sInf s)ᶜ = sSup (Compl.compl '' s) :=
  compl_sInf.trans sSup_image.symm

/--
theorem `compl_sSup'` / 定理 `compl_sSup'`

English:
theorem compl_sSup'
  statement: (sSup s)ᶜ = sInf (Compl.compl '' s)
  proof: compl_sSup.trans sInf_image.symm

中文:
定理 compl_sSup'
  结论: (sSup s)ᶜ = sInf (补集.compl '' s)
  证明: compl_sSup.trans sInf_image.symm

Depends on / 依赖: compl_sSup, compl_sSup.trans, sInf_image, sInf_image.symm
-/
theorem compl_sSup' : (sSup s)ᶜ = sInf (Compl.compl '' s) :=
  compl_sSup.trans sInf_image.symm

section symmDiff

open scoped symmDiff

/--
theorem `iSup_symmDiff_iSup_le` / 定理 `iSup_symmDiff_iSup_le`

English:
theorem iSup_symmDiff_iSup_le
  given: {g : ι -> α}
  statement: (⨆ i, f i) ∆ (⨆ i, g i) <= ⨆ i, ((f i) ∆ (g i))
  proof: by
  simp_rw [symmDiff_le_iff, ← iSup_sup_eq]
  exact ⟨iSup_mono fun i => sup_comm (g i) _ ▸ le_symmDiff_sup_right ..,
    iSup_mono fun i => sup_comm (f i) _ ▸ symmDiff_comm (f i) _ ▸ le_symmDiff_sup_right ..⟩

中文:
定理 iSup_symmDiff_iSup_le
  条件: {g : ι -> α}
  结论: (⨆ i, f i) ∆ (⨆ i, g i) <= ⨆ i, ((f i) ∆ (g i))
  证明: by
  simp_rw [symmDiff_le_iff, ← iSup_sup_eq]
  exact ⟨iSup_mono fun i => sup_comm (g i) _ ▸ le_symmDiff_sup_right ..,
    iSup_mono fun i => sup_comm (f i) _ ▸ symmDiff_comm (f i) _ ▸ le_symmDiff_sup_right ..⟩

Depends on / 依赖: iSup_mono, iSup_sup_eq, le_symmDiff_sup_right, simp_rw, sup_comm, symmDiff_comm, symmDiff_le_iff
-/
theorem iSup_symmDiff_iSup_le {g : ι -> α} : (⨆ i, f i) ∆ (⨆ i, g i) <= ⨆ i, ((f i) ∆ (g i)) := by
  simp_rw [symmDiff_le_iff, ← iSup_sup_eq]
  exact ⟨iSup_mono fun i => sup_comm (g i) _ ▸ le_symmDiff_sup_right ..,
    iSup_mono fun i => sup_comm (f i) _ ▸ symmDiff_comm (f i) _ ▸ le_symmDiff_sup_right ..⟩

/--
theorem `iSup_symmDiff_le` / 定理 `iSup_symmDiff_le`

English:
theorem iSup_symmDiff_le
  given: [Nonempty ι] {a : α}
  statement: (⨆ i, f i) ∆ a <= ⨆ i, f i ∆ a
  proof: by
  simpa [iSup_const] using iSup_symmDiff_iSup_le (g := fun _ : ι => a)

中文:
定理 iSup_symmDiff_le
  条件: [非空 ι] {a : α}
  结论: (⨆ i, f i) ∆ a <= ⨆ i, f i ∆ a
  证明: by
  simpa [iSup_const] using iSup_symmDiff_iSup_le (g := fun _ : ι => a)

Depends on / 依赖: iSup_const, iSup_symmDiff_iSup_le
-/
theorem iSup_symmDiff_le [Nonempty ι] {a : α} : (⨆ i, f i) ∆ a <= ⨆ i, f i ∆ a := by
  simpa [iSup_const] using iSup_symmDiff_iSup_le (g := fun _ : ι => a)

/--
theorem `symmDiff_iSup_le` / 定理 `symmDiff_iSup_le`

English:
theorem symmDiff_iSup_le
  given: [Nonempty ι] {a : α}
  statement: a ∆ (⨆ i, f i) <= ⨆ i, a ∆ f i
  proof: by
  simpa [symmDiff_comm] using iSup_symmDiff_le (a := a)

中文:
定理 symmDiff_iSup_le
  条件: [非空 ι] {a : α}
  结论: a ∆ (⨆ i, f i) <= ⨆ i, a ∆ f i
  证明: by
  simpa [symmDiff_comm] using iSup_symmDiff_le (a := a)

Depends on / 依赖: iSup_symmDiff_le, symmDiff_comm
-/
theorem symmDiff_iSup_le [Nonempty ι] {a : α} : a ∆ (⨆ i, f i) <= ⨆ i, a ∆ f i := by
  simpa [symmDiff_comm] using iSup_symmDiff_le (a := a)

/--
theorem `sSup_symmDiff_le` / 定理 `sSup_symmDiff_le`

English:
theorem sSup_symmDiff_le
  given: (hs : s.Nonempty) {a : α}
  statement: sSup s ∆ a <= sSup ((· ∆ a) '' s)
  proof: by
  rw [sSup_image']; rw [sSup_eq_iSup']
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  exact iSup_symmDiff_le

中文:
定理 sSup_symmDiff_le
  条件: (hs : s.非空) {a : α}
  结论: sSup s ∆ a <= sSup ((· ∆ a) '' s)
  证明: by
  rw [sSup_image']; rw [sSup_eq_iSup']
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  exact iSup_symmDiff_le

Depends on / 依赖: Nonempty, Set.nonempty_coe_sort.mpr, iSup_symmDiff_le, nonempty_coe_sort, sSup_eq_iSup, sSup_image
-/
theorem sSup_symmDiff_le (hs : s.Nonempty) {a : α} : sSup s ∆ a <= sSup ((· ∆ a) '' s) := by
  rw [sSup_image']; rw [sSup_eq_iSup']
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  exact iSup_symmDiff_le

/--
theorem `symmDiff_sSup_le` / 定理 `symmDiff_sSup_le`

English:
theorem symmDiff_sSup_le
  given: (hs : s.Nonempty) {a : α}
  statement: a ∆ sSup s <= sSup ((a ∆ ·) '' s)
  proof: by
  simpa [symmDiff_comm] using sSup_symmDiff_le (a := a) hs

中文:
定理 symmDiff_sSup_le
  条件: (hs : s.非空) {a : α}
  结论: a ∆ sSup s <= sSup ((a ∆ ·) '' s)
  证明: by
  simpa [symmDiff_comm] using sSup_symmDiff_le (a := a) hs

Depends on / 依赖: sSup_symmDiff_le, symmDiff_comm
-/
theorem symmDiff_sSup_le (hs : s.Nonempty) {a : α} : a ∆ sSup s <= sSup ((a ∆ ·) '' s) := by
  simpa [symmDiff_comm] using sSup_symmDiff_le (a := a) hs

/--
theorem `sSup_symmDiff_sSup_le` / 定理 `sSup_symmDiff_sSup_le`

English:
theorem sSup_symmDiff_sSup_le
  given: {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  rw [sSup_image2]
  calc
  _ <= ⨆ a in s, a ∆ sSup t := by simpa [sSup_image] using sSup_symmDiff_le hs
  _ <= _ := iSup_mono fun a => iSup_mono fun _ => by simpa [sSup_image] using symmDiff_sSup_le ht

中文:
定理 sSup_symmDiff_sSup_le
  条件: {s t : 集合 α} (hs : s.非空) (ht : t.非空)
  证明: by
  rw [sSup_image2]
  calc
  _ <= ⨆ a in s, a ∆ sSup t := by simpa [sSup_image] using sSup_symmDiff_le hs
  _ <= _ := iSup_mono fun a => iSup_mono fun _ => by simpa [sSup_image] using symmDiff_sSup_le ht

Depends on / 依赖: iSup_mono, sSup_image, sSup_image2, sSup_symmDiff_le, symmDiff_sSup_le
-/
theorem sSup_symmDiff_sSup_le {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup s ∆ sSup t <= sSup (image2 (· ∆ ·) s t) := by
  rw [sSup_image2]
  calc
  _ <= ⨆ a in s, a ∆ sSup t := by simpa [sSup_image] using sSup_symmDiff_le hs
  _ <= _ := iSup_mono fun a => iSup_mono fun _ => by simpa [sSup_image] using symmDiff_sSup_le ht

/--
theorem `biSup_symmDiff_biSup_le` / 定理 `biSup_symmDiff_biSup_le`

English:
theorem biSup_symmDiff_biSup_le
  given: {p : ι -> Prop} {f g : (i : ι) -> p i -> α}
  proof: le_trans iSup_symmDiff_iSup_le iSup_mono fun _ => iSup_symmDiff_iSup_le

中文:
定理 biSup_symmDiff_biSup_le
  条件: {p : ι -> 命题} {f g : (i : ι) -> p i -> α}
  证明: le_trans iSup_symmDiff_iSup_le iSup_mono fun _ => iSup_symmDiff_iSup_le

Depends on / 依赖: iSup_mono, iSup_symmDiff_iSup_le, le_trans
-/
theorem biSup_symmDiff_biSup_le {p : ι -> Prop} {f g : (i : ι) -> p i -> α} :
    (⨆ i, ⨆ (h : p i), f i h) ∆ (⨆ i, ⨆ (h : p i), g i h) <=
    ⨆ i, ⨆ (h : p i), ((f i h) ∆ (g i h)) :=
le_trans iSup_symmDiff_iSup_le iSup_mono fun _ => iSup_symmDiff_iSup_le

end symmDiff

end CompleteBooleanAlgebra

-- We do not directly extend `CompletelyDistribLattice` to avoid having the `hnot` field
/--
Definition of `CompleteAtomicBooleanAlgebra` / `CompleteAtomicBooleanAlgebra` 的定义

English:
class CompleteAtomicBooleanAlgebra
  parameters: (α : Type u)
  extends: CompleteBooleanAlgebra α
  axioms and operations (1):
    - iInf_iSup_eq({ι : Type u} {κ : ι -> Type u} (f : forall a, κ a -> α)) : (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a)

中文:
类 余mpleteAtomic布尔ean代数
  参数: (α : 类型u)
  继承: 完备布尔代数 α
  公理与运算 (1 个):
    - iInf_iSup_eq({ι : 类型u} {κ : ι -> 类型u} (f : 对任意 a, κ a -> α)) : (⨅ a, ⨆ b, f a b) = ⨆ g : 对任意 a, κ a, ⨅ a, f a (g a)
-/
class CompleteAtomicBooleanAlgebra (α : Type u) extends CompleteBooleanAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι -> Type u} (f : forall a, κ a -> α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : forall a, κ a, ⨅ a, f a (g a)

-- See note [lower instance priority]
instance (priority := 100) CompleteAtomicBooleanAlgebra.toCompletelyDistribLattice
    [CompleteAtomicBooleanAlgebra α] : CompletelyDistribLattice α where
  __ := ‹CompleteAtomicBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra

/--
Instance `Prod.instCompleteAtomicBooleanAlgebra` / 实例 `Prod.instCompleteAtomicBooleanAlgebra`

English:
instance Prod.instCompleteAtomicBooleanAlgebra
  signature: [CompleteAtomicBooleanAlgebra α]
  body: instBooleanAlgebra
  __ := instCompletelyDistribLattice

中文:
实例 积类型.instCompleteAtomic布尔eanAlgebra
  签名: [余mpleteAtomic布尔ean代数 α]
  定义体: instBooleanAlgebra
  __ := instCompletelyDistribLattice

Depends on / 依赖: instBooleanAlgebra
-/
instance Prod.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α]
    [CompleteAtomicBooleanAlgebra β] : CompleteAtomicBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompletelyDistribLattice

/--
Instance `Pi.instCompleteAtomicBooleanAlgebra` / 实例 `Pi.instCompleteAtomicBooleanAlgebra`

English:
instance Pi.instCompleteAtomicBooleanAlgebra
  signature: {ι : Type*} {π : ι -> Type*}
  body: Pi.instCompleteBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]

中文:
实例 依赖函数类型.instCompleteAtomic布尔eanAlgebra
  签名: {ι : 类型} {π : ι -> 类型}
  定义体: Pi.instCompleteBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]

Depends on / 依赖: Pi.instCompleteBooleanAlgebra, instCompleteBooleanAlgebra
-/
instance Pi.instCompleteAtomicBooleanAlgebra {ι : Type*} {π : ι -> Type*}
    [forall i, CompleteAtomicBooleanAlgebra (π i)] : CompleteAtomicBooleanAlgebra (forall i, π i) where
  __ := Pi.instCompleteBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]

/--
Instance `OrderDual.instCompleteAtomicBooleanAlgebra` / 实例 `OrderDual.instCompleteAtomicBooleanAlgebra`

English:
instance OrderDual.instCompleteAtomicBooleanAlgebra
  signature: [CompleteAtomicBooleanAlgebra α]
  body: instCompleteBooleanAlgebra
  __ := instCompletelyDistribLattice

中文:
实例 OrderDual.instCompleteAtomic布尔eanAlgebra
  签名: [余mpleteAtomic布尔ean代数 α]
  定义体: instCompleteBooleanAlgebra
  __ := instCompletelyDistribLattice

Depends on / 依赖: instCompleteBooleanAlgebra
-/
instance OrderDual.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra αᵒᵈ where
  __ := instCompleteBooleanAlgebra
  __ := instCompletelyDistribLattice

/--
Instance `Prop.instCompleteAtomicBooleanAlgebra` / 实例 `Prop.instCompleteAtomicBooleanAlgebra`

English:
instance Prop.instCompleteAtomicBooleanAlgebra
  signature: : CompleteAtomicBooleanAlgebra Prop where
  body: Prop.instCompleteLattice
  __ := Prop.instBooleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]

中文:
实例 命题.instCompleteAtomic布尔eanAlgebra
  签名: : 余mpleteAtomic布尔ean代数 命题 where
  定义体: Prop.instCompleteLattice
  __ := Prop.instBooleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]

Depends on / 依赖: Prop.instCompleteLattice, instCompleteLattice
-/
instance Prop.instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.instBooleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]

/--
Instance `Prop.instCompleteBooleanAlgebra` / 实例 `Prop.instCompleteBooleanAlgebra`

English:
instance Prop.instCompleteBooleanAlgebra
  signature: : CompleteBooleanAlgebra Prop
  body: inferInstance

中文:
实例 命题.instComplete布尔eanAlgebra
  签名: : 完备布尔代数 命题
  定义体: inferInstance
-/
instance Prop.instCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop := inferInstance

section lift

/-- Pullback an `Order.Frame.MinimalAxioms` along an injection. -/
@[to_dual /-- Pullback an `Order.Coframe.MinimalAxioms` along a function. -/]
/--
theorem `Function.frameMinimalAxioms` / 定理 `Function.frameMinimalAxioms`

English:
theorem Function.frameMinimalAxioms
  statement: [CompleteLattice α] [CompleteLattice β]
  proof: by
    rw [← le]; rw [← sSup_image]; rw [map_inf]; rw [map_sSup s]; rw [minAx.inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

@[to_dual (attr := deprecated (since := "2026-07-30"))]
alias Function.Injective.frameMinimalAxioms := Function.frameMinimalAxioms

中文:
定理 函数.frameMinimalAxioms
  结论: [完备格 α] [完备格 β]
  证明: by
    rw [← le]; rw [← sSup_image]; rw [map_inf]; rw [map_sSup s]; rw [minAx.inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

@[to_dual (attr := deprecated (since := "2026-07-30"))]
alias Function.Injective.frameMinimalAxioms := Function.frameMinimalAxioms
-/
protected theorem Function.frameMinimalAxioms [CompleteLattice α] [CompleteLattice β]
    (minAx : Frame.MinimalAxioms β) (f : α -> β)
    (le : forall {x y}, f x <= f y ↔ x <= y)
    (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) : Frame.MinimalAxioms α where
  inf_sSup_le_iSup_inf a s := by
    rw [← le]; rw [← sSup_image]; rw [map_inf]; rw [map_sSup s]; rw [minAx.inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

@[to_dual (attr := deprecated (since := "2026-07-30"))]
alias Function.Injective.frameMinimalAxioms := Function.frameMinimalAxioms

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.frame` / `Function.Injective.frame` 的定义

English:
abbreviation Function.Injective.frame
  signature: [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
  body: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp

中文:
缩写 函数.单射.frame
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [上确界集 α] [下确界集 α]
  定义体: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp
-/
protected abbrev Function.Injective.frame [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [Compl α] [HImp α] [Frame β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : forall a, f aᶜ = (f a)ᶜ)
    (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b) : Frame α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.heytingAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_himp

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.coframe` / `Function.Injective.coframe` 的定义

English:
abbreviation Function.Injective.coframe
  signature: [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
  body: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

中文:
缩写 函数.单射.coframe
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [上确界集 α] [下确界集 α]
  定义体: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff
-/
protected abbrev Function.Injective.coframe [Max α] [Min α] [LE α] [LT α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HNot α] [SDiff α] [Coframe β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : forall a, f (￢a) = ￢f a)
    (map_sdiff : forall a b, f (a \ b) = f a \ f b) : Coframe α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coheytingAlgebra f le lt map_sup map_inf map_top map_bot map_hnot map_sdiff

/--
theorem `Function.completeDistribLatticeMinimalAxioms` / 定理 `Function.completeDistribLatticeMinimalAxioms`

English:
theorem Function.completeDistribLatticeMinimalAxioms
  proof: f.frameMinimalAxioms minAx.toFrame le map_inf map_sSup
  __ := f.coframeMinimalAxioms minAx.toCoframe le map_sup map_sInf

@[deprecated (since := "2026-07-30")]
alias Function.Injective.completeDistribLatticeMinimalAxioms :=
  Function.completeDistribLatticeMinimalAxioms

中文:
定理 函数.completeDistribLatticeMinimalAxioms
  证明: f.frameMinimalAxioms minAx.toFrame le map_inf map_sSup
  __ := f.coframeMinimalAxioms minAx.toCoframe le map_sup map_sInf

@[deprecated (since := "2026-07-30")]
alias Function.Injective.completeDistribLatticeMinimalAxioms :=
  Function.completeDistribLatticeMinimalAxioms
-/
protected theorem Function.completeDistribLatticeMinimalAxioms
    [CompleteLattice α] [CompleteLattice β]
    (minAx : CompleteDistribLattice.MinimalAxioms β) (f : α -> β)
    (le : forall {x y}, f x <= f y ↔ x <= y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a) :
    CompleteDistribLattice.MinimalAxioms α where
  __ := f.frameMinimalAxioms minAx.toFrame le map_inf map_sSup
  __ := f.coframeMinimalAxioms minAx.toCoframe le map_sup map_sInf

@[deprecated (since := "2026-07-30")]
alias Function.Injective.completeDistribLatticeMinimalAxioms :=
  Function.completeDistribLatticeMinimalAxioms

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.completeDistribLattice` / `Function.Injective.completeDistribLattice` 的定义

English:
abbreviation Function.Injective.completeDistribLattice
  signature: [Max α] [Min α]
  body: hf.frame f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp
  __ := hf.coframe f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_hnot map_sdiff

中文:
缩写 函数.单射.completeDistribLattice
  签名: [最大值 α] [最小值 α]
  定义体: hf.frame f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp
  __ := hf.coframe f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_hnot map_sdiff
-/
protected abbrev Function.Injective.completeDistribLattice [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompleteDistribLattice β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : forall a, f aᶜ = (f a)ᶜ) (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : forall a, f (￢a) = ￢f a) (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    CompleteDistribLattice α where
  __ := hf.frame f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp
  __ := hf.coframe f le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_hnot map_sdiff

/--
theorem `Function.Injective.completelyDistribLatticeMinimalAxioms` / 定理 `Function.Injective.completelyDistribLatticeMinimalAxioms`

English:
theorem Function.Injective.completelyDistribLatticeMinimalAxioms
  proof: hf by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      minAx.iInf_iSup_eq']

中文:
定理 函数.单射.completelyDistribLatticeMinimalAxioms
  证明: hf by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      minAx.iInf_iSup_eq']
-/
protected theorem Function.Injective.completelyDistribLatticeMinimalAxioms
    [CompleteLattice α] [CompleteLattice β]
    (minAx : CompletelyDistribLattice.MinimalAxioms β) (f : α -> β) (hf : Injective f)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a) :
    CompletelyDistribLattice.MinimalAxioms α where
iInf_iSup_eq g := hf by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      minAx.iInf_iSup_eq']

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.completelyDistribLattice` / `Function.Injective.completelyDistribLattice` 的定义

English:
abbreviation Function.Injective.completelyDistribLattice
  signature: [Max α] [Min α]
  body: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.biheytingAlgebra f
    le lt map_sup map_inf map_top map_bot map_compl map_hnot map_himp map_sdiff
iInf_iSup_eq g := hf by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range

中文:
缩写 函数.单射.completelyDistribLattice
  签名: [最大值 α] [最小值 α]
  定义体: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.biheytingAlgebra f
    le lt map_sup map_inf map_top map_bot map_compl map_hnot map_himp map_sdiff
iInf_iSup_eq g := hf by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range
-/
protected abbrev Function.Injective.completelyDistribLattice [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompletelyDistribLattice β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : forall a, f aᶜ = (f a)ᶜ) (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : forall a, f (￢a) = ￢f a) (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    CompletelyDistribLattice α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.biheytingAlgebra f
    le lt map_sup map_inf map_top map_bot map_compl map_hnot map_himp map_sdiff
iInf_iSup_eq g := hf by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.completeBooleanAlgebra` / `Function.Injective.completeBooleanAlgebra` 的定义

English:
abbreviation Function.Injective.completeBooleanAlgebra
  signature: [Max α] [Min α]
  body: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

中文:
缩写 函数.单射.complete布尔eanAlgebra
  签名: [最大值 α] [最小值 α]
  定义体: hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp
-/
protected abbrev Function.Injective.completeBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [SDiff α]
    [CompleteBooleanAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : forall a, f aᶜ = (f a)ᶜ) (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b)
    (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α where
  __ := hf.completeLattice f le lt map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.completeAtomicBooleanAlgebra` / `Function.Injective.completeAtomicBooleanAlgebra` 的定义

English:
abbreviation Function.Injective.completeAtomicBooleanAlgebra
  signature: [Max α] [Min α]
  body: hf.completelyDistribLattice f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp map_hnot map_sdiff
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

中文:
缩写 函数.单射.completeAtomic布尔eanAlgebra
  签名: [最大值 α] [最小值 α]
  定义体: hf.completelyDistribLattice f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp map_hnot map_sdiff
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp
-/
protected abbrev Function.Injective.completeAtomicBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [SupSet α] [InfSet α] [Top α] [Bot α] [Compl α] [HImp α] [HNot α] [SDiff α]
    [CompleteAtomicBooleanAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : forall a, f aᶜ = (f a)ᶜ) (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : forall a, f (￢a) = ￢f a) (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    CompleteAtomicBooleanAlgebra α where
  __ := hf.completelyDistribLattice f
    le lt map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp map_hnot map_sdiff
  __ := hf.booleanAlgebra f le lt map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `frame` / `frame` 的定义

English:
abbreviation frame
  signature: [Frame β]
  body: by
  let completeLattice := e.completeLattice
  let heytingAlgebra := e.heytingAlgebra
  apply e.injective.frame <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 frame
  签名: [框架 β]
  定义体: by
  let completeLattice := e.completeLattice
  let heytingAlgebra := e.heytingAlgebra
  apply e.injective.frame <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev frame [Frame β] : Frame α := by
  let completeLattice := e.completeLattice
  let heytingAlgebra := e.heytingAlgebra
  apply e.injective.frame <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `coframe` / `coframe` 的定义

English:
abbreviation coframe
  signature: [Coframe β]
  body: by
  let completeLattice := e.completeLattice
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.coframe <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 coframe
  签名: [余frame β]
  定义体: by
  let completeLattice := e.completeLattice
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.coframe <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev coframe [Coframe β] : Coframe α := by
  let completeLattice := e.completeLattice
  let coheytingAlgebra := e.coheytingAlgebra
  apply e.injective.coframe <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `completeDistribLattice` / `completeDistribLattice` 的定义

English:
abbreviation completeDistribLattice
  signature: [CompleteDistribLattice β]
  body: by
  let completeLattice := e.completeLattice
  let biheytingAlgebra := e.biheytingAlgebra
  apply e.injective.completeDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 completeDistribLattice
  签名: [完备分配格 β]
  定义体: by
  let completeLattice := e.completeLattice
  let biheytingAlgebra := e.biheytingAlgebra
  apply e.injective.completeDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev completeDistribLattice [CompleteDistribLattice β] : CompleteDistribLattice α := by
  let completeLattice := e.completeLattice
  let biheytingAlgebra := e.biheytingAlgebra
  apply e.injective.completeDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `completelyDistribLattice` / `completelyDistribLattice` 的定义

English:
abbreviation completelyDistribLattice
  signature: [CompletelyDistribLattice β]
  body: by
  let completeDistribLattice := e.completeDistribLattice
  apply e.injective.completelyDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 completelyDistribLattice
  签名: [余mpletelyDistrib格 β]
  定义体: by
  let completeDistribLattice := e.completeDistribLattice
  apply e.injective.completelyDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev completelyDistribLattice [CompletelyDistribLattice β] :
    CompletelyDistribLattice α := by
  let completeDistribLattice := e.completeDistribLattice
  apply e.injective.completelyDistribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `completeBooleanAlgebra` / `completeBooleanAlgebra` 的定义

English:
abbreviation completeBooleanAlgebra
  signature: [CompleteBooleanAlgebra β]
  body: by
  let completeLattice := e.completeLattice
  let booleanAlgebra := e.booleanAlgebra
  apply e.injective.completeBooleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 complete布尔eanAlgebra
  签名: [完备布尔代数 β]
  定义体: by
  let completeLattice := e.completeLattice
  let booleanAlgebra := e.booleanAlgebra
  apply e.injective.completeBooleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev completeBooleanAlgebra [CompleteBooleanAlgebra β] : CompleteBooleanAlgebra α := by
  let completeLattice := e.completeLattice
  let booleanAlgebra := e.booleanAlgebra
  apply e.injective.completeBooleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

/--
Definition of `completeAtomicBooleanAlgebra` / `completeAtomicBooleanAlgebra` 的定义

English:
abbreviation completeAtomicBooleanAlgebra
  signature: [CompleteAtomicBooleanAlgebra β]
  body: by
  let completeBooleanAlgebra := e.completeBooleanAlgebra
  apply e.injective.completeAtomicBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

中文:
缩写 completeAtomic布尔eanAlgebra
  签名: [余mpleteAtomic布尔ean代数 β]
  定义体: by
  let completeBooleanAlgebra := e.completeBooleanAlgebra
  apply e.injective.completeAtomicBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _
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

/--
Instance `instCompleteBooleanAlgebra` / 实例 `instCompleteBooleanAlgebra`

English:
instance instCompleteBooleanAlgebra
  signature: : CompleteBooleanAlgebra PUnit where

中文:
实例 instComplete布尔eanAlgebra
  签名: : 完备布尔代数 命题单元 where
-/
instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra PUnit where

/--
Instance `instCompleteAtomicBooleanAlgebra` / 实例 `instCompleteAtomicBooleanAlgebra`

English:
instance instCompleteAtomicBooleanAlgebra
  signature: : CompleteAtomicBooleanAlgebra PUnit where
  body: rfl

@[to_dual (attr := simp)]

中文:
实例 instCompleteAtomic布尔eanAlgebra
  签名: : 余mpleteAtomic布尔ean代数 命题单元 where
  定义体: rfl

@[to_dual (attr := simp)]
-/
instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra PUnit where
  iInf_iSup_eq _ := rfl

@[to_dual (attr := simp)]
/--
theorem `sSup_eq` / 定理 `sSup_eq`

English:
theorem sSup_eq
  statement: sSup s = unit
  proof: rfl

中文:
定理 sSup_eq
  结论: sSup s = unit
  证明: rfl
-/
theorem sSup_eq : sSup s = unit :=
  rfl

end PUnit
