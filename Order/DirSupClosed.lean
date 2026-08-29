/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.UpperLower.Basic

import Mathlib.Data.Set.Lattice

/-!
# Sets closed under directed suprema

We say that a set `s` is closed under directed suprema whenever it contains all least upper bounds
for nonempty, directed subsets. Conversely, a set `s` is inaccessible by directed suprema whenever
its complement is closed under directed suprema. Equivalently, if the least upper bound of a
nonempty directed set `t` is contained in `s`, then `t` and `s` must have nonempty intersection.

## Main definitions

- `DirSupClosed`: sets closed under directed suprema.
- `DirSupInacc`: sets inaccessible by directed suprema.
-/

@[expose] public section

variable {α : Type*} {s t : Set α} {D D₁ D₂ : Set (Set α)}

open Set

section Preorder
variable [Preorder α]

/--
Definition of `DirSupClosedOn` / `DirSupClosedOn` 的定义

English:
definition DirSupClosedOn
  signature: (D : Set (Set α)) (s : Set α)
  body: forall ⦃d⦄, d in D -> d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s

中文:
定义 DirSupClosedOn
  签名: (D : Set (Set α)) (s : Set α)
  定义体: forall ⦃d⦄, d in D -> d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty, subseteq
-/
def DirSupClosedOn (D : Set (Set α)) (s : Set α) : Prop :=
  forall ⦃d⦄, d in D -> d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s

/--
Definition of `DirSupInaccOn` / `DirSupInaccOn` 的定义

English:
definition DirSupInaccOn
  signature: (D : Set (Set α)) (s : Set α)
  body: forall ⦃d⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty

中文:
定义 DirSupInaccOn
  签名: (D : Set (Set α)) (s : Set α)
  定义体: forall ⦃d⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty
-/
def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  forall ⦃d⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty

/--
Definition of `DirSupClosed` / `DirSupClosed` 的定义

English:
definition DirSupClosed
  signature: (s : Set α)
  body: forall ⦃d⦄, d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s

中文:
定义 DirSupClosed
  签名: (s : Set α)
  定义体: forall ⦃d⦄, d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty, subseteq
-/
def DirSupClosed (s : Set α) : Prop :=
  forall ⦃d⦄, d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s

/--
Definition of `DirSupInacc` / `DirSupInacc` 的定义

English:
definition DirSupInacc
  signature: (s : Set α)
  body: forall ⦃d⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty

中文:
定义 DirSupInacc
  签名: (s : Set α)
  定义体: forall ⦃d⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty
-/
def DirSupInacc (s : Set α) : Prop :=
  forall ⦃d⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty

/--
lemma `dirSupClosedOn_univ` / 引理 `dirSupClosedOn_univ`

English:
lemma dirSupClosedOn_univ
  statement: DirSupClosedOn univ s ↔ DirSupClosed s
  proof: by
  simp [DirSupClosedOn, DirSupClosed]

中文:
引理 dirSupClosedOn_univ
  结论: DirSupClosedOn univ s ↔ DirSupClosed s
  证明: by
  simp [DirSupClosedOn, DirSupClosed]
-/
@[simp] lemma dirSupClosedOn_univ : DirSupClosedOn univ s ↔ DirSupClosed s := by
  simp [DirSupClosedOn, DirSupClosed]

/--
lemma `dirSupInaccOn_univ` / 引理 `dirSupInaccOn_univ`

English:
lemma dirSupInaccOn_univ
  statement: DirSupInaccOn univ s ↔ DirSupInacc s
  proof: by
  simp [DirSupInaccOn, DirSupInacc]

中文:
引理 dirSupInaccOn_univ
  结论: DirSupInaccOn univ s ↔ DirSupInacc s
  证明: by
  simp [DirSupInaccOn, DirSupInacc]
-/
@[simp] lemma dirSupInaccOn_univ : DirSupInaccOn univ s ↔ DirSupInacc s := by
  simp [DirSupInaccOn, DirSupInacc]

/--
lemma `DirSupClosed.dirSupClosedOn` / 引理 `DirSupClosed.dirSupClosedOn`

English:
lemma DirSupClosed.dirSupClosedOn
  statement: DirSupClosed s -> DirSupClosedOn D s
  proof: @fun h _ _ => @h _

中文:
引理 DirSupClosed.dirSupClosedOn
  结论: DirSupClosed s -> DirSupClosedOn D s
  证明: @fun h _ _ => @h _
-/
@[simp] lemma DirSupClosed.dirSupClosedOn : DirSupClosed s -> DirSupClosedOn D s := @fun h _ _ => @h _
/--
lemma `DirSupInacc.dirSupInaccOn` / 引理 `DirSupInacc.dirSupInaccOn`

English:
lemma DirSupInacc.dirSupInaccOn
  statement: DirSupInacc s -> DirSupInaccOn D s
  proof: @fun h _ _ => @h _

中文:
引理 DirSupInacc.dirSupInaccOn
  结论: DirSupInacc s -> DirSupInaccOn D s
  证明: @fun h _ _ => @h _
-/
@[simp] lemma DirSupInacc.dirSupInaccOn : DirSupInacc s -> DirSupInaccOn D s := @fun h _ _ => @h _

/--
theorem `DirSupClosed.of_isEmpty` / 定理 `DirSupClosed.of_isEmpty`

English:
theorem DirSupClosed.of_isEmpty
  given: [IsEmpty α] {s : Set α}
  statement: DirSupClosed s
  proof: fun _ _ ⟨a, _⟩ => isEmptyElim a

中文:
定理 DirSupClosed.of_isEmpty
  条件: [IsEmpty α] {s : Set α}
  结论: DirSupClosed s
  证明: fun _ _ ⟨a, _⟩ => isEmptyElim a
-/
@[simp] theorem DirSupClosed.of_isEmpty [IsEmpty α] {s : Set α} : DirSupClosed s :=
  fun _ _ ⟨a, _⟩ => isEmptyElim a

/--
theorem `DirSupInacc.of_isEmpty` / 定理 `DirSupInacc.of_isEmpty`

English:
theorem DirSupInacc.of_isEmpty
  given: [IsEmpty α] {s : Set α}
  statement: DirSupInacc s
  proof: fun _ ⟨a, _⟩ => isEmptyElim a

中文:
定理 DirSupInacc.of_isEmpty
  条件: [IsEmpty α] {s : Set α}
  结论: DirSupInacc s
  证明: fun _ ⟨a, _⟩ => isEmptyElim a
-/
@[simp] theorem DirSupInacc.of_isEmpty [IsEmpty α] {s : Set α} : DirSupInacc s :=
  fun _ ⟨a, _⟩ => isEmptyElim a

/--
theorem `DirSupClosedOn.of_isEmpty` / 定理 `DirSupClosedOn.of_isEmpty`

English:
theorem DirSupClosedOn.of_isEmpty
  given: [IsEmpty α] {s : Set α}
  statement: DirSupClosedOn D s
  proof: by simp

中文:
定理 DirSupClosedOn.of_isEmpty
  条件: [IsEmpty α] {s : Set α}
  结论: DirSupClosedOn D s
  证明: by simp
-/
theorem DirSupClosedOn.of_isEmpty [IsEmpty α] {s : Set α} : DirSupClosedOn D s := by simp
/--
theorem `DirSupInaccOn.of_isEmpty` / 定理 `DirSupInaccOn.of_isEmpty`

English:
theorem DirSupInaccOn.of_isEmpty
  given: [IsEmpty α] {s : Set α}
  statement: DirSupInaccOn D s
  proof: by simp

@[gcongr]

中文:
定理 DirSupInaccOn.of_isEmpty
  条件: [IsEmpty α] {s : Set α}
  结论: DirSupInaccOn D s
  证明: by simp

@[gcongr]
-/
theorem DirSupInaccOn.of_isEmpty [IsEmpty α] {s : Set α} : DirSupInaccOn D s := by simp

@[gcongr]
/--
lemma `DirSupClosedOn.mono` / 引理 `DirSupClosedOn.mono`

English:
lemma DirSupClosedOn.mono
  given: (hD : D₁ subseteq D₂) (hf : DirSupClosedOn D₂ s)
  statement: DirSupClosedOn D₁ s
  proof: fun _ a => hf (hD a)

@[gcongr]

中文:
引理 DirSupClosedOn.mono
  条件: (hD : D₁ subseteq D₂) (hf : DirSupClosedOn D₂ s)
  结论: DirSupClosedOn D₁ s
  证明: fun _ a => hf (hD a)

@[gcongr]
-/
lemma DirSupClosedOn.mono (hD : D₁ subseteq D₂) (hf : DirSupClosedOn D₂ s) : DirSupClosedOn D₁ s :=
  fun _ a => hf (hD a)

@[gcongr]
/--
lemma `DirSupInaccOn.mono` / 引理 `DirSupInaccOn.mono`

English:
lemma DirSupInaccOn.mono
  given: (hD : D₁ subseteq D₂) (hf : DirSupInaccOn D₂ s)
  statement: DirSupInaccOn D₁ s
  proof: fun _ a => hf (hD a)

@[simp]

中文:
引理 DirSupInaccOn.mono
  条件: (hD : D₁ subseteq D₂) (hf : DirSupInaccOn D₂ s)
  结论: DirSupInaccOn D₁ s
  证明: fun _ a => hf (hD a)

@[simp]
-/
lemma DirSupInaccOn.mono (hD : D₁ subseteq D₂) (hf : DirSupInaccOn D₂ s) : DirSupInaccOn D₁ s :=
  fun _ a => hf (hD a)

@[simp]
/--
lemma `dirSupClosedOn_compl` / 引理 `dirSupClosedOn_compl`

English:
lemma dirSupClosedOn_compl
  statement: DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s
  proof: by
  simp_rw [DirSupClosedOn, DirSupInaccOn, ← not_disjoint_iff_nonempty_inter]
  grind

@[simp]

中文:
引理 dirSupClosedOn_compl
  结论: DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s
  证明: by
  simp_rw [DirSupClosedOn, DirSupInaccOn, ← not_disjoint_iff_nonempty_inter]
  grind

@[simp]

Depends on / 依赖: DirSupClosedOn, DirSupInaccOn, not_disjoint_iff_nonempty_inter, simp_rw
-/
lemma dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s := by
  simp_rw [DirSupClosedOn, DirSupInaccOn, ← not_disjoint_iff_nonempty_inter]
  grind

@[simp]
/--
lemma `dirSupClosed_compl` / 引理 `dirSupClosed_compl`

English:
lemma dirSupClosed_compl
  statement: DirSupClosed sᶜ ↔ DirSupInacc s
  proof: by
  rw [← dirSupClosedOn_univ]; rw [dirSupClosedOn_compl]; rw [dirSupInaccOn_univ]

@[simp]

中文:
引理 dirSupClosed_compl
  结论: DirSupClosed sᶜ ↔ DirSupInacc s
  证明: by
  rw [← dirSupClosedOn_univ]; rw [dirSupClosedOn_compl]; rw [dirSupInaccOn_univ]

@[simp]

Depends on / 依赖: dirSupClosedOn_compl, dirSupClosedOn_univ, dirSupInaccOn_univ
-/
lemma dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s := by
  rw [← dirSupClosedOn_univ]; rw [dirSupClosedOn_compl]; rw [dirSupInaccOn_univ]

@[simp]
/--
lemma `dirSupInaccOn_compl` / 引理 `dirSupInaccOn_compl`

English:
lemma dirSupInaccOn_compl
  statement: DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s
  proof: by
  rw [← dirSupClosedOn_compl]; rw [compl_compl]

@[simp]

中文:
引理 dirSupInaccOn_compl
  结论: DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s
  证明: by
  rw [← dirSupClosedOn_compl]; rw [compl_compl]

@[simp]

Depends on / 依赖: compl_compl, dirSupClosedOn_compl
-/
lemma dirSupInaccOn_compl : DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s := by
  rw [← dirSupClosedOn_compl]; rw [compl_compl]

@[simp]
/--
lemma `dirSupInacc_compl` / 引理 `dirSupInacc_compl`

English:
lemma dirSupInacc_compl
  statement: DirSupInacc sᶜ ↔ DirSupClosed s
  proof: by
  rw [← dirSupClosed_compl]; rw [compl_compl]

alias ⟨DirSupInaccOn.of_compl, DirSupInaccOn.compl⟩ := dirSupClosedOn_compl
alias ⟨DirSupClosedOn.of_compl, DirSupClosedOn.compl⟩ := dirSupInaccOn_compl
alias ⟨DirSupInacc.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl
alias ⟨DirSupClosed.of_comp

中文:
引理 dirSupInacc_compl
  结论: DirSupInacc sᶜ ↔ DirSupClosed s
  证明: by
  rw [← dirSupClosed_compl]; rw [compl_compl]

alias ⟨DirSupInaccOn.of_compl, DirSupInaccOn.compl⟩ := dirSupClosedOn_compl
alias ⟨DirSupClosedOn.of_compl, DirSupClosedOn.compl⟩ := dirSupInaccOn_compl
alias ⟨DirSupInacc.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl
alias ⟨DirSupClosed.of_comp

Depends on / 依赖: compl_compl, dirSupClosed_compl
-/
lemma dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s := by
  rw [← dirSupClosed_compl]; rw [compl_compl]

alias ⟨DirSupInaccOn.of_compl, DirSupInaccOn.compl⟩ := dirSupClosedOn_compl
alias ⟨DirSupClosedOn.of_compl, DirSupClosedOn.compl⟩ := dirSupInaccOn_compl
alias ⟨DirSupInacc.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl
alias ⟨DirSupClosed.of_compl, DirSupClosed.compl⟩ := dirSupInacc_compl

/--
theorem `DirSupClosed.empty` / 定理 `DirSupClosed.empty`

English:
theorem DirSupClosed.empty
  statement: DirSupClosed (∅ : Set α)
  proof: by simp [DirSupClosed]

中文:
定理 DirSupClosed.empty
  结论: DirSupClosed (∅ : Set α)
  证明: by simp [DirSupClosed]
-/
@[simp] theorem DirSupClosed.empty : DirSupClosed (∅ : Set α) := by simp [DirSupClosed]
/--
theorem `DirSupInacc.empty` / 定理 `DirSupInacc.empty`

English:
theorem DirSupInacc.empty
  statement: DirSupInacc (∅ : Set α)
  proof: by simp [DirSupInacc]

中文:
定理 DirSupInacc.empty
  结论: DirSupInacc (∅ : Set α)
  证明: by simp [DirSupInacc]
-/
@[simp] theorem DirSupInacc.empty : DirSupInacc (∅ : Set α) := by simp [DirSupInacc]
/--
theorem `DirSupClosedOn.empty` / 定理 `DirSupClosedOn.empty`

English:
theorem DirSupClosedOn.empty
  statement: DirSupClosedOn D ∅
  proof: by simp

中文:
定理 DirSupClosedOn.empty
  结论: DirSupClosedOn D ∅
  证明: by simp
-/
theorem DirSupClosedOn.empty : DirSupClosedOn D ∅ := by simp
/--
theorem `DirSupInaccOn.empty` / 定理 `DirSupInaccOn.empty`

English:
theorem DirSupInaccOn.empty
  statement: DirSupInaccOn D ∅
  proof: by simp

中文:
定理 DirSupInaccOn.empty
  结论: DirSupInaccOn D ∅
  证明: by simp
-/
theorem DirSupInaccOn.empty : DirSupInaccOn D ∅ := by simp

/--
theorem `DirSupClosed.univ` / 定理 `DirSupClosed.univ`

English:
theorem DirSupClosed.univ
  statement: DirSupClosed (univ : Set α)
  proof: by simp [DirSupClosed]

中文:
定理 DirSupClosed.univ
  结论: DirSupClosed (univ : Set α)
  证明: by simp [DirSupClosed]
-/
@[simp] theorem DirSupClosed.univ : DirSupClosed (univ : Set α) := by simp [DirSupClosed]
/--
theorem `DirSupInacc.univ` / 定理 `DirSupInacc.univ`

English:
theorem DirSupInacc.univ
  statement: DirSupInacc (univ : Set α)
  proof: by simp [← compl_empty]

中文:
定理 DirSupInacc.univ
  结论: DirSupInacc (univ : Set α)
  证明: by simp [← compl_empty]
-/
@[simp] theorem DirSupInacc.univ : DirSupInacc (univ : Set α) := by simp [← compl_empty]
/--
theorem `DirSupClosedOn.univ` / 定理 `DirSupClosedOn.univ`

English:
theorem DirSupClosedOn.univ
  statement: DirSupClosedOn D univ
  proof: by simp

中文:
定理 DirSupClosedOn.univ
  结论: DirSupClosedOn D univ
  证明: by simp
-/
theorem DirSupClosedOn.univ : DirSupClosedOn D univ := by simp
/--
theorem `DirSupInaccOn.univ` / 定理 `DirSupInaccOn.univ`

English:
theorem DirSupInaccOn.univ
  statement: DirSupInaccOn D univ
  proof: by simp

中文:
定理 DirSupInaccOn.univ
  结论: DirSupInaccOn D univ
  证明: by simp
-/
theorem DirSupInaccOn.univ : DirSupInaccOn D univ := by simp

/--
theorem `DirSupClosedOn.sInter` / 定理 `DirSupClosedOn.sInter`

English:
theorem DirSupClosedOn.sInter
  given: {s : Set (Set α)} (hs : forall x in s, DirSupClosedOn D x)
  proof: fun _d hD hds hd hd' _a ha t ht => hs t ht hD (hds.trans fun _x hx => hx _ ht) hd hd' ha

中文:
定理 DirSupClosedOn.sInter
  条件: {s : Set (Set α)} (hs : 对任意 x in s, DirSupClosedOn D x)
  证明: fun _d hD hds hd hd' _a ha t ht => hs t ht hD (hds.trans fun _x hx => hx _ ht) hd hd' ha

Depends on / 依赖: hds.trans
-/
theorem DirSupClosedOn.sInter {s : Set (Set α)} (hs : forall x in s, DirSupClosedOn D x) :
    DirSupClosedOn D (⋂₀ s) :=
  fun _d hD hds hd hd' _a ha t ht => hs t ht hD (hds.trans fun _x hx => hx _ ht) hd hd' ha

/--
theorem `DirSupClosed.sInter` / 定理 `DirSupClosed.sInter`

English:
theorem DirSupClosed.sInter
  given: {s : Set (Set α)} (hs : forall x in s, DirSupClosed x)
  proof: by
  simpa using DirSupClosedOn.sInter fun x hx => (hs x hx).dirSupClosedOn (D := .univ)

中文:
定理 DirSupClosed.sInter
  条件: {s : Set (Set α)} (hs : 对任意 x in s, DirSupClosed x)
  证明: by
  simpa using DirSupClosedOn.sInter fun x hx => (hs x hx).dirSupClosedOn (D := .univ)

Depends on / 依赖: DirSupClosedOn, DirSupClosedOn.sInter, dirSupClosedOn, sInter
-/
theorem DirSupClosed.sInter {s : Set (Set α)} (hs : forall x in s, DirSupClosed x) :
    DirSupClosed (⋂₀ s) := by
  simpa using DirSupClosedOn.sInter fun x hx => (hs x hx).dirSupClosedOn (D := .univ)

/--
theorem `DirSupInaccOn.sUnion` / 定理 `DirSupInaccOn.sUnion`

English:
theorem DirSupInaccOn.sUnion
  given: {s : Set (Set α)} (hs : forall x in s, DirSupInaccOn D x)
  proof: by
  rw [← dirSupClosedOn_compl]; rw [Set.compl_sUnion]
  apply DirSupClosedOn.sInter
  rintro x ⟨x, hx, rfl⟩
  exact (hs x hx).compl

中文:
定理 DirSupInaccOn.sUnion
  条件: {s : Set (Set α)} (hs : 对任意 x in s, DirSupInaccOn D x)
  证明: by
  rw [← dirSupClosedOn_compl]; rw [Set.compl_sUnion]
  apply DirSupClosedOn.sInter
  rintro x ⟨x, hx, rfl⟩
  exact (hs x hx).compl

Depends on / 依赖: DirSupClosedOn, DirSupClosedOn.sInter, Set.compl_sUnion, compl_sUnion, dirSupClosedOn_compl, sInter
-/
theorem DirSupInaccOn.sUnion {s : Set (Set α)} (hs : forall x in s, DirSupInaccOn D x) :
    DirSupInaccOn D (⋃₀ s) := by
  rw [← dirSupClosedOn_compl]; rw [Set.compl_sUnion]
  apply DirSupClosedOn.sInter
  rintro x ⟨x, hx, rfl⟩
  exact (hs x hx).compl

/--
theorem `DirSupInacc.sUnion` / 定理 `DirSupInacc.sUnion`

English:
theorem DirSupInacc.sUnion
  given: {s : Set (Set α)} (hs : forall x in s, DirSupInacc x)
  proof: by
  simpa using DirSupInaccOn.sUnion fun x hx => (hs x hx).dirSupInaccOn (D := .univ)

中文:
定理 DirSupInacc.sUnion
  条件: {s : Set (Set α)} (hs : 对任意 x in s, DirSupInacc x)
  证明: by
  simpa using DirSupInaccOn.sUnion fun x hx => (hs x hx).dirSupInaccOn (D := .univ)

Depends on / 依赖: DirSupInaccOn, DirSupInaccOn.sUnion, dirSupInaccOn, sUnion
-/
theorem DirSupInacc.sUnion {s : Set (Set α)} (hs : forall x in s, DirSupInacc x) :
    DirSupInacc (⋃₀ s) := by
  simpa using DirSupInaccOn.sUnion fun x hx => (hs x hx).dirSupInaccOn (D := .univ)

/--
theorem `DirSupClosedOn.iInter` / 定理 `DirSupClosedOn.iInter`

English:
theorem DirSupClosedOn.iInter
  given: {ι} {f : ι -> Set α} (hs : forall i, DirSupClosedOn D (f i))
  proof: by
  rw [← sInter_range f]
  exact DirSupClosedOn.sInter (by simpa)

中文:
定理 DirSupClosedOn.iInter
  条件: {ι} {f : ι -> Set α} (hs : 对任意 i, DirSupClosedOn D (f i))
  证明: by
  rw [← sInter_range f]
  exact DirSupClosedOn.sInter (by simpa)

Depends on / 依赖: DirSupClosedOn, DirSupClosedOn.sInter, sInter, sInter_range
-/
theorem DirSupClosedOn.iInter {ι} {f : ι -> Set α} (hs : forall i, DirSupClosedOn D (f i)) :
    DirSupClosedOn D (⋂ i, f i) := by
  rw [← sInter_range f]
  exact DirSupClosedOn.sInter (by simpa)

/--
theorem `DirSupClosed.iInter` / 定理 `DirSupClosed.iInter`

English:
theorem DirSupClosed.iInter
  given: {ι} {f : ι -> Set α} (hs : forall i, DirSupClosed (f i))
  proof: by
  rw [← sInter_range f]
  exact DirSupClosed.sInter (by simpa)

中文:
定理 DirSupClosed.iInter
  条件: {ι} {f : ι -> Set α} (hs : 对任意 i, DirSupClosed (f i))
  证明: by
  rw [← sInter_range f]
  exact DirSupClosed.sInter (by simpa)

Depends on / 依赖: DirSupClosed, DirSupClosed.sInter, sInter, sInter_range
-/
theorem DirSupClosed.iInter {ι} {f : ι -> Set α} (hs : forall i, DirSupClosed (f i)) :
    DirSupClosed (⋂ i, f i) := by
  rw [← sInter_range f]
  exact DirSupClosed.sInter (by simpa)

/--
theorem `DirSupInaccOn.iUnion` / 定理 `DirSupInaccOn.iUnion`

English:
theorem DirSupInaccOn.iUnion
  given: {ι} {f : ι -> Set α} (hs : forall i, DirSupInaccOn D (f i))
  proof: by
  rw [← sUnion_range f]
  exact DirSupInaccOn.sUnion (by simpa)

中文:
定理 DirSupInaccOn.iUnion
  条件: {ι} {f : ι -> Set α} (hs : 对任意 i, DirSupInaccOn D (f i))
  证明: by
  rw [← sUnion_range f]
  exact DirSupInaccOn.sUnion (by simpa)

Depends on / 依赖: DirSupInaccOn, DirSupInaccOn.sUnion, sUnion, sUnion_range
-/
theorem DirSupInaccOn.iUnion {ι} {f : ι -> Set α} (hs : forall i, DirSupInaccOn D (f i)) :
    DirSupInaccOn D (⋃ i, f i) := by
  rw [← sUnion_range f]
  exact DirSupInaccOn.sUnion (by simpa)

/--
theorem `DirSupInacc.iUnion` / 定理 `DirSupInacc.iUnion`

English:
theorem DirSupInacc.iUnion
  given: {ι} {f : ι -> Set α} (hs : forall i, DirSupInacc (f i))
  proof: by
  rw [← sUnion_range f]
  exact DirSupInacc.sUnion (by simpa)

中文:
定理 DirSupInacc.iUnion
  条件: {ι} {f : ι -> Set α} (hs : 对任意 i, DirSupInacc (f i))
  证明: by
  rw [← sUnion_range f]
  exact DirSupInacc.sUnion (by simpa)

Depends on / 依赖: DirSupInacc, DirSupInacc.sUnion, sUnion, sUnion_range
-/
theorem DirSupInacc.iUnion {ι} {f : ι -> Set α} (hs : forall i, DirSupInacc (f i)) :
    DirSupInacc (⋃ i, f i) := by
  rw [← sUnion_range f]
  exact DirSupInacc.sUnion (by simpa)

/--
lemma `DirSupClosedOn.inter` / 引理 `DirSupClosedOn.inter`

English:
lemma DirSupClosedOn.inter
  given: (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t)
  proof: by
  rw [← sInter_pair]
  refine .sInter ?_
  simpa [hs]

中文:
引理 DirSupClosedOn.inter
  条件: (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t)
  证明: by
  rw [← sInter_pair]
  refine .sInter ?_
  simpa [hs]

Depends on / 依赖: sInter, sInter_pair
-/
lemma DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) :
    DirSupClosedOn D (s inter t) := by
  rw [← sInter_pair]
  refine .sInter ?_
  simpa [hs]

/--
lemma `DirSupClosed.inter` / 引理 `DirSupClosed.inter`

English:
lemma DirSupClosed.inter
  given: (hs : DirSupClosed s) (ht : DirSupClosed t)
  statement: DirSupClosed (s inter t)
  proof: by
  simpa using hs.dirSupClosedOn.inter ht.dirSupClosedOn (D := .univ)

中文:
引理 DirSupClosed.inter
  条件: (hs : DirSupClosed s) (ht : DirSupClosed t)
  结论: DirSupClosed (s inter t)
  证明: by
  simpa using hs.dirSupClosedOn.inter ht.dirSupClosedOn (D := .univ)

Depends on / 依赖: dirSupClosedOn, hs.dirSupClosedOn.inter, ht.dirSupClosedOn
-/
lemma DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s inter t) := by
  simpa using hs.dirSupClosedOn.inter ht.dirSupClosedOn (D := .univ)

/--
lemma `DirSupInaccOn.union` / 引理 `DirSupInaccOn.union`

English:
lemma DirSupInaccOn.union
  given: (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t)
  proof: by
  rw [← dirSupClosedOn_compl]; rw [compl_union]; exact hs.compl.inter ht.compl

中文:
引理 DirSupInaccOn.union
  条件: (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t)
  证明: by
  rw [← dirSupClosedOn_compl]; rw [compl_union]; exact hs.compl.inter ht.compl

Depends on / 依赖: compl_union, dirSupClosedOn_compl, hs.compl.inter, ht.compl
-/
lemma DirSupInaccOn.union (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) :
    DirSupInaccOn D (s union t) := by
  rw [← dirSupClosedOn_compl]; rw [compl_union]; exact hs.compl.inter ht.compl

/--
lemma `DirSupInacc.union` / 引理 `DirSupInacc.union`

English:
lemma DirSupInacc.union
  given: (hs : DirSupInacc s) (ht : DirSupInacc t)
  statement: DirSupInacc (s union t)
  proof: by
  simpa using hs.dirSupInaccOn.union ht.dirSupInaccOn (D := .univ)

中文:
引理 DirSupInacc.union
  条件: (hs : DirSupInacc s) (ht : DirSupInacc t)
  结论: DirSupInacc (s union t)
  证明: by
  simpa using hs.dirSupInaccOn.union ht.dirSupInaccOn (D := .univ)

Depends on / 依赖: dirSupInaccOn, hs.dirSupInaccOn.union, ht.dirSupInaccOn
-/
lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s union t) := by
  simpa using hs.dirSupInaccOn.union ht.dirSupInaccOn (D := .univ)

/--
theorem `DirSupClosedOn.union` / 定理 `DirSupClosedOn.union`

English:
theorem DirSupClosedOn.union
  statement: (hDL : IsLowerSet D)
  proof: by
  intro d hD hdu hd₀ hd₁ a ha
  have hdst : d inter s union d inter t = d := by grind
  wlog h : DirectedOn (· <= ·) (d inter s) ∧ IsCofinalFor (d inter t) (d inter s)
  · rw [union_comm] at hdu hdst ⊢
exact this hDL ht hs hD hdu hd₀ hd₁ ha hdst
      (directedOn_union_iff.mp (by rwa [hdst])).res

中文:
定理 DirSupClosedOn.union
  结论: (hDL : IsLowerSet D)
  证明: by
  intro d hD hdu hd₀ hd₁ a ha
  have hdst : d inter s union d inter t = d := by grind
  wlog h : DirectedOn (· <= ·) (d inter s) ∧ IsCofinalFor (d inter t) (d inter s)
  · rw [union_comm] at hdu hdst ⊢
exact this hDL ht hs hD hdu hd₀ hd₁ ha hdst
      (directedOn_union_iff.mp (by rwa [hdst])).res

Depends on / 依赖: DirectedOn, IsCofinalFor, directedOn_union_iff, directedOn_union_iff.mp, ha.of_isCofin, hcof.union_right.mono_left, hdst.ge, inter_subset_left, inter_subset_right, mono_left, nonempty, of_isCofin, resolve_right, union_comm, union_right
-/
theorem DirSupClosedOn.union (hDL : IsLowerSet D)
    (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) : DirSupClosedOn D (s union t) := by
  intro d hD hdu hd₀ hd₁ a ha
  have hdst : d inter s union d inter t = d := by grind
  wlog h : DirectedOn (· <= ·) (d inter s) ∧ IsCofinalFor (d inter t) (d inter s)
  · rw [union_comm] at hdu hdst ⊢
exact this hDL ht hs hD hdu hd₀ hd₁ ha hdst
      (directedOn_union_iff.mp (by rwa [hdst])).resolve_right h
  obtain ⟨hds, hcof⟩ := h
  have hcof' : IsCofinalFor d (d inter s) := hcof.union_right.mono_left hdst.ge
exact .inl hs (hDL inter_subset_left hD) inter_subset_right
    (hcof'.nonempty hd₀) hds (ha.of_isCofinalFor inter_subset_left hcof')

/--
theorem `DirSupInaccOn.inter` / 定理 `DirSupInaccOn.inter`

English:
theorem DirSupInaccOn.inter
  statement: (hDL : IsLowerSet D)
  proof: by
  rw [← dirSupClosedOn_compl]; rw [compl_inter]; exact hs.compl.union hDL ht.compl

中文:
定理 DirSupInaccOn.inter
  结论: (hDL : IsLowerSet D)
  证明: by
  rw [← dirSupClosedOn_compl]; rw [compl_inter]; exact hs.compl.union hDL ht.compl

Depends on / 依赖: compl_inter, dirSupClosedOn_compl, hs.compl.union, ht.compl
-/
theorem DirSupInaccOn.inter (hDL : IsLowerSet D)
    (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) : DirSupInaccOn D (s inter t) := by
  rw [← dirSupClosedOn_compl]; rw [compl_inter]; exact hs.compl.union hDL ht.compl

/--
theorem `DirSupClosed.union` / 定理 `DirSupClosed.union`

English:
theorem DirSupClosed.union
  given: (hs : DirSupClosed s) (ht : DirSupClosed t)
  statement: DirSupClosed (s union t)
  proof: by
  simpa using hs.dirSupClosedOn.union isLowerSet_univ ht.dirSupClosedOn

中文:
定理 DirSupClosed.union
  条件: (hs : DirSupClosed s) (ht : DirSupClosed t)
  结论: DirSupClosed (s union t)
  证明: by
  simpa using hs.dirSupClosedOn.union isLowerSet_univ ht.dirSupClosedOn

Depends on / 依赖: dirSupClosedOn, hs.dirSupClosedOn.union, ht.dirSupClosedOn, isLowerSet_univ
-/
theorem DirSupClosed.union (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s union t) := by
  simpa using hs.dirSupClosedOn.union isLowerSet_univ ht.dirSupClosedOn

/--
theorem `DirSupInacc.inter` / 定理 `DirSupInacc.inter`

English:
theorem DirSupInacc.inter
  given: (hs : DirSupInacc s) (ht : DirSupInacc t)
  statement: DirSupInacc (s inter t)
  proof: by
  simpa using hs.dirSupInaccOn.inter isLowerSet_univ ht.dirSupInaccOn

中文:
定理 DirSupInacc.inter
  条件: (hs : DirSupInacc s) (ht : DirSupInacc t)
  结论: DirSupInacc (s inter t)
  证明: by
  simpa using hs.dirSupInaccOn.inter isLowerSet_univ ht.dirSupInaccOn

Depends on / 依赖: dirSupInaccOn, hs.dirSupInaccOn.inter, ht.dirSupInaccOn, isLowerSet_univ
-/
theorem DirSupInacc.inter (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s inter t) := by
  simpa using hs.dirSupInaccOn.inter isLowerSet_univ ht.dirSupInaccOn

/--
theorem `DirSupInaccOn.of_inter_subset` / 定理 `DirSupInaccOn.of_inter_subset`

English:
theorem DirSupInaccOn.of_inter_subset
  proof: by
  intro d hd₀ hd₁ hd₂ a hda hd₃
  obtain ⟨b, hbd, hb⟩ := h hd₀ hd₁ hd₂ hda hd₃
  exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

中文:
定理 DirSupInaccOn.of_inter_subset
  证明: by
  intro d hd₀ hd₁ hd₂ a hda hd₃
  obtain ⟨b, hbd, hb⟩ := h hd₀ hd₁ hd₂ hda hd₃
  exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

Depends on / 依赖: le_rfl
-/
theorem DirSupInaccOn.of_inter_subset
    (h : forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d ->
      forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s) : DirSupInaccOn D s := by
  intro d hd₀ hd₁ hd₂ a hda hd₃
  obtain ⟨b, hbd, hb⟩ := h hd₀ hd₁ hd₂ hda hd₃
  exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

/--
theorem `DirSupInacc.of_inter_subset` / 定理 `DirSupInacc.of_inter_subset`

English:
theorem DirSupInacc.of_inter_subset
  proof: dirSupInaccOn_univ.1 (.of_inter_subset (by simpa))

中文:
定理 DirSupInacc.of_inter_subset
  证明: dirSupInaccOn_univ.1 (.of_inter_subset (by simpa))

Depends on / 依赖: dirSupInaccOn_univ, of_inter_subset
-/
theorem DirSupInacc.of_inter_subset
    (h : forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d ->
      forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s) : DirSupInacc s :=
  dirSupInaccOn_univ.1 (.of_inter_subset (by simpa))

/--
theorem `dirSupInaccOn_iff_inter_subset` / 定理 `dirSupInaccOn_iff_inter_subset`

English:
theorem dirSupInaccOn_iff_inter_subset
  given: (hDL : IsLowerSet D)
  proof: .of_inter_subset
  mp h t hD ht₀ ht₁ a ha has := by
    by_contra! H
    have hcof : IsCofinalFor t (t \ s) := by grind [IsCofinalFor, not_subset]
    obtain ⟨x, hx, hxs⟩ := h (hDL sdiff_subset hD) (hcof.nonempty ht₀)
      (ht₁.of_isCofinalFor sdiff_subset hcof)
      (ha.of_isCofinalFor sdiff_subs

中文:
定理 dirSupInaccOn_iff_inter_subset
  条件: (hDL : IsLowerSet D)
  证明: .of_inter_subset
  mp h t hD ht₀ ht₁ a ha has := by
    by_contra! H
    have hcof : IsCofinalFor t (t \ s) := by grind [IsCofinalFor, not_subset]
    obtain ⟨x, hx, hxs⟩ := h (hDL sdiff_subset hD) (hcof.nonempty ht₀)
      (ht₁.of_isCofinalFor sdiff_subset hcof)
      (ha.of_isCofinalFor sdiff_subs

Depends on / 依赖: of_inter_subset
-/
theorem dirSupInaccOn_iff_inter_subset (hDL : IsLowerSet D) :
    DirSupInaccOn D s ↔ forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d ->
      forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s where
  mpr := .of_inter_subset
  mp h t hD ht₀ ht₁ a ha has := by
    by_contra! H
    have hcof : IsCofinalFor t (t \ s) := by grind [IsCofinalFor, not_subset]
    obtain ⟨x, hx, hxs⟩ := h (hDL sdiff_subset hD) (hcof.nonempty ht₀)
      (ht₁.of_isCofinalFor sdiff_subset hcof)
      (ha.of_isCofinalFor sdiff_subset hcof) has
    exact hx.2 hxs

/--
theorem `dirSupInacc_iff_inter_subset` / 定理 `dirSupInacc_iff_inter_subset`

English:
theorem dirSupInacc_iff_inter_subset
  proof: by
  simpa using dirSupInaccOn_iff_inter_subset isLowerSet_univ

中文:
定理 dirSupInacc_iff_inter_subset
  证明: by
  simpa using dirSupInaccOn_iff_inter_subset isLowerSet_univ

Depends on / 依赖: dirSupInaccOn_iff_inter_subset, isLowerSet_univ
-/
theorem dirSupInacc_iff_inter_subset :
    DirSupInacc s ↔ forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d ->
      forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s := by
  simpa using dirSupInaccOn_iff_inter_subset isLowerSet_univ

/--
lemma `IsUpperSet.dirSupClosed` / 引理 `IsUpperSet.dirSupClosed`

English:
lemma IsUpperSet.dirSupClosed
  given: (hs : IsUpperSet s)
  statement: DirSupClosed s
  proof: fun _d hds ⟨_b, hb⟩ _ _a ha => hs (ha.1 hb) hds hb

中文:
引理 IsUpperSet.dirSupClosed
  条件: (hs : IsUpperSet s)
  结论: DirSupClosed s
  证明: fun _d hds ⟨_b, hb⟩ _ _a ha => hs (ha.1 hb) hds hb
-/
lemma IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s :=
fun _d hds ⟨_b, hb⟩ _ _a ha => hs (ha.1 hb) hds hb

/--
lemma `IsUpperSet.dirSupClosedOn` / 引理 `IsUpperSet.dirSupClosedOn`

English:
lemma IsUpperSet.dirSupClosedOn
  given: (hs : IsUpperSet s)
  statement: DirSupClosedOn D s
  proof: hs.dirSupClosed.dirSupClosedOn

中文:
引理 IsUpperSet.dirSupClosedOn
  条件: (hs : IsUpperSet s)
  结论: DirSupClosedOn D s
  证明: hs.dirSupClosed.dirSupClosedOn

Depends on / 依赖: dirSupClosed, dirSupClosedOn, hs.dirSupClosed.dirSupClosedOn
-/
lemma IsUpperSet.dirSupClosedOn (hs : IsUpperSet s) : DirSupClosedOn D s :=
  hs.dirSupClosed.dirSupClosedOn

/--
lemma `IsLowerSet.dirSupInacc` / 引理 `IsLowerSet.dirSupInacc`

English:
lemma IsLowerSet.dirSupInacc
  given: (hs : IsLowerSet s)
  statement: DirSupInacc s
  proof: .of_compl hs.compl.dirSupClosed

中文:
引理 IsLowerSet.dirSupInacc
  条件: (hs : IsLowerSet s)
  结论: DirSupInacc s
  证明: .of_compl hs.compl.dirSupClosed

Depends on / 依赖: dirSupClosed, hs.compl.dirSupClosed, of_compl
-/
lemma IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s :=
  .of_compl hs.compl.dirSupClosed

/--
lemma `IsLowerSet.dirSupInaccOn` / 引理 `IsLowerSet.dirSupInaccOn`

English:
lemma IsLowerSet.dirSupInaccOn
  given: (hs : IsLowerSet s)
  statement: DirSupInaccOn D s
  proof: .of_compl hs.compl.dirSupClosedOn

中文:
引理 IsLowerSet.dirSupInaccOn
  条件: (hs : IsLowerSet s)
  结论: DirSupInaccOn D s
  证明: .of_compl hs.compl.dirSupClosedOn

Depends on / 依赖: dirSupClosedOn, hs.compl.dirSupClosedOn, of_compl
-/
lemma IsLowerSet.dirSupInaccOn (hs : IsLowerSet s) : DirSupInaccOn D s :=
  .of_compl hs.compl.dirSupClosedOn

/--
theorem `DirSupClosed.mem_imp_of_antisymmRel` / 定理 `DirSupClosed.mem_imp_of_antisymmRel`

English:
theorem DirSupClosed.mem_imp_of_antisymmRel
  statement: (hs : DirSupClosed s) {a b : α}
  proof: by
  apply hs (singleton_subset_iff.2 ha) ⟨a, rfl⟩ (directedOn_singleton a)
  rw [← isLUB_congr_of_antisymmRel h]
  exact isLUB_singleton

中文:
定理 DirSupClosed.mem_imp_of_antisymmRel
  结论: (hs : DirSupClosed s) {a b : α}
  证明: by
  apply hs (singleton_subset_iff.2 ha) ⟨a, rfl⟩ (directedOn_singleton a)
  rw [← isLUB_congr_of_antisymmRel h]
  exact isLUB_singleton

Depends on / 依赖: directedOn_singleton, isLUB_congr_of_antisymmRel, isLUB_singleton, singleton_subset_iff
-/
theorem DirSupClosed.mem_imp_of_antisymmRel (hs : DirSupClosed s) {a b : α}
    (h : AntisymmRel (· <= ·) a b) (ha : a in s) : b in s := by
  apply hs (singleton_subset_iff.2 ha) ⟨a, rfl⟩ (directedOn_singleton a)
  rw [← isLUB_congr_of_antisymmRel h]
  exact isLUB_singleton

/--
theorem `DirSupClosed.mem_iff_of_antisymmRel` / 定理 `DirSupClosed.mem_iff_of_antisymmRel`

English:
theorem DirSupClosed.mem_iff_of_antisymmRel
  statement: (hs : DirSupClosed s) {a b : α}
  proof: ⟨hs.mem_imp_of_antisymmRel h, hs.mem_imp_of_antisymmRel h.symm⟩

中文:
定理 DirSupClosed.mem_iff_of_antisymmRel
  结论: (hs : DirSupClosed s) {a b : α}
  证明: ⟨hs.mem_imp_of_antisymmRel h, hs.mem_imp_of_antisymmRel h.symm⟩

Depends on / 依赖: h.symm, hs.mem_imp_of_antisymmRel, mem_imp_of_antisymmRel
-/
theorem DirSupClosed.mem_iff_of_antisymmRel (hs : DirSupClosed s) {a b : α}
    (h : AntisymmRel (· <= ·) a b) : a in s ↔ b in s :=
  ⟨hs.mem_imp_of_antisymmRel h, hs.mem_imp_of_antisymmRel h.symm⟩

/--
theorem `DirSupInacc.mem_iff_of_antisymmRel` / 定理 `DirSupInacc.mem_iff_of_antisymmRel`

English:
theorem DirSupInacc.mem_iff_of_antisymmRel
  statement: (hs : DirSupInacc s) {a b : α}
  proof: by
  simpa [not_iff_not] using hs.compl.mem_iff_of_antisymmRel h

中文:
定理 DirSupInacc.mem_iff_of_antisymmRel
  结论: (hs : DirSupInacc s) {a b : α}
  证明: by
  simpa [not_iff_not] using hs.compl.mem_iff_of_antisymmRel h

Depends on / 依赖: hs.compl.mem_iff_of_antisymmRel, mem_iff_of_antisymmRel, not_iff_not
-/
theorem DirSupInacc.mem_iff_of_antisymmRel (hs : DirSupInacc s) {a b : α}
    (h : AntisymmRel (· <= ·) a b) : a in s ↔ b in s := by
  simpa [not_iff_not] using hs.compl.mem_iff_of_antisymmRel h

/--
lemma `dirSupClosed_Iic` / 引理 `dirSupClosed_Iic`

English:
lemma dirSupClosed_Iic
  given: (a : α)
  statement: DirSupClosed (Iic a)
  proof: fun _d h _ _ _a ha => (isLUB_le_iff ha).2 h

中文:
引理 dirSupClosed_Iic
  条件: (a : α)
  结论: DirSupClosed (Iic a)
  证明: fun _d h _ _ _a ha => (isLUB_le_iff ha).2 h

Depends on / 依赖: isLUB_le_iff
-/
lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) :=
  fun _d h _ _ _a ha => (isLUB_le_iff ha).2 h

/--
lemma `dirSupClosedOn_Iic` / 引理 `dirSupClosedOn_Iic`

English:
lemma dirSupClosedOn_Iic
  given: (a : α)
  statement: DirSupClosedOn D (Iic a)
  proof: (dirSupClosed_Iic a).dirSupClosedOn

中文:
引理 dirSupClosedOn_Iic
  条件: (a : α)
  结论: DirSupClosedOn D (Iic a)
  证明: (dirSupClosed_Iic a).dirSupClosedOn

Depends on / 依赖: dirSupClosedOn, dirSupClosed_Iic
-/
lemma dirSupClosedOn_Iic (a : α) : DirSupClosedOn D (Iic a) :=
  (dirSupClosed_Iic a).dirSupClosedOn

/--
lemma `dirSupInacc_Iic` / 引理 `dirSupInacc_Iic`

English:
lemma dirSupInacc_Iic
  given: (a : α)
  statement: DirSupInacc (Iic a)
  proof: (isLowerSet_Iic a).dirSupInacc

中文:
引理 dirSupInacc_Iic
  条件: (a : α)
  结论: DirSupInacc (Iic a)
  证明: (isLowerSet_Iic a).dirSupInacc

Depends on / 依赖: dirSupInacc, isLowerSet_Iic
-/
lemma dirSupInacc_Iic (a : α) : DirSupInacc (Iic a) :=
  (isLowerSet_Iic a).dirSupInacc

/--
lemma `dirSupInaccOn_Iic` / 引理 `dirSupInaccOn_Iic`

English:
lemma dirSupInaccOn_Iic
  given: (a : α)
  statement: DirSupInaccOn D (Iic a)
  proof: (isLowerSet_Iic a).dirSupInaccOn

中文:
引理 dirSupInaccOn_Iic
  条件: (a : α)
  结论: DirSupInaccOn D (Iic a)
  证明: (isLowerSet_Iic a).dirSupInaccOn

Depends on / 依赖: dirSupInaccOn, isLowerSet_Iic
-/
lemma dirSupInaccOn_Iic (a : α) : DirSupInaccOn D (Iic a) :=
  (isLowerSet_Iic a).dirSupInaccOn

end Preorder

namespace PartialOrder
variable [PartialOrder α]

/--
theorem `dirSupClosed_singleton` / 定理 `dirSupClosed_singleton`

English:
theorem dirSupClosed_singleton
  given: (a : α)
  statement: DirSupClosed {a}
  proof: by
  intro d hda hdn _ b hb
  rw [hdn.subset_singleton_iff] at hda
  subst hda
  exact mem_singleton_of_eq (hb.unique isLUB_singleton)

中文:
定理 dirSupClosed_singleton
  条件: (a : α)
  结论: DirSupClosed {a}
  证明: by
  intro d hda hdn _ b hb
  rw [hdn.subset_singleton_iff] at hda
  subst hda
  exact mem_singleton_of_eq (hb.unique isLUB_singleton)

Depends on / 依赖: hb.unique, hdn.subset_singleton_iff, isLUB_singleton, mem_singleton_of_eq, subset_singleton_iff, unique
-/
theorem dirSupClosed_singleton (a : α) : DirSupClosed {a} := by
  intro d hda hdn _ b hb
  rw [hdn.subset_singleton_iff] at hda
  subst hda
  exact mem_singleton_of_eq (hb.unique isLUB_singleton)

/--
theorem `dirSupClosedOn_singleton` / 定理 `dirSupClosedOn_singleton`

English:
theorem dirSupClosedOn_singleton
  given: (a : α)
  statement: DirSupClosedOn D {a}
  proof: (dirSupClosed_singleton a).dirSupClosedOn

中文:
定理 dirSupClosedOn_singleton
  条件: (a : α)
  结论: DirSupClosedOn D {a}
  证明: (dirSupClosed_singleton a).dirSupClosedOn

Depends on / 依赖: dirSupClosedOn, dirSupClosed_singleton
-/
theorem dirSupClosedOn_singleton (a : α) : DirSupClosedOn D {a} :=
  (dirSupClosed_singleton a).dirSupClosedOn

end PartialOrder

section LinearOrder
variable [LinearOrder α]

/--
theorem `dirSupClosedOn_iff_of_linearOrder` / 定理 `dirSupClosedOn_iff_of_linearOrder`

English:
theorem dirSupClosedOn_iff_of_linearOrder
  proof: by
  simp [DirSupClosedOn]

中文:
定理 dirSupClosedOn_iff_of_linearOrder
  证明: by
  simp [DirSupClosedOn]

Depends on / 依赖: DirSupClosedOn
-/
theorem dirSupClosedOn_iff_of_linearOrder :
    DirSupClosedOn D s ↔ forall ⦃d⦄, d in D -> d subseteq s -> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s := by
  simp [DirSupClosedOn]

/--
theorem `dirSupClosed_iff_of_linearOrder` / 定理 `dirSupClosed_iff_of_linearOrder`

English:
theorem dirSupClosed_iff_of_linearOrder
  proof: by
  simp [DirSupClosed]

中文:
定理 dirSupClosed_iff_of_linearOrder
  证明: by
  simp [DirSupClosed]

Depends on / 依赖: DirSupClosed
-/
theorem dirSupClosed_iff_of_linearOrder :
    DirSupClosed s ↔ forall ⦃d⦄, d subseteq s -> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s := by
  simp [DirSupClosed]

/--
theorem `dirSupInaccOn_iff_of_linearOrder` / 定理 `dirSupInaccOn_iff_of_linearOrder`

English:
theorem dirSupInaccOn_iff_of_linearOrder
  proof: by
  simp [DirSupInaccOn]

中文:
定理 dirSupInaccOn_iff_of_linearOrder
  证明: by
  simp [DirSupInaccOn]

Depends on / 依赖: DirSupInaccOn, IsAdjoinRoot, IsAdjoinRoot.root
-/
theorem dirSupInaccOn_iff_of_linearOrder :
    DirSupInaccOn D s ↔
      forall ⦃d⦄, d in D -> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty := by
  simp [DirSupInaccOn]

/--
theorem `dirSupInacc_iff_of_linearOrder` / 定理 `dirSupInacc_iff_of_linearOrder`

English:
theorem dirSupInacc_iff_of_linearOrder
  proof: by
  simp [DirSupInacc]

中文:
定理 dirSupInacc_iff_of_linearOrder
  证明: by
  simp [DirSupInacc]

Depends on / 依赖: DirSupInacc
-/
theorem dirSupInacc_iff_of_linearOrder :
    DirSupInacc s ↔ forall ⦃d⦄, d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty := by
  simp [DirSupInacc]

end LinearOrder

section CompleteLattice
variable [CompleteLattice α]

/--
lemma `dirSupClosedOn_iff_forall_sSup` / 引理 `dirSupClosedOn_iff_forall_sSup`

English:
lemma dirSupClosedOn_iff_forall_sSup
  statement: DirSupClosedOn D s ↔
  proof: by
  simp [DirSupClosedOn, isLUB_iff_sSup_eq]

中文:
引理 dirSupClosedOn_iff_forall_sSup
  结论: DirSupClosedOn D s ↔
  证明: by
  simp [DirSupClosedOn, isLUB_iff_sSup_eq]

Depends on / 依赖: DirSupClosedOn, isLUB_iff_sSup_eq
-/
lemma dirSupClosedOn_iff_forall_sSup : DirSupClosedOn D s ↔
    forall ⦃d⦄, d in D -> d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s := by
  simp [DirSupClosedOn, isLUB_iff_sSup_eq]

/--
lemma `dirSupInaccOn_iff_forall_sSup` / 引理 `dirSupInaccOn_iff_forall_sSup`

English:
lemma dirSupInaccOn_iff_forall_sSup
  statement: DirSupInaccOn D s ↔
  proof: by
  simp [DirSupInaccOn, isLUB_iff_sSup_eq]

中文:
引理 dirSupInaccOn_iff_forall_sSup
  结论: DirSupInaccOn D s ↔
  证明: by
  simp [DirSupInaccOn, isLUB_iff_sSup_eq]

Depends on / 依赖: DirSupInaccOn, isLUB_iff_sSup_eq
-/
lemma dirSupInaccOn_iff_forall_sSup : DirSupInaccOn D s ↔
    forall ⦃d⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s -> (d inter s).Nonempty := by
  simp [DirSupInaccOn, isLUB_iff_sSup_eq]

/--
lemma `dirSupClosed_iff_forall_sSup` / 引理 `dirSupClosed_iff_forall_sSup`

English:
lemma dirSupClosed_iff_forall_sSup
  statement: DirSupClosed s ↔
  proof: by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

中文:
引理 dirSupClosed_iff_forall_sSup
  结论: DirSupClosed s ↔
  证明: by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

Depends on / 依赖: DirSupClosed, isLUB_iff_sSup_eq
-/
lemma dirSupClosed_iff_forall_sSup : DirSupClosed s ↔
    forall ⦃d⦄, d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s := by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

/--
lemma `dirSupInacc_iff_forall_sSup` / 引理 `dirSupInacc_iff_forall_sSup`

English:
lemma dirSupInacc_iff_forall_sSup
  statement: DirSupInacc s ↔
  proof: by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

中文:
引理 dirSupInacc_iff_forall_sSup
  结论: DirSupInacc s ↔
  证明: by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

Depends on / 依赖: DirSupInacc, isLUB_iff_sSup_eq
-/
lemma dirSupInacc_iff_forall_sSup : DirSupInacc s ↔
    forall ⦃d⦄, d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s -> (d inter s).Nonempty := by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

end CompleteLattice
