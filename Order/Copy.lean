/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Yaël Dillies
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/

@[expose] public section


open Order

universe u

variable {α : Type u}

/-- A function to create a provable equal copy of a top order
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `OrderTop.copy` / `OrderTop.copy` 的定义

English:
definition OrderTop.copy
  signature: {h : LE α} {h' : LE α} (c : @OrderTop α h')
  body: @OrderTop.mk α h { top := top } fun _ => by simp [eq_top, le_eq]

中文:
定义 有顶序.copy
  签名: {h : LE α} {h' : LE α} (c : @有顶序 α h')
  定义体: @OrderTop.mk α h { top := top } fun _ => by simp [eq_top, le_eq]

Depends on / 依赖: OrderTop, OrderTop.mk, eq_top, le_eq
-/
def OrderTop.copy {h : LE α} {h' : LE α} (c : @OrderTop α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (le_eq : forall x y : α, (@LE.le α h) x y ↔ x <= y) : @OrderTop α h :=
  @OrderTop.mk α h { top := top } fun _ => by simp [eq_top, le_eq]

/-- A function to create a provable equal copy of a bottom order
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `OrderBot.copy` / `OrderBot.copy` 的定义

English:
definition OrderBot.copy
  signature: {h : LE α} {h' : LE α} (c : @OrderBot α h')
  body: @OrderBot.mk α h { bot := bot } fun _ => by simp [eq_bot, le_eq]

中文:
定义 有底序.copy
  签名: {h : LE α} {h' : LE α} (c : @有底序 α h')
  定义体: @OrderBot.mk α h { bot := bot } fun _ => by simp [eq_bot, le_eq]

Depends on / 依赖: OrderBot, OrderBot.mk, eq_bot, le_eq
-/
def OrderBot.copy {h : LE α} {h' : LE α} (c : @OrderBot α h')
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : forall x y : α, (@LE.le α h) x y ↔ x <= y) : @OrderBot α h :=
  @OrderBot.mk α h { bot := bot } fun _ => by simp [eq_bot, le_eq]

/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `BoundedOrder.copy` / `BoundedOrder.copy` 的定义

English:
definition BoundedOrder.copy
  signature: {h : LE α} {h' : LE α} (c : @BoundedOrder α h')
  body: @BoundedOrder.mk α h (@OrderTop.mk α h { top := top } (fun _ => by simp [eq_top, le_eq]))
    (@OrderBot.mk α h { bot := bot } (fun _ => by simp [eq_bot, le_eq]))

中文:
定义 有界序.copy
  签名: {h : LE α} {h' : LE α} (c : @有界序 α h')
  定义体: @BoundedOrder.mk α h (@OrderTop.mk α h { top := top } (fun _ => by simp [eq_top, le_eq]))
    (@OrderBot.mk α h { bot := bot } (fun _ => by simp [eq_bot, le_eq]))

Depends on / 依赖: BoundedOrder, BoundedOrder.mk, OrderBot, OrderBot.mk, OrderTop, OrderTop.mk, eq_bot, eq_top, le_eq
-/
def BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : forall x y : α, (@LE.le α h) x y ↔ x <= y) : @BoundedOrder α h :=
  @BoundedOrder.mk α h (@OrderTop.mk α h { top := top } (fun _ => by simp [eq_top, le_eq]))
    (@OrderBot.mk α h { bot := bot } (fun _ => by simp [eq_bot, le_eq]))

/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `Lattice.copy` / `Lattice.copy` 的定义

English:
definition Lattice.copy
  signature: (c : Lattice α)
  body: le
  sup := sup
  inf := inf
  lt := fun a b => le a b ∧ ¬ le b a
  le_refl := by intros; simp [eq_le]
  le_trans := by intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  le_antisymm := by intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  le_sup_left := by intros; simp [eq_le, eq_sup]
  le_sup_right := by intros; simp [eq_le, eq_sup]
  sup_le := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  inf_le_left := by intros; simp [eq_le, eq_inf]
  inf_le_right := by intros; simp [eq_le, eq_inf]
  le_inf := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]

中文:
定义 格.copy
  签名: (c : 格 α)
  定义体: le
  sup := sup
  inf := inf
  lt := fun a b => le a b ∧ ¬ le b a
  le_refl := by intros; simp [eq_le]
  le_trans := by intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  le_antisymm := by intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  le_sup_left := by intros; simp [eq_le, eq_sup]
  le_sup_right := by intros; simp [eq_le, eq_sup]
  sup_le := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  inf_le_left := by intros; simp [eq_le, eq_inf]
  inf_le_right := by intros; simp [eq_le, eq_inf]
  le_inf := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]
-/
def Lattice.copy (c : Lattice α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min) : Lattice α where
  le := le
  sup := sup
  inf := inf
  lt := fun a b => le a b ∧ ¬ le b a
  le_refl := by intros; simp [eq_le]
  le_trans := by intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  le_antisymm := by intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  le_sup_left := by intros; simp [eq_le, eq_sup]
  le_sup_right := by intros; simp [eq_le, eq_sup]
  sup_le := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  inf_le_left := by intros; simp [eq_le, eq_inf]
  inf_le_right := by intros; simp [eq_le, eq_inf]
  le_inf := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `DistribLattice.copy` / `DistribLattice.copy` 的定义

English:
definition DistribLattice.copy
  signature: (c : DistribLattice α)
  body: Lattice.copy (@DistribLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  le_sup_inf := by intros; simp +instances [eq_le, eq_sup, eq_inf, le_sup_inf]

中文:
定义 Distrib格.copy
  签名: (c : Distrib格 α)
  定义体: Lattice.copy (@DistribLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  le_sup_inf := by intros; simp +instances [eq_le, eq_sup, eq_inf, le_sup_inf]

Depends on / 依赖: DistribLattice, DistribLattice.toLattice, Lattice, Lattice.copy, eq_inf, eq_le, eq_sup, toLattice
-/
def DistribLattice.copy (c : DistribLattice α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min) : DistribLattice α where
  toLattice := Lattice.copy (@DistribLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  le_sup_inf := by intros; simp +instances [eq_le, eq_sup, eq_inf, le_sup_inf]

/-- A function to create a provable equal copy of a generalised heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `GeneralizedHeytingAlgebra.copy` / `GeneralizedHeytingAlgebra.copy` 的定义

English:
definition GeneralizedHeytingAlgebra.copy
  signature: (c : GeneralizedHeytingAlgebra α)
  body: Lattice.copy (@GeneralizedHeytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderTop.copy (@GeneralizedHeytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  himp := himp
  le_himp_iff _ _ _ := by simp +instances [eq_le, eq_himp, eq_inf]

中文:
定义 GeneralizedHeyting代数.copy
  签名: (c : GeneralizedHeyting代数 α)
  定义体: Lattice.copy (@GeneralizedHeytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderTop.copy (@GeneralizedHeytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  himp := himp
  le_himp_iff _ _ _ := by simp +instances [eq_le, eq_himp, eq_inf]

Depends on / 依赖: GeneralizedHeytingAlgebra, GeneralizedHeytingAlgebra.toLattice, Lattice, Lattice.copy, eq_inf, eq_le, eq_sup, toLattice
-/
def GeneralizedHeytingAlgebra.copy (c : GeneralizedHeytingAlgebra α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α -> α -> α) (eq_himp : himp = (by infer_instance : HImp α).himp) :
    GeneralizedHeytingAlgebra α where
  __ := Lattice.copy (@GeneralizedHeytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderTop.copy (@GeneralizedHeytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  himp := himp
  le_himp_iff _ _ _ := by simp +instances [eq_le, eq_himp, eq_inf]

/-- A function to create a provable equal copy of a generalised co-Heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `GeneralizedCoheytingAlgebra.copy` / `GeneralizedCoheytingAlgebra.copy` 的定义

English:
definition GeneralizedCoheytingAlgebra.copy
  signature: (c : GeneralizedCoheytingAlgebra α)
  body: Lattice.copy (@GeneralizedCoheytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderBot.copy (@GeneralizedCoheytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  sdiff := sdiff
  sdiff_le_iff := by simp +instances [eq_le, eq_sdiff, eq_sup]

中文:
定义 GeneralizedCoheyting代数.copy
  签名: (c : GeneralizedCoheyting代数 α)
  定义体: Lattice.copy (@GeneralizedCoheytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderBot.copy (@GeneralizedCoheytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  sdiff := sdiff
  sdiff_le_iff := by simp +instances [eq_le, eq_sdiff, eq_sup]

Depends on / 依赖: GeneralizedCoheytingAlgebra, GeneralizedCoheytingAlgebra.toLattice, Lattice, Lattice.copy, eq_inf, eq_le, eq_sup, toLattice
-/
def GeneralizedCoheytingAlgebra.copy (c : GeneralizedCoheytingAlgebra α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α -> α -> α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff) :
    GeneralizedCoheytingAlgebra α where
  __ := Lattice.copy (@GeneralizedCoheytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderBot.copy (@GeneralizedCoheytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  sdiff := sdiff
  sdiff_le_iff := by simp +instances [eq_le, eq_sdiff, eq_sup]

/-- A function to create a provable equal copy of a heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `HeytingAlgebra.copy` / `HeytingAlgebra.copy` 的定义

English:
definition HeytingAlgebra.copy
  signature: (c : HeytingAlgebra α)
  body: GeneralizedHeytingAlgebra.copy
    (@HeytingAlgebra.toGeneralizedHeytingAlgebra α c) le eq_le top eq_top sup eq_sup inf eq_inf himp
    eq_himp
  __ := OrderBot.copy (@HeytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  compl := compl
  himp_bot := by simp +instances [eq_le, eq_himp, eq_bot, eq_compl]

中文:
定义 Heyting代数.copy
  签名: (c : Heyting代数 α)
  定义体: GeneralizedHeytingAlgebra.copy
    (@HeytingAlgebra.toGeneralizedHeytingAlgebra α c) le eq_le top eq_top sup eq_sup inf eq_inf himp
    eq_himp
  __ := OrderBot.copy (@HeytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  compl := compl
  himp_bot := by simp +instances [eq_le, eq_himp, eq_bot, eq_compl]

Depends on / 依赖: GeneralizedHeytingAlgebra, GeneralizedHeytingAlgebra.copy
-/
def HeytingAlgebra.copy (c : HeytingAlgebra α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α -> α -> α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α -> α) (eq_compl : compl = (by infer_instance : Compl α).compl) :
    HeytingAlgebra α where
  toGeneralizedHeytingAlgebra := GeneralizedHeytingAlgebra.copy
    (@HeytingAlgebra.toGeneralizedHeytingAlgebra α c) le eq_le top eq_top sup eq_sup inf eq_inf himp
    eq_himp
  __ := OrderBot.copy (@HeytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  compl := compl
  himp_bot := by simp +instances [eq_le, eq_himp, eq_bot, eq_compl]

/-- A function to create a provable equal copy of a co-Heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `CoheytingAlgebra.copy` / `CoheytingAlgebra.copy` 的定义

English:
definition CoheytingAlgebra.copy
  signature: (c : CoheytingAlgebra α)
  body: GeneralizedCoheytingAlgebra.copy
    (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra α c) le eq_le bot eq_bot sup eq_sup inf eq_inf
      sdiff eq_sdiff
  __ := OrderTop.copy (@CoheytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  hnot := hnot
  top_sdiff := by simp +instances [eq_le, eq_sdiff, eq_top, eq_hnot]

中文:
定义 余heyting代数.copy
  签名: (c : 余heyting代数 α)
  定义体: GeneralizedCoheytingAlgebra.copy
    (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra α c) le eq_le bot eq_bot sup eq_sup inf eq_inf
      sdiff eq_sdiff
  __ := OrderTop.copy (@CoheytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  hnot := hnot
  top_sdiff := by simp +instances [eq_le, eq_sdiff, eq_top, eq_hnot]

Depends on / 依赖: GeneralizedCoheytingAlgebra, GeneralizedCoheytingAlgebra.copy
-/
def CoheytingAlgebra.copy (c : CoheytingAlgebra α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α -> α -> α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α -> α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot) :
    CoheytingAlgebra α where
  toGeneralizedCoheytingAlgebra := GeneralizedCoheytingAlgebra.copy
    (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra α c) le eq_le bot eq_bot sup eq_sup inf eq_inf
      sdiff eq_sdiff
  __ := OrderTop.copy (@CoheytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ => .rfl)
  hnot := hnot
  top_sdiff := by simp +instances [eq_le, eq_sdiff, eq_top, eq_hnot]

/-- A function to create a provable equal copy of a bi-Heyting algebra
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `BiheytingAlgebra.copy` / `BiheytingAlgebra.copy` 的定义

English:
definition BiheytingAlgebra.copy
  signature: (c : BiheytingAlgebra α)
  body: HeytingAlgebra.copy (@BiheytingAlgebra.toHeytingAlgebra α c) le eq_le top
    eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl
  __ := CoheytingAlgebra.copy (@BiheytingAlgebra.toCoheytingAlgebra α c) le eq_le top eq_top bot
    eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

中文:
定义 Biheyting代数.copy
  签名: (c : Biheyting代数 α)
  定义体: HeytingAlgebra.copy (@BiheytingAlgebra.toHeytingAlgebra α c) le eq_le top
    eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl
  __ := CoheytingAlgebra.copy (@BiheytingAlgebra.toCoheytingAlgebra α c) le eq_le top eq_top bot
    eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

Depends on / 依赖: BiheytingAlgebra, BiheytingAlgebra.toHeytingAlgebra, HeytingAlgebra, HeytingAlgebra.copy, eq_le, toHeytingAlgebra
-/
def BiheytingAlgebra.copy (c : BiheytingAlgebra α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α -> α -> α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α -> α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (himp : α -> α -> α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α -> α) (eq_compl : compl = (by infer_instance : Compl α).compl) :
    BiheytingAlgebra α where
  toHeytingAlgebra := HeytingAlgebra.copy (@BiheytingAlgebra.toHeytingAlgebra α c) le eq_le top
    eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl
  __ := CoheytingAlgebra.copy (@BiheytingAlgebra.toCoheytingAlgebra α c) le eq_le top eq_top bot
    eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `CompleteLattice.copy` / `CompleteLattice.copy` 的定义

English:
definition CompleteLattice.copy
  signature: (c : CompleteLattice α)
  body: Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  top := top
  bot := bot
  sSup := sSup
  sInf := sInf
  isLUB_sSup _ := by simp +instances only [eq_le, eq_sSup, isLUB_sSup]
  isGLB_sInf _ := by simp +instances only [eq_le, eq_sInf, isGLB_sInf]
  le_top := by intros; simp +instances [eq_le, eq_top]
  bot_le := by intros; simp +instances [eq_le, eq_bot]

中文:
定义 完备格.copy
  签名: (c : 完备格 α)
  定义体: Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  top := top
  bot := bot
  sSup := sSup
  sInf := sInf
  isLUB_sSup _ := by simp +instances only [eq_le, eq_sSup, isLUB_sSup]
  isGLB_sInf _ := by simp +instances only [eq_le, eq_sInf, isGLB_sInf]
  le_top := by intros; simp +instances [eq_le, eq_top]
  bot_le := by intros; simp +instances [eq_le, eq_bot]

Depends on / 依赖: CompleteLattice, CompleteLattice.toLattice, Lattice, Lattice.copy, eq_inf, eq_le, eq_sup, toLattice
-/
def CompleteLattice.copy (c : CompleteLattice α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sSup : Set α -> α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α -> α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteLattice α where
  toLattice := Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  top := top
  bot := bot
  sSup := sSup
  sInf := sInf
  isLUB_sSup _ := by simp +instances only [eq_le, eq_sSup, isLUB_sSup]
  isGLB_sInf _ := by simp +instances only [eq_le, eq_sInf, isGLB_sInf]
  le_top := by intros; simp +instances [eq_le, eq_top]
  bot_le := by intros; simp +instances [eq_le, eq_bot]

/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
@[instance_reducible]
/--
Definition of `Frame.copy` / `Frame.copy` 的定义

English:
definition Frame.copy
  signature: (c : Frame α) (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
  body: CompleteLattice.copy (@Frame.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := HeytingAlgebra.copy (@Frame.toHeytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl

中文:
定义 框架.copy
  签名: (c : 框架 α) (le : α -> α -> 命题) (eq_le : le = (by infer_instance : LE α).le)
  定义体: CompleteLattice.copy (@Frame.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := HeytingAlgebra.copy (@Frame.toHeytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl

Depends on / 依赖: CompleteLattice, CompleteLattice.copy, Frame.toCompleteLattice, toCompleteLattice
-/
def Frame.copy (c : Frame α) (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α -> α -> α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α -> α) (eq_compl : compl = (by infer_instance : Compl α).compl)
    (sSup : Set α -> α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α -> α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Frame α where
  toCompleteLattice := CompleteLattice.copy (@Frame.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := HeytingAlgebra.copy (@Frame.toHeytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl

/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
@[instance_reducible]
/--
Definition of `Coframe.copy` / `Coframe.copy` 的定义

English:
definition Coframe.copy
  signature: (c : Coframe α) (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
  body: CompleteLattice.copy (@Coframe.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := CoheytingAlgebra.copy (@Coframe.toCoheytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

中文:
定义 余frame.copy
  签名: (c : 余frame α) (le : α -> α -> 命题) (eq_le : le = (by infer_instance : LE α).le)
  定义体: CompleteLattice.copy (@Coframe.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := CoheytingAlgebra.copy (@Coframe.toCoheytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

Depends on / 依赖: Coframe, Coframe.toCompleteLattice, CompleteLattice, CompleteLattice.copy, Polynomial, Polynomial.smeval, ascPochhammer, factorial, n.factorial, smeval, toCompleteLattice
-/
def Coframe.copy (c : Coframe α) (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α -> α -> α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α -> α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (sSup : Set α -> α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α -> α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Coframe α where
  toCompleteLattice := CompleteLattice.copy (@Coframe.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := CoheytingAlgebra.copy (@Coframe.toCoheytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `CompleteDistribLattice.copy` / `CompleteDistribLattice.copy` 的定义

English:
definition CompleteDistribLattice.copy
  signature: (c : CompleteDistribLattice α)
  body: Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf himp eq_himp compl eq_compl sSup eq_sSup sInf eq_sInf
  __ := Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot sSup eq_sSup sInf eq_sInf

中文:
定义 完备分配格.copy
  签名: (c : 完备分配格 α)
  定义体: Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf himp eq_himp compl eq_compl sSup eq_sSup sInf eq_sInf
  __ := Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot sSup eq_sSup sInf eq_sInf

Depends on / 依赖: CompleteDistribLattice, CompleteDistribLattice.toFrame, Frame.copy, eq_bot, eq_le, eq_top, toFrame
-/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α -> α -> α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α -> α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (himp : α -> α -> α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α -> α) (eq_compl : compl = (by infer_instance : Compl α).compl)
    (sSup : Set α -> α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α -> α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteDistribLattice α where
  toFrame := Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf himp eq_himp compl eq_compl sSup eq_sSup sInf eq_sInf
  __ := Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot sSup eq_sSup sInf eq_sInf

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
@[instance_reducible]
/--
Definition of `ConditionallyCompleteLattice.copy` / `ConditionallyCompleteLattice.copy` 的定义

English:
definition ConditionallyCompleteLattice.copy
  signature: (c : ConditionallyCompleteLattice α)
  body: Lattice.copy (@ConditionallyCompleteLattice.toLattice α c)
    le eq_le sup eq_sup inf eq_inf
  sSup := sSup
  sInf := sInf
  isLUB_csSup := by subst_vars; exact c.isLUB_csSup
  isGLB_csInf := by subst_vars; exact c.isGLB_csInf

中文:
定义 条件完备格.copy
  签名: (c : 条件完备格 α)
  定义体: Lattice.copy (@ConditionallyCompleteLattice.toLattice α c)
    le eq_le sup eq_sup inf eq_inf
  sSup := sSup
  sInf := sInf
  isLUB_csSup := by subst_vars; exact c.isLUB_csSup
  isGLB_csInf := by subst_vars; exact c.isGLB_csInf

Depends on / 依赖: ConditionallyCompleteLattice, ConditionallyCompleteLattice.toLattice, Lattice, Lattice.copy, toLattice
-/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α)
    (le : α -> α -> Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α -> α -> α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α -> α -> α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sSup : Set α -> α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α -> α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    ConditionallyCompleteLattice α where
  toLattice := Lattice.copy (@ConditionallyCompleteLattice.toLattice α c)
    le eq_le sup eq_sup inf eq_inf
  sSup := sSup
  sInf := sInf
  isLUB_csSup := by subst_vars; exact c.isLUB_csSup
  isGLB_csInf := by subst_vars; exact c.isGLB_csInf
