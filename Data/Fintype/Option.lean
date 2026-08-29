/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Option

/-!
# fintype instances for option
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

open Function

open Nat

universe u v

variable {α β : Type*}

open Finset

instance {α : Type*} [Fintype α] : Fintype (Option α) :=
  ⟨Finset.insertNone univ, fun a => by simp⟩

instance {α : Type*} [Finite α] : Finite (Option α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

/--
theorem `univ_option` / 定理 `univ_option`

English:
theorem univ_option
  given: (α : Type*) [Fintype α]
  statement: (univ : Finset (Option α)) = insertNone univ
  proof: rfl

@[simp]

中文:
定理 univ_option
  条件: (α : 类型) [有限类型 α]
  结论: (univ : 有限集 (选项类型 α)) = insertNone univ
  证明: rfl

@[simp]
-/
theorem univ_option (α : Type*) [Fintype α] : (univ : Finset (Option α)) = insertNone univ :=
  rfl

@[simp]
/--
theorem `Fintype.card_option` / 定理 `Fintype.card_option`

English:
theorem Fintype.card_option
  given: {α : Type*} [Fintype α]
  proof: (Finset.card_cons (by simp)).trans congr_arg₂ _ (card_map _) rfl

中文:
定理 有限类型.card_option
  条件: {α : 类型} [有限类型 α]
  证明: (Finset.card_cons (by simp)).trans congr_arg₂ _ (card_map _) rfl

Depends on / 依赖: Finset, Finset.card_cons, card_cons, card_map
-/
theorem Fintype.card_option {α : Type*} [Fintype α] :
    Fintype.card (Option α) = Fintype.card α + 1 :=
(Finset.card_cons (by simp)).trans congr_arg₂ _ (card_map _) rfl

/-- If `Option α` is a `Fintype` then so is `α` -/
@[instance_reducible]
/--
Definition of `fintypeOfOption` / `fintypeOfOption` 的定义

English:
definition fintypeOfOption
  signature: {α : Type*} [Fintype (Option α)]
  body: ⟨Finset.eraseNone (Fintype.elems (α := Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩

中文:
定义 fintypeOfOption
  签名: {α : 类型} [有限类型 (选项类型 α)]
  定义体: ⟨Finset.eraseNone (Fintype.elems (α := Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩

Depends on / 依赖: Finset, Finset.eraseNone, Fintype, Fintype.complete, Fintype.elems, complete, eraseNone, mem_eraseNone, mem_eraseNone.mpr
-/
def fintypeOfOption {α : Type*} [Fintype (Option α)] : Fintype α :=
  ⟨Finset.eraseNone (Fintype.elems (α := Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩

/-- A type is a `Fintype` if its successor (using `Option`) is a `Fintype`. -/
@[instance_reducible]
/--
Definition of `fintypeOfOptionEquiv` / `fintypeOfOptionEquiv` 的定义

English:
definition fintypeOfOptionEquiv
  signature: [Fintype α] (f : α ≃ Option β)
  body: haveI := Fintype.ofEquiv _ f
  fintypeOfOption

中文:
定义 fintypeOfOptionEquiv
  签名: [有限类型 α] (f : α ≃ 选项类型 β)
  定义体: haveI := Fintype.ofEquiv _ f
  fintypeOfOption

Depends on / 依赖: Fintype, Fintype.ofEquiv, fintypeOfOption, length, ofEquiv
-/
def fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β :=
  haveI := Fintype.ofEquiv _ f
  fintypeOfOption

namespace Fintype

/--
Definition of `truncRecEmptyOption` / `truncRecEmptyOption` 的定义

English:
definition truncRecEmptyOption
  signature: {P : Type u -> Sort v} (of_equiv : forall {α β}, α ≃ β -> P α -> P β)
  body: by
  suffices forall n : Nat, Trunc (P (ULift <| Fin n)) by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (Equiv.ulift.trans e.symm) h
  intro n
  induction n with
  | zero =>
    have : card PEmpty = card (ULift (Fin 0)) := by
      simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.mk
    exact of_equiv e h_empty
  | succ n ih =>
    have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    exact of_equiv e (h_option ih)

中文:
定义 truncRecEmptyOption
  签名: {P : 类型u -> 类型层 v} (of_equiv : 对任意 {α β}, α ≃ β -> P α -> P β)
  定义体: by
  suffices forall n : Nat, Trunc (P (ULift <| Fin n)) by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (Equiv.ulift.trans e.symm) h
  intro n
  induction n with
  | zero =>
    have : card PEmpty = card (ULift (Fin 0)) := by
      simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.mk
    exact of_equiv e h_empty
  | succ n ih =>
    have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    exact of_equiv e (h_option ih)

Depends on / 依赖: Equiv.ulift.trans, Fintype, Fintype.card, Fintype.truncEquivFin, PEmpty, Trunc.bind, Trunc.map, Trunc.mk, card_fin, card_pempty, card_ulift, e.symm, h_empty, n.succ, of_equiv, truncEquivFin, truncEquivOfCardEq
-/
def truncRecEmptyOption {P : Type u -> Sort v} (of_equiv : forall {α β}, α ≃ β -> P α -> P β)
    (h_empty : P PEmpty) (h_option : forall {α} [Fintype α] [DecidableEq α], P α -> P (Option α))
    (α : Type u) [Fintype α] [DecidableEq α] : Trunc (P α) := by
  suffices forall n : Nat, Trunc (P (ULift <| Fin n)) by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (Equiv.ulift.trans e.symm) h
  intro n
  induction n with
  | zero =>
    have : card PEmpty = card (ULift (Fin 0)) := by
      simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.mk
    exact of_equiv e h_empty
  | succ n ih =>
    have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    exact of_equiv e (h_option ih)

/-- An induction principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
@[elab_as_elim]
/--
theorem `induction_empty_option` / 定理 `induction_empty_option`

English:
theorem induction_empty_option
  statement: {P : forall (α : Type u) [Fintype α], Prop}
  proof: by
  obtain ⟨p⟩ :=
    let f_empty := fun i => by convert! h_empty
    let h_option : forall {α : Type u} [Fintype α] [DecidableEq α],
          (forall (h : Fintype α), P α) -> forall (h : Fintype (Option α)), P (Option α) := by
      rintro α hα - Pα hα'
      convert! h_option α (Pα _)
    @truncRecEmptyOption (fun α => forall h, @P α h) (@fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      f_empty h_option α _ (Classical.decEq α)
  exact p _
  -- ·

中文:
定理 induction_empty_option
  结论: {P : 对任意 (α : 类型u) [有限类型 α], 命题}
  证明: by
  obtain ⟨p⟩ :=
    let f_empty := fun i => by convert! h_empty
    let h_option : forall {α : Type u} [Fintype α] [DecidableEq α],
          (forall (h : Fintype α), P α) -> forall (h : Fintype (Option α)), P (Option α) := by
      rintro α hα - Pα hα'
      convert! h_option α (Pα _)
    @truncRecEmptyOption (fun α => forall h, @P α h) (@fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      f_empty h_option α _ (Classical.decEq α)
  exact p _
  -- ·

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Fintype, convert, f_empty, h_empty, h_option, implicitDefEqProofs, length, of_equiv, truncRecEmptyOption
-/
theorem induction_empty_option {P : forall (α : Type u) [Fintype α], Prop}
    (of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) -> @P β ‹_›)
    (h_empty : P PEmpty) (h_option : forall (α) [Fintype α], P α -> P (Option α)) (α : Type u)
    [h_fintype : Fintype α] : P α := by
  obtain ⟨p⟩ :=
    let f_empty := fun i => by convert! h_empty
    let h_option : forall {α : Type u} [Fintype α] [DecidableEq α],
          (forall (h : Fintype α), P α) -> forall (h : Fintype (Option α)), P (Option α) := by
      rintro α hα - Pα hα'
      convert! h_option α (Pα _)
    @truncRecEmptyOption (fun α => forall h, @P α h) (@fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      f_empty h_option α _ (Classical.decEq α)
  exact p _
  -- ·

end Fintype

/--
theorem `Finite.induction_empty_option` / 定理 `Finite.induction_empty_option`

English:
theorem Finite.induction_empty_option
  statement: {P : Type u -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β)
  proof: by
  cases nonempty_fintype α
  refine Fintype.induction_empty_option ?_ ?_ ?_ α
  exacts [fun α β _ => of_equiv, h_empty, @h_option]

中文:
定理 有限.induction_empty_option
  结论: {P : 类型u -> 命题} (of_equiv : 对任意 {α β}, α ≃ β -> P α -> P β)
  证明: by
  cases nonempty_fintype α
  refine Fintype.induction_empty_option ?_ ?_ ?_ α
  exacts [fun α β _ => of_equiv, h_empty, @h_option]

Depends on / 依赖: Fintype, Fintype.induction_empty_option, exacts, h_empty, h_option, induction_empty_option, nonempty_fintype, of_equiv
-/
theorem Finite.induction_empty_option {P : Type u -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β)
    (h_empty : P PEmpty) (h_option : forall {α} [Fintype α], P α -> P (Option α)) (α : Type u)
    [Finite α] : P α := by
  cases nonempty_fintype α
  refine Fintype.induction_empty_option ?_ ?_ ?_ α
  exacts [fun α β _ => of_equiv, h_empty, @h_option]
