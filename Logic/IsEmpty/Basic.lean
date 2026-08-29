/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Relator

/-!
In this file we prove some basic properties about the typeclass `IsEmpty`.
-/

public section

variable {α β γ : Sort*}

@[simp, push]
/--
theorem `not_nonempty_iff` / 定理 `not_nonempty_iff`

English:
theorem not_nonempty_iff
  statement: ¬Nonempty α ↔ IsEmpty α
  proof: ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h1 h2 => h2.elim h1.elim⟩

@[simp, push]

中文:
定理 not_nonempty_iff
  结论: ¬Nonempty α ↔ IsEmpty α
  证明: ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h1 h2 => h2.elim h1.elim⟩

@[simp, push]

Depends on / 依赖: h1.elim, h2.elim
-/
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h1 h2 => h2.elim h1.elim⟩

@[simp, push]
/--
theorem `not_isEmpty_iff` / 定理 `not_isEmpty_iff`

English:
theorem not_isEmpty_iff
  statement: ¬IsEmpty α ↔ Nonempty α
  proof: not_iff_comm.mp not_nonempty_iff

@[simp]

中文:
定理 not_isEmpty_iff
  结论: ¬IsEmpty α ↔ Nonempty α
  证明: not_iff_comm.mp not_nonempty_iff

@[simp]

Depends on / 依赖: not_iff_comm, not_iff_comm.mp, not_nonempty_iff
-/
theorem not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff

@[simp]
/--
theorem `isEmpty_Prop` / 定理 `isEmpty_Prop`

English:
theorem isEmpty_Prop
  given: {p : Prop}
  statement: IsEmpty p ↔ ¬p
  proof: by
  simp only [← not_nonempty_iff, nonempty_prop]

@[simp]

中文:
定理 isEmpty_Prop
  条件: {p : 命题}
  结论: IsEmpty p ↔ ¬p
  证明: by
  simp only [← not_nonempty_iff, nonempty_prop]

@[simp]

Depends on / 依赖: nonempty_prop, not_nonempty_iff
-/
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [← not_nonempty_iff, nonempty_prop]

@[simp]
/--
theorem `isEmpty_pi` / 定理 `isEmpty_pi`

English:
theorem isEmpty_pi
  given: {π : α -> Sort*}
  statement: IsEmpty (forall a, π a) ↔ exists a, IsEmpty (π a)
  proof: by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]

中文:
定理 isEmpty_pi
  条件: {π : α -> Sort*}
  结论: IsEmpty (对任意 a, π a) ↔ 存在 a, IsEmpty (π a)
  证明: by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]

Depends on / 依赖: Classical, Classical.nonempty_pi, nonempty_pi, not_forall, not_nonempty_iff
-/
theorem isEmpty_pi {π : α -> Sort*} : IsEmpty (forall a, π a) ↔ exists a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]

/--
theorem `isEmpty_fun` / 定理 `isEmpty_fun`

English:
theorem isEmpty_fun
  statement: IsEmpty (α -> β) ↔ Nonempty α ∧ IsEmpty β
  proof: by
  rw [isEmpty_pi]; rw [← exists_true_iff_nonempty]; rw [← exists_and_right]; rw [true_and]

@[simp]

中文:
定理 isEmpty_fun
  结论: IsEmpty (α -> β) ↔ Nonempty α ∧ IsEmpty β
  证明: by
  rw [isEmpty_pi]; rw [← exists_true_iff_nonempty]; rw [← exists_and_right]; rw [true_and]

@[simp]

Depends on / 依赖: exists_and_right, exists_true_iff_nonempty, isEmpty_pi, true_and
-/
theorem isEmpty_fun : IsEmpty (α -> β) ↔ Nonempty α ∧ IsEmpty β := by
  rw [isEmpty_pi]; rw [← exists_true_iff_nonempty]; rw [← exists_and_right]; rw [true_and]

@[simp]
/--
theorem `nonempty_fun` / 定理 `nonempty_fun`

English:
theorem nonempty_fun
  statement: Nonempty (α -> β) ↔ IsEmpty α ∨ Nonempty β
  proof: not_iff_not.mp by rw [not_or, not_nonempty_iff, not_nonempty_iff, isEmpty_fun, not_isEmpty_iff]

@[simp]

中文:
定理 nonempty_fun
  结论: Nonempty (α -> β) ↔ IsEmpty α ∨ Nonempty β
  证明: not_iff_not.mp by rw [not_or, not_nonempty_iff, not_nonempty_iff, isEmpty_fun, not_isEmpty_iff]

@[simp]

Depends on / 依赖: isEmpty_fun, not_iff_not, not_iff_not.mp, not_isEmpty_iff, not_nonempty_iff, not_or
-/
theorem nonempty_fun : Nonempty (α -> β) ↔ IsEmpty α ∨ Nonempty β :=
not_iff_not.mp by rw [not_or, not_nonempty_iff, not_nonempty_iff, isEmpty_fun, not_isEmpty_iff]

@[simp]
/--
theorem `isEmpty_sigma` / 定理 `isEmpty_sigma`

English:
theorem isEmpty_sigma
  given: {α} {E : α -> Type*}
  statement: IsEmpty (Sigma E) ↔ forall a, IsEmpty (E a)
  proof: by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

@[simp]

中文:
定理 isEmpty_sigma
  条件: {α} {E : α -> 类型}
  结论: IsEmpty (Sigma E) ↔ 对任意 a, IsEmpty (E a)
  证明: by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

@[simp]

Depends on / 依赖: nonempty_sigma, not_exists, not_nonempty_iff
-/
theorem isEmpty_sigma {α} {E : α -> Type*} : IsEmpty (Sigma E) ↔ forall a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

@[simp]
/--
theorem `isEmpty_psigma` / 定理 `isEmpty_psigma`

English:
theorem isEmpty_psigma
  given: {α} {E : α -> Sort*}
  statement: IsEmpty (PSigma E) ↔ forall a, IsEmpty (E a)
  proof: by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]

中文:
定理 isEmpty_psigma
  条件: {α} {E : α -> Sort*}
  结论: IsEmpty (PSigma E) ↔ 对任意 a, IsEmpty (E a)
  证明: by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]

Depends on / 依赖: nonempty_psigma, not_exists, not_nonempty_iff
-/
theorem isEmpty_psigma {α} {E : α -> Sort*} : IsEmpty (PSigma E) ↔ forall a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]

/--
theorem `isEmpty_subtype` / 定理 `isEmpty_subtype`

English:
theorem isEmpty_subtype
  given: (p : α -> Prop)
  statement: IsEmpty (Subtype p) ↔ forall x, ¬p x
  proof: by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]

@[simp]

中文:
定理 isEmpty_subtype
  条件: (p : α -> 命题)
  结论: IsEmpty (Subtype p) ↔ 对任意 x, ¬p x
  证明: by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]

@[simp]

Depends on / 依赖: nonempty_subtype, not_exists, not_nonempty_iff
-/
theorem isEmpty_subtype (p : α -> Prop) : IsEmpty (Subtype p) ↔ forall x, ¬p x := by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]

@[simp]
/--
theorem `isEmpty_prod` / 定理 `isEmpty_prod`

English:
theorem isEmpty_prod
  given: {α β : Type*}
  statement: IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β
  proof: by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

@[simp]

中文:
定理 isEmpty_prod
  条件: {α β : 类型}
  结论: IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β
  证明: by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

@[simp]

Depends on / 依赖: nonempty_prod, not_and_or, not_nonempty_iff
-/
theorem isEmpty_prod {α β : Type*} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

@[simp]
/--
theorem `isEmpty_pprod` / 定理 `isEmpty_pprod`

English:
theorem isEmpty_pprod
  statement: IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β
  proof: by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]

@[simp]

中文:
定理 isEmpty_pprod
  结论: IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β
  证明: by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]

@[simp]

Depends on / 依赖: nonempty_pprod, not_and_or, not_nonempty_iff
-/
theorem isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]

@[simp]
/--
theorem `isEmpty_sum` / 定理 `isEmpty_sum`

English:
theorem isEmpty_sum
  given: {α β}
  statement: IsEmpty (α oplus β) ↔ IsEmpty α ∧ IsEmpty β
  proof: by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

@[simp]

中文:
定理 isEmpty_sum
  条件: {α β}
  结论: IsEmpty (α oplus β) ↔ IsEmpty α ∧ IsEmpty β
  证明: by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

@[simp]

Depends on / 依赖: nonempty_sum, not_nonempty_iff, not_or
-/
theorem isEmpty_sum {α β} : IsEmpty (α oplus β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

@[simp]
/--
theorem `isEmpty_psum` / 定理 `isEmpty_psum`

English:
theorem isEmpty_psum
  given: {α β}
  statement: IsEmpty (α oplus' β) ↔ IsEmpty α ∧ IsEmpty β
  proof: by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

@[simp]

中文:
定理 isEmpty_psum
  条件: {α β}
  结论: IsEmpty (α oplus' β) ↔ IsEmpty α ∧ IsEmpty β
  证明: by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

@[simp]

Depends on / 依赖: nonempty_psum, not_nonempty_iff, not_or
-/
theorem isEmpty_psum {α β} : IsEmpty (α oplus' β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

@[simp]
/--
theorem `isEmpty_ulift` / 定理 `isEmpty_ulift`

English:
theorem isEmpty_ulift
  given: {α}
  statement: IsEmpty (ULift α) ↔ IsEmpty α
  proof: by
  simp only [← not_nonempty_iff, nonempty_ulift]

@[simp]

中文:
定理 isEmpty_ulift
  条件: {α}
  结论: IsEmpty (ULift α) ↔ IsEmpty α
  证明: by
  simp only [← not_nonempty_iff, nonempty_ulift]

@[simp]

Depends on / 依赖: nonempty_ulift, not_nonempty_iff
-/
theorem isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_ulift]

@[simp]
/--
theorem `isEmpty_plift` / 定理 `isEmpty_plift`

English:
theorem isEmpty_plift
  given: {α}
  statement: IsEmpty (PLift α) ↔ IsEmpty α
  proof: by
  simp only [← not_nonempty_iff, nonempty_plift]

中文:
定理 isEmpty_plift
  条件: {α}
  结论: IsEmpty (PLift α) ↔ IsEmpty α
  证明: by
  simp only [← not_nonempty_iff, nonempty_plift]

Depends on / 依赖: nonempty_plift, not_nonempty_iff
-/
theorem isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_plift]

/--
theorem `wellFounded_of_isEmpty` / 定理 `wellFounded_of_isEmpty`

English:
theorem wellFounded_of_isEmpty
  given: {α} [IsEmpty α] (r : α -> α -> Prop)
  statement: WellFounded r
  proof: ⟨isEmptyElim⟩

中文:
定理 wellFounded_of_isEmpty
  条件: {α} [IsEmpty α] (r : α -> α -> 命题)
  结论: WellFounded r
  证明: ⟨isEmptyElim⟩

Depends on / 依赖: isEmptyElim
-/
theorem wellFounded_of_isEmpty {α} [IsEmpty α] (r : α -> α -> Prop) : WellFounded r :=
  ⟨isEmptyElim⟩

variable (α)

/--
theorem `isEmpty_or_nonempty` / 定理 `isEmpty_or_nonempty`

English:
theorem isEmpty_or_nonempty
  statement: IsEmpty α ∨ Nonempty α
  proof: (em <| IsEmpty α).elim Or.inl Or.inr ∘ not_isEmpty_iff.mp

@[simp]

中文:
定理 isEmpty_or_nonempty
  结论: IsEmpty α ∨ Nonempty α
  证明: (em <| IsEmpty α).elim Or.inl Or.inr ∘ not_isEmpty_iff.mp

@[simp]

Depends on / 依赖: IsEmpty, Or.inl, Or.inr, not_isEmpty_iff, not_isEmpty_iff.mp
-/
theorem isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α :=
(em <| IsEmpty α).elim Or.inl Or.inr ∘ not_isEmpty_iff.mp

@[simp]
/--
theorem `not_isEmpty_of_nonempty` / 定理 `not_isEmpty_of_nonempty`

English:
theorem not_isEmpty_of_nonempty
  given: [h : Nonempty α]
  statement: ¬IsEmpty α
  proof: not_isEmpty_iff.mpr h

中文:
定理 not_isEmpty_of_nonempty
  条件: [h : Nonempty α]
  结论: ¬IsEmpty α
  证明: not_isEmpty_iff.mpr h

Depends on / 依赖: not_isEmpty_iff, not_isEmpty_iff.mpr
-/
theorem not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_isEmpty_iff.mpr h

variable {α}

/--
theorem `Function.extend_of_isEmpty` / 定理 `Function.extend_of_isEmpty`

English:
theorem Function.extend_of_isEmpty
  given: [IsEmpty α] (f : α -> β) (g : α -> γ) (h : β -> γ)
  proof: funext fun _ => (Function.extend_apply' _ _ _) fun ⟨a, _⟩ => isEmptyElim a

中文:
定理 Function.extend_of_isEmpty
  条件: [IsEmpty α] (f : α -> β) (g : α -> γ) (h : β -> γ)
  证明: funext fun _ => (Function.extend_apply' _ _ _) fun ⟨a, _⟩ => isEmptyElim a

Depends on / 依赖: Function, Function.extend_apply, extend_apply, isEmptyElim
-/
theorem Function.extend_of_isEmpty [IsEmpty α] (f : α -> β) (g : α -> γ) (h : β -> γ) :
    Function.extend f g h = h :=
  funext fun _ => (Function.extend_apply' _ _ _) fun ⟨a, _⟩ => isEmptyElim a

open Relator

variable {α β : Type*} (R : α -> β -> Prop)

@[simp]
/--
theorem `leftTotal_empty` / 定理 `leftTotal_empty`

English:
theorem leftTotal_empty
  given: [IsEmpty α]
  statement: LeftTotal R
  proof: by
  simp only [LeftTotal, IsEmpty.forall_iff]

中文:
定理 leftTotal_empty
  条件: [IsEmpty α]
  结论: LeftTotal R
  证明: by
  simp only [LeftTotal, IsEmpty.forall_iff]

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, LeftTotal, forall_iff
-/
theorem leftTotal_empty [IsEmpty α] : LeftTotal R := by
  simp only [LeftTotal, IsEmpty.forall_iff]

/--
theorem `leftTotal_iff_isEmpty_left` / 定理 `leftTotal_iff_isEmpty_left`

English:
theorem leftTotal_iff_isEmpty_left
  given: [IsEmpty β]
  statement: LeftTotal R ↔ IsEmpty α
  proof: by
  simp only [LeftTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]

中文:
定理 leftTotal_iff_isEmpty_left
  条件: [IsEmpty β]
  结论: LeftTotal R ↔ IsEmpty α
  证明: by
  simp only [LeftTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]

Depends on / 依赖: IsEmpty, IsEmpty.exists_iff, LeftTotal, exists_iff, isEmpty_iff
-/
theorem leftTotal_iff_isEmpty_left [IsEmpty β] : LeftTotal R ↔ IsEmpty α := by
  simp only [LeftTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]
/--
theorem `rightTotal_empty` / 定理 `rightTotal_empty`

English:
theorem rightTotal_empty
  given: [IsEmpty β]
  statement: RightTotal R
  proof: by
  simp only [RightTotal, IsEmpty.forall_iff]

中文:
定理 rightTotal_empty
  条件: [IsEmpty β]
  结论: RightTotal R
  证明: by
  simp only [RightTotal, IsEmpty.forall_iff]

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, RightTotal, forall_iff
-/
theorem rightTotal_empty [IsEmpty β] : RightTotal R := by
  simp only [RightTotal, IsEmpty.forall_iff]

/--
theorem `rightTotal_iff_isEmpty_right` / 定理 `rightTotal_iff_isEmpty_right`

English:
theorem rightTotal_iff_isEmpty_right
  given: [IsEmpty α]
  statement: RightTotal R ↔ IsEmpty β
  proof: by
  simp only [RightTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]

中文:
定理 rightTotal_iff_isEmpty_right
  条件: [IsEmpty α]
  结论: RightTotal R ↔ IsEmpty β
  证明: by
  simp only [RightTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]

Depends on / 依赖: IsEmpty, IsEmpty.exists_iff, RightTotal, exists_iff, isEmpty_iff
-/
theorem rightTotal_iff_isEmpty_right [IsEmpty α] : RightTotal R ↔ IsEmpty β := by
  simp only [RightTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]
/--
theorem `biTotal_empty` / 定理 `biTotal_empty`

English:
theorem biTotal_empty
  given: [IsEmpty α] [IsEmpty β]
  statement: BiTotal R
  proof: ⟨leftTotal_empty R, rightTotal_empty R⟩

中文:
定理 biTotal_empty
  条件: [IsEmpty α] [IsEmpty β]
  结论: BiTotal R
  证明: ⟨leftTotal_empty R, rightTotal_empty R⟩

Depends on / 依赖: leftTotal_empty, rightTotal_empty
-/
theorem biTotal_empty [IsEmpty α] [IsEmpty β] : BiTotal R :=
  ⟨leftTotal_empty R, rightTotal_empty R⟩

/--
theorem `biTotal_iff_isEmpty_right` / 定理 `biTotal_iff_isEmpty_right`

English:
theorem biTotal_iff_isEmpty_right
  given: [IsEmpty α]
  statement: BiTotal R ↔ IsEmpty β
  proof: by
  simp only [BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and]

中文:
定理 biTotal_iff_isEmpty_right
  条件: [IsEmpty α]
  结论: BiTotal R ↔ IsEmpty β
  证明: by
  simp only [BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and]

Depends on / 依赖: BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and
-/
theorem biTotal_iff_isEmpty_right [IsEmpty α] : BiTotal R ↔ IsEmpty β := by
  simp only [BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and]

/--
theorem `biTotal_iff_isEmpty_left` / 定理 `biTotal_iff_isEmpty_left`

English:
theorem biTotal_iff_isEmpty_left
  given: [IsEmpty β]
  statement: BiTotal R ↔ IsEmpty α
  proof: by
  simp only [BiTotal, leftTotal_iff_isEmpty_left, rightTotal_empty, and_true]

中文:
定理 biTotal_iff_isEmpty_left
  条件: [IsEmpty β]
  结论: BiTotal R ↔ IsEmpty α
  证明: by
  simp only [BiTotal, leftTotal_iff_isEmpty_left, rightTotal_empty, and_true]

Depends on / 依赖: BiTotal, and_true, leftTotal_iff_isEmpty_left, rightTotal_empty
-/
theorem biTotal_iff_isEmpty_left [IsEmpty β] : BiTotal R ↔ IsEmpty α := by
  simp only [BiTotal, leftTotal_iff_isEmpty_left, rightTotal_empty, and_true]

/--
theorem `Function.Surjective.of_isEmpty` / 定理 `Function.Surjective.of_isEmpty`

English:
theorem Function.Surjective.of_isEmpty
  given: [IsEmpty β] (f : α -> β)
  statement: f.Surjective
  proof: IsEmpty.elim ‹_›

中文:
定理 Function.Surjective.of_isEmpty
  条件: [IsEmpty β] (f : α -> β)
  结论: f.Surjective
  证明: IsEmpty.elim ‹_›

Depends on / 依赖: IsEmpty, IsEmpty.elim
-/
theorem Function.Surjective.of_isEmpty [IsEmpty β] (f : α -> β) : f.Surjective := IsEmpty.elim ‹_›

/--
theorem `Function.surjective_iff_isEmpty` / 定理 `Function.surjective_iff_isEmpty`

English:
theorem Function.surjective_iff_isEmpty
  given: [IsEmpty α] (f : α -> β)
  statement: f.Surjective ↔ IsEmpty β
  proof: ⟨Surjective.isEmpty, fun _ => .of_isEmpty f⟩

中文:
定理 Function.surjective_iff_isEmpty
  条件: [IsEmpty α] (f : α -> β)
  结论: f.Surjective ↔ IsEmpty β
  证明: ⟨Surjective.isEmpty, fun _ => .of_isEmpty f⟩

Depends on / 依赖: Surjective, Surjective.isEmpty, isEmpty, of_isEmpty
-/
theorem Function.surjective_iff_isEmpty [IsEmpty α] (f : α -> β) : f.Surjective ↔ IsEmpty β :=
  ⟨Surjective.isEmpty, fun _ => .of_isEmpty f⟩

/--
theorem `Function.Bijective.of_isEmpty` / 定理 `Function.Bijective.of_isEmpty`

English:
theorem Function.Bijective.of_isEmpty
  given: (f : α -> β) [IsEmpty β]
  statement: f.Bijective
  proof: have := f.isEmpty
  ⟨injective_of_subsingleton f, .of_isEmpty f⟩

中文:
定理 Function.Bijective.of_isEmpty
  条件: (f : α -> β) [IsEmpty β]
  结论: f.Bijective
  证明: have := f.isEmpty
  ⟨injective_of_subsingleton f, .of_isEmpty f⟩

Depends on / 依赖: f.isEmpty, injective_of_subsingleton, isEmpty, of_isEmpty
-/
theorem Function.Bijective.of_isEmpty (f : α -> β) [IsEmpty β] : f.Bijective :=
  have := f.isEmpty
  ⟨injective_of_subsingleton f, .of_isEmpty f⟩

/--
theorem `Function.not_surjective_of_isEmpty_of_nonempty` / 定理 `Function.not_surjective_of_isEmpty_of_nonempty`

English:
theorem Function.not_surjective_of_isEmpty_of_nonempty
  given: [IsEmpty α] [Nonempty β] (f : α -> β)
  proof: (not_isEmpty_of_nonempty β ·.isEmpty)

中文:
定理 Function.not_surjective_of_isEmpty_of_nonempty
  条件: [IsEmpty α] [Nonempty β] (f : α -> β)
  证明: (not_isEmpty_of_nonempty β ·.isEmpty)

Depends on / 依赖: isEmpty, not_isEmpty_of_nonempty
-/
theorem Function.not_surjective_of_isEmpty_of_nonempty [IsEmpty α] [Nonempty β] (f : α -> β) :
    ¬f.Surjective :=
  (not_isEmpty_of_nonempty β ·.isEmpty)
