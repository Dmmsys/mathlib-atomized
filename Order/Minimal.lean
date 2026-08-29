/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Peter Nelson
-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.WellFounded

/-!
# Minimality and Maximality

This file proves basic facts about minimality and maximality
of an element with respect to a predicate `P` on an ordered type `α`.

## Implementation Details

This file underwent a refactor from a version where minimality and maximality were defined using
sets rather than predicates, and with an unbundled order relation rather than a `LE` instance.

A side effect is that it has become less straightforward to state that something is minimal
with respect to a relation that is *not* defeq to the default `LE`.
One possible way would be with a type synonym,
and another would be with an ad hoc `LE` instance and `@` notation.
This was not an issue in practice anywhere in mathlib at the time of the refactor,
but it may be worth re-examining this to make it easier in the future; see the TODO below.

## TODO

* In the linearly ordered case, versions of lemmas like `minimal_mem_image` will hold with
  `MonotoneOn`/`AntitoneOn` assumptions rather than the stronger `x ≤ y ↔ f x ≤ f y` assumptions.

* `Set.maximal_iff_forall_insert` and `Set.minimal_iff_forall_sdiff_singleton` will generalize to
  lemmas about covering in the case of an `IsStronglyAtomic`/`IsStronglyCoatomic` order.

* `Finset` versions of the lemmas about sets.

* API to allow for easily expressing min/maximality with respect to an arbitrary non-`LE` relation.
* API for `MinimalFor`/`MaximalFor`
-/

@[expose] public section

assert_not_exists CompleteLattice

open Set OrderDual

variable {ι α β : Type*}

section LE
variable [LE α] {P Q : ι -> Prop} {f : ι -> α} {i j : ι}

@[to_dual (attr := simp)]
/--
lemma `minimalFor_eq_iff` / 引理 `minimalFor_eq_iff`

English:
lemma minimalFor_eq_iff
  statement: MinimalFor (· = j) f i ↔ i = j
  proof: by simp +contextual [MinimalFor]

@[to_dual (attr := gcongr)]

中文:
引理 minimalFor_eq_iff
  结论: MinimalFor (· = j) f i ↔ i = j
  证明: by simp +contextual [MinimalFor]

@[to_dual (attr := gcongr)]

Depends on / 依赖: MinimalFor, contextual
-/
lemma minimalFor_eq_iff : MinimalFor (· = j) f i ↔ i = j := by simp +contextual [MinimalFor]

@[to_dual (attr := gcongr)]
/--
theorem `MinimalFor.anti` / 定理 `MinimalFor.anti`

English:
theorem MinimalFor.anti
  given: (h : MinimalFor P f i) (hle : Q <= P) (hQ : Q i)
  statement: MinimalFor Q f i
  proof: ⟨hQ, (h.le_of_le <| hle · ·)⟩

中文:
定理 MinimalFor.anti
  条件: (h : MinimalFor P f i) (hle : Q <= P) (hQ : Q i)
  结论: MinimalFor Q f i
  证明: ⟨hQ, (h.le_of_le <| hle · ·)⟩

Depends on / 依赖: h.le_of_le, le_of_le
-/
theorem MinimalFor.anti (h : MinimalFor P f i) (hle : Q <= P) (hQ : Q i) : MinimalFor Q f i :=
  ⟨hQ, (h.le_of_le <| hle · ·)⟩

end LE

variable {P Q : α -> Prop} {a x y : α}

section LE
variable [LE α]

@[to_dual (attr := simp)]
/--
lemma `minimalFor_id` / 引理 `minimalFor_id`

English:
lemma minimalFor_id
  statement: MinimalFor P id x ↔ Minimal P x
  proof: .rfl

@[to_dual (attr := simp)]

中文:
引理 minimalFor_id
  结论: MinimalFor P id x ↔ 极小 P x
  证明: .rfl

@[to_dual (attr := simp)]
-/
lemma minimalFor_id : MinimalFor P id x ↔ Minimal P x := .rfl

@[to_dual (attr := simp)]
/--
theorem `minimal_toDual` / 定理 `minimal_toDual`

English:
theorem minimal_toDual
  statement: Minimal (fun x => P (ofDual x)) (toDual x) ↔ Maximal P x
  proof: Iff.rfl

@[to_dual]
alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[to_dual (attr := simp)]

中文:
定理 minimal_toDual
  结论: 极小 (fun x => P (ofDual x)) (toDual x) ↔ 极大 P x
  证明: Iff.rfl

@[to_dual]
alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem minimal_toDual : Minimal (fun x => P (ofDual x)) (toDual x) ↔ Maximal P x :=
  Iff.rfl

@[to_dual]
alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[to_dual (attr := simp)]
/--
theorem `minimal_false` / 定理 `minimal_false`

English:
theorem minimal_false
  statement: ¬ Minimal (fun _ => False) x
  proof: by
  simp [Minimal]

中文:
定理 minimal_false
  结论: ¬ 极小 (fun _ => 假) x
  证明: by
  simp [Minimal]

Depends on / 依赖: Minimal
-/
theorem minimal_false : ¬ Minimal (fun _ => False) x := by
  simp [Minimal]

/--
theorem `minimal_true` / 定理 `minimal_true`

English:
theorem minimal_true
  statement: Minimal (fun _ => True) x ↔ IsMin x
  proof: by
  simp [IsMin, Minimal]

@[to_dual (attr := simp)]

中文:
定理 minimal_true
  结论: 极小 (fun _ => 真) x ↔ IsMin x
  证明: by
  simp [IsMin, Minimal]

@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] theorem minimal_true : Minimal (fun _ => True) x ↔ IsMin x := by
  simp [IsMin, Minimal]

@[to_dual (attr := simp)]
/--
theorem `minimal_subtype` / 定理 `minimal_subtype`

English:
theorem minimal_subtype
  given: {x : Subtype Q}
  proof: by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[to_dual]

中文:
定理 minimal_subtype
  条件: {x : 子类型 Q}
  证明: by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[to_dual]

Depends on / 依赖: Minimal, Pi.inf_apply, Subtype, Subtype.forall, Subtype.mk_le_mk, inf_Prop_eq, inf_apply, mk_le_mk
-/
theorem minimal_subtype {x : Subtype Q} :
    Minimal (fun x => P x.1) x ↔ Minimal (P ⊓ Q) x := by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[to_dual]
/--
theorem `minimal_true_subtype` / 定理 `minimal_true_subtype`

English:
theorem minimal_true_subtype
  given: {x : Subtype P}
  statement: Minimal (fun _ => True) x ↔ Minimal P x
  proof: by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[to_dual (attr := simp)]

中文:
定理 minimal_true_subtype
  条件: {x : 子类型 P}
  结论: 极小 (fun _ => 真) x ↔ 极小 P x
  证明: by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[to_dual (attr := simp)]

Depends on / 依赖: Minimal
-/
theorem minimal_true_subtype {x : Subtype P} : Minimal (fun _ => True) x ↔ Minimal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[to_dual (attr := simp)]
/--
theorem `minimal_minimal` / 定理 `minimal_minimal`

English:
theorem minimal_minimal
  statement: Minimal (Minimal P) x ↔ Minimal P x
  proof: ⟨fun h => h.prop, fun h => ⟨h, fun _ hy hyx => h.le_of_le hy.prop hyx⟩⟩

中文:
定理 minimal_minimal
  结论: 极小 (极小 P) x ↔ 极小 P x
  证明: ⟨fun h => h.prop, fun h => ⟨h, fun _ hy hyx => h.le_of_le hy.prop hyx⟩⟩

Depends on / 依赖: h.le_of_le, h.prop, hy.prop, le_of_le
-/
theorem minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x :=
  ⟨fun h => h.prop, fun h => ⟨h, fun _ hy hyx => h.le_of_le hy.prop hyx⟩⟩

/-- If `P` is down-closed, then minimal elements satisfying `P` are exactly the globally minimal
elements satisfying `P`. -/
@[to_dual
/-- If `P` is up-closed, then maximal elements satisfying `P` are exactly the globally maximal
elements satisfying `P`. -/]
/--
theorem `minimal_iff_isMin` / 定理 `minimal_iff_isMin`

English:
theorem minimal_iff_isMin
  given: (hP : forall ⦃x y⦄, P y -> x <= y -> P x)
  statement: Minimal P x ↔ P x ∧ IsMin x
  proof: ⟨fun h => ⟨h.prop, fun _ h' => h.le_of_le (hP h.prop h') h'⟩, fun h => ⟨h.1, fun _ _ h' => h.2 h'⟩⟩

@[to_dual]

中文:
定理 minimal_iff_isMin
  条件: (hP : 对任意 ⦃x y⦄, P y -> x <= y -> P x)
  结论: 极小 P x ↔ P x ∧ IsMin x
  证明: ⟨fun h => ⟨h.prop, fun _ h' => h.le_of_le (hP h.prop h') h'⟩, fun h => ⟨h.1, fun _ _ h' => h.2 h'⟩⟩

@[to_dual]

Depends on / 依赖: h.le_of_le, h.prop, le_of_le
-/
theorem minimal_iff_isMin (hP : forall ⦃x y⦄, P y -> x <= y -> P x) : Minimal P x ↔ P x ∧ IsMin x :=
  ⟨fun h => ⟨h.prop, fun _ h' => h.le_of_le (hP h.prop h') h'⟩, fun h => ⟨h.1, fun _ _ h' => h.2 h'⟩⟩

@[to_dual]
/--
theorem `Minimal.mono` / 定理 `Minimal.mono`

English:
theorem Minimal.mono
  given: (h : Minimal P x) (hle : Q <= P) (hQ : Q x)
  statement: Minimal Q x
  proof: ⟨hQ, fun y hQy => h.le_of_le (hle y hQy)⟩

@[to_dual]

中文:
定理 极小.mono
  条件: (h : 极小 P x) (hle : Q <= P) (hQ : Q x)
  结论: 极小 Q x
  证明: ⟨hQ, fun y hQy => h.le_of_le (hle y hQy)⟩

@[to_dual]

Depends on / 依赖: h.le_of_le, le_of_le
-/
theorem Minimal.mono (h : Minimal P x) (hle : Q <= P) (hQ : Q x) : Minimal Q x :=
  ⟨hQ, fun y hQy => h.le_of_le (hle y hQy)⟩

@[to_dual]
/--
theorem `Minimal.and_right` / 定理 `Minimal.and_right`

English:
theorem Minimal.and_right
  given: (h : Minimal P x) (hQ : Q x)
  statement: Minimal (fun x => P x ∧ Q x) x
  proof: h.mono (fun _ => And.left) ⟨h.prop, hQ⟩

@[to_dual]

中文:
定理 极小.and_right
  条件: (h : 极小 P x) (hQ : Q x)
  结论: 极小 (fun x => P x ∧ Q x) x
  证明: h.mono (fun _ => And.left) ⟨h.prop, hQ⟩

@[to_dual]

Depends on / 依赖: And.left, h.mono, h.prop
-/
theorem Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x => P x ∧ Q x) x :=
  h.mono (fun _ => And.left) ⟨h.prop, hQ⟩

@[to_dual]
/--
theorem `Minimal.and_left` / 定理 `Minimal.and_left`

English:
theorem Minimal.and_left
  given: (h : Minimal P x) (hQ : Q x)
  statement: Minimal (fun x => (Q x ∧ P x)) x
  proof: h.mono (fun _ => And.right) ⟨hQ, h.prop⟩

中文:
定理 极小.and_left
  条件: (h : 极小 P x) (hQ : Q x)
  结论: 极小 (fun x => (Q x ∧ P x)) x
  证明: h.mono (fun _ => And.right) ⟨hQ, h.prop⟩

Depends on / 依赖: And.right, h.mono, h.prop
-/
theorem Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x => (Q x ∧ P x)) x :=
  h.mono (fun _ => And.right) ⟨hQ, h.prop⟩

/--
theorem `minimal_eq_iff` / 定理 `minimal_eq_iff`

English:
theorem minimal_eq_iff
  statement: Minimal (· = y) x ↔ x = y
  proof: by
  simp +contextual [Minimal]

@[to_dual]

中文:
定理 minimal_eq_iff
  结论: 极小 (· = y) x ↔ x = y
  证明: by
  simp +contextual [Minimal]

@[to_dual]
-/
@[to_dual (attr := simp)] theorem minimal_eq_iff : Minimal (· = y) x ↔ x = y := by
  simp +contextual [Minimal]

@[to_dual]
/--
theorem `not_minimal_iff` / 定理 `not_minimal_iff`

English:
theorem not_minimal_iff
  given: (hx : P x)
  statement: ¬ Minimal P x ↔ exists y, P y ∧ y <= x ∧ ¬ (x <= y)
  proof: by
  simp [Minimal, hx]

@[to_dual]

中文:
定理 not_minimal_iff
  条件: (hx : P x)
  结论: ¬ 极小 P x ↔ 存在 y, P y ∧ y <= x ∧ ¬ (x <= y)
  证明: by
  simp [Minimal, hx]

@[to_dual]

Depends on / 依赖: Minimal
-/
theorem not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ exists y, P y ∧ y <= x ∧ ¬ (x <= y) := by
  simp [Minimal, hx]

@[to_dual]
/--
theorem `Minimal.or` / 定理 `Minimal.or`

English:
theorem Minimal.or
  given: (h : Minimal (fun x => P x ∨ Q x) x)
  statement: Minimal P x ∨ Minimal Q x
  proof: by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx => hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx => hmin (Or.inr hy) hyx⟩

@[to_dual]

中文:
定理 极小.or
  条件: (h : 极小 (fun x => P x ∨ Q x) x)
  结论: 极小 P x ∨ 极小 Q x
  证明: by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx => hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx => hmin (Or.inr hy) hyx⟩

@[to_dual]

Depends on / 依赖: Or.inl, Or.inr
-/
theorem Minimal.or (h : Minimal (fun x => P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx => hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx => hmin (Or.inr hy) hyx⟩

@[to_dual]
/--
theorem `minimal_and_iff_right_of_imp` / 定理 `minimal_and_iff_right_of_imp`

English:
theorem minimal_and_iff_right_of_imp
  given: (hPQ : forall ⦃x⦄, P x -> Q x)
  proof: by
  simp_rw [and_iff_left_of_imp (fun x => hPQ x), iff_self_and]
  exact fun h => hPQ h.prop

@[to_dual]

中文:
定理 minimal_and_iff_right_of_imp
  条件: (hPQ : 对任意 ⦃x⦄, P x -> Q x)
  证明: by
  simp_rw [and_iff_left_of_imp (fun x => hPQ x), iff_self_and]
  exact fun h => hPQ h.prop

@[to_dual]

Depends on / 依赖: and_iff_left_of_imp, h.prop, iff_self_and, simp_rw
-/
theorem minimal_and_iff_right_of_imp (hPQ : forall ⦃x⦄, P x -> Q x) :
    Minimal (fun x => P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x := by
  simp_rw [and_iff_left_of_imp (fun x => hPQ x), iff_self_and]
  exact fun h => hPQ h.prop

@[to_dual]
/--
theorem `minimal_and_iff_left_of_imp` / 定理 `minimal_and_iff_left_of_imp`

English:
theorem minimal_and_iff_left_of_imp
  given: (hPQ : forall ⦃x⦄, P x -> Q x)
  proof: by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

中文:
定理 minimal_and_iff_left_of_imp
  条件: (hPQ : 对任意 ⦃x⦄, P x -> Q x)
  证明: by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

Depends on / 依赖: and_comm, iff_comm, minimal_and_iff_right_of_imp, simp_rw
-/
theorem minimal_and_iff_left_of_imp (hPQ : forall ⦃x⦄, P x -> Q x) :
    Minimal (fun x => Q x ∧ P x) x ↔ Q x ∧ (Minimal P x) := by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

end LE

section Preorder

variable [Preorder α] [Preorder β] {Q : ι -> Prop} {f : ι -> α} {g : α -> β} {i j : ι}

@[to_dual maximal_iff_forall_gt]
/--
theorem `minimal_iff_forall_lt` / 定理 `minimal_iff_forall_lt`

English:
theorem minimal_iff_forall_lt
  statement: Minimal P x ↔ P x ∧ forall ⦃y⦄, y < x -> ¬ P y
  proof: by
  simp [Minimal, lt_iff_le_not_ge, imp.swap]

@[to_dual maximalFor_iff_forall_gt]

中文:
定理 minimal_iff_对任意_lt
  结论: 极小 P x ↔ P x ∧ 对任意 ⦃y⦄, y < x -> ¬ P y
  证明: by
  simp [Minimal, lt_iff_le_not_ge, imp.swap]

@[to_dual maximalFor_iff_forall_gt]

Depends on / 依赖: Minimal, imp.swap, lt_iff_le_not_ge
-/
theorem minimal_iff_forall_lt : Minimal P x ↔ P x ∧ forall ⦃y⦄, y < x -> ¬ P y := by
  simp [Minimal, lt_iff_le_not_ge, imp.swap]

@[to_dual maximalFor_iff_forall_gt]
/--
theorem `minimalFor_iff_forall_lt` / 定理 `minimalFor_iff_forall_lt`

English:
theorem minimalFor_iff_forall_lt
  statement: MinimalFor Q f i ↔ Q i ∧ forall ⦃j⦄, f j < f i -> ¬ Q j
  proof: by
  simp [MinimalFor, lt_iff_le_not_ge, imp.swap]

@[to_dual not_prop_of_gt]

中文:
定理 minimalFor_iff_对任意_lt
  结论: MinimalFor Q f i ↔ Q i ∧ 对任意 ⦃j⦄, f j < f i -> ¬ Q j
  证明: by
  simp [MinimalFor, lt_iff_le_not_ge, imp.swap]

@[to_dual not_prop_of_gt]

Depends on / 依赖: MinimalFor, imp.swap, lt_iff_le_not_ge
-/
theorem minimalFor_iff_forall_lt : MinimalFor Q f i ↔ Q i ∧ forall ⦃j⦄, f j < f i -> ¬ Q j := by
  simp [MinimalFor, lt_iff_le_not_ge, imp.swap]

@[to_dual not_prop_of_gt]
/--
theorem `Minimal.not_prop_of_lt` / 定理 `Minimal.not_prop_of_lt`

English:
theorem Minimal.not_prop_of_lt
  given: (h : Minimal P x) (hlt : y < x)
  statement: ¬ P y
  proof: (minimal_iff_forall_lt.1 h).2 hlt

@[to_dual not_prop_of_gt]

中文:
定理 极小.not_prop_of_lt
  条件: (h : 极小 P x) (hlt : y < x)
  结论: ¬ P y
  证明: (minimal_iff_forall_lt.1 h).2 hlt

@[to_dual not_prop_of_gt]

Depends on / 依赖: minimal_iff_forall_lt
-/
theorem Minimal.not_prop_of_lt (h : Minimal P x) (hlt : y < x) : ¬ P y :=
  (minimal_iff_forall_lt.1 h).2 hlt

@[to_dual not_prop_of_gt]
/--
theorem `MinimalFor.not_prop_of_lt` / 定理 `MinimalFor.not_prop_of_lt`

English:
theorem MinimalFor.not_prop_of_lt
  given: (h : MinimalFor Q f i) (hlt : f j < f i)
  statement: ¬ Q j
  proof: (minimalFor_iff_forall_lt.1 h).2 hlt

@[to_dual not_gt]

中文:
定理 MinimalFor.not_prop_of_lt
  条件: (h : MinimalFor Q f i) (hlt : f j < f i)
  结论: ¬ Q j
  证明: (minimalFor_iff_forall_lt.1 h).2 hlt

@[to_dual not_gt]

Depends on / 依赖: minimalFor_iff_forall_lt
-/
theorem MinimalFor.not_prop_of_lt (h : MinimalFor Q f i) (hlt : f j < f i) : ¬ Q j :=
  (minimalFor_iff_forall_lt.1 h).2 hlt

@[to_dual not_gt]
/--
theorem `Minimal.not_lt` / 定理 `Minimal.not_lt`

English:
theorem Minimal.not_lt
  given: (h : Minimal P x) (hy : P y)
  statement: ¬(y < x)
  proof: fun hlt => h.not_prop_of_lt hlt hy

@[to_dual not_gt]

中文:
定理 极小.not_lt
  条件: (h : 极小 P x) (hy : P y)
  结论: ¬(y < x)
  证明: fun hlt => h.not_prop_of_lt hlt hy

@[to_dual not_gt]

Depends on / 依赖: h.not_prop_of_lt, not_prop_of_lt
-/
theorem Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x) :=
  fun hlt => h.not_prop_of_lt hlt hy

@[to_dual not_gt]
/--
theorem `MinimalFor.not_lt` / 定理 `MinimalFor.not_lt`

English:
theorem MinimalFor.not_lt
  given: (h : MinimalFor Q f i) (hj : Q j)
  statement: ¬(f j < f i)
  proof: fun hlt => h.not_prop_of_lt hlt hj

@[to_dual (attr := simp) maximal_ge_iff]

中文:
定理 MinimalFor.not_lt
  条件: (h : MinimalFor Q f i) (hj : Q j)
  结论: ¬(f j < f i)
  证明: fun hlt => h.not_prop_of_lt hlt hj

@[to_dual (attr := simp) maximal_ge_iff]

Depends on / 依赖: h.not_prop_of_lt, not_prop_of_lt
-/
theorem MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) : ¬(f j < f i) :=
  fun hlt => h.not_prop_of_lt hlt hj

@[to_dual (attr := simp) maximal_ge_iff]
/--
theorem `minimal_le_iff` / 定理 `minimal_le_iff`

English:
theorem minimal_le_iff
  statement: Minimal (· <= y) x ↔ x <= y ∧ IsMin x
  proof: minimal_iff_isMin (fun _ _ h h' => h'.trans h)

@[to_dual (attr := simp) maximal_gt_iff]

中文:
定理 minimal_le_iff
  结论: 极小 (· <= y) x ↔ x <= y ∧ IsMin x
  证明: minimal_iff_isMin (fun _ _ h h' => h'.trans h)

@[to_dual (attr := simp) maximal_gt_iff]

Depends on / 依赖: minimal_iff_isMin
-/
theorem minimal_le_iff : Minimal (· <= y) x ↔ x <= y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' => h'.trans h)

@[to_dual (attr := simp) maximal_gt_iff]
/--
theorem `minimal_lt_iff` / 定理 `minimal_lt_iff`

English:
theorem minimal_lt_iff
  statement: Minimal (· < y) x ↔ x < y ∧ IsMin x
  proof: minimal_iff_isMin (fun _ _ h h' => h'.trans_lt h)

@[to_dual not_maximal_iff_exists_gt]

中文:
定理 minimal_lt_iff
  结论: 极小 (· < y) x ↔ x < y ∧ IsMin x
  证明: minimal_iff_isMin (fun _ _ h h' => h'.trans_lt h)

@[to_dual not_maximal_iff_exists_gt]

Depends on / 依赖: minimal_iff_isMin, trans_lt
-/
theorem minimal_lt_iff : Minimal (· < y) x ↔ x < y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' => h'.trans_lt h)

@[to_dual not_maximal_iff_exists_gt]
/--
theorem `not_minimal_iff_exists_lt` / 定理 `not_minimal_iff_exists_lt`

English:
theorem not_minimal_iff_exists_lt
  given: (hx : P x)
  statement: ¬ Minimal P x ↔ exists y, y < x ∧ P y
  proof: by
  simp_rw [not_minimal_iff hx, lt_iff_le_not_ge, and_comm]

@[to_dual exists_gt_of_not_maximal]
alias ⟨exists_lt_of_not_minimal, _⟩ := not_minimal_iff_exists_lt

@[to_dual]

中文:
定理 not_minimal_iff_存在_lt
  条件: (hx : P x)
  结论: ¬ 极小 P x ↔ 存在 y, y < x ∧ P y
  证明: by
  simp_rw [not_minimal_iff hx, lt_iff_le_not_ge, and_comm]

@[to_dual exists_gt_of_not_maximal]
alias ⟨exists_lt_of_not_minimal, _⟩ := not_minimal_iff_exists_lt

@[to_dual]

Depends on / 依赖: and_comm, lt_iff_le_not_ge, not_minimal_iff, simp_rw
-/
theorem not_minimal_iff_exists_lt (hx : P x) : ¬ Minimal P x ↔ exists y, y < x ∧ P y := by
  simp_rw [not_minimal_iff hx, lt_iff_le_not_ge, and_comm]

@[to_dual exists_gt_of_not_maximal]
alias ⟨exists_lt_of_not_minimal, _⟩ := not_minimal_iff_exists_lt

@[to_dual]
/--
theorem `MinimalFor.of_strictMonoOn_comp` / 定理 `MinimalFor.of_strictMonoOn_comp`

English:
theorem MinimalFor.of_strictMonoOn_comp
  statement: (hg : StrictMonoOn g (f '' Set.ofPred Q))
  proof: by
  refine ⟨h.prop, fun j hj hle => ?_⟩
  by_contra
exact h.not_lt hj hg ⟨j, hj, rfl⟩ ⟨i, h.prop, rfl⟩ lt_of_le_not_ge hle this

@[to_dual]

中文:
定理 MinimalFor.of_strictMonoOn_comp
  结论: (hg : StrictMonoOn g (f '' 集合.ofPred Q))
  证明: by
  refine ⟨h.prop, fun j hj hle => ?_⟩
  by_contra
exact h.not_lt hj hg ⟨j, hj, rfl⟩ ⟨i, h.prop, rfl⟩ lt_of_le_not_ge hle this

@[to_dual]

Depends on / 依赖: h.not_lt, h.prop, lt_of_le_not_ge, not_lt
-/
theorem MinimalFor.of_strictMonoOn_comp (hg : StrictMonoOn g (f '' Set.ofPred Q))
    (h : MinimalFor Q (g ∘ f) i) : MinimalFor Q f i := by
  refine ⟨h.prop, fun j hj hle => ?_⟩
  by_contra
exact h.not_lt hj hg ⟨j, hj, rfl⟩ ⟨i, h.prop, rfl⟩ lt_of_le_not_ge hle this

@[to_dual]
/--
theorem `MinimalFor.minimal_of_strictMonoOn` / 定理 `MinimalFor.minimal_of_strictMonoOn`

English:
theorem MinimalFor.minimal_of_strictMonoOn
  statement: (hg : StrictMonoOn g (Set.ofPred P))
  proof: minimalFor_id.mp .of_strictMonoOn_comp (Set.image_id _ ▸ hg) h

@[to_dual]

中文:
定理 MinimalFor.minimal_of_strictMonoOn
  结论: (hg : StrictMonoOn g (集合.ofPred P))
  证明: minimalFor_id.mp .of_strictMonoOn_comp (Set.image_id _ ▸ hg) h

@[to_dual]

Depends on / 依赖: Set.image_id, image_id, minimalFor_id, minimalFor_id.mp, of_strictMonoOn_comp
-/
theorem MinimalFor.minimal_of_strictMonoOn (hg : StrictMonoOn g (Set.ofPred P))
    (h : MinimalFor P g x) :
    Minimal P x :=
minimalFor_id.mp .of_strictMonoOn_comp (Set.image_id _ ▸ hg) h

@[to_dual]
/--
theorem `MinimalFor.maximalFor_of_strictAntiOn_comp` / 定理 `MinimalFor.maximalFor_of_strictAntiOn_comp`

English:
theorem MinimalFor.maximalFor_of_strictAntiOn_comp
  statement: (hg : StrictAntiOn g (f '' Set.ofPred Q))
  proof: by
  refine ⟨h.prop, fun j hj hle => ?_⟩
  by_contra
exact h.not_lt hj hg ⟨i, h.prop, rfl⟩ ⟨j, hj, rfl⟩ lt_of_le_not_ge hle this

@[to_dual]

中文:
定理 MinimalFor.maximalFor_of_strictAntiOn_comp
  结论: (hg : StrictAntiOn g (f '' 集合.ofPred Q))
  证明: by
  refine ⟨h.prop, fun j hj hle => ?_⟩
  by_contra
exact h.not_lt hj hg ⟨i, h.prop, rfl⟩ ⟨j, hj, rfl⟩ lt_of_le_not_ge hle this

@[to_dual]

Depends on / 依赖: h.not_lt, h.prop, lt_of_le_not_ge, not_lt
-/
theorem MinimalFor.maximalFor_of_strictAntiOn_comp (hg : StrictAntiOn g (f '' Set.ofPred Q))
    (h : MinimalFor Q (g ∘ f) i) : MaximalFor Q f i := by
  refine ⟨h.prop, fun j hj hle => ?_⟩
  by_contra
exact h.not_lt hj hg ⟨i, h.prop, rfl⟩ ⟨j, hj, rfl⟩ lt_of_le_not_ge hle this

@[to_dual]
/--
theorem `MinimalFor.maximal_of_strictAntiOn` / 定理 `MinimalFor.maximal_of_strictAntiOn`

English:
theorem MinimalFor.maximal_of_strictAntiOn
  statement: (hg : StrictAntiOn g (Set.ofPred P))
  proof: maximalFor_id.mp MinimalFor.maximalFor_of_strictAntiOn_comp (Set.image_id _ ▸ hg) h

中文:
定理 MinimalFor.maximal_of_strictAntiOn
  结论: (hg : StrictAntiOn g (集合.ofPred P))
  证明: maximalFor_id.mp MinimalFor.maximalFor_of_strictAntiOn_comp (Set.image_id _ ▸ hg) h

Depends on / 依赖: MinimalFor, MinimalFor.maximalFor_of_strictAntiOn_comp, Set.image_id, image_id, maximalFor_id, maximalFor_id.mp, maximalFor_of_strictAntiOn_comp
-/
theorem MinimalFor.maximal_of_strictAntiOn (hg : StrictAntiOn g (Set.ofPred P))
    (h : MinimalFor P g x) :
    Maximal P x :=
maximalFor_id.mp MinimalFor.maximalFor_of_strictAntiOn_comp (Set.image_id _ ▸ hg) h

section WellFoundedLT
variable [WellFoundedLT α]

@[to_dual]
/--
lemma `exists_minimalFor_of_wellFoundedLT` / 引理 `exists_minimalFor_of_wellFoundedLT`

English:
lemma exists_minimalFor_of_wellFoundedLT
  given: (P : ι -> Prop) (f : ι -> α) (hP : exists i, P i)
  proof: by
  simpa [not_lt_iff_le_imp_ge, InvImage]
    using! (instIsWellFoundedInvImage (· < ·) f).wf.has_min _ hP

@[to_dual]

中文:
引理 存在_minimalFor_of_wellFoundedLT
  条件: (P : ι -> 命题) (f : ι -> α) (hP : 存在 i, P i)
  证明: by
  simpa [not_lt_iff_le_imp_ge, InvImage]
    using! (instIsWellFoundedInvImage (· < ·) f).wf.has_min _ hP

@[to_dual]

Depends on / 依赖: InvImage, has_min, instIsWellFoundedInvImage, not_lt_iff_le_imp_ge, wf.has_min
-/
lemma exists_minimalFor_of_wellFoundedLT (P : ι -> Prop) (f : ι -> α) (hP : exists i, P i) :
    exists i, MinimalFor P f i := by
  simpa [not_lt_iff_le_imp_ge, InvImage]
    using! (instIsWellFoundedInvImage (· < ·) f).wf.has_min _ hP

@[to_dual]
/--
lemma `exists_minimal_of_wellFoundedLT` / 引理 `exists_minimal_of_wellFoundedLT`

English:
lemma exists_minimal_of_wellFoundedLT
  given: (P : α -> Prop) (hP : exists a, P a)
  statement: exists a, Minimal P a
  proof: exists_minimalFor_of_wellFoundedLT P id hP

@[to_dual exists_maximal_ge_of_wellFoundedGT]

中文:
引理 存在_minimal_of_wellFoundedLT
  条件: (P : α -> 命题) (hP : 存在 a, P a)
  结论: 存在 a, 极小 P a
  证明: exists_minimalFor_of_wellFoundedLT P id hP

@[to_dual exists_maximal_ge_of_wellFoundedGT]

Depends on / 依赖: exists_minimalFor_of_wellFoundedLT
-/
lemma exists_minimal_of_wellFoundedLT (P : α -> Prop) (hP : exists a, P a) : exists a, Minimal P a :=
  exists_minimalFor_of_wellFoundedLT P id hP

@[to_dual exists_maximal_ge_of_wellFoundedGT]
/--
lemma `exists_minimal_le_of_wellFoundedLT` / 引理 `exists_minimal_le_of_wellFoundedLT`

English:
lemma exists_minimal_le_of_wellFoundedLT
  given: (P : α -> Prop) (a : α) (ha : P a)
  proof: by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun b => b <= a ∧ P b) ⟨a, le_rfl, ha⟩
  exact ⟨b, hba, hb, fun c hc hcb => hbmin ⟨hcb.trans hba, hc⟩ hcb⟩

中文:
引理 存在_minimal_le_of_wellFoundedLT
  条件: (P : α -> 命题) (a : α) (ha : P a)
  证明: by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun b => b <= a ∧ P b) ⟨a, le_rfl, ha⟩
  exact ⟨b, hba, hb, fun c hc hcb => hbmin ⟨hcb.trans hba, hc⟩ hcb⟩

Depends on / 依赖: exists_minimal_of_wellFoundedLT, hcb.trans, le_rfl
-/
lemma exists_minimal_le_of_wellFoundedLT (P : α -> Prop) (a : α) (ha : P a) :
    exists b <= a, Minimal P b := by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun b => b <= a ∧ P b) ⟨a, le_rfl, ha⟩
  exact ⟨b, hba, hb, fun c hc hcb => hbmin ⟨hcb.trans hba, hc⟩ hcb⟩

end WellFoundedLT
end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual (rename := hge -> hle) eq_of_le]
/--
theorem `Minimal.eq_of_ge` / 定理 `Minimal.eq_of_ge`

English:
theorem Minimal.eq_of_ge
  given: (hx : Minimal P x) (hy : P y) (hge : y <= x)
  statement: x = y
  proof: (hx.2 hy hge).antisymm hge

@[to_dual (rename := hle -> hge) eq_of_ge]

中文:
定理 极小.eq_of_ge
  条件: (hx : 极小 P x) (hy : P y) (hge : y <= x)
  结论: x = y
  证明: (hx.2 hy hge).antisymm hge

@[to_dual (rename := hle -> hge) eq_of_ge]

Depends on / 依赖: antisymm
-/
theorem Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : y <= x) : x = y :=
  (hx.2 hy hge).antisymm hge

@[to_dual (rename := hle -> hge) eq_of_ge]
/--
theorem `Minimal.eq_of_le` / 定理 `Minimal.eq_of_le`

English:
theorem Minimal.eq_of_le
  given: (hx : Minimal P x) (hy : P y) (hle : y <= x)
  statement: y = x
  proof: (hx.eq_of_ge hy hle).symm

@[to_dual]

中文:
定理 极小.eq_of_le
  条件: (hx : 极小 P x) (hy : P y) (hle : y <= x)
  结论: y = x
  证明: (hx.eq_of_ge hy hle).symm

@[to_dual]

Depends on / 依赖: eq_of_ge, hx.eq_of_ge
-/
theorem Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : y <= x) : y = x :=
  (hx.eq_of_ge hy hle).symm

@[to_dual]
/--
theorem `minimal_iff` / 定理 `minimal_iff`

English:
theorem minimal_iff
  statement: Minimal P x ↔ P x ∧ forall ⦃y⦄, P y -> y <= x -> x = y
  proof: ⟨fun h => ⟨h.1, fun _ => h.eq_of_ge⟩, fun h => ⟨h.1, fun _ hy hle => (h.2 hy hle).le⟩⟩

@[to_dual]

中文:
定理 minimal_iff
  结论: 极小 P x ↔ P x ∧ 对任意 ⦃y⦄, P y -> y <= x -> x = y
  证明: ⟨fun h => ⟨h.1, fun _ => h.eq_of_ge⟩, fun h => ⟨h.1, fun _ hy hle => (h.2 hy hle).le⟩⟩

@[to_dual]

Depends on / 依赖: eq_of_ge, h.eq_of_ge
-/
theorem minimal_iff : Minimal P x ↔ P x ∧ forall ⦃y⦄, P y -> y <= x -> x = y :=
  ⟨fun h => ⟨h.1, fun _ => h.eq_of_ge⟩, fun h => ⟨h.1, fun _ hy hle => (h.2 hy hle).le⟩⟩

@[to_dual]
/--
theorem `minimal_mem_iff` / 定理 `minimal_mem_iff`

English:
theorem minimal_mem_iff
  given: {s : Set α}
  statement: Minimal (· in s) x ↔ x in s ∧ forall ⦃y⦄, y in s -> y <= x -> x = y
  proof: minimal_iff

中文:
定理 minimal_mem_iff
  条件: {s : 集合 α}
  结论: 极小 (· in s) x ↔ x in s ∧ 对任意 ⦃y⦄, y in s -> y <= x -> x = y
  证明: minimal_iff

Depends on / 依赖: minimal_iff
-/
theorem minimal_mem_iff {s : Set α} : Minimal (· in s) x ↔ x in s ∧ forall ⦃y⦄, y in s -> y <= x -> x = y :=
  minimal_iff

/-- If `P y` holds, and everything satisfying `P` is above `y`, then `y` is the unique minimal
element satisfying `P`. -/
@[to_dual
/-- If `P y` holds, and everything satisfying `P` is below `y`, then `y` is the unique maximal
element satisfying `P`. -/]
/--
theorem `minimal_iff_eq` / 定理 `minimal_iff_eq`

English:
theorem minimal_iff_eq
  given: (hy : P y) (hP : forall ⦃x⦄, P x -> y <= x)
  statement: Minimal P x ↔ x = y
  proof: ⟨fun h => h.eq_of_ge hy (hP h.prop), by rintro rfl; exact ⟨hy, fun z hz _ => hP hz⟩⟩

中文:
定理 minimal_iff_eq
  条件: (hy : P y) (hP : 对任意 ⦃x⦄, P x -> y <= x)
  结论: 极小 P x ↔ x = y
  证明: ⟨fun h => h.eq_of_ge hy (hP h.prop), by rintro rfl; exact ⟨hy, fun z hz _ => hP hz⟩⟩

Depends on / 依赖: eq_of_ge, h.eq_of_ge, h.prop
-/
theorem minimal_iff_eq (hy : P y) (hP : forall ⦃x⦄, P x -> y <= x) : Minimal P x ↔ x = y :=
  ⟨fun h => h.eq_of_ge hy (hP h.prop), by rintro rfl; exact ⟨hy, fun z hz _ => hP hz⟩⟩

/--
theorem `minimal_ge_iff` / 定理 `minimal_ge_iff`

English:
theorem minimal_ge_iff
  statement: Minimal (y <= ·) x ↔ x = y
  proof: minimal_iff_eq rfl.le fun _ => id

@[to_dual]

中文:
定理 minimal_ge_iff
  结论: 极小 (y <= ·) x ↔ x = y
  证明: minimal_iff_eq rfl.le fun _ => id

@[to_dual]
-/
@[to_dual (attr := simp) maximal_le_iff] theorem minimal_ge_iff : Minimal (y <= ·) x ↔ x = y :=
  minimal_iff_eq rfl.le fun _ => id

@[to_dual]
/--
theorem `minimal_iff_minimal_of_imp_of_forall` / 定理 `minimal_iff_minimal_of_imp_of_forall`

English:
theorem minimal_iff_minimal_of_imp_of_forall
  statement: (hPQ : forall ⦃x⦄, Q x -> P x)
  proof: by
  refine ⟨fun h' => ⟨?_, fun y hy hyx => h'.le_of_le (hPQ hy) hyx⟩,
    fun h' => ⟨hPQ h'.prop, fun y hy hyx => ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

中文:
定理 minimal_iff_minimal_of_imp_of_对任意
  结论: (hPQ : 对任意 ⦃x⦄, Q x -> P x)
  证明: by
  refine ⟨fun h' => ⟨?_, fun y hy hyx => h'.le_of_le (hPQ hy) hyx⟩,
    fun h' => ⟨hPQ h'.prop, fun y hy hyx => ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

Depends on / 依赖: antisymm, hzy.trans, le_of_le
-/
theorem minimal_iff_minimal_of_imp_of_forall (hPQ : forall ⦃x⦄, Q x -> P x)
    (h : forall ⦃x⦄, P x -> exists y, y <= x ∧ Q y) : Minimal P x ↔ Minimal Q x := by
  refine ⟨fun h' => ⟨?_, fun y hy hyx => h'.le_of_le (hPQ hy) hyx⟩,
    fun h' => ⟨hPQ h'.prop, fun y hy hyx => ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

end PartialOrder

section LinearOrder

variable [LinearOrder α] {i j : ι} {Q : ι -> Prop} {f : ι -> α}

@[to_dual]
/--
theorem `Minimal.le` / 定理 `Minimal.le`

English:
theorem Minimal.le
  given: (h : Minimal P x) (hy : P y)
  statement: x <= y
  proof: le_of_not_gt (h.not_lt hy)

@[to_dual]

中文:
定理 极小.le
  条件: (h : 极小 P x) (hy : P y)
  结论: x <= y
  证明: le_of_not_gt (h.not_lt hy)

@[to_dual]

Depends on / 依赖: h.not_lt, le_of_not_gt, not_lt
-/
theorem Minimal.le (h : Minimal P x) (hy : P y) : x <= y :=
  le_of_not_gt (h.not_lt hy)

@[to_dual]
/--
theorem `MinimalFor.le` / 定理 `MinimalFor.le`

English:
theorem MinimalFor.le
  given: (h : MinimalFor Q f i) (hj : Q j)
  statement: f i <= f j
  proof: le_of_not_gt (h.not_lt hj)

中文:
定理 MinimalFor.le
  条件: (h : MinimalFor Q f i) (hj : Q j)
  结论: f i <= f j
  证明: le_of_not_gt (h.not_lt hj)

Depends on / 依赖: h.not_lt, le_of_not_gt, not_lt
-/
theorem MinimalFor.le (h : MinimalFor Q f i) (hj : Q j) : f i <= f j :=
  le_of_not_gt (h.not_lt hj)

end LinearOrder

section Subset

variable {P : Set α -> Prop} {s t : Set α}

/--
theorem `Minimal.eq_of_superset` / 定理 `Minimal.eq_of_superset`

English:
theorem Minimal.eq_of_superset
  given: (h : Minimal P s) (ht : P t) (hts : t subseteq s)
  statement: s = t
  proof: h.eq_of_ge ht hts

中文:
定理 极小.eq_of_superset
  条件: (h : 极小 P s) (ht : P t) (hts : t subseteq s)
  结论: s = t
  证明: h.eq_of_ge ht hts

Depends on / 依赖: IsScalarTower, eq_of_ge, h.eq_of_ge, isScalarTower_right
-/
theorem Minimal.eq_of_superset (h : Minimal P s) (ht : P t) (hts : t subseteq s) : s = t :=
  h.eq_of_ge ht hts

/--
theorem `Maximal.eq_of_subset` / 定理 `Maximal.eq_of_subset`

English:
theorem Maximal.eq_of_subset
  given: (h : Maximal P s) (ht : P t) (hst : s subseteq t)
  statement: s = t
  proof: h.eq_of_le ht hst

中文:
定理 极大.eq_of_subset
  条件: (h : 极大 P s) (ht : P t) (hst : s subseteq t)
  结论: s = t
  证明: h.eq_of_le ht hst

Depends on / 依赖: eq_of_le, h.eq_of_le
-/
theorem Maximal.eq_of_subset (h : Maximal P s) (ht : P t) (hst : s subseteq t) : s = t :=
  h.eq_of_le ht hst

/--
theorem `Minimal.eq_of_subset` / 定理 `Minimal.eq_of_subset`

English:
theorem Minimal.eq_of_subset
  given: (h : Minimal P s) (ht : P t) (hts : t subseteq s)
  statement: t = s
  proof: h.eq_of_le ht hts

中文:
定理 极小.eq_of_subset
  条件: (h : 极小 P s) (ht : P t) (hts : t subseteq s)
  结论: t = s
  证明: h.eq_of_le ht hts

Depends on / 依赖: eq_of_le, h.eq_of_le
-/
theorem Minimal.eq_of_subset (h : Minimal P s) (ht : P t) (hts : t subseteq s) : t = s :=
  h.eq_of_le ht hts

/--
theorem `Maximal.eq_of_superset` / 定理 `Maximal.eq_of_superset`

English:
theorem Maximal.eq_of_superset
  given: (h : Maximal P s) (ht : P t) (hst : s subseteq t)
  statement: t = s
  proof: h.eq_of_ge ht hst

中文:
定理 极大.eq_of_superset
  条件: (h : 极大 P s) (ht : P t) (hst : s subseteq t)
  结论: t = s
  证明: h.eq_of_ge ht hst

Depends on / 依赖: eq_of_ge, h.eq_of_ge
-/
theorem Maximal.eq_of_superset (h : Maximal P s) (ht : P t) (hst : s subseteq t) : t = s :=
  h.eq_of_ge ht hst

/--
theorem `minimal_subset_iff` / 定理 `minimal_subset_iff`

English:
theorem minimal_subset_iff
  statement: Minimal P s ↔ P s ∧ forall ⦃t⦄, P t -> t subseteq s -> s = t
  proof: _root_.minimal_iff

中文:
定理 minimal_subset_iff
  结论: 极小 P s ↔ P s ∧ 对任意 ⦃t⦄, P t -> t subseteq s -> s = t
  证明: _root_.minimal_iff

Depends on / 依赖: _root_, _root_.minimal_iff, minimal_iff
-/
theorem minimal_subset_iff : Minimal P s ↔ P s ∧ forall ⦃t⦄, P t -> t subseteq s -> s = t :=
  _root_.minimal_iff

/--
theorem `maximal_subset_iff` / 定理 `maximal_subset_iff`

English:
theorem maximal_subset_iff
  statement: Maximal P s ↔ P s ∧ forall ⦃t⦄, P t -> s subseteq t -> s = t
  proof: _root_.maximal_iff

中文:
定理 maximal_subset_iff
  结论: 极大 P s ↔ P s ∧ 对任意 ⦃t⦄, P t -> s subseteq t -> s = t
  证明: _root_.maximal_iff

Depends on / 依赖: _root_, _root_.maximal_iff, maximal_iff
-/
theorem maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄, P t -> s subseteq t -> s = t :=
  _root_.maximal_iff

/--
theorem `minimal_subset_iff'` / 定理 `minimal_subset_iff'`

English:
theorem minimal_subset_iff'
  statement: Minimal P s ↔ P s ∧ forall ⦃t⦄, P t -> t subseteq s -> s subseteq t
  proof: Iff.rfl

中文:
定理 minimal_subset_iff'
  结论: 极小 P s ↔ P s ∧ 对任意 ⦃t⦄, P t -> t subseteq s -> s subseteq t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem minimal_subset_iff' : Minimal P s ↔ P s ∧ forall ⦃t⦄, P t -> t subseteq s -> s subseteq t :=
  Iff.rfl

/--
theorem `maximal_subset_iff'` / 定理 `maximal_subset_iff'`

English:
theorem maximal_subset_iff'
  statement: Maximal P s ↔ P s ∧ forall ⦃t⦄, P t -> s subseteq t -> t subseteq s
  proof: Iff.rfl

中文:
定理 maximal_subset_iff'
  结论: 极大 P s ↔ P s ∧ 对任意 ⦃t⦄, P t -> s subseteq t -> t subseteq s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem maximal_subset_iff' : Maximal P s ↔ P s ∧ forall ⦃t⦄, P t -> s subseteq t -> t subseteq s :=
  Iff.rfl

/--
theorem `not_minimal_subset_iff` / 定理 `not_minimal_subset_iff`

English:
theorem not_minimal_subset_iff
  given: (hs : P s)
  statement: ¬ Minimal P s ↔ exists t, t ⊂ s ∧ P t
  proof: not_minimal_iff_exists_lt hs

中文:
定理 not_minimal_subset_iff
  条件: (hs : P s)
  结论: ¬ 极小 P s ↔ 存在 t, t ⊂ s ∧ P t
  证明: not_minimal_iff_exists_lt hs

Depends on / 依赖: not_minimal_iff_exists_lt
-/
theorem not_minimal_subset_iff (hs : P s) : ¬ Minimal P s ↔ exists t, t ⊂ s ∧ P t :=
  not_minimal_iff_exists_lt hs

/--
theorem `not_maximal_subset_iff` / 定理 `not_maximal_subset_iff`

English:
theorem not_maximal_subset_iff
  given: (hs : P s)
  statement: ¬ Maximal P s ↔ exists t, s ⊂ t ∧ P t
  proof: not_maximal_iff_exists_gt hs

中文:
定理 not_maximal_subset_iff
  条件: (hs : P s)
  结论: ¬ 极大 P s ↔ 存在 t, s ⊂ t ∧ P t
  证明: not_maximal_iff_exists_gt hs

Depends on / 依赖: not_maximal_iff_exists_gt
-/
theorem not_maximal_subset_iff (hs : P s) : ¬ Maximal P s ↔ exists t, s ⊂ t ∧ P t :=
  not_maximal_iff_exists_gt hs

/--
theorem `Set.minimal_iff_forall_ssubset` / 定理 `Set.minimal_iff_forall_ssubset`

English:
theorem Set.minimal_iff_forall_ssubset
  statement: Minimal P s ↔ P s ∧ forall ⦃t⦄, t ⊂ s -> ¬ P t
  proof: minimal_iff_forall_lt

中文:
定理 集合.minimal_iff_对任意_ssubset
  结论: 极小 P s ↔ P s ∧ 对任意 ⦃t⦄, t ⊂ s -> ¬ P t
  证明: minimal_iff_forall_lt

Depends on / 依赖: minimal_iff_forall_lt
-/
theorem Set.minimal_iff_forall_ssubset : Minimal P s ↔ P s ∧ forall ⦃t⦄, t ⊂ s -> ¬ P t :=
  minimal_iff_forall_lt

/--
theorem `Minimal.not_prop_of_ssubset` / 定理 `Minimal.not_prop_of_ssubset`

English:
theorem Minimal.not_prop_of_ssubset
  given: (h : Minimal P s) (ht : t ⊂ s)
  statement: ¬ P t
  proof: (minimal_iff_forall_lt.1 h).2 ht

中文:
定理 极小.not_prop_of_ssubset
  条件: (h : 极小 P s) (ht : t ⊂ s)
  结论: ¬ P t
  证明: (minimal_iff_forall_lt.1 h).2 ht

Depends on / 依赖: minimal_iff_forall_lt
-/
theorem Minimal.not_prop_of_ssubset (h : Minimal P s) (ht : t ⊂ s) : ¬ P t :=
  (minimal_iff_forall_lt.1 h).2 ht

/--
theorem `Minimal.not_ssubset` / 定理 `Minimal.not_ssubset`

English:
theorem Minimal.not_ssubset
  given: (h : Minimal P s) (ht : P t)
  statement: ¬ t ⊂ s
  proof: h.not_lt ht

中文:
定理 极小.not_ssubset
  条件: (h : 极小 P s) (ht : P t)
  结论: ¬ t ⊂ s
  证明: h.not_lt ht

Depends on / 依赖: h.not_lt, not_lt
-/
theorem Minimal.not_ssubset (h : Minimal P s) (ht : P t) : ¬ t ⊂ s :=
  h.not_lt ht

/--
theorem `Maximal.mem_of_prop_insert` / 定理 `Maximal.mem_of_prop_insert`

English:
theorem Maximal.mem_of_prop_insert
  given: (h : Maximal P s) (hx : P (insert x s))
  statement: x in s
  proof: h.eq_of_subset hx (subset_insert _ _) ▸ mem_insert ..

中文:
定理 极大.mem_of_prop_insert
  条件: (h : 极大 P s) (hx : P (insert x s))
  结论: x in s
  证明: h.eq_of_subset hx (subset_insert _ _) ▸ mem_insert ..

Depends on / 依赖: eq_of_subset, h.eq_of_subset, mem_insert, subset_insert
-/
theorem Maximal.mem_of_prop_insert (h : Maximal P s) (hx : P (insert x s)) : x in s :=
  h.eq_of_subset hx (subset_insert _ _) ▸ mem_insert ..

/--
theorem `Minimal.notMem_of_prop_sdiff_singleton` / 定理 `Minimal.notMem_of_prop_sdiff_singleton`

English:
theorem Minimal.notMem_of_prop_sdiff_singleton
  given: (h : Minimal P s) (hx : P (s \ {x}))
  statement: x ∉ s
  proof: fun hxs => ((h.eq_of_superset hx sdiff_subset).subset hxs).2 rfl

@[deprecated (since := "2026-06-03")]
alias Minimal.notMem_of_prop_diff_singleton := Minimal.notMem_of_prop_sdiff_singleton

中文:
定理 极小.notMem_of_prop_sdiff_singleton
  条件: (h : 极小 P s) (hx : P (s \ {x}))
  结论: x ∉ s
  证明: fun hxs => ((h.eq_of_superset hx sdiff_subset).subset hxs).2 rfl

@[deprecated (since := "2026-06-03")]
alias Minimal.notMem_of_prop_diff_singleton := Minimal.notMem_of_prop_sdiff_singleton

Depends on / 依赖: eq_of_superset, h.eq_of_superset, sdiff_subset, subset
-/
theorem Minimal.notMem_of_prop_sdiff_singleton (h : Minimal P s) (hx : P (s \ {x})) : x ∉ s :=
  fun hxs => ((h.eq_of_superset hx sdiff_subset).subset hxs).2 rfl

@[deprecated (since := "2026-06-03")]
alias Minimal.notMem_of_prop_diff_singleton := Minimal.notMem_of_prop_sdiff_singleton

/--
theorem `Set.minimal_iff_forall_sdiff_singleton` / 定理 `Set.minimal_iff_forall_sdiff_singleton`

English:
theorem Set.minimal_iff_forall_sdiff_singleton
  given: (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s)
  proof: ⟨fun h => ⟨h.1, fun _ hx hP => h.notMem_of_prop_sdiff_singleton hP hx⟩,
    fun h => ⟨h.1, fun _ ht hts x hxs => by_contra fun hxt =>
      h.2 x hxs (hP ht <| subset_sdiff_singleton hts hxt)⟩⟩

@[deprecated (since := "2026-06-03")]
alias Set.minimal_iff_forall_diff_singleton := Set.minimal_iff_forall_sdiff_singleton

中文:
定理 集合.minimal_iff_对任意_sdiff_singleton
  条件: (hP : 对任意 ⦃s t⦄, P t -> t subseteq s -> P s)
  证明: ⟨fun h => ⟨h.1, fun _ hx hP => h.notMem_of_prop_sdiff_singleton hP hx⟩,
    fun h => ⟨h.1, fun _ ht hts x hxs => by_contra fun hxt =>
      h.2 x hxs (hP ht <| subset_sdiff_singleton hts hxt)⟩⟩

@[deprecated (since := "2026-06-03")]
alias Set.minimal_iff_forall_diff_singleton := Set.minimal_iff_forall_sdiff_singleton

Depends on / 依赖: h.notMem_of_prop_sdiff_singleton, notMem_of_prop_sdiff_singleton, subset_sdiff_singleton
-/
theorem Set.minimal_iff_forall_sdiff_singleton (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) :
    Minimal P s ↔ P s ∧ forall x in s, ¬ P (s \ {x}) :=
  ⟨fun h => ⟨h.1, fun _ hx hP => h.notMem_of_prop_sdiff_singleton hP hx⟩,
    fun h => ⟨h.1, fun _ ht hts x hxs => by_contra fun hxt =>
      h.2 x hxs (hP ht <| subset_sdiff_singleton hts hxt)⟩⟩

@[deprecated (since := "2026-06-03")]
alias Set.minimal_iff_forall_diff_singleton := Set.minimal_iff_forall_sdiff_singleton

/--
theorem `Set.exists_sdiff_singleton_of_not_minimal` / 定理 `Set.exists_sdiff_singleton_of_not_minimal`

English:
theorem Set.exists_sdiff_singleton_of_not_minimal
  statement: (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) (hs : P s)
  proof: by
  simpa [Set.minimal_iff_forall_sdiff_singleton hP, hs] using h

@[deprecated (since := "2026-06-03")]
alias Set.exists_diff_singleton_of_not_minimal := Set.exists_sdiff_singleton_of_not_minimal

中文:
定理 集合.存在_sdiff_singleton_of_not_minimal
  结论: (hP : 对任意 ⦃s t⦄, P t -> t subseteq s -> P s) (hs : P s)
  证明: by
  simpa [Set.minimal_iff_forall_sdiff_singleton hP, hs] using h

@[deprecated (since := "2026-06-03")]
alias Set.exists_diff_singleton_of_not_minimal := Set.exists_sdiff_singleton_of_not_minimal

Depends on / 依赖: Set.minimal_iff_forall_sdiff_singleton, minimal_iff_forall_sdiff_singleton
-/
theorem Set.exists_sdiff_singleton_of_not_minimal (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) (hs : P s)
    (h : ¬ Minimal P s) : exists x in s, P (s \ {x}) := by
  simpa [Set.minimal_iff_forall_sdiff_singleton hP, hs] using h

@[deprecated (since := "2026-06-03")]
alias Set.exists_diff_singleton_of_not_minimal := Set.exists_sdiff_singleton_of_not_minimal

/--
theorem `Set.maximal_iff_forall_ssuperset` / 定理 `Set.maximal_iff_forall_ssuperset`

English:
theorem Set.maximal_iff_forall_ssuperset
  statement: Maximal P s ↔ P s ∧ forall ⦃t⦄, s ⊂ t -> ¬ P t
  proof: maximal_iff_forall_gt

中文:
定理 集合.maximal_iff_对任意_ssuperset
  结论: 极大 P s ↔ P s ∧ 对任意 ⦃t⦄, s ⊂ t -> ¬ P t
  证明: maximal_iff_forall_gt

Depends on / 依赖: maximal_iff_forall_gt
-/
theorem Set.maximal_iff_forall_ssuperset : Maximal P s ↔ P s ∧ forall ⦃t⦄, s ⊂ t -> ¬ P t :=
  maximal_iff_forall_gt

/--
theorem `Maximal.not_prop_of_ssuperset` / 定理 `Maximal.not_prop_of_ssuperset`

English:
theorem Maximal.not_prop_of_ssuperset
  given: (h : Maximal P s) (ht : s ⊂ t)
  statement: ¬ P t
  proof: (maximal_iff_forall_gt.1 h).2 ht

中文:
定理 极大.not_prop_of_ssuperset
  条件: (h : 极大 P s) (ht : s ⊂ t)
  结论: ¬ P t
  证明: (maximal_iff_forall_gt.1 h).2 ht

Depends on / 依赖: maximal_iff_forall_gt
-/
theorem Maximal.not_prop_of_ssuperset (h : Maximal P s) (ht : s ⊂ t) : ¬ P t :=
  (maximal_iff_forall_gt.1 h).2 ht

/--
theorem `Maximal.not_ssuperset` / 定理 `Maximal.not_ssuperset`

English:
theorem Maximal.not_ssuperset
  given: (h : Maximal P s) (ht : P t)
  statement: ¬ s ⊂ t
  proof: h.not_gt ht

中文:
定理 极大.not_ssuperset
  条件: (h : 极大 P s) (ht : P t)
  结论: ¬ s ⊂ t
  证明: h.not_gt ht

Depends on / 依赖: h.not_gt, not_gt
-/
theorem Maximal.not_ssuperset (h : Maximal P s) (ht : P t) : ¬ s ⊂ t :=
  h.not_gt ht

/--
theorem `Set.maximal_iff_forall_insert` / 定理 `Set.maximal_iff_forall_insert`

English:
theorem Set.maximal_iff_forall_insert
  given: (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s)
  proof: by
  simp only [not_imp_not]
  exact ⟨fun h => ⟨h.1, fun x => h.mem_of_prop_insert⟩,
    fun h => ⟨h.1, fun t ht hst x hxt => h.2 x (hP ht <| insert_subset hxt hst)⟩⟩

中文:
定理 集合.maximal_iff_对任意_insert
  条件: (hP : 对任意 ⦃s t⦄, P t -> s subseteq t -> P s)
  证明: by
  simp only [not_imp_not]
  exact ⟨fun h => ⟨h.1, fun x => h.mem_of_prop_insert⟩,
    fun h => ⟨h.1, fun t ht hst x hxt => h.2 x (hP ht <| insert_subset hxt hst)⟩⟩

Depends on / 依赖: h.mem_of_prop_insert, insert_subset, mem_of_prop_insert, not_imp_not
-/
theorem Set.maximal_iff_forall_insert (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s) :
    Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (insert x s) := by
  simp only [not_imp_not]
  exact ⟨fun h => ⟨h.1, fun x => h.mem_of_prop_insert⟩,
    fun h => ⟨h.1, fun t ht hst x hxt => h.2 x (hP ht <| insert_subset hxt hst)⟩⟩

/--
theorem `Set.exists_insert_of_not_maximal` / 定理 `Set.exists_insert_of_not_maximal`

English:
theorem Set.exists_insert_of_not_maximal
  statement: (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s) (hs : P s)
  proof: by
  simpa [Set.maximal_iff_forall_insert hP, hs] using h

中文:
定理 集合.存在_insert_of_not_maximal
  结论: (hP : 对任意 ⦃s t⦄, P t -> s subseteq t -> P s) (hs : P s)
  证明: by
  simpa [Set.maximal_iff_forall_insert hP, hs] using h

Depends on / 依赖: Set.maximal_iff_forall_insert, maximal_iff_forall_insert
-/
theorem Set.exists_insert_of_not_maximal (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s) (hs : P s)
    (h : ¬ Maximal P s) : exists x ∉ s, P (insert x s) := by
  simpa [Set.maximal_iff_forall_insert hP, hs] using h

/- TODO : generalize `minimal_iff_forall_sdiff_singleton` and `maximal_iff_forall_insert`
to `IsStronglyCoatomic`/`IsStronglyAtomic` orders. -/

end Subset

section Set

variable {s t : Set α}
section Preorder

variable [Preorder α]

@[to_dual]
/--
theorem `setOfPred_minimal_subset` / 定理 `setOfPred_minimal_subset`

English:
theorem setOfPred_minimal_subset
  given: (s : Set α)
  statement: {x | Minimal (· in s) x} subseteq s
  proof: sep_subset ..

@[deprecated (since := "2026-07-09")] alias setOf_minimal_subset := setOfPred_minimal_subset
@[deprecated (since := "2026-07-09")] alias setOf_maximal_subset := setOfPred_maximal_subset

@[to_dual]

中文:
定理 setOfPred_minimal_subset
  条件: (s : 集合 α)
  结论: {x | 极小 (· in s) x} subseteq s
  证明: sep_subset ..

@[deprecated (since := "2026-07-09")] alias setOf_minimal_subset := setOfPred_minimal_subset
@[deprecated (since := "2026-07-09")] alias setOf_maximal_subset := setOfPred_maximal_subset

@[to_dual]

Depends on / 依赖: sep_subset
-/
theorem setOfPred_minimal_subset (s : Set α) : {x | Minimal (· in s) x} subseteq s :=
  sep_subset ..

@[deprecated (since := "2026-07-09")] alias setOf_minimal_subset := setOfPred_minimal_subset
@[deprecated (since := "2026-07-09")] alias setOf_maximal_subset := setOfPred_maximal_subset

@[to_dual]
/--
theorem `Set.Subsingleton.minimal_mem_iff` / 定理 `Set.Subsingleton.minimal_mem_iff`

English:
theorem Set.Subsingleton.minimal_mem_iff
  given: (h : s.Subsingleton)
  statement: Minimal (· in s) x ↔ x in s
  proof: by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

@[to_dual]

中文:
定理 集合.子单例.minimal_mem_iff
  条件: (h : s.子单例)
  结论: 极小 (· in s) x ↔ x in s
  证明: by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

@[to_dual]

Depends on / 依赖: eq_empty_or_singleton, h.eq_empty_or_singleton
-/
theorem Set.Subsingleton.minimal_mem_iff (h : s.Subsingleton) : Minimal (· in s) x ↔ x in s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

@[to_dual]
/--
theorem `IsLeast.minimal` / 定理 `IsLeast.minimal`

English:
theorem IsLeast.minimal
  given: (h : IsLeast s x)
  statement: Minimal (· in s) x
  proof: ⟨h.1, fun _b hb _ => h.2 hb⟩

中文:
定理 IsLeast.minimal
  条件: (h : IsLeast s x)
  结论: 极小 (· in s) x
  证明: ⟨h.1, fun _b hb _ => h.2 hb⟩
-/
theorem IsLeast.minimal (h : IsLeast s x) : Minimal (· in s) x :=
  ⟨h.1, fun _b hb _ => h.2 hb⟩

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual]
/--
theorem `IsLeast.minimal_iff` / 定理 `IsLeast.minimal_iff`

English:
theorem IsLeast.minimal_iff
  given: (h : IsLeast s a)
  statement: Minimal (· in s) x ↔ x = a
  proof: ⟨fun h' => h'.eq_of_ge h.1 (h.2 h'.prop), fun h' => h' ▸ h.minimal⟩

中文:
定理 IsLeast.minimal_iff
  条件: (h : IsLeast s a)
  结论: 极小 (· in s) x ↔ x = a
  证明: ⟨fun h' => h'.eq_of_ge h.1 (h.2 h'.prop), fun h' => h' ▸ h.minimal⟩

Depends on / 依赖: eq_of_ge, h.minimal, minimal
-/
theorem IsLeast.minimal_iff (h : IsLeast s a) : Minimal (· in s) x ↔ x = a :=
  ⟨fun h' => h'.eq_of_ge h.1 (h.2 h'.prop), fun h' => h' ▸ h.minimal⟩

end PartialOrder

end Set

section Image

variable [Preorder α] [Preorder β] {s : Set α} {t : Set β}
section Function

variable {f : α -> β}

-- TODO: the names in this section are all wrong
@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `minimal_mem_image_monotone` / 定理 `minimal_mem_image_monotone`

English:
theorem minimal_mem_image_monotone
  statement: (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y))
  proof: by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy]; rw [hf hy hx.prop]
  exact hx.le_of_le hy

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 minimal_mem_image_monotone
  结论: (hf : 对任意 ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y))
  证明: by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy]; rw [hf hy hx.prop]
  exact hx.le_of_le hy

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: hx.le_of_le, hx.prop, le_of_le, mem_image_of_mem
-/
theorem minimal_mem_image_monotone (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y))
    (hx : Minimal (· in s) x) : Minimal (· in f '' s) (f x) := by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy]; rw [hf hy hx.prop]
  exact hx.le_of_le hy

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `minimal_mem_image_monotone_iff` / 定理 `minimal_mem_image_monotone_iff`

English:
theorem minimal_mem_image_monotone_iff
  statement: (ha : a in s)
  proof: by
  refine ⟨fun h => ⟨ha, fun y hys => ?_⟩, minimal_mem_image_monotone hf⟩
  rw [← hf ha hys]; rw [← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 minimal_mem_image_monotone_iff
  结论: (ha : a in s)
  证明: by
  refine ⟨fun h => ⟨ha, fun y hys => ?_⟩, minimal_mem_image_monotone hf⟩
  rw [← hf ha hys]; rw [← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: h.le_of_le, le_of_le, mem_image_of_mem, minimal_mem_image_monotone
-/
theorem minimal_mem_image_monotone_iff (ha : a in s)
    (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) :
    Minimal (· in f '' s) (f a) ↔ Minimal (· in s) a := by
  refine ⟨fun h => ⟨ha, fun y hys => ?_⟩, minimal_mem_image_monotone hf⟩
  rw [← hf ha hys]; rw [← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `minimal_mem_image_antitone` / 定理 `minimal_mem_image_antitone`

English:
theorem minimal_mem_image_antitone
  statement: (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x))
  proof: minimal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' => hf h' h) hx

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 minimal_mem_image_antitone
  结论: (hf : 对任意 ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x))
  证明: minimal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' => hf h' h) hx

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: minimal_mem_image_monotone
-/
theorem minimal_mem_image_antitone (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x))
    (hx : Minimal (· in s) x) : Maximal (· in f '' s) (f x) :=
  minimal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' => hf h' h) hx

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `minimal_mem_image_antitone_iff` / 定理 `minimal_mem_image_antitone_iff`

English:
theorem minimal_mem_image_antitone_iff
  statement: (ha : a in s)
  proof: maximal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' => hf h' h)

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 minimal_mem_image_antitone_iff
  结论: (ha : a in s)
  证明: maximal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' => hf h' h)

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: maximal_mem_image_monotone_iff
-/
theorem minimal_mem_image_antitone_iff (ha : a in s)
    (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x)) :
    Minimal (· in f '' s) (f a) ↔ Maximal (· in s) a :=
  maximal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' => hf h' h)

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `image_monotone_setOfPred_minimal` / 定理 `image_monotone_setOfPred_minimal`

English:
theorem image_monotone_setOfPred_minimal
  given: (hf : forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y))
  proof: by
  refine Set.ext fun x => ⟨?_, fun h => ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    exact (minimal_mem_image_monotone_iff hx.prop hf).2 hx
  obtain ⟨y, hy, rfl⟩ := (mem_ofPred_eq ▸ h).prop
exact mem_image_of_mem _ (minimal_mem_image_monotone_iff (s := Set.ofPred P) hy hf).1 h

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal := image_monotone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal := image_monotone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 image_monotone_setOfPred_minimal
  条件: (hf : 对任意 ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y))
  证明: by
  refine Set.ext fun x => ⟨?_, fun h => ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    exact (minimal_mem_image_monotone_iff hx.prop hf).2 hx
  obtain ⟨y, hy, rfl⟩ := (mem_ofPred_eq ▸ h).prop
exact mem_image_of_mem _ (minimal_mem_image_monotone_iff (s := Set.ofPred P) hy hf).1 h

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal := image_monotone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal := image_monotone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: Minimal, Set.ext, Set.ofPred, hx.prop, mem_image_of_mem, mem_ofPred_eq, minimal_mem_image_monotone_iff, ofPred
-/
theorem image_monotone_setOfPred_minimal (hf : forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y)) :
    f '' {x | Minimal P x} = {x | Minimal (exists x₀, P x₀ ∧ f x₀ = ·) x} := by
  refine Set.ext fun x => ⟨?_, fun h => ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    exact (minimal_mem_image_monotone_iff hx.prop hf).2 hx
  obtain ⟨y, hy, rfl⟩ := (mem_ofPred_eq ▸ h).prop
exact mem_image_of_mem _ (minimal_mem_image_monotone_iff (s := Set.ofPred P) hy hf).1 h

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal := image_monotone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal := image_monotone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `image_antitone_setOfPred_minimal` / 定理 `image_antitone_setOfPred_minimal`

English:
theorem image_antitone_setOfPred_minimal
  given: (hf : forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ y <= x))
  proof: image_monotone_setOfPred_minimal (β := βᵒᵈ) (fun _ _ hx hy => hf hy hx)

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal := image_antitone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal := image_antitone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 image_antitone_setOfPred_minimal
  条件: (hf : 对任意 ⦃x y⦄, P x -> P y -> (f x <= f y ↔ y <= x))
  证明: image_monotone_setOfPred_minimal (β := βᵒᵈ) (fun _ _ hx hy => hf hy hx)

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal := image_antitone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal := image_antitone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: image_monotone_setOfPred_minimal
-/
theorem image_antitone_setOfPred_minimal (hf : forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ y <= x)) :
    f '' {x | Minimal P x} = {x | Maximal (exists x₀, P x₀ ∧ f x₀ = ·) x} :=
  image_monotone_setOfPred_minimal (β := βᵒᵈ) (fun _ _ hx hy => hf hy hx)

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal := image_antitone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal := image_antitone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `image_monotone_setOfPred_minimal_mem` / 定理 `image_monotone_setOfPred_minimal_mem`

English:
theorem image_monotone_setOfPred_minimal_mem
  given: (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y))
  proof: image_monotone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal_mem := image_monotone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal_mem := image_monotone_setOfPred_maximal_mem

@[to_dual (reorder := hf (x y, 3 4))]

中文:
定理 image_monotone_setOfPred_minimal_mem
  条件: (hf : 对任意 ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y))
  证明: image_monotone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal_mem := image_monotone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal_mem := image_monotone_setOfPred_maximal_mem

@[to_dual (reorder := hf (x y, 3 4))]

Depends on / 依赖: image_monotone_setOfPred_minimal
-/
theorem image_monotone_setOfPred_minimal_mem (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) :
    f '' {x | Minimal (· in s) x} = {x | Minimal (· in f '' s) x} :=
  image_monotone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal_mem := image_monotone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal_mem := image_monotone_setOfPred_maximal_mem

@[to_dual (reorder := hf (x y, 3 4))]
/--
theorem `image_antitone_setOfPred_minimal_mem` / 定理 `image_antitone_setOfPred_minimal_mem`

English:
theorem image_antitone_setOfPred_minimal_mem
  given: (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x))
  proof: image_antitone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal_mem := image_antitone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal_mem := image_antitone_setOfPred_maximal_mem

中文:
定理 image_antitone_setOfPred_minimal_mem
  条件: (hf : 对任意 ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x))
  证明: image_antitone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal_mem := image_antitone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal_mem := image_antitone_setOfPred_maximal_mem

Depends on / 依赖: image_antitone_setOfPred_minimal
-/
theorem image_antitone_setOfPred_minimal_mem (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x)) :
    f '' {x | Minimal (· in s) x} = {x | Maximal (· in f '' s) x} :=
  image_antitone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal_mem := image_antitone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal_mem := image_antitone_setOfPred_maximal_mem

end Function

namespace OrderEmbedding

variable {f : α ↪o β} {t : Set β}

@[to_dual]
/--
theorem `minimal_mem_image` / 定理 `minimal_mem_image`

English:
theorem minimal_mem_image
  given: (f : α ↪o β) (hx : Minimal (· in s) x)
  statement: Minimal (· in f '' s) (f x)
  proof: _root_.minimal_mem_image_monotone (by simp [f.le_iff_le]) hx

@[to_dual]

中文:
定理 minimal_mem_image
  条件: (f : α ↪o β) (hx : 极小 (· in s) x)
  结论: 极小 (· in f '' s) (f x)
  证明: _root_.minimal_mem_image_monotone (by simp [f.le_iff_le]) hx

@[to_dual]

Depends on / 依赖: _root_, _root_.minimal_mem_image_monotone, f.le_iff_le, le_iff_le, minimal_mem_image_monotone
-/
theorem minimal_mem_image (f : α ↪o β) (hx : Minimal (· in s) x) : Minimal (· in f '' s) (f x) :=
  _root_.minimal_mem_image_monotone (by simp [f.le_iff_le]) hx

@[to_dual]
/--
theorem `minimal_mem_image_iff` / 定理 `minimal_mem_image_iff`

English:
theorem minimal_mem_image_iff
  given: (ha : a in s)
  statement: Minimal (· in f '' s) (f a) ↔ Minimal (· in s) a
  proof: _root_.minimal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

@[to_dual]

中文:
定理 minimal_mem_image_iff
  条件: (ha : a in s)
  结论: 极小 (· in f '' s) (f a) ↔ 极小 (· in s) a
  证明: _root_.minimal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

@[to_dual]

Depends on / 依赖: _root_, _root_.minimal_mem_image_monotone_iff, f.le_iff_le, le_iff_le, minimal_mem_image_monotone_iff
-/
theorem minimal_mem_image_iff (ha : a in s) : Minimal (· in f '' s) (f a) ↔ Minimal (· in s) a :=
  _root_.minimal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

@[to_dual]
/--
theorem `minimal_apply_mem_inter_range_iff` / 定理 `minimal_apply_mem_inter_range_iff`

English:
theorem minimal_apply_mem_inter_range_iff
  proof: by
  refine ⟨fun h => ⟨h.prop.1, fun y hy => ?_⟩, fun h => ⟨⟨h.prop, mem_range_self x⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, mem_range_self y⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

@[to_dual]

中文:
定理 minimal_apply_mem_inter_range_iff
  证明: by
  refine ⟨fun h => ⟨h.prop.1, fun y hy => ?_⟩, fun h => ⟨⟨h.prop, mem_range_self x⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, mem_range_self y⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

@[to_dual]

Depends on / 依赖: f.le_iff_le, h.le_of_le, h.prop, le_iff_le, le_of_le, mem_range_self, simp_rw
-/
theorem minimal_apply_mem_inter_range_iff :
    Minimal (· in t inter range f) (f x) ↔ Minimal (fun x => f x in t) x := by
  refine ⟨fun h => ⟨h.prop.1, fun y hy => ?_⟩, fun h => ⟨⟨h.prop, mem_range_self x⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, mem_range_self y⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

@[to_dual]
/--
theorem `minimal_apply_mem_iff` / 定理 `minimal_apply_mem_iff`

English:
theorem minimal_apply_mem_iff
  given: (ht : t subseteq Set.range f)
  proof: by
  rw [← f.minimal_apply_mem_inter_range_iff]; rw [inter_eq_self_of_subset_left ht]

@[deprecated (since := "2026-04-07")] alias maximal_apply_iff := maximal_apply_mem_iff

中文:
定理 minimal_apply_mem_iff
  条件: (ht : t subseteq 集合.range f)
  证明: by
  rw [← f.minimal_apply_mem_inter_range_iff]; rw [inter_eq_self_of_subset_left ht]

@[deprecated (since := "2026-04-07")] alias maximal_apply_iff := maximal_apply_mem_iff

Depends on / 依赖: f.minimal_apply_mem_inter_range_iff, inter_eq_self_of_subset_left, minimal_apply_mem_inter_range_iff
-/
theorem minimal_apply_mem_iff (ht : t subseteq Set.range f) :
    Minimal (· in t) (f x) ↔ Minimal (fun x => f x in t) x := by
  rw [← f.minimal_apply_mem_inter_range_iff]; rw [inter_eq_self_of_subset_left ht]

@[deprecated (since := "2026-04-07")] alias maximal_apply_iff := maximal_apply_mem_iff

/--
theorem `image_setOfPred_minimal` / 定理 `image_setOfPred_minimal`

English:
theorem image_setOfPred_minimal
  statement: f '' {x | Minimal (· in s) x} = {x | Minimal (· in f '' s) x}
  proof: _root_.image_monotone_setOfPred_minimal (by simp [f.le_iff_le])

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal

@[to_dual]

中文:
定理 image_setOfPred_minimal
  结论: f '' {x | 极小 (· in s) x} = {x | 极小 (· in f '' s) x}
  证明: _root_.image_monotone_setOfPred_minimal (by simp [f.le_iff_le])

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal

@[to_dual]

Depends on / 依赖: _root_, _root_.image_monotone_setOfPred_minimal, f.le_iff_le, image_monotone_setOfPred_minimal, le_iff_le
-/
theorem image_setOfPred_minimal : f '' {x | Minimal (· in s) x} = {x | Minimal (· in f '' s) x} :=
  _root_.image_monotone_setOfPred_minimal (by simp [f.le_iff_le])

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal

@[to_dual]
/--
theorem `inter_preimage_setOfPred_minimal_eq_of_subset` / 定理 `inter_preimage_setOfPred_minimal_eq_of_subset`

English:
theorem inter_preimage_setOfPred_minimal_eq_of_subset
  given: (hts : t subseteq f '' s)
  proof: by
  simp_rw [mem_inter_iff, preimage_ofPred_eq, mem_ofPred_eq, mem_preimage,
    f.minimal_apply_mem_iff (hts.trans (image_subset_range _ _)),
    minimal_and_iff_left_of_imp (fun _ hx => f.injective.mem_set_image.1 <| hts hx)]

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_minimal_eq_of_subset := inter_preimage_setOfPred_minimal_eq_of_subset

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_maximal_eq_of_subset := inter_preimage_setOfPred_maximal_eq_of_subset

中文:
定理 inter_preimage_setOfPred_minimal_eq_of_subset
  条件: (hts : t subseteq f '' s)
  证明: by
  simp_rw [mem_inter_iff, preimage_ofPred_eq, mem_ofPred_eq, mem_preimage,
    f.minimal_apply_mem_iff (hts.trans (image_subset_range _ _)),
    minimal_and_iff_left_of_imp (fun _ hx => f.injective.mem_set_image.1 <| hts hx)]

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_minimal_eq_of_subset := inter_preimage_setOfPred_minimal_eq_of_subset

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_maximal_eq_of_subset := inter_preimage_setOfPred_maximal_eq_of_subset

Depends on / 依赖: f.injective.mem_set_image, f.minimal_apply_mem_iff, hts.trans, image_subset_range, injective, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_set_image, minimal_and_iff_left_of_imp, minimal_apply_mem_iff, preimage_ofPred_eq, simp_rw
-/
theorem inter_preimage_setOfPred_minimal_eq_of_subset (hts : t subseteq f '' s) :
    x in s inter f ⁻¹' {y | Minimal (· in t) y} ↔ Minimal (· in s inter f ⁻¹' t) x := by
  simp_rw [mem_inter_iff, preimage_ofPred_eq, mem_ofPred_eq, mem_preimage,
    f.minimal_apply_mem_iff (hts.trans (image_subset_range _ _)),
    minimal_and_iff_left_of_imp (fun _ hx => f.injective.mem_set_image.1 <| hts hx)]

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_minimal_eq_of_subset := inter_preimage_setOfPred_minimal_eq_of_subset

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_maximal_eq_of_subset := inter_preimage_setOfPred_maximal_eq_of_subset

end OrderEmbedding

namespace OrderIso

@[to_dual]
/--
theorem `image_setOfPred_minimal` / 定理 `image_setOfPred_minimal`

English:
theorem image_setOfPred_minimal
  given: (f : α ≃o β) (P : α -> Prop)
  proof: by
  convert! _root_.image_monotone_setOfPred_minimal (f := f) (by simp [f.le_iff_le])
  aesop

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal
@[deprecated (since := "2026-07-09")]
alias image_setOf_maximal := image_setOfPred_maximal

@[to_dual]

中文:
定理 image_setOfPred_minimal
  条件: (f : α ≃o β) (P : α -> 命题)
  证明: by
  convert! _root_.image_monotone_setOfPred_minimal (f := f) (by simp [f.le_iff_le])
  aesop

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal
@[deprecated (since := "2026-07-09")]
alias image_setOf_maximal := image_setOfPred_maximal

@[to_dual]

Depends on / 依赖: _root_, _root_.image_monotone_setOfPred_minimal, convert, f.le_iff_le, image_monotone_setOfPred_minimal, le_iff_le
-/
theorem image_setOfPred_minimal (f : α ≃o β) (P : α -> Prop) :
    f '' {x | Minimal P x} = {x | Minimal (fun x => P (f.symm x)) x} := by
  convert! _root_.image_monotone_setOfPred_minimal (f := f) (by simp [f.le_iff_le])
  aesop

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal
@[deprecated (since := "2026-07-09")]
alias image_setOf_maximal := image_setOfPred_maximal

@[to_dual]
/--
theorem `map_minimal_mem` / 定理 `map_minimal_mem`

English:
theorem map_minimal_mem
  given: (f : s ≃o t) (hx : Minimal (· in s) x)
  proof: by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using! OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype (· in t))) (s := univ) (x := ⟨x, hx.prop⟩)

中文:
定理 map_minimal_mem
  条件: (f : s ≃o t) (hx : 极小 (· in s) x)
  证明: by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using! OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype (· in t))) (s := univ) (x := ⟨x, hx.prop⟩)

Depends on / 依赖: OrderEmbedding, OrderEmbedding.minimal_mem_image, OrderEmbedding.subtype, Subtype, Subtype.val, f.toOrderEmbedding.trans, hx.prop, image_univ, mem_univ, minimal_mem_image, minimal_true_subtype, subtype, toOrderEmbedding, true_imp_iff
-/
theorem map_minimal_mem (f : s ≃o t) (hx : Minimal (· in s) x) :
    Minimal (· in t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using! OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype (· in t))) (s := univ) (x := ⟨x, hx.prop⟩)

/--
Definition of `mapSetOfPredMinimal` / `mapSetOfPredMinimal` 的定义

English:
definition mapSetOfPredMinimal
  signature: (f : s ≃o t)
  body: ⟨f ⟨x, x.2.1⟩, f.map_minimal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_minimal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMinimal := mapSetOfPredMinimal

中文:
定义 mapSetOfPredMinimal
  签名: (f : s ≃o t)
  定义体: ⟨f ⟨x, x.2.1⟩, f.map_minimal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_minimal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMinimal := mapSetOfPredMinimal

Depends on / 依赖: f.map_minimal_mem, map_minimal_mem
-/
def mapSetOfPredMinimal (f : s ≃o t) : {x | Minimal (· in s) x} ≃o {x | Minimal (· in t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_minimal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_minimal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMinimal := mapSetOfPredMinimal

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
@[to_dual existing]
/--
Definition of `mapSetOfPredMaximal` / `mapSetOfPredMaximal` 的定义

English:
definition mapSetOfPredMaximal
  signature: (f : s ≃o t)
  body: ⟨f ⟨x, x.2.1⟩, f.map_maximal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_maximal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMaximal := mapSetOfPredMaximal

中文:
定义 mapSetOfPredMaximal
  签名: (f : s ≃o t)
  定义体: ⟨f ⟨x, x.2.1⟩, f.map_maximal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_maximal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMaximal := mapSetOfPredMaximal

Depends on / 依赖: f.map_maximal_mem, map_maximal_mem
-/
def mapSetOfPredMaximal (f : s ≃o t) : {x | Maximal (· in s) x} ≃o {x | Maximal (· in t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_maximal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_maximal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMaximal := mapSetOfPredMaximal

/-- If two sets are antitonically order isomorphic, their minimals/maximals are too. -/
@[to_dual /-- If two sets are antitonically order isomorphic, their maximals/minimals are too. -/]
/--
Definition of `setOfPredMinimalIsoSetOfPredMaximal` / `setOfPredMinimalIsoSetOfPredMaximal` 的定义

English:
definition setOfPredMinimalIsoSetOfPredMaximal
  signature: (f : s ≃o tᵒᵈ)
  body: ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal x).2⟩
      invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfPredMinimal x).2⟩
      __ := (show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal

@[deprecated (since := "2026-07-09")]
alias setOfMinimalIsoSetOfMaximal := setOfPredMinimalIsoSetOfPredMaximal
@[deprecated (since := "2026-07-09")]
alias setOfMaximalIsoSetOfMinimal := setOfPredMaximalIsoSetOfPredMinimal

中文:
定义 setOfPredMinimalIsoSetOfPredMaximal
  签名: (f : s ≃o tᵒᵈ)
  定义体: ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal x).2⟩
      invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfPredMinimal x).2⟩
      __ := (show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal

@[deprecated (since := "2026-07-09")]
alias setOfMinimalIsoSetOfMaximal := setOfPredMinimalIsoSetOfPredMaximal
@[deprecated (since := "2026-07-09")]
alias setOfMaximalIsoSetOfMinimal := setOfPredMaximalIsoSetOfPredMinimal

Depends on / 依赖: mapSetOfPredMinimal, ofDual
-/
def setOfPredMinimalIsoSetOfPredMaximal (f : s ≃o tᵒᵈ) :
    {x | Minimal (· in s) x} ≃o {x | Maximal (· in t) (ofDual x)} where
      toFun x := ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal x).2⟩
      invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfPredMinimal x).2⟩
      __ := (show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal

@[deprecated (since := "2026-07-09")]
alias setOfMinimalIsoSetOfMaximal := setOfPredMinimalIsoSetOfPredMaximal
@[deprecated (since := "2026-07-09")]
alias setOfMaximalIsoSetOfMinimal := setOfPredMaximalIsoSetOfPredMinimal

end OrderIso

end Image
section Interval

variable [PartialOrder α] {a b : α}

@[to_dual]
/--
theorem `minimal_mem_Icc` / 定理 `minimal_mem_Icc`

English:
theorem minimal_mem_Icc
  given: (hab : a <= b)
  statement: Minimal (· in Icc a b) x ↔ x = a
  proof: minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ => And.left)

@[to_dual]

中文:
定理 minimal_mem_Icc
  条件: (hab : a <= b)
  结论: 极小 (· in 闭区间 a b) x ↔ x = a
  证明: minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ => And.left)

@[to_dual]

Depends on / 依赖: And.left, minimal_iff_eq, rfl.le
-/
theorem minimal_mem_Icc (hab : a <= b) : Minimal (· in Icc a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ => And.left)

@[to_dual]
/--
theorem `minimal_mem_Ico` / 定理 `minimal_mem_Ico`

English:
theorem minimal_mem_Ico
  given: (hab : a < b)
  statement: Minimal (· in Ico a b) x ↔ x = a
  proof: minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ => And.left)

中文:
定理 minimal_mem_Ico
  条件: (hab : a < b)
  结论: 极小 (· in 左闭右开区间 a b) x ↔ x = a
  证明: minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ => And.left)

Depends on / 依赖: And.left, minimal_iff_eq, rfl.le
-/
theorem minimal_mem_Ico (hab : a < b) : Minimal (· in Ico a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ => And.left)

/- Note : The one-sided interval versions of these lemmas are unnecessary,
since `simp` handles them with `maximal_le_iff` and `minimal_ge_iff`. -/

end Interval
