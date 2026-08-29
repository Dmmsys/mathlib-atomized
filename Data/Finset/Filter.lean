/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Multiset.Filter

/-!
# Filtering a finite set

## Main declarations

* `Finset.filter`: Given a decidable predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### filter -/

section Filter

variable (p q : α -> Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (s : Finset α)
  body: ⟨_, s.2.filter p⟩

中文:
定义 filter
  签名: (s : Finset α)
  定义体: ⟨_, s.2.filter p⟩

Depends on / 依赖: filter
-/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩

end Finset.Filter

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder

/-- Return `true` if `expectedType?` is `some (Finset ?α)`, throws `throwUnsupportedSyntax` if it is
`some (Set ?α)`, and returns `false` otherwise. -/
meta def knownToBeFinsetNotSet (expectedType? : Option Expr) : TermElabM Bool :=
  -- As we want to reason about the expected type, we would like to wait for it to be available.
  -- However this means that if we fall back on `elabSetBuilder` we will have postponed.
  -- This is undesirable as we want set builder notation to quickly elaborate to a `Set` when no
  -- expected type is available.
  -- tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | some expectedType =>
    match_expr expectedType with
    -- If the expected type is known to be `Finset ?α`, return `true`.
    | Finset _ => pure true
    -- If the expected type is known to be `Set ?α`, give up.
    | Set _ => throwUnsupportedSyntax
    -- If the expected type is known to not be `Finset ?α` or `Set ?α`, return `false`.
    | _ => pure false
  -- If the expected type is not known, return `false`.
  | none => pure false

/-- Elaborate set builder notation for `Finset`.

`{x ∈ s | p x}` is elaborated as `Finset.filter (fun x ↦ p x) s` if either the expected type is
`Finset ?α` or the expected type is not `Set ?α` and `s` has expected type `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator handling syntax of the
  form `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.

TODO: Write a delaborator
-/
@[term_elab setBuilder]
meta def elabFinsetBuilderSep : TermElab
  | `({ $x:ident in $s:term | $p }), expectedType? => do
    -- If the expected type is known to be `Set ?α`, give up. If it is not known to be `Set ?α` or
    -- `Finset ?α`, check the expected type of `s`.
    unless ← knownToBeFinsetNotSet expectedType? do
      let ty ← try whnfR (← inferType (← elabTerm s none)) catch _ => throwUnsupportedSyntax
      -- If the expected type of `s` is not known to be `Finset ?α`, give up.
      match_expr ty with
      | Finset _ => pure ()
      | _ => throwUnsupportedSyntax
    -- Finally, we can elaborate the syntax as a finset.
    -- TODO: Seems a bit wasteful to have computed the expected type but still use `expectedType?`.
    elabTerm (← `(Finset.filter (fun $x:ident => $p) $s)) expectedType?
  | _, _ => throwUnsupportedSyntax

end Mathlib.Meta

namespace Finset
section Filter
variable (p q : α -> Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

@[simp]
/--
theorem `filter_val` / 定理 `filter_val`

English:
theorem filter_val
  given: (s : Finset α)
  statement: (filter p s).1 = s.1.filter p
  proof: rfl

@[simp]

中文:
定理 filter_val
  条件: (s : Finset α)
  结论: (filter p s).1 = s.1.filter p
  证明: rfl

@[simp]
-/
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl

@[simp]
/--
theorem `filter_subset` / 定理 `filter_subset`

English:
theorem filter_subset
  given: (s : Finset α)
  statement: s.filter p subseteq s
  proof: Multiset.filter_subset _ _

中文:
定理 filter_subset
  条件: (s : Finset α)
  结论: s.filter p subseteq s
  证明: Multiset.filter_subset _ _

Depends on / 依赖: Multiset, Multiset.filter_subset, filter_subset
-/
theorem filter_subset (s : Finset α) : s.filter p subseteq s :=
  Multiset.filter_subset _ _

variable {p}

@[simp, grind =]
/--
theorem `mem_filter` / 定理 `mem_filter`

English:
theorem mem_filter
  given: {s : Finset α} {a : α}
  statement: a in s.filter p ↔ a in s ∧ p a
  proof: Multiset.mem_filter

中文:
定理 mem_filter
  条件: {s : Finset α} {a : α}
  结论: a in s.filter p ↔ a in s ∧ p a
  证明: Multiset.mem_filter

Depends on / 依赖: Multiset, Multiset.mem_filter, mem_filter
-/
theorem mem_filter {s : Finset α} {a : α} : a in s.filter p ↔ a in s ∧ p a :=
  Multiset.mem_filter

/--
theorem `mem_of_mem_filter` / 定理 `mem_of_mem_filter`

English:
theorem mem_of_mem_filter
  given: {s : Finset α} (x : α) (h : x in s.filter p)
  statement: x in s
  proof: Multiset.mem_of_mem_filter h

中文:
定理 mem_of_mem_filter
  条件: {s : Finset α} (x : α) (h : x in s.filter p)
  结论: x in s
  证明: Multiset.mem_of_mem_filter h

Depends on / 依赖: Multiset, Multiset.mem_of_mem_filter, mem_of_mem_filter
-/
theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x in s.filter p) : x in s :=
  Multiset.mem_of_mem_filter h

/--
theorem `filter_ssubset` / 定理 `filter_ssubset`

English:
theorem filter_ssubset
  given: {s : Finset α}
  statement: s.filter p ⊂ s ↔ exists x in s, ¬p x
  proof: by grind

中文:
定理 filter_ssubset
  条件: {s : Finset α}
  结论: s.filter p ⊂ s ↔ 存在 x in s, ¬p x
  证明: by grind
-/
theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ exists x in s, ¬p x := by grind

variable (p)

/--
theorem `filter_filter` / 定理 `filter_filter`

English:
theorem filter_filter
  given: (s : Finset α)
  statement: (s.filter p).filter q = s.filter fun a => p a ∧ q a
  proof: by
  grind

中文:
定理 filter_filter
  条件: (s : Finset α)
  结论: (s.filter p).filter q = s.filter fun a => p a ∧ q a
  证明: by
  grind
-/
theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a := by
  grind

/--
theorem `filter_comm` / 定理 `filter_comm`

English:
theorem filter_comm
  given: (s : Finset α)
  statement: (s.filter p).filter q = (s.filter q).filter p
  proof: by
  grind

中文:
定理 filter_comm
  条件: (s : Finset α)
  结论: (s.filter p).filter q = (s.filter q).filter p
  证明: by
  grind
-/
theorem filter_comm (s : Finset α) : (s.filter p).filter q = (s.filter q).filter p := by
  grind

-- We can replace an application of filter where the decidability is inferred in "the wrong way".
/--
theorem `filter_congr_decidable` / 定理 `filter_congr_decidable`

English:
theorem filter_congr_decidable
  statement: (s : Finset α) (p : α -> Prop) (h : DecidablePred p)
  proof: by congr

@[simp]

中文:
定理 filter_congr_decidable
  结论: (s : Finset α) (p : α -> 命题) (h : DecidablePred p)
  证明: by congr

@[simp]
-/
theorem filter_congr_decidable (s : Finset α) (p : α -> Prop) (h : DecidablePred p)
    [DecidablePred p] : @filter α p h s = s.filter p := by congr

@[simp]
/--
theorem `filter_true` / 定理 `filter_true`

English:
theorem filter_true
  given: {h} (s : Finset α)
  statement: @filter _ (fun _ => True) h s = s
  proof: by ext; simp

@[simp]

中文:
定理 filter_true
  条件: {h} (s : Finset α)
  结论: @filter _ (fun _ => True) h s = s
  证明: by ext; simp

@[simp]
-/
theorem filter_true {h} (s : Finset α) : @filter _ (fun _ => True) h s = s := by ext; simp

@[simp]
/--
theorem `filter_false` / 定理 `filter_false`

English:
theorem filter_false
  given: {h} (s : Finset α)
  statement: @filter _ (fun _ => False) h s = ∅
  proof: by ext; simp

中文:
定理 filter_false
  条件: {h} (s : Finset α)
  结论: @filter _ (fun _ => False) h s = ∅
  证明: by ext; simp
-/
theorem filter_false {h} (s : Finset α) : @filter _ (fun _ => False) h s = ∅ := by ext; simp

variable {p q}

@[simp]
/--
lemma `filter_eq_self` / 引理 `filter_eq_self`

English:
lemma filter_eq_self
  statement: s.filter p = s ↔ forall x in s, p x
  proof: by simp [Finset.ext_iff]

@[simp]

中文:
引理 filter_eq_self
  结论: s.filter p = s ↔ 对任意 x in s, p x
  证明: by simp [Finset.ext_iff]

@[simp]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
lemma filter_eq_self : s.filter p = s ↔ forall x in s, p x := by simp [Finset.ext_iff]

@[simp]
/--
theorem `filter_eq_empty_iff` / 定理 `filter_eq_empty_iff`

English:
theorem filter_eq_empty_iff
  statement: s.filter p = ∅ ↔ forall ⦃x⦄, x in s -> ¬p x
  proof: by simp [Finset.ext_iff]

中文:
定理 filter_eq_empty_iff
  结论: s.filter p = ∅ ↔ 对任意 ⦃x⦄, x in s -> ¬p x
  证明: by simp [Finset.ext_iff]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
theorem filter_eq_empty_iff : s.filter p = ∅ ↔ forall ⦃x⦄, x in s -> ¬p x := by simp [Finset.ext_iff]

/--
theorem `filter_nonempty_iff` / 定理 `filter_nonempty_iff`

English:
theorem filter_nonempty_iff
  statement: (s.filter p).Nonempty ↔ exists a in s, p a
  proof: by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]

中文:
定理 filter_nonempty_iff
  结论: (s.filter p).Nonempty ↔ 存在 a in s, p a
  证明: by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]

Depends on / 依赖: Classical, Classical.not_not, exists_prop, filter_eq_empty_iff, nonempty_iff_ne_empty, not_forall, not_not
-/
theorem filter_nonempty_iff : (s.filter p).Nonempty ↔ exists a in s, p a := by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]

/--
theorem `filter_true_of_mem` / 定理 `filter_true_of_mem`

English:
theorem filter_true_of_mem
  given: (h : forall x in s, p x)
  statement: s.filter p = s
  proof: filter_eq_self.2 h

中文:
定理 filter_true_of_mem
  条件: (h : 对任意 x in s, p x)
  结论: s.filter p = s
  证明: filter_eq_self.2 h

Depends on / 依赖: filter_eq_self
-/
theorem filter_true_of_mem (h : forall x in s, p x) : s.filter p = s := filter_eq_self.2 h

/--
theorem `filter_false_of_mem` / 定理 `filter_false_of_mem`

English:
theorem filter_false_of_mem
  given: (h : forall x in s, ¬p x)
  statement: s.filter p = ∅
  proof: filter_eq_empty_iff.2 h

@[simp]

中文:
定理 filter_false_of_mem
  条件: (h : 对任意 x in s, ¬p x)
  结论: s.filter p = ∅
  证明: filter_eq_empty_iff.2 h

@[simp]

Depends on / 依赖: filter_eq_empty_iff
-/
theorem filter_false_of_mem (h : forall x in s, ¬p x) : s.filter p = ∅ := filter_eq_empty_iff.2 h

@[simp]
/--
theorem `filter_const` / 定理 `filter_const`

English:
theorem filter_const
  given: (p : Prop) [Decidable p] (s : Finset α)
  proof: by split_ifs <;> simp [*]

@[congr]

中文:
定理 filter_const
  条件: (p : 命题) [Decidable p] (s : Finset α)
  证明: by split_ifs <;> simp [*]

@[congr]

Depends on / 依赖: split_ifs
-/
theorem filter_const (p : Prop) [Decidable p] (s : Finset α) :
    (s.filter fun _a => p) = if p then s else ∅ := by split_ifs <;> simp [*]

@[congr]
/--
theorem `filter_congr` / 定理 `filter_congr`

English:
theorem filter_congr
  given: {s : Finset α} (H : forall x in s, p x ↔ q x)
  statement: filter p s = filter q s
  proof: eq_of_veq Multiset.filter_congr H

中文:
定理 filter_congr
  条件: {s : Finset α} (H : 对任意 x in s, p x ↔ q x)
  结论: filter p s = filter q s
  证明: eq_of_veq Multiset.filter_congr H

Depends on / 依赖: Multiset, Multiset.filter_congr, eq_of_veq, filter_congr
-/
theorem filter_congr {s : Finset α} (H : forall x in s, p x ↔ q x) : filter p s = filter q s :=
eq_of_veq Multiset.filter_congr H

variable (p q)

@[simp]
/--
theorem `filter_empty` / 定理 `filter_empty`

English:
theorem filter_empty
  statement: filter p ∅ = ∅
  proof: subset_empty.1 filter_subset _ _

@[gcongr]

中文:
定理 filter_empty
  结论: filter p ∅ = ∅
  证明: subset_empty.1 filter_subset _ _

@[gcongr]

Depends on / 依赖: filter_subset, subset_empty
-/
theorem filter_empty : filter p ∅ = ∅ :=
subset_empty.1 filter_subset _ _

@[gcongr]
/--
theorem `filter_subset_filter` / 定理 `filter_subset_filter`

English:
theorem filter_subset_filter
  given: {s t : Finset α} (h : s subseteq t)
  statement: s.filter p subseteq t.filter p
  proof: fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

中文:
定理 filter_subset_filter
  条件: {s t : Finset α} (h : s subseteq t)
  结论: s.filter p subseteq t.filter p
  证明: fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
-/
theorem filter_subset_filter {s t : Finset α} (h : s subseteq t) : s.filter p subseteq t.filter p := fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

/--
theorem `monotone_filter_left` / 定理 `monotone_filter_left`

English:
theorem monotone_filter_left
  statement: Monotone (filter p)
  proof: fun _ _ => filter_subset_filter p

@[gcongr]

中文:
定理 monotone_filter_left
  结论: Monotone (filter p)
  证明: fun _ _ => filter_subset_filter p

@[gcongr]

Depends on / 依赖: filter_subset_filter
-/
theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p

@[gcongr]
/--
theorem `monotone_filter_right` / 定理 `monotone_filter_right`

English:
theorem monotone_filter_right
  given: (s : Finset α) ⦃p q
  statement: α -> Prop⦄ [DecidablePred p] [DecidablePred q]
  proof: by simp +contextual [subset_iff, h]

@[simp, norm_cast]

中文:
定理 monotone_filter_right
  条件: (s : Finset α) ⦃p q
  结论: α -> 命题⦄ [DecidablePred p] [DecidablePred q]
  证明: by simp +contextual [subset_iff, h]

@[simp, norm_cast]

Depends on / 依赖: contextual, subset_iff
-/
theorem monotone_filter_right (s : Finset α) ⦃p q : α -> Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : forall a in s, p a -> q a) : s.filter p subseteq s.filter q := by simp +contextual [subset_iff, h]

@[simp, norm_cast]
/--
theorem `coe_filter` / 定理 `coe_filter`

English:
theorem coe_filter
  given: (s : Finset α)
  statement: ↑(s.filter p) = ({ x in ↑s | p x } : Set α)
  proof: Set.ext fun _ => mem_filter

中文:
定理 coe_filter
  条件: (s : Finset α)
  结论: ↑(s.filter p) = ({ x in ↑s | p x } : Set α)
  证明: Set.ext fun _ => mem_filter

Depends on / 依赖: Set.ext, mem_filter
-/
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x in ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter

/--
theorem `subset_coe_filter_of_subset_forall` / 定理 `subset_coe_filter_of_subset_forall`

English:
theorem subset_coe_filter_of_subset_forall
  statement: (s : Finset α) {t : Set α} (h₁ : t subseteq s)
  proof: fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩

中文:
定理 subset_coe_filter_of_subset_forall
  结论: (s : Finset α) {t : Set α} (h₁ : t subseteq s)
  证明: fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩

Depends on / 依赖: coe_filter, s.coe_filter
-/
theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t subseteq s)
    (h₂ : forall x in t, p x) : t subseteq s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩

/--
theorem `disjoint_filter_filter` / 定理 `disjoint_filter_filter`

English:
theorem disjoint_filter_filter
  statement: {s t : Finset α}
  proof: Disjoint.mono (filter_subset _ _) (filter_subset _ _)

中文:
定理 disjoint_filter_filter
  结论: {s t : Finset α}
  证明: Disjoint.mono (filter_subset _ _) (filter_subset _ _)

Depends on / 依赖: Disjoint, Disjoint.mono, filter_subset
-/
theorem disjoint_filter_filter {s t : Finset α}
    {p q : α -> Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint s t -> Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)

/--
lemma `_root_.Set.pairwiseDisjoint_filter` / 引理 `_root_.Set.pairwiseDisjoint_filter`

English:
lemma _root_.Set.pairwiseDisjoint_filter
  given: [DecidableEq β] (f : α -> β) (s : Set β) (t : Finset α)
  proof: by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x in t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x in t ∧ f x = j := by simpa using hj hx
  contradiction

中文:
引理 _root_.Set.pairwiseDisjoint_filter
  条件: [DecidableEq β] (f : α -> β) (s : Set β) (t : Finset α)
  证明: by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x in t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x in t ∧ f x = j := by simpa using hj hx
  contradiction
-/
lemma _root_.Set.pairwiseDisjoint_filter [DecidableEq β] (f : α -> β) (s : Set β) (t : Finset α) :
    s.PairwiseDisjoint fun x => t.filter (f · = x) := by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x in t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x in t ∧ f x = j := by simpa using hj hx
  contradiction

/--
theorem `disjoint_filter_and_not_filter` / 定理 `disjoint_filter_and_not_filter`

English:
theorem disjoint_filter_and_not_filter
  proof: by
  intro _ htp htq
  simp only [bot_eq_empty, subset_empty]
  by_contra! ⟨_, hx⟩
  exact (mem_filter.mp (htq hx)).2.2 (mem_filter.mp (htp hx)).2.1

中文:
定理 disjoint_filter_and_not_filter
  证明: by
  intro _ htp htq
  simp only [bot_eq_empty, subset_empty]
  by_contra! ⟨_, hx⟩
  exact (mem_filter.mp (htq hx)).2.2 (mem_filter.mp (htp hx)).2.1

Depends on / 依赖: bot_eq_empty, mem_filter, mem_filter.mp, subset_empty
-/
theorem disjoint_filter_and_not_filter :
    Disjoint (s.filter (fun x => p x ∧ ¬q x)) (s.filter (fun x => q x ∧ ¬p x)) := by
  intro _ htp htq
  simp only [bot_eq_empty, subset_empty]
  by_contra! ⟨_, hx⟩
  exact (mem_filter.mp (htq hx)).2.2 (mem_filter.mp (htp hx)).2.1

variable {p q}

/--
lemma `filter_inj` / 引理 `filter_inj`

English:
lemma filter_inj
  statement: s.filter p = t.filter p ↔ forall ⦃a⦄, p a -> (a in s ↔ a in t)
  proof: by
  simp [Finset.ext_iff]

中文:
引理 filter_inj
  结论: s.filter p = t.filter p ↔ 对任意 ⦃a⦄, p a -> (a in s ↔ a in t)
  证明: by
  simp [Finset.ext_iff]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
lemma filter_inj : s.filter p = t.filter p ↔ forall ⦃a⦄, p a -> (a in s ↔ a in t) := by
  simp [Finset.ext_iff]

/--
lemma `filter_inj'` / 引理 `filter_inj'`

English:
lemma filter_inj'
  statement: s.filter p = s.filter q ↔ forall ⦃a⦄, a in s -> (p a ↔ q a)
  proof: by
  simp [Finset.ext_iff]

@[simp]

中文:
引理 filter_inj'
  结论: s.filter p = s.filter q ↔ 对任意 ⦃a⦄, a in s -> (p a ↔ q a)
  证明: by
  simp [Finset.ext_iff]

@[simp]

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff
-/
lemma filter_inj' : s.filter p = s.filter q ↔ forall ⦃a⦄, a in s -> (p a ↔ q a) := by
  simp [Finset.ext_iff]

@[simp]
/--
lemma `filter_mem_eq_of_subset` / 引理 `filter_mem_eq_of_subset`

English:
lemma filter_mem_eq_of_subset
  given: [DecidablePred (· in s)] (hst : s subseteq t)
  proof: by
  grind

中文:
引理 filter_mem_eq_of_subset
  条件: [DecidablePred (· in s)] (hst : s subseteq t)
  证明: by
  grind
-/
lemma filter_mem_eq_of_subset [DecidablePred (· in s)] (hst : s subseteq t) :
    t.filter (· in s) = s := by
  grind

end Filter

end Finset
