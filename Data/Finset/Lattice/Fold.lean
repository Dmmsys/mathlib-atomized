/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Multiset.Lattice
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Nat

/-!
# Lattice operations on finsets

This file is concerned with folding binary lattice operations over finsets.

For the special case of maximum and minimum of a finset, see Max.lean.

See also `Mathlib/Order/CompleteLattice/Finset.lean`, which is instead concerned with how big
lattice or set operations behave when indexed by a finset.
-/

@[expose] public section

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### sup and inf -/


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
@[to_dual /-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/]
/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: (s : Finset β) (f : β -> α)
  body: s.fold (· ⊔ ·) ⊥ f

中文:
定义 sup
  签名: (s : Finset β) (f : β -> α)
  定义体: s.fold (· ⊔ ·) ⊥ f

Depends on / 依赖: s.fold
-/
def sup (s : Finset β) (f : β -> α) : α :=
  s.fold (· ⊔ ·) ⊥ f

variable {s s₁ s₂ : Finset β} {f g : β -> α} {a : α}

@[to_dual]
/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  statement: s.sup f = (s.1.map f).sup
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 sup_def
  结论: s.sup f = (s.1.map f).sup
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `sup_empty` / 定理 `sup_empty`

English:
theorem sup_empty
  statement: (∅ : Finset β).sup f = ⊥
  proof: fold_empty

@[to_dual (attr := simp)]

中文:
定理 sup_empty
  结论: (∅ : Finset β).sup f = ⊥
  证明: fold_empty

@[to_dual (attr := simp)]

Depends on / 依赖: fold_empty
-/
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty

@[to_dual (attr := simp)]
/--
theorem `sup_cons` / 定理 `sup_cons`

English:
theorem sup_cons
  given: {b : β} (h : b ∉ s)
  statement: (cons b s h).sup f = f b ⊔ s.sup f
  proof: fold_cons h

@[to_dual (attr := simp, grind =)]

中文:
定理 sup_cons
  条件: {b : β} (h : b ∉ s)
  结论: (cons b s h).sup f = f b ⊔ s.sup f
  证明: fold_cons h

@[to_dual (attr := simp, grind =)]

Depends on / 依赖: fold_cons
-/
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
  fold_cons h

@[to_dual (attr := simp, grind =)]
/--
theorem `sup_insert` / 定理 `sup_insert`

English:
theorem sup_insert
  given: [DecidableEq β] {b : β}
  statement: (insert b s : Finset β).sup f = f b ⊔ s.sup f
  proof: fold_insert_idem

@[to_dual (attr := simp)]

中文:
定理 sup_insert
  条件: [DecidableEq β] {b : β}
  结论: (insert b s : Finset β).sup f = f b ⊔ s.sup f
  证明: fold_insert_idem

@[to_dual (attr := simp)]

Depends on / 依赖: fold_insert_idem
-/
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b ⊔ s.sup f :=
  fold_insert_idem

@[to_dual (attr := simp)]
/--
theorem `sup_image` / 定理 `sup_image`

English:
theorem sup_image
  given: [DecidableEq β] (s : Finset γ) (f : γ -> β) (g : β -> α)
  proof: fold_image_idem

@[to_dual (attr := simp)]

中文:
定理 sup_image
  条件: [DecidableEq β] (s : Finset γ) (f : γ -> β) (g : β -> α)
  证明: fold_image_idem

@[to_dual (attr := simp)]

Depends on / 依赖: fold_image_idem
-/
theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) (g : β -> α) :
    (s.image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem

@[to_dual (attr := simp)]
/--
theorem `sup_map` / 定理 `sup_map`

English:
theorem sup_map
  given: (s : Finset γ) (f : γ ↪ β) (g : β -> α)
  statement: (s.map f).sup g = s.sup (g ∘ f)
  proof: fold_map

@[to_dual (attr := simp)]

中文:
定理 sup_map
  条件: (s : Finset γ) (f : γ ↪ β) (g : β -> α)
  结论: (s.map f).sup g = s.sup (g ∘ f)
  证明: fold_map

@[to_dual (attr := simp)]

Depends on / 依赖: fold_map
-/
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map

@[to_dual (attr := simp)]
/--
theorem `sup_singleton` / 定理 `sup_singleton`

English:
theorem sup_singleton
  given: {b : β}
  statement: ({b} : Finset β).sup f = f b
  proof: Multiset.sup_singleton

@[to_dual]

中文:
定理 sup_singleton
  条件: {b : β}
  结论: ({b} : Finset β).sup f = f b
  证明: Multiset.sup_singleton

@[to_dual]

Depends on / 依赖: Multiset, Multiset.sup_singleton, sup_singleton
-/
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  Multiset.sup_singleton

@[to_dual]
/--
theorem `sup_sup` / 定理 `sup_sup`

English:
theorem sup_sup
  statement: s.sup (f ⊔ g) = s.sup f ⊔ s.sup g
  proof: by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  | cons _ _ _ ih =>
    rw [sup_cons]; rw [sup_cons]; rw [sup_cons]; rw [ih]
    exact sup_sup_sup_comm _ _ _ _

@[to_dual]

中文:
定理 sup_sup
  结论: s.sup (f ⊔ g) = s.sup f ⊔ s.sup g
  证明: by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  | cons _ _ _ ih =>
    rw [sup_cons]; rw [sup_cons]; rw [sup_cons]; rw [ih]
    exact sup_sup_sup_comm _ _ _ _

@[to_dual]

Depends on / 依赖: Finset, Finset.cons_induction, bot_sup_eq, cons_induction, sup_cons, sup_empty, sup_sup_sup_comm
-/
theorem sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  | cons _ _ _ ih =>
    rw [sup_cons]; rw [sup_cons]; rw [sup_cons]; rw [ih]
    exact sup_sup_sup_comm _ _ _ _

@[to_dual]
/--
theorem `sup_congr` / 定理 `sup_congr`

English:
theorem sup_congr
  given: {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a)
  proof: by
  subst hs
  exact Finset.fold_congr hfg

@[to_dual (attr := simp)]

中文:
定理 sup_congr
  条件: {f g : β -> α} (hs : s₁ = s₂) (hfg : 对任意 a in s₂, f a = g a)
  证明: by
  subst hs
  exact Finset.fold_congr hfg

@[to_dual (attr := simp)]

Depends on / 依赖: Finset, Finset.fold_congr, fold_congr
-/
theorem sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a) :
    s₁.sup f = s₂.sup g := by
  subst hs
  exact Finset.fold_congr hfg

@[to_dual (attr := simp)]
/--
theorem `_root_.map_finset_sup` / 定理 `_root_.map_finset_sup`

English:
theorem _root_.map_finset_sup
  statement: [SemilatticeSup β] [OrderBot β]
  proof: Finset.cons_induction_on s (map_bot f) fun i s _ h => by
    rw [sup_cons]; rw [sup_cons]; rw [map_sup]; rw [h]; rw [Function.comp_apply]

@[to_dual (attr := simp) le_inf_iff]

中文:
定理 _root_.map_finset_sup
  结论: [SemilatticeSup β] [OrderBot β]
  证明: Finset.cons_induction_on s (map_bot f) fun i s _ h => by
    rw [sup_cons]; rw [sup_cons]; rw [map_sup]; rw [h]; rw [Function.comp_apply]

@[to_dual (attr := simp) le_inf_iff]

Depends on / 依赖: Finset, Finset.cons_induction_on, Function, Function.comp_apply, comp_apply, cons_induction_on, map_bot, map_sup, sup_cons
-/
theorem _root_.map_finset_sup [SemilatticeSup β] [OrderBot β]
    [FunLike F α β] [SupBotHomClass F α β]
    (f : F) (s : Finset ι) (g : ι -> α) : f (s.sup g) = s.sup (f ∘ g) :=
  Finset.cons_induction_on s (map_bot f) fun i s _ h => by
    rw [sup_cons]; rw [sup_cons]; rw [map_sup]; rw [h]; rw [Function.comp_apply]

@[to_dual (attr := simp) le_inf_iff]
/--
theorem `sup_le_iff` / 定理 `sup_le_iff`

English:
theorem sup_le_iff
  given: {a : α}
  statement: s.sup f <= a ↔ forall b in s, f b <= a
  proof: by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

@[to_dual le_inf] protected alias ⟨_, sup_le⟩ := Finset.sup_le_iff

@[to_dual le_inf_const]

中文:
定理 sup_le_iff
  条件: {a : α}
  结论: s.sup f <= a ↔ 对任意 b in s, f b <= a
  证明: by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

@[to_dual le_inf] protected alias ⟨_, sup_le⟩ := Finset.sup_le_iff

@[to_dual le_inf_const]
-/
protected theorem sup_le_iff {a : α} : s.sup f <= a ↔ forall b in s, f b <= a := by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

@[to_dual le_inf] protected alias ⟨_, sup_le⟩ := Finset.sup_le_iff

@[to_dual le_inf_const]
/--
theorem `sup_const_le` / 定理 `sup_const_le`

English:
theorem sup_const_le
  statement: (s.sup fun _ => a) <= a
  proof: Finset.sup_le fun _ _ => le_rfl

@[deprecated (since := "2026-03-25")] alias le_inf_const_le := le_inf_const

@[to_dual inf_le]

中文:
定理 sup_const_le
  结论: (s.sup fun _ => a) <= a
  证明: Finset.sup_le fun _ _ => le_rfl

@[deprecated (since := "2026-03-25")] alias le_inf_const_le := le_inf_const

@[to_dual inf_le]

Depends on / 依赖: Finset, Finset.sup_le, le_rfl, sup_le
-/
theorem sup_const_le : (s.sup fun _ => a) <= a :=
  Finset.sup_le fun _ _ => le_rfl

@[deprecated (since := "2026-03-25")] alias le_inf_const_le := le_inf_const

@[to_dual inf_le]
/--
theorem `le_sup` / 定理 `le_sup`

English:
theorem le_sup
  given: {b : β} (hb : b in s)
  statement: f b <= s.sup f
  proof: Finset.sup_le_iff.1 le_rfl _ hb

@[to_dual]

中文:
定理 le_sup
  条件: {b : β} (hb : b in s)
  结论: f b <= s.sup f
  证明: Finset.sup_le_iff.1 le_rfl _ hb

@[to_dual]

Depends on / 依赖: Finset, Finset.sup_le_iff, le_rfl, sup_le_iff
-/
theorem le_sup {b : β} (hb : b in s) : f b <= s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb

@[to_dual]
/--
lemma `isLUB_sup` / 引理 `isLUB_sup`

English:
lemma isLUB_sup
  statement: IsLUB (f '' s) (s.sup f)
  proof: by
  simp +contextual [IsLUB, IsLeast, upperBounds, lowerBounds, le_sup]

@[to_dual]

中文:
引理 isLUB_sup
  结论: IsLUB (f '' s) (s.sup f)
  证明: by
  simp +contextual [IsLUB, IsLeast, upperBounds, lowerBounds, le_sup]

@[to_dual]

Depends on / 依赖: IsLeast, contextual, le_sup, lowerBounds, upperBounds
-/
lemma isLUB_sup : IsLUB (f '' s) (s.sup f) := by
  simp +contextual [IsLUB, IsLeast, upperBounds, lowerBounds, le_sup]

@[to_dual]
/--
lemma `isLUB_sup_id` / 引理 `isLUB_sup_id`

English:
lemma isLUB_sup_id
  given: {s : Finset α}
  statement: IsLUB s (s.sup id)
  proof: by simpa using isLUB_sup (f := id)

@[to_dual inf_le_of_le]

中文:
引理 isLUB_sup_id
  条件: {s : Finset α}
  结论: IsLUB s (s.sup id)
  证明: by simpa using isLUB_sup (f := id)

@[to_dual inf_le_of_le]

Depends on / 依赖: isLUB_sup
-/
lemma isLUB_sup_id {s : Finset α} : IsLUB s (s.sup id) := by simpa using isLUB_sup (f := id)

@[to_dual inf_le_of_le]
/--
theorem `le_sup_of_le` / 定理 `le_sup_of_le`

English:
theorem le_sup_of_le
  given: {b : β} (hb : b in s) (h : a <= f b)
  statement: a <= s.sup f
  proof: h.trans le_sup hb

@[to_dual (attr := grind _=_)]

中文:
定理 le_sup_of_le
  条件: {b : β} (hb : b in s) (h : a <= f b)
  结论: a <= s.sup f
  证明: h.trans le_sup hb

@[to_dual (attr := grind _=_)]

Depends on / 依赖: h.trans, le_sup
-/
theorem le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) : a <= s.sup f := h.trans le_sup hb

@[to_dual (attr := grind _=_)]
/--
theorem `sup_union` / 定理 `sup_union`

English:
theorem sup_union
  given: [DecidableEq β]
  statement: (s₁ union s₂).sup f = s₁.sup f ⊔ s₂.sup f
  proof: eq_of_forall_ge_iff fun c => by simp [or_imp, forall_and]

@[to_dual]

中文:
定理 sup_union
  条件: [DecidableEq β]
  结论: (s₁ union s₂).sup f = s₁.sup f ⊔ s₂.sup f
  证明: eq_of_forall_ge_iff fun c => by simp [or_imp, forall_and]

@[to_dual]

Depends on / 依赖: eq_of_forall_ge_iff, forall_and, or_imp
-/
theorem sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
  eq_of_forall_ge_iff fun c => by simp [or_imp, forall_and]

@[to_dual]
/--
theorem `sup_const` / 定理 `sup_const`

English:
theorem sup_const
  given: {s : Finset β} (h : s.Nonempty) (c : α)
  statement: (s.sup fun _ => c) = c
  proof: eq_of_forall_ge_iff (fun _ => Finset.sup_le_iff.trans h.forall_const)

@[to_dual (attr := simp)]

中文:
定理 sup_const
  条件: {s : Finset β} (h : s.Nonempty) (c : α)
  结论: (s.sup fun _ => c) = c
  证明: eq_of_forall_ge_iff (fun _ => Finset.sup_le_iff.trans h.forall_const)

@[to_dual (attr := simp)]

Depends on / 依赖: Finset, Finset.sup_le_iff.trans, eq_of_forall_ge_iff, forall_const, h.forall_const, sup_le_iff
-/
theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff (fun _ => Finset.sup_le_iff.trans h.forall_const)

@[to_dual (attr := simp)]
/--
theorem `sup_bot` / 定理 `sup_bot`

English:
theorem sup_bot
  given: (s : Finset β)
  statement: (s.sup fun _ => ⊥) = (⊥ : α)
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _

@[to_dual]

中文:
定理 sup_bot
  条件: (s : Finset β)
  结论: (s.sup fun _ => ⊥) = (⊥ : α)
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _

@[to_dual]

Depends on / 依赖: eq_empty_or_nonempty, s.eq_empty_or_nonempty, sup_const, sup_empty
-/
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _

@[to_dual]
/--
theorem `sup_ite` / 定理 `sup_ite`

English:
theorem sup_ite
  given: (p : β -> Prop) [DecidablePred p]
  proof: fold_ite _

@[to_dual (attr := gcongr, grind ←)]

中文:
定理 sup_ite
  条件: (p : β -> 命题) [DecidablePred p]
  证明: fold_ite _

@[to_dual (attr := gcongr, grind ←)]

Depends on / 依赖: fold_ite
-/
theorem sup_ite (p : β -> Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g :=
  fold_ite _

@[to_dual (attr := gcongr, grind ←)]
/--
theorem `sup_mono_fun` / 定理 `sup_mono_fun`

English:
theorem sup_mono_fun
  given: {g : β -> α} (h : forall b in s, f b <= g b)
  statement: s.sup f <= s.sup g
  proof: Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)

@[to_dual (attr := gcongr, grind ←)]

中文:
定理 sup_mono_fun
  条件: {g : β -> α} (h : 对任意 b in s, f b <= g b)
  结论: s.sup f <= s.sup g
  证明: Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)

@[to_dual (attr := gcongr, grind ←)]

Depends on / 依赖: Finset, Finset.sup_le, le_sup, le_trans, sup_le
-/
theorem sup_mono_fun {g : β -> α} (h : forall b in s, f b <= g b) : s.sup f <= s.sup g :=
  Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)

@[to_dual (attr := gcongr, grind ←)]
/--
theorem `sup_mono` / 定理 `sup_mono`

English:
theorem sup_mono
  given: (h : s₁ subseteq s₂)
  statement: s₁.sup f <= s₂.sup f
  proof: Finset.sup_le (fun _ hb => le_sup (h hb))

@[to_dual]

中文:
定理 sup_mono
  条件: (h : s₁ subseteq s₂)
  结论: s₁.sup f <= s₂.sup f
  证明: Finset.sup_le (fun _ hb => le_sup (h hb))

@[to_dual]

Depends on / 依赖: Finset, Finset.sup_le, le_sup, sup_le
-/
theorem sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f :=
  Finset.sup_le (fun _ hb => le_sup (h hb))

@[to_dual]
/--
theorem `sup_comm` / 定理 `sup_comm`

English:
theorem sup_comm
  given: (s : Finset β) (t : Finset γ) (f : β -> γ -> α)
  proof: eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual (attr := simp)]

中文:
定理 sup_comm
  条件: (s : Finset β) (t : Finset γ) (f : β -> γ -> α)
  证明: eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual (attr := simp)]
-/
protected theorem sup_comm (s : Finset β) (t : Finset γ) (f : β -> γ -> α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c :=
  eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual (attr := simp)]
/--
theorem `sup_attach` / 定理 `sup_attach`

English:
theorem sup_attach
  given: (s : Finset β) (f : β -> α)
  statement: (s.attach.sup fun x => f x) = s.sup f
  proof: (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans congr_arg _ attach_map_val

@[to_dual (attr := simp)]

中文:
定理 sup_attach
  条件: (s : Finset β) (f : β -> α)
  结论: (s.attach.sup fun x => f x) = s.sup f
  证明: (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans congr_arg _ attach_map_val

@[to_dual (attr := simp)]

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, attach, attach_map_val, congr_arg, s.attach.sup_map, subtype, sup_map, symm.trans
-/
theorem sup_attach (s : Finset β) (f : β -> α) : (s.attach.sup fun x => f x) = s.sup f :=
(s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans congr_arg _ attach_map_val

@[to_dual (attr := simp)]
/--
theorem `sup_erase_bot` / 定理 `sup_erase_bot`

English:
theorem sup_erase_bot
  given: [DecidableEq α] (s : Finset α)
  statement: (s.erase ⊥).sup id = s.sup id
  proof: by
  refine (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => ?_)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)

中文:
定理 sup_erase_bot
  条件: [DecidableEq α] (s : Finset α)
  结论: (s.erase ⊥).sup id = s.sup id
  证明: by
  refine (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => ?_)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)

Depends on / 依赖: Finset, Finset.sup_le_iff, antisymm, bot_le, eq_or_ne, erase_subset, le_sup, mem_erase, s.erase_subset, sup_le_iff, sup_mono
-/
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id := by
  refine (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => ?_)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)

/--
theorem `sup_sdiff_right` / 定理 `sup_sdiff_right`

English:
theorem sup_sdiff_right
  statement: {α β : Type*} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β -> α)
  proof: by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, bot_sdiff]
  | cons _ _ _ h => rw [sup_cons, sup_cons, h, sup_sdiff]

@[to_dual]

中文:
定理 sup_sdiff_right
  结论: {α β : 类型} [Generalized布尔eanAlgebra α] (s : Finset β) (f : β -> α)
  证明: by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, bot_sdiff]
  | cons _ _ _ h => rw [sup_cons, sup_cons, h, sup_sdiff]

@[to_dual]

Depends on / 依赖: Finset, Finset.cons_induction, bot_sdiff, cons_induction, sup_cons, sup_empty, sup_sdiff
-/
theorem sup_sdiff_right {α β : Type*} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β -> α)
    (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, bot_sdiff]
  | cons _ _ _ h => rw [sup_cons, sup_cons, h, sup_sdiff]

@[to_dual]
/--
theorem `apply_sup_eq_sup_comp` / 定理 `apply_sup_eq_sup_comp`

English:
theorem apply_sup_eq_sup_comp
  statement: [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ)
  proof: Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons]; rw [sup_cons]; rw [g_sup]; rw [ih]; rw [Function.comp_apply]

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp := apply_sup_eq_sup_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp := apply_inf

中文:
定理 apply_sup_eq_sup_comp
  结论: [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ)
  证明: Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons]; rw [sup_cons]; rw [g_sup]; rw [ih]; rw [Function.comp_apply]

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp := apply_sup_eq_sup_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp := apply_inf

Depends on / 依赖: Finset, Finset.cons_induction_on, Function, Function.comp_apply, comp_apply, cons_induction_on, g_sup, sup_cons
-/
theorem apply_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ)
    (g_sup : forall x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons]; rw [sup_cons]; rw [g_sup]; rw [ih]; rw [Function.comp_apply]

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp := apply_sup_eq_sup_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp := apply_inf_eq_inf_comp

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
@[to_dual (rename := Pbot -> Ptop, Psup -> Pinf)
/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/]
/--
theorem `sup_coe` / 定理 `sup_coe`

English:
theorem sup_coe
  statement: {P : α -> Prop} {Pbot : P ⊥} {Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)} (t : Finset β)
  proof: Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.sup f).val = t.sup fun x => ↑(f x) := by
  let := Subtype.semilatticeSup Psup
  let := Subtype.orderBot Pbot
  apply apply_sup_eq_sup_comp Subtype.val <;> intros <;> rfl

@[simp]

中文:
定理 sup_coe
  结论: {P : α -> 命题} {Pbot : P ⊥} {Psup : 对任意 ⦃x y⦄, P x -> P y -> P (x ⊔ y)} (t : Finset β)
  证明: Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.sup f).val = t.sup fun x => ↑(f x) := by
  let := Subtype.semilatticeSup Psup
  let := Subtype.orderBot Pbot
  apply apply_sup_eq_sup_comp Subtype.val <;> intros <;> rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, semilatticeSup
-/
theorem sup_coe {P : α -> Prop} {Pbot : P ⊥} {Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)} (t : Finset β)
    (f : β -> { x : α // P x }) :
    letI := Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.sup f).val = t.sup fun x => ↑(f x) := by
  let := Subtype.semilatticeSup Psup
  let := Subtype.orderBot Pbot
  apply apply_sup_eq_sup_comp Subtype.val <;> intros <;> rfl

@[simp]
/--
theorem `sup_toFinset` / 定理 `sup_toFinset`

English:
theorem sup_toFinset
  given: {α β} [DecidableEq β] (s : Finset α) (f : α -> Multiset β)
  proof: apply_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl

@[to_dual]

中文:
定理 sup_toFinset
  条件: {α β} [DecidableEq β] (s : Finset α) (f : α -> Multiset β)
  证明: apply_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl

@[to_dual]

Depends on / 依赖: Multiset, Multiset.toFinset, apply_sup_eq_sup_comp, toFinset, toFinset_union
-/
theorem sup_toFinset {α β} [DecidableEq β] (s : Finset α) (f : α -> Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  apply_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl

@[to_dual]
/--
theorem `_root_.List.foldr_sup_eq_sup_toFinset` / 定理 `_root_.List.foldr_sup_eq_sup_toFinset`

English:
theorem _root_.List.foldr_sup_eq_sup_toFinset
  given: [DecidableEq α] (l : List α)
  proof: by
  rw [← coe_fold_r]; rw [← Multiset.fold_dedup_idem]; rw [sup_def]; rw [← List.toFinset_coe]; rw [toFinset_val]; rw [Multiset.map_id]
  rfl

中文:
定理 _root_.List.foldr_sup_eq_sup_toFinset
  条件: [DecidableEq α] (l : List α)
  证明: by
  rw [← coe_fold_r]; rw [← Multiset.fold_dedup_idem]; rw [sup_def]; rw [← List.toFinset_coe]; rw [toFinset_val]; rw [Multiset.map_id]
  rfl

Depends on / 依赖: List.toFinset_coe, Multiset, Multiset.fold_dedup_idem, Multiset.map_id, coe_fold_r, fold_dedup_idem, map_id, sup_def, toFinset_coe, toFinset_val
-/
theorem _root_.List.foldr_sup_eq_sup_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊔ ·) ⊥ = l.toFinset.sup id := by
  rw [← coe_fold_r]; rw [← Multiset.fold_dedup_idem]; rw [sup_def]; rw [← List.toFinset_coe]; rw [toFinset_val]; rw [Multiset.map_id]
  rfl

/--
theorem `subset_range_sup_succ` / 定理 `subset_range_sup_succ`

English:
theorem subset_range_sup_succ
  given: (s : Finset Nat)
  statement: s subseteq range (s.sup id).succ
  proof: fun _ hn =>
mem_range.2 Nat.lt_succ_of_le @le_sup _ _ _ _ _ id _ hn

@[to_dual]

中文:
定理 subset_range_sup_succ
  条件: (s : Finset 自然数)
  结论: s subseteq range (s.sup id).succ
  证明: fun _ hn =>
mem_range.2 Nat.lt_succ_of_le @le_sup _ _ _ _ _ id _ hn

@[to_dual]
-/
theorem subset_range_sup_succ (s : Finset Nat) : s subseteq range (s.sup id).succ := fun _ hn =>
mem_range.2 Nat.lt_succ_of_le @le_sup _ _ _ _ _ id _ hn

@[to_dual]
/--
theorem `sup_induction` / 定理 `sup_induction`

English:
theorem sup_induction
  statement: {p : α -> Prop} (hb : p ⊥) (hp : forall a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂))
  proof: by
  induction s using Finset.cons_induction with
  | empty => exact hb
  | cons _ _ _ ih =>
    simp only [sup_cons, forall_mem_cons] at hs ⊢
    exact hp _ hs.1 _ (ih hs.2)

@[to_dual le_inf_of_directed_le]

中文:
定理 sup_induction
  结论: {p : α -> 命题} (hb : p ⊥) (hp : 对任意 a₁, p a₁ -> 对任意 a₂, p a₂ -> p (a₁ ⊔ a₂))
  证明: by
  induction s using Finset.cons_induction with
  | empty => exact hb
  | cons _ _ _ ih =>
    simp only [sup_cons, forall_mem_cons] at hs ⊢
    exact hp _ hs.1 _ (ih hs.2)

@[to_dual le_inf_of_directed_le]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, forall_mem_cons, sup_cons
-/
theorem sup_induction {p : α -> Prop} (hb : p ⊥) (hp : forall a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂))
    (hs : forall b in s, p (f b)) : p (s.sup f) := by
  induction s using Finset.cons_induction with
  | empty => exact hb
  | cons _ _ _ ih =>
    simp only [sup_cons, forall_mem_cons] at hs ⊢
    exact hp _ hs.1 _ (ih hs.2)

@[to_dual le_inf_of_directed_le]
/--
theorem `sup_le_of_le_directed` / 定理 `sup_le_of_le_directed`

English:
theorem sup_le_of_le_directed
  statement: {α : Type*} [SemilatticeSup α] [OrderBot α] (s : Set α)
  proof: by
  classical
    induction t using Finset.induction_on with
    | empty =>
      simpa only [forall_prop_of_true, and_true, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, notMem_empty]
    | insert a r _ ih =>
      intro h
      have incs : (r : Set α) subseteq ↑

中文:
定理 sup_le_of_le_directed
  结论: {α : 类型} [SemilatticeSup α] [OrderBot α] (s : Set α)
  证明: by
  classical
    induction t using Finset.induction_on with
    | empty =>
      simpa only [forall_prop_of_true, and_true, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, notMem_empty]
    | insert a r _ ih =>
      intro h
      have incs : (r : Set α) subseteq ↑

Depends on / 依赖: Finset, Finset.coe_subset, Finset.induction_on, Finset.subset_insert, and_true, bot_le, classical, coe_subset, forall_prop_of_false, forall_prop_of_true, forall_true_iff, induction_on, insert, notMem_empty, not_false_iff, subset_insert, subseteq, sup_empty
-/
theorem sup_le_of_le_directed {α : Type*} [SemilatticeSup α] [OrderBot α] (s : Set α)
    (hs : s.Nonempty) (hdir : DirectedOn (· <= ·) s) (t : Finset α) :
    (forall x in t, exists y in s, x <= y) -> exists x in s, t.sup id <= x := by
  classical
    induction t using Finset.induction_on with
    | empty =>
      simpa only [forall_prop_of_true, and_true, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, notMem_empty]
    | insert a r _ ih =>
      intro h
      have incs : (r : Set α) subseteq ↑(insert a r) := by
        rw [Finset.coe_subset]
        apply Finset.subset_insert
      -- x ∈ s is above the sup of r
obtain ⟨x, ⟨hxs, hsx_sup⟩⟩ := ih fun x hx => h x incs hx
      -- y ∈ s is above a
      obtain ⟨y, hys, hay⟩ := h a (Finset.mem_insert_self a r)
      -- z ∈ s is above x and y
      obtain ⟨z, hzs, ⟨hxz, hyz⟩⟩ := hdir x hxs y hys
      use z, hzs
      rw [sup_insert]; rw [id]; rw [sup_le_iff]
      exact ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩

-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : SubsemilatticeSupBot`
@[to_dual]
/--
theorem `sup_mem` / 定理 `sup_mem`

English:
theorem sup_mem
  statement: (s : Set α) (w₁ : ⊥ in s) (w₂ : forallᵉ (x in s) (y in s), x ⊔ y in s)
  proof: @sup_induction _ _ _ _ _ _ (· in s) w₁ w₂ h

@[to_dual (attr := simp)]

中文:
定理 sup_mem
  结论: (s : Set α) (w₁ : ⊥ in s) (w₂ : 对任意ᵉ (x in s) (y in s), x ⊔ y in s)
  证明: @sup_induction _ _ _ _ _ _ (· in s) w₁ w₂ h

@[to_dual (attr := simp)]

Depends on / 依赖: sup_induction
-/
theorem sup_mem (s : Set α) (w₁ : ⊥ in s) (w₂ : forallᵉ (x in s) (y in s), x ⊔ y in s)
    {ι : Type*} (t : Finset ι) (p : ι -> α) (h : forall i in t, p i in s) : t.sup p in s :=
  @sup_induction _ _ _ _ _ _ (· in s) w₁ w₂ h

@[to_dual (attr := simp)]
/--
theorem `sup_eq_bot_iff` / 定理 `sup_eq_bot_iff`

English:
theorem sup_eq_bot_iff
  given: (f : β -> α) (S : Finset β)
  statement: S.sup f = ⊥ ↔ forall s in S, f s = ⊥
  proof: by
  classical induction S using Finset.induction <;> simp [*]

@[to_additive (attr := simp)]

中文:
定理 sup_eq_bot_iff
  条件: (f : β -> α) (S : Finset β)
  结论: S.sup f = ⊥ ↔ 对任意 s in S, f s = ⊥
  证明: by
  classical induction S using Finset.induction <;> simp [*]

@[to_additive (attr := simp)]
-/
protected theorem sup_eq_bot_iff (f : β -> α) (S : Finset β) : S.sup f = ⊥ ↔ forall s in S, f s = ⊥ := by
  classical induction S using Finset.induction <;> simp [*]

@[to_additive (attr := simp)]
/--
lemma `sup_eq_one` / 引理 `sup_eq_one`

English:
lemma sup_eq_one
  given: [One α] [IsBotOneClass α]
  statement: s.sup f = 1 ↔ forall i in s, f i = 1
  proof: by
  simp [← bot_eq_one]

@[to_dual (attr := simp)]

中文:
引理 sup_eq_one
  条件: [One α] [IsBotOneClass α]
  结论: s.sup f = 1 ↔ 对任意 i in s, f i = 1
  证明: by
  simp [← bot_eq_one]

@[to_dual (attr := simp)]

Depends on / 依赖: bot_eq_one
-/
lemma sup_eq_one [One α] [IsBotOneClass α] : s.sup f = 1 ↔ forall i in s, f i = 1 := by
  simp [← bot_eq_one]

@[to_dual (attr := simp)]
/--
lemma `sup_disjSum` / 引理 `sup_disjSum`

English:
lemma sup_disjSum
  given: (s : Finset β) (t : Finset γ) (f : β oplus γ -> α)
  proof: congr(fold _ $(bot_sup_eq _ |>.symm) _ _).trans (fold_disjSum _ _ _ _ _ _)

@[to_dual (attr := simp)]

中文:
引理 sup_disjSum
  条件: (s : Finset β) (t : Finset γ) (f : β oplus γ -> α)
  证明: congr(fold _ $(bot_sup_eq _ |>.symm) _ _).trans (fold_disjSum _ _ _ _ _ _)

@[to_dual (attr := simp)]

Depends on / 依赖: bot_sup_eq, fold_disjSum
-/
lemma sup_disjSum (s : Finset β) (t : Finset γ) (f : β oplus γ -> α) :
    (s.disjSum t).sup f = (s.sup fun x => f (.inl x)) ⊔ (t.sup fun x => f (.inr x)) :=
  congr(fold _ $(bot_sup_eq _ |>.symm) _ _).trans (fold_disjSum _ _ _ _ _ _)

@[to_dual (attr := simp)]
/--
theorem `sup_eq_bot_of_isEmpty` / 定理 `sup_eq_bot_of_isEmpty`

English:
theorem sup_eq_bot_of_isEmpty
  given: [IsEmpty β] (f : β -> α) (S : Finset β)
  statement: S.sup f = ⊥
  proof: by
  rw [Finset.sup_eq_bot_iff]
exact fun x _ => False.elim IsEmpty.false x

@[to_dual inf_dite_pos_le]

中文:
定理 sup_eq_bot_of_isEmpty
  条件: [IsEmpty β] (f : β -> α) (S : Finset β)
  结论: S.sup f = ⊥
  证明: by
  rw [Finset.sup_eq_bot_iff]
exact fun x _ => False.elim IsEmpty.false x

@[to_dual inf_dite_pos_le]

Depends on / 依赖: False.elim, Finset, Finset.sup_eq_bot_iff, IsEmpty, IsEmpty.false, sup_eq_bot_iff
-/
theorem sup_eq_bot_of_isEmpty [IsEmpty β] (f : β -> α) (S : Finset β) : S.sup f = ⊥ := by
  rw [Finset.sup_eq_bot_iff]
exact fun x _ => False.elim IsEmpty.false x

@[to_dual inf_dite_pos_le]
/--
theorem `le_sup_dite_pos` / 定理 `le_sup_dite_pos`

English:
theorem le_sup_dite_pos
  statement: (p : β -> Prop) [DecidablePred p]
  proof: by
  grind [le_sup_of_le]

@[to_dual inf_dite_neg_le]

中文:
定理 le_sup_dite_pos
  结论: (p : β -> 命题) [DecidablePred p]
  证明: by
  grind [le_sup_of_le]

@[to_dual inf_dite_neg_le]

Depends on / 依赖: le_sup_of_le
-/
theorem le_sup_dite_pos (p : β -> Prop) [DecidablePred p]
    {f : (b : β) -> p b -> α} {g : (b : β) -> ¬p b -> α} {b : β} (h₀ : b in s) (h₁ : p b) :
    f b h₁ <= s.sup fun i => if h : p i then f i h else g i h := by
  grind [le_sup_of_le]

@[to_dual inf_dite_neg_le]
/--
theorem `le_sup_dite_neg` / 定理 `le_sup_dite_neg`

English:
theorem le_sup_dite_neg
  statement: (p : β -> Prop) [DecidablePred p]
  proof: by
  grind [le_sup_of_le]

中文:
定理 le_sup_dite_neg
  结论: (p : β -> 命题) [DecidablePred p]
  证明: by
  grind [le_sup_of_le]

Depends on / 依赖: le_sup_of_le
-/
theorem le_sup_dite_neg (p : β -> Prop) [DecidablePred p]
    {f : (b : β) -> p b -> α} {g : (b : β) -> ¬p b -> α} {b : β} (h₀ : b in s) (h₁ : ¬p b) :
    g b h₁ <= s.sup fun i => if h : p i then f i h else g i h := by
  grind [le_sup_of_le]

end Sup

@[to_dual]
/--
theorem `sup_eq_iSup` / 定理 `sup_eq_iSup`

English:
theorem sup_eq_iSup
  given: [CompleteLattice β] (s : Finset α) (f : α -> β)
  statement: s.sup f = ⨆ a in s, f a
  proof: le_antisymm
    (Finset.sup_le (fun a ha => le_iSup_of_le a <| le_iSup (fun _ => f a) ha))
    (iSup_le fun _ => iSup_le fun ha => le_sup ha)

@[to_dual]

中文:
定理 sup_eq_iSup
  条件: [CompleteLattice β] (s : Finset α) (f : α -> β)
  结论: s.sup f = ⨆ a in s, f a
  证明: le_antisymm
    (Finset.sup_le (fun a ha => le_iSup_of_le a <| le_iSup (fun _ => f a) ha))
    (iSup_le fun _ => iSup_le fun ha => le_sup ha)

@[to_dual]

Depends on / 依赖: Finset, Finset.sup_le, iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_sup, sup_le
-/
theorem sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : α -> β) : s.sup f = ⨆ a in s, f a :=
  le_antisymm
    (Finset.sup_le (fun a ha => le_iSup_of_le a <| le_iSup (fun _ => f a) ha))
    (iSup_le fun _ => iSup_le fun ha => le_sup ha)

@[to_dual]
/--
theorem `sup_id_eq_sSup` / 定理 `sup_id_eq_sSup`

English:
theorem sup_id_eq_sSup
  given: [CompleteLattice α] (s : Finset α)
  statement: s.sup id = sSup s
  proof: by
  simp [sSup_eq_iSup, sup_eq_iSup]

中文:
定理 sup_id_eq_sSup
  条件: [CompleteLattice α] (s : Finset α)
  结论: s.sup id = sSup s
  证明: by
  simp [sSup_eq_iSup, sup_eq_iSup]

Depends on / 依赖: sSup_eq_iSup, sup_eq_iSup
-/
theorem sup_id_eq_sSup [CompleteLattice α] (s : Finset α) : s.sup id = sSup s := by
  simp [sSup_eq_iSup, sup_eq_iSup]

/--
theorem `sup_id_set_eq_sUnion` / 定理 `sup_id_set_eq_sUnion`

English:
theorem sup_id_set_eq_sUnion
  given: (s : Finset (Set α))
  statement: s.sup id = ⋃₀ ↑s
  proof: sup_id_eq_sSup _

中文:
定理 sup_id_set_eq_sUnion
  条件: (s : Finset (Set α))
  结论: s.sup id = ⋃₀ ↑s
  证明: sup_id_eq_sSup _

Depends on / 依赖: sup_id_eq_sSup
-/
theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s :=
  sup_id_eq_sSup _

/--
theorem `inf_id_set_eq_sInter` / 定理 `inf_id_set_eq_sInter`

English:
theorem inf_id_set_eq_sInter
  given: (s : Finset (Set α))
  statement: s.inf id = ⋂₀ ↑s
  proof: inf_id_eq_sInf _

@[simp]

中文:
定理 inf_id_set_eq_sInter
  条件: (s : Finset (Set α))
  结论: s.inf id = ⋂₀ ↑s
  证明: inf_id_eq_sInf _

@[simp]

Depends on / 依赖: inf_id_eq_sInf
-/
theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_sInf _

@[simp]
/--
theorem `sup_set_eq_biUnion` / 定理 `sup_set_eq_biUnion`

English:
theorem sup_set_eq_biUnion
  given: (s : Finset α) (f : α -> Set β)
  statement: s.sup f = ⋃ x in s, f x
  proof: sup_eq_iSup _ _

@[simp]

中文:
定理 sup_set_eq_biUnion
  条件: (s : Finset α) (f : α -> Set β)
  结论: s.sup f = ⋃ x in s, f x
  证明: sup_eq_iSup _ _

@[simp]

Depends on / 依赖: sup_eq_iSup
-/
theorem sup_set_eq_biUnion (s : Finset α) (f : α -> Set β) : s.sup f = ⋃ x in s, f x :=
  sup_eq_iSup _ _

@[simp]
/--
theorem `inf_set_eq_iInter` / 定理 `inf_set_eq_iInter`

English:
theorem inf_set_eq_iInter
  given: (s : Finset α) (f : α -> Set β)
  statement: s.inf f = ⋂ x in s, f x
  proof: inf_eq_iInf _ _

@[to_dual]

中文:
定理 inf_set_eq_iInter
  条件: (s : Finset α) (f : α -> Set β)
  结论: s.inf f = ⋂ x in s, f x
  证明: inf_eq_iInf _ _

@[to_dual]

Depends on / 依赖: inf_eq_iInf
-/
theorem inf_set_eq_iInter (s : Finset α) (f : α -> Set β) : s.inf f = ⋂ x in s, f x :=
  inf_eq_iInf _ _

@[to_dual]
/--
theorem `sup_eq_sSup_image` / 定理 `sup_eq_sSup_image`

English:
theorem sup_eq_sSup_image
  given: [CompleteLattice β] (s : Finset α) (f : α -> β)
  proof: by
  classical rw [← Finset.coe_image, ← sup_id_eq_sSup, sup_image, Function.id_comp]

@[to_dual exists_inf_le]

中文:
定理 sup_eq_sSup_image
  条件: [CompleteLattice β] (s : Finset α) (f : α -> β)
  证明: by
  classical rw [← Finset.coe_image, ← sup_id_eq_sSup, sup_image, Function.id_comp]

@[to_dual exists_inf_le]

Depends on / 依赖: Finset, Finset.coe_image, Function, Function.id_comp, classical, coe_image, id_comp, sup_id_eq_sSup, sup_image
-/
theorem sup_eq_sSup_image [CompleteLattice β] (s : Finset α) (f : α -> β) :
    s.sup f = sSup (f '' s) := by
  classical rw [← Finset.coe_image, ← sup_id_eq_sSup, sup_image, Function.id_comp]

@[to_dual exists_inf_le]
/--
theorem `exists_sup_ge` / 定理 `exists_sup_ge`

English:
theorem exists_sup_ge
  given: [SemilatticeSup β] [OrderBot β] [WellFoundedGT β] (f : α -> β)
  proof: by
  cases isEmpty_or_nonempty α
  · exact ⟨⊥, isEmptyElim⟩
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := wellFounded_gt.has_min _ (Set.range_nonempty (sup · f))
  refine ⟨t, fun a => ?_⟩
  classical
  have := ht (f a ⊔ t.sup f) ⟨insert a t, by simp⟩
  rwa [right_lt_sup, not_not] at this

@[to_dual]

中文:
定理 exists_sup_ge
  条件: [SemilatticeSup β] [OrderBot β] [WellFoundedGT β] (f : α -> β)
  证明: by
  cases isEmpty_or_nonempty α
  · exact ⟨⊥, isEmptyElim⟩
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := wellFounded_gt.has_min _ (Set.range_nonempty (sup · f))
  refine ⟨t, fun a => ?_⟩
  classical
  have := ht (f a ⊔ t.sup f) ⟨insert a t, by simp⟩
  rwa [right_lt_sup, not_not] at this

@[to_dual]

Depends on / 依赖: Set.range_nonempty, classical, has_min, insert, isEmptyElim, isEmpty_or_nonempty, not_not, range_nonempty, right_lt_sup, t.sup, wellFounded_gt, wellFounded_gt.has_min
-/
theorem exists_sup_ge [SemilatticeSup β] [OrderBot β] [WellFoundedGT β] (f : α -> β) :
    exists t : Finset α, forall a, f a <= t.sup f := by
  cases isEmpty_or_nonempty α
  · exact ⟨⊥, isEmptyElim⟩
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := wellFounded_gt.has_min _ (Set.range_nonempty (sup · f))
  refine ⟨t, fun a => ?_⟩
  classical
  have := ht (f a ⊔ t.sup f) ⟨insert a t, by simp⟩
  rwa [right_lt_sup, not_not] at this

@[to_dual]
/--
theorem `exists_sup_eq_iSup` / 定理 `exists_sup_eq_iSup`

English:
theorem exists_sup_eq_iSup
  given: [CompleteLattice β] [WellFoundedGT β] (f : α -> β)
  proof: have ⟨t, ht⟩ := exists_sup_ge f
⟨t, (Finset.sup_le fun _ _ => le_iSup ..).antisymm iSup_le ht⟩

@[to_dual (attr := simp)]

中文:
定理 exists_sup_eq_iSup
  条件: [CompleteLattice β] [WellFoundedGT β] (f : α -> β)
  证明: have ⟨t, ht⟩ := exists_sup_ge f
⟨t, (Finset.sup_le fun _ _ => le_iSup ..).antisymm iSup_le ht⟩

@[to_dual (attr := simp)]

Depends on / 依赖: Finset, Finset.sup_le, antisymm, exists_sup_ge, iSup_le, le_iSup, sup_le
-/
theorem exists_sup_eq_iSup [CompleteLattice β] [WellFoundedGT β] (f : α -> β) :
    exists t : Finset α, t.sup f = ⨆ a, f a :=
  have ⟨t, ht⟩ := exists_sup_ge f
⟨t, (Finset.sup_le fun _ _ => le_iSup ..).antisymm iSup_le ht⟩

@[to_dual (attr := simp)]
/--
theorem `toDual_sup` / 定理 `toDual_sup`

English:
theorem toDual_sup
  given: [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β -> α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_sup
  条件: [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β -> α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β -> α) :
    toDual (s.sup f) = s.inf (toDual ∘ f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_sup` / 定理 `ofDual_sup`

English:
theorem ofDual_sup
  given: [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β -> αᵒᵈ)
  proof: rfl

中文:
定理 ofDual_sup
  条件: [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β -> αᵒᵈ)
  证明: rfl
-/
theorem ofDual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β -> αᵒᵈ) :
    ofDual (s.sup f) = s.inf (ofDual ∘ f) :=
  rfl

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι -> α} {g : κ -> α} {a : α}

@[to_dual]
/--
theorem `sup_inf_distrib_left` / 定理 `sup_inf_distrib_left`

English:
theorem sup_inf_distrib_left
  given: (s : Finset ι) (f : ι -> α) (a : α)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp_rw [Finset.sup_empty, inf_bot_eq]
  | cons _ _ _ h => rw [sup_cons, sup_cons, inf_sup_left, h]

@[to_dual]

中文:
定理 sup_inf_distrib_left
  条件: (s : Finset ι) (f : ι -> α) (a : α)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp_rw [Finset.sup_empty, inf_bot_eq]
  | cons _ _ _ h => rw [sup_cons, sup_cons, inf_sup_left, h]

@[to_dual]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.sup_empty, cons_induction, inf_bot_eq, inf_sup_left, simp_rw, sup_cons, sup_empty
-/
theorem sup_inf_distrib_left (s : Finset ι) (f : ι -> α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i := by
  induction s using Finset.cons_induction with
  | empty => simp_rw [Finset.sup_empty, inf_bot_eq]
  | cons _ _ _ h => rw [sup_cons, sup_cons, inf_sup_left, h]

@[to_dual]
/--
theorem `sup_inf_distrib_right` / 定理 `sup_inf_distrib_right`

English:
theorem sup_inf_distrib_right
  given: (s : Finset ι) (f : ι -> α) (a : α)
  proof: by
  rw [_root_.inf_comm]; rw [s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]

@[to_dual]

中文:
定理 sup_inf_distrib_right
  条件: (s : Finset ι) (f : ι -> α) (a : α)
  证明: by
  rw [_root_.inf_comm]; rw [s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]

@[to_dual]

Depends on / 依赖: _root_, _root_.inf_comm, inf_comm, s.sup_inf_distrib_left, simp_rw, sup_inf_distrib_left
-/
theorem sup_inf_distrib_right (s : Finset ι) (f : ι -> α) (a : α) :
    s.sup f ⊓ a = s.sup fun i => f i ⊓ a := by
  rw [_root_.inf_comm]; rw [s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]

@[to_dual]
/--
theorem `disjoint_sup_right` / 定理 `disjoint_sup_right`

English:
theorem disjoint_sup_right
  statement: Disjoint a (s.sup f) ↔ forall ⦃i⦄, i in s -> Disjoint a (f i)
  proof: by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]

@[to_dual]

中文:
定理 disjoint_sup_right
  结论: Disjoint a (s.sup f) ↔ 对任意 ⦃i⦄, i in s -> Disjoint a (f i)
  证明: by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]

@[to_dual]
-/
protected theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ forall ⦃i⦄, i in s -> Disjoint a (f i) := by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]

@[to_dual]
/--
theorem `disjoint_sup_left` / 定理 `disjoint_sup_left`

English:
theorem disjoint_sup_left
  statement: Disjoint (s.sup f) a ↔ forall ⦃i⦄, i in s -> Disjoint (f i) a
  proof: by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]

中文:
定理 disjoint_sup_left
  结论: Disjoint (s.sup f) a ↔ 对任意 ⦃i⦄, i in s -> Disjoint (f i) a
  证明: by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]
-/
protected theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ forall ⦃i⦄, i in s -> Disjoint (f i) a := by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]

end OrderBot

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra α] {s : Finset ι}

/--
theorem `sup_sdiff_left` / 定理 `sup_sdiff_left`

English:
theorem sup_sdiff_left
  given: (s : Finset ι) (f : ι -> α) (a : α)
  proof: by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, inf_empty, sdiff_top]
  | cons _ _ _ h => rw [sup_cons, inf_cons, h, sdiff_inf]

中文:
定理 sup_sdiff_left
  条件: (s : Finset ι) (f : ι -> α) (a : α)
  证明: by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, inf_empty, sdiff_top]
  | cons _ _ _ h => rw [sup_cons, inf_cons, h, sdiff_inf]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, inf_cons, inf_empty, sdiff_inf, sdiff_top, sup_cons, sup_empty
-/
theorem sup_sdiff_left (s : Finset ι) (f : ι -> α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, inf_empty, sdiff_top]
  | cons _ _ _ h => rw [sup_cons, inf_cons, h, sdiff_inf]

/--
theorem `inf_sdiff_left` / 定理 `inf_sdiff_left`

English:
theorem inf_sdiff_left
  given: (hs : s.Nonempty) (f : ι -> α) (a : α)
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [sup_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [sup_cons, inf_cons, ih, sdiff_sup]

中文:
定理 inf_sdiff_left
  条件: (hs : s.Nonempty) (f : ι -> α) (a : α)
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [sup_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [sup_cons, inf_cons, ih, sdiff_sup]

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, cons_induction, inf_cons, inf_singleton, sdiff_sup, singleton, sup_cons, sup_singleton
-/
theorem inf_sdiff_left (hs : s.Nonempty) (f : ι -> α) (a : α) :
    (s.inf fun b => a \ f b) = a \ s.sup f := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [sup_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [sup_cons, inf_cons, ih, sdiff_sup]

/--
theorem `inf_sdiff_right` / 定理 `inf_sdiff_right`

English:
theorem inf_sdiff_right
  given: (hs : s.Nonempty) (f : ι -> α) (a : α)
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [inf_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [inf_cons, inf_cons, ih, inf_sdiff]

中文:
定理 inf_sdiff_right
  条件: (hs : s.Nonempty) (f : ι -> α) (a : α)
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [inf_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [inf_cons, inf_cons, ih, inf_sdiff]

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, cons_induction, inf_cons, inf_sdiff, inf_singleton, singleton
-/
theorem inf_sdiff_right (hs : s.Nonempty) (f : ι -> α) (a : α) :
    (s.inf fun b => f b \ a) = s.inf f \ a := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [inf_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [inf_cons, inf_cons, ih, inf_sdiff]

/--
theorem `inf_himp_right` / 定理 `inf_himp_right`

English:
theorem inf_himp_right
  given: (s : Finset ι) (f : ι -> α) (a : α)
  proof: @sup_sdiff_left αᵒᵈ _ _ _ _ _

中文:
定理 inf_himp_right
  条件: (s : Finset ι) (f : ι -> α) (a : α)
  证明: @sup_sdiff_left αᵒᵈ _ _ _ _ _

Depends on / 依赖: sup_sdiff_left
-/
theorem inf_himp_right (s : Finset ι) (f : ι -> α) (a : α) :
    (s.inf fun b => f b ⇨ a) = s.sup f ⇨ a :=
  @sup_sdiff_left αᵒᵈ _ _ _ _ _

/--
theorem `sup_himp_right` / 定理 `sup_himp_right`

English:
theorem sup_himp_right
  given: (hs : s.Nonempty) (f : ι -> α) (a : α)
  proof: @inf_sdiff_left αᵒᵈ _ _ _ hs _ _

中文:
定理 sup_himp_right
  条件: (hs : s.Nonempty) (f : ι -> α) (a : α)
  证明: @inf_sdiff_left αᵒᵈ _ _ _ hs _ _

Depends on / 依赖: inf_sdiff_left
-/
theorem sup_himp_right (hs : s.Nonempty) (f : ι -> α) (a : α) :
    (s.sup fun b => f b ⇨ a) = s.inf f ⇨ a :=
  @inf_sdiff_left αᵒᵈ _ _ _ hs _ _

/--
theorem `sup_himp_left` / 定理 `sup_himp_left`

English:
theorem sup_himp_left
  given: (hs : s.Nonempty) (f : ι -> α) (a : α)
  proof: @inf_sdiff_right αᵒᵈ _ _ _ hs _ _

@[simp]

中文:
定理 sup_himp_left
  条件: (hs : s.Nonempty) (f : ι -> α) (a : α)
  证明: @inf_sdiff_right αᵒᵈ _ _ _ hs _ _

@[simp]

Depends on / 依赖: inf_sdiff_right
-/
theorem sup_himp_left (hs : s.Nonempty) (f : ι -> α) (a : α) :
    (s.sup fun b => a ⇨ f b) = a ⇨ s.sup f :=
  @inf_sdiff_right αᵒᵈ _ _ _ hs _ _

@[simp]
/--
theorem `compl_sup` / 定理 `compl_sup`

English:
theorem compl_sup
  given: (s : Finset ι) (f : ι -> α)
  statement: (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ
  proof: map_finset_sup (OrderIso.compl α) _ _

@[simp]

中文:
定理 compl_sup
  条件: (s : Finset ι) (f : ι -> α)
  结论: (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ
  证明: map_finset_sup (OrderIso.compl α) _ _

@[simp]
-/
protected theorem compl_sup (s : Finset ι) (f : ι -> α) : (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ :=
  map_finset_sup (OrderIso.compl α) _ _

@[simp]
/--
theorem `compl_inf` / 定理 `compl_inf`

English:
theorem compl_inf
  given: (s : Finset ι) (f : ι -> α)
  statement: (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ
  proof: map_finset_inf (OrderIso.compl α) _ _

中文:
定理 compl_inf
  条件: (s : Finset ι) (f : ι -> α)
  结论: (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ
  证明: map_finset_inf (OrderIso.compl α) _ _
-/
protected theorem compl_inf (s : Finset ι) (f : ι -> α) : (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ :=
  map_finset_inf (OrderIso.compl α) _ _

end BooleanAlgebra

section LinearOrder

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι -> α} {a : α}

@[to_dual]
/--
theorem `apply_sup_eq_sup_comp_of_linearOrder` / 定理 `apply_sup_eq_sup_comp_of_linearOrder`

English:
theorem apply_sup_eq_sup_comp_of_linearOrder
  statement: [SemilatticeSup β] [OrderBot β] (g : α -> β)
  proof: apply_sup_eq_sup_comp g mono_g.map_sup bot

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp_of_is_total := apply_sup_eq_sup_comp_of_linearOrder

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp_of_is_total := apply_inf_eq_inf_comp_of_linearOrder

@[to_dual (attr := s

中文:
定理 apply_sup_eq_sup_comp_of_linearOrder
  结论: [SemilatticeSup β] [OrderBot β] (g : α -> β)
  证明: apply_sup_eq_sup_comp g mono_g.map_sup bot

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp_of_is_total := apply_sup_eq_sup_comp_of_linearOrder

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp_of_is_total := apply_inf_eq_inf_comp_of_linearOrder

@[to_dual (attr := s

Depends on / 依赖: apply_sup_eq_sup_comp, map_sup, mono_g, mono_g.map_sup
-/
theorem apply_sup_eq_sup_comp_of_linearOrder [SemilatticeSup β] [OrderBot β] (g : α -> β)
    (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  apply_sup_eq_sup_comp g mono_g.map_sup bot

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp_of_is_total := apply_sup_eq_sup_comp_of_linearOrder

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp_of_is_total := apply_inf_eq_inf_comp_of_linearOrder

@[to_dual (attr := simp) inf_le_iff]
/--
theorem `le_sup_iff` / 定理 `le_sup_iff`

English:
theorem le_sup_iff
  given: (ha : ⊥ < a)
  statement: a <= s.sup f ↔ exists b in s, a <= f b
  proof: by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · (not_le_of_gt ha))
    | cons c t hc ih =>
      rw [sup_cons]; rw [le_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hle⟩ := ih h; ⟨b, mem_cons

中文:
定理 le_sup_iff
  条件: (ha : ⊥ < a)
  结论: a <= s.sup f ↔ 存在 b in s, a <= f b
  证明: by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · (not_le_of_gt ha))
    | cons c t hc ih =>
      rw [sup_cons]; rw [le_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hle⟩ := ih h; ⟨b, mem_cons
-/
protected theorem le_sup_iff (ha : ⊥ < a) : a <= s.sup f ↔ exists b in s, a <= f b := by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · (not_le_of_gt ha))
    | cons c t hc ih =>
      rw [sup_cons]; rw [le_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hle⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hle⟩
  · exact fun ⟨b, hb, hle⟩ => le_trans hle (le_sup hb)

@[to_dual]
/--
theorem `sup_eq_top_iff` / 定理 `sup_eq_top_iff`

English:
theorem sup_eq_top_iff
  statement: {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α]
  proof: by
  simp only [← top_le_iff]
  exact Finset.le_sup_iff bot_lt_top

@[to_dual]

中文:
定理 sup_eq_top_iff
  结论: {α : 类型} [LinearOrder α] [BoundedOrder α] [Nontrivial α]
  证明: by
  simp only [← top_le_iff]
  exact Finset.le_sup_iff bot_lt_top

@[to_dual]
-/
protected theorem sup_eq_top_iff {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α]
    {s : Finset ι} {f : ι -> α} : s.sup f = ⊤ ↔ exists b in s, f b = ⊤ := by
  simp only [← top_le_iff]
  exact Finset.le_sup_iff bot_lt_top

@[to_dual]
/--
theorem `Nonempty.sup_eq_top_iff` / 定理 `Nonempty.sup_eq_top_iff`

English:
theorem Nonempty.sup_eq_top_iff
  statement: {α : Type*} [LinearOrder α] [BoundedOrder α]
  proof: by
  cases subsingleton_or_nontrivial α
  · simpa [Subsingleton.elim _ (⊤ : α)]
  · exact Finset.sup_eq_top_iff

@[to_dual (attr := simp) inf_lt_iff]

中文:
定理 Nonempty.sup_eq_top_iff
  结论: {α : 类型} [LinearOrder α] [BoundedOrder α]
  证明: by
  cases subsingleton_or_nontrivial α
  · simpa [Subsingleton.elim _ (⊤ : α)]
  · exact Finset.sup_eq_top_iff

@[to_dual (attr := simp) inf_lt_iff]
-/
protected theorem Nonempty.sup_eq_top_iff {α : Type*} [LinearOrder α] [BoundedOrder α]
    {s : Finset ι} {f : ι -> α} (hs : s.Nonempty) : s.sup f = ⊤ ↔ exists b in s, f b = ⊤ := by
  cases subsingleton_or_nontrivial α
  · simpa [Subsingleton.elim _ (⊤ : α)]
  · exact Finset.sup_eq_top_iff

@[to_dual (attr := simp) inf_lt_iff]
/--
theorem `lt_sup_iff` / 定理 `lt_sup_iff`

English:
theorem lt_sup_iff
  statement: a < s.sup f ↔ exists b in s, a < f b
  proof: by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · not_lt_bot)
    | cons c t hc ih =>
      rw [sup_cons]; rw [lt_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hlt⟩ := ih h; ⟨b, mem_cons.2 (Or.

中文:
定理 lt_sup_iff
  结论: a < s.sup f ↔ 存在 b in s, a < f b
  证明: by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · not_lt_bot)
    | cons c t hc ih =>
      rw [sup_cons]; rw [lt_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hlt⟩ := ih h; ⟨b, mem_cons.2 (Or.
-/
protected theorem lt_sup_iff : a < s.sup f ↔ exists b in s, a < f b := by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · not_lt_bot)
    | cons c t hc ih =>
      rw [sup_cons]; rw [lt_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hlt⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hlt⟩
  · exact fun ⟨b, hb, hlt⟩ => lt_of_lt_of_le hlt (le_sup hb)

@[to_dual (attr := simp) lt_inf_iff]
/--
theorem `sup_lt_iff` / 定理 `sup_lt_iff`

English:
theorem sup_lt_iff
  given: (ha : ⊥ < a)
  statement: s.sup f < a ↔ forall b in s, f b < a
  proof: ⟨fun hs _ hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩

@[to_dual]

中文:
定理 sup_lt_iff
  条件: (ha : ⊥ < a)
  结论: s.sup f < a ↔ 对任意 b in s, f b < a
  证明: ⟨fun hs _ hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩

@[to_dual]
-/
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ forall b in s, f b < a :=
  ⟨fun hs _ hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩

@[to_dual]
/--
theorem `sup_mem_of_nonempty` / 定理 `sup_mem_of_nonempty`

English:
theorem sup_mem_of_nonempty
  given: (hs : s.Nonempty)
  statement: s.sup f in f '' s
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | insert a s _ h =>
    rw [Finset.sup_insert (b := a) (s := s) (f := f)]
    cases s.eq_empty_or_nonempty with
    | inl hs => simp [hs]
    | inr hs =>
      simp only [Finset.coe_in

中文:
定理 sup_mem_of_nonempty
  条件: (hs : s.Nonempty)
  结论: s.sup f in f '' s
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | insert a s _ h =>
    rw [Finset.sup_insert (b := a) (s := s) (f := f)]
    cases s.eq_empty_or_nonempty with
    | inl hs => simp [hs]
    | inr hs =>
      simp only [Finset.coe_in

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction, Finset.not_nonempty_empty, Finset.sup_insert, Set.image_mono, Set.mem_image_of_mem, Set.mem_insert, Set.subset_insert, classical, coe_insert, eq_empty_or_nonempty, image_mono, insert, le_total, mem_image_of_mem, mem_insert, not_nonempty_empty, s.eq_empty_or_nonempty, s.sup
-/
theorem sup_mem_of_nonempty (hs : s.Nonempty) : s.sup f in f '' s := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | insert a s _ h =>
    rw [Finset.sup_insert (b := a) (s := s) (f := f)]
    cases s.eq_empty_or_nonempty with
    | inl hs => simp [hs]
    | inr hs =>
      simp only [Finset.coe_insert]
      rcases le_total (f a) (s.sup f) with (ha | ha)
      · rw [sup_eq_right.mpr ha]
        exact Set.image_mono (Set.subset_insert a s) (h hs)
      · rw [sup_eq_left.mpr ha]
        apply Set.mem_image_of_mem _ (Set.mem_insert a ↑s)

end OrderBot

end LinearOrder

section Sup'

variable [SemilatticeSup α]

@[to_dual]
/--
theorem `sup_of_mem` / 定理 `sup_of_mem`

English:
theorem sup_of_mem
  given: {s : Finset β} (f : β -> α) {b : β} (h : b in s)
  proof: (WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) (f b) rfl).imp fun _ => And.left

中文:
定理 sup_of_mem
  条件: {s : Finset β} (f : β -> α) {b : β} (h : b in s)
  证明: (WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) (f b) rfl).imp fun _ => And.left

Depends on / 依赖: And.left, WithBot, WithBot.le_iff_forall, le_iff_forall, le_sup
-/
theorem sup_of_mem {s : Finset β} (f : β -> α) {b : β} (h : b in s) :
    exists a : α, s.sup ((↑) ∘ f : β -> WithBot α) = ↑a :=
  (WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) (f b) rfl).imp fun _ => And.left

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `Finset.sup` which does not require `s` nonempty. -/
@[to_dual
/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `Finset.inf` which does not require `s` nonempty. -/]
/--
Definition of `sup'` / `sup'` 的定义

English:
definition sup'
  signature: (s : Finset β) (H : s.Nonempty) (f : β -> α)
  body: WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using! H)

中文:
定义 sup'
  签名: (s : Finset β) (H : s.Nonempty) (f : β -> α)
  定义体: WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using! H)
-/
def sup' (s : Finset β) (H : s.Nonempty) (f : β -> α) : α :=
  WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using! H)

variable {s : Finset β} (H : s.Nonempty) (f : β -> α)

@[to_dual (attr := simp)]
/--
theorem `coe_sup'` / 定理 `coe_sup'`

English:
theorem coe_sup'
  statement: ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f)
  proof: by
  rw [sup']; rw [WithBot.coe_unbot]

@[to_dual (attr := simp)]

中文:
定理 coe_sup'
  结论: ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f)
  证明: by
  rw [sup']; rw [WithBot.coe_unbot]

@[to_dual (attr := simp)]

Depends on / 依赖: WithBot, WithBot.coe_unbot, coe_unbot
-/
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f) := by
  rw [sup']; rw [WithBot.coe_unbot]

@[to_dual (attr := simp)]
/--
theorem `sup'_cons` / 定理 `sup'_cons`

English:
theorem sup'_cons
  given: {b : β} {hb : b ∉ s}
  proof: by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]

中文:
定理 sup'_cons
  条件: {b : β} {hb : b ∉ s}
  证明: by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]
-/
theorem sup'_cons {b : β} {hb : b ∉ s} :
    (cons b s hb).sup' (cons_nonempty hb) f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]
/--
theorem `sup'_insert` / 定理 `sup'_insert`

English:
theorem sup'_insert
  given: [DecidableEq β] {b : β}
  proof: by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]

中文:
定理 sup'_insert
  条件: [DecidableEq β] {b : β}
  证明: by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]
-/
theorem sup'_insert [DecidableEq β] {b : β} :
    (insert b s).sup' (insert_nonempty _ _) f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]
/--
theorem `sup'_singleton` / 定理 `sup'_singleton`

English:
theorem sup'_singleton
  given: {b : β}
  statement: ({b} : Finset β).sup' (singleton_nonempty _) f = f b
  proof: rfl

@[to_dual (attr := simp) le_inf'_iff]

中文:
定理 sup'_singleton
  条件: {b : β}
  结论: ({b} : Finset β).sup' (singleton_nonempty _) f = f b
  证明: rfl

@[to_dual (attr := simp) le_inf'_iff]
-/
theorem sup'_singleton {b : β} : ({b} : Finset β).sup' (singleton_nonempty _) f = f b :=
  rfl

@[to_dual (attr := simp) le_inf'_iff]
/--
theorem `sup'_le_iff` / 定理 `sup'_le_iff`

English:
theorem sup'_le_iff
  given: {a : α}
  statement: s.sup' H f <= a ↔ forall b in s, f b <= a
  proof: by
  simp_rw [← @WithBot.coe_le_coe α, coe_sup', Finset.sup_le_iff]; rfl

@[to_dual le_inf'] alias ⟨_, sup'_le⟩ := sup'_le_iff

@[to_dual inf'_le]

中文:
定理 sup'_le_iff
  条件: {a : α}
  结论: s.sup' H f <= a ↔ 对任意 b in s, f b <= a
  证明: by
  simp_rw [← @WithBot.coe_le_coe α, coe_sup', Finset.sup_le_iff]; rfl

@[to_dual le_inf'] alias ⟨_, sup'_le⟩ := sup'_le_iff

@[to_dual inf'_le]
-/
theorem sup'_le_iff {a : α} : s.sup' H f <= a ↔ forall b in s, f b <= a := by
  simp_rw [← @WithBot.coe_le_coe α, coe_sup', Finset.sup_le_iff]; rfl

@[to_dual le_inf'] alias ⟨_, sup'_le⟩ := sup'_le_iff

@[to_dual inf'_le]
/--
theorem `le_sup'` / 定理 `le_sup'`

English:
theorem le_sup'
  given: {b : β} (h : b in s)
  statement: f b <= s.sup' ⟨b, h⟩ f
  proof: (sup'_le_iff ⟨b, h⟩ f).1 le_rfl b h

@[to_dual]

中文:
定理 le_sup'
  条件: {b : β} (h : b in s)
  结论: f b <= s.sup' ⟨b, h⟩ f
  证明: (sup'_le_iff ⟨b, h⟩ f).1 le_rfl b h

@[to_dual]

Depends on / 依赖: _le_iff, le_rfl
-/
theorem le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f :=
  (sup'_le_iff ⟨b, h⟩ f).1 le_rfl b h

@[to_dual]
/--
theorem `isLUB_sup'` / 定理 `isLUB_sup'`

English:
theorem isLUB_sup'
  given: {s : Finset α} (hs : s.Nonempty)
  statement: IsLUB s (sup' s hs id)
  proof: ⟨fun x h => id_eq x ▸ le_sup' id h, fun _ h => Finset.sup'_le hs id h⟩

@[to_dual inf'_le_of_le]

中文:
定理 isLUB_sup'
  条件: {s : Finset α} (hs : s.Nonempty)
  结论: IsLUB s (sup' s hs id)
  证明: ⟨fun x h => id_eq x ▸ le_sup' id h, fun _ h => Finset.sup'_le hs id h⟩

@[to_dual inf'_le_of_le]

Depends on / 依赖: Finset, Finset.sup, id_eq, le_sup
-/
theorem isLUB_sup' {s : Finset α} (hs : s.Nonempty) : IsLUB s (sup' s hs id) :=
  ⟨fun x h => id_eq x ▸ le_sup' id h, fun _ h => Finset.sup'_le hs id h⟩

@[to_dual inf'_le_of_le]
/--
theorem `le_sup'_of_le` / 定理 `le_sup'_of_le`

English:
theorem le_sup'_of_le
  given: {a : α} {b : β} (hb : b in s) (h : a <= f b)
  statement: a <= s.sup' ⟨b, hb⟩ f
  proof: h.trans le_sup' _ hb

@[to_dual]

中文:
定理 le_sup'_of_le
  条件: {a : α} {b : β} (hb : b in s) (h : a <= f b)
  结论: a <= s.sup' ⟨b, hb⟩ f
  证明: h.trans le_sup' _ hb

@[to_dual]
-/
theorem le_sup'_of_le {a : α} {b : β} (hb : b in s) (h : a <= f b) : a <= s.sup' ⟨b, hb⟩ f :=
h.trans le_sup' _ hb

@[to_dual]
/--
lemma `sup'_eq_of_forall` / 引理 `sup'_eq_of_forall`

English:
lemma sup'_eq_of_forall
  given: {a : α} (h : forall b in s, f b = a)
  statement: s.sup' H f = a
  proof: le_antisymm (sup'_le _ _ (fun _ hb => (h _ hb).le))
    (le_sup'_of_le _ H.choose_spec (h _ H.choose_spec).ge)

@[to_dual (attr := simp)]

中文:
引理 sup'_eq_of_forall
  条件: {a : α} (h : 对任意 b in s, f b = a)
  结论: s.sup' H f = a
  证明: le_antisymm (sup'_le _ _ (fun _ hb => (h _ hb).le))
    (le_sup'_of_le _ H.choose_spec (h _ H.choose_spec).ge)

@[to_dual (attr := simp)]
-/
lemma sup'_eq_of_forall {a : α} (h : forall b in s, f b = a) : s.sup' H f = a :=
  le_antisymm (sup'_le _ _ (fun _ hb => (h _ hb).le))
    (le_sup'_of_le _ H.choose_spec (h _ H.choose_spec).ge)

@[to_dual (attr := simp)]
/--
theorem `sup'_const` / 定理 `sup'_const`

English:
theorem sup'_const
  given: (a : α)
  statement: s.sup' H (fun _ => a) = a
  proof: sup'_eq_of_forall H (fun _ => a) fun _ => congrFun rfl

@[to_dual]

中文:
定理 sup'_const
  条件: (a : α)
  结论: s.sup' H (fun _ => a) = a
  证明: sup'_eq_of_forall H (fun _ => a) fun _ => congrFun rfl

@[to_dual]
-/
theorem sup'_const (a : α) : s.sup' H (fun _ => a) = a :=
  sup'_eq_of_forall H (fun _ => a) fun _ => congrFun rfl

@[to_dual]
/--
theorem `sup'_union` / 定理 `sup'_union`

English:
theorem sup'_union
  statement: [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
  proof: eq_of_forall_ge_iff fun a => by simp [or_imp, forall_and]

@[to_dual]

中文:
定理 sup'_union
  结论: [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
  证明: eq_of_forall_ge_iff fun a => by simp [or_imp, forall_and]

@[to_dual]
-/
theorem sup'_union [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (f : β -> α) :
    (s₁ union s₂).sup' (h₁.mono subset_union_left) f = s₁.sup' h₁ f ⊔ s₂.sup' h₂ f :=
  eq_of_forall_ge_iff fun a => by simp [or_imp, forall_and]

@[to_dual]
/--
theorem `sup'_comm` / 定理 `sup'_comm`

English:
theorem sup'_comm
  given: {t : Finset γ} (hs : s.Nonempty) (ht : t.Nonempty) (f : β -> γ -> α)
  proof: eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual]

中文:
定理 sup'_comm
  条件: {t : Finset γ} (hs : s.Nonempty) (ht : t.Nonempty) (f : β -> γ -> α)
  证明: eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual]
-/
protected theorem sup'_comm {t : Finset γ} (hs : s.Nonempty) (ht : t.Nonempty) (f : β -> γ -> α) :
    (s.sup' hs fun b => t.sup' ht (f b)) = t.sup' ht fun c => s.sup' hs fun b => f b c :=
  eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual]
/--
theorem `sup'_induction` / 定理 `sup'_induction`

English:
theorem sup'_induction
  statement: {p : α -> Prop} (hp : forall a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂))
  proof: by
  change @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine sup_induction trivial (fun a₁ h₁ a₂ h₂ => ?_) hs
  match a₁, a₂ with
  | ⊥, _ => rwa [bot_sup_eq]
  | (a₁ : α), ⊥ => rwa [sup_bot_eq]
  | (a₁ : α), (a₂ : α) => exact hp a₁ h₁ a₂ h₂

@[to_dual]

中文:
定理 sup'_induction
  结论: {p : α -> 命题} (hp : 对任意 a₁, p a₁ -> 对任意 a₂, p a₂ -> p (a₁ ⊔ a₂))
  证明: by
  change @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine sup_induction trivial (fun a₁ h₁ a₂ h₂ => ?_) hs
  match a₁, a₂ with
  | ⊥, _ => rwa [bot_sup_eq]
  | (a₁ : α), ⊥ => rwa [sup_bot_eq]
  | (a₁ : α), (a₂ : α) => exact hp a₁ h₁ a₂ h₂

@[to_dual]
-/
theorem sup'_induction {p : α -> Prop} (hp : forall a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂))
    (hs : forall b in s, p (f b)) : p (s.sup' H f) := by
  change @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine sup_induction trivial (fun a₁ h₁ a₂ h₂ => ?_) hs
  match a₁, a₂ with
  | ⊥, _ => rwa [bot_sup_eq]
  | (a₁ : α), ⊥ => rwa [sup_bot_eq]
  | (a₁ : α), (a₂ : α) => exact hp a₁ h₁ a₂ h₂

@[to_dual]
/--
theorem `sup'_mem` / 定理 `sup'_mem`

English:
theorem sup'_mem
  statement: (s : Set α) (w : forallᵉ (x in s) (y in s), x ⊔ y in s) {ι : Type*}
  proof: sup'_induction H p w h

@[to_dual (attr := congr)]

中文:
定理 sup'_mem
  结论: (s : Set α) (w : 对任意ᵉ (x in s) (y in s), x ⊔ y in s) {ι : 类型}
  证明: sup'_induction H p w h

@[to_dual (attr := congr)]
-/
theorem sup'_mem (s : Set α) (w : forallᵉ (x in s) (y in s), x ⊔ y in s) {ι : Type*}
    (t : Finset ι) (H : t.Nonempty) (p : ι -> α) (h : forall i in t, p i in s) : t.sup' H p in s :=
  sup'_induction H p w h

@[to_dual (attr := congr)]
/--
theorem `sup'_congr` / 定理 `sup'_congr`

English:
theorem sup'_congr
  given: {t : Finset β} {f g : β -> α} (h₁ : s = t) (h₂ : forall x in s, f x = g x)
  proof: by
  subst s
  refine eq_of_forall_ge_iff fun c => ?_
  simp +contextual only [sup'_le_iff, h₂]

@[to_dual]

中文:
定理 sup'_congr
  条件: {t : Finset β} {f g : β -> α} (h₁ : s = t) (h₂ : 对任意 x in s, f x = g x)
  证明: by
  subst s
  refine eq_of_forall_ge_iff fun c => ?_
  simp +contextual only [sup'_le_iff, h₂]

@[to_dual]
-/
theorem sup'_congr {t : Finset β} {f g : β -> α} (h₁ : s = t) (h₂ : forall x in s, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  refine eq_of_forall_ge_iff fun c => ?_
  simp +contextual only [sup'_le_iff, h₂]

@[to_dual]
/--
theorem `apply_sup'_eq_sup'_comp` / 定理 `apply_sup'_eq_sup'_comp`

English:
theorem apply_sup'_eq_sup'_comp
  statement: [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β -> α}
  proof: by
  refine H.cons_induction ?_ ?_ <;> intros <;> simp [*]

@[deprecated (since := "2026-05-29")]
alias comp_sup'_eq_sup'_comp := apply_sup'_eq_sup'_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf'_eq_inf'_comp := apply_sup'_eq_sup'_comp

@[to_dual (attr := simp)]

中文:
定理 apply_sup'_eq_sup'_comp
  结论: [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β -> α}
  证明: by
  refine H.cons_induction ?_ ?_ <;> intros <;> simp [*]

@[deprecated (since := "2026-05-29")]
alias comp_sup'_eq_sup'_comp := apply_sup'_eq_sup'_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf'_eq_inf'_comp := apply_sup'_eq_sup'_comp

@[to_dual (attr := simp)]

Depends on / 依赖: H.cons_induction, cons_induction, intros
-/
theorem apply_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β -> α}
    (g : α -> γ) (g_sup : forall x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) := by
  refine H.cons_induction ?_ ?_ <;> intros <;> simp [*]

@[deprecated (since := "2026-05-29")]
alias comp_sup'_eq_sup'_comp := apply_sup'_eq_sup'_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf'_eq_inf'_comp := apply_sup'_eq_sup'_comp

@[to_dual (attr := simp)]
/--
theorem `_root_.map_finset_sup'` / 定理 `_root_.map_finset_sup'`

English:
theorem _root_.map_finset_sup'
  statement: [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
  proof: by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

中文:
定理 _root_.map_finset_sup'
  结论: [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
  证明: by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

Depends on / 依赖: cons_induction, hs.cons_induction, intros
-/
theorem _root_.map_finset_sup' [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : F) {s : Finset ι} (hs) (g : ι -> α) :
    f (s.sup' hs g) = s.sup' hs (f ∘ g) := by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

/-- To rewrite from right to left, use `Finset.sup'_comp_eq_image`. -/
@[to_dual (attr := simp) /-- To rewrite from right to left, use `Finset.inf'_comp_eq_image`. -/]
/--
theorem `sup'_image` / 定理 `sup'_image`

English:
theorem sup'_image
  statement: [DecidableEq β] {s : Finset γ} {f : γ -> β} (hs : (s.image f).Nonempty)
  proof: by
  rw [← WithBot.coe_eq_coe]; simp only [coe_sup', sup_image]; rfl

中文:
定理 sup'_image
  结论: [DecidableEq β] {s : Finset γ} {f : γ -> β} (hs : (s.image f).Nonempty)
  证明: by
  rw [← WithBot.coe_eq_coe]; simp only [coe_sup', sup_image]; rfl
-/
theorem sup'_image [DecidableEq β] {s : Finset γ} {f : γ -> β} (hs : (s.image f).Nonempty)
    (g : β -> α) :
    (s.image f).sup' hs g = s.sup' hs.of_image (g ∘ f) := by
  rw [← WithBot.coe_eq_coe]; simp only [coe_sup', sup_image]; rfl

/-- A version of `Finset.sup'_image` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
@[to_dual /-- A version of `Finset.inf'_image` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/]
/--
lemma `sup'_comp_eq_image` / 引理 `sup'_comp_eq_image`

English:
lemma sup'_comp_eq_image
  given: [DecidableEq β] {s : Finset γ} {f : γ -> β} (hs : s.Nonempty) (g : β -> α)
  proof: .symm sup'_image _ _

中文:
引理 sup'_comp_eq_image
  条件: [DecidableEq β] {s : Finset γ} {f : γ -> β} (hs : s.Nonempty) (g : β -> α)
  证明: .symm sup'_image _ _
-/
lemma sup'_comp_eq_image [DecidableEq β] {s : Finset γ} {f : γ -> β} (hs : s.Nonempty) (g : β -> α) :
    s.sup' hs (g ∘ f) = (s.image f).sup' (hs.image f) g :=
.symm sup'_image _ _

/-- To rewrite from right to left, use `Finset.sup'_comp_eq_map`. -/
@[to_dual (attr := simp) /-- To rewrite from right to left, use `Finset.inf'_comp_eq_map`. -/]
/--
theorem `sup'_map` / 定理 `sup'_map`

English:
theorem sup'_map
  given: {s : Finset γ} {f : γ ↪ β} (g : β -> α) (hs : (s.map f).Nonempty)
  proof: by
  rw [← WithBot.coe_eq_coe]; rw [coe_sup']; rw [sup_map]; rw [coe_sup']
  rfl

中文:
定理 sup'_map
  条件: {s : Finset γ} {f : γ ↪ β} (g : β -> α) (hs : (s.map f).Nonempty)
  证明: by
  rw [← WithBot.coe_eq_coe]; rw [coe_sup']; rw [sup_map]; rw [coe_sup']
  rfl
-/
theorem sup'_map {s : Finset γ} {f : γ ↪ β} (g : β -> α) (hs : (s.map f).Nonempty) :
    (s.map f).sup' hs g = s.sup' (map_nonempty.1 hs) (g ∘ f) := by
  rw [← WithBot.coe_eq_coe]; rw [coe_sup']; rw [sup_map]; rw [coe_sup']
  rfl

/-- A version of `Finset.sup'_map` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
@[to_dual /-- A version of `Finset.inf'_map` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/]
/--
lemma `sup'_comp_eq_map` / 引理 `sup'_comp_eq_map`

English:
lemma sup'_comp_eq_map
  given: {s : Finset γ} {f : γ ↪ β} (g : β -> α) (hs : s.Nonempty)
  proof: .symm sup'_map _ _


@[to_dual (attr := gcongr)]

中文:
引理 sup'_comp_eq_map
  条件: {s : Finset γ} {f : γ ↪ β} (g : β -> α) (hs : s.Nonempty)
  证明: .symm sup'_map _ _


@[to_dual (attr := gcongr)]
-/
lemma sup'_comp_eq_map {s : Finset γ} {f : γ ↪ β} (g : β -> α) (hs : s.Nonempty) :
    s.sup' hs (g ∘ f) = (s.map f).sup' (map_nonempty.2 hs) g :=
.symm sup'_map _ _


@[to_dual (attr := gcongr)]
/--
theorem `sup'_mono` / 定理 `sup'_mono`

English:
theorem sup'_mono
  given: {s₁ s₂ : Finset β} (h : s₁ subseteq s₂) (h₁ : s₁.Nonempty)
  proof: Finset.sup'_le h₁ _ (fun _ hb => le_sup' _ (h hb))

@[to_dual (attr := gcongr)]

中文:
定理 sup'_mono
  条件: {s₁ s₂ : Finset β} (h : s₁ subseteq s₂) (h₁ : s₁.Nonempty)
  证明: Finset.sup'_le h₁ _ (fun _ hb => le_sup' _ (h hb))

@[to_dual (attr := gcongr)]
-/
theorem sup'_mono {s₁ s₂ : Finset β} (h : s₁ subseteq s₂) (h₁ : s₁.Nonempty) :
    s₁.sup' h₁ f <= s₂.sup' (h₁.mono h) f :=
  Finset.sup'_le h₁ _ (fun _ hb => le_sup' _ (h hb))

@[to_dual (attr := gcongr)]
/--
lemma `sup'_mono_fun` / 引理 `sup'_mono_fun`

English:
lemma sup'_mono_fun
  given: {hs : s.Nonempty} {f g : β -> α} (h : forall b in s, f b <= g b)
  proof: sup'_le _ _ fun b hb => (h b hb).trans (le_sup' _ hb)

中文:
引理 sup'_mono_fun
  条件: {hs : s.Nonempty} {f g : β -> α} (h : 对任意 b in s, f b <= g b)
  证明: sup'_le _ _ fun b hb => (h b hb).trans (le_sup' _ hb)
-/
lemma sup'_mono_fun {hs : s.Nonempty} {f g : β -> α} (h : forall b in s, f b <= g b) :
    s.sup' hs f <= s.sup' hs g := sup'_le _ _ fun b hb => (h b hb).trans (le_sup' _ hb)

end Sup'

section Sup

variable [SemilatticeSup α] [OrderBot α] {s : Finset β} {f : β -> α}

@[to_dual]
/--
theorem `sup'_eq_sup` / 定理 `sup'_eq_sup`

English:
theorem sup'_eq_sup
  given: (H : s.Nonempty) (f : β -> α)
  statement: s.sup' H f = s.sup f
  proof: le_antisymm (sup'_le H f fun _ => le_sup) (Finset.sup_le fun _ => le_sup' f)

@[to_additive (attr := simp)]

中文:
定理 sup'_eq_sup
  条件: (H : s.Nonempty) (f : β -> α)
  结论: s.sup' H f = s.sup f
  证明: le_antisymm (sup'_le H f fun _ => le_sup) (Finset.sup_le fun _ => le_sup' f)

@[to_additive (attr := simp)]
-/
theorem sup'_eq_sup (H : s.Nonempty) (f : β -> α) : s.sup' H f = s.sup f :=
  le_antisymm (sup'_le H f fun _ => le_sup) (Finset.sup_le fun _ => le_sup' f)

@[to_additive (attr := simp)]
/--
lemma `sup'_eq_one` / 引理 `sup'_eq_one`

English:
lemma sup'_eq_one
  given: [One α] [IsBotOneClass α] (hs)
  statement: s.sup' hs f = 1 ↔ forall i in s, f i = 1
  proof: by
  simp [sup'_eq_sup]

@[to_dual]

中文:
引理 sup'_eq_one
  条件: [One α] [IsBotOneClass α] (hs)
  结论: s.sup' hs f = 1 ↔ 对任意 i in s, f i = 1
  证明: by
  simp [sup'_eq_sup]

@[to_dual]
-/
lemma sup'_eq_one [One α] [IsBotOneClass α] (hs) : s.sup' hs f = 1 ↔ forall i in s, f i = 1 := by
  simp [sup'_eq_sup]

@[to_dual]
/--
theorem `coe_sup_of_nonempty` / 定理 `coe_sup_of_nonempty`

English:
theorem coe_sup_of_nonempty
  given: (h : s.Nonempty) (f : β -> α)
  proof: by simp only [← sup'_eq_sup h, coe_sup' h]

中文:
定理 coe_sup_of_nonempty
  条件: (h : s.Nonempty) (f : β -> α)
  证明: by simp only [← sup'_eq_sup h, coe_sup' h]

Depends on / 依赖: _eq_sup, coe_sup
-/
theorem coe_sup_of_nonempty (h : s.Nonempty) (f : β -> α) :
    (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f) := by simp only [← sup'_eq_sup h, coe_sup' h]

end Sup

@[to_dual (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  statement: {C : β -> Type*} [forall b : β, SemilatticeSup (C b)]
  proof: apply_sup_eq_sup_comp (fun x : forall b : β, C b => x b) (fun _ _ => rfl) rfl

@[to_dual (attr := simp)]

中文:
定理 sup_apply
  结论: {C : β -> 类型} [对任意 b : β, SemilatticeSup (C b)]
  证明: apply_sup_eq_sup_comp (fun x : forall b : β, C b => x b) (fun _ _ => rfl) rfl

@[to_dual (attr := simp)]
-/
protected theorem sup_apply {C : β -> Type*} [forall b : β, SemilatticeSup (C b)]
    [forall b : β, OrderBot (C b)] (s : Finset α) (f : α -> forall b : β, C b) (b : β) :
    s.sup f b = s.sup fun a => f a b :=
  apply_sup_eq_sup_comp (fun x : forall b : β, C b => x b) (fun _ _ => rfl) rfl

@[to_dual (attr := simp)]
/--
theorem `sup'_apply` / 定理 `sup'_apply`

English:
theorem sup'_apply
  statement: {C : β -> Type*} [forall b : β, SemilatticeSup (C b)]
  proof: apply_sup'_eq_sup'_comp H (fun x : forall b : β, C b => x b) fun _ _ => rfl

@[to_dual (attr := simp)]

中文:
定理 sup'_apply
  结论: {C : β -> 类型} [对任意 b : β, SemilatticeSup (C b)]
  证明: apply_sup'_eq_sup'_comp H (fun x : forall b : β, C b => x b) fun _ _ => rfl

@[to_dual (attr := simp)]
-/
protected theorem sup'_apply {C : β -> Type*} [forall b : β, SemilatticeSup (C b)]
    {s : Finset α} (H : s.Nonempty) (f : α -> forall b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  apply_sup'_eq_sup'_comp H (fun x : forall b : β, C b => x b) fun _ _ => rfl

@[to_dual (attr := simp)]
/--
theorem `toDual_sup'` / 定理 `toDual_sup'`

English:
theorem toDual_sup'
  given: [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> α)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_sup'
  条件: [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> α)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> α) :
    toDual (s.sup' hs f) = s.inf' hs (toDual ∘ f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_sup'` / 定理 `ofDual_sup'`

English:
theorem ofDual_sup'
  given: [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> αᵒᵈ)
  proof: rfl

中文:
定理 ofDual_sup'
  条件: [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> αᵒᵈ)
  证明: rfl
-/
theorem ofDual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (ofDual ∘ f) :=
  rfl

section DistribLattice
variable [DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
  {f : ι -> α} {g : κ -> α} {a : α}

@[to_dual]
/--
theorem `sup'_inf_distrib_left` / 定理 `sup'_inf_distrib_left`

English:
theorem sup'_inf_distrib_left
  given: (f : ι -> α) (a : α)
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih => simp_rw [sup'_cons hs, inf_sup_left, ih]

@[to_dual]

中文:
定理 sup'_inf_distrib_left
  条件: (f : ι -> α) (a : α)
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih => simp_rw [sup'_cons hs, inf_sup_left, ih]

@[to_dual]
-/
theorem sup'_inf_distrib_left (f : ι -> α) (a : α) :
    a ⊓ s.sup' hs f = s.sup' hs fun i => a ⊓ f i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih => simp_rw [sup'_cons hs, inf_sup_left, ih]

@[to_dual]
/--
theorem `sup'_inf_distrib_right` / 定理 `sup'_inf_distrib_right`

English:
theorem sup'_inf_distrib_right
  given: (f : ι -> α) (a : α)
  proof: by
  rw [inf_comm]; rw [sup'_inf_distrib_left]; simp_rw [inf_comm]

中文:
定理 sup'_inf_distrib_right
  条件: (f : ι -> α) (a : α)
  证明: by
  rw [inf_comm]; rw [sup'_inf_distrib_left]; simp_rw [inf_comm]
-/
theorem sup'_inf_distrib_right (f : ι -> α) (a : α) :
    s.sup' hs f ⊓ a = s.sup' hs fun i => f i ⊓ a := by
  rw [inf_comm]; rw [sup'_inf_distrib_left]; simp_rw [inf_comm]

end DistribLattice

section LinearOrder

variable [LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι -> α} {a : α}

@[to_dual]
/--
theorem `apply_sup_eq_sup_comp_of_nonempty` / 定理 `apply_sup_eq_sup_comp_of_nonempty`

English:
theorem apply_sup_eq_sup_comp_of_nonempty
  statement: [OrderBot α] [SemilatticeSup β] [OrderBot β]
  proof: by
  rw [← Finset.sup'_eq_sup H]; rw [← Finset.sup'_eq_sup H]
  exact Finset.apply_sup'_eq_sup'_comp H g (fun x y => Monotone.map_sup mono_g x y)

@[deprecated (since := "2026-03-25")]
alias comp_sup_eq_sup_comp_of_nonempty := apply_sup_eq_sup_comp_of_nonempty

@[to_dual (attr := simp) inf'_le_iff]

中文:
定理 apply_sup_eq_sup_comp_of_nonempty
  结论: [OrderBot α] [SemilatticeSup β] [OrderBot β]
  证明: by
  rw [← Finset.sup'_eq_sup H]; rw [← Finset.sup'_eq_sup H]
  exact Finset.apply_sup'_eq_sup'_comp H g (fun x y => Monotone.map_sup mono_g x y)

@[deprecated (since := "2026-03-25")]
alias comp_sup_eq_sup_comp_of_nonempty := apply_sup_eq_sup_comp_of_nonempty

@[to_dual (attr := simp) inf'_le_iff]

Depends on / 依赖: Finset, Finset.apply_sup, Finset.sup, Monotone, Monotone.map_sup, _comp, _eq_sup, apply_sup, map_sup, mono_g
-/
theorem apply_sup_eq_sup_comp_of_nonempty [OrderBot α] [SemilatticeSup β] [OrderBot β]
    {g : α -> β} (mono_g : Monotone g) (H : s.Nonempty) : g (s.sup f) = s.sup (g ∘ f) := by
  rw [← Finset.sup'_eq_sup H]; rw [← Finset.sup'_eq_sup H]
  exact Finset.apply_sup'_eq_sup'_comp H g (fun x y => Monotone.map_sup mono_g x y)

@[deprecated (since := "2026-03-25")]
alias comp_sup_eq_sup_comp_of_nonempty := apply_sup_eq_sup_comp_of_nonempty

@[to_dual (attr := simp) inf'_le_iff]
/--
theorem `le_sup'_iff` / 定理 `le_sup'_iff`

English:
theorem le_sup'_iff
  statement: a <= s.sup' H f ↔ exists b in s, a <= f b
  proof: by
  rw [← WithBot.coe_le_coe]; rw [coe_sup']; rw [Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_le_coe)

@[to_dual (attr := simp) inf'_lt_iff]

中文:
定理 le_sup'_iff
  结论: a <= s.sup' H f ↔ 存在 b in s, a <= f b
  证明: by
  rw [← WithBot.coe_le_coe]; rw [coe_sup']; rw [Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_le_coe)

@[to_dual (attr := simp) inf'_lt_iff]
-/
theorem le_sup'_iff : a <= s.sup' H f ↔ exists b in s, a <= f b := by
  rw [← WithBot.coe_le_coe]; rw [coe_sup']; rw [Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_le_coe)

@[to_dual (attr := simp) inf'_lt_iff]
/--
theorem `lt_sup'_iff` / 定理 `lt_sup'_iff`

English:
theorem lt_sup'_iff
  statement: a < s.sup' H f ↔ exists b in s, a < f b
  proof: by
  rw [← WithBot.coe_lt_coe]; rw [coe_sup']; rw [Finset.lt_sup_iff]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_lt_coe)

@[to_dual (attr := simp) lt_inf'_iff]

中文:
定理 lt_sup'_iff
  结论: a < s.sup' H f ↔ 存在 b in s, a < f b
  证明: by
  rw [← WithBot.coe_lt_coe]; rw [coe_sup']; rw [Finset.lt_sup_iff]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_lt_coe)

@[to_dual (attr := simp) lt_inf'_iff]

Depends on / 依赖: Finset, Finset.lt_sup_iff, WithBot, WithBot.coe_lt_coe, and_congr_right, coe_lt_coe, coe_sup, exists_congr, lt_sup_iff
-/
theorem lt_sup'_iff : a < s.sup' H f ↔ exists b in s, a < f b := by
  rw [← WithBot.coe_lt_coe]; rw [coe_sup']; rw [Finset.lt_sup_iff]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_lt_coe)

@[to_dual (attr := simp) lt_inf'_iff]
/--
theorem `sup'_lt_iff` / 定理 `sup'_lt_iff`

English:
theorem sup'_lt_iff
  statement: s.sup' H f < a ↔ forall i in s, f i < a
  proof: by
  rw [← WithBot.coe_lt_coe]; rw [coe_sup']; rw [Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact forall₂_congr (fun _ _ => WithBot.coe_lt_coe)

@[to_dual]

中文:
定理 sup'_lt_iff
  结论: s.sup' H f < a ↔ 对任意 i in s, f i < a
  证明: by
  rw [← WithBot.coe_lt_coe]; rw [coe_sup']; rw [Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact forall₂_congr (fun _ _ => WithBot.coe_lt_coe)

@[to_dual]
-/
theorem sup'_lt_iff : s.sup' H f < a ↔ forall i in s, f i < a := by
  rw [← WithBot.coe_lt_coe]; rw [coe_sup']; rw [Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact forall₂_congr (fun _ _ => WithBot.coe_lt_coe)

@[to_dual]
/--
theorem `exists_mem_eq_sup'` / 定理 `exists_mem_eq_sup'`

English:
theorem exists_mem_eq_sup'
  given: (f : ι -> α)
  statement: exists i, i in s ∧ s.sup' H f = f i
  proof: by
  induction H using Finset.Nonempty.cons_induction with
  | singleton c => exact ⟨c, mem_singleton_self c, rfl⟩
  | cons c s hcs hs ih =>
    rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs]; rw [h']
    cases le_total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left

中文:
定理 exists_mem_eq_sup'
  条件: (f : ι -> α)
  结论: 存在 i, i in s ∧ s.sup' H f = f i
  证明: by
  induction H using Finset.Nonempty.cons_induction with
  | singleton c => exact ⟨c, mem_singleton_self c, rfl⟩
  | cons c s hcs hs ih =>
    rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs]; rw [h']
    cases le_total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, Or.inl, Or.inr, _cons, cons_induction, le_total, mem_cons, mem_singleton_self, singleton, sup_eq_left, sup_eq_right
-/
theorem exists_mem_eq_sup' (f : ι -> α) : exists i, i in s ∧ s.sup' H f = f i := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton c => exact ⟨c, mem_singleton_self c, rfl⟩
  | cons c s hcs hs ih =>
    rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs]; rw [h']
    cases le_total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    | inr h => exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩

@[to_dual]
/--
theorem `exists_mem_eq_sup` / 定理 `exists_mem_eq_sup`

English:
theorem exists_mem_eq_sup
  given: [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι -> α)
  proof: sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

中文:
定理 exists_mem_eq_sup
  条件: [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι -> α)
  证明: sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

Depends on / 依赖: _eq_sup, exists_mem_eq_sup
-/
theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι -> α) :
    exists i, i in s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

end LinearOrder

end Finset

namespace Multiset

/--
theorem `map_finset_sup` / 定理 `map_finset_sup`

English:
theorem map_finset_sup
  statement: [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ -> Multiset β)
  proof: Finset.apply_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)

中文:
定理 map_finset_sup
  结论: [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ -> Multiset β)
  证明: Finset.apply_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)

Depends on / 依赖: Finset, Finset.apply_sup_eq_sup_comp, apply_sup_eq_sup_comp, map_union, map_zero
-/
theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ -> Multiset β)
    (g : β -> α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.apply_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)

/--
theorem `count_finset_sup` / 定理 `count_finset_sup`

English:
theorem count_finset_sup
  given: [DecidableEq β] (s : Finset α) (f : α -> Multiset β) (b : β)
  proof: by
  let := Classical.decEq α
  refine s.induction ?_ ?_
  · exact count_zero _
  · intro i s _ ih
    rw [Finset.sup_insert]; rw [sup_eq_union]; rw [count_union]; rw [Finset.sup_insert]; rw [ih]

中文:
定理 count_finset_sup
  条件: [DecidableEq β] (s : Finset α) (f : α -> Multiset β) (b : β)
  证明: by
  let := Classical.decEq α
  refine s.induction ?_ ?_
  · exact count_zero _
  · intro i s _ ih
    rw [Finset.sup_insert]; rw [sup_eq_union]; rw [count_union]; rw [Finset.sup_insert]; rw [ih]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.sup_insert, count_union, count_zero, s.induction, sup_eq_union, sup_insert
-/
theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α -> Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) := by
  let := Classical.decEq α
  refine s.induction ?_ ?_
  · exact count_zero _
  · intro i s _ ih
    rw [Finset.sup_insert]; rw [sup_eq_union]; rw [count_union]; rw [Finset.sup_insert]; rw [ih]

/--
theorem `mem_sup` / 定理 `mem_sup`

English:
theorem mem_sup
  given: {α β} [DecidableEq β] {s : Finset α} {f : α -> Multiset β} {x : β}
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

中文:
定理 mem_sup
  条件: {α β} [DecidableEq β] {s : Finset α} {f : α -> Multiset β} {x : β}
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α -> Multiset β} {x : β} :
    x in s.sup f ↔ exists v in s, x in f v := by
  induction s using Finset.cons_induction <;> simp [*]

end Multiset

namespace Finset
variable [DecidableEq α] {s : Finset ι} {f : ι -> Finset α} {a : α}

/--
lemma `mem_sup'` / 引理 `mem_sup'`

English:
lemma mem_sup'
  given: (hs)
  statement: a in s.sup' hs f ↔ exists i in s, a in f i
  proof: by
  induction hs using Nonempty.cons_induction <;> simp [*]

中文:
引理 mem_sup'
  条件: (hs)
  结论: a in s.sup' hs f ↔ 存在 i in s, a in f i
  证明: by
  induction hs using Nonempty.cons_induction <;> simp [*]
-/
@[simp] lemma mem_sup' (hs) : a in s.sup' hs f ↔ exists i in s, a in f i := by
  induction hs using Nonempty.cons_induction <;> simp [*]

/--
lemma `mem_inf'` / 引理 `mem_inf'`

English:
lemma mem_inf'
  given: (hs)
  statement: a in s.inf' hs f ↔ forall i in s, a in f i
  proof: by
  induction hs using Nonempty.cons_induction <;> simp [*]

中文:
引理 mem_inf'
  条件: (hs)
  结论: a in s.inf' hs f ↔ 对任意 i in s, a in f i
  证明: by
  induction hs using Nonempty.cons_induction <;> simp [*]
-/
@[simp] lemma mem_inf' (hs) : a in s.inf' hs f ↔ forall i in s, a in f i := by
  induction hs using Nonempty.cons_induction <;> simp [*]

/--
lemma `mem_sup` / 引理 `mem_sup`

English:
lemma mem_sup
  statement: a in s.sup f ↔ exists i in s, a in f i
  proof: by
  induction s using cons_induction <;> simp [*]

@[simp]

中文:
引理 mem_sup
  结论: a in s.sup f ↔ 存在 i in s, a in f i
  证明: by
  induction s using cons_induction <;> simp [*]

@[simp]
-/
@[simp] lemma mem_sup : a in s.sup f ↔ exists i in s, a in f i := by
  induction s using cons_induction <;> simp [*]

@[simp]
/--
theorem `sup_singleton_apply` / 定理 `sup_singleton_apply`

English:
theorem sup_singleton_apply
  given: (s : Finset β) (f : β -> α)
  proof: by
  ext a
  rw [mem_sup]; rw [mem_image]
  simp only [mem_singleton, eq_comm]

@[simp]

中文:
定理 sup_singleton_apply
  条件: (s : Finset β) (f : β -> α)
  证明: by
  ext a
  rw [mem_sup]; rw [mem_image]
  simp only [mem_singleton, eq_comm]

@[simp]

Depends on / 依赖: eq_comm, mem_image, mem_singleton, mem_sup
-/
theorem sup_singleton_apply (s : Finset β) (f : β -> α) :
    (s.sup fun b => {f b}) = s.image f := by
  ext a
  rw [mem_sup]; rw [mem_image]
  simp only [mem_singleton, eq_comm]

@[simp]
/--
theorem `sup_singleton_eq_self` / 定理 `sup_singleton_eq_self`

English:
theorem sup_singleton_eq_self
  given: (s : Finset α)
  statement: s.sup singleton = s
  proof: (s.sup_singleton_apply _).trans image_id

中文:
定理 sup_singleton_eq_self
  条件: (s : Finset α)
  结论: s.sup singleton = s
  证明: (s.sup_singleton_apply _).trans image_id

Depends on / 依赖: image_id, s.sup_singleton_apply, sup_singleton_apply
-/
theorem sup_singleton_eq_self (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton_apply _).trans image_id

end Finset
