/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Batteries.Tactic.Congr
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Data.Set.SymmDiff
public import Mathlib.Data.Set.Inclusion

/-!
# Images and preimages of sets

## Main definitions

* `preimage f t : Set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `range f : Set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

## Notation

* `f ⁻¹' t` for `Set.preimage f t`

* `f '' s` for `Set.image f s`

## Tags

set, sets, image, preimage, pre-image, range

-/

public section

assert_not_exists WithTop OrderIso

universe u v

open Function Set

namespace Set

variable {α β γ : Type*} {ι : Sort*}

/-! ### Inverse image -/


section Preimage

variable {f : α -> β} {g : β -> γ}

@[simp]
/--
theorem `preimage_empty` / 定理 `preimage_empty`

English:
theorem preimage_empty
  statement: f ⁻¹' ∅ = ∅
  proof: rfl

中文:
定理 preimage_empty
  结论: f ⁻¹' ∅ = ∅
  证明: rfl
-/
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl

/--
theorem `preimage_congr` / 定理 `preimage_congr`

English:
theorem preimage_congr
  given: {f g : α -> β} {s : Set β} (h : forall x : α, f x = g x)
  statement: f ⁻¹' s = g ⁻¹' s
  proof: by
  congr with x
  simp [h]

@[gcongr]

中文:
定理 preimage_congr
  条件: {f g : α -> β} {s : Set β} (h : 对任意 x : α, f x = g x)
  结论: f ⁻¹' s = g ⁻¹' s
  证明: by
  congr with x
  simp [h]

@[gcongr]
-/
theorem preimage_congr {f g : α -> β} {s : Set β} (h : forall x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s := by
  congr with x
  simp [h]

@[gcongr]
/--
theorem `preimage_mono` / 定理 `preimage_mono`

English:
theorem preimage_mono
  given: {s t : Set β} (h : s subseteq t)
  statement: f ⁻¹' s subseteq f ⁻¹' t
  proof: fun _ hx => h hx

@[simp, mfld_simps]

中文:
定理 preimage_mono
  条件: {s t : Set β} (h : s subseteq t)
  结论: f ⁻¹' s subseteq f ⁻¹' t
  证明: fun _ hx => h hx

@[simp, mfld_simps]
-/
theorem preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹' s subseteq f ⁻¹' t := fun _ hx => h hx

@[simp, mfld_simps]
/--
theorem `preimage_univ` / 定理 `preimage_univ`

English:
theorem preimage_univ
  statement: f ⁻¹' univ = univ
  proof: rfl

中文:
定理 preimage_univ
  结论: f ⁻¹' univ = univ
  证明: rfl
-/
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl

/--
theorem `subset_preimage_univ` / 定理 `subset_preimage_univ`

English:
theorem subset_preimage_univ
  given: {s : Set α}
  statement: s subseteq f ⁻¹' univ
  proof: subset_univ _

@[simp, mfld_simps]

中文:
定理 subset_preimage_univ
  条件: {s : Set α}
  结论: s subseteq f ⁻¹' univ
  证明: subset_univ _

@[simp, mfld_simps]

Depends on / 依赖: subset_univ
-/
theorem subset_preimage_univ {s : Set α} : s subseteq f ⁻¹' univ :=
  subset_univ _

@[simp, mfld_simps]
/--
theorem `preimage_inter` / 定理 `preimage_inter`

English:
theorem preimage_inter
  given: {s t : Set β}
  statement: f ⁻¹' (s inter t) = f ⁻¹' s inter f ⁻¹' t
  proof: rfl

@[simp]

中文:
定理 preimage_inter
  条件: {s t : Set β}
  结论: f ⁻¹' (s inter t) = f ⁻¹' s inter f ⁻¹' t
  证明: rfl

@[simp]
-/
theorem preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f ⁻¹' s inter f ⁻¹' t :=
  rfl

@[simp]
/--
theorem `preimage_union` / 定理 `preimage_union`

English:
theorem preimage_union
  given: {s t : Set β}
  statement: f ⁻¹' (s union t) = f ⁻¹' s union f ⁻¹' t
  proof: rfl

@[simp]

中文:
定理 preimage_union
  条件: {s t : Set β}
  结论: f ⁻¹' (s union t) = f ⁻¹' s union f ⁻¹' t
  证明: rfl

@[simp]
-/
theorem preimage_union {s t : Set β} : f ⁻¹' (s union t) = f ⁻¹' s union f ⁻¹' t :=
  rfl

@[simp]
/--
theorem `preimage_compl` / 定理 `preimage_compl`

English:
theorem preimage_compl
  given: {s : Set β}
  statement: f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
  proof: rfl

@[simp]

中文:
定理 preimage_compl
  条件: {s : Set β}
  结论: f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
  证明: rfl

@[simp]
-/
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl

@[simp]
/--
theorem `preimage_sdiff` / 定理 `preimage_sdiff`

English:
theorem preimage_sdiff
  given: (f : α -> β) (s t : Set β)
  statement: f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t
  proof: rfl

@[deprecated (since := "2026-06-03")] alias preimage_diff := preimage_sdiff

中文:
定理 preimage_sdiff
  条件: (f : α -> β) (s t : Set β)
  结论: f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t
  证明: rfl

@[deprecated (since := "2026-06-03")] alias preimage_diff := preimage_sdiff
-/
theorem preimage_sdiff (f : α -> β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl

@[deprecated (since := "2026-06-03")] alias preimage_diff := preimage_sdiff

open scoped symmDiff in
@[simp]
/--
lemma `preimage_symmDiff` / 引理 `preimage_symmDiff`

English:
lemma preimage_symmDiff
  given: {f : α -> β} (s t : Set β)
  statement: f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t)
  proof: rfl

@[simp]

中文:
引理 preimage_symmDiff
  条件: {f : α -> β} (s t : Set β)
  结论: f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t)
  证明: rfl

@[simp]
-/
lemma preimage_symmDiff {f : α -> β} (s t : Set β) : f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
  rfl

@[simp]
/--
theorem `preimage_ite` / 定理 `preimage_ite`

English:
theorem preimage_ite
  given: (f : α -> β) (s t₁ t₂ : Set β)
  proof: rfl

@[simp]

中文:
定理 preimage_ite
  条件: (f : α -> β) (s t₁ t₂ : Set β)
  证明: rfl

@[simp]
-/
theorem preimage_ite (f : α -> β) (s t₁ t₂ : Set β) :
    f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl

@[simp]
/--
theorem `preimage_ofPred_eq` / 定理 `preimage_ofPred_eq`

English:
theorem preimage_ofPred_eq
  given: {p : α -> Prop} {f : β -> α}
  statement: f ⁻¹' { a | p a } = { a | p (f a) }
  proof: rfl

@[deprecated (since := "2026-07-09")] alias preimage_setOf_eq := preimage_ofPred_eq

@[simp]

中文:
定理 preimage_ofPred_eq
  条件: {p : α -> 命题} {f : β -> α}
  结论: f ⁻¹' { a | p a } = { a | p (f a) }
  证明: rfl

@[deprecated (since := "2026-07-09")] alias preimage_setOf_eq := preimage_ofPred_eq

@[simp]
-/
theorem preimage_ofPred_eq {p : α -> Prop} {f : β -> α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl

@[deprecated (since := "2026-07-09")] alias preimage_setOf_eq := preimage_ofPred_eq

@[simp]
/--
theorem `preimage_id_eq` / 定理 `preimage_id_eq`

English:
theorem preimage_id_eq
  statement: preimage (id : α -> α) = id
  proof: rfl

@[mfld_simps]

中文:
定理 preimage_id_eq
  结论: preimage (id : α -> α) = id
  证明: rfl

@[mfld_simps]
-/
theorem preimage_id_eq : preimage (id : α -> α) = id :=
  rfl

@[mfld_simps]
/--
theorem `preimage_id` / 定理 `preimage_id`

English:
theorem preimage_id
  given: {s : Set α}
  statement: id ⁻¹' s = s
  proof: rfl

@[simp, mfld_simps]

中文:
定理 preimage_id
  条件: {s : Set α}
  结论: id ⁻¹' s = s
  证明: rfl

@[simp, mfld_simps]
-/
theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl

@[simp, mfld_simps]
/--
theorem `preimage_id'` / 定理 `preimage_id'`

English:
theorem preimage_id'
  given: {s : Set α}
  statement: (fun x => x) ⁻¹' s = s
  proof: rfl

@[simp]

中文:
定理 preimage_id'
  条件: {s : Set α}
  结论: (fun x => x) ⁻¹' s = s
  证明: rfl

@[simp]
-/
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl

@[simp]
/--
theorem `preimage_const_of_mem` / 定理 `preimage_const_of_mem`

English:
theorem preimage_const_of_mem
  given: {b : β} {s : Set β} (h : b in s)
  statement: (fun _ : α => b) ⁻¹' s = univ
  proof: eq_univ_of_forall fun _ => h

@[simp]

中文:
定理 preimage_const_of_mem
  条件: {b : β} {s : Set β} (h : b in s)
  结论: (fun _ : α => b) ⁻¹' s = univ
  证明: eq_univ_of_forall fun _ => h

@[simp]

Depends on / 依赖: eq_univ_of_forall
-/
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b in s) : (fun _ : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun _ => h

@[simp]
/--
theorem `preimage_const_of_notMem` / 定理 `preimage_const_of_notMem`

English:
theorem preimage_const_of_notMem
  given: {b : β} {s : Set β} (h : b ∉ s)
  statement: (fun _ : α => b) ⁻¹' s = ∅
  proof: eq_empty_of_subset_empty fun _ hx => h hx

中文:
定理 preimage_const_of_notMem
  条件: {b : β} {s : Set β} (h : b ∉ s)
  结论: (fun _ : α => b) ⁻¹' s = ∅
  证明: eq_empty_of_subset_empty fun _ hx => h hx

Depends on / 依赖: eq_empty_of_subset_empty
-/
theorem preimage_const_of_notMem {b : β} {s : Set β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun _ hx => h hx

/--
theorem `preimage_const` / 定理 `preimage_const`

English:
theorem preimage_const
  given: (b : β) (s : Set β) [Decidable (b in s)]
  proof: by grind

中文:
定理 preimage_const
  条件: (b : β) (s : Set β) [Decidable (b in s)]
  证明: by grind
-/
theorem preimage_const (b : β) (s : Set β) [Decidable (b in s)] :
    (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅ := by grind

/--
lemma `exists_eq_const_of_preimage_singleton` / 引理 `exists_eq_const_of_preimage_singleton`

English:
lemma exists_eq_const_of_preimage_singleton
  statement: [Nonempty β] {f : α -> β}
  proof: by
  rcases em (exists b, f ⁻¹' {b} = univ) with ⟨b, hb⟩ | hf'
  · exact ⟨b, funext fun x => eq_univ_iff_forall.1 hb x⟩
  · have : forall x b, f x != b := fun x b =>
      eq_empty_iff_forall_notMem.1 ((hf b).resolve_right fun h => hf' ⟨b, h⟩) x
    exact ⟨Classical.arbitrary β, funext fun x => absu

中文:
引理 exists_eq_const_of_preimage_singleton
  结论: [Nonempty β] {f : α -> β}
  证明: by
  rcases em (exists b, f ⁻¹' {b} = univ) with ⟨b, hb⟩ | hf'
  · exact ⟨b, funext fun x => eq_univ_iff_forall.1 hb x⟩
  · have : forall x b, f x != b := fun x b =>
      eq_empty_iff_forall_notMem.1 ((hf b).resolve_right fun h => hf' ⟨b, h⟩) x
    exact ⟨Classical.arbitrary β, funext fun x => absu

Depends on / 依赖: Classical, Classical.arbitrary, absurd, arbitrary, eq_empty_iff_forall_notMem, eq_univ_iff_forall, resolve_right
-/
lemma exists_eq_const_of_preimage_singleton [Nonempty β] {f : α -> β}
    (hf : forall b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b} = univ) : exists b, f = const α b := by
  rcases em (exists b, f ⁻¹' {b} = univ) with ⟨b, hb⟩ | hf'
  · exact ⟨b, funext fun x => eq_univ_iff_forall.1 hb x⟩
  · have : forall x b, f x != b := fun x b =>
      eq_empty_iff_forall_notMem.1 ((hf b).resolve_right fun h => hf' ⟨b, h⟩) x
    exact ⟨Classical.arbitrary β, funext fun x => absurd rfl (this x _)⟩

/--
theorem `preimage_comp` / 定理 `preimage_comp`

English:
theorem preimage_comp
  given: {s : Set γ}
  statement: g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹' s
  proof: rfl

中文:
定理 preimage_comp
  条件: {s : Set γ}
  结论: g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹' s
  证明: rfl
-/
theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹' s :=
  rfl

/--
theorem `preimage_comp_eq` / 定理 `preimage_comp_eq`

English:
theorem preimage_comp_eq
  statement: preimage (g ∘ f) = preimage f ∘ preimage g
  proof: rfl

中文:
定理 preimage_comp_eq
  结论: preimage (g ∘ f) = preimage f ∘ preimage g
  证明: rfl
-/
theorem preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g :=
  rfl

/--
theorem `preimage_iterate_eq` / 定理 `preimage_iterate_eq`

English:
theorem preimage_iterate_eq
  given: {f : α -> α} {n : Nat}
  statement: Set.preimage f^[n] = (Set.preimage f)^[n]
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, iterate_succ', preimage_comp_eq, ih]

中文:
定理 preimage_iterate_eq
  条件: {f : α -> α} {n : 自然数}
  结论: Set.preimage f^[n] = (Set.preimage f)^[n]
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, iterate_succ', preimage_comp_eq, ih]

Depends on / 依赖: iterate_succ, preimage_comp_eq
-/
theorem preimage_iterate_eq {f : α -> α} {n : Nat} : Set.preimage f^[n] = (Set.preimage f)^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, iterate_succ', preimage_comp_eq, ih]

/--
theorem `preimage_preimage` / 定理 `preimage_preimage`

English:
theorem preimage_preimage
  given: {g : β -> γ} {f : α -> β} {s : Set γ}
  proof: preimage_comp.symm

中文:
定理 preimage_preimage
  条件: {g : β -> γ} {f : α -> β} {s : Set γ}
  证明: preimage_comp.symm

Depends on / 依赖: preimage_comp, preimage_comp.symm
-/
theorem preimage_preimage {g : β -> γ} {f : α -> β} {s : Set γ} :
    f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm

/--
theorem `eq_preimage_subtype_val_iff` / 定理 `eq_preimage_subtype_val_iff`

English:
theorem eq_preimage_subtype_val_iff
  given: {p : α -> Prop} {s : Set (Subtype p)} {t : Set α}
  proof: by grind

中文:
定理 eq_preimage_subtype_val_iff
  条件: {p : α -> 命题} {s : Set (Subtype p)} {t : Set α}
  证明: by grind
-/
theorem eq_preimage_subtype_val_iff {p : α -> Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ forall (x) (h : p x), (⟨x, h⟩ : Subtype p) in s ↔ x in t := by grind

/--
theorem `nonempty_of_nonempty_preimage` / 定理 `nonempty_of_nonempty_preimage`

English:
theorem nonempty_of_nonempty_preimage
  given: {s : Set β} {f : α -> β} (hf : (f ⁻¹' s).Nonempty)
  proof: let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩

中文:
定理 nonempty_of_nonempty_preimage
  条件: {s : Set β} {f : α -> β} (hf : (f ⁻¹' s).Nonempty)
  证明: let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩
-/
theorem nonempty_of_nonempty_preimage {s : Set β} {f : α -> β} (hf : (f ⁻¹' s).Nonempty) :
    s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩

/--
theorem `nonempty_preimage_iff` / 定理 `nonempty_preimage_iff`

English:
theorem nonempty_preimage_iff
  given: {s : Set β} {f : α -> β}
  proof: by
  simp [Set.Nonempty]

中文:
定理 nonempty_preimage_iff
  条件: {s : Set β} {f : α -> β}
  证明: by
  simp [Set.Nonempty]

Depends on / 依赖: Nonempty, Set.Nonempty
-/
theorem nonempty_preimage_iff {s : Set β} {f : α -> β} :
    (f ⁻¹' s).Nonempty ↔ (s inter range f).Nonempty := by
  simp [Set.Nonempty]

/--
theorem `preimage_singleton_true` / 定理 `preimage_singleton_true`

English:
theorem preimage_singleton_true
  given: (p : α -> Prop)
  statement: p ⁻¹' {True} = {a | p a}
  proof: by ext; simp

中文:
定理 preimage_singleton_true
  条件: (p : α -> 命题)
  结论: p ⁻¹' {True} = {a | p a}
  证明: by ext; simp
-/
@[simp] theorem preimage_singleton_true (p : α -> Prop) : p ⁻¹' {True} = {a | p a} := by ext; simp

/--
theorem `preimage_singleton_false` / 定理 `preimage_singleton_false`

English:
theorem preimage_singleton_false
  given: (p : α -> Prop)
  statement: p ⁻¹' {False} = {a | ¬p a}
  proof: by ext; simp

中文:
定理 preimage_singleton_false
  条件: (p : α -> 命题)
  结论: p ⁻¹' {False} = {a | ¬p a}
  证明: by ext; simp
-/
@[simp] theorem preimage_singleton_false (p : α -> Prop) : p ⁻¹' {False} = {a | ¬p a} := by ext; simp

/--
theorem `preimage_subtype_coe_eq_compl` / 定理 `preimage_subtype_coe_eq_compl`

English:
theorem preimage_subtype_coe_eq_compl
  statement: {s u v : Set α} (hsuv : s subseteq u union v)
  proof: by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_notMem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · grind

中文:
定理 preimage_subtype_coe_eq_compl
  结论: {s u v : Set α} (hsuv : s subseteq u union v)
  证明: by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_notMem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · grind

Depends on / 依赖: eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem.mp, x_in_s, x_in_u, x_in_v
-/
theorem preimage_subtype_coe_eq_compl {s u v : Set α} (hsuv : s subseteq u union v)
    (H : s inter (u inter v) = ∅) : ((↑) : s -> α) ⁻¹' u = ((↑) ⁻¹' v)ᶜ := by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_notMem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · grind

/--
lemma `preimage_subset` / 引理 `preimage_subset`

English:
lemma preimage_subset
  given: {s t} (hs : s subseteq f '' t) (hf : Set.InjOn f (f ⁻¹' s))
  statement: f ⁻¹' s subseteq t
  proof: by
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hs ha
  rwa [hf ha _ hba.symm]
  simpa [hba]

中文:
引理 preimage_subset
  条件: {s t} (hs : s subseteq f '' t) (hf : Set.InjOn f (f ⁻¹' s))
  结论: f ⁻¹' s subseteq t
  证明: by
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hs ha
  rwa [hf ha _ hba.symm]
  simpa [hba]

Depends on / 依赖: hba.symm
-/
lemma preimage_subset {s t} (hs : s subseteq f '' t) (hf : Set.InjOn f (f ⁻¹' s)) : f ⁻¹' s subseteq t := by
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hs ha
  rwa [hf ha _ hba.symm]
  simpa [hba]

end Preimage

/-! ### Image of a set under a function -/


section Image

variable {f : α -> β} {s t : Set α}

/--
theorem `image_eta` / 定理 `image_eta`

English:
theorem image_eta
  given: (f : α -> β)
  statement: f '' s = (fun x => f x) '' s
  proof: rfl

中文:
定理 image_eta
  条件: (f : α -> β)
  结论: f '' s = (fun x => f x) '' s
  证明: rfl
-/
theorem image_eta (f : α -> β) : f '' s = (fun x => f x) '' s :=
  rfl

/--
theorem `_root_.Function.Injective.mem_set_image` / 定理 `_root_.Function.Injective.mem_set_image`

English:
theorem _root_.Function.Injective.mem_set_image
  given: {f : α -> β} (hf : Injective f) {s : Set α} {a : α}
  proof: ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, by grind⟩

中文:
定理 _root_.Function.Injective.mem_set_image
  条件: {f : α -> β} (hf : Injective f) {s : Set α} {a : α}
  证明: ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, by grind⟩
-/
theorem _root_.Function.Injective.mem_set_image {f : α -> β} (hf : Injective f) {s : Set α} {a : α} :
    f a in f '' s ↔ a in s :=
  ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, by grind⟩

/--
lemma `preimage_subset_of_surjOn` / 引理 `preimage_subset_of_surjOn`

English:
lemma preimage_subset_of_surjOn
  given: {t : Set β} (hf : Injective f) (h : SurjOn f s t)
  proof: fun _ hx =>
hf.mem_set_image.1 h hx

中文:
引理 preimage_subset_of_surjOn
  条件: {t : Set β} (hf : Injective f) (h : SurjOn f s t)
  证明: fun _ hx =>
hf.mem_set_image.1 h hx
-/
lemma preimage_subset_of_surjOn {t : Set β} (hf : Injective f) (h : SurjOn f s t) :
    f ⁻¹' t subseteq s := fun _ hx =>
hf.mem_set_image.1 h hx

/--
theorem `forall_mem_image` / 定理 `forall_mem_image`

English:
theorem forall_mem_image
  given: {f : α -> β} {s : Set α} {p : β -> Prop}
  proof: by simp

中文:
定理 forall_mem_image
  条件: {f : α -> β} {s : Set α} {p : β -> 命题}
  证明: by simp
-/
theorem forall_mem_image {f : α -> β} {s : Set α} {p : β -> Prop} :
    (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x) := by simp

/--
theorem `exists_mem_image` / 定理 `exists_mem_image`

English:
theorem exists_mem_image
  given: {f : α -> β} {s : Set α} {p : β -> Prop}
  proof: by simp

@[congr]

中文:
定理 exists_mem_image
  条件: {f : α -> β} {s : Set α} {p : β -> 命题}
  证明: by simp

@[congr]
-/
theorem exists_mem_image {f : α -> β} {s : Set α} {p : β -> Prop} :
    (exists y in f '' s, p y) ↔ exists x in s, p (f x) := by simp

@[congr]
/--
theorem `image_congr` / 定理 `image_congr`

English:
theorem image_congr
  given: {f g : α -> β} {s : Set α} (h : forall a in s, f a = g a)
  statement: f '' s = g '' s
  proof: by
  aesop

中文:
定理 image_congr
  条件: {f g : α -> β} {s : Set α} (h : 对任意 a in s, f a = g a)
  结论: f '' s = g '' s
  证明: by
  aesop
-/
theorem image_congr {f g : α -> β} {s : Set α} (h : forall a in s, f a = g a) : f '' s = g '' s := by
  aesop

/--
theorem `image_congr'` / 定理 `image_congr'`

English:
theorem image_congr'
  given: {f g : α -> β} {s : Set α} (h : forall x : α, f x = g x)
  statement: f '' s = g '' s
  proof: by
  grind

@[gcongr]

中文:
定理 image_congr'
  条件: {f g : α -> β} {s : Set α} (h : 对任意 x : α, f x = g x)
  结论: f '' s = g '' s
  证明: by
  grind

@[gcongr]
-/
theorem image_congr' {f g : α -> β} {s : Set α} (h : forall x : α, f x = g x) : f '' s = g '' s := by
  grind

@[gcongr]
/--
lemma `image_mono` / 引理 `image_mono`

English:
lemma image_mono
  given: (h : s subseteq t)
  statement: f '' s subseteq f '' t
  proof: by grind

中文:
引理 image_mono
  条件: (h : s subseteq t)
  结论: f '' s subseteq f '' t
  证明: by grind
-/
lemma image_mono (h : s subseteq t) : f '' s subseteq f '' t := by grind

/--
lemma `monotone_image` / 引理 `monotone_image`

English:
lemma monotone_image
  statement: Monotone (image f)
  proof: fun _ _ => image_mono

中文:
引理 monotone_image
  结论: Monotone (image f)
  证明: fun _ _ => image_mono

Depends on / 依赖: image_mono
-/
lemma monotone_image : Monotone (image f) := fun _ _ => image_mono

/--
theorem `image_comp` / 定理 `image_comp`

English:
theorem image_comp
  given: (f : β -> γ) (g : α -> β) (a : Set α)
  statement: f ∘ g '' a = f '' g '' a
  proof: by aesop

中文:
定理 image_comp
  条件: (f : β -> γ) (g : α -> β) (a : Set α)
  结论: f ∘ g '' a = f '' g '' a
  证明: by aesop
-/
theorem image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g '' a = f '' g '' a := by aesop

/--
theorem `image_comp_eq` / 定理 `image_comp_eq`

English:
theorem image_comp_eq
  given: {g : β -> γ}
  statement: image (g ∘ f) = image g ∘ image f
  proof: by grind

中文:
定理 image_comp_eq
  条件: {g : β -> γ}
  结论: image (g ∘ f) = image g ∘ image f
  证明: by grind
-/
theorem image_comp_eq {g : β -> γ} : image (g ∘ f) = image g ∘ image f := by grind

/--
theorem `image_comp_image` / 定理 `image_comp_image`

English:
theorem image_comp_image
  given: {g : β -> γ}
  statement: image g ∘ image f = image (g ∘ f)
  proof: by grind

中文:
定理 image_comp_image
  条件: {g : β -> γ}
  结论: image g ∘ image f = image (g ∘ f)
  证明: by grind
-/
theorem image_comp_image {g : β -> γ} : image g ∘ image f = image (g ∘ f) := by grind

/-- A variant of `image_comp`, useful for rewriting -/
@[grind =]
/--
theorem `image_image` / 定理 `image_image`

English:
theorem image_image
  given: (g : β -> γ) (f : α -> β) (s : Set α)
  statement: g '' f '' s = (fun x => g (f x)) '' s
  proof: (image_comp g f s).symm

中文:
定理 image_image
  条件: (g : β -> γ) (f : α -> β) (s : Set α)
  结论: g '' f '' s = (fun x => g (f x)) '' s
  证明: (image_comp g f s).symm

Depends on / 依赖: image_comp
-/
theorem image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '' f '' s = (fun x => g (f x)) '' s :=
  (image_comp g f s).symm

/--
theorem `image_comm` / 定理 `image_comm`

English:
theorem image_comm
  statement: {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ}
  proof: by grind

中文:
定理 image_comm
  结论: {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ}
  证明: by grind
-/
theorem image_comm {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ}
    (h_comm : forall a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').image g' := by grind

/--
theorem `_root_.Function.Semiconj.set_image` / 定理 `_root_.Function.Semiconj.set_image`

English:
theorem _root_.Function.Semiconj.set_image
  statement: {f : α -> β} {ga : α -> α} {gb : β -> β}
  proof: fun _ =>
  image_comm h

中文:
定理 _root_.Function.Semiconj.set_image
  结论: {f : α -> β} {ga : α -> α} {gb : β -> β}
  证明: fun _ =>
  image_comm h
-/
theorem _root_.Function.Semiconj.set_image {f : α -> β} {ga : α -> α} {gb : β -> β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h

/--
theorem `_root_.Function.Commute.set_image` / 定理 `_root_.Function.Commute.set_image`

English:
theorem _root_.Function.Commute.set_image
  given: {f g : α -> α} (h : Function.Commute f g)
  proof: Function.Semiconj.set_image h

中文:
定理 _root_.Function.Commute.set_image
  条件: {f g : α -> α} (h : Function.Commute f g)
  证明: Function.Semiconj.set_image h

Depends on / 依赖: Function, Function.Semiconj.set_image, Semiconj, set_image
-/
theorem _root_.Function.Commute.set_image {f g : α -> α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  Function.Semiconj.set_image h

/--
theorem `image_union` / 定理 `image_union`

English:
theorem image_union
  given: (f : α -> β) (s t : Set α)
  statement: f '' (s union t) = f '' s union f '' t
  proof: by grind

@[simp]

中文:
定理 image_union
  条件: (f : α -> β) (s t : Set α)
  结论: f '' (s union t) = f '' s union f '' t
  证明: by grind

@[simp]
-/
theorem image_union (f : α -> β) (s t : Set α) : f '' (s union t) = f '' s union f '' t := by grind

@[simp]
/--
theorem `image_empty` / 定理 `image_empty`

English:
theorem image_empty
  given: (f : α -> β)
  statement: f '' ∅ = ∅
  proof: by grind

中文:
定理 image_empty
  条件: (f : α -> β)
  结论: f '' ∅ = ∅
  证明: by grind
-/
theorem image_empty (f : α -> β) : f '' ∅ = ∅ := by grind

/--
theorem `image_inter_subset` / 定理 `image_inter_subset`

English:
theorem image_inter_subset
  given: (f : α -> β) (s t : Set α)
  statement: f '' (s inter t) subseteq f '' s inter f '' t
  proof: subset_inter (image_mono inter_subset_left) (image_mono inter_subset_right)

中文:
定理 image_inter_subset
  条件: (f : α -> β) (s t : Set α)
  结论: f '' (s inter t) subseteq f '' s inter f '' t
  证明: subset_inter (image_mono inter_subset_left) (image_mono inter_subset_right)

Depends on / 依赖: image_mono, inter_subset_left, inter_subset_right, subset_inter
-/
theorem image_inter_subset (f : α -> β) (s t : Set α) : f '' (s inter t) subseteq f '' s inter f '' t :=
  subset_inter (image_mono inter_subset_left) (image_mono inter_subset_right)

/--
theorem `image_sdiff_subset` / 定理 `image_sdiff_subset`

English:
theorem image_sdiff_subset
  given: (f : α -> β) (s t : Set α)
  statement: f '' (s \ t) subseteq f '' s inter f '' tᶜ
  proof: image_inter_subset f s tᶜ

@[deprecated (since := "2026-06-03")] alias image_diff_subset := image_sdiff_subset

中文:
定理 image_sdiff_subset
  条件: (f : α -> β) (s t : Set α)
  结论: f '' (s \ t) subseteq f '' s inter f '' tᶜ
  证明: image_inter_subset f s tᶜ

@[deprecated (since := "2026-06-03")] alias image_diff_subset := image_sdiff_subset

Depends on / 依赖: image_inter_subset
-/
theorem image_sdiff_subset (f : α -> β) (s t : Set α) : f '' (s \ t) subseteq f '' s inter f '' tᶜ :=
  image_inter_subset f s tᶜ

@[deprecated (since := "2026-06-03")] alias image_diff_subset := image_sdiff_subset

/--
theorem `image_inter_on` / 定理 `image_inter_on`

English:
theorem image_inter_on
  given: {f : α -> β} {s t : Set α} (h : forall x in t, forall y in s, f x = f y -> x = y)
  proof: (image_inter_subset _ _ _).antisymm
    fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩

中文:
定理 image_inter_on
  条件: {f : α -> β} {s t : Set α} (h : 对任意 x in t, 对任意 y in s, f x = f y -> x = y)
  证明: (image_inter_subset _ _ _).antisymm
    fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩

Depends on / 依赖: antisymm, image_inter_subset
-/
theorem image_inter_on {f : α -> β} {s t : Set α} (h : forall x in t, forall y in s, f x = f y -> x = y) :
    f '' (s inter t) = f '' s inter f '' t :=
  (image_inter_subset _ _ _).antisymm
    fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩

/--
theorem `image_inter` / 定理 `image_inter`

English:
theorem image_inter
  given: {f : α -> β} {s t : Set α} (H : Injective f)
  statement: f '' (s inter t) = f '' s inter f '' t
  proof: image_inter_on fun _ _ _ _ h => H h

中文:
定理 image_inter
  条件: {f : α -> β} {s t : Set α} (H : Injective f)
  结论: f '' (s inter t) = f '' s inter f '' t
  证明: image_inter_on fun _ _ _ _ h => H h

Depends on / 依赖: image_inter_on
-/
theorem image_inter {f : α -> β} {s t : Set α} (H : Injective f) : f '' (s inter t) = f '' s inter f '' t :=
  image_inter_on fun _ _ _ _ h => H h

/--
theorem `image_univ_of_surjective` / 定理 `image_univ_of_surjective`

English:
theorem image_univ_of_surjective
  given: {ι : Type*} {f : ι -> β} (H : Surjective f)
  statement: f '' univ = univ
  proof: eq_univ_of_forall by simpa [image]

@[simp]

中文:
定理 image_univ_of_surjective
  条件: {ι : 类型} {f : ι -> β} (H : Surjective f)
  结论: f '' univ = univ
  证明: eq_univ_of_forall by simpa [image]

@[simp]

Depends on / 依赖: eq_univ_of_forall
-/
theorem image_univ_of_surjective {ι : Type*} {f : ι -> β} (H : Surjective f) : f '' univ = univ :=
eq_univ_of_forall by simpa [image]

@[simp]
/--
theorem `image_singleton` / 定理 `image_singleton`

English:
theorem image_singleton
  given: {f : α -> β} {a : α}
  statement: f '' {a} = {f a}
  proof: by grind

@[simp]

中文:
定理 image_singleton
  条件: {f : α -> β} {a : α}
  结论: f '' {a} = {f a}
  证明: by grind

@[simp]
-/
theorem image_singleton {f : α -> β} {a : α} : f '' {a} = {f a} := by grind

@[simp]
/--
theorem `Nonempty.image_const` / 定理 `Nonempty.image_const`

English:
theorem Nonempty.image_const
  given: {s : Set α} (hs : s.Nonempty) (a : β)
  statement: (fun _ => a) '' s = {a}
  proof: ext fun _ =>
    ⟨fun ⟨_, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun _ hy => ⟨hy, rfl⟩⟩

@[simp, mfld_simps]

中文:
定理 Nonempty.image_const
  条件: {s : Set α} (hs : s.Nonempty) (a : β)
  结论: (fun _ => a) '' s = {a}
  证明: ext fun _ =>
    ⟨fun ⟨_, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun _ hy => ⟨hy, rfl⟩⟩

@[simp, mfld_simps]

Depends on / 依赖: eq_of_mem_singleton, hs.imp, mem_singleton
-/
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) '' s = {a} :=
  ext fun _ =>
    ⟨fun ⟨_, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun _ hy => ⟨hy, rfl⟩⟩

@[simp, mfld_simps]
/--
theorem `image_eq_empty` / 定理 `image_eq_empty`

English:
theorem image_eq_empty
  given: {α β} {f : α -> β} {s : Set α}
  statement: f '' s = ∅ ↔ s = ∅
  proof: by
  simp only [eq_empty_iff_forall_notMem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

@[simp, mfld_simps]

中文:
定理 image_eq_empty
  条件: {α β} {f : α -> β} {s : Set α}
  结论: f '' s = ∅ ↔ s = ∅
  证明: by
  simp only [eq_empty_iff_forall_notMem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

@[simp, mfld_simps]

Depends on / 依赖: eq_empty_iff_forall_notMem
-/
theorem image_eq_empty {α β} {f : α -> β} {s : Set α} : f '' s = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_forall_notMem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

@[simp, mfld_simps]
/--
theorem `empty_eq_image` / 定理 `empty_eq_image`

English:
theorem empty_eq_image
  given: {α β} {f : α -> β} {s : Set α}
  statement: ∅ = f '' s ↔ s = ∅
  proof: by
  rw [eq_comm]; rw [image_eq_empty]

中文:
定理 empty_eq_image
  条件: {α β} {f : α -> β} {s : Set α}
  结论: ∅ = f '' s ↔ s = ∅
  证明: by
  rw [eq_comm]; rw [image_eq_empty]

Depends on / 依赖: eq_comm, image_eq_empty
-/
theorem empty_eq_image {α β} {f : α -> β} {s : Set α} : ∅ = f '' s ↔ s = ∅ := by
  rw [eq_comm]; rw [image_eq_empty]

/--
theorem `preimage_compl_eq_image_compl` / 定理 `preimage_compl_eq_image_compl`

English:
theorem preimage_compl_eq_image_compl
  given: [BooleanAlgebra α] (s : Set α)
  proof: Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun _ hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩

中文:
定理 preimage_compl_eq_image_compl
  条件: [布尔eanAlgebra α] (s : Set α)
  证明: Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun _ hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩

Depends on / 依赖: Exists, Exists.elim, Set.ext, compl_compl, compl_eq_comm, compl_eq_comm.mp, symm.subst
-/
theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (s : Set α) :
    Compl.compl ⁻¹' s = Compl.compl '' s :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun _ hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩

/--
theorem `mem_compl_image` / 定理 `mem_compl_image`

English:
theorem mem_compl_image
  given: [BooleanAlgebra α] (t : α) (s : Set α)
  proof: by
  simp [← preimage_compl_eq_image_compl]

@[simp]

中文:
定理 mem_compl_image
  条件: [布尔eanAlgebra α] (t : α) (s : Set α)
  证明: by
  simp [← preimage_compl_eq_image_compl]

@[simp]

Depends on / 依赖: preimage_compl_eq_image_compl
-/
theorem mem_compl_image [BooleanAlgebra α] (t : α) (s : Set α) :
    t in Compl.compl '' s ↔ tᶜ in s := by
  simp [← preimage_compl_eq_image_compl]

@[simp]
/--
theorem `image_id_eq` / 定理 `image_id_eq`

English:
theorem image_id_eq
  statement: image (id : α -> α) = id
  proof: by ext; simp

中文:
定理 image_id_eq
  结论: image (id : α -> α) = id
  证明: by ext; simp
-/
theorem image_id_eq : image (id : α -> α) = id := by ext; simp

/-- A variant of `image_id` -/
@[simp]
/--
theorem `image_id'` / 定理 `image_id'`

English:
theorem image_id'
  given: (s : Set α)
  statement: (fun x => x) '' s = s
  proof: by
  ext
  simp

中文:
定理 image_id'
  条件: (s : Set α)
  结论: (fun x => x) '' s = s
  证明: by
  ext
  simp
-/
theorem image_id' (s : Set α) : (fun x => x) '' s = s := by
  ext
  simp

/--
theorem `image_id` / 定理 `image_id`

English:
theorem image_id
  given: (s : Set α)
  statement: id '' s = s
  proof: by simp

中文:
定理 image_id
  条件: (s : Set α)
  结论: id '' s = s
  证明: by simp
-/
theorem image_id (s : Set α) : id '' s = s := by simp

/--
lemma `image_iterate_eq` / 引理 `image_iterate_eq`

English:
lemma image_iterate_eq
  given: {f : α -> α} {n : Nat}
  statement: image (f^[n]) = (image f)^[n]
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ', iterate_succ', ← ih, image_comp_eq]

中文:
引理 image_iterate_eq
  条件: {f : α -> α} {n : 自然数}
  结论: image (f^[n]) = (image f)^[n]
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ', iterate_succ', ← ih, image_comp_eq]

Depends on / 依赖: image_comp_eq, iterate_succ
-/
lemma image_iterate_eq {f : α -> α} {n : Nat} : image (f^[n]) = (image f)^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ', iterate_succ', ← ih, image_comp_eq]

/--
theorem `compl_compl_image` / 定理 `compl_compl_image`

English:
theorem compl_compl_image
  given: [BooleanAlgebra α] (s : Set α)
  proof: by
  rw [← image_comp]; rw [compl_comp_compl]; rw [image_id]

中文:
定理 compl_compl_image
  条件: [布尔eanAlgebra α] (s : Set α)
  证明: by
  rw [← image_comp]; rw [compl_comp_compl]; rw [image_id]

Depends on / 依赖: compl_comp_compl, image_comp, image_id
-/
theorem compl_compl_image [BooleanAlgebra α] (s : Set α) :
    Compl.compl '' Compl.compl '' s = s := by
  rw [← image_comp]; rw [compl_comp_compl]; rw [image_id]

/--
theorem `image_insert_eq` / 定理 `image_insert_eq`

English:
theorem image_insert_eq
  given: {f : α -> β} {a : α} {s : Set α}
  proof: by grind

中文:
定理 image_insert_eq
  条件: {f : α -> β} {a : α} {s : Set α}
  证明: by grind
-/
theorem image_insert_eq {f : α -> β} {a : α} {s : Set α} :
    f '' insert a s = insert (f a) (f '' s) := by grind

/--
theorem `image_pair` / 定理 `image_pair`

English:
theorem image_pair
  given: (f : α -> β) (a b : α)
  statement: f '' {a, b} = {f a, f b}
  proof: by grind

中文:
定理 image_pair
  条件: (f : α -> β) (a b : α)
  结论: f '' {a, b} = {f a, f b}
  证明: by grind
-/
theorem image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, f b} := by grind

/--
theorem `_root_.Function.LeftInverse.mem_preimage_iff` / 定理 `_root_.Function.LeftInverse.mem_preimage_iff`

English:
theorem _root_.Function.LeftInverse.mem_preimage_iff
  statement: {f : α -> β} {g : β -> α} (hfg : LeftInverse g f)
  proof: by
  rw [Set.mem_preimage]; rw [hfg x]

中文:
定理 _root_.Function.LeftInverse.mem_preimage_iff
  结论: {f : α -> β} {g : β -> α} (hfg : LeftInverse g f)
  证明: by
  rw [Set.mem_preimage]; rw [hfg x]

Depends on / 依赖: Set.mem_preimage, mem_preimage
-/
theorem _root_.Function.LeftInverse.mem_preimage_iff {f : α -> β} {g : β -> α} (hfg : LeftInverse g f)
    {s : Set α} {x : α} : f x in g ⁻¹' s ↔ x in s := by
  rw [Set.mem_preimage]; rw [hfg x]

/--
theorem `image_subset_preimage_of_inverse` / 定理 `image_subset_preimage_of_inverse`

English:
theorem image_subset_preimage_of_inverse
  given: {f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set α)
  proof: fun _ ⟨_, h, e⟩ => e ▸ I.mem_preimage_iff.mpr h

中文:
定理 image_subset_preimage_of_inverse
  条件: {f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set α)
  证明: fun _ ⟨_, h, e⟩ => e ▸ I.mem_preimage_iff.mpr h

Depends on / 依赖: I.mem_preimage_iff.mpr, mem_preimage_iff
-/
theorem image_subset_preimage_of_inverse {f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set α) :
    f '' s subseteq g ⁻¹' s := fun _ ⟨_, h, e⟩ => e ▸ I.mem_preimage_iff.mpr h

/--
theorem `preimage_subset_image_of_inverse` / 定理 `preimage_subset_image_of_inverse`

English:
theorem preimage_subset_image_of_inverse
  given: {f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set β)
  proof: fun b h => ⟨f b, h, I b⟩

中文:
定理 preimage_subset_image_of_inverse
  条件: {f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set β)
  证明: fun b h => ⟨f b, h, I b⟩
-/
theorem preimage_subset_image_of_inverse {f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set β) :
    f ⁻¹' s subseteq g '' s := fun b h => ⟨f b, h, I b⟩

/--
theorem `range_inter_ssubset_iff_preimage_ssubset` / 定理 `range_inter_ssubset_iff_preimage_ssubset`

English:
theorem range_inter_ssubset_iff_preimage_ssubset
  given: {f : α -> β} {s s' : Set β}
  proof: by
  simp only [Set.ssubset_iff_exists]
  apply and_congr ?_ (by aesop)
  constructor
  all_goals
    intro r x hx
    simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage,
      mem_inter_iff, mem_range, true_and]
    aesop

中文:
定理 range_inter_ssubset_iff_preimage_ssubset
  条件: {f : α -> β} {s s' : Set β}
  证明: by
  simp only [Set.ssubset_iff_exists]
  apply and_congr ?_ (by aesop)
  constructor
  all_goals
    intro r x hx
    simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage,
      mem_inter_iff, mem_range, true_and]
    aesop

Depends on / 依赖: Set.ssubset_iff_exists, all_goals, and_congr, inter_subset_left, mem_inter_iff, mem_preimage, mem_range, ssubset_iff_exists, subset_inter_iff, true_and
-/
theorem range_inter_ssubset_iff_preimage_ssubset {f : α -> β} {s s' : Set β} :
    range f inter s ⊂ range f inter s' ↔ f ⁻¹' s ⊂ f ⁻¹' s' := by
  simp only [Set.ssubset_iff_exists]
  apply and_congr ?_ (by aesop)
  constructor
  all_goals
    intro r x hx
    simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage,
      mem_inter_iff, mem_range, true_and]
    aesop

/--
theorem `image_eq_preimage_of_inverse` / 定理 `image_eq_preimage_of_inverse`

English:
theorem image_eq_preimage_of_inverse
  statement: {f : α -> β} {g : β -> α} (h₁ : LeftInverse g f)
  proof: funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)

中文:
定理 image_eq_preimage_of_inverse
  结论: {f : α -> β} {g : β -> α} (h₁ : LeftInverse g f)
  证明: funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, image_subset_preimage_of_inverse, preimage_subset_image_of_inverse
-/
theorem image_eq_preimage_of_inverse {f : α -> β} {g : β -> α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : image f = preimage g :=
  funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)

/--
theorem `_root_.Function.Involutive.image_eq_preimage_symm` / 定理 `_root_.Function.Involutive.image_eq_preimage_symm`

English:
theorem _root_.Function.Involutive.image_eq_preimage_symm
  given: {f : α -> α} (hf : f.Involutive)
  proof: image_eq_preimage_of_inverse hf.leftInverse hf.rightInverse

中文:
定理 _root_.Function.Involutive.image_eq_preimage_symm
  条件: {f : α -> α} (hf : f.Involutive)
  证明: image_eq_preimage_of_inverse hf.leftInverse hf.rightInverse

Depends on / 依赖: hf.leftInverse, hf.rightInverse, image_eq_preimage_of_inverse, leftInverse, rightInverse
-/
theorem _root_.Function.Involutive.image_eq_preimage_symm {f : α -> α} (hf : f.Involutive) :
    image f = preimage f :=
  image_eq_preimage_of_inverse hf.leftInverse hf.rightInverse

/--
theorem `mem_image_iff_of_inverse` / 定理 `mem_image_iff_of_inverse`

English:
theorem mem_image_iff_of_inverse
  statement: {f : α -> β} {g : β -> α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
  proof: by
  rw [image_eq_preimage_of_inverse h₁ h₂]; rw [mem_preimage]

中文:
定理 mem_image_iff_of_inverse
  结论: {f : α -> β} {g : β -> α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
  证明: by
  rw [image_eq_preimage_of_inverse h₁ h₂]; rw [mem_preimage]

Depends on / 依赖: image_eq_preimage_of_inverse, mem_preimage
-/
theorem mem_image_iff_of_inverse {f : α -> β} {g : β -> α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b in f '' s ↔ g b in s := by
  rw [image_eq_preimage_of_inverse h₁ h₂]; rw [mem_preimage]

/--
theorem `image_compl_subset` / 定理 `image_compl_subset`

English:
theorem image_compl_subset
  given: {f : α -> β} {s : Set α} (H : Injective f)
  statement: f '' sᶜ subseteq (f '' s)ᶜ
  proof: Disjoint.subset_compl_left by simp [disjoint_iff_inf_le, ← image_inter H]

中文:
定理 image_compl_subset
  条件: {f : α -> β} {s : Set α} (H : Injective f)
  结论: f '' sᶜ subseteq (f '' s)ᶜ
  证明: Disjoint.subset_compl_left by simp [disjoint_iff_inf_le, ← image_inter H]

Depends on / 依赖: Disjoint, Disjoint.subset_compl_left, disjoint_iff_inf_le, image_inter, subset_compl_left
-/
theorem image_compl_subset {f : α -> β} {s : Set α} (H : Injective f) : f '' sᶜ subseteq (f '' s)ᶜ :=
Disjoint.subset_compl_left by simp [disjoint_iff_inf_le, ← image_inter H]

/--
theorem `subset_image_compl` / 定理 `subset_image_compl`

English:
theorem subset_image_compl
  given: {f : α -> β} {s : Set α} (H : Surjective f)
  statement: (f '' s)ᶜ subseteq f '' sᶜ
  proof: compl_subset_iff_union.2 by
    rw [← image_union]
    simp [image_univ_of_surjective H]

中文:
定理 subset_image_compl
  条件: {f : α -> β} {s : Set α} (H : Surjective f)
  结论: (f '' s)ᶜ subseteq f '' sᶜ
  证明: compl_subset_iff_union.2 by
    rw [← image_union]
    simp [image_univ_of_surjective H]

Depends on / 依赖: compl_subset_iff_union, image_union, image_univ_of_surjective
-/
theorem subset_image_compl {f : α -> β} {s : Set α} (H : Surjective f) : (f '' s)ᶜ subseteq f '' sᶜ :=
compl_subset_iff_union.2 by
    rw [← image_union]
    simp [image_univ_of_surjective H]

/--
theorem `image_compl_eq` / 定理 `image_compl_eq`

English:
theorem image_compl_eq
  given: {f : α -> β} {s : Set α} (H : Bijective f)
  statement: f '' sᶜ = (f '' s)ᶜ
  proof: Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

中文:
定理 image_compl_eq
  条件: {f : α -> β} {s : Set α} (H : Bijective f)
  结论: f '' sᶜ = (f '' s)ᶜ
  证明: Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, image_compl_subset, subset_image_compl
-/
theorem image_compl_eq {f : α -> β} {s : Set α} (H : Bijective f) : f '' sᶜ = (f '' s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

/--
theorem `subset_image_sdiff` / 定理 `subset_image_sdiff`

English:
theorem subset_image_sdiff
  given: (f : α -> β) (s t : Set α)
  statement: f '' s \ f '' t subseteq f '' (s \ t)
  proof: by
  rw [sdiff_subset_iff]; rw [← image_union]; rw [union_sdiff_self]
  exact image_mono subset_union_right

中文:
定理 subset_image_sdiff
  条件: (f : α -> β) (s t : Set α)
  结论: f '' s \ f '' t subseteq f '' (s \ t)
  证明: by
  rw [sdiff_subset_iff]; rw [← image_union]; rw [union_sdiff_self]
  exact image_mono subset_union_right
-/
private theorem subset_image_sdiff (f : α -> β) (s t : Set α) : f '' s \ f '' t subseteq f '' (s \ t) := by
  rw [sdiff_subset_iff]; rw [← image_union]; rw [union_sdiff_self]
  exact image_mono subset_union_right

/--
theorem `image_sdiff` / 定理 `image_sdiff`

English:
theorem image_sdiff
  given: {f : α -> β} (hf : Injective f) (s t : Set α)
  statement: f '' (s \ t) = f '' s \ f '' t
  proof: Subset.antisymm
    (Subset.trans (image_sdiff_subset f s t) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_sdiff f s t)

@[deprecated image_sdiff (since := "2026-06-03")] alias subset_image_diff := subset_image_sdiff
@[deprecated (since := "2026-06-03")] alias image_diff 

中文:
定理 image_sdiff
  条件: {f : α -> β} (hf : Injective f) (s t : Set α)
  结论: f '' (s \ t) = f '' s \ f '' t
  证明: Subset.antisymm
    (Subset.trans (image_sdiff_subset f s t) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_sdiff f s t)

@[deprecated image_sdiff (since := "2026-06-03")] alias subset_image_diff := subset_image_sdiff
@[deprecated (since := "2026-06-03")] alias image_diff 

Depends on / 依赖: Subset, Subset.antisymm, Subset.trans, antisymm, image_compl_subset, image_sdiff_subset, inter_subset_inter_right, subset_image_sdiff
-/
theorem image_sdiff {f : α -> β} (hf : Injective f) (s t : Set α) : f '' (s \ t) = f '' s \ f '' t :=
  Subset.antisymm
    (Subset.trans (image_sdiff_subset f s t) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_sdiff f s t)

@[deprecated image_sdiff (since := "2026-06-03")] alias subset_image_diff := subset_image_sdiff
@[deprecated (since := "2026-06-03")] alias image_diff := image_sdiff

open scoped symmDiff in
/--
theorem `image_symmDiff` / 定理 `image_symmDiff`

English:
theorem image_symmDiff
  given: (hf : Injective f) (s t : Set α)
  statement: f '' s ∆ t = (f '' s) ∆ (f '' t)
  proof: by
  simp_rw [Set.symmDiff_def, image_union, image_sdiff hf]

中文:
定理 image_symmDiff
  条件: (hf : Injective f) (s t : Set α)
  结论: f '' s ∆ t = (f '' s) ∆ (f '' t)
  证明: by
  simp_rw [Set.symmDiff_def, image_union, image_sdiff hf]

Depends on / 依赖: Set.symmDiff_def, image_sdiff, image_union, simp_rw, symmDiff_def
-/
theorem image_symmDiff (hf : Injective f) (s t : Set α) : f '' s ∆ t = (f '' s) ∆ (f '' t) := by
  simp_rw [Set.symmDiff_def, image_union, image_sdiff hf]

/--
theorem `Nonempty.image` / 定理 `Nonempty.image`

English:
theorem Nonempty.image
  given: (f : α -> β) {s : Set α}
  statement: s.Nonempty -> (f '' s).Nonempty

中文:
定理 Nonempty.image
  条件: (f : α -> β) {s : Set α}
  结论: s.Nonempty -> (f '' s).Nonempty
-/
theorem Nonempty.image (f : α -> β) {s : Set α} : s.Nonempty -> (f '' s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩

/--
theorem `Nonempty.of_image` / 定理 `Nonempty.of_image`

English:
theorem Nonempty.of_image
  given: {f : α -> β} {s : Set α}
  statement: (f '' s).Nonempty -> s.Nonempty

中文:
定理 Nonempty.of_image
  条件: {f : α -> β} {s : Set α}
  结论: (f '' s).Nonempty -> s.Nonempty
-/
theorem Nonempty.of_image {f : α -> β} {s : Set α} : (f '' s).Nonempty -> s.Nonempty
  | ⟨_, x, hx, _⟩ => ⟨x, hx⟩

@[simp]
/--
theorem `image_nonempty` / 定理 `image_nonempty`

English:
theorem image_nonempty
  given: {f : α -> β} {s : Set α}
  statement: (f '' s).Nonempty ↔ s.Nonempty
  proof: ⟨Nonempty.of_image, fun h => h.image f⟩

中文:
定理 image_nonempty
  条件: {f : α -> β} {s : Set α}
  结论: (f '' s).Nonempty ↔ s.Nonempty
  证明: ⟨Nonempty.of_image, fun h => h.image f⟩

Depends on / 依赖: Nonempty, Nonempty.of_image, h.image, of_image
-/
theorem image_nonempty {f : α -> β} {s : Set α} : (f '' s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.image f⟩

/--
theorem `Nonempty.preimage` / 定理 `Nonempty.preimage`

English:
theorem Nonempty.preimage
  given: {s : Set β} (hs : s.Nonempty) {f : α -> β} (hf : Surjective f)
  proof: let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, by grind⟩

中文:
定理 Nonempty.preimage
  条件: {s : Set β} (hs : s.Nonempty) {f : α -> β} (hf : Surjective f)
  证明: let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, by grind⟩
-/
theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α -> β} (hf : Surjective f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, by grind⟩

instance (f : α -> β) (s : Set α) [Nonempty s] : Nonempty (f '' s) :=
  (Set.Nonempty.image f .of_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
/--
theorem `image_subset_iff` / 定理 `image_subset_iff`

English:
theorem image_subset_iff
  given: {s : Set α} {t : Set β} {f : α -> β}
  statement: f '' s subseteq t ↔ s subseteq f ⁻¹' t
  proof: forall_mem_image

中文:
定理 image_subset_iff
  条件: {s : Set α} {t : Set β} {f : α -> β}
  结论: f '' s subseteq t ↔ s subseteq f ⁻¹' t
  证明: forall_mem_image

Depends on / 依赖: forall_mem_image
-/
theorem image_subset_iff {s : Set α} {t : Set β} {f : α -> β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t :=
  forall_mem_image

/--
theorem `image_preimage_subset` / 定理 `image_preimage_subset`

English:
theorem image_preimage_subset
  given: (f : α -> β) (s : Set β)
  statement: f '' f ⁻¹' s subseteq s
  proof: image_subset_iff.2 Subset.rfl

中文:
定理 image_preimage_subset
  条件: (f : α -> β) (s : Set β)
  结论: f '' f ⁻¹' s subseteq s
  证明: image_subset_iff.2 Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, image_subset_iff
-/
theorem image_preimage_subset (f : α -> β) (s : Set β) : f '' f ⁻¹' s subseteq s :=
  image_subset_iff.2 Subset.rfl

/--
theorem `subset_preimage_image` / 定理 `subset_preimage_image`

English:
theorem subset_preimage_image
  given: (f : α -> β) (s : Set α)
  statement: s subseteq f ⁻¹' f '' s
  proof: fun _ =>
  mem_image_of_mem f

中文:
定理 subset_preimage_image
  条件: (f : α -> β) (s : Set α)
  结论: s subseteq f ⁻¹' f '' s
  证明: fun _ =>
  mem_image_of_mem f
-/
theorem subset_preimage_image (f : α -> β) (s : Set α) : s subseteq f ⁻¹' f '' s := fun _ =>
  mem_image_of_mem f

/--
theorem `preimage_image_univ` / 定理 `preimage_image_univ`

English:
theorem preimage_image_univ
  given: {f : α -> β}
  statement: f ⁻¹' f '' univ = univ
  proof: Subset.antisymm (fun _ _ => trivial) (subset_preimage_image f univ)

@[simp]

中文:
定理 preimage_image_univ
  条件: {f : α -> β}
  结论: f ⁻¹' f '' univ = univ
  证明: Subset.antisymm (fun _ _ => trivial) (subset_preimage_image f univ)

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, subset_preimage_image
-/
theorem preimage_image_univ {f : α -> β} : f ⁻¹' f '' univ = univ :=
  Subset.antisymm (fun _ _ => trivial) (subset_preimage_image f univ)

@[simp]
/--
theorem `preimage_image_eq` / 定理 `preimage_image_eq`

English:
theorem preimage_image_eq
  given: {f : α -> β} (s : Set α) (h : Injective f)
  statement: f ⁻¹' f '' s = s
  proof: Subset.antisymm (fun _ ⟨_, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

@[simp]

中文:
定理 preimage_image_eq
  条件: {f : α -> β} (s : Set α) (h : Injective f)
  结论: f ⁻¹' f '' s = s
  证明: Subset.antisymm (fun _ ⟨_, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, subset_preimage_image
-/
theorem preimage_image_eq {f : α -> β} (s : Set α) (h : Injective f) : f ⁻¹' f '' s = s :=
  Subset.antisymm (fun _ ⟨_, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

@[simp]
/--
theorem `image_preimage_eq` / 定理 `image_preimage_eq`

English:
theorem image_preimage_eq
  given: {f : α -> β} (s : Set β) (h : Surjective f)
  statement: f '' f ⁻¹' s = s
  proof: Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, by grind⟩

@[simp]

中文:
定理 image_preimage_eq
  条件: {f : α -> β} (s : Set β) (h : Surjective f)
  结论: f '' f ⁻¹' s = s
  证明: Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, by grind⟩

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, image_preimage_subset
-/
theorem image_preimage_eq {f : α -> β} (s : Set β) (h : Surjective f) : f '' f ⁻¹' s = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, by grind⟩

@[simp]
/--
theorem `Nonempty.subset_preimage_const` / 定理 `Nonempty.subset_preimage_const`

English:
theorem Nonempty.subset_preimage_const
  given: {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β)
  proof: by
  rw [← image_subset_iff]; rw [hs.image_const]; rw [singleton_subset_iff]

@[simp]

中文:
定理 Nonempty.subset_preimage_const
  条件: {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β)
  证明: by
  rw [← image_subset_iff]; rw [hs.image_const]; rw [singleton_subset_iff]

@[simp]

Depends on / 依赖: hs.image_const, image_const, image_subset_iff, singleton_subset_iff
-/
theorem Nonempty.subset_preimage_const {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β) :
    s subseteq (fun _ => a) ⁻¹' t ↔ a in t := by
  rw [← image_subset_iff]; rw [hs.image_const]; rw [singleton_subset_iff]

@[simp]
/--
theorem `preimage_injective` / 定理 `preimage_injective`

English:
theorem preimage_injective
  statement: Injective (preimage f) ↔ Surjective f
  proof: by
  rw [← Injective.of_comp_iff Set.mem_injective]; rw [← Injective.of_comp_iff' _ Set.ofPred_bijective]
  exact injective_comp_right_iff_surjective

@[simp]

中文:
定理 preimage_injective
  结论: Injective (preimage f) ↔ Surjective f
  证明: by
  rw [← Injective.of_comp_iff Set.mem_injective]; rw [← Injective.of_comp_iff' _ Set.ofPred_bijective]
  exact injective_comp_right_iff_surjective

@[simp]

Depends on / 依赖: Injective, Injective.of_comp_iff, Set.mem_injective, Set.ofPred_bijective, injective_comp_right_iff_surjective, mem_injective, ofPred_bijective, of_comp_iff
-/
theorem preimage_injective : Injective (preimage f) ↔ Surjective f := by
  rw [← Injective.of_comp_iff Set.mem_injective]; rw [← Injective.of_comp_iff' _ Set.ofPred_bijective]
  exact injective_comp_right_iff_surjective

@[simp]
/--
theorem `preimage_surjective` / 定理 `preimage_surjective`

English:
theorem preimage_surjective
  statement: Surjective (preimage f) ↔ Injective f
  proof: by
  rw [← Surjective.of_comp_iff _ Set.ofPred_bijective.surjective]; rw [← Surjective.of_comp_iff' Set.mem_bijective]
  exact surjective_comp_right_iff_injective

@[simp]

中文:
定理 preimage_surjective
  结论: Surjective (preimage f) ↔ Injective f
  证明: by
  rw [← Surjective.of_comp_iff _ Set.ofPred_bijective.surjective]; rw [← Surjective.of_comp_iff' Set.mem_bijective]
  exact surjective_comp_right_iff_injective

@[simp]

Depends on / 依赖: Set.mem_bijective, Set.ofPred_bijective.surjective, Surjective, Surjective.of_comp_iff, mem_bijective, ofPred_bijective, of_comp_iff, surjective, surjective_comp_right_iff_injective
-/
theorem preimage_surjective : Surjective (preimage f) ↔ Injective f := by
  rw [← Surjective.of_comp_iff _ Set.ofPred_bijective.surjective]; rw [← Surjective.of_comp_iff' Set.mem_bijective]
  exact surjective_comp_right_iff_injective

@[simp]
/--
theorem `preimage_eq_preimage` / 定理 `preimage_eq_preimage`

English:
theorem preimage_eq_preimage
  given: {f : β -> α} (hf : Surjective f)
  statement: f ⁻¹' s = f ⁻¹' t ↔ s = t
  proof: (preimage_injective.mpr hf).eq_iff

中文:
定理 preimage_eq_preimage
  条件: {f : β -> α} (hf : Surjective f)
  结论: f ⁻¹' s = f ⁻¹' t ↔ s = t
  证明: (preimage_injective.mpr hf).eq_iff

Depends on / 依赖: eq_iff, preimage_injective, preimage_injective.mpr
-/
theorem preimage_eq_preimage {f : β -> α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  (preimage_injective.mpr hf).eq_iff

/--
theorem `image_inter_preimage` / 定理 `image_inter_preimage`

English:
theorem image_inter_preimage
  given: (f : α -> β) (s : Set α) (t : Set β)
  proof: by grind

中文:
定理 image_inter_preimage
  条件: (f : α -> β) (s : Set α) (t : Set β)
  证明: by grind
-/
theorem image_inter_preimage (f : α -> β) (s : Set α) (t : Set β) :
    f '' (s inter f ⁻¹' t) = f '' s inter t := by grind

/--
theorem `image_preimage_inter` / 定理 `image_preimage_inter`

English:
theorem image_preimage_inter
  given: (f : α -> β) (s : Set α) (t : Set β)
  proof: by simp only [inter_comm, image_inter_preimage]

@[simp]

中文:
定理 image_preimage_inter
  条件: (f : α -> β) (s : Set α) (t : Set β)
  证明: by simp only [inter_comm, image_inter_preimage]

@[simp]

Depends on / 依赖: image_inter_preimage, inter_comm
-/
theorem image_preimage_inter (f : α -> β) (s : Set α) (t : Set β) :
    f '' (f ⁻¹' t inter s) = t inter f '' s := by simp only [inter_comm, image_inter_preimage]

@[simp]
/--
theorem `image_inter_nonempty_iff` / 定理 `image_inter_nonempty_iff`

English:
theorem image_inter_nonempty_iff
  given: {f : α -> β} {s : Set α} {t : Set β}
  proof: by
  rw [← image_inter_preimage]; rw [image_nonempty]

中文:
定理 image_inter_nonempty_iff
  条件: {f : α -> β} {s : Set α} {t : Set β}
  证明: by
  rw [← image_inter_preimage]; rw [image_nonempty]

Depends on / 依赖: image_inter_preimage, image_nonempty
-/
theorem image_inter_nonempty_iff {f : α -> β} {s : Set α} {t : Set β} :
    (f '' s inter t).Nonempty ↔ (s inter f ⁻¹' t).Nonempty := by
  rw [← image_inter_preimage]; rw [image_nonempty]

/--
theorem `disjoint_image_left` / 定理 `disjoint_image_left`

English:
theorem disjoint_image_left
  given: {f : α -> β} {s : Set α} {t : Set β}
  proof: by
  simp_rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, image_inter_nonempty_iff]

中文:
定理 disjoint_image_left
  条件: {f : α -> β} {s : Set α} {t : Set β}
  证明: by
  simp_rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, image_inter_nonempty_iff]

Depends on / 依赖: disjoint_iff_inter_eq_empty, image_inter_nonempty_iff, not_nonempty_iff_eq_empty, simp_rw
-/
theorem disjoint_image_left {f : α -> β} {s : Set α} {t : Set β} :
    Disjoint (f '' s) t ↔ Disjoint s (f ⁻¹' t) := by
  simp_rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, image_inter_nonempty_iff]

/--
theorem `disjoint_image_right` / 定理 `disjoint_image_right`

English:
theorem disjoint_image_right
  given: {f : α -> β} {s : Set α} {t : Set β}
  proof: by
  rw [disjoint_comm]; rw [disjoint_comm (b := s)]; rw [disjoint_image_left]

中文:
定理 disjoint_image_right
  条件: {f : α -> β} {s : Set α} {t : Set β}
  证明: by
  rw [disjoint_comm]; rw [disjoint_comm (b := s)]; rw [disjoint_image_left]

Depends on / 依赖: disjoint_comm, disjoint_image_left
-/
theorem disjoint_image_right {f : α -> β} {s : Set α} {t : Set β} :
    Disjoint t (f '' s) ↔ Disjoint (f ⁻¹' t) s := by
  rw [disjoint_comm]; rw [disjoint_comm (b := s)]; rw [disjoint_image_left]

/--
theorem `image_sdiff_preimage` / 定理 `image_sdiff_preimage`

English:
theorem image_sdiff_preimage
  given: {f : α -> β} {s : Set α} {t : Set β}
  proof: by simp_rw [sdiff_eq, ← preimage_compl, image_inter_preimage]

@[deprecated (since := "2026-06-03")] alias image_diff_preimage := image_sdiff_preimage

中文:
定理 image_sdiff_preimage
  条件: {f : α -> β} {s : Set α} {t : Set β}
  证明: by simp_rw [sdiff_eq, ← preimage_compl, image_inter_preimage]

@[deprecated (since := "2026-06-03")] alias image_diff_preimage := image_sdiff_preimage

Depends on / 依赖: image_inter_preimage, preimage_compl, sdiff_eq, simp_rw
-/
theorem image_sdiff_preimage {f : α -> β} {s : Set α} {t : Set β} :
    f '' (s \ f ⁻¹' t) = f '' s \ t := by simp_rw [sdiff_eq, ← preimage_compl, image_inter_preimage]

@[deprecated (since := "2026-06-03")] alias image_diff_preimage := image_sdiff_preimage

/--
theorem `compl_image` / 定理 `compl_image`

English:
theorem compl_image
  statement: image (compl : Set α -> Set α) = preimage compl
  proof: image_eq_preimage_of_inverse compl_compl compl_compl

中文:
定理 compl_image
  结论: image (compl : Set α -> Set α) = preimage compl
  证明: image_eq_preimage_of_inverse compl_compl compl_compl

Depends on / 依赖: compl_compl, image_eq_preimage_of_inverse
-/
theorem compl_image : image (compl : Set α -> Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl

/--
theorem `compl_image_ofPred` / 定理 `compl_image_ofPred`

English:
theorem compl_image_ofPred
  given: {p : Set α -> Prop}
  statement: compl '' { s | p s } = { s | p sᶜ }
  proof: congr_fun compl_image {x | p x}

@[deprecated (since := "2026-07-13")] alias compl_image_set_of := compl_image_ofPred

中文:
定理 compl_image_ofPred
  条件: {p : Set α -> 命题}
  结论: compl '' { s | p s } = { s | p sᶜ }
  证明: congr_fun compl_image {x | p x}

@[deprecated (since := "2026-07-13")] alias compl_image_set_of := compl_image_ofPred

Depends on / 依赖: compl_image, congr_fun
-/
theorem compl_image_ofPred {p : Set α -> Prop} : compl '' { s | p s } = { s | p sᶜ } :=
  congr_fun compl_image {x | p x}

@[deprecated (since := "2026-07-13")] alias compl_image_set_of := compl_image_ofPred

/--
theorem `inter_preimage_subset` / 定理 `inter_preimage_subset`

English:
theorem inter_preimage_subset
  given: (s : Set α) (t : Set β) (f : α -> β)
  proof: fun _ h => ⟨mem_image_of_mem _ h.left, h.right⟩

中文:
定理 inter_preimage_subset
  条件: (s : Set α) (t : Set β) (f : α -> β)
  证明: fun _ h => ⟨mem_image_of_mem _ h.left, h.right⟩

Depends on / 依赖: h.left, h.right, mem_image_of_mem
-/
theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α -> β) :
    s inter f ⁻¹' t subseteq f ⁻¹' (f '' s inter t) := fun _ h => ⟨mem_image_of_mem _ h.left, h.right⟩

/--
theorem `union_preimage_subset` / 定理 `union_preimage_subset`

English:
theorem union_preimage_subset
  given: (s : Set α) (t : Set β) (f : α -> β)
  proof: fun _ h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r

中文:
定理 union_preimage_subset
  条件: (s : Set α) (t : Set β) (f : α -> β)
  证明: fun _ h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r
-/
theorem union_preimage_subset (s : Set α) (t : Set β) (f : α -> β) :
    s union f ⁻¹' t subseteq f ⁻¹' (f '' s union t) := fun _ h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r

/--
theorem `subset_image_union` / 定理 `subset_image_union`

English:
theorem subset_image_union
  given: (f : α -> β) (s : Set α) (t : Set β)
  statement: f '' (s union f ⁻¹' t) subseteq f '' s union t
  proof: image_subset_iff.2 (union_preimage_subset _ _ _)

中文:
定理 subset_image_union
  条件: (f : α -> β) (s : Set α) (t : Set β)
  结论: f '' (s union f ⁻¹' t) subseteq f '' s union t
  证明: image_subset_iff.2 (union_preimage_subset _ _ _)

Depends on / 依赖: image_subset_iff, union_preimage_subset
-/
theorem subset_image_union (f : α -> β) (s : Set α) (t : Set β) : f '' (s union f ⁻¹' t) subseteq f '' s union t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)

/--
theorem `preimage_subset_iff` / 定理 `preimage_subset_iff`

English:
theorem preimage_subset_iff
  given: {A : Set α} {B : Set β} {f : α -> β}
  proof: Iff.rfl

中文:
定理 preimage_subset_iff
  条件: {A : Set α} {B : Set β} {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α -> β} :
    f ⁻¹' B subseteq A ↔ forall a : α, f a in B -> a in A :=
  Iff.rfl

/--
theorem `image_eq_image` / 定理 `image_eq_image`

English:
theorem image_eq_image
  given: {f : α -> β} (hf : Injective f)
  statement: f '' s = f '' t ↔ s = t
  proof: Iff.symm
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf]; rw [← preimage_image_eq t hf]; rw [eq]

中文:
定理 image_eq_image
  条件: {f : α -> β} (hf : Injective f)
  结论: f '' s = f '' t ↔ s = t
  证明: Iff.symm
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf]; rw [← preimage_image_eq t hf]; rw [eq]

Depends on / 依赖: Iff.intro, Iff.symm, preimage_image_eq
-/
theorem image_eq_image {f : α -> β} (hf : Injective f) : f '' s = f '' t ↔ s = t :=
Iff.symm
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf]; rw [← preimage_image_eq t hf]; rw [eq]

/--
theorem `subset_image_iff` / 定理 `subset_image_iff`

English:
theorem subset_image_iff
  given: {t : Set β}
  proof: by
  refine ⟨fun h => ⟨f ⁻¹' t inter s, inter_subset_right, ?_⟩,
    fun ⟨u, hu, hu'⟩ => hu'.symm ▸ image_mono hu⟩
  rwa [image_preimage_inter, inter_eq_left]

@[simp]

中文:
定理 subset_image_iff
  条件: {t : Set β}
  证明: by
  refine ⟨fun h => ⟨f ⁻¹' t inter s, inter_subset_right, ?_⟩,
    fun ⟨u, hu, hu'⟩ => hu'.symm ▸ image_mono hu⟩
  rwa [image_preimage_inter, inter_eq_left]

@[simp]

Depends on / 依赖: image_mono, image_preimage_inter, inter_eq_left, inter_subset_right
-/
theorem subset_image_iff {t : Set β} :
    t subseteq f '' s ↔ exists u, u subseteq s ∧ f '' u = t := by
  refine ⟨fun h => ⟨f ⁻¹' t inter s, inter_subset_right, ?_⟩,
    fun ⟨u, hu, hu'⟩ => hu'.symm ▸ image_mono hu⟩
  rwa [image_preimage_inter, inter_eq_left]

@[simp]
/--
lemma `exists_subset_image_iff` / 引理 `exists_subset_image_iff`

English:
lemma exists_subset_image_iff
  given: {p : Set β -> Prop}
  statement: (exists t subseteq f '' s, p t) ↔ exists t subseteq s, p (f '' t)
  proof: by
  simp [subset_image_iff]

@[simp]

中文:
引理 exists_subset_image_iff
  条件: {p : Set β -> 命题}
  结论: (存在 t subseteq f '' s, p t) ↔ 存在 t subseteq s, p (f '' t)
  证明: by
  simp [subset_image_iff]

@[simp]

Depends on / 依赖: subset_image_iff
-/
lemma exists_subset_image_iff {p : Set β -> Prop} : (exists t subseteq f '' s, p t) ↔ exists t subseteq s, p (f '' t) := by
  simp [subset_image_iff]

@[simp]
/--
lemma `forall_subset_image_iff` / 引理 `forall_subset_image_iff`

English:
lemma forall_subset_image_iff
  given: {p : Set β -> Prop}
  statement: (forall t subseteq f '' s, p t) ↔ forall t subseteq s, p (f '' t)
  proof: by
  simp [subset_image_iff]

中文:
引理 forall_subset_image_iff
  条件: {p : Set β -> 命题}
  结论: (对任意 t subseteq f '' s, p t) ↔ 对任意 t subseteq s, p (f '' t)
  证明: by
  simp [subset_image_iff]

Depends on / 依赖: subset_image_iff
-/
lemma forall_subset_image_iff {p : Set β -> Prop} : (forall t subseteq f '' s, p t) ↔ forall t subseteq s, p (f '' t) := by
  simp [subset_image_iff]

/--
theorem `image_subset_image_iff` / 定理 `image_subset_image_iff`

English:
theorem image_subset_image_iff
  given: {f : α -> β} (hf : Injective f)
  statement: f '' s subseteq f '' t ↔ s subseteq t
  proof: by
  grind [Set.image_subset_iff, Set.preimage_image_eq]

中文:
定理 image_subset_image_iff
  条件: {f : α -> β} (hf : Injective f)
  结论: f '' s subseteq f '' t ↔ s subseteq t
  证明: by
  grind [Set.image_subset_iff, Set.preimage_image_eq]

Depends on / 依赖: Set.image_subset_iff, Set.preimage_image_eq, image_subset_iff, preimage_image_eq
-/
theorem image_subset_image_iff {f : α -> β} (hf : Injective f) : f '' s subseteq f '' t ↔ s subseteq t := by
  grind [Set.image_subset_iff, Set.preimage_image_eq]

/--
theorem `prod_quotient_preimage_eq_image` / 定理 `prod_quotient_preimage_eq_image`

English:
theorem prod_quotient_preimage_eq_image
  statement: [s : Setoid α] (g : Quotient s -> β) {h : α -> β}
  proof: Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quot.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) in r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩

中文:
定理 prod_quotient_preimage_eq_image
  结论: [s : Setoid α] (g : Quotient s -> β) {h : α -> β}
  证明: Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quot.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) in r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩

Depends on / 依赖: Hh.symm, Prod.ext_iff, Quot.induction_on, Set.ext, ext_iff
-/
theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s -> β) {h : α -> β}
    (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) in r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) '' ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quot.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) in r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩

/--
theorem `exists_image_iff` / 定理 `exists_image_iff`

English:
theorem exists_image_iff
  given: (f : α -> β) (x : Set α) (P : β -> Prop)
  proof: ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.choose_spec.1⟩, a.prop.choose_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩

中文:
定理 exists_image_iff
  条件: (f : α -> β) (x : Set α) (P : β -> 命题)
  证明: ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.choose_spec.1⟩, a.prop.choose_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩

Depends on / 依赖: a.prop, a.prop.choose_spec, choose_spec
-/
theorem exists_image_iff (f : α -> β) (x : Set α) (P : β -> Prop) :
    (exists a : f '' x, P a) ↔ exists a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.choose_spec.1⟩, a.prop.choose_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩

/--
theorem `imageFactorization_eq` / 定理 `imageFactorization_eq`

English:
theorem imageFactorization_eq
  given: {f : α -> β} {s : Set α}
  proof: funext fun _ => rfl

中文:
定理 imageFactorization_eq
  条件: {f : α -> β} {s : Set α}
  证明: funext fun _ => rfl
-/
theorem imageFactorization_eq {f : α -> β} {s : Set α} :
    Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun _ => rfl

/--
theorem `imageFactorization_surjective` / 定理 `imageFactorization_surjective`

English:
theorem imageFactorization_surjective
  given: {f : α -> β} {s : Set α}
  proof: fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩

中文:
定理 imageFactorization_surjective
  条件: {f : α -> β} {s : Set α}
  证明: fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩
-/
theorem imageFactorization_surjective {f : α -> β} {s : Set α} :
    Surjective (imageFactorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩

/--
theorem `image_perm` / 定理 `image_perm`

English:
theorem image_perm
  given: {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a != a } subseteq s)
  statement: σ '' s = s
  proof: by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine ⟨?_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine iff_of_true ⟨σ.symm i, hs fun h => hi ?_, σ.apply_symm_apply _⟩ (hs hi)
    grind

中文:
定理 image_perm
  条件: {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a != a } subseteq s)
  结论: σ '' s = s
  证明: by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine ⟨?_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine iff_of_true ⟨σ.symm i, hs fun h => hi ?_, σ.apply_symm_apply _⟩ (hs hi)
    grind

Depends on / 依赖: apply_symm_apply, eq_or_ne, h.symm, hi.trans, iff_of_true, injective
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a != a } subseteq s) : σ '' s = s := by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine ⟨?_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine iff_of_true ⟨σ.symm i, hs fun h => hi ?_, σ.apply_symm_apply _⟩ (hs hi)
    grind

end Image

/-! ### Lemmas about the powerset and image. -/

/--
theorem `powerset_insert` / 定理 `powerset_insert`

English:
theorem powerset_insert
  given: (s : Set α) (a : α)
  statement: 𝒫 insert a s = 𝒫 s union insert a '' 𝒫 s
  proof: by
  ext t
  constructor
  · intro h
    by_cases hs : a in t
    · right
      refine ⟨t \ {a}, by grind⟩
    · grind
  · grind

中文:
定理 powerset_insert
  条件: (s : Set α) (a : α)
  结论: 𝒫 insert a s = 𝒫 s union insert a '' 𝒫 s
  证明: by
  ext t
  constructor
  · intro h
    by_cases hs : a in t
    · right
      refine ⟨t \ {a}, by grind⟩
    · grind
  · grind
-/
theorem powerset_insert (s : Set α) (a : α) : 𝒫 insert a s = 𝒫 s union insert a '' 𝒫 s := by
  ext t
  constructor
  · intro h
    by_cases hs : a in t
    · right
      refine ⟨t \ {a}, by grind⟩
    · grind
  · grind

/--
theorem `disjoint_powerset_insert` / 定理 `disjoint_powerset_insert`

English:
theorem disjoint_powerset_insert
  given: {s : Set α} {a : α} (h : a ∉ s)
  proof: by
  grind

中文:
定理 disjoint_powerset_insert
  条件: {s : Set α} {a : α} (h : a ∉ s)
  证明: by
  grind
-/
theorem disjoint_powerset_insert {s : Set α} {a : α} (h : a ∉ s) :
    Disjoint (𝒫 s) (insert a '' 𝒫 s) := by
  grind

/--
theorem `powerset_insert_injOn` / 定理 `powerset_insert_injOn`

English:
theorem powerset_insert_injOn
  given: {s : Set α} {a : α} (h : a ∉ s)
  proof: fun u u_mem v v_mem eq => by
  grind

中文:
定理 powerset_insert_injOn
  条件: {s : Set α} {a : α} (h : a ∉ s)
  证明: fun u u_mem v v_mem eq => by
  grind

Depends on / 依赖: u_mem, v_mem
-/
theorem powerset_insert_injOn {s : Set α} {a : α} (h : a ∉ s) :
    Set.InjOn (insert a) (𝒫 s) := fun u u_mem v v_mem eq => by
  grind

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι -> α} {s t : Set α}

/--
theorem `forall_mem_range` / 定理 `forall_mem_range`

English:
theorem forall_mem_range
  given: {p : α -> Prop}
  statement: (forall a in range f, p a) ↔ forall i, p (f i)
  proof: by simp

中文:
定理 forall_mem_range
  条件: {p : α -> 命题}
  结论: (对任意 a in range f, p a) ↔ 对任意 i, p (f i)
  证明: by simp
-/
theorem forall_mem_range {p : α -> Prop} : (forall a in range f, p a) ↔ forall i, p (f i) := by simp

/--
theorem `forall_subtype_range_iff` / 定理 `forall_subtype_range_iff`

English:
theorem forall_subtype_range_iff
  given: {p : range f -> Prop}
  proof: by grind

中文:
定理 forall_subtype_range_iff
  条件: {p : range f -> 命题}
  证明: by grind
-/
theorem forall_subtype_range_iff {p : range f -> Prop} :
    (forall a : range f, p a) ↔ forall i, p ⟨f i, mem_range_self _⟩ := by grind

/--
theorem `exists_range_iff` / 定理 `exists_range_iff`

English:
theorem exists_range_iff
  given: {p : α -> Prop}
  statement: (exists a in range f, p a) ↔ exists i, p (f i)
  proof: by simp

中文:
定理 exists_range_iff
  条件: {p : α -> 命题}
  结论: (存在 a in range f, p a) ↔ 存在 i, p (f i)
  证明: by simp
-/
theorem exists_range_iff {p : α -> Prop} : (exists a in range f, p a) ↔ exists i, p (f i) := by simp

/--
theorem `exists_subtype_range_iff` / 定理 `exists_subtype_range_iff`

English:
theorem exists_subtype_range_iff
  given: {p : range f -> Prop}
  proof: by grind

中文:
定理 exists_subtype_range_iff
  条件: {p : range f -> 命题}
  证明: by grind
-/
theorem exists_subtype_range_iff {p : range f -> Prop} :
    (exists a : range f, p a) ↔ exists i, p ⟨f i, mem_range_self _⟩ := by grind

/--
theorem `range_eq_univ` / 定理 `range_eq_univ`

English:
theorem range_eq_univ
  statement: range f = univ ↔ Surjective f
  proof: eq_univ_iff_forall

alias ⟨_, _root_.Function.Surjective.range_eq⟩ := range_eq_univ

@[simp]

中文:
定理 range_eq_univ
  结论: range f = univ ↔ Surjective f
  证明: eq_univ_iff_forall

alias ⟨_, _root_.Function.Surjective.range_eq⟩ := range_eq_univ

@[simp]

Depends on / 依赖: eq_univ_iff_forall
-/
theorem range_eq_univ : range f = univ ↔ Surjective f :=
  eq_univ_iff_forall

alias ⟨_, _root_.Function.Surjective.range_eq⟩ := range_eq_univ

@[simp]
/--
theorem `subset_range_of_surjective` / 定理 `subset_range_of_surjective`

English:
theorem subset_range_of_surjective
  given: {f : α -> β} (h : Surjective f) (s : Set β)
  proof: Surjective.range_eq h ▸ subset_univ s

@[simp]

中文:
定理 subset_range_of_surjective
  条件: {f : α -> β} (h : Surjective f) (s : Set β)
  证明: Surjective.range_eq h ▸ subset_univ s

@[simp]

Depends on / 依赖: Surjective, Surjective.range_eq, range_eq, subset_univ
-/
theorem subset_range_of_surjective {f : α -> β} (h : Surjective f) (s : Set β) :
    s subseteq range f := Surjective.range_eq h ▸ subset_univ s

@[simp]
/--
theorem `image_univ` / 定理 `image_univ`

English:
theorem image_univ
  given: {f : α -> β}
  statement: f '' univ = range f
  proof: by grind

中文:
定理 image_univ
  条件: {f : α -> β}
  结论: f '' univ = range f
  证明: by grind
-/
theorem image_univ {f : α -> β} : f '' univ = range f := by grind

/--
lemma `image_compl_eq_range_sdiff_image` / 引理 `image_compl_eq_range_sdiff_image`

English:
lemma image_compl_eq_range_sdiff_image
  given: {f : α -> β} (hf : Injective f) (s : Set α)
  proof: by rw [← image_univ, ← image_sdiff hf, compl_eq_univ_sdiff]

@[deprecated (since := "2026-06-03")]
alias image_compl_eq_range_diff_image := image_compl_eq_range_sdiff_image

中文:
引理 image_compl_eq_range_sdiff_image
  条件: {f : α -> β} (hf : Injective f) (s : Set α)
  证明: by rw [← image_univ, ← image_sdiff hf, compl_eq_univ_sdiff]

@[deprecated (since := "2026-06-03")]
alias image_compl_eq_range_diff_image := image_compl_eq_range_sdiff_image

Depends on / 依赖: compl_eq_univ_sdiff, image_sdiff, image_univ
-/
lemma image_compl_eq_range_sdiff_image {f : α -> β} (hf : Injective f) (s : Set α) :
    f '' sᶜ = range f \ f '' s := by rw [← image_univ, ← image_sdiff hf, compl_eq_univ_sdiff]

@[deprecated (since := "2026-06-03")]
alias image_compl_eq_range_diff_image := image_compl_eq_range_sdiff_image

/--
lemma `range_sdiff_image` / 引理 `range_sdiff_image`

English:
lemma range_sdiff_image
  given: {f : α -> β} (hf : Injective f) (s : Set α)
  proof: by
  rw [image_compl_eq_range_sdiff_image hf]

@[deprecated (since := "2026-06-03")] alias range_diff_image := range_sdiff_image

@[simp]

中文:
引理 range_sdiff_image
  条件: {f : α -> β} (hf : Injective f) (s : Set α)
  证明: by
  rw [image_compl_eq_range_sdiff_image hf]

@[deprecated (since := "2026-06-03")] alias range_diff_image := range_sdiff_image

@[simp]

Depends on / 依赖: image_compl_eq_range_sdiff_image
-/
lemma range_sdiff_image {f : α -> β} (hf : Injective f) (s : Set α) :
    range f \ f '' s = f '' sᶜ := by
  rw [image_compl_eq_range_sdiff_image hf]

@[deprecated (since := "2026-06-03")] alias range_diff_image := range_sdiff_image

@[simp]
/--
theorem `preimage_eq_univ_iff` / 定理 `preimage_eq_univ_iff`

English:
theorem preimage_eq_univ_iff
  given: {f : α -> β} {s}
  statement: f ⁻¹' s = univ ↔ range f subseteq s
  proof: by
  rw [← univ_subset_iff]; rw [← image_subset_iff]; rw [image_univ]

中文:
定理 preimage_eq_univ_iff
  条件: {f : α -> β} {s}
  结论: f ⁻¹' s = univ ↔ range f subseteq s
  证明: by
  rw [← univ_subset_iff]; rw [← image_subset_iff]; rw [image_univ]

Depends on / 依赖: image_subset_iff, image_univ, univ_subset_iff
-/
theorem preimage_eq_univ_iff {f : α -> β} {s} : f ⁻¹' s = univ ↔ range f subseteq s := by
  rw [← univ_subset_iff]; rw [← image_subset_iff]; rw [image_univ]

/--
theorem `image_subset_range` / 定理 `image_subset_range`

English:
theorem image_subset_range
  given: (f : α -> β) (s)
  statement: f '' s subseteq range f
  proof: by
  rw [← image_univ]; exact image_mono (subset_univ _)

中文:
定理 image_subset_range
  条件: (f : α -> β) (s)
  结论: f '' s subseteq range f
  证明: by
  rw [← image_univ]; exact image_mono (subset_univ _)

Depends on / 依赖: image_mono, image_univ, subset_univ
-/
theorem image_subset_range (f : α -> β) (s) : f '' s subseteq range f := by
  rw [← image_univ]; exact image_mono (subset_univ _)

/--
theorem `mem_range_of_mem_image` / 定理 `mem_range_of_mem_image`

English:
theorem mem_range_of_mem_image
  given: (f : α -> β) (s) {x : β} (h : x in f '' s)
  statement: x in range f
  proof: image_subset_range f s h

中文:
定理 mem_range_of_mem_image
  条件: (f : α -> β) (s) {x : β} (h : x in f '' s)
  结论: x in range f
  证明: image_subset_range f s h

Depends on / 依赖: image_subset_range
-/
theorem mem_range_of_mem_image (f : α -> β) (s) {x : β} (h : x in f '' s) : x in range f :=
  image_subset_range f s h

/--
theorem `_root_.Nat.mem_range_succ` / 定理 `_root_.Nat.mem_range_succ`

English:
theorem _root_.Nat.mem_range_succ
  given: (i : Nat)
  statement: i in range Nat.succ ↔ 0 < i
  proof: ⟨by grind, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩

中文:
定理 _root_.Nat.mem_range_succ
  条件: (i : 自然数)
  结论: i in range 自然数.succ ↔ 0 < i
  证明: ⟨by grind, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩

Depends on / 依赖: Nat.succ_pred_eq_of_pos, succ_pred_eq_of_pos
-/
theorem _root_.Nat.mem_range_succ (i : Nat) : i in range Nat.succ ↔ 0 < i :=
  ⟨by grind, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩

/--
theorem `Nonempty.preimage'` / 定理 `Nonempty.preimage'`

English:
theorem Nonempty.preimage'
  given: {s : Set β} (hs : s.Nonempty) {f : α -> β} (hf : s subseteq range f)
  proof: let ⟨_, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, by grind⟩

中文:
定理 Nonempty.preimage'
  条件: {s : Set β} (hs : s.Nonempty) {f : α -> β} (hf : s subseteq range f)
  证明: let ⟨_, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, by grind⟩
-/
theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α -> β} (hf : s subseteq range f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨_, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, by grind⟩

/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  given: (g : α -> β) (f : ι -> α)
  statement: range (g ∘ f) = g '' range f
  proof: by aesop

中文:
定理 range_comp
  条件: (g : α -> β) (f : ι -> α)
  结论: range (g ∘ f) = g '' range f
  证明: by aesop
-/
theorem range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g '' range f := by aesop

/--
theorem `range_comp'` / 定理 `range_comp'`

English:
theorem range_comp'
  given: (g : α -> β) (f : ι -> α)
  statement: range (fun x => g (f x)) = g '' range f
  proof: range_comp g f

中文:
定理 range_comp'
  条件: (g : α -> β) (f : ι -> α)
  结论: range (fun x => g (f x)) = g '' range f
  证明: range_comp g f

Depends on / 依赖: range_comp
-/
theorem range_comp' (g : α -> β) (f : ι -> α) : range (fun x => g (f x)) = g '' range f :=
  range_comp g f

/--
theorem `range_subset_iff` / 定理 `range_subset_iff`

English:
theorem range_subset_iff
  statement: range f subseteq s ↔ forall y, f y in s
  proof: forall_mem_range

中文:
定理 range_subset_iff
  结论: range f subseteq s ↔ 对任意 y, f y in s
  证明: forall_mem_range

Depends on / 依赖: forall_mem_range
-/
theorem range_subset_iff : range f subseteq s ↔ forall y, f y in s :=
  forall_mem_range

/--
theorem `range_subset_range_iff_exists_comp` / 定理 `range_subset_range_iff_exists_comp`

English:
theorem range_subset_range_iff_exists_comp
  given: {f : α -> γ} {g : β -> γ}
  proof: by
  simp only [range_subset_iff, mem_range, Classical.skolem, funext_iff, (· ∘ ·), eq_comm]

中文:
定理 range_subset_range_iff_exists_comp
  条件: {f : α -> γ} {g : β -> γ}
  证明: by
  simp only [range_subset_iff, mem_range, Classical.skolem, funext_iff, (· ∘ ·), eq_comm]

Depends on / 依赖: Classical, Classical.skolem, eq_comm, funext_iff, mem_range, range_subset_iff, skolem
-/
theorem range_subset_range_iff_exists_comp {f : α -> γ} {g : β -> γ} :
    range f subseteq range g ↔ exists h : α -> β, f = g ∘ h := by
  simp only [range_subset_iff, mem_range, Classical.skolem, funext_iff, (· ∘ ·), eq_comm]

/--
theorem `range_eq_iff` / 定理 `range_eq_iff`

English:
theorem range_eq_iff
  given: (f : α -> β) (s : Set β)
  proof: by grind

中文:
定理 range_eq_iff
  条件: (f : α -> β) (s : Set β)
  证明: by grind
-/
theorem range_eq_iff (f : α -> β) (s : Set β) :
    range f = s ↔ (forall a, f a in s) ∧ forall b in s, exists a, f a = b := by grind

/--
theorem `range_comp_subset_range` / 定理 `range_comp_subset_range`

English:
theorem range_comp_subset_range
  given: (f : α -> β) (g : β -> γ)
  statement: range (g ∘ f) subseteq range g
  proof: by grind

中文:
定理 range_comp_subset_range
  条件: (f : α -> β) (g : β -> γ)
  结论: range (g ∘ f) subseteq range g
  证明: by grind
-/
theorem range_comp_subset_range (f : α -> β) (g : β -> γ) : range (g ∘ f) subseteq range g := by grind

/--
theorem `range_nonempty_iff_nonempty` / 定理 `range_nonempty_iff_nonempty`

English:
theorem range_nonempty_iff_nonempty
  statement: (range f).Nonempty ↔ Nonempty ι
  proof: ⟨fun ⟨_, x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩

中文:
定理 range_nonempty_iff_nonempty
  结论: (range f).Nonempty ↔ Nonempty ι
  证明: ⟨fun ⟨_, x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩

Depends on / 依赖: mem_range_self
-/
theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨_, x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩

/--
theorem `range_nonempty` / 定理 `range_nonempty`

English:
theorem range_nonempty
  given: [h : Nonempty ι] (f : ι -> α)
  statement: (range f).Nonempty
  proof: range_nonempty_iff_nonempty.2 h

@[simp]

中文:
定理 range_nonempty
  条件: [h : Nonempty ι] (f : ι -> α)
  结论: (range f).Nonempty
  证明: range_nonempty_iff_nonempty.2 h

@[simp]

Depends on / 依赖: range_nonempty_iff_nonempty
-/
theorem range_nonempty [h : Nonempty ι] (f : ι -> α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h

@[simp]
/--
theorem `range_eq_empty_iff` / 定理 `range_eq_empty_iff`

English:
theorem range_eq_empty_iff
  given: {f : ι -> α}
  statement: range f = ∅ ↔ IsEmpty ι
  proof: by
  rw [← not_nonempty_iff]; rw [← range_nonempty_iff_nonempty]; rw [not_nonempty_iff_eq_empty]

中文:
定理 range_eq_empty_iff
  条件: {f : ι -> α}
  结论: range f = ∅ ↔ IsEmpty ι
  证明: by
  rw [← not_nonempty_iff]; rw [← range_nonempty_iff_nonempty]; rw [not_nonempty_iff_eq_empty]

Depends on / 依赖: not_nonempty_iff, not_nonempty_iff_eq_empty, range_nonempty_iff_nonempty
-/
theorem range_eq_empty_iff {f : ι -> α} : range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff]; rw [← range_nonempty_iff_nonempty]; rw [not_nonempty_iff_eq_empty]

/--
theorem `range_eq_empty` / 定理 `range_eq_empty`

English:
theorem range_eq_empty
  given: [IsEmpty ι] (f : ι -> α)
  statement: range f = ∅
  proof: range_eq_empty_iff.2 ‹_›

@[simp]

中文:
定理 range_eq_empty
  条件: [IsEmpty ι] (f : ι -> α)
  结论: range f = ∅
  证明: range_eq_empty_iff.2 ‹_›

@[simp]

Depends on / 依赖: range_eq_empty_iff
-/
theorem range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›

@[simp]
/--
theorem `range_eq_singleton_iff` / 定理 `range_eq_singleton_iff`

English:
theorem range_eq_singleton_iff
  given: [Nonempty ι] {y}
  proof: by
  simp_rw [Set.ext_iff, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun h _ => by simp_rw [← h, exists_apply_eq_apply],
      fun h _ => by simp_rw [h, exists_const, eq_comm]⟩

中文:
定理 range_eq_singleton_iff
  条件: [Nonempty ι] {y}
  证明: by
  simp_rw [Set.ext_iff, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun h _ => by simp_rw [← h, exists_apply_eq_apply],
      fun h _ => by simp_rw [h, exists_const, eq_comm]⟩

Depends on / 依赖: Set.ext_iff, Set.mem_range, Set.mem_singleton_iff, eq_comm, exists_apply_eq_apply, exists_const, ext_iff, mem_range, mem_singleton_iff, simp_rw
-/
theorem range_eq_singleton_iff [Nonempty ι] {y} :
    Set.range f = {y} ↔ forall (x : ι), f x = y := by
  simp_rw [Set.ext_iff, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun h _ => by simp_rw [← h, exists_apply_eq_apply],
      fun h _ => by simp_rw [h, exists_const, eq_comm]⟩

/--
theorem `range_eq_singleton` / 定理 `range_eq_singleton`

English:
theorem range_eq_singleton
  given: [Nonempty ι] {y} (hy : forall (x : ι), f x = y)
  proof: range_eq_singleton_iff.mpr hy

中文:
定理 range_eq_singleton
  条件: [Nonempty ι] {y} (hy : 对任意 (x : ι), f x = y)
  证明: range_eq_singleton_iff.mpr hy

Depends on / 依赖: range_eq_singleton_iff, range_eq_singleton_iff.mpr
-/
theorem range_eq_singleton [Nonempty ι] {y} (hy : forall (x : ι), f x = y) :
    Set.range f = {y} := range_eq_singleton_iff.mpr hy

/--
Instance `instNonemptyRange` / 实例 `instNonemptyRange`

English:
instance instNonemptyRange
  signature: [Nonempty ι] (f : ι -> α)
  body: (range_nonempty f).to_subtype

@[simp]

中文:
实例 instNonemptyRange
  签名: [Nonempty ι] (f : ι -> α)
  定义体: (range_nonempty f).to_subtype

@[simp]

Depends on / 依赖: range_nonempty, to_subtype
-/
instance instNonemptyRange [Nonempty ι] (f : ι -> α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

@[simp]
/--
theorem `image_union_image_compl_eq_range` / 定理 `image_union_image_compl_eq_range`

English:
theorem image_union_image_compl_eq_range
  given: (f : α -> β)
  statement: f '' s union f '' sᶜ = range f
  proof: by grind

中文:
定理 image_union_image_compl_eq_range
  条件: (f : α -> β)
  结论: f '' s union f '' sᶜ = range f
  证明: by grind
-/
theorem image_union_image_compl_eq_range (f : α -> β) : f '' s union f '' sᶜ = range f := by grind

/--
theorem `insert_image_compl_eq_range` / 定理 `insert_image_compl_eq_range`

English:
theorem insert_image_compl_eq_range
  given: (f : α -> β) (x : α)
  statement: insert (f x) (f '' {x}ᶜ) = range f
  proof: by
  grind

中文:
定理 insert_image_compl_eq_range
  条件: (f : α -> β) (x : α)
  结论: insert (f x) (f '' {x}ᶜ) = range f
  证明: by
  grind
-/
theorem insert_image_compl_eq_range (f : α -> β) (x : α) : insert (f x) (f '' {x}ᶜ) = range f := by
  grind

/--
theorem `image_preimage_eq_range_inter` / 定理 `image_preimage_eq_range_inter`

English:
theorem image_preimage_eq_range_inter
  given: {f : α -> β} {t : Set β}
  statement: f '' f ⁻¹' t = range f inter t
  proof: by
  grind

中文:
定理 image_preimage_eq_range_inter
  条件: {f : α -> β} {t : Set β}
  结论: f '' f ⁻¹' t = range f inter t
  证明: by
  grind
-/
theorem image_preimage_eq_range_inter {f : α -> β} {t : Set β} : f '' f ⁻¹' t = range f inter t := by
  grind

/--
theorem `image_preimage_eq_inter_range` / 定理 `image_preimage_eq_inter_range`

English:
theorem image_preimage_eq_inter_range
  given: {f : α -> β} {t : Set β}
  statement: f '' f ⁻¹' t = t inter range f
  proof: by
  grind

中文:
定理 image_preimage_eq_inter_range
  条件: {f : α -> β} {t : Set β}
  结论: f '' f ⁻¹' t = t inter range f
  证明: by
  grind
-/
theorem image_preimage_eq_inter_range {f : α -> β} {t : Set β} : f '' f ⁻¹' t = t inter range f := by
  grind

/--
theorem `image_preimage_eq_of_subset` / 定理 `image_preimage_eq_of_subset`

English:
theorem image_preimage_eq_of_subset
  given: {f : α -> β} {s : Set β} (hs : s subseteq range f)
  proof: by grind

中文:
定理 image_preimage_eq_of_subset
  条件: {f : α -> β} {s : Set β} (hs : s subseteq range f)
  证明: by grind
-/
theorem image_preimage_eq_of_subset {f : α -> β} {s : Set β} (hs : s subseteq range f) :
    f '' f ⁻¹' s = s := by grind

/--
theorem `image_preimage_eq_iff` / 定理 `image_preimage_eq_iff`

English:
theorem image_preimage_eq_iff
  given: {f : α -> β} {s : Set β}
  statement: f '' f ⁻¹' s = s ↔ s subseteq range f
  proof: by grind

中文:
定理 image_preimage_eq_iff
  条件: {f : α -> β} {s : Set β}
  结论: f '' f ⁻¹' s = s ↔ s subseteq range f
  证明: by grind
-/
theorem image_preimage_eq_iff {f : α -> β} {s : Set β} : f '' f ⁻¹' s = s ↔ s subseteq range f := by grind

/--
theorem `subset_range_iff_exists_image_eq` / 定理 `subset_range_iff_exists_image_eq`

English:
theorem subset_range_iff_exists_image_eq
  given: {f : α -> β} {s : Set β}
  statement: s subseteq range f ↔ exists t, f '' t = s
  proof: ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨_, ht⟩ => ht ▸ image_subset_range _ _⟩

中文:
定理 subset_range_iff_exists_image_eq
  条件: {f : α -> β} {s : Set β}
  结论: s subseteq range f ↔ 存在 t, f '' t = s
  证明: ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨_, ht⟩ => ht ▸ image_subset_range _ _⟩

Depends on / 依赖: image_preimage_eq_iff, image_subset_range
-/
theorem subset_range_iff_exists_image_eq {f : α -> β} {s : Set β} : s subseteq range f ↔ exists t, f '' t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨_, ht⟩ => ht ▸ image_subset_range _ _⟩

/--
theorem `range_image` / 定理 `range_image`

English:
theorem range_image
  given: (f : α -> β)
  statement: range (image f) = 𝒫 range f
  proof: ext fun _ => subset_range_iff_exists_image_eq.symm

@[simp]

中文:
定理 range_image
  条件: (f : α -> β)
  结论: range (image f) = 𝒫 range f
  证明: ext fun _ => subset_range_iff_exists_image_eq.symm

@[simp]

Depends on / 依赖: subset_range_iff_exists_image_eq, subset_range_iff_exists_image_eq.symm
-/
theorem range_image (f : α -> β) : range (image f) = 𝒫 range f :=
  ext fun _ => subset_range_iff_exists_image_eq.symm

@[simp]
/--
theorem `exists_subset_range_and_iff` / 定理 `exists_subset_range_and_iff`

English:
theorem exists_subset_range_and_iff
  given: {f : α -> β} {p : Set β -> Prop}
  proof: by
  rw [← exists_range_iff]; rw [range_image]; rfl

@[simp]

中文:
定理 exists_subset_range_and_iff
  条件: {f : α -> β} {p : Set β -> 命题}
  证明: by
  rw [← exists_range_iff]; rw [range_image]; rfl

@[simp]

Depends on / 依赖: exists_range_iff, range_image
-/
theorem exists_subset_range_and_iff {f : α -> β} {p : Set β -> Prop} :
    (exists s, s subseteq range f ∧ p s) ↔ exists s, p (f '' s) := by
  rw [← exists_range_iff]; rw [range_image]; rfl

@[simp]
/--
theorem `forall_subset_range_iff` / 定理 `forall_subset_range_iff`

English:
theorem forall_subset_range_iff
  given: {f : α -> β} {p : Set β -> Prop}
  proof: by
  rw [← forall_mem_range]; rw [range_image]; simp only [mem_powerset_iff]

@[simp]

中文:
定理 forall_subset_range_iff
  条件: {f : α -> β} {p : Set β -> 命题}
  证明: by
  rw [← forall_mem_range]; rw [range_image]; simp only [mem_powerset_iff]

@[simp]

Depends on / 依赖: forall_mem_range, mem_powerset_iff, range_image
-/
theorem forall_subset_range_iff {f : α -> β} {p : Set β -> Prop} :
    (forall s, s subseteq range f -> p s) ↔ forall s, p (f '' s) := by
  rw [← forall_mem_range]; rw [range_image]; simp only [mem_powerset_iff]

@[simp]
/--
theorem `preimage_subset_preimage_iff` / 定理 `preimage_subset_preimage_iff`

English:
theorem preimage_subset_preimage_iff
  given: {s t : Set α} {f : β -> α} (hs : s subseteq range f)
  proof: by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h

中文:
定理 preimage_subset_preimage_iff
  条件: {s t : Set α} {f : β -> α} (hs : s subseteq range f)
  证明: by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h
-/
theorem preimage_subset_preimage_iff {s t : Set α} {f : β -> α} (hs : s subseteq range f) :
    f ⁻¹' s subseteq f ⁻¹' t ↔ s subseteq t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h

/--
theorem `preimage_eq_preimage'` / 定理 `preimage_eq_preimage'`

English:
theorem preimage_eq_preimage'
  given: {s t : Set α} {f : β -> α} (hs : s subseteq range f) (ht : t subseteq range f)
  proof: by
  constructor
  · intro h
    apply Subset.antisymm
    · rw [← preimage_subset_preimage_iff hs, h]
    · rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl

中文:
定理 preimage_eq_preimage'
  条件: {s t : Set α} {f : β -> α} (hs : s subseteq range f) (ht : t subseteq range f)
  证明: by
  constructor
  · intro h
    apply Subset.antisymm
    · rw [← preimage_subset_preimage_iff hs, h]
    · rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl

Depends on / 依赖: Subset, Subset.antisymm, antisymm, preimage_subset_preimage_iff
-/
theorem preimage_eq_preimage' {s t : Set α} {f : β -> α} (hs : s subseteq range f) (ht : t subseteq range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply Subset.antisymm
    · rw [← preimage_subset_preimage_iff hs, h]
    · rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl

-- Not `@[simp]` since `simp` can prove this.
/--
theorem `preimage_inter_range` / 定理 `preimage_inter_range`

English:
theorem preimage_inter_range
  given: {f : α -> β} {s : Set β}
  statement: f ⁻¹' (s inter range f) = f ⁻¹' s
  proof: Set.ext fun x => and_iff_left ⟨x, rfl⟩

中文:
定理 preimage_inter_range
  条件: {f : α -> β} {s : Set β}
  结论: f ⁻¹' (s inter range f) = f ⁻¹' s
  证明: Set.ext fun x => and_iff_left ⟨x, rfl⟩

Depends on / 依赖: Set.ext, and_iff_left
-/
theorem preimage_inter_range {f : α -> β} {s : Set β} : f ⁻¹' (s inter range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩

-- Not `@[simp]` since `simp` can prove this.
/--
theorem `preimage_range_inter` / 定理 `preimage_range_inter`

English:
theorem preimage_range_inter
  given: {f : α -> β} {s : Set β}
  statement: f ⁻¹' (range f inter s) = f ⁻¹' s
  proof: by
  rw [inter_comm]; rw [preimage_inter_range]

中文:
定理 preimage_range_inter
  条件: {f : α -> β} {s : Set β}
  结论: f ⁻¹' (range f inter s) = f ⁻¹' s
  证明: by
  rw [inter_comm]; rw [preimage_inter_range]

Depends on / 依赖: inter_comm, preimage_inter_range
-/
theorem preimage_range_inter {f : α -> β} {s : Set β} : f ⁻¹' (range f inter s) = f ⁻¹' s := by
  rw [inter_comm]; rw [preimage_inter_range]

/--
theorem `preimage_image_preimage` / 定理 `preimage_image_preimage`

English:
theorem preimage_image_preimage
  given: {f : α -> β} {s : Set β}
  statement: f ⁻¹' f '' f ⁻¹' s = f ⁻¹' s
  proof: by
  rw [image_preimage_eq_range_inter]; rw [preimage_range_inter]

@[simp, mfld_simps]

中文:
定理 preimage_image_preimage
  条件: {f : α -> β} {s : Set β}
  结论: f ⁻¹' f '' f ⁻¹' s = f ⁻¹' s
  证明: by
  rw [image_preimage_eq_range_inter]; rw [preimage_range_inter]

@[simp, mfld_simps]

Depends on / 依赖: image_preimage_eq_range_inter, preimage_range_inter
-/
theorem preimage_image_preimage {f : α -> β} {s : Set β} : f ⁻¹' f '' f ⁻¹' s = f ⁻¹' s := by
  rw [image_preimage_eq_range_inter]; rw [preimage_range_inter]

@[simp, mfld_simps]
/--
theorem `range_id` / 定理 `range_id`

English:
theorem range_id
  statement: range (@id α) = univ
  proof: range_eq_univ.2 surjective_id

@[simp, mfld_simps]

中文:
定理 range_id
  结论: range (@id α) = univ
  证明: range_eq_univ.2 surjective_id

@[simp, mfld_simps]

Depends on / 依赖: range_eq_univ, surjective_id
-/
theorem range_id : range (@id α) = univ :=
  range_eq_univ.2 surjective_id

@[simp, mfld_simps]
/--
theorem `range_id'` / 定理 `range_id'`

English:
theorem range_id'
  statement: (range fun x : α => x) = univ
  proof: range_id

@[simp]

中文:
定理 range_id'
  结论: (range fun x : α => x) = univ
  证明: range_id

@[simp]

Depends on / 依赖: range_id
-/
theorem range_id' : (range fun x : α => x) = univ :=
  range_id

@[simp]
/--
theorem `_root_.Prod.range_fst` / 定理 `_root_.Prod.range_fst`

English:
theorem _root_.Prod.range_fst
  given: [Nonempty β]
  statement: range (Prod.fst : α × β -> α) = univ
  proof: Prod.fst_surjective.range_eq

@[simp]

中文:
定理 _root_.Prod.range_fst
  条件: [Nonempty β]
  结论: range (Prod.fst : α × β -> α) = univ
  证明: Prod.fst_surjective.range_eq

@[simp]

Depends on / 依赖: Prod.fst_surjective.range_eq, fst_surjective, range_eq
-/
theorem _root_.Prod.range_fst [Nonempty β] : range (Prod.fst : α × β -> α) = univ :=
  Prod.fst_surjective.range_eq

@[simp]
/--
theorem `_root_.Prod.range_snd` / 定理 `_root_.Prod.range_snd`

English:
theorem _root_.Prod.range_snd
  given: [Nonempty α]
  statement: range (Prod.snd : α × β -> β) = univ
  proof: Prod.snd_surjective.range_eq

@[simp]

中文:
定理 _root_.Prod.range_snd
  条件: [Nonempty α]
  结论: range (Prod.snd : α × β -> β) = univ
  证明: Prod.snd_surjective.range_eq

@[simp]

Depends on / 依赖: Prod.snd_surjective.range_eq, range_eq, snd_surjective
-/
theorem _root_.Prod.range_snd [Nonempty α] : range (Prod.snd : α × β -> β) = univ :=
  Prod.snd_surjective.range_eq

@[simp]
/--
theorem `range_eval` / 定理 `range_eval`

English:
theorem range_eval
  given: {α : ι -> Sort _} [forall i, Nonempty (α i)] (i : ι)
  proof: (surjective_eval i).range_eq

中文:
定理 range_eval
  条件: {α : ι -> Sort _} [对任意 i, Nonempty (α i)] (i : ι)
  证明: (surjective_eval i).range_eq

Depends on / 依赖: range_eq, surjective_eval
-/
theorem range_eval {α : ι -> Sort _} [forall i, Nonempty (α i)] (i : ι) :
    range (eval i : (forall i, α i) -> α i) = univ :=
  (surjective_eval i).range_eq

/--
theorem `range_inl` / 定理 `range_inl`

English:
theorem range_inl
  statement: range (@Sum.inl α β) = {x | Sum.isLeft x}
  proof: by ext (_ | _) <;> simp

中文:
定理 range_inl
  结论: range (@Sum.inl α β) = {x | Sum.isLeft x}
  证明: by ext (_ | _) <;> simp
-/
theorem range_inl : range (@Sum.inl α β) = {x | Sum.isLeft x} := by ext (_ | _) <;> simp
/--
theorem `range_inr` / 定理 `range_inr`

English:
theorem range_inr
  statement: range (@Sum.inr α β) = {x | Sum.isRight x}
  proof: by ext (_ | _) <;> simp

中文:
定理 range_inr
  结论: range (@Sum.inr α β) = {x | Sum.isRight x}
  证明: by ext (_ | _) <;> simp
-/
theorem range_inr : range (@Sum.inr α β) = {x | Sum.isRight x} := by ext (_ | _) <;> simp

/--
theorem `isCompl_range_inl_range_inr` / 定理 `isCompl_range_inl_range_inr`

English:
theorem isCompl_range_inl_range_inr
  statement: IsCompl (range <| @Sum.inl α β) (range Sum.inr)
  proof: IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, h⟩⟩
      exact Sum.noConfusion rfl rfl (heq_of_eq h))
    (by rintro (x | y) - <;> [left; right] <;> exact mem_range_self _)

@[simp]

中文:
定理 isCompl_range_inl_range_inr
  结论: IsCompl (range <| @Sum.inl α β) (range Sum.inr)
  证明: IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, h⟩⟩
      exact Sum.noConfusion rfl rfl (heq_of_eq h))
    (by rintro (x | y) - <;> [left; right] <;> exact mem_range_self _)

@[simp]

Depends on / 依赖: IsCompl, IsCompl.of_le, Sum.noConfusion, heq_of_eq, mem_range_self, noConfusion, of_le
-/
theorem isCompl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.inr) :=
  IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, h⟩⟩
      exact Sum.noConfusion rfl rfl (heq_of_eq h))
    (by rintro (x | y) - <;> [left; right] <;> exact mem_range_self _)

@[simp]
/--
theorem `range_inl_union_range_inr` / 定理 `range_inl_union_range_inr`

English:
theorem range_inl_union_range_inr
  statement: range (Sum.inl : α -> α oplus β) union range Sum.inr = univ
  proof: isCompl_range_inl_range_inr.sup_eq_top

@[simp]

中文:
定理 range_inl_union_range_inr
  结论: range (Sum.inl : α -> α oplus β) union range Sum.inr = univ
  证明: isCompl_range_inl_range_inr.sup_eq_top

@[simp]

Depends on / 依赖: isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.sup_eq_top, sup_eq_top
-/
theorem range_inl_union_range_inr : range (Sum.inl : α -> α oplus β) union range Sum.inr = univ :=
  isCompl_range_inl_range_inr.sup_eq_top

@[simp]
/--
theorem `range_inl_inter_range_inr` / 定理 `range_inl_inter_range_inr`

English:
theorem range_inl_inter_range_inr
  statement: range (Sum.inl : α -> α oplus β) inter range Sum.inr = ∅
  proof: isCompl_range_inl_range_inr.inf_eq_bot

@[simp]

中文:
定理 range_inl_inter_range_inr
  结论: range (Sum.inl : α -> α oplus β) inter range Sum.inr = ∅
  证明: isCompl_range_inl_range_inr.inf_eq_bot

@[simp]

Depends on / 依赖: inf_eq_bot, isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.inf_eq_bot
-/
theorem range_inl_inter_range_inr : range (Sum.inl : α -> α oplus β) inter range Sum.inr = ∅ :=
  isCompl_range_inl_range_inr.inf_eq_bot

@[simp]
/--
theorem `range_inr_union_range_inl` / 定理 `range_inr_union_range_inl`

English:
theorem range_inr_union_range_inl
  statement: range (Sum.inr : β -> α oplus β) union range Sum.inl = univ
  proof: isCompl_range_inl_range_inr.symm.sup_eq_top

@[simp]

中文:
定理 range_inr_union_range_inl
  结论: range (Sum.inr : β -> α oplus β) union range Sum.inl = univ
  证明: isCompl_range_inl_range_inr.symm.sup_eq_top

@[simp]

Depends on / 依赖: isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.symm.sup_eq_top, sup_eq_top
-/
theorem range_inr_union_range_inl : range (Sum.inr : β -> α oplus β) union range Sum.inl = univ :=
  isCompl_range_inl_range_inr.symm.sup_eq_top

@[simp]
/--
theorem `range_inr_inter_range_inl` / 定理 `range_inr_inter_range_inl`

English:
theorem range_inr_inter_range_inl
  statement: range (Sum.inr : β -> α oplus β) inter range Sum.inl = ∅
  proof: isCompl_range_inl_range_inr.symm.inf_eq_bot

@[simp]

中文:
定理 range_inr_inter_range_inl
  结论: range (Sum.inr : β -> α oplus β) inter range Sum.inl = ∅
  证明: isCompl_range_inl_range_inr.symm.inf_eq_bot

@[simp]

Depends on / 依赖: inf_eq_bot, isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.symm.inf_eq_bot
-/
theorem range_inr_inter_range_inl : range (Sum.inr : β -> α oplus β) inter range Sum.inl = ∅ :=
  isCompl_range_inl_range_inr.symm.inf_eq_bot

@[simp]
/--
theorem `preimage_inl_image_inr` / 定理 `preimage_inl_image_inr`

English:
theorem preimage_inl_image_inr
  given: (s : Set β)
  statement: Sum.inl ⁻¹' @Sum.inr α β '' s = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 preimage_inl_image_inr
  条件: (s : Set β)
  结论: Sum.inl ⁻¹' @Sum.inr α β '' s = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' @Sum.inr α β '' s = ∅ := by
  ext
  simp

@[simp]
/--
theorem `preimage_inr_image_inl` / 定理 `preimage_inr_image_inl`

English:
theorem preimage_inr_image_inl
  given: (s : Set α)
  statement: Sum.inr ⁻¹' @Sum.inl α β '' s = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 preimage_inr_image_inl
  条件: (s : Set α)
  结论: Sum.inr ⁻¹' @Sum.inl α β '' s = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' @Sum.inl α β '' s = ∅ := by
  ext
  simp

@[simp]
/--
theorem `preimage_inl_range_inr` / 定理 `preimage_inl_range_inr`

English:
theorem preimage_inl_range_inr
  statement: Sum.inl ⁻¹' range (Sum.inr : β -> α oplus β) = ∅
  proof: by
  rw [← image_univ]; rw [preimage_inl_image_inr]

@[simp]

中文:
定理 preimage_inl_range_inr
  结论: Sum.inl ⁻¹' range (Sum.inr : β -> α oplus β) = ∅
  证明: by
  rw [← image_univ]; rw [preimage_inl_image_inr]

@[simp]

Depends on / 依赖: image_univ, preimage_inl_image_inr
-/
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β -> α oplus β) = ∅ := by
  rw [← image_univ]; rw [preimage_inl_image_inr]

@[simp]
/--
theorem `preimage_inr_range_inl` / 定理 `preimage_inr_range_inl`

English:
theorem preimage_inr_range_inl
  statement: Sum.inr ⁻¹' range (Sum.inl : α -> α oplus β) = ∅
  proof: by
  rw [← image_univ]; rw [preimage_inr_image_inl]

@[simp]

中文:
定理 preimage_inr_range_inl
  结论: Sum.inr ⁻¹' range (Sum.inl : α -> α oplus β) = ∅
  证明: by
  rw [← image_univ]; rw [preimage_inr_image_inl]

@[simp]

Depends on / 依赖: image_univ, preimage_inr_image_inl
-/
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α -> α oplus β) = ∅ := by
  rw [← image_univ]; rw [preimage_inr_image_inl]

@[simp]
/--
theorem `compl_range_inl` / 定理 `compl_range_inl`

English:
theorem compl_range_inl
  statement: (range (Sum.inl : α -> α oplus β))ᶜ = range (Sum.inr : β -> α oplus β)
  proof: IsCompl.compl_eq isCompl_range_inl_range_inr

@[simp]

中文:
定理 compl_range_inl
  结论: (range (Sum.inl : α -> α oplus β))ᶜ = range (Sum.inr : β -> α oplus β)
  证明: IsCompl.compl_eq isCompl_range_inl_range_inr

@[simp]

Depends on / 依赖: IsCompl, IsCompl.compl_eq, compl_eq, isCompl_range_inl_range_inr
-/
theorem compl_range_inl : (range (Sum.inl : α -> α oplus β))ᶜ = range (Sum.inr : β -> α oplus β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr

@[simp]
/--
theorem `compl_range_inr` / 定理 `compl_range_inr`

English:
theorem compl_range_inr
  statement: (range (Sum.inr : β -> α oplus β))ᶜ = range (Sum.inl : α -> α oplus β)
  proof: IsCompl.compl_eq isCompl_range_inl_range_inr.symm

中文:
定理 compl_range_inr
  结论: (range (Sum.inr : β -> α oplus β))ᶜ = range (Sum.inl : α -> α oplus β)
  证明: IsCompl.compl_eq isCompl_range_inl_range_inr.symm

Depends on / 依赖: IsCompl, IsCompl.compl_eq, compl_eq, isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.symm
-/
theorem compl_range_inr : (range (Sum.inr : β -> α oplus β))ᶜ = range (Sum.inl : α -> α oplus β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr.symm

/--
theorem `preimage_sumElim` / 定理 `preimage_sumElim`

English:
theorem preimage_sumElim
  given: (s : Set γ) (f : α -> γ) (g : β -> γ)
  proof: by
  ext (_ | _) <;> simp

中文:
定理 preimage_sumElim
  条件: (s : Set γ) (f : α -> γ) (g : β -> γ)
  证明: by
  ext (_ | _) <;> simp
-/
theorem preimage_sumElim (s : Set γ) (f : α -> γ) (g : β -> γ) :
    Sum.elim f g ⁻¹' s = Sum.inl '' f ⁻¹' s union Sum.inr '' g ⁻¹' s := by
  ext (_ | _) <;> simp

/--
theorem `image_preimage_inl_union_image_preimage_inr` / 定理 `image_preimage_inl_union_image_preimage_inr`

English:
theorem image_preimage_inl_union_image_preimage_inr
  given: (s : Set (α oplus β))
  proof: by
  rw [← preimage_sumElim]; rw [Sum.elim_inl_inr]; rw [preimage_id]

中文:
定理 image_preimage_inl_union_image_preimage_inr
  条件: (s : Set (α oplus β))
  证明: by
  rw [← preimage_sumElim]; rw [Sum.elim_inl_inr]; rw [preimage_id]

Depends on / 依赖: Sum.elim_inl_inr, elim_inl_inr, preimage_id, preimage_sumElim
-/
theorem image_preimage_inl_union_image_preimage_inr (s : Set (α oplus β)) :
    Sum.inl '' Sum.inl ⁻¹' s union Sum.inr '' Sum.inr ⁻¹' s = s := by
  rw [← preimage_sumElim]; rw [Sum.elim_inl_inr]; rw [preimage_id]

/--
theorem `image_sumElim` / 定理 `image_sumElim`

English:
theorem image_sumElim
  given: (s : Set (α oplus β)) (f : α -> γ) (g : β -> γ)
  proof: by
  grind

@[simp]

中文:
定理 image_sumElim
  条件: (s : Set (α oplus β)) (f : α -> γ) (g : β -> γ)
  证明: by
  grind

@[simp]
-/
theorem image_sumElim (s : Set (α oplus β)) (f : α -> γ) (g : β -> γ) :
    Sum.elim f g '' s = f '' Sum.inl ⁻¹' s union g '' Sum.inr ⁻¹' s := by
  grind

@[simp]
/--
theorem `range_quot_mk` / 定理 `range_quot_mk`

English:
theorem range_quot_mk
  given: (r : α -> α -> Prop)
  statement: range (Quot.mk r) = univ
  proof: Quot.mk_surjective.range_eq

@[simp]

中文:
定理 range_quot_mk
  条件: (r : α -> α -> 命题)
  结论: range (Quot.mk r) = univ
  证明: Quot.mk_surjective.range_eq

@[simp]

Depends on / 依赖: Quot.mk_surjective.range_eq, mk_surjective, range_eq
-/
theorem range_quot_mk (r : α -> α -> Prop) : range (Quot.mk r) = univ :=
  Quot.mk_surjective.range_eq

@[simp]
/--
theorem `range_quot_lift` / 定理 `range_quot_lift`

English:
theorem range_quot_lift
  given: {r : ι -> ι -> Prop} (hf : forall x y, r x y -> f x = f y)
  proof: ext fun _ => Quot.mk_surjective.exists

@[simp]

中文:
定理 range_quot_lift
  条件: {r : ι -> ι -> 命题} (hf : 对任意 x y, r x y -> f x = f y)
  证明: ext fun _ => Quot.mk_surjective.exists

@[simp]

Depends on / 依赖: Quot.mk_surjective.exists, mk_surjective
-/
theorem range_quot_lift {r : ι -> ι -> Prop} (hf : forall x y, r x y -> f x = f y) :
    range (Quot.lift f hf) = range f :=
  ext fun _ => Quot.mk_surjective.exists

@[simp]
/--
theorem `range_quotient_mk` / 定理 `range_quotient_mk`

English:
theorem range_quotient_mk
  given: {s : Setoid α}
  statement: range (Quotient.mk s) = univ
  proof: range_quot_mk _

@[simp]

中文:
定理 range_quotient_mk
  条件: {s : Setoid α}
  结论: range (Quotient.mk s) = univ
  证明: range_quot_mk _

@[simp]

Depends on / 依赖: range_quot_mk
-/
theorem range_quotient_mk {s : Setoid α} : range (Quotient.mk s) = univ :=
  range_quot_mk _

@[simp]
/--
theorem `range_quotient_lift` / 定理 `range_quotient_lift`

English:
theorem range_quotient_lift
  given: [s : Setoid ι] (hf)
  proof: range_quot_lift _

@[simp]

中文:
定理 range_quotient_lift
  条件: [s : Setoid ι] (hf)
  证明: range_quot_lift _

@[simp]

Depends on / 依赖: range_quot_lift
-/
theorem range_quotient_lift [s : Setoid ι] (hf) :
    range (Quotient.lift f hf : Quotient s -> α) = range f :=
  range_quot_lift _

@[simp]
/--
theorem `range_quotient_mk'` / 定理 `range_quotient_mk'`

English:
theorem range_quotient_mk'
  given: {s : Setoid α}
  statement: range (Quotient.mk' : α -> Quotient s) = univ
  proof: range_quot_mk _

中文:
定理 range_quotient_mk'
  条件: {s : Setoid α}
  结论: range (Quotient.mk' : α -> Quotient s) = univ
  证明: range_quot_mk _

Depends on / 依赖: range_quot_mk
-/
theorem range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α -> Quotient s) = univ :=
  range_quot_mk _

/--
lemma `Quotient.range_mk''` / 引理 `Quotient.range_mk''`

English:
lemma Quotient.range_mk''
  given: {sa : Setoid α}
  statement: range (Quotient.mk'' (s₁ := sa)) = univ
  proof: range_quotient_mk

@[simp]

中文:
引理 Quotient.range_mk''
  条件: {sa : Setoid α}
  结论: range (Quotient.mk'' (s₁ := sa)) = univ
  证明: range_quotient_mk

@[simp]
-/
lemma Quotient.range_mk'' {sa : Setoid α} : range (Quotient.mk'' (s₁ := sa)) = univ :=
  range_quotient_mk

@[simp]
/--
theorem `range_quotient_lift_on'` / 定理 `range_quotient_lift_on'`

English:
theorem range_quotient_lift_on'
  given: {s : Setoid ι} (hf)
  proof: range_quot_lift _

中文:
定理 range_quotient_lift_on'
  条件: {s : Setoid ι} (hf)
  证明: range_quot_lift _

Depends on / 依赖: range_quot_lift
-/
theorem range_quotient_lift_on' {s : Setoid ι} (hf) :
    (range fun x : Quotient s => Quotient.liftOn' x f hf) = range f :=
  range_quot_lift _

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: (c) (p) [CanLift α β c p]
  body: subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)

中文:
实例 canLift
  签名: (c) (p) [CanLift α β c p]
  定义体: subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)

Depends on / 依赖: CanLift, CanLift.prf, subset_range_iff_exists_image_eq, subset_range_iff_exists_image_eq.mp
-/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Set α) (Set β) (c '' ·) fun s => forall x in s, p x where
  prf _ hs := subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)

/--
theorem `range_const_subset` / 定理 `range_const_subset`

English:
theorem range_const_subset
  given: {c : α}
  statement: (range fun _ : ι => c) subseteq {c}
  proof: range_subset_iff.2 fun _ => rfl

@[simp]

中文:
定理 range_const_subset
  条件: {c : α}
  结论: (range fun _ : ι => c) subseteq {c}
  证明: range_subset_iff.2 fun _ => rfl

@[simp]

Depends on / 依赖: range_subset_iff
-/
theorem range_const_subset {c : α} : (range fun _ : ι => c) subseteq {c} :=
  range_subset_iff.2 fun _ => rfl

@[simp]
/--
theorem `range_const` / 定理 `range_const`

English:
theorem range_const
  statement: forall [Nonempty ι] {c : α}, (range fun _ : ι => c) = {c}
  proof: range_eq_singleton (fun _ => rfl)

中文:
定理 range_const
  结论: 对任意 [Nonempty ι] {c : α}, (range fun _ : ι => c) = {c}
  证明: range_eq_singleton (fun _ => rfl)

Depends on / 依赖: range_eq_singleton
-/
theorem range_const : forall [Nonempty ι] {c : α}, (range fun _ : ι => c) = {c} :=
  range_eq_singleton (fun _ => rfl)

/--
theorem `range_subtype_map` / 定理 `range_subtype_map`

English:
theorem range_subtype_map
  given: {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall x, p x -> q (f x))
  proof: by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map]
  simp only [Subtype.mk.injEq, exists_prop, mem_ofPred_eq]

中文:
定理 range_subtype_map
  条件: {p : α -> 命题} {q : β -> 命题} (f : α -> β) (h : 对任意 x, p x -> q (f x))
  证明: by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map]
  simp only [Subtype.mk.injEq, exists_prop, mem_ofPred_eq]

Depends on / 依赖: Subtype, Subtype.exists, Subtype.map, Subtype.mk.injEq, exists_prop, mem_image, mem_ofPred_eq, mem_preimage, mem_range, simp_rw
-/
theorem range_subtype_map {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall x, p x -> q (f x)) :
    range (Subtype.map f h) = (↑) ⁻¹' f '' { x | p x } := by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map]
  simp only [Subtype.mk.injEq, exists_prop, mem_ofPred_eq]

/--
theorem `image_swap_eq_preimage_swap` / 定理 `image_swap_eq_preimage_swap`

English:
theorem image_swap_eq_preimage_swap
  statement: image (@Prod.swap α β) = preimage Prod.swap
  proof: image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse

中文:
定理 image_swap_eq_preimage_swap
  结论: image (@Prod.swap α β) = preimage Prod.swap
  证明: image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse

Depends on / 依赖: Prod.swap_leftInverse, Prod.swap_rightInverse, image_eq_preimage_of_inverse, swap_leftInverse, swap_rightInverse
-/
theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse

/--
theorem `preimage_singleton_nonempty` / 定理 `preimage_singleton_nonempty`

English:
theorem preimage_singleton_nonempty
  given: {f : α -> β} {y : β}
  statement: (f ⁻¹' {y}).Nonempty ↔ y in range f
  proof: Iff.rfl

中文:
定理 preimage_singleton_nonempty
  条件: {f : α -> β} {y : β}
  结论: (f ⁻¹' {y}).Nonempty ↔ y in range f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem preimage_singleton_nonempty {f : α -> β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y in range f :=
  Iff.rfl

/--
theorem `preimage_singleton_eq_empty` / 定理 `preimage_singleton_eq_empty`

English:
theorem preimage_singleton_eq_empty
  given: {f : α -> β} {y : β}
  statement: f ⁻¹' {y} = ∅ ↔ y ∉ range f
  proof: not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not

中文:
定理 preimage_singleton_eq_empty
  条件: {f : α -> β} {y : β}
  结论: f ⁻¹' {y} = ∅ ↔ y ∉ range f
  证明: not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not

Depends on / 依赖: not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.symm.trans, preimage_singleton_nonempty, preimage_singleton_nonempty.not
-/
theorem preimage_singleton_eq_empty {f : α -> β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not

/--
theorem `range_subset_singleton` / 定理 `range_subset_singleton`

English:
theorem range_subset_singleton
  given: {f : ι -> α} {x : α}
  statement: range f subseteq {x} ↔ f = const ι x
  proof: by
  simp [funext_iff]

中文:
定理 range_subset_singleton
  条件: {f : ι -> α} {x : α}
  结论: range f subseteq {x} ↔ f = const ι x
  证明: by
  simp [funext_iff]

Depends on / 依赖: funext_iff
-/
theorem range_subset_singleton {f : ι -> α} {x : α} : range f subseteq {x} ↔ f = const ι x := by
  simp [funext_iff]

/--
theorem `image_compl_preimage` / 定理 `image_compl_preimage`

English:
theorem image_compl_preimage
  given: {f : α -> β} {s : Set β}
  statement: f '' (f ⁻¹' s)ᶜ = range f \ s
  proof: by
  rw [compl_eq_univ_sdiff]; rw [image_sdiff_preimage]; rw [image_univ]

中文:
定理 image_compl_preimage
  条件: {f : α -> β} {s : Set β}
  结论: f '' (f ⁻¹' s)ᶜ = range f \ s
  证明: by
  rw [compl_eq_univ_sdiff]; rw [image_sdiff_preimage]; rw [image_univ]

Depends on / 依赖: compl_eq_univ_sdiff, image_sdiff_preimage, image_univ
-/
theorem image_compl_preimage {f : α -> β} {s : Set β} : f '' (f ⁻¹' s)ᶜ = range f \ s := by
  rw [compl_eq_univ_sdiff]; rw [image_sdiff_preimage]; rw [image_univ]

/--
theorem `rangeFactorization_eq` / 定理 `rangeFactorization_eq`

English:
theorem rangeFactorization_eq
  given: {f : ι -> β}
  statement: Subtype.val ∘ rangeFactorization f = f
  proof: funext fun _ => rfl

@[simp]

中文:
定理 rangeFactorization_eq
  条件: {f : ι -> β}
  结论: Subtype.val ∘ rangeFactorization f = f
  证明: funext fun _ => rfl

@[simp]
-/
theorem rangeFactorization_eq {f : ι -> β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun _ => rfl

@[simp]
/--
theorem `rangeFactorization_coe` / 定理 `rangeFactorization_coe`

English:
theorem rangeFactorization_coe
  given: (f : ι -> β) (a : ι)
  statement: (rangeFactorization f a : β) = f a
  proof: rfl

@[simp]

中文:
定理 rangeFactorization_coe
  条件: (f : ι -> β) (a : ι)
  结论: (rangeFactorization f a : β) = f a
  证明: rfl

@[simp]
-/
theorem rangeFactorization_coe (f : ι -> β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl

@[simp]
/--
theorem `coe_comp_rangeFactorization` / 定理 `coe_comp_rangeFactorization`

English:
theorem coe_comp_rangeFactorization
  given: (f : ι -> β)
  statement: (↑) ∘ rangeFactorization f = f
  proof: rfl

中文:
定理 coe_comp_rangeFactorization
  条件: (f : ι -> β)
  结论: (↑) ∘ rangeFactorization f = f
  证明: rfl
-/
theorem coe_comp_rangeFactorization (f : ι -> β) : (↑) ∘ rangeFactorization f = f := rfl

/--
theorem `image_eq_range` / 定理 `image_eq_range`

English:
theorem image_eq_range
  given: (f : α -> β) (s : Set α)
  statement: f '' s = range fun x : s => f x
  proof: by
  ext
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩
  · rintro ⟨⟨x, h1⟩, h2⟩
    exact ⟨x, h1, h2⟩

中文:
定理 image_eq_range
  条件: (f : α -> β) (s : Set α)
  结论: f '' s = range fun x : s => f x
  证明: by
  ext
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩
  · rintro ⟨⟨x, h1⟩, h2⟩
    exact ⟨x, h1, h2⟩
-/
theorem image_eq_range (f : α -> β) (s : Set α) : f '' s = range fun x : s => f x := by
  ext
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩
  · rintro ⟨⟨x, h1⟩, h2⟩
    exact ⟨x, h1, h2⟩

/--
theorem `_root_.Sum.range_eq` / 定理 `_root_.Sum.range_eq`

English:
theorem _root_.Sum.range_eq
  given: (f : α oplus β -> γ)
  proof: ext fun _ => Sum.exists

@[simp]

中文:
定理 _root_.Sum.range_eq
  条件: (f : α oplus β -> γ)
  证明: ext fun _ => Sum.exists

@[simp]

Depends on / 依赖: Sum.exists
-/
theorem _root_.Sum.range_eq (f : α oplus β -> γ) :
    range f = range (f ∘ Sum.inl) union range (f ∘ Sum.inr) :=
  ext fun _ => Sum.exists

@[simp]
/--
theorem `Sum.elim_range` / 定理 `Sum.elim_range`

English:
theorem Sum.elim_range
  given: (f : α -> γ) (g : β -> γ)
  statement: range (Sum.elim f g) = range f union range g
  proof: Sum.range_eq _

中文:
定理 Sum.elim_range
  条件: (f : α -> γ) (g : β -> γ)
  结论: range (Sum.elim f g) = range f union range g
  证明: Sum.range_eq _

Depends on / 依赖: Sum.range_eq, range_eq
-/
theorem Sum.elim_range (f : α -> γ) (g : β -> γ) : range (Sum.elim f g) = range f union range g :=
  Sum.range_eq _

/--
theorem `range_ite_subset'` / 定理 `range_ite_subset'`

English:
theorem range_ite_subset'
  given: {p : Prop} [Decidable p] {f g : α -> β}
  proof: by grind

中文:
定理 range_ite_subset'
  条件: {p : 命题} [Decidable p] {f g : α -> β}
  证明: by grind
-/
theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α -> β} :
    range (if p then f else g) subseteq range f union range g := by grind

/--
theorem `range_ite_subset` / 定理 `range_ite_subset`

English:
theorem range_ite_subset
  given: {p : α -> Prop} [DecidablePred p] {f g : α -> β}
  proof: by grind

@[simp]

中文:
定理 range_ite_subset
  条件: {p : α -> 命题} [DecidablePred p] {f g : α -> β}
  证明: by grind

@[simp]
-/
theorem range_ite_subset {p : α -> Prop} [DecidablePred p] {f g : α -> β} :
    (range fun x => if p x then f x else g x) subseteq range f union range g := by grind

@[simp]
/--
theorem `preimage_range` / 定理 `preimage_range`

English:
theorem preimage_range
  given: (f : α -> β)
  statement: f ⁻¹' range f = univ
  proof: eq_univ_of_forall mem_range_self

中文:
定理 preimage_range
  条件: (f : α -> β)
  结论: f ⁻¹' range f = univ
  证明: eq_univ_of_forall mem_range_self

Depends on / 依赖: eq_univ_of_forall, mem_range_self
-/
theorem preimage_range (f : α -> β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self

/--
theorem `range_unique` / 定理 `range_unique`

English:
theorem range_unique
  given: [Unique ι]
  statement: range f = {f default}
  proof: by
  aesop (add simp [Unique.eq_default])

@[simp]

中文:
定理 range_unique
  条件: [Unique ι]
  结论: range f = {f default}
  证明: by
  aesop (add simp [Unique.eq_default])

@[simp]

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
theorem range_unique [Unique ι] : range f = {f default} := by
  aesop (add simp [Unique.eq_default])

@[simp]
/--
theorem `range_singleton` / 定理 `range_singleton`

English:
theorem range_singleton
  given: {x : α} (f : ({x} : Set α) -> β)
  statement: range f = {f ⟨x, mem_singleton x⟩}
  proof: range_unique

@[simp]

中文:
定理 range_singleton
  条件: {x : α} (f : ({x} : Set α) -> β)
  结论: range f = {f ⟨x, mem_singleton x⟩}
  证明: range_unique

@[simp]

Depends on / 依赖: range_unique
-/
theorem range_singleton {x : α} (f : ({x} : Set α) -> β) : range f = {f ⟨x, mem_singleton x⟩} :=
  range_unique

@[simp]
/--
theorem `range_insert` / 定理 `range_insert`

English:
theorem range_insert
  given: {x : α} {s : Set α} (f : ((insert x s) : Set α) -> β)
  proof: by
  aesop

中文:
定理 range_insert
  条件: {x : α} {s : Set α} (f : ((insert x s) : Set α) -> β)
  证明: by
  aesop
-/
theorem range_insert {x : α} {s : Set α} (f : ((insert x s) : Set α) -> β) :
    range f = insert (f ⟨x, mem_insert x s⟩)
      (range fun y : s => f ⟨y, mem_insert_of_mem _ y.2⟩) := by
  aesop

/--
theorem `range_sdiff_image_subset` / 定理 `range_sdiff_image_subset`

English:
theorem range_sdiff_image_subset
  given: (f : α -> β) (s : Set α)
  statement: range f \ f '' s subseteq f '' sᶜ
  proof: fun _ ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

@[deprecated (since := "2026-06-03")] alias range_diff_image_subset := range_sdiff_image_subset

@[simp]

中文:
定理 range_sdiff_image_subset
  条件: (f : α -> β) (s : Set α)
  结论: range f \ f '' s subseteq f '' sᶜ
  证明: fun _ ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

@[deprecated (since := "2026-06-03")] alias range_diff_image_subset := range_sdiff_image_subset

@[simp]
-/
theorem range_sdiff_image_subset (f : α -> β) (s : Set α) : range f \ f '' s subseteq f '' sᶜ :=
  fun _ ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

@[deprecated (since := "2026-06-03")] alias range_diff_image_subset := range_sdiff_image_subset

@[simp]
/--
theorem `range_inclusion` / 定理 `range_inclusion`

English:
theorem range_inclusion
  given: (h : s subseteq t)
  statement: range (inclusion h) = { x : t | (x : α) in s }
  proof: by
  ext ⟨x, hx⟩
  simp

中文:
定理 range_inclusion
  条件: (h : s subseteq t)
  结论: range (inclusion h) = { x : t | (x : α) in s }
  证明: by
  ext ⟨x, hx⟩
  simp
-/
theorem range_inclusion (h : s subseteq t) : range (inclusion h) = { x : t | (x : α) in s } := by
  ext ⟨x, hx⟩
  simp

-- When `f` is injective, see also `Equiv.ofInjective`.
/--
theorem `leftInverse_rangeSplitting` / 定理 `leftInverse_rangeSplitting`

English:
theorem leftInverse_rangeSplitting
  given: (f : α -> β)
  proof: fun x => by
  ext
  simp only [rangeFactorization_coe]
  apply apply_rangeSplitting

中文:
定理 leftInverse_rangeSplitting
  条件: (f : α -> β)
  证明: fun x => by
  ext
  simp only [rangeFactorization_coe]
  apply apply_rangeSplitting

Depends on / 依赖: apply_rangeSplitting, rangeFactorization_coe
-/
theorem leftInverse_rangeSplitting (f : α -> β) :
    LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x => by
  ext
  simp only [rangeFactorization_coe]
  apply apply_rangeSplitting

/--
theorem `rangeSplitting_injective` / 定理 `rangeSplitting_injective`

English:
theorem rangeSplitting_injective
  given: (f : α -> β)
  statement: Injective (rangeSplitting f)
  proof: (leftInverse_rangeSplitting f).injective

中文:
定理 rangeSplitting_injective
  条件: (f : α -> β)
  结论: Injective (rangeSplitting f)
  证明: (leftInverse_rangeSplitting f).injective

Depends on / 依赖: injective, leftInverse_rangeSplitting
-/
theorem rangeSplitting_injective (f : α -> β) : Injective (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).injective

/--
theorem `rightInverse_rangeSplitting` / 定理 `rightInverse_rangeSplitting`

English:
theorem rightInverse_rangeSplitting
  given: {f : α -> β} (h : Injective f)
  proof: (leftInverse_rangeSplitting f).rightInverse_of_injective fun _ _ hxy =>
h Subtype.ext_iff.1 hxy

@[simp]

中文:
定理 rightInverse_rangeSplitting
  条件: {f : α -> β} (h : Injective f)
  证明: (leftInverse_rangeSplitting f).rightInverse_of_injective fun _ _ hxy =>
h Subtype.ext_iff.1 hxy

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, leftInverse_rangeSplitting, rightInverse_of_injective
-/
theorem rightInverse_rangeSplitting {f : α -> β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).rightInverse_of_injective fun _ _ hxy =>
h Subtype.ext_iff.1 hxy

@[simp]
/--
lemma `leftInverse_rangeFactorization_iff_injective` / 引理 `leftInverse_rangeFactorization_iff_injective`

English:
lemma leftInverse_rangeFactorization_iff_injective
  given: (f : α -> β)
  proof: ⟨(rangeFactorization_injective.mp ·.injective),
    fun h => congrFun' (rightInverse_rangeSplitting h).id⟩

中文:
引理 leftInverse_rangeFactorization_iff_injective
  条件: (f : α -> β)
  证明: ⟨(rangeFactorization_injective.mp ·.injective),
    fun h => congrFun' (rightInverse_rangeSplitting h).id⟩

Depends on / 依赖: injective, rangeFactorization_injective, rangeFactorization_injective.mp, rightInverse_rangeSplitting
-/
lemma leftInverse_rangeFactorization_iff_injective (f : α -> β) :
    LeftInverse (rangeSplitting f) (rangeFactorization f) ↔ f.Injective :=
  ⟨(rangeFactorization_injective.mp ·.injective),
    fun h => congrFun' (rightInverse_rangeSplitting h).id⟩

/--
theorem `preimage_rangeSplitting` / 定理 `preimage_rangeSplitting`

English:
theorem preimage_rangeSplitting
  given: {f : α -> β} (hf : Injective f)
  proof: (image_eq_preimage_of_inverse (rightInverse_rangeSplitting hf)
      (leftInverse_rangeSplitting f)).symm

中文:
定理 preimage_rangeSplitting
  条件: {f : α -> β} (hf : Injective f)
  证明: (image_eq_preimage_of_inverse (rightInverse_rangeSplitting hf)
      (leftInverse_rangeSplitting f)).symm

Depends on / 依赖: image_eq_preimage_of_inverse, leftInverse_rangeSplitting, rightInverse_rangeSplitting
-/
theorem preimage_rangeSplitting {f : α -> β} (hf : Injective f) :
    preimage (rangeSplitting f) = image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (rightInverse_rangeSplitting hf)
      (leftInverse_rangeSplitting f)).symm

/--
theorem `rangeSplitting_strictMono` / 定理 `rangeSplitting_strictMono`

English:
theorem rangeSplitting_strictMono
  given: [LinearOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: by
  refine fun x y h => hf.reflect_lt ?_
  simpa [apply_rangeSplitting f]

中文:
定理 rangeSplitting_strictMono
  条件: [LinearOrder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  证明: by
  refine fun x y h => hf.reflect_lt ?_
  simpa [apply_rangeSplitting f]

Depends on / 依赖: apply_rangeSplitting, hf.reflect_lt, reflect_lt
-/
theorem rangeSplitting_strictMono [LinearOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) :
    StrictMono (rangeSplitting f) := by
  refine fun x y h => hf.reflect_lt ?_
  simpa [apply_rangeSplitting f]

/--
theorem `isCompl_range_some_none` / 定理 `isCompl_range_some_none`

English:
theorem isCompl_range_some_none
  given: (α : Type*)
  statement: IsCompl (range (some : α -> Option α)) {none}
  proof: IsCompl.of_le (fun _ ⟨⟨_, ha⟩, (hn : _ = none)⟩ => Option.some_ne_none _ (ha.trans hn))
fun x _ => Option.casesOn x (Or.inr rfl) fun _ => Or.inl mem_range_self _

@[simp]

中文:
定理 isCompl_range_some_none
  条件: (α : 类型)
  结论: IsCompl (range (some : α -> Option α)) {none}
  证明: IsCompl.of_le (fun _ ⟨⟨_, ha⟩, (hn : _ = none)⟩ => Option.some_ne_none _ (ha.trans hn))
fun x _ => Option.casesOn x (Or.inr rfl) fun _ => Or.inl mem_range_self _

@[simp]

Depends on / 依赖: IsCompl, IsCompl.of_le, Option.casesOn, Option.some_ne_none, Or.inl, Or.inr, casesOn, ha.trans, mem_range_self, of_le, some_ne_none
-/
theorem isCompl_range_some_none (α : Type*) : IsCompl (range (some : α -> Option α)) {none} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, (hn : _ = none)⟩ => Option.some_ne_none _ (ha.trans hn))
fun x _ => Option.casesOn x (Or.inr rfl) fun _ => Or.inl mem_range_self _

@[simp]
/--
theorem `compl_range_some` / 定理 `compl_range_some`

English:
theorem compl_range_some
  given: (α : Type*)
  statement: (range (some : α -> Option α))ᶜ = {none}
  proof: (isCompl_range_some_none α).compl_eq

@[simp]

中文:
定理 compl_range_some
  条件: (α : 类型)
  结论: (range (some : α -> Option α))ᶜ = {none}
  证明: (isCompl_range_some_none α).compl_eq

@[simp]

Depends on / 依赖: compl_eq, isCompl_range_some_none
-/
theorem compl_range_some (α : Type*) : (range (some : α -> Option α))ᶜ = {none} :=
  (isCompl_range_some_none α).compl_eq

@[simp]
/--
theorem `range_some_inter_none` / 定理 `range_some_inter_none`

English:
theorem range_some_inter_none
  given: (α : Type*)
  statement: range (some : α -> Option α) inter {none} = ∅
  proof: (isCompl_range_some_none α).inf_eq_bot

中文:
定理 range_some_inter_none
  条件: (α : 类型)
  结论: range (some : α -> Option α) inter {none} = ∅
  证明: (isCompl_range_some_none α).inf_eq_bot

Depends on / 依赖: inf_eq_bot, isCompl_range_some_none
-/
theorem range_some_inter_none (α : Type*) : range (some : α -> Option α) inter {none} = ∅ :=
  (isCompl_range_some_none α).inf_eq_bot

-- Not `@[simp]` since `simp` can prove this.
/--
theorem `range_some_union_none` / 定理 `range_some_union_none`

English:
theorem range_some_union_none
  given: (α : Type*)
  statement: range (some : α -> Option α) union {none} = univ
  proof: (isCompl_range_some_none α).sup_eq_top

@[simp]

中文:
定理 range_some_union_none
  条件: (α : 类型)
  结论: range (some : α -> Option α) union {none} = univ
  证明: (isCompl_range_some_none α).sup_eq_top

@[simp]

Depends on / 依赖: isCompl_range_some_none, sup_eq_top
-/
theorem range_some_union_none (α : Type*) : range (some : α -> Option α) union {none} = univ :=
  (isCompl_range_some_none α).sup_eq_top

@[simp]
/--
theorem `insert_none_range_some` / 定理 `insert_none_range_some`

English:
theorem insert_none_range_some
  given: (α : Type*)
  statement: insert none (range (some : α -> Option α)) = univ
  proof: (isCompl_range_some_none α).symm.sup_eq_top

中文:
定理 insert_none_range_some
  条件: (α : 类型)
  结论: insert none (range (some : α -> Option α)) = univ
  证明: (isCompl_range_some_none α).symm.sup_eq_top

Depends on / 依赖: isCompl_range_some_none, sup_eq_top, symm.sup_eq_top
-/
theorem insert_none_range_some (α : Type*) : insert none (range (some : α -> Option α)) = univ :=
  (isCompl_range_some_none α).symm.sup_eq_top

/--
lemma `image_of_range_union_range_eq_univ` / 引理 `image_of_range_union_range_eq_univ`

English:
lemma image_of_range_union_range_eq_univ
  statement: {α β γ γ' δ δ' : Type*}
  proof: by
  rw [← image_comp]; rw [← image_comp]; rw [← hf]; rw [← hg]; rw [image_comp]; rw [image_comp]; rw [image_preimage_eq_inter_range]; rw [image_preimage_eq_inter_range]; rw [← image_union]; rw [← inter_union_distrib_left]; rw [hfg]; rw [inter_univ]

中文:
引理 image_of_range_union_range_eq_univ
  结论: {α β γ γ' δ δ' : 类型}
  证明: by
  rw [← image_comp]; rw [← image_comp]; rw [← hf]; rw [← hg]; rw [image_comp]; rw [image_comp]; rw [image_preimage_eq_inter_range]; rw [image_preimage_eq_inter_range]; rw [← image_union]; rw [← inter_union_distrib_left]; rw [hfg]; rw [inter_univ]

Depends on / 依赖: image_comp, image_preimage_eq_inter_range, image_union, inter_union_distrib_left, inter_univ
-/
lemma image_of_range_union_range_eq_univ {α β γ γ' δ δ' : Type*}
    {h : β -> α} {f : γ -> β} {f₁ : γ' -> α} {f₂ : γ -> γ'} {g : δ -> β} {g₁ : δ' -> α} {g₂ : δ -> δ'}
    (hf : h ∘ f = f₁ ∘ f₂) (hg : h ∘ g = g₁ ∘ g₂) (hfg : range f union range g = univ) (s : Set β) :
    h '' s = f₁ '' f₂ '' f ⁻¹' s union g₁ '' g₂ '' g ⁻¹' s := by
  rw [← image_comp]; rw [← image_comp]; rw [← hf]; rw [← hg]; rw [image_comp]; rw [image_comp]; rw [image_preimage_eq_inter_range]; rw [image_preimage_eq_inter_range]; rw [← image_union]; rw [← inter_union_distrib_left]; rw [hfg]; rw [inter_univ]

end Range

section Subsingleton

variable {s : Set α} {f : α -> β}

/--
theorem `Subsingleton.image` / 定理 `Subsingleton.image`

English:
theorem Subsingleton.image
  given: (hs : s.Subsingleton) (f : α -> β)
  statement: (f '' s).Subsingleton
  proof: fun _ ⟨_, hx, Hx⟩ _ ⟨_, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)

中文:
定理 Subsingleton.image
  条件: (hs : s.Subsingleton) (f : α -> β)
  结论: (f '' s).Subsingleton
  证明: fun _ ⟨_, hx, Hx⟩ _ ⟨_, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)

Depends on / 依赖: congr_arg
-/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α -> β) : (f '' s).Subsingleton :=
  fun _ ⟨_, hx, Hx⟩ _ ⟨_, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)

/--
theorem `Subsingleton.preimage` / 定理 `Subsingleton.preimage`

English:
theorem Subsingleton.preimage
  statement: {s : Set β} (hs : s.Subsingleton)
  proof: fun _ ha _ hb => hf hs ha hb

中文:
定理 Subsingleton.preimage
  结论: {s : Set β} (hs : s.Subsingleton)
  证明: fun _ ha _ hb => hf hs ha hb
-/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton)
(hf : Function.Injective f) : (f ⁻¹' s).Subsingleton := fun _ ha _ hb => hf hs ha hb

/--
theorem `subsingleton_of_image` / 定理 `subsingleton_of_image`

English:
theorem subsingleton_of_image
  statement: (hf : Function.Injective f) (s : Set α)
  proof: (hs.preimage hf).anti subset_preimage_image _ _

中文:
定理 subsingleton_of_image
  结论: (hf : Function.Injective f) (s : Set α)
  证明: (hs.preimage hf).anti subset_preimage_image _ _

Depends on / 依赖: hs.preimage, preimage, subset_preimage_image
-/
theorem subsingleton_of_image (hf : Function.Injective f) (s : Set α)
    (hs : (f '' s).Subsingleton) : s.Subsingleton :=
(hs.preimage hf).anti subset_preimage_image _ _

/--
theorem `subsingleton_of_preimage` / 定理 `subsingleton_of_preimage`

English:
theorem subsingleton_of_preimage
  statement: (hf : Function.Surjective f) (s : Set β)
  proof: fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)

中文:
定理 subsingleton_of_preimage
  结论: (hf : Function.Surjective f) (s : Set β)
  证明: fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)

Depends on / 依赖: congr_arg
-/
theorem subsingleton_of_preimage (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)

/--
theorem `subsingleton_range` / 定理 `subsingleton_range`

English:
theorem subsingleton_range
  given: {α : Sort*} [Subsingleton α] (f : α -> β)
  statement: (range f).Subsingleton
  proof: forall_mem_range.2 fun x => forall_mem_range.2 fun y => congr_arg f (Subsingleton.elim x y)

中文:
定理 subsingleton_range
  条件: {α : Sort*} [Subsingleton α] (f : α -> β)
  结论: (range f).Subsingleton
  证明: forall_mem_range.2 fun x => forall_mem_range.2 fun y => congr_arg f (Subsingleton.elim x y)

Depends on / 依赖: Subsingleton, Subsingleton.elim, congr_arg, forall_mem_range
-/
theorem subsingleton_range {α : Sort*} [Subsingleton α] (f : α -> β) : (range f).Subsingleton :=
  forall_mem_range.2 fun x => forall_mem_range.2 fun y => congr_arg f (Subsingleton.elim x y)

/--
theorem `Nontrivial.preimage` / 定理 `Nontrivial.preimage`

English:
theorem Nontrivial.preimage
  statement: {s : Set β} (hs : s.Nontrivial)
  proof: by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

中文:
定理 Nontrivial.preimage
  结论: {s : Set β} (hs : s.Nontrivial)
  证明: by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

Depends on / 依赖: congr_arg
-/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial)
    (hf : Function.Surjective f) : (f ⁻¹' s).Nontrivial := by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

/--
theorem `Nontrivial.image` / 定理 `Nontrivial.image`

English:
theorem Nontrivial.image
  given: (hs : s.Nontrivial) (hf : Function.Injective f)
  proof: let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩

中文:
定理 Nontrivial.image
  条件: (hs : s.Nontrivial) (hf : Function.Injective f)
  证明: let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩

Depends on / 依赖: hf.ne, mem_image_of_mem
-/
theorem Nontrivial.image (hs : s.Nontrivial) (hf : Function.Injective f) :
    (f '' s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩

/--
theorem `Nontrivial.image_of_injOn` / 定理 `Nontrivial.image_of_injOn`

English:
theorem Nontrivial.image_of_injOn
  given: (hs : s.Nontrivial) (hf : s.InjOn f)
  proof: by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

中文:
定理 Nontrivial.image_of_injOn
  条件: (hs : s.Nontrivial) (hf : s.InjOn f)
  证明: by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

Depends on / 依赖: mem_image_of_mem
-/
theorem Nontrivial.image_of_injOn (hs : s.Nontrivial) (hf : s.InjOn f) :
    (f '' s).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

/--
theorem `nontrivial_of_image` / 定理 `nontrivial_of_image`

English:
theorem nontrivial_of_image
  given: (f : α -> β) (s : Set α) (hs : (f '' s).Nontrivial)
  statement: s.Nontrivial
  proof: let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

@[simp]

中文:
定理 nontrivial_of_image
  条件: (f : α -> β) (s : Set α) (hs : (f '' s).Nontrivial)
  结论: s.Nontrivial
  证明: let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

@[simp]

Depends on / 依赖: congr_arg
-/
theorem nontrivial_of_image (f : α -> β) (s : Set α) (hs : (f '' s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

@[simp]
/--
theorem `image_nontrivial` / 定理 `image_nontrivial`

English:
theorem image_nontrivial
  given: (hf : f.Injective)
  statement: (f '' s).Nontrivial ↔ s.Nontrivial
  proof: ⟨nontrivial_of_image f s, fun h => h.image hf⟩

@[simp]

中文:
定理 image_nontrivial
  条件: (hf : f.Injective)
  结论: (f '' s).Nontrivial ↔ s.Nontrivial
  证明: ⟨nontrivial_of_image f s, fun h => h.image hf⟩

@[simp]

Depends on / 依赖: h.image, nontrivial_of_image
-/
theorem image_nontrivial (hf : f.Injective) : (f '' s).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image f s, fun h => h.image hf⟩

@[simp]
/--
theorem `InjOn.image_nontrivial_iff` / 定理 `InjOn.image_nontrivial_iff`

English:
theorem InjOn.image_nontrivial_iff
  given: (hf : s.InjOn f)
  proof: ⟨nontrivial_of_image f s, fun h => h.image_of_injOn hf⟩

中文:
定理 InjOn.image_nontrivial_iff
  条件: (hf : s.InjOn f)
  证明: ⟨nontrivial_of_image f s, fun h => h.image_of_injOn hf⟩

Depends on / 依赖: h.image_of_injOn, image_of_injOn, nontrivial_of_image
-/
theorem InjOn.image_nontrivial_iff (hf : s.InjOn f) :
    (f '' s).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image f s, fun h => h.image_of_injOn hf⟩

/--
theorem `nontrivial_of_preimage` / 定理 `nontrivial_of_preimage`

English:
theorem nontrivial_of_preimage
  statement: (hf : Function.Injective f) (s : Set β)
  proof: (hs.image hf).mono image_preimage_subset _ _

中文:
定理 nontrivial_of_preimage
  结论: (hf : Function.Injective f) (s : Set β)
  证明: (hs.image hf).mono image_preimage_subset _ _

Depends on / 依赖: hs.image, image_preimage_subset
-/
theorem nontrivial_of_preimage (hf : Function.Injective f) (s : Set β)
    (hs : (f ⁻¹' s).Nontrivial) : s.Nontrivial :=
(hs.image hf).mono image_preimage_subset _ _

end Subsingleton

end Set

namespace Function

variable {α β : Type*} {ι : Sort*} {f : α -> β}

open Set

/--
theorem `Surjective.preimage_injective` / 定理 `Surjective.preimage_injective`

English:
theorem Surjective.preimage_injective
  given: (hf : Surjective f)
  statement: Injective (preimage f)
  proof: fun _ _ =>
  (preimage_eq_preimage hf).1

中文:
定理 Surjective.preimage_injective
  条件: (hf : Surjective f)
  结论: Injective (preimage f)
  证明: fun _ _ =>
  (preimage_eq_preimage hf).1
-/
theorem Surjective.preimage_injective (hf : Surjective f) : Injective (preimage f) := fun _ _ =>
  (preimage_eq_preimage hf).1

/--
theorem `Injective.preimage_image` / 定理 `Injective.preimage_image`

English:
theorem Injective.preimage_image
  given: (hf : Injective f) (s : Set α)
  statement: f ⁻¹' f '' s = s
  proof: preimage_image_eq s hf

中文:
定理 Injective.preimage_image
  条件: (hf : Injective f) (s : Set α)
  结论: f ⁻¹' f '' s = s
  证明: preimage_image_eq s hf

Depends on / 依赖: preimage_image_eq
-/
theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' f '' s = s :=
  preimage_image_eq s hf

/--
theorem `Injective.preimage_surjective` / 定理 `Injective.preimage_surjective`

English:
theorem Injective.preimage_surjective
  given: (hf : Injective f)
  statement: Surjective (preimage f)
  proof: Set.preimage_surjective.mpr hf

中文:
定理 Injective.preimage_surjective
  条件: (hf : Injective f)
  结论: Surjective (preimage f)
  证明: Set.preimage_surjective.mpr hf

Depends on / 依赖: Set.preimage_surjective.mpr, preimage_surjective
-/
theorem Injective.preimage_surjective (hf : Injective f) : Surjective (preimage f) :=
  Set.preimage_surjective.mpr hf

/--
theorem `Injective.subsingleton_image_iff` / 定理 `Injective.subsingleton_image_iff`

English:
theorem Injective.subsingleton_image_iff
  given: (hf : Injective f) {s : Set α}
  proof: ⟨subsingleton_of_image hf s, fun h => h.image f⟩

中文:
定理 Injective.subsingleton_image_iff
  条件: (hf : Injective f) {s : Set α}
  证明: ⟨subsingleton_of_image hf s, fun h => h.image f⟩

Depends on / 依赖: h.image, subsingleton_of_image
-/
theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} :
    (f '' s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩

/--
theorem `Surjective.image_preimage` / 定理 `Surjective.image_preimage`

English:
theorem Surjective.image_preimage
  given: (hf : Surjective f) (s : Set β)
  statement: f '' f ⁻¹' s = s
  proof: image_preimage_eq s hf

中文:
定理 Surjective.image_preimage
  条件: (hf : Surjective f) (s : Set β)
  结论: f '' f ⁻¹' s = s
  证明: image_preimage_eq s hf

Depends on / 依赖: image_preimage_eq
-/
theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f '' f ⁻¹' s = s :=
  image_preimage_eq s hf

/--
theorem `Surjective.image_surjective` / 定理 `Surjective.image_surjective`

English:
theorem Surjective.image_surjective
  given: (hf : Surjective f)
  statement: Surjective (image f)
  proof: by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]

@[simp]

中文:
定理 Surjective.image_surjective
  条件: (hf : Surjective f)
  结论: Surjective (image f)
  证明: by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]

@[simp]

Depends on / 依赖: hf.image_preimage, image_preimage
-/
theorem Surjective.image_surjective (hf : Surjective f) : Surjective (image f) := by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]

@[simp]
/--
theorem `Surjective.nonempty_preimage` / 定理 `Surjective.nonempty_preimage`

English:
theorem Surjective.nonempty_preimage
  given: (hf : Surjective f) {s : Set β}
  proof: by rw [← image_nonempty, hf.image_preimage]

中文:
定理 Surjective.nonempty_preimage
  条件: (hf : Surjective f) {s : Set β}
  证明: by rw [← image_nonempty, hf.image_preimage]

Depends on / 依赖: hf.image_preimage, image_nonempty, image_preimage
-/
theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} :
    (f ⁻¹' s).Nonempty ↔ s.Nonempty := by rw [← image_nonempty, hf.image_preimage]

/--
theorem `Injective.image_injective` / 定理 `Injective.image_injective`

English:
theorem Injective.image_injective
  given: (hf : Injective f)
  statement: Injective (image f)
  proof: by
  intro s t h
  rw [← preimage_image_eq s hf]; rw [← preimage_image_eq t hf]; rw [h]

中文:
定理 Injective.image_injective
  条件: (hf : Injective f)
  结论: Injective (image f)
  证明: by
  intro s t h
  rw [← preimage_image_eq s hf]; rw [← preimage_image_eq t hf]; rw [h]

Depends on / 依赖: preimage_image_eq
-/
theorem Injective.image_injective (hf : Injective f) : Injective (image f) := by
  intro s t h
  rw [← preimage_image_eq s hf]; rw [← preimage_image_eq t hf]; rw [h]

/--
lemma `Injective.image_strictMono` / 引理 `Injective.image_strictMono`

English:
lemma Injective.image_strictMono
  given: (inj : Function.Injective f)
  statement: StrictMono (image f)
  proof: monotone_image.strictMono_of_injective inj.image_injective

中文:
引理 Injective.image_strictMono
  条件: (inj : Function.Injective f)
  结论: StrictMono (image f)
  证明: monotone_image.strictMono_of_injective inj.image_injective

Depends on / 依赖: image_injective, inj.image_injective, monotone_image, monotone_image.strictMono_of_injective, strictMono_of_injective
-/
lemma Injective.image_strictMono (inj : Function.Injective f) : StrictMono (image f) :=
  monotone_image.strictMono_of_injective inj.image_injective

/--
theorem `Surjective.preimage_subset_preimage_iff` / 定理 `Surjective.preimage_subset_preimage_iff`

English:
theorem Surjective.preimage_subset_preimage_iff
  given: {s t : Set β} (hf : Surjective f)
  proof: by
  apply Set.preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ

中文:
定理 Surjective.preimage_subset_preimage_iff
  条件: {s t : Set β} (hf : Surjective f)
  证明: by
  apply Set.preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ

Depends on / 依赖: Set.preimage_subset_preimage_iff, hf.range_eq, preimage_subset_preimage_iff, range_eq, subset_univ
-/
theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) :
    f ⁻¹' s subseteq f ⁻¹' t ↔ s subseteq t := by
  apply Set.preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ

/--
theorem `Surjective.range_comp` / 定理 `Surjective.range_comp`

English:
theorem Surjective.range_comp
  given: {ι' : Sort*} {f : ι -> ι'} (hf : Surjective f) (g : ι' -> α)
  proof: ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm

中文:
定理 Surjective.range_comp
  条件: {ι' : Sort*} {f : ι -> ι'} (hf : Surjective f) (g : ι' -> α)
  证明: ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm

Depends on / 依赖: Surjective, Surjective.exists
-/
theorem Surjective.range_comp {ι' : Sort*} {f : ι -> ι'} (hf : Surjective f) (g : ι' -> α) :
    range (g ∘ f) = range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm

/--
theorem `Injective.mem_range_iff_existsUnique` / 定理 `Injective.mem_range_iff_existsUnique`

English:
theorem Injective.mem_range_iff_existsUnique
  given: (hf : Injective f) {b : β}
  proof: ⟨fun ⟨a, h⟩ => ⟨a, h, fun _ ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

alias ⟨Injective.existsUnique_of_mem_range, _⟩ := Injective.mem_range_iff_existsUnique

中文:
定理 Injective.mem_range_iff_existsUnique
  条件: (hf : Injective f) {b : β}
  证明: ⟨fun ⟨a, h⟩ => ⟨a, h, fun _ ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

alias ⟨Injective.existsUnique_of_mem_range, _⟩ := Injective.mem_range_iff_existsUnique

Depends on / 依赖: ExistsUnique, ExistsUnique.exists, h.symm, ha.trans
-/
theorem Injective.mem_range_iff_existsUnique (hf : Injective f) {b : β} :
    b in range f ↔ exists! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun _ ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

alias ⟨Injective.existsUnique_of_mem_range, _⟩ := Injective.mem_range_iff_existsUnique

/--
theorem `Injective.compl_image_eq` / 定理 `Injective.compl_image_eq`

English:
theorem Injective.compl_image_eq
  given: (hf : Injective f) (s : Set α)
  proof: by
  grind

中文:
定理 Injective.compl_image_eq
  条件: (hf : Injective f) (s : Set α)
  证明: by
  grind
-/
theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) :
    (f '' s)ᶜ = f '' sᶜ union (range f)ᶜ := by
  grind

/--
theorem `LeftInverse.image_image` / 定理 `LeftInverse.image_image`

English:
theorem LeftInverse.image_image
  given: {g : β -> α} (h : LeftInverse g f) (s : Set α)
  proof: by rw [← image_comp, h.comp_eq_id, image_id]

中文:
定理 LeftInverse.image_image
  条件: {g : β -> α} (h : LeftInverse g f) (s : Set α)
  证明: by rw [← image_comp, h.comp_eq_id, image_id]

Depends on / 依赖: comp_eq_id, h.comp_eq_id, image_comp, image_id
-/
theorem LeftInverse.image_image {g : β -> α} (h : LeftInverse g f) (s : Set α) :
    g '' f '' s = s := by rw [← image_comp, h.comp_eq_id, image_id]

/--
theorem `LeftInverse.preimage_preimage` / 定理 `LeftInverse.preimage_preimage`

English:
theorem LeftInverse.preimage_preimage
  given: {g : β -> α} (h : LeftInverse g f) (s : Set α)
  proof: by rw [← preimage_comp, h.comp_eq_id, preimage_id]

中文:
定理 LeftInverse.preimage_preimage
  条件: {g : β -> α} (h : LeftInverse g f) (s : Set α)
  证明: by rw [← preimage_comp, h.comp_eq_id, preimage_id]

Depends on / 依赖: comp_eq_id, h.comp_eq_id, preimage_comp, preimage_id
-/
theorem LeftInverse.preimage_preimage {g : β -> α} (h : LeftInverse g f) (s : Set α) :
    f ⁻¹' g ⁻¹' s = s := by rw [← preimage_comp, h.comp_eq_id, preimage_id]

/--
theorem `Involutive.preimage` / 定理 `Involutive.preimage`

English:
theorem Involutive.preimage
  given: {f : α -> α} (hf : Involutive f)
  statement: Involutive (preimage f)
  proof: hf.rightInverse.preimage_preimage

中文:
定理 Involutive.preimage
  条件: {f : α -> α} (hf : Involutive f)
  结论: Involutive (preimage f)
  证明: hf.rightInverse.preimage_preimage
-/
protected theorem Involutive.preimage {f : α -> α} (hf : Involutive f) : Involutive (preimage f) :=
  hf.rightInverse.preimage_preimage

/--
theorem `LeftInverse.image_eq` / 定理 `LeftInverse.image_eq`

English:
theorem LeftInverse.image_eq
  given: {f : α -> β} {g : β -> α} (hfg : LeftInverse g f) (s : Set α)
  proof: by
  rw [← image_preimage_eq_range_inter]; rw [hfg.preimage_preimage]

中文:
定理 LeftInverse.image_eq
  条件: {f : α -> β} {g : β -> α} (hfg : LeftInverse g f) (s : Set α)
  证明: by
  rw [← image_preimage_eq_range_inter]; rw [hfg.preimage_preimage]

Depends on / 依赖: hfg.preimage_preimage, image_preimage_eq_range_inter, preimage_preimage
-/
theorem LeftInverse.image_eq {f : α -> β} {g : β -> α} (hfg : LeftInverse g f) (s : Set α) :
    f '' s = range f inter g ⁻¹' s := by
  rw [← image_preimage_eq_range_inter]; rw [hfg.preimage_preimage]

end Function

namespace EquivLike

variable {ι ι' : Sort*} {E : Type*} [EquivLike E ι ι']

/--
lemma `range_comp` / 引理 `range_comp`

English:
lemma range_comp
  given: {α : Type*} (f : ι' -> α) (e : E)
  statement: range (f ∘ e) = range f
  proof: (EquivLike.surjective _).range_comp _

中文:
引理 range_comp
  条件: {α : 类型} (f : ι' -> α) (e : E)
  结论: range (f ∘ e) = range f
  证明: (EquivLike.surjective _).range_comp _
-/
@[simp] lemma range_comp {α : Type*} (f : ι' -> α) (e : E) : range (f ∘ e) = range f :=
  (EquivLike.surjective _).range_comp _

end EquivLike

/-! ### Image and preimage on subtypes -/


namespace Subtype

variable {α : Type*}

/--
theorem `coe_image` / 定理 `coe_image`

English:
theorem coe_image
  given: {p : α -> Prop} {s : Set (Subtype p)}
  proof: Set.ext fun a =>
    ⟨fun ⟨⟨_, ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]

中文:
定理 coe_image
  条件: {p : α -> 命题} {s : Set (Subtype p)}
  证明: Set.ext fun a =>
    ⟨fun ⟨⟨_, ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]

Depends on / 依赖: Set.ext, h_eq, in_s
-/
theorem coe_image {p : α -> Prop} {s : Set (Subtype p)} :
    (↑) '' s = { x | exists h : p x, (⟨x, h⟩ : Subtype p) in s } :=
  Set.ext fun a =>
    ⟨fun ⟨⟨_, ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]
/--
theorem `coe_image_of_subset` / 定理 `coe_image_of_subset`

English:
theorem coe_image_of_subset
  given: {s t : Set α} (h : t subseteq s)
  statement: (↑) '' { x : ↥s | ↑x in t } = t
  proof: by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨_, hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

中文:
定理 coe_image_of_subset
  条件: {s t : Set α} (h : t subseteq s)
  结论: (↑) '' { x : ↥s | ↑x in t } = t
  证明: by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨_, hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

Depends on / 依赖: mem_image
-/
theorem coe_image_of_subset {s t : Set α} (h : t subseteq s) : (↑) '' { x : ↥s | ↑x in t } = t := by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨_, hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  given: {s : Set α}
  statement: range ((↑) : s -> α) = s
  proof: by
  rw [← image_univ]
  simp [-image_univ, coe_image]

中文:
定理 range_coe
  条件: {s : Set α}
  结论: range ((↑) : s -> α) = s
  证明: by
  rw [← image_univ]
  simp [-image_univ, coe_image]

Depends on / 依赖: coe_image, image_univ
-/
theorem range_coe {s : Set α} : range ((↑) : s -> α) = s := by
  rw [← image_univ]
  simp [-image_univ, coe_image]

/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  given: {s : Set α}
  statement: range (Subtype.val : s -> α) = s
  proof: range_coe

中文:
定理 range_val
  条件: {s : Set α}
  结论: range (Subtype.val : s -> α) = s
  证明: range_coe

Depends on / 依赖: range_coe
-/
theorem range_val {s : Set α} : range (Subtype.val : s -> α) = s :=
  range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : Set α` the function `(↑) : s → α`, then the inferred implicit arguments of `(↑)` are
  `↑α (fun x ↦ x ∈ s)`. -/
@[simp]
/--
theorem `range_coe_subtype` / 定理 `range_coe_subtype`

English:
theorem range_coe_subtype
  given: {p : α -> Prop}
  statement: range ((↑) : Subtype p -> α) = { x | p x }
  proof: range_coe

@[simp]

中文:
定理 range_coe_subtype
  条件: {p : α -> 命题}
  结论: range ((↑) : Subtype p -> α) = { x | p x }
  证明: range_coe

@[simp]

Depends on / 依赖: range_coe
-/
theorem range_coe_subtype {p : α -> Prop} : range ((↑) : Subtype p -> α) = { x | p x } :=
  range_coe

@[simp]
/--
theorem `coe_preimage_self` / 定理 `coe_preimage_self`

English:
theorem coe_preimage_self
  given: (s : Set α)
  statement: ((↑) : s -> α) ⁻¹' s = univ
  proof: by
  rw [← preimage_range]; rw [range_coe]

中文:
定理 coe_preimage_self
  条件: (s : Set α)
  结论: ((↑) : s -> α) ⁻¹' s = univ
  证明: by
  rw [← preimage_range]; rw [range_coe]

Depends on / 依赖: preimage_range, range_coe
-/
theorem coe_preimage_self (s : Set α) : ((↑) : s -> α) ⁻¹' s = univ := by
  rw [← preimage_range]; rw [range_coe]

/--
theorem `range_val_subtype` / 定理 `range_val_subtype`

English:
theorem range_val_subtype
  given: {p : α -> Prop}
  statement: range (Subtype.val : Subtype p -> α) = { x | p x }
  proof: range_coe

中文:
定理 range_val_subtype
  条件: {p : α -> 命题}
  结论: range (Subtype.val : Subtype p -> α) = { x | p x }
  证明: range_coe

Depends on / 依赖: range_coe
-/
theorem range_val_subtype {p : α -> Prop} : range (Subtype.val : Subtype p -> α) = { x | p x } :=
  range_coe

/--
theorem `coe_image_subset` / 定理 `coe_image_subset`

English:
theorem coe_image_subset
  given: (s : Set α) (t : Set s)
  statement: ((↑) : s -> α) '' t subseteq s
  proof: fun x ⟨y, _, yvaleq⟩ => by
  rw [← yvaleq]; exact y.property

中文:
定理 coe_image_subset
  条件: (s : Set α) (t : Set s)
  结论: ((↑) : s -> α) '' t subseteq s
  证明: fun x ⟨y, _, yvaleq⟩ => by
  rw [← yvaleq]; exact y.property

Depends on / 依赖: property, y.property, yvaleq
-/
theorem coe_image_subset (s : Set α) (t : Set s) : ((↑) : s -> α) '' t subseteq s :=
  fun x ⟨y, _, yvaleq⟩ => by
  rw [← yvaleq]; exact y.property

/--
theorem `coe_image_univ` / 定理 `coe_image_univ`

English:
theorem coe_image_univ
  given: (s : Set α)
  statement: ((↑) : s -> α) '' Set.univ = s
  proof: image_univ.trans range_coe

@[simp]

中文:
定理 coe_image_univ
  条件: (s : Set α)
  结论: ((↑) : s -> α) '' Set.univ = s
  证明: image_univ.trans range_coe

@[simp]

Depends on / 依赖: image_univ, image_univ.trans, range_coe
-/
theorem coe_image_univ (s : Set α) : ((↑) : s -> α) '' Set.univ = s :=
  image_univ.trans range_coe

@[simp]
/--
theorem `image_preimage_coe` / 定理 `image_preimage_coe`

English:
theorem image_preimage_coe
  given: (s t : Set α)
  statement: ((↑) : s -> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
  proof: image_preimage_eq_range_inter.trans congr_arg (· inter t) range_coe

中文:
定理 image_preimage_coe
  条件: (s t : Set α)
  结论: ((↑) : s -> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
  证明: image_preimage_eq_range_inter.trans congr_arg (· inter t) range_coe

Depends on / 依赖: congr_arg, image_preimage_eq_range_inter, image_preimage_eq_range_inter.trans, range_coe
-/
theorem image_preimage_coe (s t : Set α) : ((↑) : s -> α) '' ((↑) : s -> α) ⁻¹' t = s inter t :=
image_preimage_eq_range_inter.trans congr_arg (· inter t) range_coe

/--
theorem `image_preimage_val` / 定理 `image_preimage_val`

English:
theorem image_preimage_val
  given: (s t : Set α)
  statement: (Subtype.val : s -> α) '' Subtype.val ⁻¹' t = s inter t
  proof: image_preimage_coe s t

中文:
定理 image_preimage_val
  条件: (s t : Set α)
  结论: (Subtype.val : s -> α) '' Subtype.val ⁻¹' t = s inter t
  证明: image_preimage_coe s t

Depends on / 依赖: image_preimage_coe
-/
theorem image_preimage_val (s t : Set α) : (Subtype.val : s -> α) '' Subtype.val ⁻¹' t = s inter t :=
  image_preimage_coe s t

/--
theorem `preimage_coe_eq_preimage_coe_iff` / 定理 `preimage_coe_eq_preimage_coe_iff`

English:
theorem preimage_coe_eq_preimage_coe_iff
  given: {s t u : Set α}
  proof: by
  rw [← image_preimage_coe]; rw [← image_preimage_coe]; rw [coe_injective.image_injective.eq_iff]

中文:
定理 preimage_coe_eq_preimage_coe_iff
  条件: {s t u : Set α}
  证明: by
  rw [← image_preimage_coe]; rw [← image_preimage_coe]; rw [coe_injective.image_injective.eq_iff]

Depends on / 依赖: coe_injective, coe_injective.image_injective.eq_iff, eq_iff, image_injective, image_preimage_coe
-/
theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} :
    ((↑) : s -> α) ⁻¹' t = ((↑) : s -> α) ⁻¹' u ↔ s inter t = s inter u := by
  rw [← image_preimage_coe]; rw [← image_preimage_coe]; rw [coe_injective.image_injective.eq_iff]

/--
theorem `preimage_coe_self_inter` / 定理 `preimage_coe_self_inter`

English:
theorem preimage_coe_self_inter
  given: (s t : Set α)
  proof: by
  rw [preimage_coe_eq_preimage_coe_iff]; rw [← inter_assoc]; rw [inter_self]

中文:
定理 preimage_coe_self_inter
  条件: (s t : Set α)
  证明: by
  rw [preimage_coe_eq_preimage_coe_iff]; rw [← inter_assoc]; rw [inter_self]

Depends on / 依赖: inter_assoc, inter_self, preimage_coe_eq_preimage_coe_iff
-/
theorem preimage_coe_self_inter (s t : Set α) :
    ((↑) : s -> α) ⁻¹' (s inter t) = ((↑) : s -> α) ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff]; rw [← inter_assoc]; rw [inter_self]

-- Not `@[simp]` since `simp` can prove this.
/--
theorem `preimage_coe_inter_self` / 定理 `preimage_coe_inter_self`

English:
theorem preimage_coe_inter_self
  given: (s t : Set α)
  proof: by
  rw [inter_comm]; rw [preimage_coe_self_inter]

中文:
定理 preimage_coe_inter_self
  条件: (s t : Set α)
  证明: by
  rw [inter_comm]; rw [preimage_coe_self_inter]

Depends on / 依赖: inter_comm, preimage_coe_self_inter
-/
theorem preimage_coe_inter_self (s t : Set α) :
    ((↑) : s -> α) ⁻¹' (t inter s) = ((↑) : s -> α) ⁻¹' t := by
  rw [inter_comm]; rw [preimage_coe_self_inter]

/--
theorem `preimage_val_eq_preimage_val_iff` / 定理 `preimage_val_eq_preimage_val_iff`

English:
theorem preimage_val_eq_preimage_val_iff
  given: (s t u : Set α)
  proof: preimage_coe_eq_preimage_coe_iff

中文:
定理 preimage_val_eq_preimage_val_iff
  条件: (s t u : Set α)
  证明: preimage_coe_eq_preimage_coe_iff

Depends on / 依赖: preimage_coe_eq_preimage_coe_iff
-/
theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s -> α) ⁻¹' t = Subtype.val ⁻¹' u ↔ s inter t = s inter u :=
  preimage_coe_eq_preimage_coe_iff

/--
lemma `preimage_val_subset_preimage_val_iff` / 引理 `preimage_val_subset_preimage_val_iff`

English:
lemma preimage_val_subset_preimage_val_iff
  given: (s t u : Set α)
  proof: by
  constructor
  · rw [← image_preimage_coe, ← image_preimage_coe]
    exact image_mono
  · intro h x a
    exact (h ⟨x.2, a⟩).2

中文:
引理 preimage_val_subset_preimage_val_iff
  条件: (s t u : Set α)
  证明: by
  constructor
  · rw [← image_preimage_coe, ← image_preimage_coe]
    exact image_mono
  · intro h x a
    exact (h ⟨x.2, a⟩).2

Depends on / 依赖: image_mono, image_preimage_coe
-/
lemma preimage_val_subset_preimage_val_iff (s t u : Set α) :
    (Subtype.val ⁻¹' t : Set s) subseteq Subtype.val ⁻¹' u ↔ s inter t subseteq s inter u := by
  constructor
  · rw [← image_preimage_coe, ← image_preimage_coe]
    exact image_mono
  · intro h x a
    exact (h ⟨x.2, a⟩).2

/--
theorem `exists_set_subtype` / 定理 `exists_set_subtype`

English:
theorem exists_set_subtype
  given: {t : Set α} (p : Set α -> Prop)
  proof: by
  rw [← exists_subset_range_and_iff]; rw [range_coe]

中文:
定理 exists_set_subtype
  条件: {t : Set α} (p : Set α -> 命题)
  证明: by
  rw [← exists_subset_range_and_iff]; rw [range_coe]

Depends on / 依赖: exists_subset_range_and_iff, range_coe
-/
theorem exists_set_subtype {t : Set α} (p : Set α -> Prop) :
    (exists s : Set t, p (((↑) : t -> α) '' s)) ↔ exists s : Set α, s subseteq t ∧ p s := by
  rw [← exists_subset_range_and_iff]; rw [range_coe]

/--
theorem `forall_set_subtype` / 定理 `forall_set_subtype`

English:
theorem forall_set_subtype
  given: {t : Set α} (p : Set α -> Prop)
  proof: by
  rw [← forall_subset_range_iff]; rw [range_coe]

中文:
定理 forall_set_subtype
  条件: {t : Set α} (p : Set α -> 命题)
  证明: by
  rw [← forall_subset_range_iff]; rw [range_coe]

Depends on / 依赖: forall_subset_range_iff, range_coe
-/
theorem forall_set_subtype {t : Set α} (p : Set α -> Prop) :
    (forall s : Set t, p (((↑) : t -> α) '' s)) ↔ forall s : Set α, s subseteq t -> p s := by
  rw [← forall_subset_range_iff]; rw [range_coe]

/--
theorem `preimage_coe_nonempty` / 定理 `preimage_coe_nonempty`

English:
theorem preimage_coe_nonempty
  given: {s t : Set α}
  proof: by
  rw [← image_preimage_coe]; rw [image_nonempty]

中文:
定理 preimage_coe_nonempty
  条件: {s t : Set α}
  证明: by
  rw [← image_preimage_coe]; rw [image_nonempty]

Depends on / 依赖: image_nonempty, image_preimage_coe
-/
theorem preimage_coe_nonempty {s t : Set α} :
    (((↑) : s -> α) ⁻¹' t).Nonempty ↔ (s inter t).Nonempty := by
  rw [← image_preimage_coe]; rw [image_nonempty]

/--
theorem `preimage_coe_eq_empty` / 定理 `preimage_coe_eq_empty`

English:
theorem preimage_coe_eq_empty
  given: {s t : Set α}
  statement: ((↑) : s -> α) ⁻¹' t = ∅ ↔ s inter t = ∅
  proof: by
  simp [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

中文:
定理 preimage_coe_eq_empty
  条件: {s t : Set α}
  结论: ((↑) : s -> α) ⁻¹' t = ∅ ↔ s inter t = ∅
  证明: by
  simp [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

Depends on / 依赖: not_nonempty_iff_eq_empty, preimage_coe_nonempty
-/
theorem preimage_coe_eq_empty {s t : Set α} : ((↑) : s -> α) ⁻¹' t = ∅ ↔ s inter t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

-- Not `@[simp]` since `simp` can prove this.
/--
theorem `preimage_coe_compl` / 定理 `preimage_coe_compl`

English:
theorem preimage_coe_compl
  given: (s : Set α)
  statement: ((↑) : s -> α) ⁻¹' sᶜ = ∅
  proof: preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]

中文:
定理 preimage_coe_compl
  条件: (s : Set α)
  结论: ((↑) : s -> α) ⁻¹' sᶜ = ∅
  证明: preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]

Depends on / 依赖: inter_compl_self, preimage_coe_eq_empty
-/
theorem preimage_coe_compl (s : Set α) : ((↑) : s -> α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]
/--
theorem `preimage_coe_compl'` / 定理 `preimage_coe_compl'`

English:
theorem preimage_coe_compl'
  given: (s : Set α)
  proof: preimage_coe_eq_empty.2 (compl_inter_self s)

中文:
定理 preimage_coe_compl'
  条件: (s : Set α)
  证明: preimage_coe_eq_empty.2 (compl_inter_self s)

Depends on / 依赖: compl_inter_self, preimage_coe_eq_empty
-/
theorem preimage_coe_compl' (s : Set α) :
    (fun x : (sᶜ : Set α) => (x : α)) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)

end Subtype

/-! ### Images and preimages on `Option` -/


namespace Option

/--
theorem `injective_iff` / 定理 `injective_iff`

English:
theorem injective_iff
  given: {α β} {f : Option α -> β}
  proof: by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine
⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne Option.some_ne_none _⟩, ?_⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts [rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]

中文:
定理 injective_iff
  条件: {α β} {f : Option α -> β}
  证明: by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine
⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne Option.some_ne_none _⟩, ?_⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts [rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]

Depends on / 依赖: Option.some_injective, Option.some_ne_none, congr_arg, exacts, h_none, h_some, hab.symm, hf.comp, hf.ne, mem_range, not_exists, some_injective, some_ne_none
-/
theorem injective_iff {α β} {f : Option α -> β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some) := by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine
⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne Option.some_ne_none _⟩, ?_⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts [rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: {α β} (f : Option α -> β)
  statement: range f = insert (f none) (range (f ∘ some))
  proof: Set.ext fun _ => Option.exists.trans eq_comm.or Iff.rfl

中文:
定理 range_eq
  条件: {α β} (f : Option α -> β)
  结论: range f = insert (f none) (range (f ∘ some))
  证明: Set.ext fun _ => Option.exists.trans eq_comm.or Iff.rfl

Depends on / 依赖: Iff.rfl, Option.exists.trans, Set.ext, eq_comm, eq_comm.or
-/
theorem range_eq {α β} (f : Option α -> β) : range f = insert (f none) (range (f ∘ some)) :=
Set.ext fun _ => Option.exists.trans eq_comm.or Iff.rfl

/--
theorem `range_elim` / 定理 `range_elim`

English:
theorem range_elim
  given: {α β} (b : β) (f : α -> β)
  proof: by
  rw [range_eq]
  simp [Function.comp_def]

中文:
定理 range_elim
  条件: {α β} (b : β) (f : α -> β)
  证明: by
  rw [range_eq]
  simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, range_eq
-/
theorem range_elim {α β} (b : β) (f : α -> β) :
    range (fun o : Option α => o.elim b f) = insert b (range f) := by
  rw [range_eq]
  simp [Function.comp_def]

/--
theorem `image_elim_range_some_eq_range` / 定理 `image_elim_range_some_eq_range`

English:
theorem image_elim_range_some_eq_range
  given: {α β} (f : α -> β) (b : β)
  proof: by
  rw [← range_comp']
  simp

中文:
定理 image_elim_range_some_eq_range
  条件: {α β} (f : α -> β) (b : β)
  证明: by
  rw [← range_comp']
  simp

Depends on / 依赖: range_comp
-/
theorem image_elim_range_some_eq_range {α β} (f : α -> β) (b : β) :
    (fun o : Option α => o.elim b f) '' range some = range f := by
  rw [← range_comp']
  simp

end Option

namespace Set

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α -> β}

@[simp]
/--
theorem `image_surjective` / 定理 `image_surjective`

English:
theorem image_surjective
  statement: Surjective (image f) ↔ Surjective f
  proof: by
  refine ⟨fun h y => ?_, Surjective.image_surjective⟩
  rcases h {y} with ⟨s, hs⟩
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

@[simp]

中文:
定理 image_surjective
  结论: Surjective (image f) ↔ Surjective f
  证明: by
  refine ⟨fun h y => ?_, Surjective.image_surjective⟩
  rcases h {y} with ⟨s, hs⟩
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

@[simp]

Depends on / 依赖: Surjective, Surjective.image_surjective, image_surjective, mem_singleton
-/
theorem image_surjective : Surjective (image f) ↔ Surjective f := by
  refine ⟨fun h y => ?_, Surjective.image_surjective⟩
  rcases h {y} with ⟨s, hs⟩
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

@[simp]
/--
theorem `image_injective` / 定理 `image_injective`

English:
theorem image_injective
  statement: Injective (image f) ↔ Injective f
  proof: by
  refine ⟨fun h x x' hx => ?_, Injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton]; rw [image_singleton]; rw [hx]

中文:
定理 image_injective
  结论: Injective (image f) ↔ Injective f
  证明: by
  refine ⟨fun h x x' hx => ?_, Injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton]; rw [image_singleton]; rw [hx]

Depends on / 依赖: Injective, Injective.image_injective, image_injective, image_singleton, singleton_eq_singleton_iff
-/
theorem image_injective : Injective (image f) ↔ Injective f := by
  refine ⟨fun h x x' hx => ?_, Injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton]; rw [image_singleton]; rw [hx]

/--
theorem `preimage_eq_iff_eq_image` / 定理 `preimage_eq_iff_eq_image`

English:
theorem preimage_eq_iff_eq_image
  given: {f : α -> β} (hf : Bijective f) {s t}
  proof: by rw [← image_eq_image hf.1, hf.2.image_preimage]

中文:
定理 preimage_eq_iff_eq_image
  条件: {f : α -> β} (hf : Bijective f) {s t}
  证明: by rw [← image_eq_image hf.1, hf.2.image_preimage]

Depends on / 依赖: image_eq_image, image_preimage
-/
theorem preimage_eq_iff_eq_image {f : α -> β} (hf : Bijective f) {s t} :
    f ⁻¹' s = t ↔ s = f '' t := by rw [← image_eq_image hf.1, hf.2.image_preimage]

/--
theorem `eq_preimage_iff_image_eq` / 定理 `eq_preimage_iff_image_eq`

English:
theorem eq_preimage_iff_image_eq
  given: {f : α -> β} (hf : Bijective f) {s t}
  proof: by rw [← image_eq_image hf.1, hf.2.image_preimage]

中文:
定理 eq_preimage_iff_image_eq
  条件: {f : α -> β} (hf : Bijective f) {s t}
  证明: by rw [← image_eq_image hf.1, hf.2.image_preimage]

Depends on / 依赖: image_eq_image, image_preimage
-/
theorem eq_preimage_iff_image_eq {f : α -> β} (hf : Bijective f) {s t} :
    s = f ⁻¹' t ↔ f '' s = t := by rw [← image_eq_image hf.1, hf.2.image_preimage]

end ImagePreimage

end Set

/-! ### Disjoint lemmas for image and preimage -/

section Disjoint
variable {α β γ : Type*} {f : α -> β} {s t : Set α}

/--
theorem `Disjoint.preimage` / 定理 `Disjoint.preimage`

English:
theorem Disjoint.preimage
  given: (f : α -> β) {s t : Set β} (h : Disjoint s t)
  proof: disjoint_iff_inf_le.mpr fun _ hx => h.le_bot hx

中文:
定理 Disjoint.preimage
  条件: (f : α -> β) {s t : Set β} (h : Disjoint s t)
  证明: disjoint_iff_inf_le.mpr fun _ hx => h.le_bot hx

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, h.le_bot, le_bot
-/
theorem Disjoint.preimage (f : α -> β) {s t : Set β} (h : Disjoint s t) :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) :=
  disjoint_iff_inf_le.mpr fun _ hx => h.le_bot hx

/--
lemma `Codisjoint.preimage` / 引理 `Codisjoint.preimage`

English:
lemma Codisjoint.preimage
  given: (f : α -> β) {s t : Set β} (h : Codisjoint s t)
  proof: by
  simp only [codisjoint_iff_le_sup, Set.sup_eq_union, top_le_iff, ← Set.preimage_union] at h ⊢
  rw [h]; rfl

中文:
引理 Codisjoint.preimage
  条件: (f : α -> β) {s t : Set β} (h : Codisjoint s t)
  证明: by
  simp only [codisjoint_iff_le_sup, Set.sup_eq_union, top_le_iff, ← Set.preimage_union] at h ⊢
  rw [h]; rfl

Depends on / 依赖: Set.preimage_union, Set.sup_eq_union, codisjoint_iff_le_sup, preimage_union, sup_eq_union, top_le_iff
-/
lemma Codisjoint.preimage (f : α -> β) {s t : Set β} (h : Codisjoint s t) :
    Codisjoint (f ⁻¹' s) (f ⁻¹' t) := by
  simp only [codisjoint_iff_le_sup, Set.sup_eq_union, top_le_iff, ← Set.preimage_union] at h ⊢
  rw [h]; rfl

/--
lemma `IsCompl.preimage` / 引理 `IsCompl.preimage`

English:
lemma IsCompl.preimage
  given: (f : α -> β) {s t : Set β} (h : IsCompl s t)
  proof: ⟨h.1.preimage f, h.2.preimage f⟩

中文:
引理 IsCompl.preimage
  条件: (f : α -> β) {s t : Set β} (h : IsCompl s t)
  证明: ⟨h.1.preimage f, h.2.preimage f⟩

Depends on / 依赖: preimage
-/
lemma IsCompl.preimage (f : α -> β) {s t : Set β} (h : IsCompl s t) :
    IsCompl (f ⁻¹' s) (f ⁻¹' t) :=
  ⟨h.1.preimage f, h.2.preimage f⟩

namespace Set

/--
theorem `disjoint_image_image` / 定理 `disjoint_image_image`

English:
theorem disjoint_image_image
  statement: {f : β -> α} {g : γ -> α} {s : Set β} {t : Set γ}
  proof: disjoint_iff_inf_le.mpr by rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩; exact h b hb c hc eq

中文:
定理 disjoint_image_image
  结论: {f : β -> α} {g : γ -> α} {s : Set β} {t : Set γ}
  证明: disjoint_iff_inf_le.mpr by rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩; exact h b hb c hc eq

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr
-/
theorem disjoint_image_image {f : β -> α} {g : γ -> α} {s : Set β} {t : Set γ}
    (h : forall b in s, forall c in t, f b != g c) : Disjoint (f '' s) (g '' t) :=
disjoint_iff_inf_le.mpr by rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩; exact h b hb c hc eq

/--
theorem `disjoint_image_of_injective` / 定理 `disjoint_image_of_injective`

English:
theorem disjoint_image_of_injective
  given: (hf : Injective f) {s t : Set α} (hd : Disjoint s t)
  proof: disjoint_image_image fun _ hx _ hy => hf.ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩

中文:
定理 disjoint_image_of_injective
  条件: (hf : Injective f) {s t : Set α} (hd : Disjoint s t)
  证明: disjoint_image_image fun _ hx _ hy => hf.ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩

Depends on / 依赖: H.symm, Set.disjoint_iff, disjoint_iff, disjoint_image_image, hf.ne
-/
theorem disjoint_image_of_injective (hf : Injective f) {s t : Set α} (hd : Disjoint s t) :
    Disjoint (f '' s) (f '' t) :=
  disjoint_image_image fun _ hx _ hy => hf.ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩

/--
theorem `_root_.Disjoint.of_image` / 定理 `_root_.Disjoint.of_image`

English:
theorem _root_.Disjoint.of_image
  given: (h : Disjoint (f '' s) (f '' t))
  statement: Disjoint s t
  proof: disjoint_iff_inf_le.mpr fun _ hx =>
    disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)

@[simp]

中文:
定理 _root_.Disjoint.of_image
  条件: (h : Disjoint (f '' s) (f '' t))
  结论: Disjoint s t
  证明: disjoint_iff_inf_le.mpr fun _ hx =>
    disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)

@[simp]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, disjoint_left, mem_image_of_mem
-/
theorem _root_.Disjoint.of_image (h : Disjoint (f '' s) (f '' t)) : Disjoint s t :=
  disjoint_iff_inf_le.mpr fun _ hx =>
    disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)

@[simp]
/--
theorem `disjoint_image_iff` / 定理 `disjoint_image_iff`

English:
theorem disjoint_image_iff
  given: (hf : Injective f)
  statement: Disjoint (f '' s) (f '' t) ↔ Disjoint s t
  proof: ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩

中文:
定理 disjoint_image_iff
  条件: (hf : Injective f)
  结论: Disjoint (f '' s) (f '' t) ↔ Disjoint s t
  证明: ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩

Depends on / 依赖: Disjoint, Disjoint.of_image, disjoint_image_of_injective, of_image
-/
theorem disjoint_image_iff (hf : Injective f) : Disjoint (f '' s) (f '' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩

/--
theorem `_root_.Disjoint.of_preimage` / 定理 `_root_.Disjoint.of_preimage`

English:
theorem _root_.Disjoint.of_preimage
  statement: (hf : Surjective f) {s t : Set β}
  proof: by
  rw [disjoint_iff_inter_eq_empty]; rw [← image_preimage_eq (_ inter _) hf]; rw [preimage_inter]; rw [h.inter_eq]; rw [image_empty]

@[simp]

中文:
定理 _root_.Disjoint.of_preimage
  结论: (hf : Surjective f) {s t : Set β}
  证明: by
  rw [disjoint_iff_inter_eq_empty]; rw [← image_preimage_eq (_ inter _) hf]; rw [preimage_inter]; rw [h.inter_eq]; rw [image_empty]

@[simp]

Depends on / 依赖: disjoint_iff_inter_eq_empty, h.inter_eq, image_empty, image_preimage_eq, inter_eq, preimage_inter
-/
theorem _root_.Disjoint.of_preimage (hf : Surjective f) {s t : Set β}
    (h : Disjoint (f ⁻¹' s) (f ⁻¹' t)) : Disjoint s t := by
  rw [disjoint_iff_inter_eq_empty]; rw [← image_preimage_eq (_ inter _) hf]; rw [preimage_inter]; rw [h.inter_eq]; rw [image_empty]

@[simp]
/--
theorem `disjoint_preimage_iff` / 定理 `disjoint_preimage_iff`

English:
theorem disjoint_preimage_iff
  given: (hf : Surjective f) {s t : Set β}
  proof: ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩

中文:
定理 disjoint_preimage_iff
  条件: (hf : Surjective f) {s t : Set β}
  证明: ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩

Depends on / 依赖: Disjoint, Disjoint.of_preimage, Disjoint.preimage, of_preimage, preimage
-/
theorem disjoint_preimage_iff (hf : Surjective f) {s t : Set β} :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩

/--
theorem `preimage_eq_empty` / 定理 `preimage_eq_empty`

English:
theorem preimage_eq_empty
  given: {s : Set β} (h : Disjoint s (range f))
  proof: by
  simpa using h.preimage f

中文:
定理 preimage_eq_empty
  条件: {s : Set β} (h : Disjoint s (range f))
  证明: by
  simpa using h.preimage f

Depends on / 依赖: h.preimage, preimage
-/
theorem preimage_eq_empty {s : Set β} (h : Disjoint s (range f)) :
    f ⁻¹' s = ∅ := by
  simpa using h.preimage f

/--
theorem `preimage_eq_empty_iff` / 定理 `preimage_eq_empty_iff`

English:
theorem preimage_eq_empty_iff
  given: {s : Set β}
  statement: f ⁻¹' s = ∅ ↔ Disjoint s (range f)
  proof: ⟨fun h => by
    simp only [eq_empty_iff_forall_notMem, mem_preimage] at h ⊢
    grind,
  preimage_eq_empty⟩

@[simp]

中文:
定理 preimage_eq_empty_iff
  条件: {s : Set β}
  结论: f ⁻¹' s = ∅ ↔ Disjoint s (range f)
  证明: ⟨fun h => by
    simp only [eq_empty_iff_forall_notMem, mem_preimage] at h ⊢
    grind,
  preimage_eq_empty⟩

@[simp]

Depends on / 依赖: eq_empty_iff_forall_notMem, mem_preimage, preimage_eq_empty
-/
theorem preimage_eq_empty_iff {s : Set β} : f ⁻¹' s = ∅ ↔ Disjoint s (range f) :=
  ⟨fun h => by
    simp only [eq_empty_iff_forall_notMem, mem_preimage] at h ⊢
    grind,
  preimage_eq_empty⟩

@[simp]
/--
theorem `disjoint_image_inl_image_inr` / 定理 `disjoint_image_inl_image_inr`

English:
theorem disjoint_image_inl_image_inr
  given: {u : Set α} {v : Set β}
  proof: disjoint_image_image by simp

@[simp]

中文:
定理 disjoint_image_inl_image_inr
  条件: {u : Set α} {v : Set β}
  证明: disjoint_image_image by simp

@[simp]

Depends on / 依赖: disjoint_image_image
-/
theorem disjoint_image_inl_image_inr {u : Set α} {v : Set β} :
    Disjoint (Sum.inl '' u) (Sum.inr '' v) :=
disjoint_image_image by simp

@[simp]
/--
theorem `disjoint_range_inl_image_inr` / 定理 `disjoint_range_inl_image_inr`

English:
theorem disjoint_range_inl_image_inr
  given: {v : Set β}
  proof: by
  grind

@[simp]

中文:
定理 disjoint_range_inl_image_inr
  条件: {v : Set β}
  证明: by
  grind

@[simp]

Depends on / 依赖: Sum.inl, Sum.inr
-/
theorem disjoint_range_inl_image_inr {v : Set β} :
    Disjoint (α := Set (α oplus β)) (range Sum.inl) (Sum.inr '' v) := by
  grind

@[simp]
/--
theorem `disjoint_image_inl_range_inr` / 定理 `disjoint_image_inl_range_inr`

English:
theorem disjoint_image_inl_range_inr
  given: {u : Set α}
  proof: by
  grind

中文:
定理 disjoint_image_inl_range_inr
  条件: {u : Set α}
  证明: by
  grind

Depends on / 依赖: Sum.inl, Sum.inr
-/
theorem disjoint_image_inl_range_inr {u : Set α} :
    Disjoint (α := Set (α oplus β)) (Sum.inl '' u) (range Sum.inr) := by
  grind

end Set

end Disjoint

section Sigma

variable {α : Type*} {β : α -> Type*} {i j : α} {s : Set (β i)}

/--
lemma `sigma_mk_preimage_image'` / 引理 `sigma_mk_preimage_image'`

English:
lemma sigma_mk_preimage_image'
  given: (h : i != j)
  statement: Sigma.mk j ⁻¹' Sigma.mk i '' s = ∅
  proof: by
  simp [image, h]

中文:
引理 sigma_mk_preimage_image'
  条件: (h : i != j)
  结论: Sigma.mk j ⁻¹' Sigma.mk i '' s = ∅
  证明: by
  simp [image, h]
-/
lemma sigma_mk_preimage_image' (h : i != j) : Sigma.mk j ⁻¹' Sigma.mk i '' s = ∅ := by
  simp [image, h]

/--
lemma `sigma_mk_preimage_image_eq_self` / 引理 `sigma_mk_preimage_image_eq_self`

English:
lemma sigma_mk_preimage_image_eq_self
  statement: Sigma.mk i ⁻¹' Sigma.mk i '' s = s
  proof: by
  simp [image]

中文:
引理 sigma_mk_preimage_image_eq_self
  结论: Sigma.mk i ⁻¹' Sigma.mk i '' s = s
  证明: by
  simp [image]
-/
lemma sigma_mk_preimage_image_eq_self : Sigma.mk i ⁻¹' Sigma.mk i '' s = s := by
  simp [image]

end Sigma
