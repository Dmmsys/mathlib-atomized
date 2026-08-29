/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Concept

import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

The theory of concept lattices allows for a simple construction. In fact, `DedekindCut α` is simply
an abbreviation for `Concept α α (· ≤ ·)`. This means we don't need to reprove that this is a
complete lattice; instead, the file simply proves that any order embedding into another complete
lattice factors through it.

## Todo

- Build the order isomorphism `DedekindCut ℚ ≃o EReal`.

- Make the `to_dual` tactic work so that some lemmas are created automatically, eg
  `DedekindCut.le_principal_iff` from `DedekindCut.principal_le_iff`.
  See [https://github.com/leanprover-community/mathlib4/pull/37939#discussion_r3328958630]

## Tags

Dedekind completion, Dedekind cut
-/

@[expose] public section

open Concept Set

variable {α β : Type*}

variable (α) in
/--
Definition of `DedekindCut` / `DedekindCut` 的定义

English:
abbreviation DedekindCut
  signature: [Preorder α]
  body: Concept α α (· <= ·)

中文:
缩写 DedekindCut
  签名: [Preorder α]
  定义体: Concept α α (· <= ·)

Depends on / 依赖: Concept
-/
abbrev DedekindCut [Preorder α] := Concept α α (· <= ·)

namespace DedekindCut

section Preorder
variable [Preorder α] [Preorder β]

/--
Definition of `left` / `left` 的定义

English:
abbreviation left
  signature: (A : DedekindCut α)
  body: A.extent

中文:
缩写 left
  签名: (A : DedekindCut α)
  定义体: A.extent

Depends on / 依赖: A.extent, extent
-/
abbrev left (A : DedekindCut α) : Set α := A.extent

/--
Definition of `right` / `right` 的定义

English:
abbreviation right
  signature: (A : DedekindCut α)
  body: A.intent

中文:
缩写 right
  签名: (A : DedekindCut α)
  定义体: A.intent

Depends on / 依赖: A.intent, intent
-/
abbrev right (A : DedekindCut α) : Set α := A.intent

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {A B : DedekindCut α} (h : A.left = B.left)
  statement: A = B
  proof: Concept.ext h

中文:
定理 ext
  条件: {A B : DedekindCut α} (h : A.left = B.left)
  结论: A = B
  证明: Concept.ext h
-/
@[ext] theorem ext {A B : DedekindCut α} (h : A.left = B.left) : A = B := Concept.ext h

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {A B : DedekindCut α} (h : A.right = B.right)
  statement: A = B
  proof: Concept.ext' h

@[simp]

中文:
定理 ext'
  条件: {A B : DedekindCut α} (h : A.right = B.right)
  结论: A = B
  证明: Concept.ext' h

@[simp]

Depends on / 依赖: Concept, Concept.ext
-/
theorem ext' {A B : DedekindCut α} (h : A.right = B.right) : A = B := Concept.ext' h

@[simp]
/--
theorem `upperBounds_left` / 定理 `upperBounds_left`

English:
theorem upperBounds_left
  given: (A : DedekindCut α)
  statement: upperBounds A.left = A.right
  proof: A.upperPolar_extent

@[simp]

中文:
定理 upperBounds_left
  条件: (A : DedekindCut α)
  结论: upperBounds A.left = A.right
  证明: A.upperPolar_extent

@[simp]

Depends on / 依赖: A.upperPolar_extent, upperPolar_extent
-/
theorem upperBounds_left (A : DedekindCut α) : upperBounds A.left = A.right :=
  A.upperPolar_extent

@[simp]
/--
theorem `lowerBounds_right` / 定理 `lowerBounds_right`

English:
theorem lowerBounds_right
  given: (A : DedekindCut α)
  statement: lowerBounds A.right = A.left
  proof: A.lowerPolar_intent

中文:
定理 lowerBounds_right
  条件: (A : DedekindCut α)
  结论: lowerBounds A.right = A.left
  证明: A.lowerPolar_intent

Depends on / 依赖: A.lowerPolar_intent, lowerPolar_intent
-/
theorem lowerBounds_right (A : DedekindCut α) : lowerBounds A.right = A.left :=
  A.lowerPolar_intent

/--
theorem `image_left_subset_lowerBounds` / 定理 `image_left_subset_lowerBounds`

English:
theorem image_left_subset_lowerBounds
  statement: {f : α -> β} (hf : Monotone f)
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
exact hf rel_extent_intent hx hy

中文:
定理 image_left_subset_lowerBounds
  结论: {f : α -> β} (hf : Monotone f)
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
exact hf rel_extent_intent hx hy

Depends on / 依赖: rel_extent_intent
-/
theorem image_left_subset_lowerBounds {f : α -> β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.left subseteq lowerBounds (f '' A.right) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
exact hf rel_extent_intent hx hy

/--
theorem `image_right_subset_upperBounds` / 定理 `image_right_subset_upperBounds`

English:
theorem image_right_subset_upperBounds
  statement: {f : α -> β} (hf : Monotone f)
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
exact hf rel_extent_intent hy hx

中文:
定理 image_right_subset_upperBounds
  结论: {f : α -> β} (hf : Monotone f)
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
exact hf rel_extent_intent hy hx

Depends on / 依赖: rel_extent_intent
-/
theorem image_right_subset_upperBounds {f : α -> β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.right subseteq upperBounds (f '' A.left) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
exact hf rel_extent_intent hy hx

/--
Definition of `principal` / `principal` 的定义

English:
definition principal
  signature: (a : α)
  body: (Concept.ofObject _ a).copy (Iic a) (Ici a)
    (by ext; simpa [mem_lowerPolar_iff] using! forall_ge_iff_le.symm)
    (by ext; simp)

中文:
定义 principal
  签名: (a : α)
  定义体: (Concept.ofObject _ a).copy (Iic a) (Ici a)
    (by ext; simpa [mem_lowerPolar_iff] using! forall_ge_iff_le.symm)
    (by ext; simp)

Depends on / 依赖: Concept, Concept.ofObject, forall_ge_iff_le, forall_ge_iff_le.symm, mem_lowerPolar_iff, ofObject
-/
def principal (a : α) : DedekindCut α :=
  (Concept.ofObject _ a).copy (Iic a) (Ici a)
    (by ext; simpa [mem_lowerPolar_iff] using! forall_ge_iff_le.symm)
    (by ext; simp)

/--
theorem `left_principal` / 定理 `left_principal`

English:
theorem left_principal
  given: (a : α)
  statement: (principal a).left = Iic a
  proof: rfl

中文:
定理 left_principal
  条件: (a : α)
  结论: (principal a).left = Iic a
  证明: rfl
-/
@[simp] theorem left_principal (a : α) : (principal a).left = Iic a := rfl
/--
theorem `right_principal` / 定理 `right_principal`

English:
theorem right_principal
  given: (a : α)
  statement: (principal a).right = Ici a
  proof: rfl

中文:
定理 right_principal
  条件: (a : α)
  结论: (principal a).right = Ici a
  证明: rfl
-/
@[simp] theorem right_principal (a : α) : (principal a).right = Ici a := rfl

/--
theorem `ofObject_eq_principal` / 定理 `ofObject_eq_principal`

English:
theorem ofObject_eq_principal
  given: (a : α)
  statement: ofObject (· <= ·) a = principal a
  proof: (copy_eq ..).symm

中文:
定理 ofObject_eq_principal
  条件: (a : α)
  结论: ofObject (· <= ·) a = principal a
  证明: (copy_eq ..).symm
-/
@[simp] theorem ofObject_eq_principal (a : α) : ofObject (· <= ·) a = principal a :=
  (copy_eq ..).symm
/--
theorem `ofAttribute_eq_principal` / 定理 `ofAttribute_eq_principal`

English:
theorem ofAttribute_eq_principal
  given: (a : α)
  statement: ofAttribute (· <= ·) a = principal a
  proof: by
  ext; simp

@[simp]

中文:
定理 ofAttribute_eq_principal
  条件: (a : α)
  结论: ofAttribute (· <= ·) a = principal a
  证明: by
  ext; simp

@[simp]
-/
@[simp] theorem ofAttribute_eq_principal (a : α) : ofAttribute (· <= ·) a = principal a := by
  ext; simp

@[simp]
/--
theorem `principal_le_principal` / 定理 `principal_le_principal`

English:
theorem principal_le_principal
  given: {a b : α}
  statement: principal a <= principal b ↔ a <= b
  proof: by
  simpa using ofObject_le_ofAttribute_iff (r := (· <= ·)) (a := a)

@[simp]

中文:
定理 principal_le_principal
  条件: {a b : α}
  结论: principal a <= principal b ↔ a <= b
  证明: by
  simpa using ofObject_le_ofAttribute_iff (r := (· <= ·)) (a := a)

@[simp]

Depends on / 依赖: ofObject_le_ofAttribute_iff
-/
theorem principal_le_principal {a b : α} : principal a <= principal b ↔ a <= b := by
  simpa using ofObject_le_ofAttribute_iff (r := (· <= ·)) (a := a)

@[simp]
/--
theorem `principal_lt_principal` / 定理 `principal_lt_principal`

English:
theorem principal_lt_principal
  given: {a b : α}
  statement: principal a < principal b ↔ a < b
  proof: by
  simp [lt_iff_le_not_ge]

中文:
定理 principal_lt_principal
  条件: {a b : α}
  结论: principal a < principal b ↔ a < b
  证明: by
  simp [lt_iff_le_not_ge]

Depends on / 依赖: lt_iff_le_not_ge
-/
theorem principal_lt_principal {a b : α} : principal a < principal b ↔ a < b := by
  simp [lt_iff_le_not_ge]

/--
lemma `principal_le_iff` / 引理 `principal_le_iff`

English:
lemma principal_le_iff
  given: {a : α} {c : DedekindCut α}
  proof: by
  simp only [← extent_subset_extent_iff, left_principal]
  exact ⟨fun h => h self_mem_Iic, fun h y hy => mem_extent_of_rel_extent hy h⟩

中文:
引理 principal_le_iff
  条件: {a : α} {c : DedekindCut α}
  证明: by
  simp only [← extent_subset_extent_iff, left_principal]
  exact ⟨fun h => h self_mem_Iic, fun h y hy => mem_extent_of_rel_extent hy h⟩

Depends on / 依赖: extent_subset_extent_iff, left_principal, mem_extent_of_rel_extent, self_mem_Iic
-/
lemma principal_le_iff {a : α} {c : DedekindCut α} :
    principal a <= c ↔ a in c.left := by
  simp only [← extent_subset_extent_iff, left_principal]
  exact ⟨fun h => h self_mem_Iic, fun h y hy => mem_extent_of_rel_extent hy h⟩

/--
lemma `le_principal_iff` / 引理 `le_principal_iff`

English:
lemma le_principal_iff
  given: {a : α} {c : DedekindCut α}
  proof: by
  simp only [← intent_subset_intent_iff, right_principal]
  exact ⟨fun h => h self_mem_Ici, fun h _y hy => mem_intent_of_intent_rel hy h⟩

中文:
引理 le_principal_iff
  条件: {a : α} {c : DedekindCut α}
  证明: by
  simp only [← intent_subset_intent_iff, right_principal]
  exact ⟨fun h => h self_mem_Ici, fun h _y hy => mem_intent_of_intent_rel hy h⟩

Depends on / 依赖: intent_subset_intent_iff, mem_intent_of_intent_rel, right_principal, self_mem_Ici
-/
lemma le_principal_iff {a : α} {c : DedekindCut α} :
    c <= principal a ↔ a in c.right := by
  simp only [← intent_subset_intent_iff, right_principal]
  exact ⟨fun h => h self_mem_Ici, fun h _y hy => mem_intent_of_intent_rel hy h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableLE (DedekindCut α)
  body: Classical.decRel _

中文:
实例 :
  签名: DecidableLE (DedekindCut α)
  定义体: Classical.decRel _

Depends on / 依赖: Classical, Classical.decRel, decRel
-/
noncomputable instance : DecidableLE (DedekindCut α) :=
  Classical.decRel _

end Preorder

section PartialOrder
variable [PartialOrder α]

@[simp]
/--
theorem `principal_inj` / 定理 `principal_inj`

English:
theorem principal_inj
  given: {a b : α}
  statement: principal a = principal b ↔ a = b
  proof: by
  simp [le_antisymm_iff]

中文:
定理 principal_inj
  条件: {a b : α}
  结论: principal a = principal b ↔ a = b
  证明: by
  simp [le_antisymm_iff]

Depends on / 依赖: le_antisymm_iff
-/
theorem principal_inj {a b : α} : principal a = principal b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `DedekindCut.principal` as an `OrderEmbedding`. -/
@[simps! apply]
/--
Definition of `principalEmbedding` / `principalEmbedding` 的定义

English:
definition principalEmbedding
  signature: : α ↪o DedekindCut α where
  body: principal
  inj' _ _ := principal_inj.1
  map_rel_iff' := principal_le_principal

中文:
定义 principalEmbedding
  签名: : α ↪o DedekindCut α where
  定义体: principal
  inj' _ _ := principal_inj.1
  map_rel_iff' := principal_le_principal

Depends on / 依赖: principal
-/
def principalEmbedding : α ↪o DedekindCut α where
  toFun := principal
  inj' _ _ := principal_inj.1
  map_rel_iff' := principal_le_principal

/--
theorem `coe_principalEmbedding` / 定理 `coe_principalEmbedding`

English:
theorem coe_principalEmbedding
  statement: ⇑(@principalEmbedding α _) = principal
  proof: rfl

中文:
定理 coe_principalEmbedding
  结论: ⇑(@principalEmbedding α _) = principal
  证明: rfl
-/
@[simp] theorem coe_principalEmbedding : ⇑(@principalEmbedding α _) = principal := rfl

end PartialOrder

section CompleteLattice
variable [CompleteLattice α] [PartialOrder β]

@[simp]
/--
theorem `principal_sSup_left` / 定理 `principal_sSup_left`

English:
theorem principal_sSup_left
  given: (A : DedekindCut α)
  statement: principal (sSup A.left) = A
  proof: by
  apply ext'
  ext
  rw [right_principal]; rw [mem_Ici]; rw [sSup_le_iff]; rw [← upperBounds_left]; rw [mem_upperBounds]

@[simp]

中文:
定理 principal_sSup_left
  条件: (A : DedekindCut α)
  结论: principal (sSup A.left) = A
  证明: by
  apply ext'
  ext
  rw [right_principal]; rw [mem_Ici]; rw [sSup_le_iff]; rw [← upperBounds_left]; rw [mem_upperBounds]

@[simp]

Depends on / 依赖: mem_Ici, mem_upperBounds, right_principal, sSup_le_iff, upperBounds_left
-/
theorem principal_sSup_left (A : DedekindCut α) : principal (sSup A.left) = A := by
  apply ext'
  ext
  rw [right_principal]; rw [mem_Ici]; rw [sSup_le_iff]; rw [← upperBounds_left]; rw [mem_upperBounds]

@[simp]
/--
theorem `principal_sInf_right` / 定理 `principal_sInf_right`

English:
theorem principal_sInf_right
  given: (A : DedekindCut α)
  statement: principal (sInf A.right) = A
  proof: by
  ext
  rw [left_principal]; rw [mem_Iic]; rw [le_sInf_iff]; rw [← lowerBounds_right]; rw [mem_lowerBounds]

中文:
定理 principal_sInf_right
  条件: (A : DedekindCut α)
  结论: principal (sInf A.right) = A
  证明: by
  ext
  rw [left_principal]; rw [mem_Iic]; rw [le_sInf_iff]; rw [← lowerBounds_right]; rw [mem_lowerBounds]

Depends on / 依赖: le_sInf_iff, left_principal, lowerBounds_right, mem_Iic, mem_lowerBounds
-/
theorem principal_sInf_right (A : DedekindCut α) : principal (sInf A.right) = A := by
  ext
  rw [left_principal]; rw [mem_Iic]; rw [le_sInf_iff]; rw [← lowerBounds_right]; rw [mem_lowerBounds]

/--
Definition of `factorEmbedding` / `factorEmbedding` 的定义

English:
definition factorEmbedding
  signature: (f : β ↪o α)
  body: .ofMapLEIff (fun A => sSup (f '' A.left)) by
    refine fun A B => ⟨fun h x hx => ?_, fun h => sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_right]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_right_subset_upperBou

中文:
定义 factorEmbedding
  签名: (f : β ↪o α)
  定义体: .ofMapLEIff (fun A => sSup (f '' A.left)) by
    refine fun A B => ⟨fun h x hx => ?_, fun h => sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_right]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_right_subset_upperBou

Depends on / 依赖: A.left, f.le_iff_le, f.monotone, forall_mem_image, image_mono, image_right_subset_upperBounds, le_iff_le, le_sSup_iff, lowerBounds_right, mem_image_of_mem, monotone, ofMapLEIff, sSup_le_iff, sSup_le_sSup, simp_rw
-/
def factorEmbedding (f : β ↪o α) : DedekindCut β ↪o α :=
.ofMapLEIff (fun A => sSup (f '' A.left)) by
    refine fun A B => ⟨fun h x hx => ?_, fun h => sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_right]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_right_subset_upperBounds f.monotone _ (mem_image_of_mem _ hy)) hx

/--
theorem `factorEmbedding_apply` / 定理 `factorEmbedding_apply`

English:
theorem factorEmbedding_apply
  given: (f : β ↪o α) (A : DedekindCut β)
  proof: rfl

@[simp]

中文:
定理 factorEmbedding_apply
  条件: (f : β ↪o α) (A : DedekindCut β)
  证明: rfl

@[simp]
-/
theorem factorEmbedding_apply (f : β ↪o α) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.left) :=
  rfl

@[simp]
/--
theorem `factorEmbedding_principal` / 定理 `factorEmbedding_principal`

English:
theorem factorEmbedding_principal
  given: (f : β ↪o α) (x : β)
  statement: factorEmbedding f (principal x) = f x
  proof: by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy => hy ?_
  simp

中文:
定理 factorEmbedding_principal
  条件: (f : β ↪o α) (x : β)
  结论: factorEmbedding f (principal x) = f x
  证明: by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy => hy ?_
  simp

Depends on / 依赖: factorEmbedding_apply, le_antisymm, le_sSup_iff
-/
theorem factorEmbedding_principal (f : β ↪o α) (x : β) : factorEmbedding f (principal x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy => hy ?_
  simp

/--
theorem `principalEmbedding_trans_factorEmbedding` / 定理 `principalEmbedding_trans_factorEmbedding`

English:
theorem principalEmbedding_trans_factorEmbedding
  given: (f : β ↪o α)
  proof: by
  ext; simp

中文:
定理 principalEmbedding_trans_factorEmbedding
  条件: (f : β ↪o α)
  证明: by
  ext; simp
-/
theorem principalEmbedding_trans_factorEmbedding (f : β ↪o α) :
    principalEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- `DedekindCut.principal` as an `OrderIso`.

This provides the second half of the **fundamental theorem of concept lattices**: every complete
lattice is isomorphic to a concept lattice (its own Dedekind completion).

See `Concept.instCompleteLattice` for the first half. -/
@[simps! apply]
/--
Definition of `principalIso` / `principalIso` 的定义

English:
definition principalIso
  signature: : α ≃o DedekindCut α where
  body: factorEmbedding (OrderIso.refl α)
  left_inv x := factorEmbedding_principal _ x
  right_inv x := by simp [factorEmbedding]
  __ := principalEmbedding

中文:
定义 principalIso
  签名: : α ≃o DedekindCut α where
  定义体: factorEmbedding (OrderIso.refl α)
  left_inv x := factorEmbedding_principal _ x
  right_inv x := by simp [factorEmbedding]
  __ := principalEmbedding

Depends on / 依赖: OrderIso, OrderIso.refl, factorEmbedding
-/
def principalIso : α ≃o DedekindCut α where
  invFun := factorEmbedding (OrderIso.refl α)
  left_inv x := factorEmbedding_principal _ x
  right_inv x := by simp [factorEmbedding]
  __ := principalEmbedding

set_option backward.isDefEq.respectTransparency false in
/--
theorem `principalIso_symm_apply` / 定理 `principalIso_symm_apply`

English:
theorem principalIso_symm_apply
  given: (A : DedekindCut α)
  statement: principalIso.symm A = sSup A.left
  proof: (factorEmbedding_apply ..).trans by simp

中文:
定理 principalIso_symm_apply
  条件: (A : DedekindCut α)
  结论: principalIso.symm A = sSup A.left
  证明: (factorEmbedding_apply ..).trans by simp

Depends on / 依赖: factorEmbedding_apply
-/
theorem principalIso_symm_apply (A : DedekindCut α) : principalIso.symm A = sSup A.left :=
(factorEmbedding_apply ..).trans by simp

end CompleteLattice

section LinearOrder
variable [LinearOrder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Total (DedekindCut α) (· <= ·)
  body: le_total (α := LowerSet α) ⟨_, isLowerSet_extent_le x⟩ ⟨_, isLowerSet_extent_le y⟩

中文:
实例 :
  签名: @Std.Total (DedekindCut α) (· <= ·)
  定义体: le_total (α := LowerSet α) ⟨_, isLowerSet_extent_le x⟩ ⟨_, isLowerSet_extent_le y⟩

Depends on / 依赖: LowerSet, isLowerSet_extent_le, le_total
-/
instance : @Std.Total (DedekindCut α) (· <= ·) where
  total x y := le_total (α := LowerSet α) ⟨_, isLowerSet_extent_le x⟩ ⟨_, isLowerSet_extent_le y⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (DedekindCut α)
  body: congrFun₂ inf_eq_minDefault x y
  max_def x y := congrFun₂ sup_eq_maxDefault x y
  le_total := total_of _
  toDecidableLE := inferInstance

中文:
实例 :
  签名: LinearOrder (DedekindCut α)
  定义体: congrFun₂ inf_eq_minDefault x y
  max_def x y := congrFun₂ sup_eq_maxDefault x y
  le_total := total_of _
  toDecidableLE := inferInstance

Depends on / 依赖: inf_eq_minDefault
-/
noncomputable instance : LinearOrder (DedekindCut α) where
  min_def x y := congrFun₂ inf_eq_minDefault x y
  max_def x y := congrFun₂ sup_eq_maxDefault x y
  le_total := total_of _
  toDecidableLE := inferInstance

/--
theorem `lt_iff_exists` / 定理 `lt_iff_exists`

English:
theorem lt_iff_exists
  given: {a b : DedekindCut α}
  proof: by
  refine ⟨fun h => ?_, fun ⟨c, hca, hcb⟩ => hca.trans_le hcb⟩
  rw [← extent_ssubset_extent_iff]; rw [Set.ssubset_iff_exists] at h
  simpa [← not_le, principal_le_iff, and_comm] using h.2

中文:
定理 lt_iff_exists
  条件: {a b : DedekindCut α}
  证明: by
  refine ⟨fun h => ?_, fun ⟨c, hca, hcb⟩ => hca.trans_le hcb⟩
  rw [← extent_ssubset_extent_iff]; rw [Set.ssubset_iff_exists] at h
  simpa [← not_le, principal_le_iff, and_comm] using h.2

Depends on / 依赖: Set.ssubset_iff_exists, and_comm, extent_ssubset_extent_iff, hca.trans_le, not_le, principal_le_iff, ssubset_iff_exists, trans_le
-/
theorem lt_iff_exists {a b : DedekindCut α} :
    a < b ↔ exists c, a < principal c ∧ principal c <= b := by
  refine ⟨fun h => ?_, fun ⟨c, hca, hcb⟩ => hca.trans_le hcb⟩
  rw [← extent_ssubset_extent_iff]; rw [Set.ssubset_iff_exists] at h
  simpa [← not_le, principal_le_iff, and_comm] using h.2

/--
theorem `lt_iff_exists'` / 定理 `lt_iff_exists'`

English:
theorem lt_iff_exists'
  given: {a b : DedekindCut α}
  proof: by
  refine ⟨fun h => ?_, fun ⟨c, hca, hcb⟩ => lt_of_le_of_lt hca hcb⟩
  rw [← intent_ssubset_intent_iff]; rw [Set.ssubset_iff_exists] at h
  simpa [← not_le, le_principal_iff] using h.2

中文:
定理 lt_iff_exists'
  条件: {a b : DedekindCut α}
  证明: by
  refine ⟨fun h => ?_, fun ⟨c, hca, hcb⟩ => lt_of_le_of_lt hca hcb⟩
  rw [← intent_ssubset_intent_iff]; rw [Set.ssubset_iff_exists] at h
  simpa [← not_le, le_principal_iff] using h.2

Depends on / 依赖: Set.ssubset_iff_exists, intent_ssubset_intent_iff, le_principal_iff, lt_of_le_of_lt, not_le, ssubset_iff_exists
-/
theorem lt_iff_exists' {a b : DedekindCut α} :
    a < b ↔ exists c, a <= principal c ∧ principal c < b := by
  refine ⟨fun h => ?_, fun ⟨c, hca, hcb⟩ => lt_of_le_of_lt hca hcb⟩
  rw [← intent_ssubset_intent_iff]; rw [Set.ssubset_iff_exists] at h
  simpa [← not_le, le_principal_iff] using h.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLinearOrder (DedekindCut α)
  body: (inferInstance : LinearOrder _)
  __ := (inferInstance : CompleteLattice _)
  __ := LinearOrder.toBiheytingAlgebra _

中文:
实例 :
  签名: CompleteLinearOrder (DedekindCut α)
  定义体: (inferInstance : LinearOrder _)
  __ := (inferInstance : CompleteLattice _)
  __ := LinearOrder.toBiheytingAlgebra _

Depends on / 依赖: LinearOrder
-/
noncomputable instance : CompleteLinearOrder (DedekindCut α) where
  __ := (inferInstance : LinearOrder _)
  __ := (inferInstance : CompleteLattice _)
  __ := LinearOrder.toBiheytingAlgebra _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DenselyOrdered
  signature: α] : DenselyOrdered (DedekindCut α) where
  body: by
    obtain ⟨c, hac, hcb⟩ := lt_iff_exists.mp h
    obtain ⟨d, had, hdc⟩ := lt_iff_exists'.mp hac
    simp only [principal_lt_principal] at hdc
    obtain ⟨u, _, _⟩ := DenselyOrdered.dense d c hdc
    exact ⟨principal u, had.trans_lt (by simpa), hcb.trans_lt' (by simpa)⟩

中文:
实例 [DenselyOrdered
  签名: α] : DenselyOrdered (DedekindCut α) where
  定义体: by
    obtain ⟨c, hac, hcb⟩ := lt_iff_exists.mp h
    obtain ⟨d, had, hdc⟩ := lt_iff_exists'.mp hac
    simp only [principal_lt_principal] at hdc
    obtain ⟨u, _, _⟩ := DenselyOrdered.dense d c hdc
    exact ⟨principal u, had.trans_lt (by simpa), hcb.trans_lt' (by simpa)⟩

Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, had.trans_lt, hcb.trans_lt, lt_iff_exists, lt_iff_exists.mp, principal, principal_lt_principal, trans_lt
-/
instance [DenselyOrdered α] : DenselyOrdered (DedekindCut α) where
  dense a b h := by
    obtain ⟨c, hac, hcb⟩ := lt_iff_exists.mp h
    obtain ⟨d, had, hdc⟩ := lt_iff_exists'.mp hac
    simp only [principal_lt_principal] at hdc
    obtain ⟨u, _, _⟩ := DenselyOrdered.dense d c hdc
    exact ⟨principal u, had.trans_lt (by simpa), hcb.trans_lt' (by simpa)⟩

/--
theorem `principal_lt_iff` / 定理 `principal_lt_iff`

English:
theorem principal_lt_iff
  given: {a : α} {c : DedekindCut α}
  proof: by
  rw [← not_le]; rw [le_principal_iff]
  rw [not_iff_comm]; rw [not_exists]; rw [← le_principal_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

中文:
定理 principal_lt_iff
  条件: {a : α} {c : DedekindCut α}
  证明: by
  rw [← not_le]; rw [le_principal_iff]
  rw [not_iff_comm]; rw [not_exists]; rw [← le_principal_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

Depends on / 依赖: le_principal_iff, not_and, not_exists, not_iff_comm, not_le, not_not, simp_rw
-/
theorem principal_lt_iff {a : α} {c : DedekindCut α} :
    principal a < c ↔ exists b in c.left, a < b := by
  rw [← not_le]; rw [le_principal_iff]
  rw [not_iff_comm]; rw [not_exists]; rw [← le_principal_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

/--
theorem `lt_principal_iff` / 定理 `lt_principal_iff`

English:
theorem lt_principal_iff
  given: {a : α} {c : DedekindCut α}
  proof: by
  rw [← not_le]; rw [principal_le_iff]
  rw [not_iff_comm]; rw [not_exists]; rw [← principal_le_iff]
  rw [← intent_subset_intent_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

中文:
定理 lt_principal_iff
  条件: {a : α} {c : DedekindCut α}
  证明: by
  rw [← not_le]; rw [principal_le_iff]
  rw [not_iff_comm]; rw [not_exists]; rw [← principal_le_iff]
  rw [← intent_subset_intent_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

Depends on / 依赖: intent_subset_intent_iff, not_and, not_exists, not_iff_comm, not_le, not_not, principal_le_iff, simp_rw
-/
theorem lt_principal_iff {a : α} {c : DedekindCut α} :
    c < principal a ↔ exists b in c.right, b < a := by
  rw [← not_le]; rw [principal_le_iff]
  rw [not_iff_comm]; rw [not_exists]; rw [← principal_le_iff]
  rw [← intent_subset_intent_iff]
  simp_rw [← not_le, not_and, not_not]
  rfl

end LinearOrder
end DedekindCut
